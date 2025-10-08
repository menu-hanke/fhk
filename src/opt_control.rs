//! Control flow simplification.

// this pass performs the following simplifications:
//   SWITCH    elimination of "model switch" IFs
//   LOOP      elimination of side-effect-free loops
//   PHI       elimination of constant and unused PHIs
//   CCP       elimination of conditionally constant values
//   GOTO      elimination of redundant GOTOs

use core::iter::zip;

use crate::bitmap::BitmapWord;
use crate::bump::{Bump, BumpRef};
use crate::controlflow::BlockId;
use crate::index::{self, index, IndexArray, IndexOption, IndexSet, IndexSlice, IndexVec};
use crate::ir::{ins_matches, FuncId, Ins, InsId, Opcode, Phi, PhiId, Type};
use crate::optimize::{Ocx, OptFlag};
use crate::relation::Relation;
use crate::trace::trace;
use crate::zerocopy_union::zerocopy_union;

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct BlockData {
    ctr: InsId, // the control instruction corresponding to this block
    pin: u16,   // number of instructions pinned to this block
}

const MAX_CCPFACT: usize = BitmapWord::BITS;
const MAX_CCPFIX: usize = MAX_CCPFACT / 2;
const MAX_CCPDEPTH: usize = 5;

#[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct CCPBlock {
    branch: BitmapWord<FactId>,
    fix: BitmapWord<FactId>
}

index!(struct FixId(u16));
index!(struct FactId(u16) debug("{}"));

const FIX_TRUE: InsId = zerocopy::transmute!(!0u16);
const FIX_FALSE: InsId = zerocopy::transmute!(!1u16);

zerocopy_union! {
    union InsData {
        block block_mut: IndexOption<BlockId>,
        fact fact_mut: FactId,
        fix fix_mut: InsId
    }
}

/* ---- IFCHAIN ------------------------------------------------------------- */

// if an IF jumps to another IF and...
// (1) the target IF has the same condition; AND
// (2) the target IF has no pins
// then forward the corresponding arm from the target IF.

fn ifchain_run(
    code: &mut IndexSlice<InsId, Ins>,
    dfg_users: &mut Relation<InsId, InsId>,
    blocks: &IndexSlice<BlockId, BlockData>,
    ctr_data: &IndexSlice<InsId, InsData>
) {
    // blocks is in topo order, visit in reverse order so that the last IF in the chain is
    // visited first.
    for &BlockData { ctr, .. } in blocks.raw.iter().rev() {
        let ins = code[ctr];
        if ins.opcode() != Opcode::IF { continue }
        let cond = ins.decode_V();
        for (i, &target) in ins.controls().iter().enumerate() {
            let tins = code[target];
            if tins.opcode() == Opcode::IF
                && tins.decode_V() == cond
                    && blocks[ctr_data[target].block().unwrap()].pin == 0
            {
                code[ctr].controls_mut()[i] = tins.controls()[i];
                dfg_users.remove(target, ctr);
                dfg_users.add(tins.controls()[i], ctr);
            }
        }
    }
}

/* ---- SWITCH -------------------------------------------------------------- */

// if an IF...
// (1a) compares a PHI against a constand value; AND
// (1b) all of its precedessors are JMPs that set the PHI to a constant value; AND
// (1c) it has no other pins; AND
// (1d) this is the only use of the PHI
// then rewrite each incoming JMP to a GOTO to the appropriate branch

fn hasnonswitchuser(
    code: &IndexSlice<InsId, Ins>,
    dfg_users: &Relation<InsId, InsId>,
    isswitch: &IndexSet<InsId>,
    visited: &mut IndexSet<InsId>,
    id: InsId
) -> bool {
    if visited.test_and_set(id) {
        return false
    }
    if code[id].opcode().is_control() {
        return !isswitch.contains(id);
    }
    dfg_users[id]
        .iter()
        .any(|&i| hasnonswitchuser(code, dfg_users, isswitch, visited, i))
}

fn switch_run(
    code: &mut IndexSlice<InsId, Ins>,
    blocks: &IndexSlice<BlockId, BlockData>,
    isswitch: &mut IndexSet<InsId>,
    visited: &mut IndexSet<InsId>,
    dfg_users: &mut Relation<InsId, InsId>,
) {
    'blocks: for &BlockData { ctr, pin } in &blocks.raw {
        if pin != 1 { /* failed (1a) or (1c) */ continue }
        let ins = code[ctr];
        // check (1a)
        let (phiv, isbool) = if ins_matches!(code, ins; IF (PHI)) {
            (ins.decode_V(), true)
        } else if ins_matches!(code, ins; IF ((EQ|NE) (PHI) const)) {
            (code[ins.decode_V()].decode_V(), false)
        } else {
            continue
        };
        if code[phiv].type_().is_fp() { continue } // TODO floats (nan handling)
        let (_, phi) = code[phiv].decode_PHI();
        // check (1b)
        for &user in &dfg_users[ctr] {
            if user == phiv { continue }
            let uins = code[user];
            if !ins_matches!(code, uins; JMP const) || uins.decode_JMP().2 != phi {
                continue 'blocks;
            }
        }
        // mark switch chain
        isswitch.clear();
        let mut chain = ctr;
        'chain: loop {
            trace!(OPTIMIZE "SWITCH eliminate chain {:?} {:?}", chain, code[chain]);
            isswitch.insert(chain);
            for &next in code[chain].controls() {
                if dfg_users[next].len() == 1 && match isbool {
                    true => code[next].opcode() == Opcode::IF && code[next].decode_V() == phiv,
                    false => ins_matches!(code, code[next]; IF ((EQ|NE) (PHI) const))
                        && code[code[code[next].decode_V()].decode_V()].decode_PHI().1 == phi
                } {
                    chain = next;
                    continue 'chain;
                }
            }
            break;
        }
        // check (1d) aliasing PHI instructions
        // for &BlockData { ctr, .. } in &blocks.raw {
        //     if !isswitch.contains(ctr) {
        //         for &user in dfg.uses(ctr) {
        //             let uins = code[user];
        //             if uins.opcode() == Opcode::PHI && uins.decode_PHI().1 == phi {
        //                 continue 'blocks;
        //             }
        //         }
        //     }
        // }
        // check (1d)
        visited.clear();
        if hasnonswitchuser(code, dfg_users, isswitch, visited, phiv) {
            continue 'blocks;
        }
        // this is a switch IF. redirect incoming JMPs.
        let mut u = 0;
        while let Some(&user) = dfg_users[ctr].get(u) {
            if user == phiv {
                u += 1;
            } else {
                let (jmpval, _, _) = code[user].decode_JMP();
                let kjmp = code[jmpval];
                debug_assert!(kjmp.opcode().is_const());
                let mut chain = ctr;
                while isswitch.contains(chain) {
                    let (cond, tru, fal) = code[chain].decode_IF();
                    if isbool {
                        debug_assert!(cond == phiv);
                        debug_assert!(kjmp.opcode() == Opcode::KINT && kjmp.type_() == Type::B1);
                        trace!(OPTIMIZE "kjmp = {:?}", kjmp);
                        chain = if kjmp == Ins::KINT(Type::B1, 0) { fal } else { tru };
                    } else {
                        let opcode = code[cond].opcode();
                        let kswitch = code[code[cond].decode__V()];
                        debug_assert!((Opcode::EQ|Opcode::NE).contains(opcode));
                        // note: this assumes two constants are equal iff the instructions are equal.
                        // this works as long as the KINT/KINT64/KFP64 logic is consistent everywhere,
                        // and no one modifies the (unused) a field.
                        // also, this logic only works for integers. this can be done with floats as well
                        // because we are just comparing constants, but the main purpose of this pass
                        // is to cleanup the arm/avail chunks emitted by the frontend after inlining.
                        debug_assert!(kjmp.a() == 0 && kswitch.a() == 0);
                        debug_assert!(!kjmp.type_().is_fp() && kjmp.type_() == kswitch.type_());
                        chain = if (kjmp == kswitch) == (opcode == Opcode::EQ) { tru } else { fal };
                    }
                }
                trace!(OPTIMIZE "SWITCH redirect jump {:?} {:?}  =>  {:?}", user, code[user], chain);
                code[user] = Ins::GOTO(chain);
                dfg_users.remove(ctr, user);
                dfg_users.remove(jmpval, user);
                dfg_users.add(chain, user);
            }
        }
    }
}

/* ---- LOOP ---------------------------------------------------------------- */

// if an IF...
// (1a) loops unconditionally back to itself; AND
// (1b) all uses of its PHIs/pins are inside the loop
// then eliminate and replace with GOTO

fn loop_checkbody(
    code: &IndexSlice<InsId, Ins>,
    isloop: &mut IndexSet<InsId>,
    isloopphi: &mut IndexSet<PhiId>,
    mut id: InsId,
    tail: InsId
) -> bool {
    loop {
        isloop.insert(id);
        if id == tail {
            return true
        }
        let ins = code[id];
        match ins.opcode() {
            Opcode::JMP => {
                let (_, next, phi) = ins.decode_JMP();
                isloopphi.insert(phi);
                id = next;
            },
            Opcode::GOTO => id = ins.decode_GOTO(),
            _ => return false
        };
    }
}

fn loop_isloopuse(
    code: &IndexSlice<InsId, Ins>,
    dfg_users: &Relation<InsId, InsId>,
    isloop: &mut IndexSet<InsId>,
    id: InsId
) -> bool {
    if isloop.contains(id) {
        return true
    }
    if code[id].opcode().is_control() {
        return false
    }
    if dfg_users[id]
        .iter()
        .all(|&user| loop_isloopuse(code, dfg_users, isloop, user))
    {
        isloop.insert(id);
        true
    } else {
        false
    }
}

fn loop_checkpinuse(
    code: &IndexSlice<InsId, Ins>,
    isloop: &mut IndexSet<InsId>,
    dfg_users: &Relation<InsId, InsId>,
    mut body: InsId,
    tail: InsId
) -> bool {
    loop {
        for &user in &dfg_users[body] {
            if code[user].opcode().is_pinned() && !loop_isloopuse(code, dfg_users, isloop, user) {
                return false
            }
        }
        if body == tail {
            return true
        }
        body = code[body].decode_C();
    }
}

fn loop_checkphiuse(
    code: &IndexSlice<InsId, Ins>,
    blocks: &IndexSlice<BlockId, BlockData>,
    isloop: &IndexSet<InsId>,
    isloopphi: &IndexSet<PhiId>,
    dfg_users: &Relation<InsId, InsId>
) -> bool {
    for &BlockData { ctr, .. } in &blocks.raw {
        if !isloop.contains(ctr) {
            for &user in &dfg_users[ctr] {
                let ins = code[user];
                if ins.opcode() == Opcode::PHI {
                    let (_, phi) = ins.decode_PHI();
                    if isloopphi.contains(phi) {
                        return false
                    }
                }
            }
        }
    }
    return true
}

fn loop_run(
    code: &mut IndexSlice<InsId, Ins>,
    blocks: &IndexSlice<BlockId, BlockData>,
    isloop: &mut IndexSet<InsId>,
    isloopphi: &mut IndexSet<PhiId>,
    dfg_users: &mut Relation<InsId, InsId>
) {
    for &BlockData { ctr, .. } in &blocks.raw {
        let ins = code[ctr];
        if ins.opcode() != Opcode::IF { continue }
        for &branch in ins.controls() {
            isloop.clear();
            isloopphi.clear();
            // check (1a)
            if !loop_checkbody(code, isloop, isloopphi, branch, ctr) { continue }
            // check (1b): are all uses of pins inside the loop?
            if !loop_checkpinuse(code, isloop, dfg_users, branch, ctr) { continue }
            // check (1b): are all uses of phis inside the loop?
            if !loop_checkphiuse(code, blocks, isloop, isloopphi, dfg_users) { continue }
            // this IF is a side-effect-free loop. eliminate it.
            let (cond, tru, fal) = code[ctr].decode_IF();
            let dest = if branch == tru { fal } else { tru };
            let notdest = if branch == tru { tru } else { fal };
            trace!(OPTIMIZE "LOOP eliminate {:?} {:?}  =>  {:?}", ctr, code[ctr], dest);
            code[ctr] = Ins::GOTO(dest);
            dfg_users.remove(cond, ctr);
            dfg_users.remove(notdest, ctr);
            break
        }
    }
}

/* ---- PHI ----------------------------------------------------------------- */

// if a PHI...
// (1) is only written one value  -->  replace PHI with MOV
// (2) is never read  -->  replace JMP with GOTO

const PHI_NONE: InsId = zerocopy::transmute!(!0u16);
const PHI_MANY: InsId = zerocopy::transmute!(!1u16);

#[derive(Clone, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct PhiData {
    value: InsId,
    read: u16,
    new: IndexOption<PhiId>
}

fn phi_run(
    code: &mut IndexSlice<InsId, Ins>,
    phis: &mut IndexVec<PhiId, Phi>,
    blocks: &mut IndexSlice<BlockId, BlockData>,
    dfg_users: &mut Relation<InsId, InsId>,
    phi_data: &mut IndexSlice<PhiId, PhiData>,
    arg: PhiId
) {
    phi_data.raw.fill(PhiData { value: PHI_NONE, read: 0, new: None.into() });
    for i in index::iter_span(arg) {
        phi_data[i].new = Some(i).into();
    }
    for &BlockData { ctr, .. } in &blocks.raw {
        let ins = code[ctr];
        // check (1)
        if ins.opcode() == Opcode::JMP {
            let (value, _, phi) = ins.decode_JMP();
            match &mut phi_data[phi].value {
                v @ &mut PHI_NONE => *v = value,
                &mut PHI_MANY => {},
                v if *v == value => {},
                v => *v = PHI_MANY
            }
        }
        // check (2)
        for &user in &dfg_users[ctr] {
            let uins = code[user];
            if uins.opcode() == Opcode::PHI {
                let (_, phi) = uins.decode_PHI();
                phi_data[phi].read += 1;
            }
        }
    }
    if index::iter_range(arg..phis.end())
        .all(|p| phi_data[p].read > 0 && phi_data[p].value >= PHI_MANY)
    {
        // nothing to eliminate
        return
    }
    // compute new placements
    let mut cursor = arg;
    for p in index::iter_range(arg..phis.end()) {
        let data = &mut phi_data[p];
        // read>0 but value=PHI_NONE is possible here if an earlier pass nuked the writes,
        // the reads are now dead code. don't bother patching them, later passes or scheduling
        // will remove them.
        if data.read > 0 && data.value >= PHI_MANY {
            phis[cursor] = phis[p];
            data.new = Some(cursor).into();
            cursor += 1;
        } else {
            trace!(OPTIMIZE "PHI eliminate {:?}", p);
        }
    }
    phis.raw.truncate(cursor.into());
    for block in &mut blocks.raw {
        let ctr = block.ctr;
        let ins = &mut code[ctr];
        // patch (1)
        if ins.opcode() == Opcode::JMP {
            let (value, dest, phi) = ins.decode_JMP();
            match phi_data[phi].new.unpack() {
                Some(new) => *ins.phi_mut().unwrap() = new,
                None => {
                    trace!(OPTIMIZE "PHI patch jump {:?} {:?}", ctr, *ins);
                    *ins = Ins::GOTO(dest);
                    dfg_users.remove(value, ctr);
                }
            }
        }
        // patch (2)
        let mut u = 0;
        while let Some(&user) = dfg_users[ctr].get(u) {
            let uins = &mut code[user];
            if uins.opcode() == Opcode::PHI {
                let (_, phi) = uins.decode_PHI();
                match phi_data[phi] {
                    PhiData { new, .. } if new.is_some() => *uins.phi_mut().unwrap() = new.raw,
                    PhiData { value, .. } => {
                        trace!(OPTIMIZE "PHI patch read {:?} {:?}  =>  {:?}", user, uins, value);
                        block.pin -= 1;
                        dfg_users.remove(ctr, user);
                        dfg_users.add(value, user);
                        *uins = uins.set_opcode(Opcode::MOV).set_a(zerocopy::transmute!(value));
                        continue;
                    }
                }
            }
            u += 1;
        }
    }
}

/* ---- GOTO ---------------------------------------------------------------- */

// if a GOTO...
// (1) has no pins  -->  merge to successor
// (2) is the only precedessor of its successor  -->  merge to successor and move pins
// (3) has exactly one precedessor, the precedessor is not an IF or a JMP setting a PHI pinned
//     to this block -->  merge to precedessor and move pins

fn goto_run(
    code: &mut IndexSlice<InsId, Ins>,
    blocks: &mut IndexSlice<BlockId, BlockData>,
    ctr_data: &IndexSlice<InsId, InsData>,
    dfg_users: &mut Relation<InsId, InsId>
) {
    'blocks: for block in index::iter_span(blocks.end()) {
        let BlockData { ctr, pin } = blocks[block];
        let ins = code[ctr];
        if ins.opcode() == Opcode::GOTO {
            let succ = ins.decode_GOTO();
            let movepins: IndexOption<InsId> = 'pins: {
                // case (1)
                if pin == 0 {
                    break 'pins None
                }
                // case (2)
                if dfg_users[succ].len() == blocks[ctr_data[succ].block().unwrap()].pin as usize+1 {
                    break 'pins Some(succ)
                }
                // case (3)
                let users = &dfg_users[ctr];
                if users.len() == pin as usize + 1 {
                    let pred = users
                        .iter()
                        .cloned()
                        .find(|&i| code[i].opcode().is_control())
                        .unwrap();
                    match code[pred].opcode() {
                        Opcode::IF => continue 'blocks,
                        Opcode::JMP => {
                            let (_, _, phi) = code[pred].decode_JMP();
                            if users
                                .iter()
                                .any(|&i| code[i].opcode() == Opcode::PHI
                                    && code[i].decode_PHI().1 == phi)
                            {
                                continue 'blocks;
                            }
                        },
                        _ => {}
                    }
                    break 'pins Some(pred);
                }
                // else: it's not redundant
                continue 'blocks
            }.into();
            // remove GOTO.
            trace!(OPTIMIZE "GOTO eliminate {:?} {:?}", ctr, ins);
            blocks[block].pin = 0;
            let succ = code[ctr].decode_C();
            code[ctr] = code[ctr].set_opcode(Opcode::NOP);
            dfg_users.remove(succ, ctr);
            while let Some(&user) = dfg_users[ctr].get(0) {
                let uins = &mut code[user];
                let repl = if uins.opcode().is_pinned() {
                    let mp = movepins.unwrap();
                    blocks[ctr_data[mp].block().unwrap()].pin += 1;
                    mp
                } else {
                    succ
                };
                for c in uins.controls_mut() { if *c == ctr { *c = repl; } }
                dfg_users.remove(ctr, user);
                dfg_users.add(repl, user);
            }
        }
    }
}

/* ---- CCP ----------------------------------------------------------------- */

fn fact2fix(fact: FactId) -> FixId {
    let fact: usize = fact.into();
    (fact>>1).into()
}

fn fix2fact(fix: FixId) -> FactId {
    let fix: usize = fix.into();
    (fix<<1).into()
}

fn fact2branch(fact: FactId) -> bool {
    let fact: usize = fact.into();
    fact & 1 == 0
}

fn ccp_collect(
    code: &IndexSlice<InsId, Ins>,
    blocks: &IndexSlice<BlockId, BlockData>,
    ins_data: &mut IndexSlice<InsId, InsData>,
    fix_ins: &mut IndexArray<FixId, InsId, MAX_CCPFIX>,
    fixed: &mut IndexSet<InsId>,
    dfg_users: &Relation<InsId, InsId>
) -> usize {
    fixed.clear();
    let mut numfix = 0usize;
    for &BlockData { ctr, .. } in &blocks.raw {
        let ins = code[ctr];
        if ins.opcode() != Opcode::IF { continue }
        let cond = ins.decode_V();
        if fixed.contains(cond) { continue }
        if dfg_users[cond].len() > 1
            || (ins_matches!(code, code[cond]; (EQ|NE) _ const)
                && dfg_users[code[cond].decode_V()].len() > 1)
        {
            let fact = fix2fact(numfix.into());
            trace!(OPTIMIZE "CCP fix #{} ins={:?} facts={:?},{:?}", numfix, cond, fact, fact+1);
            fix_ins[numfix.into()] = cond;
            *ins_data[cond].fact_mut() = fact;
            fixed.insert(cond);
            numfix += 1;
            if numfix == MAX_CCPFIX { break }
        }
    }
    numfix
}

fn ccp_init(
    code: &IndexSlice<InsId, Ins>,
    blocks: &IndexSlice<BlockId, BlockData>,
    blocks_ccp: &mut IndexSlice<BlockId, CCPBlock>,
    ins_data: &IndexSlice<InsId, InsData>,
    fixed: &IndexSet<InsId>,
    dfg_users: &Relation<InsId, InsId>
) -> usize {
    let mut numfactblock = 0;
    for (id, &BlockData { ctr, .. }) in blocks.pairs() {
        let mut fact_bit: BitmapWord<FactId> = Default::default();
        'ok: {
            'fail: {
                for &user in &dfg_users[ctr] {
                    let uins = code[user];
                    match uins.opcode() {
                        Opcode::IF => {
                            let (cond, tru, fal) = uins.decode_IF();
                            if tru == fal { break 'fail; }
                            if !fixed.contains(cond) { break 'fail; }
                            let mut f_bit: BitmapWord<FactId> = Default::default();
                            f_bit |= *ins_data[cond].fact() + (ctr == fal) as isize;
                            if f_bit == fact_bit {
                                // OK.
                            } else if fact_bit.is_empty() {
                                fact_bit = f_bit;
                            } else {
                                break 'fail;
                            }
                        },
                        op if op.is_control() => break 'fail,
                        _ => continue
                    }
                }
                break 'ok;
            }
            fact_bit = Default::default();
        }
        blocks_ccp[id].branch = fact_bit;
        blocks_ccp[id].fix = fact_bit;
        if !fact_bit.is_empty() {
            trace!(OPTIMIZE "CCP block {:?}/{:?} initial facts: {:?}", id, ctr, fact_bit);
            numfactblock += 1;
        }
    }
    numfactblock
}

fn ccp_propagate(
    code: &IndexSlice<InsId, Ins>,
    blocks: &IndexSlice<BlockId, BlockData>,
    blocks_ccp: &mut IndexSlice<BlockId, CCPBlock>,
    ins_data: &IndexSlice<InsId, InsData>,
    dfg_users: &Relation<InsId, InsId>
) {
    loop {
        let mut fixpoint = true;
        for (id, &BlockData { ctr, .. }) in blocks.pairs().skip(1) {
            let mut w: BitmapWord<FactId> = BitmapWord::ones();
            for &user in &dfg_users[ctr] {
                if code[user].opcode().is_control() {
                    if let Some(block) = ins_data[user].block().unpack() {
                        w &= blocks_ccp[block].fix;
                    }
                }
            }
            w |= blocks_ccp[id].branch;
            if w != blocks_ccp[id].fix {
                fixpoint = false;
                blocks_ccp[id].fix = w;
            }
        }
        if fixpoint { break }
    }
}

fn ccp_patchins(
    code: &mut IndexVec<InsId, Ins>,
    ins_data: &IndexSlice<InsId, InsData>,
    fixed: &IndexSet<InsId>,
    id: InsId,
    depth: usize
) -> IndexOption<InsId> {
    if depth == 0 {
        return None.into();
    }
    if fixed.contains(id) {
        return Some(match *ins_data[id].fix() {
            FIX_FALSE => {
                trace!(OPTIMIZE "CCP constify {:?} -> TRUE", id);
                code.push(Ins::KINT(Type::B1, 0))
            },
            FIX_TRUE => {
                trace!(OPTIMIZE "CCP constify {:?} -> FALSE", id);
                code.push(Ins::KINT(Type::B1, 1))
            },
            new => {
                trace!(OPTIMIZE "CCP constify {:?} -> {:?}", id, new);
                new
            }
        }).into();
    }
    let mut ins = code[id];
    for v in ins.inputs_mut() {
        if let Some(new) = ccp_patchins(code, ins_data, fixed, *v, depth-1).unpack() {
            *v = new;
        }
    }
    match ins == code[id] { true => None, false => Some(code.push(ins)) }.into()
}

fn ccp_patch(
    code: &mut IndexVec<InsId, Ins>,
    blocks: &IndexSlice<BlockId, BlockData>,
    blocks_ccp: &IndexSlice<BlockId, CCPBlock>,
    ins_data: &mut IndexSlice<InsId, InsData>,
    fix_ins: &IndexArray<FixId, InsId, MAX_CCPFIX>,
    fixed: &mut IndexSet<InsId>
) {
    for (&BlockData { ctr, .. }, &CCPBlock { fix, .. }) in zip(&blocks.raw, &blocks_ccp.raw) {
        // all ones -> block is unreachable
        if fix.is_empty() || fix == BitmapWord::ones() { continue }
        let mut ins = code[ctr];
        if ins.opcode().num_v() == 0 { continue }
        fixed.clear();
        for fact in fix.ones() {
            let cond = fix_ins[fact2fix(fact)];
            let branch = fact2branch(fact);
            *ins_data[cond].fix_mut() = if branch { FIX_TRUE } else { FIX_FALSE };
            fixed.insert(cond);
            let cond_ins = code[cond];
            if cond_ins.opcode() == if branch { Opcode::EQ } else { Opcode::NE } {
                let (left, right) = cond_ins.decode_VV();
                if code[right].opcode().is_const() {
                    *ins_data[left].fix_mut() = right;
                    fixed.insert(left);
                }
            }
        }
        for v in ins.inputs_mut() {
            if let Some(new) = ccp_patchins(code, ins_data, fixed, *v, MAX_CCPDEPTH).unpack() {
                *v = new;
            }
        }
        if ins != code[ctr] {
            trace!(OPTIMIZE "CCP rewrite {:?}", ctr);
            code[ctr] = ins;
        }
    }
}

fn ccp_run(
    code: &mut IndexVec<InsId, Ins>,
    blocks: &IndexSlice<BlockId, BlockData>,
    blocks_ccp: &mut IndexSlice<BlockId, CCPBlock>,
    ins_data: &mut IndexSlice<InsId, InsData>,
    fix_ins: &mut IndexArray<FixId, InsId, MAX_CCPFIX>,
    fixed: &mut IndexSet<InsId>,
    dfg_users: &mut Relation<InsId, InsId>
) {
    if ccp_collect(code, blocks, ins_data, fix_ins, fixed, dfg_users) == 0 { return }
    if ccp_init(code, blocks, blocks_ccp, ins_data, fixed, dfg_users) == 0 { return }
    ccp_propagate(code, blocks, blocks_ccp, ins_data, dfg_users);
    ccp_patch(code, blocks, blocks_ccp, ins_data, fix_ins, fixed);
}

/* -------------------------------------------------------------------------- */

fn scancontrol(
    bump: &mut Bump<BlockData>,
    blocks_start: BumpRef<BlockData>,
    code: &IndexSlice<InsId, Ins>,
    ctr_data: BumpRef<IndexSlice<InsId, InsData>>,
    visited: &mut IndexSet<InsId>,
    id: InsId
) {
    if visited.test_and_set(id) {
        return
    }
    let block = bump.push(BlockData { ctr: id, pin: 0 });
    *bump[ctr_data.elem(id)].block_mut() = Some((block.index() - blocks_start.index()).into()).into();
    for &c in code[id].controls() {
        scancontrol(bump, blocks_start, code, ctr_data, visited, c);
    }
}

fn scandata(
    code: &IndexSlice<InsId, Ins>,
    blocks: &mut IndexSlice<BlockId, BlockData>,
    iscontrol: &IndexSet<InsId>,
    ctr_data: &mut IndexSlice<InsId, InsData>,
    dfg_users: &mut Relation<InsId, InsId>
) {
    dfg_users.clear();
    for (id, &ins) in code.pairs() {
        dfg_users.add_reverse(ins.inputs_and_controls(), id);
        if ins.opcode().is_control() && !iscontrol.contains(id) {
            *ctr_data[id].block_mut() = None.into();
        } else if ins.opcode().is_pinned() {
            let c = ins.decode_C();
            if iscontrol.contains(c) {
                blocks[ctr_data[c].block().unwrap()].pin += 1;
            }
        }
    }
}

pub fn run(ocx: &mut Ocx, fid: FuncId) {
    trace!(OPTIMIZE "CONTROL {:?}", fid);
    let opt = &mut *ocx.data;
    let func = &mut ocx.ir.funcs[fid];
    let code = func.code.inner_mut();
    let base = ocx.tmp.end();
    let (insdata_ptr, _) = ocx.tmp.reserve_dst::<IndexSlice<InsId, InsData>>(code.raw.len());
    let (phi_ptr, _) = ocx.tmp.reserve_dst::<IndexSlice<PhiId, PhiData>>(func.phis.end().into());
    let (fixins_ptr, _) = ocx.tmp.reserve::<IndexArray<FixId, InsId, MAX_CCPFIX>>();
    let blocks = ocx.tmp.align_for::<BlockData>();
    let blocks_start = blocks.end();
    ocx.mark1.clear();
    scancontrol(blocks, blocks_start, code, insdata_ptr, &mut ocx.mark1, func.entry);
    let blocks_num = blocks.end().index() - blocks_start.index();
    let (ccp_ptr, _) = ocx.tmp.reserve_dst::<IndexSlice<BlockId, CCPBlock>>(blocks_num);
    let (data, blocks_ccp) = ocx.tmp.get_dst_mut_split(ccp_ptr, blocks_num);
    let (data, blocks) = data.get_dst_mut_split(blocks_start.cast(), blocks_num);
    let (data, fix_ins) = data.get_mut_split(fixins_ptr);
    let (data, phi_data) = data.get_dst_mut_split(phi_ptr, func.phis.end().into());
    let ins_data = data.get_dst_mut(insdata_ptr, code.raw.len());
    scandata(code, blocks, &ocx.mark1, ins_data, &mut opt.cf.dfg_users);
    if ocx.flags.contains(OptFlag::IFCHAIN) {
        ifchain_run(code, &mut opt.cf.dfg_users, blocks, ins_data);
    }
    if ocx.flags.contains(OptFlag::SWITCH) {
        switch_run(code, blocks, &mut ocx.mark1, &mut ocx.mark2, &mut opt.cf.dfg_users);
    }
    if ocx.flags.contains(OptFlag::LOOP) {
        loop_run(code, blocks, &mut ocx.mark1, &mut opt.phi_mark, &mut opt.cf.dfg_users);
    }
    if ocx.flags.contains(OptFlag::PHI) {
        phi_run(code, func.phis.inner_mut(), blocks, &mut opt.cf.dfg_users, phi_data, func.arg);
    }
    if ocx.flags.contains(OptFlag::GOTO) {
        goto_run(code, blocks, ins_data, &mut opt.cf.dfg_users);
        while code[func.entry].opcode() == Opcode::NOP {
            func.entry = zerocopy::transmute!(code[func.entry].a());
        }
    }
    if ocx.flags.contains(OptFlag::CCP) {
        // CCP must run last because it adds new instructions and doesn't maintain dfg.
        ccp_run(code, blocks, blocks_ccp, ins_data, fix_ins, &mut ocx.mark1, &mut opt.cf.dfg_users);
    }
    ocx.tmp.truncate(base);
}
