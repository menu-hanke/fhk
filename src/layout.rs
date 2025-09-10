//! Memory layout.

use core::cmp::max;
use core::iter::{repeat_n, zip};
use core::mem::swap;
use core::ops::Range;

use crate::bitmap::{BitMatrix, Bitmap, BitmapWord};
use crate::bump::{self, Bump, BumpPtr, BumpRef};
use crate::compile::{self, Ccx, Stage};
use crate::image::{BreakpointId, Instance};
use crate::index::{self, index, IndexSlice, IndexVec, InvalidValue};
use crate::intern::Interned;
use crate::ir::{Func, FuncId, FuncKind, Opcode, Type};
use crate::mem::{BitOffset, Chunk, Offset, ParamId, Query, QueryId, ResetId, SizeClass};
use crate::support::DynSlot;
use crate::trace::trace;
use crate::typestate::Absent;

// TODO: the proper way to do size classes is to do dataflow analysis on CINIT instructions
// TODO: query bitmap slots should never be dup'ed

// TODO: CINITs of chunks that have a pointer (in particular CINITs of dynamic chunks)
//       don't need a separate bitmap, just check the pointer

/*
 * vmctx memory layout:
 *   --> vmctx pointer (pinned register in compiled code)
 *   [ struct Instance ]
 *   [ static segment ]                              <- never explicitly reset
 *   --> first breakpoint
 *   [ mask segment ]                                <- masked on instance creation
 *   --> last breakpoint
 *   [ query segment (slots overlapped) ]            <- zeroed on query
 *   [ parameter segment (slots overlapped) ]        <- zeroed on query
 *   --> vmctx_size
 */

index!(struct SlotId(u32) invalid(!0));

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SlotType {
    Data,
    Bitmap,
    BitmapDup
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Segment {
    Static,
    Mask,
    Query
}

struct SlotDef {
    owner: FuncId,
    loc: BitOffset,
    size: u8, // also alignment, pointer size for dynamic slots
    sty: SlotType,
    seg: Segment
}

#[derive(Default)]
pub struct ComputeLayout {
    slots: IndexVec<SlotId, SlotDef>,
    func_quse: BitMatrix<FuncId, QueryId>,    // does the query call the function?
    param_quse: BitMatrix<ParamId, QueryId>,  // does the query use the parameter?
}

fn computequse(ccx: &mut Ccx<ComputeLayout>) {
    let mut func_puse: BitMatrix<FuncId, ParamId> = Default::default();
    func_puse.resize(ccx.ir.funcs.end(), ccx.layout.params.end());
    ccx.data.func_quse.resize(ccx.ir.funcs.end(), ccx.layout.queries.end());
    ccx.data.param_quse.resize(ccx.layout.params.end(), ccx.layout.queries.end());
    let base = ccx.tmp.end();
    let (query_func, _) = ccx.tmp.reserve_dst::<IndexSlice<QueryId, FuncId>>(
        ccx.layout.queries.raw.len());
    let constraints: &mut Bump<[FuncId;2]> = ccx.tmp.align_for();
    let constraints_base = constraints.end();
    for (fid,f) in ccx.ir.funcs.pairs() {
        if let FuncKind::Query(qid) = f.kind {
            ccx.data.func_quse[fid].set(qid);
            constraints[query_func.elem(qid)] = fid;
        }
        for (_,ins) in f.code.pairs() {
            match ins.opcode() {
                Opcode::CALL|Opcode::CALLC|Opcode::CALLCI => {
                    constraints.push([ins.decode_F(), fid]);
                },
                Opcode::CINIT => {
                    let g = ins.decode_F();
                    constraints.extend([[fid,g],[g,fid]]);
                },
                Opcode::QLOAD => {
                    let (param, _) = ins.decode_QLOAD();
                    func_puse[fid].set(param);
                },
                _ => {}
            }
        }
    }
    let constraints = &mut constraints[constraints_base..];
    // f calls g -> puse(g) ⊂ puse(f)
    func_puse.solve(constraints);
    // f calls g -> quse(f) ⊂ quse(g)
    for [f,g] in &mut *constraints {
        swap(f, g);
    }
    ccx.data.func_quse.solve(constraints);
    for (qid,&fid) in ccx.tmp.get_dst(query_func, ccx.layout.queries.raw.len()).pairs() {
        let puse = &func_puse[fid];
        for p in puse {
            ccx.data.param_quse[p].set(qid);
            ccx.layout.query_params.push(p);
        }
        ccx.layout.queries[qid].params_end = ccx.layout.query_params.len() as _;
    }
    ccx.tmp.truncate(base);
}

fn slotsize(scl: SizeClass, type_: Type) -> usize {
    if scl.is_dynamic() { Type::PTR } else { type_ }.size()
}

fn collectslots(ccx: &mut Ccx<ComputeLayout>) {
    // order must match save
    for (fid, func) in ccx.ir.funcs.pairs() {
        if !matches!(func.kind, FuncKind::Chunk(_)) { continue }
        let mut hasptr = false;
        let isquery = ccx.intern[func.reset][0].test(ResetId::QUERY);
        for phi in index::iter_range(func.returns()) {
            let ty = func.phis.at(phi).type_;
            if ty != Type::FX {
                ccx.data.slots.push(SlotDef {
                    owner: fid,
                    loc: Default::default(),
                    size: slotsize(func.scl, ty) as _,
                    sty: match ty {
                        Type::B1 => SlotType::Bitmap,
                        _ => SlotType::Data
                    },
                    seg: if isquery {
                        Segment::Query
                    } else if func.scl.is_dynamic() || (Type::B1|Type::PTR).contains(ty) {
                        // TODO: even if it's dynamic, secondary pointers can go in static
                        // (or all pointers if CINIT has a check bitmap)
                        Segment::Mask
                    } else {
                        Segment::Static
                    }
                });
                hasptr |= ty == Type::PTR;
            }
        }
        ccx.data.slots.push(SlotDef {
            owner: fid,
            loc: Default::default(),
            size: slotsize(func.scl, Type::B1) as _,
            sty: if hasptr && func.scl.is_dynamic() && !isquery {
                SlotType::BitmapDup
            } else {
                SlotType::Bitmap
            },
            seg: if isquery {
                Segment::Query
            } else {
                Segment::Mask
            }
        });
    }
}

// pushes sorted slot ids on ccx.tmp.
// sort order:
//   (1) segment
//   (2) mask segment: reset mask (arbitrary order)
//       query segment: owner chunk query popcount, large->small
//   (3) size class (arbitrary order)
//   (4) slot size, large->small
//   (5) slot type (arbitrary order)
fn sortslots(ccx: &mut Ccx<ComputeLayout>) {
    let base = ccx.tmp.extend(index::iter_span(ccx.data.slots.end()));
    ccx.tmp[base..].sort_unstable_by_key(|&i| {
        let slot = &ccx.data.slots[i];
        let owner = &ccx.ir.funcs[slot.owner];
        let sort2: u32 = match slot.seg {
            Segment::Static => 0,
            Segment::Mask => zerocopy::transmute!(owner.reset),
            Segment::Query => !ccx.data.func_quse[slot.owner].popcount()
        };
        let scl: u32 = zerocopy::transmute!(owner.scl);
        (slot.seg, sort2, scl, !slot.size, slot.sty)
    });
}

fn countseg(slots: &[SlotDef]) -> [usize; 3] {
    let mut count = [0; 3];
    for &SlotDef { seg, .. } in slots {
        count[seg as usize] += 1;
    }
    count
}

fn layoutstatic(
    ccx: &mut Ccx<ComputeLayout>,
    order: Range<BumpRef<SlotId>>,
    cursor: Offset
) -> Offset {
    let mut cursor = BitOffset::new_byte(cursor);
    let mut previd: SlotId = SlotId::INVALID.into();
    let mut sc = SizeClass::INVALID;
    for &id in &ccx.tmp[order] {
        let SlotDef { owner, size, sty, .. } = ccx.data.slots[id];
        let Func { scl, .. } = ccx.ir.funcs[owner];
        if cursor.bit() != 0 && (scl != sc || sty == SlotType::Data) {
            // size class or data type changed mid-bitfield: close bitfield
            cursor = cursor.next_byte(ccx.data.slots[previd].size as _);
            sc = scl;
        }
        if cursor.bit() == 0 {
            cursor = cursor.align_byte(size as _);
        } else {
            debug_assert!(cursor.byte() & (size as Offset - 1) == 0);
        }
        ccx.data.slots[id].loc = cursor;
        if sty != SlotType::Data {
            cursor = cursor.next_bit_in_byte_wrapping();
        }
        if cursor.bit() == 0 {
            cursor = cursor.next_byte(size as _);
        }
        previd = id;
    }
    cursor.align_byte(8).byte()
}

fn putbreakpoint(
    ccx: &mut Ccx<ComputeLayout>,
    breakpoint: BreakpointId,
    reset: Interned<[BitmapWord<ResetId>]>
) {
    for r in Bitmap::from_words(&ccx.intern[reset]) {
        ccx.layout.resets[r].mask.set(breakpoint);
    }
}

fn layoutreset(
    ccx: &mut Ccx<ComputeLayout>,
    order: Range<BumpRef<SlotId>>,
    cursor: Offset
) -> Offset {
    let mut cursor = BitOffset::new_byte(cursor);
    let mut rs: Interned<[BitmapWord<ResetId>]> = Interned::EMPTY;
    let mut sc = SizeClass::INVALID;
    let mut bt = SlotType::Data;
    let mut bpid: BreakpointId = 0.into();
    for pid in bump::iter_range(order.clone()) {
        let id = ccx.tmp[pid];
        let SlotDef { owner, size, sty, .. } = ccx.data.slots[id];
        let Func { reset, scl, .. } = ccx.ir.funcs[owner];
        if (rs, sc, sty) != (reset, scl, bt) {
            if cursor.bit() != 0 {
                // reset, size class, or type changed mid-bitfield: close bitfield
                cursor = cursor.next_byte(ccx.data.slots[ccx.tmp[pid.offset(-1)]].size as _);
            }
            sc = scl;
        }
        if rs != reset {
            // reset changed, begin new interval
            // TODO: handle bpid>64, merge some intervals
            ccx.image.breakpoints[bpid] = cursor.byte();
            putbreakpoint(ccx, bpid, reset);
            bpid += 1;
            rs = reset;
        }
        // align cursor
        if cursor.bit() == 0 {
            cursor = cursor.align_byte(size as _);
        } else {
            debug_assert!(cursor.byte() & (size as Offset - 1) == 0);
        }
        ccx.data.slots[id].loc = cursor;
        if sty != SlotType::Data {
            // if we are allocating a bitfield, increment bit.
            // if this wraps, the next `if` will increment the byte.
            cursor = cursor.next_bit_in_byte_wrapping();
            bt = sty;
        }
        if cursor.bit() == 0 {
            cursor = cursor.next_byte(size as _);
            bt = SlotType::Data;
        }
    }
    cursor = cursor.align_byte(8);
    ccx.image.breakpoints[bpid] = cursor.byte();
    cursor.byte()
}

fn qalloc_put(
    tmp: &mut BumpPtr,
    queries: &mut IndexSlice<QueryId, Query>,
    cursors: BumpRef<IndexSlice<QueryId, BitOffset>>,
    size: Offset,
    sty: SlotType,
    quse: &Bitmap<QueryId>
) -> BitOffset {
    let pos = quse
        .ones()
        .map(|qid| {
            let pos = tmp[cursors.elem(qid)];
            match sty {
                SlotType::Data => pos.align_byte(size as _),
                SlotType::Bitmap => pos.align_byte_bit(size as _),
                SlotType::BitmapDup => unreachable!()
            }
        })
        .max()
        .unwrap();
    let end = match sty { SlotType::Data => pos.next_byte(size), _ => pos.next_bit() };
    for q in quse {
        if queries[q].vmctx_start == 0 {
            queries[q].vmctx_start = pos.byte();
        }
        tmp[cursors.elem(q)] = end;
    }
    pos
}

fn layoutquery(
    ccx: &mut Ccx<ComputeLayout>,
    order: Range<BumpRef<SlotId>>,
    cursor: Offset
) -> Offset {
    let base = ccx.tmp.end();
    // create at least 1 cursor, even if there are no queries, so that the allocator doesn't
    // crash when no queries are defined
    let cursors = ccx.tmp.extend(repeat_n(BitOffset::new_byte(cursor),
       max(ccx.layout.queries.raw.len(), 1))).cast();
    for pid in bump::iter_range(order) {
        let id = ccx.tmp[pid];
        let SlotDef { owner, size, sty, .. } = ccx.data.slots[id];
        ccx.data.slots[id].loc = qalloc_put(&mut ccx.tmp, &mut ccx.layout.queries, cursors,
            size as _, sty, &ccx.data.func_quse[owner]);
    }
    #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
    struct ParamDef {
        id: ParamId,
        pop: u16,
        size: u16, // 0xffff->check
    }
    let params = ccx.tmp.extend(
        zip(ccx.data.param_quse.pairs(), &ccx.layout.params.raw)
        .flat_map(|((id,queries), param)| {
            let pop = queries.popcount() as u16;
            [
                ParamDef { id, pop, size: 0xffff },
                ParamDef { id, pop, size: param.size as _}
            ]
        }
    ));
    ccx.tmp[params..].sort_unstable_by_key(|p| (!p.pop, !p.size));
    for pd in bump::iter_range(params..ccx.tmp.end().cast()) {
        let ParamDef { id, size, .. } = ccx.tmp[pd];
        let loc = qalloc_put(&mut ccx.tmp, &mut ccx.layout.queries, cursors,
            if size == 0xffff { 1 } else { size as _ }, SlotType::Data, &ccx.data.param_quse[id]);
        let param = &mut ccx.layout.params[id];
        if size == 0xffff {
            param.check = loc;
        } else {
            param.value = loc;
        }
    }
    let cursors = ccx.tmp.get_dst(cursors, ccx.layout.queries.raw.len());
    let mut end = 0;
    for (query,&cursor) in zip(&mut ccx.layout.queries.raw, &cursors.raw) {
        let qend = cursor.align_byte(1).byte();
        end = max(end, qend);
        if query.vmctx_start > 0 {
            query.vmctx_end = qend;
        }
    }
    ccx.tmp.truncate(base);
    (end + 7) & !7
}

fn saveslots(ccx: &mut Ccx<ComputeLayout>) {
    let insert = ccx.perm.align_for::<BitOffset>();
    let mut slot: SlotId = 0.into();
    // order must match collect
    for func in &mut ccx.ir.funcs.raw {
        let FuncKind::Chunk(cidp) = &mut func.kind else { continue };
        let mut dynslots = 0;
        if func.scl.is_dynamic() {
            // alloc dynamic slot data for CINIT
            dynslots = ccx.image.mcode.align_data_for::<DynSlot>();
            let mut ds = slot;
            for phi in index::iter_span(func.ret) {
                let ty = func.phis.at(phi).type_;
                if ty != Type::FX {
                    let SlotDef { loc, sty, .. } = ccx.data.slots[ds];
                    let dslot = match sty {
                        SlotType::Data => DynSlot::new_data(loc.byte(), ty.size() as _),
                        _ => DynSlot::new_bitmap(loc.byte(), false, loc.bit())
                    };
                    ccx.image.mcode.write_data(&dslot);
                    ds += 1;
                }
            }
            let SlotDef { loc, sty, .. } = ccx.data.slots[ds];
            ccx.image.mcode.write_data(
                &DynSlot::new_bitmap(loc.byte(), sty == SlotType::BitmapDup, loc.bit()));
        }
        // alloc vmctx slots (fx slots don't matter, they will never be read/written)
        let slots = insert.end().cast();
        for phi in index::iter_span(func.ret) {
            insert.push(match func.phis.at(phi).type_ {
                Type::FX => Default::default(),
                _ => {
                    let s = ccx.data.slots[slot].loc;
                    slot += 1;
                    s
                }
            });
        }
        let check = ccx.data.slots[slot].loc;
        *cidp = ccx.layout.chunks.push(Chunk { check, slots, dynslots });
        slot += 1;
    }
}

impl Stage for ComputeLayout {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Default::default())
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        let base = ccx.tmp.end();
        computequse(ccx);
        collectslots(ccx);
        let slots_start: BumpRef<SlotId> = ccx.tmp.end().cast_up();
        sortslots(ccx);
        let slots_end: BumpRef<SlotId> = ccx.tmp.end().cast();
        let segn = countseg(&ccx.data.slots.raw);
        let mut cursor = size_of::<Instance>() as Offset;
        trace!(MEM "{} static slots, start {}", segn[0], cursor);
        cursor = layoutstatic(ccx, slots_start..slots_start.add(segn[0]), cursor);
        trace!(MEM "{} mask slots, start {}", segn[1], cursor);
        cursor = layoutreset(ccx, slots_start.add(segn[0])..slots_start.add(segn[0]+segn[1]),
            cursor);
        trace!(MEM "{} query slots, start {}", segn[2], cursor);
        cursor = layoutquery(ccx, slots_start.add(segn[0]+segn[1])..slots_end, cursor);
        trace!(MEM "image size: {}", cursor);
        ccx.image.size = cursor as _;
        saveslots(ccx);
        ccx.tmp.truncate(base);
        if trace!(MEM) {
            crate::dump::dump_layout(ccx.erase());
            trace!("{}", core::str::from_utf8(&ccx.tmp[base..]).unwrap());
            ccx.tmp.truncate(base);
        }
        Ok(())
    }

}
