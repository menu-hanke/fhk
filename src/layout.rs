//! Memory layout.

use core::cmp::{max, min};
use core::iter::{repeat_n, zip};
use core::mem::swap;
use core::ops::Range;

use crate::bitmap::{BitMatrix, Bitmap, BitmapWord};
use crate::bump::{self, Bump, BumpPtr, BumpRef};
use crate::compile::{self, Ccx, Stage};
use crate::image::{BreakpointId, Instance};
use crate::index::{self, index, IndexSlice, IndexVec};
use crate::intern::Interned;
use crate::ir::{Func, FuncId, FuncKind, Opcode, Type};
use crate::mem::{BitOffset, Chunk, Offset, ParamId, Query, QueryId, ResetId, SizeClass};
use crate::runtime::DynSlot;
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
enum SlotData {
    Bytes(/*size:*/ Offset, /*align:*/ u8),
    Bits,
    BitsDup
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
    data: SlotData,
    seg: Segment
}

#[derive(Default)]
pub struct ComputeLayout {
    slots: IndexVec<SlotId, SlotDef>,
    func_quse: BitMatrix<FuncId, QueryId>,    // does the query call the function?
    param_quse: BitMatrix<ParamId, QueryId>,  // does the query use the parameter?
}

impl SlotData {

    fn element_align(self) -> usize {
        match self {
            Self::Bytes(_, align) => align as _,
            _ => 1
        }
    }

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
    // crate::trace::trace!("func_quse:\n{:?}", ccx.data.func_quse);
    // collect query parameters
    for (qid,&fid) in ccx.tmp.get_dst(query_func, ccx.layout.queries.raw.len()).pairs() {
        let puse = &func_puse[fid];
        for p in puse {
            ccx.data.param_quse[p].set(qid);
            ccx.layout.query_params.push(p);
        }
        ccx.layout.queries[qid].params_end = ccx.layout.query_params.len() as _;
    }
    // demote functions to query-dependent if:
    // (1) the function is only called by one query; and
    // (2) the function has the exact same reset set as the query; and
    // (3) the query has no parameters
    let tmp_words = (ccx.layout.resets.raw.len() + BitmapWord::BITS - 1) / BitmapWord::BITS;
    let (tmp_bitmap, _) = ccx.tmp.reserve_dst::<[BitmapWord<ResetId>]>(tmp_words);
    for (fid,queries) in ccx.data.func_quse.pairs() {
        let func = &ccx.ir.funcs[fid];
        if matches!(func.kind, FuncKind::Chunk(_)) && queries.popcount() == 1 {
            let qfid = ccx.tmp[query_func.elem(queries.ffs().unwrap())];
            if func.reset == ccx.ir.funcs[qfid].reset {
                let tmp_bitmap = ccx.tmp.get_dst_mut(tmp_bitmap, tmp_words);
                tmp_bitmap.copy_from_slice(&ccx.intern[func.reset]);
                tmp_bitmap[0].set(ResetId::QUERY);
                ccx.ir.funcs[fid].reset = ccx.intern.intern(tmp_bitmap);
            }
        }
    }
    for qid in index::iter_span(ccx.layout.queries.end()) {
        let func = &mut ccx.ir.funcs[ccx.tmp[query_func.elem(qid)]];
        let reset = &ccx.intern[func.reset];
        if !reset[0].test(ResetId::QUERY) {
            let tmp_bitmap = ccx.tmp.get_dst_mut(tmp_bitmap, tmp_words);
            tmp_bitmap.copy_from_slice(reset);
            tmp_bitmap[0].set(ResetId::QUERY);
            func.reset = ccx.intern.intern(tmp_bitmap);
        }
    }
    ccx.tmp.truncate(base);
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
                    data: match ty {
                        Type::B1 => SlotData::Bits,
                        _ => SlotData::Bytes(ty.size() as _, ty.size() as _)
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
            data: if hasptr && func.scl.is_dynamic() && !isquery {
                SlotData::BitsDup
            } else {
                SlotData::Bits
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
//   (1) segment: static->mask->query
//   (2) mask segment: reset mask (arbitrary order)
//       query segment: owner chunk query popcount, large->small
//   (3) size class, dynamic->static
//   (4) slot alignment, large->small
//   (5) datatype (arbitrary order)
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
        let align = if owner.scl.is_dynamic() {
            Type::PTR.size()
        } else {
            slot.data.element_align()
        };
        let scl: u32 = zerocopy::transmute!(owner.scl);
        (slot.seg, sort2, !scl, !align, slot.data)
    });
}

fn countseg(slots: &[SlotDef]) -> [usize; 3] {
    let mut count = [0; 3];
    for &SlotDef { seg, .. } in slots {
        count[seg as usize] += 1;
    }
    count
}

#[derive(Clone, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct LayoutCursor {
    scl: SizeClass,  // in bytes, only set while inside a bitfield (ofs.bit() > 0)
    ofs: BitOffset,  // next free
}

impl LayoutCursor {

    fn new(ofs: BitOffset) -> Self {
        Self { scl: SizeClass::INVALID, ofs }
    }

    fn close_bitfield(&mut self) {
        if self.ofs.bit() != 0 {
            let size = if self.scl.is_dynamic() {
                Type::PTR.size() as _
            } else {
                self.scl.static_size()
            };
            self.scl = SizeClass::INVALID;
            self.ofs = BitOffset::new_byte(self.ofs.byte() + size);
        }
    }

    fn next_byte(&mut self, size: Offset, align: Offset) -> BitOffset {
        self.close_bitfield();
        let byte = (self.ofs.byte() + align-1) & !(align-1);
        self.ofs = BitOffset::new_byte(byte + size);
        BitOffset::new_byte(byte)
    }

    fn next_bit(&mut self, scl: SizeClass) -> BitOffset {
        if scl != self.scl {
            self.close_bitfield();
        }
        let mut ofs = self.ofs;
        debug_assert!(ofs.bit() == 0 || scl.is_static()
            || ofs.byte() & (Type::PTR as Offset - 1) == 0);
        match ofs.bit() {
            0 => {
                // start new bitfield
                let mut byte = ofs.byte();
                if scl.is_dynamic() {
                    byte = (byte + Type::PTR.size() as Offset - 1)
                        & !(Type::PTR.size() as Offset - 1);
                }
                self.scl = scl;
                ofs = BitOffset::new_byte(byte);
                self.ofs = ofs.set_bit(1);
            },
            7 => {
                // finish full bitfield
                self.close_bitfield();
            },
            _ => {
                self.ofs = ofs.set_bit(ofs.bit()+1);
            }
        }
        ofs
    }

    fn next(&mut self, scl: SizeClass, data: SlotData) -> BitOffset {
        match data {
            SlotData::Bytes(_, _) if scl.is_dynamic() =>
                self.next_byte(Type::PTR.size() as _, Type::PTR.size() as _),
            SlotData::Bytes(size, align) =>
                self.next_byte(scl.static_size() * size, align as _),
            SlotData::Bits | SlotData::BitsDup => self.next_bit(scl)
        }
    }

}

fn layoutstatic(
    ccx: &mut Ccx<ComputeLayout>,
    order: Range<BumpRef<SlotId>>,
    cursor: &mut LayoutCursor
) {
    for &id in &ccx.tmp[order] {
        let &mut SlotDef { owner, data, ref mut loc, .. } = &mut ccx.data.slots[id];
        let Func { scl, .. } = ccx.ir.funcs[owner];
        *loc = cursor.next(scl, data);
    }
    cursor.close_bitfield();
}

fn layoutreset(
    ccx: &mut Ccx<ComputeLayout>,
    order: Range<BumpRef<SlotId>>,
    cursor: &mut LayoutCursor
) {
    let mut rs: Interned<[BitmapWord<ResetId>]> = Interned::EMPTY;
    let mut isdup = false;
    let mut bpid: BreakpointId = 0.into();
    for pid in bump::iter_range(order.clone()) {
        let id = ccx.tmp[pid];
        let &mut SlotDef { owner, data, ref mut loc, .. } = &mut ccx.data.slots[id];
        let Func { reset, scl, .. } = ccx.ir.funcs[owner];
        if rs != reset || isdup != (data == SlotData::BitsDup) {
            cursor.close_bitfield();
            isdup = data == SlotData::BitsDup;
        }
        if rs != reset {
            // reset changed, begin new interval
            // TODO: handle bpid>64, merge some intervals
            debug_assert!(cursor.ofs.bit() == 0);
            ccx.image.breakpoints[bpid] = cursor.ofs.byte();
            for r in Bitmap::from_words(&ccx.intern[reset]) {
                ccx.layout.resets[r].mask.set(bpid);
            }
            bpid += 1;
            rs = reset;
        }
        *loc = cursor.next(scl, data);
    }
    cursor.close_bitfield();
    ccx.image.breakpoints[bpid] = cursor.ofs.byte();
}

fn qalloc_put(
    tmp: &mut BumpPtr,
    queries: &mut IndexSlice<QueryId, Query>,
    quse: &Bitmap<QueryId>,
    cursors: BumpRef<IndexSlice<QueryId, LayoutCursor>>,
    scl: SizeClass,
    data: SlotData
) -> BitOffset {
    if quse.is_empty() {
        // dead slot, offset doesn't matter
        return BitOffset::new_byte(0);
    }
    let mut ofs = BitOffset::new_byte(0);
    let mut end = LayoutCursor::new(ofs);
    for qid in quse.ones() {
        let mut cursor = tmp[cursors.elem(qid)].clone();
        let o = cursor.next(scl, data);
        if o > ofs {
            debug_assert!(cursor.ofs > end.ofs);
            (ofs, end) = (o, cursor);
        }
    }
    for qid in quse.ones() {
        if queries[qid].vmctx_start == 0 {
            queries[qid].vmctx_start = ofs.byte();
        }
        tmp[cursors.elem(qid)] = end.clone();
    }
    ofs
}

fn layoutquery(
    ccx: &mut Ccx<ComputeLayout>,
    order: Range<BumpRef<SlotId>>,
    cursor: &mut LayoutCursor
) {
    let base = ccx.tmp.end();
    // create at least 1 cursor, even if there are no queries, so that the allocator doesn't
    // crash when no queries are defined
    let cursors = ccx.tmp.extend(repeat_n(cursor.clone(),
       max(ccx.layout.queries.raw.len(), 1))).cast();
    for pid in bump::iter_range(order) {
        let id = ccx.tmp[pid];
        let SlotDef { owner, data, .. } = ccx.data.slots[id];
        let Func { scl, .. } = ccx.ir.funcs[owner];
        ccx.data.slots[id].loc = qalloc_put(
            &mut ccx.tmp,
            &mut ccx.layout.queries,
            &ccx.data.func_quse[owner],
            cursors,
            scl,
            data
        );
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
        let loc = qalloc_put(
            &mut ccx.tmp,
            &mut ccx.layout.queries,
            &ccx.data.param_quse[id],
            cursors,
            SizeClass::GLOBAL,
            if size == 0xffff {
                SlotData::Bits
            } else {
                SlotData::Bytes(size as _, min(size as _, 8))
            }
        );
        let param = &mut ccx.layout.params[id];
        if size == 0xffff {
            param.check = loc;
        } else {
            param.value = loc;
        }
    }
    let cursors = ccx.tmp.get_dst(cursors, ccx.layout.queries.raw.len());
    for (query,qcur) in zip(&mut ccx.layout.queries.raw, &cursors.raw) {
        let mut end = qcur.clone();
        end.close_bitfield();
        if query.vmctx_start > 0 {
            query.vmctx_end = end.ofs.byte();
        }
        if end.ofs > cursor.ofs {
            *cursor = end;
        }
    }
    ccx.tmp.truncate(base);
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
                    let SlotDef { loc, data, .. } = ccx.data.slots[ds];
                    let dslot = match data {
                        SlotData::Bytes(..) => DynSlot::new_data(loc.byte(), ty.size() as _),
                        SlotData::Bits => DynSlot::new_bitmap(loc.byte(), false, loc.bit()),
                        SlotData::BitsDup => unreachable!()
                    };
                    ccx.image.mcode.write_data(&dslot);
                    ds += 1;
                }
            }
            let SlotDef { loc, data, .. } = ccx.data.slots[ds];
            ccx.image.mcode.write_data(
                &DynSlot::new_bitmap(loc.byte(), data == SlotData::BitsDup, loc.bit()));
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
        let mut cursor = LayoutCursor::new(BitOffset::new_byte(size_of::<Instance>() as _));
        trace!(MEM "{} static slots, start {}", segn[0], cursor.ofs.byte());
        layoutstatic(ccx, slots_start..slots_start.add(segn[0]), &mut cursor);
        trace!(MEM "{} mask slots, start {}", segn[1], cursor.ofs.byte());
        layoutreset(ccx, slots_start.add(segn[0])..slots_start.add(segn[0]+segn[1]), &mut cursor);
        trace!(MEM "{} query slots, start {}", segn[2], cursor.ofs.byte());
        layoutquery(ccx, slots_start.add(segn[0]+segn[1])..slots_end, &mut cursor);
        trace!(MEM "image size: {}", cursor.ofs.byte());
        debug_assert!(cursor.ofs.bit() == 0);
        ccx.image.size = cursor.ofs.byte();
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
