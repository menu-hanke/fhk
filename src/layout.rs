//! Memory layout.

use alloc::boxed::Box;

use crate::compile::{self, Ccx, Phase};
use crate::dump::dump_layout;
use crate::image::Instance;
use crate::index::{self, index, IndexSlice, IndexVec};
use crate::ir::{Bundle, FuncKind, Type};
use crate::mem::{BreakpointId, Offset, ResetSet, SizeClass, Slot};
use crate::obj::{Obj, ObjRef, RESET};
use crate::support::DynSlot;
use crate::trace::trace;
use crate::typestate::{Absent, R, RW};

index!(struct SlotId(u32));

struct SlotDef {
    reset: ResetSet,
    scl: SizeClass,
    size: u8, // also alignment, pointer size for dynamic slots
    bitmap: bool,
    value: Slot
}

#[derive(Default)]
pub struct ComputeLayout {
    slots: IndexVec<SlotId, SlotDef>,
}

type Ctx<'a> = Ccx<ComputeLayout, RW, R<'a>>;

fn newslot(reset: ResetSet, scl: SizeClass, type_: Type) -> SlotDef {
    debug_assert!(type_.size() > 0);
    SlotDef {
        reset,
        scl,
        size: match scl.is_dynamic() {
            true => Type::PTR.size(),
            false => type_.size()
        } as _,
        bitmap: type_ == Type::B1,
        value: Default::default()
    }
}

fn collect(ctx: &mut Ccx<ComputeLayout>) {
    // order must match save
    for func in &ctx.ir.funcs.raw {
        match &func.kind {
            &FuncKind::Bundle(Bundle { reset, scl, .. }) => {
                ctx.data.slots.push(newslot(reset, scl, Type::B1));
                for phi in index::iter_range(func.returns()) {
                    let ty = func.phis.at(phi).type_;
                    if ty != Type::FX {
                        ctx.data.slots.push(newslot(reset, scl, ty));
                    }
                }
            },
            _ => {}
        }
    }
}

// for each bundle:
//   * save slot information
//   * create dynamic slots for BINIT
fn save(ctx: &mut Ccx<ComputeLayout>) {
    let slotdefs: &IndexSlice<SlotId, SlotDef> = &ctx.data.slots;
    let insert = ctx.perm.align_for::<Slot>();
    let mut slot: SlotId = 0.into();
    // order must match collect
    for (fid, func) in ctx.ir.funcs.pairs_mut() {
        match &mut func.kind {
            FuncKind::Bundle(Bundle { scl, slots, dynslots, check, .. }) => {
                let bitmap = slotdefs[slot].value;
                *check = bitmap;
                *slots = insert.end();
                trace!(MEM "{:?} bitmap {:#04x}:{}", fid, bitmap.byte(), bitmap.bit());
                if scl.is_dynamic() {
                    // alloc dynamic slot data for BINIT
                    let base = slot;
                    *dynslots = ctx.mcode.data.bump().end().cast_up();
                    ctx.mcode.data.write(&DynSlot::new(bitmap.byte(), Type::B1));
                    for phi in index::iter_span(func.ret) {
                        let ty = func.phis.at(phi).type_;
                        if ty != Type::FX {
                            slot += 1;
                            let phislot = slotdefs[slot].value;
                            ctx.mcode.data.write(&DynSlot::new(phislot.byte(), ty));
                        }
                    }
                    slot = base;
                }
                slot += 1;
                // alloc vmctx slots (fx slots don't matter, they will never be read/written)
                for phi in index::iter_span(func.ret) {
                    insert.push(match func.phis.at(phi).type_ {
                        Type::FX => Default::default(),
                        ty => {
                            let s = slotdefs[slot].value;
                            trace!(MEM "{:?} {:?} {:#04x} {}", fid, phi, s.byte(), ty.name());
                            slot += 1;
                            s
                        }
                    });
                }
            },
            _ => {}
        }
    }
}

fn sort(ctx: &Ctx) -> Box<[SlotId]> {
    let mut order: Box<[SlotId]> = index::iter_span(ctx.data.slots.end()).collect();
    order.sort_unstable_by_key(|id| {
        let slot = &ctx.data.slots[*id];
        let reset: u64 = zerocopy::transmute!(slot.reset);
        let num: u32 = zerocopy::transmute!(slot.scl);
        // NOT reset here to put slots that are never reset last
        (!reset, num, !slot.size)
    });
    order
}

fn partition(ctx: &mut Ctx, order: &[SlotId]) -> IndexVec<BreakpointId, (ResetSet, Offset)> {
    let mut breakpoints: IndexVec<BreakpointId, (ResetSet, Offset)> = Default::default();
    let mut cursor = (size_of::<Instance>() as Offset, 0); // (byte, bit) of next slot
    let mut rs = ResetSet::default();
    let mut sc = SizeClass::INVALID;
    for (i, &id) in order.iter().enumerate() {
        let SlotDef { reset, scl, size, bitmap, .. } = ctx.data.slots[id];
        if cursor.1 != 0 && (rs, sc, bitmap) != (reset, scl, true) {
            // reset, size class, or type changed mid-bitfield: close bitfield
            cursor = (cursor.0 + ctx.data.slots[order[i-1]].size as Offset, 0);
            sc = scl;
        }
        if rs != reset {
            // reset changed, begin new interval
            breakpoints.push((reset, cursor.0));
            rs = reset;
        }
        // if type_ != B1, we have bit=0, otherwise align=1, so this can never change the byte
        // while we are allocation bitfields
        cursor.0 = (cursor.0 + size as Offset - 1) & !(size as Offset - 1);
        ctx.data.slots[id].value = Slot::new(cursor.0, cursor.1);
        if bitmap {
            cursor.1 = (cursor.1 + 1) & 7;
        }
        if cursor.1 == 0 {
            cursor.0 += size as Offset;
        }
    }
    if cursor.1 != 0 {
        cursor = (cursor.0 + ctx.data.slots[*order.last().unwrap()].size as Offset, 0);
    }
    if !rs.is_empty() {
        // finish unclosed interval
        breakpoints.push((Default::default(), cursor.0));
    }
    debug_assert!(breakpoints.is_empty() || breakpoints.raw.last().unwrap().0.is_empty());
    ctx.layout.size = cursor.0;
    breakpoints
}

fn makemasks(ctx: &mut Ctx, breakpoints: &mut IndexVec<BreakpointId, (ResetSet, Offset)>) {
    if breakpoints.end() > BreakpointId::MAXNUM.into() {
        // TODO: need to come up with a fancy (or less fancy) algorithm for merging intervals.
        // probably just recursively merge smallest?
        todo!()
    }
    // any non-assigned breakpoint gets layout.size
    // this makes any bit pattern for masks valid.
    ctx.layout.breakpoints.raw.fill(ctx.layout.size);
    for (i, &(reset, offset)) in breakpoints.pairs() {
        ctx.layout.breakpoints[i] = offset;
        for j in &*reset {
            ctx.layout.reset[j].set(i);
        }
    }
    let mut idx = ObjRef::NIL;
    while let Some(i) = ctx.objs.next(idx) {
        idx = i;
        if ctx.objs[idx].op == Obj::RESET {
            let reset: &mut RESET = &mut ctx.objs[idx.cast()];
            let mask: u64 = zerocopy::transmute!(ctx.layout.reset[zerocopy::transmute!(reset.id)]);
            reset.mlo = mask as u32;
            reset.mhi = (mask >> 32) as u32;
        }
    }
}

impl Phase for ComputeLayout {

    fn new(_: &mut Ccx<Absent>) -> compile::Result<Self> {
        Ok(Default::default())
    }

    fn run(ccx: &mut Ccx<Self>) -> compile::Result {
        collect(ccx);
        ccx.freeze_ir(|ctx| {
            let order = sort(ctx);
            let mut breakpoints = partition(ctx, &order);
            makemasks(ctx, &mut breakpoints);
        });
        save(ccx);
        if trace!(MEM) {
            trace!("{}", {
                let mut tmp = Default::default();
                dump_layout(&mut tmp, &ccx.layout);
                tmp
            })
        }
        Ok(())
    }

}
