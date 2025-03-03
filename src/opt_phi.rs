//! Constant phi elimination.

use crate::bump::{BumpPtr, BumpRef};
use crate::compile::Ccx;
use crate::index::{IndexOption, IndexSlice, IndexVec};
use crate::ir::{FuncId, Ins, InsId, Opcode, Phi, PhiId};
use crate::optimize::{FuncPass, Ocx};
use crate::typestate::Absent;

#[derive(Default)]
pub struct OptPhi;

const NO_VALUES: InsId = zerocopy::transmute!(!0u16);
const MANY_VALUES: InsId = zerocopy::transmute!(!1u16);

#[derive(Clone, zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
struct PhiInfo {
    read: u16,
    write: InsId,
}

fn scan(code: &[Ins], info: &mut IndexSlice<PhiId, PhiInfo>) {
    for &ins in code {
        match ins.opcode() {
            Opcode::JMP => {
                let (value, _, phi) = ins.decode_JMP();
                match info[phi].write {
                    NO_VALUES => info[phi].write = value,
                    MANY_VALUES => {},
                    v if v == value => {},
                    _ => info[phi].write = MANY_VALUES
                }
            },
            Opcode::PHI => {
                let (_, phi) = ins.decode_PHI();
                info[phi].read += 1;
            },
            _ => {}
        }
    }
}

fn eliminate(
    phis: &mut IndexVec<PhiId, Phi>,
    bump: &mut BumpPtr,
    info: BumpRef<PhiInfo>,
    new: BumpRef<IndexOption<PhiId>>,
    start: usize,
) {
    for i in 0..start {
        bump[new.add_size(i as _)] = Some(i.into()).into();
    }
    let mut cursor: PhiId = start.into();
    for i in start..phis.end().into() {
        let PhiInfo { read, write } = bump[info.add_size(i as _)];
        phis[cursor] = phis[i.into()];
        bump[new.add_size(i as _)] = if read == 0 || write < MANY_VALUES {
            None
        } else {
            let v = Some(cursor);
            cursor += 1;
            v
        }.into();
    }
    phis.raw.truncate(cursor.into());
}

fn patch(
    code: &mut [Ins],
    info: &IndexSlice<PhiId, PhiInfo>,
    new: &IndexSlice<PhiId, IndexOption<PhiId>>
) {
    for ins in code {
        match ins.opcode() {
            Opcode::JMP => {
                let (_, dest, phi) = ins.decode_JMP();
                match new[phi].unpack() {
                    Some(newphi) => *ins.phi_mut().unwrap() = newphi,
                    None => *ins = Ins::GOTO(dest)
                }
            },
            Opcode::PHI => {
                let (_, phi) = ins.decode_PHI();
                match new[phi].unpack() {
                    Some(newphi) => *ins.phi_mut().unwrap() = newphi,
                    None => *ins = ins.set_opcode(Opcode::MOV).set_a(zerocopy::transmute!(info[phi].write))
                }
            },
            _ => {}
        }
    }
}

impl FuncPass for OptPhi {

    fn new(_: &mut Ccx<Absent>) -> Self {
        Default::default()
    }

    fn run(ccx: &mut Ocx, fid: FuncId) {
        let base = ccx.tmp.end();
        let func = &mut ccx.ir.funcs[fid];
        let code = func.code.inner_mut();
        let numphi: usize = func.phis.end().into();
        let (info_ptr, info) = ccx.tmp.reserve_dst::<IndexSlice<PhiId, PhiInfo>>(numphi);
        info.raw.fill(PhiInfo { read: 0, write: NO_VALUES });
        scan(&code.raw, info);
        let (new_ptr, _) = ccx.tmp.reserve_dst::<IndexSlice<PhiId, IndexOption<PhiId>>>(numphi);
        eliminate(func.phis.inner_mut(), &mut ccx.tmp, info_ptr.cast(), new_ptr.cast(), func.arg.into());
        patch(&mut code.raw, ccx.tmp.get_dst(info_ptr, numphi), ccx.tmp.get_dst(new_ptr, numphi));
        ccx.tmp.truncate(base);
    }

}
