//! Initial reset sets.

// use crate::hash::HashMap;
// use crate::index::{index, IndexVec};
// use crate::ir::IR;
// use crate::mem::{ResetId, ResetSet};
// use crate::obj::{FieldType, Obj, ObjRef, Objects, Operator};
// 
// index!(struct BundleId(u16));
// 
// struct BundleState {
//     reset: ResetSet
// }
// 
// fn mark(objs: &Objects, resets: &mut HashMap<ObjRef, ResetSet>, idx: ObjRef, id: ResetId) {
//     let o = objs[idx];
//     match o.operator() {
//         Operator::VAR | Operator::MOD => resets.entry(idx).or_default().set(id),
//         op => {
//             // TODO: make the fields() iterator also return offsets.
//             // this same logic is repeated in dump.rs
//             let raw = objs.get_raw(idx);
//             let mut idx = 1;
//             for (ft, _) in op.fields() {
//                 match ft {
//                     FieldType::Spec => continue,
//                     FieldType::Ref => mark(objs, resets, zerocopy::transmute!(raw[idx]), id),
//                     FieldType::Lit | FieldType::Name => {},
//                     FieldType::VRef => {
//                         for &r in &raw[idx..] {
//                             mark(objs, resets, zerocopy::transmute!(r), id);
//                         }
//                         break;
//                     }
//                     FieldType::VLit => break
//                 }
//                 idx += 1;
//             }
//         }
//     }
// }
// 
// pub fn computereset(objs: &Objects, ir: &mut IR) {
//     // mark explicitly defined resets for models and variables
//     let mut resets: HashMap<ObjRef/*VAR|MOD*/, ResetSet> = Default::default();
//     for idx in objs.keys() {
//         if objs[idx].op == Obj::RESET {
//             mark(objs, &mut resets, idx, zerocopy::transmute!(objs[idx].data));
//         }
//     }
//     // collect bundles.
//     let bundles: IndexVec<>
// 
//     // construct and solve dataflow system:
//     //   for each explicit reset r and bundle B:
//     //     (1) r ∈ R(B) if node(B) ∈ e,  where node(B) is the node B was generated from
//     //   for all pairs of bundles B,C:
//     //     (2) R(C) ⊂  R(B)  if B calls C
// 
// }
