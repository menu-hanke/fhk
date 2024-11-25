//! Like SmallVec but wastes less memory.

use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::num::NonZero;
use core::ptr::NonNull;

use crate::index::Index;

// #[repr(C, align(8))]
// struct MiniVecInline {
//     data: [u8; 15],
//     len: u8
// }
// 
// #[repr(C)]
// struct MiniVecOutline {
//     ptr: NonNull<u8>,
//     cap: NonZero<u32>,
//     len: u32
// }
// 
// /*
//  *                            byte:bit
//  *           +------+-------+--------+------------+------+
//  *           | 0..7 | 8..11 | 12..14 | 15:0..15:6 | 15:7 |
//  *           +======+=======+========+============+======+
//  * inline    |         data          |     len    |   0  |
//  *           +------+-------+--------+------------+------+
//  * outline   |  ptr |  cap  |        !len         |   1  |
//  *           +------+-------+--------+------------+------+
//  */
// #[repr(C)]
// pub union MiniIndexVec<I, T>
//     where I: Index,
//           T: zerocopy::IntoBytes
// {
//     _marker: PhantomData<(fn(&I), *mut T)>,
//     u32: [u32; 4],
//     inline: ManuallyDrop<MiniVecInline>,
//     outline: ManuallyDrop<MiniVecOutline>
// }
// 
// pub type MiniVec<T> = MiniIndexVec<usize, T>;
// 

// TODO: implement me
pub type MiniIndexVec<K,V> = crate::index::IndexVec<K,V>;
pub type MiniIndexValueVec<K,V> = crate::index::IndexValueVec<K,V>;

/* ---- Arrays -------------------------------------------------------------- */
// NOTE: rewrite this mess as a struct with generics when/if zerocopy can understand that.

// pub unsafe trait MiniArray {
// 
// }
// 
// macro_rules! mini_array {
//     ($vis:vis struct $name:ident[$index:ty => $elem:ty; $size:expr]) => {
//         #[derive(zerocopy::FromBytes, zerocopy::IntoBytes, zerocopy::Immutable)]
//         #[repr(C)]
//         $vis struct $name {
//             pub len: $index,
//             pub data: [$elem; $size]
//         }
//     };
// }
// 
// pub(crate) use mini_array;
