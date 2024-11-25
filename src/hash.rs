//! Hashbrown & FxHash re-exports.

use core::hash::{BuildHasher, Hash};

use rustc_hash::FxBuildHasher;

pub type HashMap<K, V> = hashbrown::HashMap<K, V, FxBuildHasher>;

pub fn fxhash<T: Hash>(v: T) -> u64 {
    FxBuildHasher::default().hash_one(v)
}
