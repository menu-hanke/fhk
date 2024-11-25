//! Hashbrown & FxHash re-exports.

use core::cell::UnsafeCell;
use core::hash::{BuildHasher, Hash};

use rustc_hash::FxBuildHasher;

pub type HashMap<K, V> = hashbrown::HashMap<K, V, FxBuildHasher>;

pub fn fxhash<T: Hash>(v: T) -> u64 {
    FxBuildHasher::default().hash_one(v)
}

// invariant: this type may not hand out references from methods taking &self
// (handing out references from &mut self is ok, though.)
#[repr(transparent)]
pub struct ValueHashMap<K, V>(UnsafeCell<HashMap<K, V>>);

impl<K, V> Default for ValueHashMap<K, V> {
    fn default() -> Self {
        Self(UnsafeCell::new(Default::default()))
    }
}

impl<K: Eq + Hash, V> ValueHashMap<K, V> {

    pub fn insert(&self, key: K, value: V) {
        unsafe { &mut *self.0.get() }.insert(key, value);
    }

}

impl<K: Eq + Hash, V: Clone> ValueHashMap<K, V> {

    pub fn get(&self, key: K) -> Option<V> {
        unsafe { &*self.0.get() }.get(&key).cloned()
    }

}
