//! Object pool.

use alloc::vec::Vec;

#[derive(Default)]
pub struct Pool<T> {
    objects: Vec<T>
}

impl<T: Default> Pool<T> {

    pub fn take(&mut self) -> T {
        self.objects.pop().unwrap_or_else(T::default)
    }

}

impl<T> Pool<T> {

    pub fn put(&mut self, obj: T) {
        self.objects.push(obj);
    }

}
