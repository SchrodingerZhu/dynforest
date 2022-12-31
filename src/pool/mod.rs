mod monotonic;
mod pesudo;

use std::ops::{Deref, DerefMut};

pub trait Pool<T> {
    type Ptr: Deref<Target = T> + DerefMut + Copy + PartialEq;
    fn create(&mut self, data: T) -> Self::Ptr;
    fn recycle(&mut self, ptr: Self::Ptr);
}

pub use monotonic::MonotonicPool;
pub use pesudo::Pesudo;
