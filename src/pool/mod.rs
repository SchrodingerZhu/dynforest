mod monotonic;
mod pesudo;

use std::ops::{Deref, DerefMut};

pub trait Pool<T> {
    type Ptr<'a>: Deref<Target = T> + DerefMut
    where
        Self: 'a;
    fn create<'a>(&'a mut self, data: T) -> Self::Ptr<'a>;
    fn recycle<'a>(&'a mut self, ptr: Self::Ptr<'a>);
}

pub use monotonic::MonotonicPool;
pub use pesudo::Pesudo;
