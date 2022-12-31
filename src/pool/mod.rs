mod monotonic;

use std::ops::Deref;

pub trait Pool<T> {
    type Ptr<'a>: Deref
    where
        Self: 'a;
    fn create<'a>(&'a mut self, data: T) -> Self::Ptr<'a>;
    fn recycle<'a>(&'a mut self, ptr: Self::Ptr<'a>);
}

pub use monotonic::MonotonicPool;
