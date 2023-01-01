use crate::pool::{Pointer, Pool, PoolCell};
use std::alloc::{Allocator, Global};
use std::fmt::{Debug, Formatter};
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub struct Pesudo<A: Allocator = Global> {
    alloc: A,
}

impl<A: Allocator> Pesudo<A> {
    pub fn new_in(alloc: A) -> Self {
        Self { alloc }
    }
}

impl<T: Debug> Debug for Pointer<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        unsafe { Debug::fmt(&*self.0.as_ptr(), f) }
    }
}

impl<A: Allocator, T> Pool<T> for Pesudo<A> {
    fn create(&mut self, data: T) -> Pointer<T> {
        unsafe {
            let leaked = Box::leak(Box::new_in(
                MaybeUninit::new(PoolCell {
                    data: ManuallyDrop::new(data),
                }),
                self.alloc.by_ref(),
            ));
            Pointer(NonNull::new_unchecked(leaked as _))
        }
    }

    fn recycle(&mut self, ptr: Pointer<T>) {
        unsafe {
            Box::from_raw_in(ptr.0.as_ptr(), self.alloc.by_ref());
        }
    }
}
