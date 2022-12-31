use crate::pool::Pool;
use std::alloc::{Allocator, Global};
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub struct Pesudo<A: Allocator = Global> {
    alloc: A,
}

#[repr(transparent)]
pub struct Pointer<T>(NonNull<T>);

impl<T> PartialEq for Pointer<T> {
    fn eq(&self, other: &Self) -> bool {
        other.0.as_ptr().eq(&self.0.as_ptr())
    }
}

impl<T> Clone for Pointer<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> Copy for Pointer<T> {}

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
    type Ptr = Pointer<T>;

    fn create(&mut self, data: T) -> Self::Ptr {
        let leaked = Box::leak(Box::new_in(data, self.alloc.by_ref()));
        unsafe { Pointer(NonNull::new_unchecked(leaked as _)) }
    }

    fn recycle(&mut self, ptr: Self::Ptr) {
        unsafe {
            Box::from_raw_in(ptr.0.as_ptr(), self.alloc.by_ref());
        }
    }
}

impl<T> Deref for Pointer<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<T> DerefMut for Pointer<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}
