use crate::pool::Pool;
use std::alloc::{Allocator, Global};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub struct Pesudo<A: Allocator = Global> {
    alloc: A,
}

pub struct Pointer<T>(NonNull<T>);

impl<A: Allocator, T> Pool<T> for Pesudo<A> {
    type Ptr<'a> = Pointer<T> where Self: 'a;

    fn create<'a>(&'a mut self, data: T) -> Self::Ptr<'a> {
        let leaked = Box::leak(Box::new_in(data, self.alloc.by_ref()));
        unsafe { Pointer(NonNull::new_unchecked(leaked as _)) }
    }

    fn recycle<'a>(&'a mut self, ptr: Self::Ptr<'a>) {
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
