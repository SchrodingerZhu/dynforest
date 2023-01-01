mod monotonic;
mod pesudo;

use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

union PoolCell<T> {
    data: ManuallyDrop<T>,
    next: Option<NonNull<MaybeUninit<Self>>>,
}

#[repr(transparent)]
pub struct Pointer<T>(NonNull<MaybeUninit<PoolCell<T>>>);

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

impl<T> Deref for Pointer<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref().assume_init_ref().data.deref() }
    }
}

impl<T> DerefMut for Pointer<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut().assume_init_mut().data.deref_mut() }
    }
}

pub trait Pool<T> {
    fn create(&mut self, data: T) -> Pointer<T>;
    fn recycle(&mut self, ptr: Pointer<T>);
}

pub use monotonic::MonotonicPool;
pub use pesudo::Pesudo;
