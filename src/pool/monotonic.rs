use crate::pool::Pool;
use std::marker::PhantomData;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ops::{Deref, DerefMut};
use std::pin::Pin;
use std::ptr::NonNull;

union PoolCell<T> {
    data: ManuallyDrop<T>,
    next: Option<NonNull<MaybeUninit<Self>>>,
}

struct Block<T, const N: usize> {
    data: [MaybeUninit<PoolCell<T>>; N],
}

impl<T, const N: usize> Default for Block<T, N> {
    fn default() -> Self {
        Self {
            data: MaybeUninit::uninit_array(),
        }
    }
}

pub struct MonotonicPool<T, const N: usize = 64> {
    memory: Vec<Pin<Box<Block<T, N>>>>,
    cursor: usize,
    recycle_list: Option<NonNull<MaybeUninit<PoolCell<T>>>>,
}

impl<T, const N: usize> MonotonicPool<T, N> {
    pub fn new() -> Self {
        Self {
            memory: Vec::new(),
            cursor: 0,
            recycle_list: None,
        }
    }

    pub fn capacity(&self) -> usize {
        self.memory.len() * N
    }

    fn allocate_new_block(&mut self) {
        unsafe {
            self.memory
                .push(Pin::new_unchecked(Box::new(Block::default())));
            self.cursor = (self.memory.len() - 1) * N;
        }
    }

    fn try_get_free_slot(&mut self) -> Option<NonNull<MaybeUninit<PoolCell<T>>>> {
        if let Some(slot) = self.recycle_list.clone() {
            unsafe {
                self.recycle_list = slot.as_ref().assume_init_ref().next;
                Some(slot)
            }
        } else {
            if self.capacity() == self.cursor {
                None
            } else {
                let block = self.cursor / N;
                let index = self.cursor - block * N;
                self.cursor += 1;
                unsafe {
                    Some(NonNull::new_unchecked(
                        self.memory
                            .get_unchecked_mut(block)
                            .data
                            .get_unchecked(index) as *const _ as *mut _,
                    ))
                }
            }
        }
    }
    fn get_free_slot(&mut self) -> NonNull<MaybeUninit<PoolCell<T>>> {
        if let Some(slot) = self.try_get_free_slot() {
            slot
        } else {
            self.allocate_new_block();
            let block_count = self.memory.len();
            let slot = unsafe {
                NonNull::new_unchecked(
                    self.memory
                        .get_unchecked_mut(block_count - 1)
                        .data
                        .get_unchecked(0) as *const _ as *mut _,
                )
            };
            self.cursor += 1;
            slot
        }
    }
}

impl<T, const N: usize> Pool<T> for MonotonicPool<T, N> {
    type Ptr<'a> = Pointer<'a, T> where Self: 'a;

    fn create(&mut self, data: T) -> Pointer<T> {
        let mut slot = self.get_free_slot();
        unsafe {
            slot.as_mut().write(PoolCell {
                data: ManuallyDrop::new(data),
            });
            Pointer(slot, Default::default())
        }
    }

    fn recycle(&mut self, mut ptr: Pointer<T>) {
        let next = self.recycle_list;
        unsafe {
            ManuallyDrop::drop(&mut ptr.0.as_mut().assume_init_mut().data);
            ptr.0.as_mut().write(PoolCell { next });
            self.recycle_list.replace(ptr.0);
        }
    }
}

#[repr(transparent)]
pub struct Pointer<'a, T>(NonNull<MaybeUninit<PoolCell<T>>>, PhantomData<&'a T>);

impl<'a, T> Deref for Pointer<'a, T>
where
    Self: 'a,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref().assume_init_ref().data.deref() }
    }
}

impl<'a, T> DerefMut for Pointer<'a, T>
where
    Self: 'a,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut().assume_init_mut().data.deref_mut() }
    }
}
