use std::collections::HashMap;
use std::hash::Hash;

pub trait Association<T> {
    type Key;
    fn get(&self, k: &Self::Key) -> Option<&T>;
    fn set(&mut self, k: Self::Key, data: T);
    fn remove(&mut self, k: &Self::Key);
}

#[derive(Debug)]
#[repr(transparent)]
pub struct AssocVector<T>(Vec<Option<T>>);

impl<T> Default for AssocVector<T> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<T> Association<T> for AssocVector<T> {
    type Key = usize;

    fn get(&self, k: &Self::Key) -> Option<&T> {
        self.0.get(*k).and_then(|x| x.as_ref())
    }

    fn set(&mut self, k: Self::Key, data: T) {
        if self.0.len() <= k {
            self.0.resize_with(k + 1, || Default::default());
        }
        self.0[k].replace(data);
    }

    fn remove(&mut self, k: &Self::Key) {
        if let Some(slot) = self.0.get_mut(*k) {
            slot.take();
        }
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct AssocMap<T : Hash, V>(HashMap<T, V>);

impl<T : Hash + Eq, V> Default for AssocMap<T, V> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T : Hash + Eq, V> Association<V> for AssocMap<T, V> {
    type Key = T;

    fn get(&self, k: &Self::Key) -> Option<&V> {
        self.0.get(k)
    }

    fn set(&mut self, k: Self::Key, data: V) {
        self.0.insert(k, data);
    }

    fn remove(&mut self, k: &Self::Key) {
        self.0.remove(k);
    }
}
