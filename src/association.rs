pub trait Association<T> {
    type Key;
    fn get(&self, k: &Self::Key) -> Option<&T>;
    fn set(&mut self, k: &Self::Key, data: T);
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

    fn set(&mut self, k: &Self::Key, data: T) {
        if self.0.len() <= *k {
            self.0.resize_with(k + 1, || Default::default());
        }
        self.0[*k].replace(data);
    }
}
