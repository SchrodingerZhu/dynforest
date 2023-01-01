use crate::forest::Aggregator;
use crate::pool::{Pointer, Pool};
use std::cell::UnsafeCell;
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, DerefMut};

pub mod avl;
pub mod splay;

pub struct TreeNode<T> {
    parent: Option<Pointer<Self>>,
    children: [Option<Pointer<Self>>; 2],
    attr: T,
}

impl<T: Debug> Debug for TreeNode<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Node")
            .field(&self.children[0].as_ref().map(|x| x.deref()))
            .field(&self.attr)
            .field(&self.children[1].as_ref().map(|x| x.deref()))
            .finish()
    }
}

pub trait PointerDerivation {
    type Pointer<T>;
    fn get<T>(x: &Self::Pointer<T>) -> &T;
    fn get_mut<T>(x: &mut Self::Pointer<T>) -> &mut T;
}

pub trait IndexTree {
    type Node<T>;

    fn node<T>(x: T) -> Self::Node<T>;

    fn merge_before<T, A: Aggregator<T>>(
        x: Pointer<Self::Node<T>>,
        y: Pointer<Self::Node<T>>,
    ) -> Pointer<Self::Node<T>>;
    fn merge_after<T, A: Aggregator<T>>(
        x: Pointer<Self::Node<T>>,
        y: Pointer<Self::Node<T>>,
    ) -> Pointer<Self::Node<T>>;
    fn split_before<T, A: Aggregator<T>>(
        x: Pointer<Self::Node<T>>,
    ) -> (Pointer<Self::Node<T>>, Pointer<Self::Node<T>>);
    fn split_after<T, A: Aggregator<T>>(
        x: Pointer<Self::Node<T>>,
    ) -> (Pointer<Self::Node<T>>, Pointer<Self::Node<T>>);
    fn reverse<T, A: Aggregator<T>>(n: Pointer<Self::Node<T>>) -> Pointer<Self::Node<T>>;
    fn data<T>(n: &Pointer<Self::Node<T>>) -> &mut T;
    fn remove<T, A: Aggregator<T>>(n: Pointer<Self::Node<T>>);
    fn find_min_node<T, A: Aggregator<T>>(n: Pointer<Self::Node<T>>) -> Pointer<Self::Node<T>>;
    // fn find_max(n : Ptr) -> Ptr;
}
