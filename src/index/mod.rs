use crate::pool::Pool;
use std::cell::UnsafeCell;
use std::fmt::{Debug, Formatter};
use std::ops::Deref;

pub mod avl;
pub mod splay;

struct TreeNode<P: Pool<Self>, T> {
    parent: Option<P::Ptr>,
    children: [Option<P::Ptr>; 2],
    attr: T,
}

impl<P: Pool<Self>, T: Debug> Debug for TreeNode<P, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Node")
            .field(&self.children[0].as_ref().map(|x| x.deref()))
            .field(&self.attr)
            .field(&self.children[1].as_ref().map(|x| x.deref()))
            .finish()
    }
}

pub trait IndexTree<Data, P>
where
    P: Pool<Self::Node>,
{
    type Node;
    fn individual() -> P::Ptr;
    fn merge_before(x: P::Ptr, y: P::Ptr) -> P::Ptr;
    fn merge_after(x: P::Ptr, y: P::Ptr) -> P::Ptr;
    fn split_before(x: P::Ptr) -> (P::Ptr, P::Ptr);
    fn root(x : P::Ptr) -> P::Ptr;
    fn split_after(x: P::Ptr) -> (P::Ptr, P::Ptr);
    fn reverse(n: P::Ptr);
    fn data(n: &P::Ptr) -> &mut Data;

    // fn find_min(n : Ptr) -> Ptr;
    // fn find_max(n : Ptr) -> Ptr;
}
