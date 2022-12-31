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

struct PooledTree<T, P: Pool<TreeNode<P, T>>> {
    pool: UnsafeCell<P>,
    root: UnsafeCell<Option<P::Ptr>>,
}

impl<T, P: Pool<TreeNode<P, T>>> PooledTree<T, P> {
    pub fn new_in(pool: P) -> Box<Self> {
        let target = Box::new(Self {
            pool: pool.into(),
            root: UnsafeCell::new(None),
        });
        target
    }
}

impl<T: Debug, P: Pool<TreeNode<P, T>>> Debug for PooledTree<T, P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        unsafe {
            match &*self.root.get() {
                Some(root) => f.debug_tuple("Node").field(root.deref()).finish(),
                None => f.write_str("nil"),
            }
        }
    }
}

#[test]
fn test() {
    use std::alloc::Global;
    let pool = crate::pool::Pesudo::new_in(Global);
    let pooled_tree = PooledTree::<usize, _>::new_in(pool);
    //pooled_tree.initialize();
    println!("{:?}", pooled_tree);
}
