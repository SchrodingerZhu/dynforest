use crate::association::Association;
use crate::index::IndexTree;
use crate::pool::Pool;
use std::marker::PhantomData;
use std::ops::Deref;

pub struct LCTData<P, T, I>
where
    P: Pool<I::Node>,
    I: IndexTree<Self, P>,
{
    upper_path: Option<P::Ptr>,
    data: T,
}

pub struct LinkCutTree<P, T, I, Assoc>
where
    P: Pool<I::Node>,
    I: IndexTree<LCTData<P, T, I>, P>,
    Assoc: Association<P::Ptr>,
{
    pool: P,
    pointers: Assoc,
    _phantom: PhantomData<(T, I)>,
}

impl<P, T, I, Assoc> LinkCutTree<P, T, I, Assoc>
where
    P: Pool<I::Node>,
    I: IndexTree<LCTData<P, T, I>, P>,
    Assoc: Association<P::Ptr>,
{
    fn add_vertex(&mut self, key : &Assoc::Key) {
        self.pointers.set(key, I::individual())
    }

    // make `n` the largest child of the current path tree
    // by cutting off all nodes coming after `n`.
    // Return the root of `n`
    fn expose(n : P::Ptr) -> P::Ptr {
        let (root, right) = I::split_after(n);
        let data = I::data(&right);
        data.upper_path.replace(n);
        root
    }

    // Going up and concat all the upper path
    fn splice(n : P::Ptr) -> Option<P::Ptr> {
        match I::data(&n).upper_path {
            None => None, // no more upper path
            Some(upper) => {
                Self::expose(upper);
                // upper is now the largest in its tree
                let root = I::merge_after(upper, n);
                I::data(&n).upper_path.take();
                Some(root)
            }
        }
    }

    // going up until `n` and `root` is in the same index tree
    fn access(n : P::Ptr) -> P::Ptr {
        let mut root = Self::expose(n);
        // n is the largest one
        while let Some(new_root) =  Self::splice(root) {
            root = new_root;
        }
        root
    }
}
