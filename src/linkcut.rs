use crate::association::{AssocVector, Association};
use crate::forest::Aggregator;
use crate::index::splay::{Splay, SplayData};
use crate::index::{IndexTree, TreeNode};
use crate::pool::{MonotonicPool, Pesudo, Pointer, Pool};
use std::alloc::Global;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::process::exit;

pub struct LCTData<I, T>
where
    I: IndexTree,
{
    upper_path: Option<Pointer<I::Node<Self>>>,
    data: T,
}

pub struct LinkCutTree<T, I, Assoc, A: Aggregator<T>>
where
    I: IndexTree,
    Assoc: Association<Pointer<I::Node<LCTData<I, T>>>>,
{
    pointers: Assoc,
    _phantom: PhantomData<(T, I, A)>,
}

struct LCTDataAgg<A>(PhantomData<A>);

impl<T, A: Aggregator<T>, I: IndexTree> Aggregator<LCTData<I, T>> for LCTDataAgg<A> {
    fn update(target: &mut LCTData<I, T>, x: Option<&LCTData<I, T>>, y: Option<&LCTData<I, T>>) {
        A::update(&mut target.data, x.map(|x| &x.data), y.map(|y| &y.data));
    }
}

impl<T, I, Assoc, A: Aggregator<T>> LinkCutTree<T, I, Assoc, A>
where
    I: IndexTree,
    Assoc: Association<Pointer<I::Node<LCTData<I, T>>>>,
{
    fn add<P: Pool<I::Node<LCTData<I, T>>>>(&mut self, pool: &mut P, key: &Assoc::Key, value: T) {
        self.pointers.set(
            key,
            pool.create(I::node(LCTData {
                upper_path: None,
                data: value,
            })),
        );
    }

    // make `n` the largest child of the current auxiliary tree
    // by cutting off all nodes coming after `n`.
    // Return the root of `n`
    fn expose(n: Pointer<I::Node<LCTData<I, T>>>) -> Pointer<I::Node<LCTData<I, T>>> {
        let (root, right) = I::split_after::<LCTData<I, T>, LCTDataAgg<A>>(n);
        let data = I::data::<LCTData<I, T>>(&right);
        data.upper_path.replace(n);
        root
    }

    // Going up and extend the auxiliary tree
    fn splice(n: Pointer<I::Node<LCTData<I, T>>>) -> Option<Pointer<I::Node<LCTData<I, T>>>> {
        match I::data(&n).upper_path {
            None => None, // no more upper path
            Some(upper) => {
                Self::expose(upper);
                // upper is now the largest in its tree
                let root = I::merge_after::<LCTData<I, T>, LCTDataAgg<A>>(upper, n);
                I::data(&n).upper_path.take();
                Some(root)
            }
        }
    }

    // Going up until `n` and tree root is in the same auxiliary tree
    // What is more, `n` is the largest one in the auxiliary tree
    // So the auxiliary tree is the total path from `n` to tree root
    fn access(n: Pointer<I::Node<LCTData<I, T>>>) -> Pointer<I::Node<LCTData<I, T>>> {
        let mut root = Self::expose(n);
        // n is the largest one
        while let Some(new_root) = Self::splice(root) {
            root = new_root;
        }
        root
    }

    // make `n` the root
    fn evert(n: Pointer<I::Node<LCTData<I, T>>>) -> Pointer<I::Node<LCTData<I, T>>> {
        I::reverse::<LCTData<I, T>, LCTDataAgg<A>>(Self::access(n))
    }

    pub fn link(&mut self, x: &Assoc::Key, y: &Assoc::Key) {
        if let (Some(x), Some(y)) = (self.pointers.get(x), self.pointers.get(y)) {
            let root = Self::evert(*x);
            I::data(&root).upper_path.replace(*y);
        }
    }

    pub fn cut(&mut self, x: &Assoc::Key, y: &Assoc::Key) {
        if let (Some(x), Some(y)) = (self.pointers.get(x), self.pointers.get(y)) {
            Self::evert(*x);
            Self::access(*y);
            I::remove::<LCTData<I, T>, LCTDataAgg<A>>(*y);
        }
    }

    pub fn connected(&mut self, x: &Assoc::Key, y: &Assoc::Key) -> bool {
        if let (Some(x), Some(y)) = (self.pointers.get(x), self.pointers.get(y)) {
            Self::evert(*x);
            let root = Self::access(*y);
            // x and y are in the same tree
            I::find_min_node::<LCTData<I, T>, LCTDataAgg<A>>(root) == *x
        } else {
            false
        }
    }

    pub fn query<U, F>(&mut self, x: &Assoc::Key, y: &Assoc::Key, f: F) -> Option<U>
    where
        F: FnOnce(&T) -> U,
    {
        if let (Some(x), Some(y)) = (self.pointers.get(x), self.pointers.get(y)) {
            Self::evert(*x);
            let root = Self::access(*y);
            let res = Some(&I::data(&root).data);
            if I::find_min_node::<LCTData<I, T>, LCTDataAgg<A>>(root) == *x {
                res.map(f)
            } else {
                None
            }
        } else {
            None
        }
    }
}

pub struct SplayLCT<T, Agg, Assoc, P>
where
    Agg: Aggregator<T>,
    Assoc: Association<Pointer<<Splay as IndexTree>::Node<LCTData<Splay, T>>>>,
    P: Pool<<Splay as IndexTree>::Node<LCTData<Splay, T>>>,
{
    pool: P,
    tree: LinkCutTree<T, Splay, Assoc, Agg>,
}

impl<T, Agg, Assoc, P> SplayLCT<T, Agg, Assoc, P>
where
    Agg: Aggregator<T>,
    Assoc: Association<Pointer<<Splay as IndexTree>::Node<LCTData<Splay, T>>>> + Default,
    P: Pool<<Splay as IndexTree>::Node<LCTData<Splay, T>>>,
{
    fn new(pool: P) -> Self {
        Self {
            pool,
            tree: LinkCutTree {
                pointers: Default::default(),
                _phantom: Default::default(),
            },
        }
    }
}

struct DoNothing;
impl<T> Aggregator<T> for DoNothing {
    fn update(_: &mut T, _: Option<&T>, _: Option<&T>) {}
}

#[test]
fn test() {
    let mut lct = SplayLCT::<(), DoNothing, AssocVector<_>, Pesudo>::new(Pesudo::new_in(Global));
    lct.tree.add(&mut lct.pool, &0, ());
    exit(0);
}
