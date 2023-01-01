use crate::forest::Aggregator;
use crate::index::{IndexTree, PointerDerivation, TreeNode};
use crate::pool::{Pointer, Pool};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

pub struct SplayData<T> {
    data: T,
    reversed: u8,
}

pub type Node<T> = TreeNode<SplayData<T>>;

pub struct Splay;

impl Splay {
    // handle the reverse process
    fn push_down<T>(mut n: Pointer<Node<T>>) {
        if n.attr.reversed != 0 {
            n.children.swap(0, 1);
            if let Some(mut x) = n.children[0] {
                x.attr.reversed ^= 1;
            }
            if let Some(mut y) = n.children[1] {
                y.attr.reversed ^= 1;
            }
            n.attr.reversed = 0;
        }
    }

    // get this index of a child in its parent
    fn which_child<T>(p: Pointer<Node<T>>, c: Pointer<Node<T>>) -> usize {
        if p.children[0].contains(&c) {
            0
        } else {
            1
        }
    }

    // maintain the aggregation state.
    fn maintain<T, A: Aggregator<T>>(mut n: Pointer<Node<T>>) {
        let left = n.children[0];
        let right = n.children[1];
        A::update(
            &mut n.attr.data,
            left.as_deref().map(|x| &x.attr.data),
            right.as_deref().map(|x| &x.attr.data),
        );
    }

    // binary tree rotation
    fn rotate<T, A: Aggregator<T>>(mut n: Pointer<Node<T>>) {
        if let Some(mut parent) = n.parent {
            if let Some(mut grandparent) = parent.parent {
                Self::push_down::<T>(grandparent);
            }
            Self::push_down::<T>(n);

            let side = Self::which_child::<T>(parent, n);
            if let Some(mut grandparent) = parent.parent {
                let parent_side = Self::which_child::<T>(grandparent, parent);
                grandparent.children[parent_side].replace(n);
            }
            n.parent = parent.parent;
            parent.children[side] = n.children[side ^ 1];
            if let Some(mut child) = n.children[side ^ 1] {
                child.parent.replace(parent);
            }
            n.children[side ^ 1].replace(parent);
            parent.parent.replace(n);
            Self::maintain::<T, A>(parent);
            Self::maintain::<T, A>(n);
        }
    }

    // rotate a node to the root of a tree
    fn splay<T, A: Aggregator<T>>(n: Pointer<Node<T>>) {
        while let Some(parent) = n.parent {
            match parent.parent {
                None => Self::rotate::<T, A>(n),
                Some(grandparent) => {
                    Self::push_down::<T>(grandparent);
                    Self::push_down::<T>(parent);
                    if Self::which_child(parent, n) == Self::which_child(grandparent, parent) {
                        Self::rotate::<T, A>(parent);
                        Self::rotate::<T, A>(n);
                    } else {
                        Self::rotate::<T, A>(n);
                        Self::rotate::<T, A>(n);
                    }
                }
            }
        }
    }
}

impl IndexTree for Splay {
    type Node<T> = Node<T>;

    fn node<T>(data: T) -> Self::Node<T> {
        Self::Node {
            attr: SplayData { data, reversed: 0 },
            children: [None; 2],
            parent: None,
        }
    }

    fn merge_before<T, A: Aggregator<T>>(
        mut x: Pointer<Self::Node<T>>,
        mut y: Pointer<Self::Node<T>>,
    ) -> Pointer<Self::Node<T>> {
        Splay::splay::<T, A>(x);
        Splay::splay::<T, A>(y);
        x.children[0].replace(y);
        y.parent.replace(x);
        Splay::maintain::<T, A>(x);
        x
    }

    fn merge_after<T, A: Aggregator<T>>(
        x: Pointer<Self::Node<T>>,
        y: Pointer<Self::Node<T>>,
    ) -> Pointer<Self::Node<T>> {
        todo!()
    }

    fn split_before<T, A: Aggregator<T>>(
        x: Pointer<Self::Node<T>>,
    ) -> (Pointer<Self::Node<T>>, Pointer<Self::Node<T>>) {
        todo!()
    }

    fn split_after<T, A: Aggregator<T>>(
        x: Pointer<Self::Node<T>>,
    ) -> (Pointer<Self::Node<T>>, Pointer<Self::Node<T>>) {
        todo!()
    }

    fn reverse<T, A: Aggregator<T>>(n: Pointer<Self::Node<T>>) -> Pointer<Self::Node<T>> {
        todo!()
    }

    fn data<T>(n: &Pointer<Self::Node<T>>) -> &mut T {
        todo!()
    }

    fn remove<T, A: Aggregator<T>>(n: Pointer<Self::Node<T>>) {
        todo!()
    }

    fn find_min_node<T, A: Aggregator<T>>(n: Pointer<Self::Node<T>>) -> Pointer<Self::Node<T>> {
        todo!()
    }
}
