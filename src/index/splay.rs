use crate::forest::Aggregator;
use crate::index::TreeNode;
use crate::pool::Pool;
use std::marker::PhantomData;

struct SplayData<T> {
    data: T,
    reversed: u8,
}

type Node<P, T> = TreeNode<P, SplayData<T>>;

struct SplayOperator<T, P, A>(PhantomData<(T, P, A)>);

impl<T, P: Pool<Node<P, T>>, A: Aggregator<T>> SplayOperator<T, P, A> {
    // handle the reverse process
    fn push_down(mut n: P::Ptr) {
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
    fn which_child(p: P::Ptr, c: P::Ptr) -> usize {
        if p.children[0].contains(&c) {
            0
        } else {
            1
        }
    }

    // maintain the aggregation state.
    fn maintain(mut n: P::Ptr) {
        let left = n.children[0];
        let right = n.children[1];
        A::update(
            &mut n.attr.data,
            left.as_deref().map(|x| &x.attr.data),
            right.as_deref().map(|x| &x.attr.data),
        );
    }

    // binary tree rotation
    fn rotate(mut n: P::Ptr) {
        if let Some(mut parent) = n.parent {
            if let Some(mut grandparent) = parent.parent {
                Self::push_down(grandparent);
            }
            Self::push_down(n);

            let side = Self::which_child(parent, n);
            if let Some(mut grandparent) = parent.parent {
                let parent_side = Self::which_child(grandparent, parent);
                grandparent.children[parent_side].replace(n);
            }
            n.parent = parent.parent;
            parent.children[side] = n.children[side ^ 1];
            if let Some(mut child) = n.children[side ^ 1] {
                child.parent.replace(parent);
            }
            n.children[side ^ 1].replace(parent);
            parent.parent.replace(n);
            Self::maintain(parent);
            Self::maintain(n);
        }
    }

    // rotate a node to the root of a tree
    fn splay(n: P::Ptr) {
        while let Some(parent) = n.parent {
            match parent.parent {
                None => Self::rotate(n),
                Some(grandparent) => {
                    Self::push_down(grandparent);
                    Self::push_down(parent);
                    if Self::which_child(parent, n) == Self::which_child(grandparent, parent) {
                        Self::rotate(parent);
                        Self::rotate(n);
                    } else {
                        Self::rotate(n);
                        Self::rotate(n);
                    }
                }
            }
        }
    }

    // Split the tree into two halves.
    // Cut off all the nodes that comes later than the given node in the in-order traversal order.
    fn split_after(mut n: P::Ptr) {
        Self::splay(n);
        Self::push_down(n);
        if let Some(mut right) = n.children[1] {
            right.parent.take();
            n.children[1].take();
            Self::maintain(n);
        }
    }

    // Split the tree into two halves.
    // Cut off all the nodes that comes earlier than the given node in the in-order traversal order.
    fn split_before(mut n: P::Ptr) {
        Self::splay(n);
        Self::push_down(n);
        if let Some(mut left) = n.children[0] {
            left.parent.take();
            n.children[1].take();
            Self::maintain(n);
        }
    }

    // Reverse the in-order traversal order of the subtree.
    fn reverse(mut n: P::Ptr) {
        n.attr.reversed ^= 1;
    }

    // Merge two tree, `m` is the largest node in the adopting tree.
    // `n` is the root of the adopted tree.
    fn merge_after(mut m: P::Ptr, mut n: P::Ptr) {
        Self::splay(m);
        m.children[1].replace(n);
        n.parent.replace(m);
        Self::maintain(m);
    }

    // Merge two tree, `m` is the smallest node in the adopting tree.
    // `n` is the root of the adopted tree.
    fn merge_before(mut m: P::Ptr, mut n: P::Ptr) {
        Self::splay(m);
        m.children[0].replace(n);
        n.parent.replace(m);
        Self::maintain(n);
    }
}
