use crate::forest::Aggregator;
use crate::index::TreeNode;
use crate::pool::Pool;
use std::marker::PhantomData;
use std::ops::Deref;

struct SplayData<P, T>
where
    P: Pool<Node<P, T>>,
{
    path_head: P::Ptr,
    data: T,
    reversed: u8,
}

type Node<P, T> = TreeNode<P, SplayData<P, T>>;

struct SplayOperator<T, P, A>(PhantomData<(T, P, A)>);
impl<T, P: Pool<Node<P, T>>, A: Aggregator<T>> SplayOperator<T, P, A> {
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
    fn which_child(n: P::Ptr, p: P::Ptr) -> usize {
        if n.children[0].contains(&p) {
            0
        } else {
            1
        }
    }
    fn maintain(mut n: P::Ptr) {
        let lchild = n.children[0];
        let rchild = n.children[1];
        A::update(
            &mut n.attr.data,
            lchild.as_deref().map(|x| &x.attr.data),
            rchild.as_deref().map(|x| &x.attr.data),
        );
    }
    fn rotate(mut n: P::Ptr) {
        if let Some(mut parent) = n.parent {
            if let Some(mut grandparent) = parent.parent {
                Self::push_down(grandparent);
            }
            Self::push_down(n);
            std::mem::swap(&mut n.attr.path_head, &mut parent.attr.path_head);

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
}
