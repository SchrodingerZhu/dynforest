use crate::pool::Pool;

enum TreeNode<'a, P: Pool<Self> + 'a, T> {
    Node(P::Ptr<'a>, T, u8, P::Ptr<'a>),
    Nil,
}

impl<'a, P: Pool<Self> + 'a, T> TreeNode<'a, P, T> {
    type Ptr = P::Ptr<'a>;

    fn new(pool: &'a mut P, l: Self::Ptr, x: T, h: u8, r: Self::Ptr) -> Self::Ptr {
        pool.create(Self::Node(l, x, h, r))
    }
}
