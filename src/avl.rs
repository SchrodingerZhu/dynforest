use crate::pool::Pool;

enum TreeNode<'a, P: Pool<Self> + 'a, T> {
    Node(P::Ptr<'a>, T, u8, P::Ptr<'a>),
    Nil,
}

impl<'a, P: Pool<Self> + 'a, T> TreeNode<'a, P, T> {
    fn new(pool: &'a mut P, l: P::Ptr<'a>, x: T, h: u8, r: P::Ptr<'a>) -> P::Ptr<'a> {
        pool.create(Self::Node(l, x, h, r))
    }
}
