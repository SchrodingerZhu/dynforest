trait Connectivity<V> {
    fn connected(&mut self, x : &V, y : &V) -> bool;
}

trait Incremental<V> {
    fn connect(&mut self, x : &V, y : &V);
}

trait Decremental<V> {
    fn disconnect(&mut self, x : &V, y : &V);
}

trait Aggregator<V> {
    type Attr : Default;
    type Data : Default;
    // TODO: define needed operations
}

trait Aggregation<V, A : Aggregator<V>> {
    type Handle;
    fn associate_attribute(h : &mut Self::Handle, attr : A::Attr);
    fn update_data(h : &mut Self::Handle, data : A::Data);
}

trait PathAggregation<V, A : Aggregator<V>> : Aggregation<V, A> {
    fn path_aggregate<O, F : Fn(A::Data) -> O>(&mut self, x : &V, y : &V, f : F) -> O;
}

trait SubtreeAggregation<V, A : Aggregator<V>> : Aggregation<V, A> {
    fn subtree_aggregate<O, F : Fn(A::Data) -> O>(&mut self, r : &V, x : &V, f : F) -> O;
}