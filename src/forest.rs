trait DynForest<V> {
    fn new_node(&mut self, x: &V);
    fn representative(&mut self, x: &V) -> &V;
    fn connected(&mut self, x: &V, y: &V) -> bool;
}

trait Incremental<V> {
    fn connect(&mut self, x: &V, y: &V);
}

trait Decremental<V> {
    fn disconnect(&mut self, x: &V, y: &V);
}

pub trait Aggregator<State> {
    fn update(target: &mut State, x: Option<&State>, y: Option<&State>);
}
//
