# dynforest

This crate provides a data structure to handle dynamic tree connectivity.
Both incremental and decremental operations are supported with amortized O(log n)
time complexity.

As the underlying data structure is a Splay tree, this crate works best with the situation
where the working set is relatively small.

To represent a node in the forest, one can create a handle via [`Handle::new`].
To connect two nodes, one can use [`Handle::connect`]. This will return a [`Connection`], which
will keep the two nodes connected until it is dropped.
