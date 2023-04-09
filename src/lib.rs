#![no_std]
///
/// This crate provides a data structure to handle dynamic tree connectivity.
/// Both incremental and decremental operations are supported with amortized O(log n)
/// time complexity.
///
/// As the underlying data structure is a Splay tree, this crate works best with the situation
/// where the working set is relatively small.
///
extern crate alloc;

use alloc::rc::Rc;
use core::cell::UnsafeCell;
use core::ptr::NonNull;

struct Node {
    tree_parent: Option<NonNull<Self>>,
    tree_left: Option<NonNull<Self>>,
    tree_right: Option<NonNull<Self>>,
    path_parent: Option<NonNull<Self>>,
    tree_reversed: bool,
}

/// Handle represents a node in the forest. A handle will contribute to the reference count of the node.
#[derive(Clone)]
pub struct Handle {
    target: Rc<UnsafeCell<Node>>,
}

/// Connection represents a edge between two nodes.
/// A connection will contribute to the reference count of both nodes involved in the connection.
/// If a connection is dropped, the edge will be removed from the forest.
/// # Example
/// ```
/// use dynforest::Handle;
/// let a = Handle::new();
/// let b = Handle::new();
/// {
///     let _conn = a.connect(&b);
///     assert!(a.is_connected(&b));
/// }
/// assert!(!a.is_connected(&b));
/// ```
pub struct Connection {
    targets: [Rc<UnsafeCell<Node>>; 2],
}

impl Node {
    unsafe fn get_child(this: NonNull<Self>, is_right: bool) -> Option<NonNull<Self>> {
        if is_right {
            this.as_ref().tree_right
        } else {
            this.as_ref().tree_left
        }
    }
    unsafe fn set_child(mut this: NonNull<Self>, is_right: bool, node: Option<NonNull<Self>>) {
        if is_right {
            this.as_mut().tree_right = node;
        } else {
            this.as_mut().tree_left = node;
        }
    }
    unsafe fn is_right_child(this: NonNull<Self>) -> bool {
        match this.as_ref().tree_parent {
            None => false,
            Some(x) => unsafe {
                match x.as_ref().tree_right.as_ref() {
                    None => false,
                    Some(x) => core::ptr::eq(x.as_ref(), this.as_ref()),
                }
            },
        }
    }

    fn allocate() -> Handle {
        Handle {
            target: Rc::new(UnsafeCell::from(Self {
                tree_parent: None,
                tree_left: None,
                tree_right: None,
                path_parent: None,
                tree_reversed: false,
            })),
        }
    }

    unsafe fn push_down(mut this: NonNull<Self>) {
        if this.as_ref().tree_reversed {
            let tmp = this.as_ref().tree_left;
            this.as_mut().tree_left = this.as_ref().tree_right;
            this.as_mut().tree_right = tmp;
            if let Some(mut left) = this.as_ref().tree_left {
                left.as_mut().tree_reversed = !left.as_ref().tree_reversed;
            }
            if let Some(mut right) = this.as_ref().tree_right {
                right.as_mut().tree_reversed = !right.as_ref().tree_reversed;
            }
            this.as_mut().tree_reversed = false;
        }
    }

    unsafe fn unchecked_mut_parent(this: NonNull<Self>) -> NonNull<Self> {
        this.as_ref().tree_parent.unwrap_unchecked()
    }

    unsafe fn rotate(mut this: NonNull<Self>) {
        debug_assert!(this.as_ref().tree_parent.is_some());
        // First, check the `reversed` flags for all touched nodes. Push down the flags if needed.
        if let Some(grandparent) = Self::unchecked_mut_parent(this).as_ref().tree_parent {
            Self::push_down(grandparent);
        }
        Self::push_down(Self::unchecked_mut_parent(this));
        Self::push_down(this);

        // Secondly, during the process of going up, the lower node also need to hand over the pointer to upper-level
        // paths so that only the root for each auxiliary tree can have non-null upper pointers.
        let tmp = this.as_ref().path_parent;
        this.as_mut().path_parent = Self::unchecked_mut_parent(this).as_ref().path_parent;
        Self::unchecked_mut_parent(this).as_mut().path_parent = tmp;

        // Prepare to swap pointers
        let is_right = Self::is_right_child(this);
        let mut parent_backup = this.as_ref().tree_parent.unwrap_unchecked();

        // Update parents
        if let Some(grandparent) = parent_backup.as_ref().tree_parent {
            Self::set_child(grandparent, Self::is_right_child(parent_backup), Some(this));
        }
        this.as_mut().tree_parent = parent_backup.as_ref().tree_parent;

        // Update children
        let target_child = Self::get_child(this, !is_right);
        Self::set_child(parent_backup, is_right, target_child);
        if let Some(mut target_child) = target_child {
            target_child.as_mut().tree_parent = Some(parent_backup);
        }

        // Update current node
        Self::set_child(this, !is_right, Some(parent_backup));
        parent_backup.as_mut().tree_parent = Some(this);
    }

    // Keep rotating until current node reaches the root
    unsafe fn splay(this: NonNull<Self>) {
        while let Some(parent) = this.as_ref().tree_parent {
            match parent.as_ref().tree_parent {
                None => Self::rotate(this),
                Some(grandparent) => {
                    Self::push_down(grandparent);
                    Self::push_down(parent);
                    if Self::is_right_child(this) == Self::is_right_child(parent) {
                        Self::rotate(parent);
                        Self::rotate(this);
                    } else {
                        Self::rotate(this);
                        Self::rotate(this);
                    }
                }
            }
        }
    }

    // Separate current auxiliary tree into two smaller trees such that all nodes that are deeper than the current node
    // (those who come later during in-order traversal) are cut off from the auxiliary tree.
    // After the separation, current node is the root of its auxiliary tree.
    unsafe fn separate_deeper_nodes(mut this: NonNull<Self>) {
        Self::splay(this);
        Self::push_down(this);
        if let Some(mut right) = this.as_ref().tree_right {
            right.as_mut().tree_parent = None;
            this.as_mut().tree_right = None;
            right.as_mut().path_parent = Some(this);
        }
    }

    // Merge current auxiliary tree with the upper-level one.
    // The merge process makes sure the current node is the "deepest" one in the merged auxiliary tree (by cutting off
    // irrelevant subtrees).
    // After the extension, current node is the root of the merged tree.
    // Return false if there is no upper level path.
    unsafe fn extend_upper_level_path(mut this: NonNull<Self>) -> bool {
        Self::splay(this);
        match this.as_ref().path_parent {
            None => false,
            Some(mut upper) => {
                Self::separate_deeper_nodes(upper);
                this.as_mut().tree_parent = Some(upper);
                this.as_mut().path_parent = None;
                upper.as_mut().tree_right = Some(this);
                true
            }
        }
    }

    // Extend the auxiliary tree all the way to root.
    // After the extension, current node is the root of its auxiliary tree.
    unsafe fn extend_to_root(this: NonNull<Self>) {
        Self::separate_deeper_nodes(this);
        while Self::extend_upper_level_path(this) {}
    }

    // Lift the node to the root of its tree (not the auxiliary tree).
    // To do so, we first extend the auxiliary tree to root, which represents the path from root to the current node.
    // To set the current node as root, we reverse the order of the auxiliary tree such that previous
    // root (who has the least depth) now has the deepest depth and the current node (who has the deepest depth) now has
    // the lowest depth.
    unsafe fn lift_to_root(mut this: NonNull<Self>) {
        Self::extend_to_root(this);
        Self::splay(this);
        this.as_mut().tree_reversed = !this.as_ref().tree_reversed;
    }

    unsafe fn find_min(mut current: NonNull<Self>) -> NonNull<Node> {
        Self::push_down(current);
        while let Some(left) = current.as_ref().tree_left {
            current = left;
            Self::push_down(current);
        }
        Self::splay(current);
        current
    }
}

impl Handle {
    /// Create a new handle.
    pub fn new() -> Self {
        Node::allocate()
    }
    /// Check if two nodes are connected.
    /// A node is connected to itself.
    /// This operation is O(log n).
    /// # Examples
    /// ```
    /// use dynforest::Handle;
    /// let a = Handle::new();
    /// let b = Handle::new();
    /// assert!(!a.is_connected(&b));
    /// let _conn = a.connect(&b);
    /// assert!(a.is_connected(&b));
    /// ```
    pub fn is_connected(&self, other: &Self) -> bool {
        if Rc::ptr_eq(&self.target, &other.target) {
            return true;
        }
        unsafe {
            let this = NonNull::new_unchecked(self.target.get());
            let other = NonNull::new_unchecked(other.target.get());
            Node::lift_to_root(this);
            Node::extend_to_root(other);
            Node::splay(other);
            core::ptr::eq(Node::find_min(other).as_ptr(), this.as_ptr())
        }
    }
    /// Connect two nodes without checking if they are already connected.
    /// # Safety
    /// The caller must ensure that the two handles are not connected.
    pub unsafe fn connect_unchecked(&self, other: &Self) -> Connection {
        {
            let this = NonNull::new_unchecked(self.target.get());
            let mut other = NonNull::new_unchecked(other.target.get());
            Node::lift_to_root(other);
            other.as_mut().path_parent = Some(this);
        }
        Connection {
            targets: [self.target.clone(), other.target.clone()],
        }
    }
    /// Connect two nodes.
    /// Return `None` if they are already connected.
    /// A node is always connected to itself.
    /// This operation is O(log n).
    /// # Examples
    /// ```
    /// use dynforest::Handle;
    /// let a = Handle::new();
    /// let b = Handle::new();
    /// let conn1 = a.connect(&b);
    /// assert!(conn1.is_some());
    /// assert!(a.is_connected(&b));
    /// assert!(b.is_connected(&a));
    /// let c = Handle::new();
    /// let conn2 = b.connect(&c);
    /// assert!(conn2.is_some());
    /// assert!(a.is_connected(&c));
    /// // a and c are already connected
    /// let conn3 = a.connect(&c);
    /// assert!(conn3.is_none());
    /// ```
    pub fn connect(&self, other: &Self) -> Option<Connection> {
        if self.is_connected(other) {
            return None;
        }
        Some(unsafe { self.connect_unchecked(other) })
    }
}

impl Default for Handle {
    fn default() -> Self {
        Self::new()
    }
}

impl PartialEq for Handle {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.target, &other.target)
    }
}

impl Eq for Handle {}

impl Drop for Connection {
    fn drop(&mut self) {
        unsafe {
            let x = NonNull::new_unchecked(self.targets[0].get());
            let mut y = NonNull::new_unchecked(self.targets[1].get());
            Node::lift_to_root(x);
            Node::extend_to_root(y);
            Node::splay(y);
            Node::push_down(y);
            debug_assert!(y.as_ref().tree_left.is_some());
            y.as_ref().tree_left.unwrap_unchecked().as_mut().tree_parent = None;
            y.as_mut().tree_left = None;
        }
    }
}

#[cfg(test)]
mod test {
    extern crate std;

    use super::*;
    use alloc::vec::Vec;

    #[test]
    fn test_trivial_connection() {
        let a = Handle::new();
        let b = Handle::new();
        let c = Handle::new();
        let d = Handle::new();
        let e = Handle::new();

        let handles = [a.clone(), b.clone(), c.clone(), d.clone(), e.clone()];

        for i in handles.iter() {
            for j in handles.iter() {
                assert!(!i.is_connected(j) || i == j);
            }
        }

        let _ab = a.connect(&b).unwrap();
        let cd = c.connect(&d).unwrap();

        assert!(a.is_connected(&b));
        assert!(b.is_connected(&a));
        assert!(c.is_connected(&d));
        assert!(d.is_connected(&c));

        for i in [a.clone(), b.clone()] {
            for j in [c.clone(), d.clone(), e.clone()] {
                assert!(!i.is_connected(&j));
            }
        }

        for i in [c.clone(), d.clone()] {
            for j in [a.clone(), b.clone(), e.clone()] {
                assert!(!i.is_connected(&j));
            }
        }

        for i in [a.clone(), b.clone(), c.clone(), d.clone()] {
            assert!(!i.is_connected(&e));
        }

        let _eb = e.connect(&b).unwrap();
        let _ad = a.connect(&d).unwrap();

        for i in handles.iter() {
            for j in handles.iter() {
                assert!(i.is_connected(j));
            }
        }

        drop(cd);

        for i in [a.clone(), b.clone(), d.clone(), e.clone()] {
            for j in [a.clone(), b.clone(), d.clone(), e.clone()] {
                assert!(i.is_connected(&j));
                assert!(!c.is_connected(&i));
                assert!(!i.is_connected(&c));
            }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn test_large_forests() {
        const LENGTH: usize = 1000;
        const STEP: usize = LENGTH / 10;
        let mut handles = Vec::new();
        let mut connections = std::collections::HashMap::new();
        for _ in 0..LENGTH {
            handles.push(Handle::new());
        }
        for i in 1..LENGTH {
            connections.insert((i - 1, i), handles[i - 1].connect(&handles[i]).unwrap());
        }
        for i in 0..LENGTH {
            for j in 0..LENGTH {
                assert!(handles[i].is_connected(&handles[j]));
            }
        }
        for i in (STEP..LENGTH).step_by(STEP) {
            connections.remove(&(i - 1, i));
        }
        for i in (0..LENGTH).step_by(STEP) {
            for j in i..(i + STEP) {
                for k in i..(i + STEP) {
                    assert!(handles[j].is_connected(&handles[k]));
                }
            }
        }
        for i in (0..LENGTH).step_by(STEP) {
            for j in i..(i + STEP) {
                for k in 0..i {
                    assert!(!handles[j].is_connected(&handles[k]));
                }
                for k in i + STEP..LENGTH {
                    assert!(!handles[j].is_connected(&handles[k]));
                }
            }
        }

        let mut count = 0;

        for i in 0..(LENGTH / STEP - 1) {
            let a = handles[count + STEP + i].clone();
            let b = handles[count + i].clone();
            let handle = a.connect(&b).unwrap();
            connections.insert((count + i, count + STEP + i), handle);
            count += STEP;
        }

        for i in 0..LENGTH {
            for j in 0..LENGTH {
                assert!(handles[i].is_connected(&handles[j]));
            }
        }

        for i in (0..(LENGTH / 2 - STEP)).step_by(STEP) {
            connections
                .remove(&(i + (STEP / 2) - 1, i + (STEP / 2)))
                .unwrap();
            for j in (i + STEP / 2)..(i + STEP) {
                for k in (i + STEP / 2)..(i + STEP) {
                    assert!(handles[j].is_connected(&handles[k]));
                }
            }
            for j in (i + STEP / 2)..(i + STEP) {
                for k in 0..(i + STEP / 2) {
                    assert!(!handles[j].is_connected(&handles[k]));
                }
            }
            for j in (i + STEP / 2)..(i + STEP) {
                for k in (i + STEP)..LENGTH {
                    assert!(!handles[j].is_connected(&handles[k]));
                }
            }
            let a = handles[i + (STEP / 2) - 1].clone();
            let mut b = handles[i + (STEP / 2)].clone();
            connections.insert(
                (i + (STEP / 2) - 1, i + (STEP / 2)),
                a.connect(&mut b).unwrap(),
            );
        }

        for i in 0..LENGTH {
            for j in 0..LENGTH {
                assert!(handles[i].is_connected(&handles[j]));
            }
        }
    }

    #[test]
    fn test_random() {
        #[cfg(not(miri))]
        const LENGTH: usize = 200;

        #[cfg(miri)]
        const LENGTH: usize = 15;
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let mut handles = Vec::new();
        let mut connections = std::collections::HashMap::new();
        for _ in 0..LENGTH {
            handles.push(Handle::new());
        }
        for _ in 0..10 * LENGTH {
            let i = rng.gen_range(0..LENGTH - 1);
            let j = rng.gen_range(0..(i + 1));
            if i == j {
                continue;
            }
            if let std::collections::hash_map::Entry::Vacant(e) = connections.entry((j, i)) {
                let a = handles[i].clone();
                let b = handles[j].clone();
                if let Some(h) = a.connect(&b) {
                    e.insert(h);
                }
            } else {
                assert!(handles[i].is_connected(&handles[j]));
                connections.remove(&(j, i));
                assert!(!handles[j].is_connected(&handles[i]));
            }
        }
        for i in 0..LENGTH {
            for j in i..LENGTH {
                if i == j || connections.contains_key(&(i, j)) {
                    assert!(handles[i].is_connected(&handles[j]));
                }
            }
        }
        for i in 0..LENGTH {
            // symmetric
            assert!(handles[i].is_connected(&handles[i]));
            for j in i..LENGTH {
                if handles[i].is_connected(&handles[j]) {
                    // reflexive
                    assert!(handles[j].is_connected(&handles[i]));
                    for k in 0..LENGTH {
                        if handles[j].is_connected(&handles[k]) {
                            // transitive
                            assert!(handles[i].is_connected(&handles[k]));
                        }
                    }
                }
            }
        }
    }
}
