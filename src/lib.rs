use std::collections::HashMap;
use std::hash::Hash;
use std::ops::Deref;
use std::rc::Rc;

/// A bijective map backed by `std::collections::HashMap`.
pub struct BiHashMap<L, R> {
    left2right: HashMap<Rc<L>, Rc<R>>,
    right2left: HashMap<Rc<R>, Rc<L>>,
}

impl<L, R> Clone for BiHashMap<L, R>
where
    L: Clone,
    R: Clone,
{
    fn clone(&self) -> BiHashMap<L, R> {
        BiHashMap {
            left2right: self.left2right.clone(),
            right2left: self.right2left.clone(),
        }
    }
}

impl<L, R> PartialEq for BiHashMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    fn eq(&self, other: &BiHashMap<L, R>) -> bool {
        self.left2right == other.left2right && self.right2left == other.right2left
    }
}

impl<L, R> Eq for BiHashMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
}

impl<L, R> Default for BiHashMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    fn default() -> BiHashMap<L, R> {
        BiHashMap {
            left2right: HashMap::default(),
            right2left: HashMap::default(),
        }
    }
}

impl<L, R> BiHashMap<L, R> 
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    /// Creates an empty `BiHashMap`.
    pub fn new() -> BiHashMap<L, R> {
        BiHashMap::default()
    }

    /// Returns the number of left-right pairs in the map.
    pub fn len(&self) -> usize {
        self.left2right.len()
    }

    /// Returns `true` if the map contains no elements, and `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a reference to the right value corresponding to the left key.
    pub fn get_by_left(&self, left: &L) -> Option<&R> {
        self.left2right.get(left).map(Deref::deref)
    }

    /// Returns a reference to the left value corresponding to the right key.
    pub fn get_by_right(&self, right: &R) -> Option<&L> {
        self.right2left.get(right).map(Deref::deref)
    }

    /// Returns `true` if the map contains the specified left element, and `false` otherwise.
    pub fn contains_left(&self, left: &L) -> bool {
        self.left2right.contains_key(left)
    }

    /// Returns `true` if the map contains the specified left element, and `false` otherwise.
    pub fn contains_right(&self, right: &R) -> bool {
        self.right2left.contains_key(right)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {}
}
