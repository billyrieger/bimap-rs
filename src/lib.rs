use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::Deref;
use std::rc::Rc;

/// A bijective map backed by `std::collections::HashMap`.
pub struct BiMap<L, R> {
    left2right: HashMap<Rc<L>, Rc<R>>,
    right2left: HashMap<Rc<R>, Rc<L>>,
}

impl<L, R> BiMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    /// Creates an empty `BiMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let bimap: BiMap<char, u32> = BiMap::new();
    /// ```
    pub fn new() -> BiMap<L, R> {
        BiMap::default()
    }

    /// Returns the number of left-right pairs in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    /// assert_eq!(bimap.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.left2right.len()
    }

    /// Returns `true` if the map contains no elements, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// assert!(bimap.is_empty());
    /// bimap.insert('a', 1);
    /// assert!(!bimap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a reference to the right value corresponding to the left key.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// bimap.insert('a', 1);
    /// assert_eq!(bimap.get_by_left(&'a'), Some(&1));
    /// assert_eq!(bimap.get_by_left(&'z'), None);
    /// ```
    pub fn get_by_left(&self, left: &L) -> Option<&R> {
        self.left2right.get(left).map(Deref::deref)
    }

    /// Returns a reference to the left value corresponding to the right key.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// bimap.insert('a', 1);
    /// assert_eq!(bimap.get_by_right(&1), Some(&'a'));
    /// assert_eq!(bimap.get_by_right(&2), None);
    /// ```
    pub fn get_by_right(&self, right: &R) -> Option<&L> {
        self.right2left.get(right).map(Deref::deref)
    }

    /// Returns `true` if the map contains the specified left element and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// bimap.insert('a', 1);
    /// assert!(bimap.contains_left(&'a'));
    /// assert!(!bimap.contains_left(&'b'));
    /// ```
    pub fn contains_left(&self, left: &L) -> bool {
        self.left2right.contains_key(left)
    }

    /// Returns `true` if the map contains the specified right element and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap: BiMap<char, u32> = BiMap::new();
    /// bimap.insert('a', 1);
    /// assert!(bimap.contains_right(&1));
    /// assert!(!bimap.contains_right(&2));
    /// ```
    pub fn contains_right(&self, right: &R) -> bool {
        self.right2left.contains_key(right)
    }

    /// Removes the given left element.
    /// Returns `Some((left, right))` if the map contained the element and `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    /// assert_eq!(bimap.len(), 3);
    /// assert_eq!(bimap.remove_by_left(&'b'), Some(('b', 2)));
    /// assert_eq!(bimap.len(), 2);
    /// assert_eq!(bimap.remove_by_left(&'z'), None);
    /// assert_eq!(bimap.len(), 2);
    /// ```
    pub fn remove_by_left(&mut self, left: &L) -> Option<(L, R)> {
        self.left2right.remove(left).map(|right_rc| {
            let left_rc = self.right2left.remove(&right_rc).unwrap();
            (Rc::try_unwrap(left_rc).ok().unwrap(), Rc::try_unwrap(right_rc).ok().unwrap())
        })
    }

    /// Removes the given right element.
    /// Returns `Some((left, right))` if the map contained the element and `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    /// assert_eq!(bimap.len(), 3);
    /// assert_eq!(bimap.remove_by_right(&2), Some(('b', 2)));
    /// assert_eq!(bimap.len(), 2);
    /// assert_eq!(bimap.remove_by_right(&2), None);
    /// assert_eq!(bimap.len(), 2);
    /// ```
    pub fn remove_by_right(&mut self, right: &R) -> Option<(L, R)> {
        self.right2left.remove(right).map(|left_rc| {
            let right_rc = self.left2right.remove(&left_rc).unwrap();
            (Rc::try_unwrap(left_rc).ok().unwrap(), Rc::try_unwrap(right_rc).ok().unwrap())
        })
    }

    /// Inserts the given left-right pair into the `BiMap`.
    /// If either the left value or the right value already exists, the corresponding entry is
    /// overwritten and the existing pair is returned as `Some((left, right))`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// assert_eq!(bimap.insert('a', 1), None);
    /// assert_eq!(bimap.insert('b', 2), None);
    /// assert_eq!(bimap.insert('c', 3), None);
    /// println!("{:?}", bimap); // {'a' <> 1, 'b' <> 2, 'c' <> 3}
    /// bimap.insert('a', 4);
    /// println!("{:?}", bimap);
    /// bimap.insert('c', 2);
    /// println!("{:?}", bimap);
    /// ```
    pub fn insert(&mut self, left: L, right: R) -> Option<(L, R)> {
        let mut retval = if self.contains_left(&left) {
            self.remove_by_left(&left)
        } else {
            None
        };
        retval = retval.or(if self.contains_right(&right) {
            self.remove_by_right(&right)
        } else {
            None
        });
        let left_rc = Rc::new(left);
        let right_rc = Rc::new(right);
        self.left2right.insert(left_rc.clone(), right_rc.clone());
        self.right2left.insert(right_rc, left_rc);
        retval
    }
}

impl<L, R> Clone for BiMap<L, R>
where
    L: Clone,
    R: Clone,
{
    fn clone(&self) -> BiMap<L, R> {
        BiMap {
            left2right: self.left2right.clone(),
            right2left: self.right2left.clone(),
        }
    }
}

impl<L, R> fmt::Debug for BiMap<L, R>
where
    L: Eq + Hash + fmt::Debug,
    R: Eq + Hash + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (left, right)) in self.left2right.iter().enumerate() {
            let comma = if i == 0 { "" } else { ", " };
            write!(f, "{}{:?} <-> {:?}", comma, left, right)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<L, R> Default for BiMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    fn default() -> BiMap<L, R> {
        BiMap {
            left2right: HashMap::default(),
            right2left: HashMap::default(),
        }
    }
}

impl<L, R> Eq for BiMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
}

impl<L, R> FromIterator<(L, R)> for BiMap<L, R> {
    fn from_iter<I>(iter: I) -> BiMap<L, R>
    where
        I: IntoIterator<Item = (L, R)>,
    {
        unimplemented!()
    }
}

impl<L, R> PartialEq for BiMap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    fn eq(&self, other: &BiMap<L, R>) -> bool {
        self.left2right == other.left2right
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut bimap = BiMap::new();
        bimap.insert('a', 1);
        bimap.insert('b', 2);
        bimap.insert('c', 3);
        println!("{:?}\n", bimap);
        bimap.insert('d', 1);
        println!("{:?}\n", bimap);
        bimap.insert('b', 3);
        println!("{:?}\n", bimap);
    }
}
