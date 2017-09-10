//! A fast two-way bijective map.
//!
//! A `Bimap<L, R>` is a [bijective map] between values of type `L`, called left values, and values
//! of type `R`, called right values. This means every left value is associated with exactly one
//! right value and vice versa. Compare this to a `HashMap<K, V>`, where every key is associated
//! with exactly one value but a value can be associated with more than one key.
//!
//! Internally, a `Bimap` is composed of two `HashMaps`, one for the left-to-right direction and
//! one for right-to-left. As such, the big-O performance of the `get()`, `remove()`, `insert()`,
//! and `contains()` functions are the same as those of a `HashMap`.
//!
//! As with `HashMap`, it is considered a logic error to modify a value's hash while it is in the
//! `Bimap` using a `Cell`, `RefCell`, etc.
//!
//! # Examples
//!
//! ```
//! use bimap::Bimap;
//!
//! let mut elements = Bimap::new();
//!
//! // insert chemicals and their corresponding symbols
//! elements.insert("hydrogen", "H");
//! elements.insert("carbon", "C");
//! elements.insert("bromine", "Br");
//! elements.insert("neodymium", "Nd");
//!
//! // retrieve chemical symbol by name (left to right)
//! assert_eq!(elements.get_by_left(&"bromine"), Some(&"Br"));
//! assert_eq!(elements.get_by_left(&"oxygen"), None);
//!
//! // retrieve name by chemical symbol (right to left)
//! assert_eq!(elements.get_by_right(&"C"), Some(&"carbon"));
//! assert_eq!(elements.get_by_right(&"Al"), None);
//!
//! // check membership
//! assert!(elements.contains_left(&"hydrogen"));
//! assert!(!elements.contains_right(&"He"));
//!
//! // remove elements
//! assert_eq!(elements.remove_by_left(&"neodymium"), Some(("neodymium", "Nd")));
//! assert_eq!(elements.remove_by_right(&"Nd"), None);
//!
//! // iterate over elements
//! for (left, right) in &elements {
//!     println!("the chemical symbol for {} is {}", left, right);
//! }
//! ```
//!
//! [bijective map]: https://en.wikipedia.org/wiki/Bijection

use std::cmp;
use std::collections::HashMap;
use std::collections::hash_map;
use std::fmt;
use std::hash::Hash;
use std::iter::{FromIterator, IntoIterator};
use std::ops::Deref;
use std::rc::Rc;

/// The previous left-right pairs, if any, that were overwritten by a call to `bimap.insert()`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Overwritten<L, R> {
    /// Neither the left nor the right value previously existed in the `Bimap`.
    Neither,

    /// The left value existed in the `Bimap`, and the previous left-right pair is returned.
    Left(L, R),

    /// The right value existed in the `Bimap`, and the previous left-right pair is returned.
    Right(L, R),

    /// Both the left and the right value existed in the `Bimap`, but as part of separate pairs.
    /// The first tuple is the left-right pair of the previous left value, and the second is the
    /// left-right pair of the previous right value.
    Both((L, R), (L, R)),

    /// The left-right pair already existed in the `Bimap`, and the previous left-right pair is
    /// returned.
    Pair(L, R),
}

/// A two-way map between left values and right values.
///
/// See the module-level documentation for more details and examples.
#[derive(Clone)]
pub struct Bimap<L, R> {
    left2right: HashMap<Rc<L>, Rc<R>>,
    right2left: HashMap<Rc<R>, Rc<L>>,
}

impl<L, R> Bimap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    /// Creates an empty `Bimap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap: Bimap<char, u32> = Bimap::new();
    /// ```
    pub fn new() -> Bimap<L, R> {
        Bimap::default()
    }

    /// Creates an empty `Bimap` with the given capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap: Bimap<char, u32> = Bimap::with_capacity(5);
    /// ```
    pub fn with_capacity(capacity: usize) -> Bimap<L, R> {
        Bimap {
            left2right: HashMap::with_capacity(capacity),
            right2left: HashMap::with_capacity(capacity),
        }
    }

    /// Returns the number of left-right pairs in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
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
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
    /// assert!(bimap.is_empty());
    /// bimap.insert('a', 1);
    /// assert!(!bimap.is_empty());
    /// bimap.remove_by_right(&1);
    /// assert!(bimap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Removes all left-right pairs from the `Bimap`, but keeps the allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    /// bimap.clear();
    /// assert!(bimap.len() == 0);
    /// assert!(bimap.capacity() >= 3);
    /// ```
    pub fn clear(&mut self) {
        self.left2right.clear();
        self.right2left.clear();
    }

    /// Returns a lower bound on the number of elements the `Bimap` can store without reallocating
    /// memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap: Bimap<char, u32> = Bimap::with_capacity(5);
    /// assert!(bimap.capacity() >= 5);
    /// ```
    pub fn capacity(&self) -> usize {
        cmp::min(self.left2right.capacity(), self.right2left.capacity())
    }

    /// Create an iterator over the left-right pairs in the `Bimap` in arbitrary order.
    /// The iterator element type is `(&'a L, &'a R)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    ///
    /// for (left, right) in bimap.iter() {
    ///     println!("({}, {})", left, right);
    /// }
    /// ```
    pub fn iter<'a>(&'a self) -> Iter<'a, L, R> {
        Iter { inner: self.left2right.iter() }
    }

    /// Create an iterator over the left values in the `Bimap` in arbitrary order.
    /// The iterator element type is `&'a L`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    ///
    /// for char_value in bimap.left_values() {
    ///     println!("{}", char_value);
    /// }
    /// ```
    pub fn left_values<'a>(&'a self) -> LeftValues<'a, L, R> {
        LeftValues { inner: self.left2right.iter() }
    }

    /// Create an iterator over the right values in the `Bimap` in arbitrary order.
    /// The iterator element type is `&'a R`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    ///
    /// for int_value in bimap.right_values() {
    ///     println!("{}", int_value);
    /// }
    /// ```
    pub fn right_values<'a>(&'a self) -> RightValues<'a, L, R> {
        RightValues { inner: self.left2right.iter() }
    }

    /// Returns a reference to the right value corresponding to the left key.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
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
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
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
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
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
    /// use bimap::Bimap;
    ///
    /// let mut bimap: Bimap<char, u32> = Bimap::new();
    /// bimap.insert('a', 1);
    /// assert!(bimap.contains_right(&1));
    /// assert!(!bimap.contains_right(&2));
    /// ```
    pub fn contains_right(&self, right: &R) -> bool {
        self.right2left.contains_key(right)
    }

    /// Removes the left-right pair correspondin to the given left element.
    ///
    /// Returns the previous left-right pair if the map contained the left element and `None`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    /// assert_eq!(bimap.len(), 3);
    /// assert_eq!(bimap.remove_by_left(&'b'), Some(('b', 2)));
    /// assert_eq!(bimap.len(), 2);
    /// assert_eq!(bimap.remove_by_left(&'b'), None);
    /// assert_eq!(bimap.len(), 2);
    /// ```
    pub fn remove_by_left(&mut self, left: &L) -> Option<(L, R)> {
        self.left2right.remove(left).map(|right_rc| {
            let left_rc = self.right2left.remove(&right_rc).unwrap();
            (
                Rc::try_unwrap(left_rc).ok().unwrap(),
                Rc::try_unwrap(right_rc).ok().unwrap(),
            )
        })
    }

    /// Removes the left-right pair correspondin to the given right element.
    ///
    /// Returns the previous left-right pair if the map contained the right element and `None`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
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
            (
                Rc::try_unwrap(left_rc).ok().unwrap(),
                Rc::try_unwrap(right_rc).ok().unwrap(),
            )
        })
    }

    /// Inserts the given left-right pair into the `Bimap`.
    ///
    /// Returns an enum `Overwritten` representing any left-right pairs that were overwritten by a
    /// call to `insert()`. See the documentation for `Overwritten` and the example below for more
    /// details.
    ///
    /// # Warnings
    ///
    /// Somewhat paradoxically, calling `insert()` can actually reduce the size of the `Bimap`!
    /// This is because of the invariant that each left value maps to exactly one right value and
    /// vice versa. This is detailed in the example below.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::{Bimap, Overwritten};
    ///
    /// let mut bimap = Bimap::<char, u32>::new();
    /// assert_eq!(bimap.len(), 0); // {}
    ///
    /// // no values are overwritten.
    /// assert_eq!(bimap.insert('a', 1), Overwritten::Neither);
    /// assert_eq!(bimap.len(), 1); // {'a' <> 1}
    ///
    /// // no values are overwritten.
    /// assert_eq!(bimap.insert('b', 2), Overwritten::Neither);
    /// assert_eq!(bimap.len(), 2); // {'a' <> 1, 'b' <> 2}
    ///
    /// // ('a', 1) already exists, so inserting ('a', 4) overwrites 'a', the left value.
    /// // the previous left-right pair ('a', 1) is returned.
    /// assert_eq!(bimap.insert('a', 4), Overwritten::Left('a', 1));
    /// assert_eq!(bimap.len(), 2); // {'a' <> 4, 'b' <> 2}
    ///
    /// // ('b', 2) already exists, so inserting ('c', 2) overwrites 2, the right value
    /// // the previous left-right pair ('b', 2) is returned.
    /// assert_eq!(bimap.insert('c', 2), Overwritten::Right('b', 2));
    /// assert_eq!(bimap.len(), 2); // {'a' <> 1, 'c' <> 2}
    ///
    /// // both ('a', 4) and ('c', 2) already exist, so inserting ('a', 2) overwrites both.
    /// // ('c', 2) has the overwritten left value ('c'), so it's the first tuple returned.
    /// // ('a', 4) has the overwritten right value (4), so it's the second tuple returned.
    /// assert_eq!(bimap.insert('a', 2), Overwritten::Both(('c', 2), ('a', 4)));
    /// assert_eq!(bimap.len(), 1); // {'a' <> 2} // bimap is smaller than before!
    ///
    /// // ('a', 2) already exists, so inserting ('a', 2) overwrites the pair.
    /// // the previous left-right pair ('a', 2) is returned.
    /// assert_eq!(bimap.insert('a', 2), Overwritten::Pair('a', 2));
    /// assert_eq!(bimap.len(), 1); // {'a' <> 2}
    /// ```
    pub fn insert(&mut self, left: L, right: R) -> Overwritten<L, R> {
        let retval = match (self.contains_left(&left), self.contains_right(&right)) {
            (false, false) => Overwritten::Neither,
            (true, false) => {
                let prev_pair = self.remove_by_left(&left).unwrap();
                Overwritten::Left(prev_pair.0, prev_pair.1)
            }
            (false, true) => {
                let prev_pair = self.remove_by_right(&right).unwrap();
                Overwritten::Right(prev_pair.0, prev_pair.1)
            }
            (true, true) => {
                if self.get_by_left(&left) == Some(&right) {
                    let prev_pair = self.remove_by_left(&left).unwrap();
                    Overwritten::Pair(prev_pair.0, prev_pair.1)
                } else {
                    let right_overwritten = self.remove_by_left(&left).unwrap();
                    let left_overwritten = self.remove_by_right(&right).unwrap();
                    Overwritten::Both(left_overwritten, right_overwritten)
                }
            }
        };
        let left_rc = Rc::new(left);
        let right_rc = Rc::new(right);
        self.left2right.insert(left_rc.clone(), right_rc.clone());
        self.right2left.insert(right_rc, left_rc);
        retval
    }

    /// Inserts the given left-right pair into the `Bimap` without overwriting any existing values.
    ///
    /// Returns a boolean representing if the pair was successfully inserted into the `Bimap`. If
    /// either value exists in the map, `false` is returned and the map is unchanged. Otherwise,
    /// the pair is inserted and `true` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();
    /// assert!(bimap.insert_no_overwrite('a', 1));
    /// assert!(bimap.insert_no_overwrite('b', 2));
    /// assert!(!bimap.insert_no_overwrite('a', 3));
    /// assert!(!bimap.insert_no_overwrite('c', 2));
    /// ```
    pub fn insert_no_overwrite(&mut self, left: L, right: R) -> bool {
        if self.contains_left(&left) || self.contains_right(&right) {
            false
        } else {
            self.insert(left, right);
            true
        }
    }
}

impl<L, R> fmt::Debug for Bimap<L, R>
where
    L: Eq + Hash + fmt::Debug,
    R: Eq + Hash + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{")?;
        for (i, (left, right)) in self.left2right.iter().enumerate() {
            let comma = if i == 0 { "" } else { ", " };
            write!(f, "{}{:?} <> {:?}", comma, left, right)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<L, R> Default for Bimap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    fn default() -> Bimap<L, R> {
        Bimap {
            left2right: HashMap::default(),
            right2left: HashMap::default(),
        }
    }
}

impl<L, R> Eq for Bimap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
}

impl<L, R> FromIterator<(L, R)> for Bimap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    fn from_iter<I>(iter: I) -> Bimap<L, R>
    where
        I: IntoIterator<Item = (L, R)>,
    {
        let mut bimap = Bimap::new();
        for (left, right) in iter {
            bimap.insert(left, right);
        }
        bimap
    }
}

impl<'a, L, R> IntoIterator for &'a Bimap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    type Item = (&'a L, &'a R);
    type IntoIter = Iter<'a, L, R>;

    fn into_iter(self) -> Iter<'a, L, R> {
        self.iter()
    }
}

impl<L, R> IntoIterator for Bimap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    type Item = (L, R);
    type IntoIter = IntoIter<L, R>;

    fn into_iter(self) -> IntoIter<L, R> {
        IntoIter { inner: self.left2right.into_iter() }
    }
}

impl<L, R> PartialEq for Bimap<L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    fn eq(&self, other: &Bimap<L, R>) -> bool {
        self.left2right == other.left2right
    }
}

/// An owning iterator over the left-right pairs in a `Bimap`.
pub struct IntoIter<L, R> {
    inner: hash_map::IntoIter<Rc<L>, Rc<R>>,
}

impl<L, R> Iterator for IntoIter<L, R> {
    type Item = (L, R);

    fn next(&mut self) -> Option<(L, R)> {
        self.inner.next().map(|(l, r)| {
            (
                Rc::try_unwrap(l).ok().unwrap(),
                Rc::try_unwrap(r).ok().unwrap(),
            )
        })
    }
}

/// An iterator over the left-right pairs in a `Bimap`.
pub struct Iter<'a, L, R>
where
    L: 'a,
    R: 'a,
{
    inner: hash_map::Iter<'a, Rc<L>, Rc<R>>,
}

impl<'a, L, R> Iterator for Iter<'a, L, R> {
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<(&'a L, &'a R)> {
        self.inner.next().map(|(left_rc, right_rc)| {
            (Deref::deref(left_rc), Deref::deref(right_rc))
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the left values in a `Bimap`.
pub struct LeftValues<'a, L, R>
where
    L: 'a,
    R: 'a,
{
    inner: hash_map::Iter<'a, Rc<L>, Rc<R>>,
}

impl<'a, L, R> Iterator for LeftValues<'a, L, R> {
    type Item = &'a L;

    fn next(&mut self) -> Option<&'a L> {
        self.inner.next().map(|(left_rc, _)| Deref::deref(left_rc))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the right values in a `Bimap`.
pub struct RightValues<'a, L, R>
where
    L: 'a,
    R: 'a,
{
    inner: hash_map::Iter<'a, Rc<L>, Rc<R>>,
}

impl<'a, L, R> Iterator for RightValues<'a, L, R> {
    type Item = &'a R;

    fn next(&mut self) -> Option<&'a R> {
        self.inner.next().map(
            |(_, right_rc)| Deref::deref(right_rc),
        )
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clone() {
        let mut bimap = Bimap::new();
        bimap.insert('a', 1);
        bimap.insert('b', 2);
        let bimap2 = bimap.clone();
        assert_eq!(bimap, bimap2);
    }

    #[test]
    fn test_debug() {
        let mut bimap = Bimap::new();

        bimap.insert('a', 1);
        assert_eq!("{'a' <> 1}", format!("{:?}", bimap));

        bimap.insert('b', 2);
        let expected1 = "{'a' <> 1, 'b' <> 2}";
        let expected2 = "{'b' <> 2, 'a' <> 1}";
        let formatted = format!("{:?}", bimap);
        assert!(formatted == expected1 || formatted == expected2);
    }

    #[test]
    fn test_eq() {
        let mut bimap = Bimap::new();
        assert_eq!(bimap, bimap);
        bimap.insert('a', 1);
        assert_eq!(bimap, bimap);
        bimap.insert('b', 2);
        assert_eq!(bimap, bimap);

        let mut bimap2 = Bimap::new();
        assert_ne!(bimap, bimap2);
        bimap2.insert('a', 1);
        assert_ne!(bimap, bimap2);
        bimap2.insert('b', 2);
        assert_eq!(bimap, bimap2);
        bimap2.insert('c', 3);
        assert_ne!(bimap, bimap2);
    }

    #[test]
    fn test_from_iter() {
        let bimap = Bimap::from_iter(vec![
            ('a', 1),
            ('b', 2),
            ('c', 3),
            ('b', 2),
            ('a', 4),
            ('b', 3),
        ]);
        let mut bimap2 = Bimap::with_capacity(3);
        bimap2.insert('a', 4);
        bimap2.insert('b', 3);
        assert_eq!(bimap, bimap2);
    }
}
