use std::collections::HashMap;
use std::collections::hash_map;
use std::fmt;
use std::hash::Hash;
use std::iter::{FromIterator, IntoIterator};
use std::ops::Deref;
use std::rc::Rc;

/// A two-way bijective map backed by `std::collections::HashMap`.
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
    /// let bimap: Bimap<char, u32> = Bimap::new();
    /// ```
    pub fn new() -> Bimap<L, R> {
        Bimap::default()
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

    /// Create an iterator over the left-right pairs in the `Bimap`.
    /// The iterator element type is `(&'iter L, &'iter R)`.
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
    pub fn iter<'iter>(&'iter self) -> Iter<'iter, L, R> {
        Iter { inner: self.left2right.iter() }
    }

    /// Create an iterator over only the left values in the `Bimap`.
    /// The iterator element type is `&'iter L`.
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
    pub fn left_values<'iter>(&'iter self) -> LeftValues<'iter, L, R> {
        LeftValues { inner: self.left2right.iter() }
    }

    /// Create an iterator over only the right values in the `Bimap`.
    /// The iterator element type is `&'iter R`.
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
    pub fn right_values<'iter>(&'iter self) -> RightValues<'iter, L, R> {
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

    /// Removes the given left element.
    /// Returns `Some((left, right))` if the map contained the element and `None` otherwise.
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
    /// assert_eq!(bimap.remove_by_left(&'b'), Some(2));
    /// assert_eq!(bimap.len(), 2);
    /// assert_eq!(bimap.remove_by_left(&'z'), None);
    /// assert_eq!(bimap.len(), 2);
    /// ```
    pub fn remove_by_left(&mut self, left: &L) -> Option<R> {
        self.left2right.remove(left).map(|right_rc| {
            self.right2left.remove(&right_rc);
            Rc::try_unwrap(right_rc).ok().unwrap()
        })
    }

    /// Removes the given right element.
    /// Returns `Some((left, right))` if the map contained the element and `None` otherwise.
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
    /// assert_eq!(bimap.remove_by_right(&2), Some('b'));
    /// assert_eq!(bimap.len(), 2);
    /// assert_eq!(bimap.remove_by_right(&2), None);
    /// assert_eq!(bimap.len(), 2);
    /// ```
    pub fn remove_by_right(&mut self, right: &R) -> Option<L> {
        self.right2left.remove(right).map(|left_rc| {
            self.left2right.remove(&left_rc);
            Rc::try_unwrap(left_rc).ok().unwrap()
        })
    }

    /// Inserts the given left-right pair into the `Bimap`.
    /// If either the left value or the right value already exists, the corresponding entry is
    /// overwritten and the existing pair is returned as `Some((left, right))`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::Bimap;
    ///
    /// let mut bimap = Bimap::new();                           // {}
    /// assert_eq!(bimap.insert('a', 1), (None, None));         // {'a' <> 1}
    /// assert_eq!(bimap.insert('b', 2), (None, None));         // {'a' <> 1, 'b' <> 2}
    /// assert_eq!(bimap.insert('c', 3), (None, None));         // {'a' <> 1, 'b' <> 2, 'c' <> 3}
    /// assert_eq!(bimap.insert('a', 4), (None, Some(1)));      // {'a' <> 4, 'b' <> 2, 'c' <> 3}
    /// assert_eq!(bimap.insert('d', 3), (Some('c'), None));    // {'a' <> 4, 'b' <> 2, 'd' <> 3}
    /// assert_eq!(bimap.insert('a', 2), (Some('b'), Some(4))); // {'a' <> 2, 'd' <> 3}
    /// ```
    pub fn insert(&mut self, left: L, right: R) -> (Option<L>, Option<R>) {
        // get the existing values in the map
        let right_retval = self.remove_by_left(&left);
        let left_retval = self.remove_by_right(&right);
        // create new `Rc`s for the new values
        let left_rc = Rc::new(left);
        let right_rc = Rc::new(right);
        // insert the new `Rc`s into the map
        self.left2right.insert(left_rc.clone(), right_rc.clone());
        self.right2left.insert(right_rc, left_rc);
        // return the preexisting values
        (left_retval, right_retval)
    }
}

impl<L, R> Clone for Bimap<L, R>
where
    L: Clone,
    R: Clone,
{
    fn clone(&self) -> Bimap<L, R> {
        Bimap {
            left2right: self.left2right.clone(),
            right2left: self.right2left.clone(),
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

/// A iterator over the left-right pairs in a `Bimap`.
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

/// A iterator over the left-right pairs in a `Bimap`.
pub struct Iter<'iter, L, R>
where
    L: 'iter,
    R: 'iter,
{
    inner: hash_map::Iter<'iter, Rc<L>, Rc<R>>,
}

impl<'iter, L, R> Iterator for Iter<'iter, L, R> {
    type Item = (&'iter L, &'iter R);

    fn next(&mut self) -> Option<(&'iter L, &'iter R)> {
        self.inner.next().map(|(left_rc, right_rc)| {
            (Deref::deref(left_rc), Deref::deref(right_rc))
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// A iterator over the left values in a `Bimap`.
pub struct LeftValues<'iter, L, R>
where
    L: 'iter,
    R: 'iter,
{
    inner: hash_map::Iter<'iter, Rc<L>, Rc<R>>,
}

impl<'iter, L, R> Iterator for LeftValues<'iter, L, R> {
    type Item = &'iter L;

    fn next(&mut self) -> Option<&'iter L> {
        self.inner.next().map(|(left_rc, _)| Deref::deref(left_rc))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// A iterator over the right values in a `Bimap`.
pub struct RightValues<'iter, L, R>
where
    L: 'iter,
    R: 'iter,
{
    inner: hash_map::Iter<'iter, Rc<L>, Rc<R>>,
}

impl<'iter, L, R> Iterator for RightValues<'iter, L, R> {
    type Item = &'iter R;

    fn next(&mut self) -> Option<&'iter R> {
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
    fn it_works() {
        let mut bimap = Bimap::new();
        bimap.insert('a', 1);
        bimap.insert('b', 2);
        bimap.insert('c', 3);
        for (left, right) in bimap.iter() {
            println!("{}, {}", left, right);
        }
    }
}
