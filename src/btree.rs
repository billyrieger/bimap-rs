//! A bimap backed by two `BTreeMap`s.

use crate::Overwritten;
cfg_if::cfg_if! {
    if #[cfg(feature = "std")] {
        use std::{
            cmp::Ordering,
            collections::{btree_map, BTreeMap},
            fmt,
            iter::{FromIterator, FusedIterator},
            rc::Rc,
        };
    } else {
        use core::{
            cmp::Ordering,
            fmt,
            iter::{FromIterator, FusedIterator},
        };
        use alloc::{collections::{btree_map, BTreeMap }, rc::Rc};
    }
}

/// A bimap backed by two `BTreeMap`s.
///
/// See the [module-level documentation] for more details and examples.
///
/// [module-level documentation]: crate
pub struct BiBTreeMap<L, R> {
    left2right: BTreeMap<Rc<L>, Rc<R>>,
    right2left: BTreeMap<Rc<R>, Rc<L>>,
}

impl<L, R> BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
    /// Creates an empty `BiBTreeMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let bimap = BiBTreeMap::<char, i32>::new();
    /// ```
    pub fn new() -> Self {
        Self {
            left2right: BTreeMap::new(),
            right2left: BTreeMap::new(),
        }
    }

    /// Returns the number of left-right pairs in the bimap.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    /// assert_eq!(bimap.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.left2right.len()
    }

    /// Returns `true` if the bimap contains no left-right pairs, and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// assert!(bimap.is_empty());
    /// bimap.insert('a', 1);
    /// assert!(!bimap.is_empty());
    /// bimap.remove_by_right(&1);
    /// assert!(bimap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.left2right.is_empty()
    }

    /// Removes all left-right pairs from the bimap.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    /// bimap.clear();
    /// assert!(bimap.len() == 0);
    /// ```
    pub fn clear(&mut self) {
        self.left2right.clear();
        self.right2left.clear();
    }

    /// Creates an iterator over the left-right pairs in the bimap in ascending order by left
    /// value.
    ///
    /// The iterator element type is `(&L, &R)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    ///
    /// for (left, right) in bimap.iter() {
    ///     println!("({}, {})", left, right);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, L, R> {
        Iter {
            inner: self.left2right.iter(),
        }
    }

    /// Creates an iterator over the left values in the bimap in ascending order.
    ///
    /// The iterator element type is `&L`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    ///
    /// for char_value in bimap.left_values() {
    ///     println!("{}", char_value);
    /// }
    /// ```
    pub fn left_values(&self) -> LeftValues<'_, L, R> {
        LeftValues {
            inner: self.left2right.iter(),
        }
    }

    /// Creates an iterator over the right values in the bimap in ascending order.
    ///
    /// The iterator element type is `&R`.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    ///
    /// for int_value in bimap.right_values() {
    ///     println!("{}", int_value);
    /// }
    /// ```
    pub fn right_values(&self) -> RightValues<'_, L, R> {
        RightValues {
            inner: self.right2left.iter(),
        }
    }

    /// Returns a reference to the right value corresponding to the given left value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// assert_eq!(bimap.get_by_left(&'a'), Some(&1));
    /// assert_eq!(bimap.get_by_left(&'z'), None);
    /// ```
    pub fn get_by_left(&self, left: &L) -> Option<&R> {
        self.left2right.get(left).map(|l| &**l)
    }

    /// Returns a reference to the left value corresponding to the given right value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// assert_eq!(bimap.get_by_right(&1), Some(&'a'));
    /// assert_eq!(bimap.get_by_right(&2), None);
    /// ```
    pub fn get_by_right(&self, right: &R) -> Option<&L> {
        self.right2left.get(right).map(|r| &**r)
    }

    /// Returns `true` if the bimap contains the given left value and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// assert!(bimap.contains_left(&'a'));
    /// assert!(!bimap.contains_left(&'b'));
    /// ```
    pub fn contains_left(&self, left: &L) -> bool {
        self.left2right.contains_key(left)
    }

    /// Returns `true` if the map contains the given right value and `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// assert!(bimap.contains_right(&1));
    /// assert!(!bimap.contains_right(&2));
    /// ```
    pub fn contains_right(&self, right: &R) -> bool {
        self.right2left.contains_key(right)
    }

    /// Removes the left-right pair corresponding to the given left value.
    ///
    /// Returns the previous left-right pair if the map contained the left value and `None`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    ///
    /// assert_eq!(bimap.remove_by_left(&'b'), Some(('b', 2)));
    /// assert_eq!(bimap.remove_by_left(&'b'), None);
    /// ```
    pub fn remove_by_left(&mut self, left: &L) -> Option<(L, R)> {
        self.left2right.remove(left).map(|right_rc| {
            // unwrap is safe because we know right2left contains the key (it's a bimap)
            let left_rc = self.right2left.remove(&right_rc).unwrap();
            // at this point we can safely unwrap because the other pointers are gone
            (
                Rc::try_unwrap(left_rc).ok().unwrap(),
                Rc::try_unwrap(right_rc).ok().unwrap(),
            )
        })
    }

    /// Removes the left-right pair corresponding to the given right value.
    ///
    /// Returns the previous left-right pair if the map contained the right value and `None`
    /// otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    ///
    /// assert_eq!(bimap.remove_by_right(&2), Some(('b', 2)));
    /// assert_eq!(bimap.remove_by_right(&2), None);
    /// ```
    pub fn remove_by_right(&mut self, right: &R) -> Option<(L, R)> {
        self.right2left.remove(right).map(|left_rc| {
            // unwrap is safe because we know left2right contains the key (it's a bimap)
            let right_rc = self.left2right.remove(&left_rc).unwrap();
            // at this point we can safely unwrap because the other pointers are gone
            (
                Rc::try_unwrap(left_rc).ok().unwrap(),
                Rc::try_unwrap(right_rc).ok().unwrap(),
            )
        })
    }

    /// Inserts the given left-right pair into the bimap.
    ///
    /// Returns an enum `Overwritten` representing any left-right pairs that were overwritten by
    /// the call to `insert`. The example below details all possible enum variants that can be
    /// returned.
    ///
    /// # Warnings
    ///
    /// Somewhat paradoxically, calling `insert()` can actually reduce the size of the bimap! This
    /// is because of the invariant that each left value maps to exactly one right value and vice
    /// versa.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::{BiBTreeMap, Overwritten};
    ///
    /// let mut bimap = BiBTreeMap::new();
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
    /// // ('b', 2) already exists, so inserting ('c', 2) overwrites 2, the right value.
    /// // the previous left-right pair ('b', 2) is returned.
    /// assert_eq!(bimap.insert('c', 2), Overwritten::Right('b', 2));
    /// assert_eq!(bimap.len(), 2); // {'a' <> 1, 'c' <> 2}
    ///
    /// // both ('a', 4) and ('c', 2) already exist, so inserting ('a', 2) overwrites both.
    /// // ('a', 4) has the overwritten left value ('a'), so it's the first tuple returned.
    /// // ('c', 2) has the overwritten right value (2), so it's the second tuple returned.
    /// assert_eq!(bimap.insert('a', 2), Overwritten::Both(('a', 4), ('c', 2)));
    /// assert_eq!(bimap.len(), 1); // {'a' <> 2} // bimap is smaller than before!
    ///
    /// // ('a', 2) already exists, so inserting ('a', 2) overwrites the pair.
    /// // the previous left-right pair ('a', 2) is returned.
    /// assert_eq!(bimap.insert('a', 2), Overwritten::Pair('a', 2));
    /// assert_eq!(bimap.len(), 1); // {'a' <> 2}
    /// ```
    pub fn insert(&mut self, left: L, right: R) -> Overwritten<L, R> {
        let retval = match (self.remove_by_left(&left), self.remove_by_right(&right)) {
            (None, None) => Overwritten::Neither,
            (None, Some(r_pair)) => Overwritten::Right(r_pair.0, r_pair.1),
            (Some(l_pair), None) => {
                // since remove_by_left() was called first, it's possible the right value was
                // removed if a duplicate pair is being inserted
                if l_pair.1 == right {
                    Overwritten::Pair(l_pair.0, l_pair.1)
                } else {
                    Overwritten::Left(l_pair.0, l_pair.1)
                }
            }
            (Some(l_pair), Some(r_pair)) => Overwritten::Both(l_pair, r_pair),
        };
        self.insert_unchecked(left, right);
        retval
    }

    /// Inserts the given left-right pair into the bimap without overwriting any existing values.
    ///
    /// Returns `Ok(())` if the pair was successfully inserted into the bimap. If either value
    /// exists in the map, `Err((left, right)` is returned with the attempted left-right pair and
    /// the map is unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use bimap::BiBTreeMap;
    ///
    /// let mut bimap = BiBTreeMap::new();
    /// assert_eq!(bimap.insert_no_overwrite('a', 1), Ok(()));
    /// assert_eq!(bimap.insert_no_overwrite('b', 2), Ok(()));
    /// assert_eq!(bimap.insert_no_overwrite('a', 3), Err(('a', 3)));
    /// assert_eq!(bimap.insert_no_overwrite('c', 2), Err(('c', 2)));
    /// ```
    pub fn insert_no_overwrite(&mut self, left: L, right: R) -> Result<(), (L, R)> {
        if self.contains_left(&left) || self.contains_right(&right) {
            Err((left, right))
        } else {
            self.insert_unchecked(left, right);
            Ok(())
        }
    }

    /// Inserts the given left-right pair into the bimap without checking if the pair already
    /// exists.
    fn insert_unchecked(&mut self, left: L, right: R) {
        let left_rc = Rc::new(left);
        let right_rc = Rc::new(right);
        self.left2right.insert(left_rc.clone(), right_rc.clone());
        self.right2left.insert(right_rc, left_rc);
    }
}

impl<L, R> Clone for BiBTreeMap<L, R>
where
    L: Clone + Ord,
    R: Clone + Ord,
{
    fn clone(&self) -> BiBTreeMap<L, R> {
        self.iter().map(|(l, r)| (l.clone(), r.clone())).collect()
    }
}

impl<L, R> fmt::Debug for BiBTreeMap<L, R>
where
    L: fmt::Debug + Ord,
    R: fmt::Debug + Ord,
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

impl<L, R> Default for BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
    fn default() -> BiBTreeMap<L, R> {
        BiBTreeMap {
            left2right: BTreeMap::default(),
            right2left: BTreeMap::default(),
        }
    }
}

impl<L, R> Eq for BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
}

impl<L, R> FromIterator<(L, R)> for BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
    fn from_iter<I>(iter: I) -> BiBTreeMap<L, R>
    where
        I: IntoIterator<Item = (L, R)>,
    {
        let mut bimap = BiBTreeMap::new();
        for (left, right) in iter {
            bimap.insert(left, right);
        }
        bimap
    }
}

impl<'a, L, R> IntoIterator for &'a BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
    type Item = (&'a L, &'a R);
    type IntoIter = Iter<'a, L, R>;

    fn into_iter(self) -> Iter<'a, L, R> {
        self.iter()
    }
}

impl<L, R> IntoIterator for BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
    type Item = (L, R);
    type IntoIter = IntoIter<L, R>;

    fn into_iter(self) -> IntoIter<L, R> {
        IntoIter {
            inner: self.left2right.into_iter(),
        }
    }
}

impl<L, R> Ord for BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.left2right.cmp(&other.left2right)
    }
}

impl<L, R> PartialEq for BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
    fn eq(&self, other: &Self) -> bool {
        self.left2right == other.left2right
    }
}

impl<L, R> PartialOrd for BiBTreeMap<L, R>
where
    L: Ord,
    R: Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.left2right.partial_cmp(&other.left2right)
    }
}

/// An owning iterator over the left-right pairs in a `BiBTreeMap`.
pub struct IntoIter<L, R> {
    inner: btree_map::IntoIter<Rc<L>, Rc<R>>,
}

impl<L, R> DoubleEndedIterator for IntoIter<L, R> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // unwraps are safe because right2left is gone
        self.inner.next_back().map(|(l, r)| {
            (
                Rc::try_unwrap(l).ok().unwrap(),
                Rc::try_unwrap(r).ok().unwrap(),
            )
        })
    }
}

impl<L, R> ExactSizeIterator for IntoIter<L, R> {}

impl<L, R> FusedIterator for IntoIter<L, R> {}

impl<L, R> Iterator for IntoIter<L, R> {
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        // unwraps are safe because right2left is gone
        self.inner.next().map(|(l, r)| {
            (
                Rc::try_unwrap(l).ok().unwrap(),
                Rc::try_unwrap(r).ok().unwrap(),
            )
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the left-right pairs in a `BiBTreeMap`.
///
/// This struct is created by the [`iter`] method of `BiBTreeMap`.
///
/// [`iter`]: BiBTreeMap::iter
pub struct Iter<'a, L, R> {
    inner: btree_map::Iter<'a, Rc<L>, Rc<R>>,
}

impl<'a, L, R> DoubleEndedIterator for Iter<'a, L, R> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(l, r)| (&**l, &**r))
    }
}

impl<'a, L, R> ExactSizeIterator for Iter<'a, L, R> {}

impl<'a, L, R> FusedIterator for Iter<'a, L, R> {}

impl<'a, L, R> Iterator for Iter<'a, L, R> {
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, r)| (&**l, &**r))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the left values in a `BiBTreeMap`.
///
/// This struct is created by the [`left_values`] method of `BiBTreeMap`.
///
/// [`left_values`]: BiBTreeMap::left_values
pub struct LeftValues<'a, L, R> {
    inner: btree_map::Iter<'a, Rc<L>, Rc<R>>,
}

impl<'a, L, R> DoubleEndedIterator for LeftValues<'a, L, R> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(l, _)| &**l)
    }
}

impl<'a, L, R> ExactSizeIterator for LeftValues<'a, L, R> {}

impl<'a, L, R> FusedIterator for LeftValues<'a, L, R> {}

impl<'a, L, R> Iterator for LeftValues<'a, L, R> {
    type Item = &'a L;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, _)| &**l)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An iterator over the right values in a `BiBTreeMap`.
///
/// This struct is created by the [`right_values`] method of `BiBTreeMap`.
///
/// [`right_values`]: BiBTreeMap::right_values
pub struct RightValues<'a, L, R> {
    inner: btree_map::Iter<'a, Rc<R>, Rc<L>>,
}

impl<'a, L, R> DoubleEndedIterator for RightValues<'a, L, R> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(r, _)| &**r)
    }
}

impl<'a, L, R> ExactSizeIterator for RightValues<'a, L, R> {}

impl<'a, L, R> FusedIterator for RightValues<'a, L, R> {}

impl<'a, L, R> Iterator for RightValues<'a, L, R> {
    type Item = &'a R;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(r, _)| &**r)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

// safe because internal Rcs are not exposed by the api and the reference counts only change in
// methods with &mut self
unsafe impl<L, R> Send for BiBTreeMap<L, R>
where
    L: Send,
    R: Send,
{
}
unsafe impl<L, R> Sync for BiBTreeMap<L, R>
where
    L: Sync,
    R: Sync,
{
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clone() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 1);
        bimap.insert('b', 2);
        let bimap2 = bimap.clone();
        assert_eq!(bimap, bimap2);
    }

    #[test]
    fn deep_clone() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 1);
        bimap.insert('b', 2);
        let mut bimap2 = bimap.clone();

        // would panic if clone() didn't deep clone
        bimap.insert('b', 5);
        bimap2.insert('a', 12);
        bimap2.remove_by_left(&'a');
        bimap.remove_by_right(&2);
    }

    #[test]
    fn debug() {
        let mut bimap = BiBTreeMap::new();
        assert_eq!("{}", format!("{:?}", bimap));

        bimap.insert('a', 1);
        assert_eq!("{'a' <> 1}", format!("{:?}", bimap));

        bimap.insert('b', 2);
        assert_eq!("{'a' <> 1, 'b' <> 2}", format!("{:?}", bimap));
    }

    #[test]
    fn default() {
        let _ = BiBTreeMap::<char, i32>::default();
    }

    #[test]
    fn eq() {
        let mut bimap = BiBTreeMap::new();
        assert_eq!(bimap, bimap);
        bimap.insert('a', 1);
        assert_eq!(bimap, bimap);
        bimap.insert('b', 2);
        assert_eq!(bimap, bimap);

        let mut bimap2 = BiBTreeMap::new();
        assert_ne!(bimap, bimap2);
        bimap2.insert('a', 1);
        assert_ne!(bimap, bimap2);
        bimap2.insert('b', 2);
        assert_eq!(bimap, bimap2);
        bimap2.insert('c', 3);
        assert_ne!(bimap, bimap2);
    }

    #[test]
    fn from_iter() {
        let bimap = BiBTreeMap::from_iter(vec![
            ('a', 1),
            ('b', 2),
            ('c', 3),
            ('b', 2),
            ('a', 4),
            ('b', 3),
        ]);
        let mut bimap2 = BiBTreeMap::new();
        bimap2.insert('a', 4);
        bimap2.insert('b', 3);
        assert_eq!(bimap, bimap2);
    }

    #[test]
    fn into_iter() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 3);
        bimap.insert('b', 2);
        bimap.insert('c', 1);
        let pairs = bimap.into_iter().collect::<Vec<_>>();
        assert_eq!(pairs, vec![('a', 3), ('b', 2), ('c', 1)]);
    }

    #[test]
    fn into_iter_ref() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 3);
        bimap.insert('b', 2);
        bimap.insert('c', 1);
        let pairs = (&bimap).into_iter().collect::<Vec<_>>();
        assert_eq!(pairs, vec![(&'a', &3), (&'b', &2), (&'c', &1)]);
    }

    #[test]
    fn cmp() {
        let bimap = BiBTreeMap::from_iter(vec![('a', 2)]);
        let bimap2 = BiBTreeMap::from_iter(vec![('b', 1)]);

        assert_eq!(bimap.partial_cmp(&bimap2), Some(Ordering::Less));
        assert_eq!(bimap.cmp(&bimap2), Ordering::Less);

        assert_eq!(bimap2.partial_cmp(&bimap), Some(Ordering::Greater));
        assert_eq!(bimap2.cmp(&bimap), Ordering::Greater);

        assert_eq!(bimap.cmp(&bimap), Ordering::Equal);
        assert_eq!(bimap2.cmp(&bimap2), Ordering::Equal);
    }

    #[test]
    fn iter() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 1);
        bimap.insert('b', 2);
        bimap.insert('c', 3);
        let pairs = bimap.iter().map(|(c, i)| (*c, *i)).collect::<Vec<_>>();
        assert_eq!(pairs, vec![('a', 1), ('b', 2), ('c', 3)]);
    }

    #[test]
    fn iter_rev() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 1);
        bimap.insert('b', 2);
        bimap.insert('c', 3);

        let mut iter = bimap.iter();
        assert_eq!(iter.next_back(), Some((&'c', &3)));
        assert_eq!(iter.next_back(), Some((&'b', &2)));
        assert_eq!(iter.next_back(), Some((&'a', &1)));
    }

    #[test]
    fn into_iter_rev() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 1);
        bimap.insert('b', 2);
        bimap.insert('c', 3);

        let mut iter = bimap.into_iter();
        assert_eq!(iter.next_back(), Some(('c', 3)));
        assert_eq!(iter.next_back(), Some(('b', 2)));
        assert_eq!(iter.next_back(), Some(('a', 1)));
    }

    #[test]
    fn left_values() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 3);
        bimap.insert('b', 2);
        bimap.insert('c', 1);
        let left_values = bimap.left_values().cloned().collect::<Vec<_>>();
        assert_eq!(left_values, vec!['a', 'b', 'c'])
    }

    #[test]
    fn left_values_rev() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 3);
        bimap.insert('b', 2);
        bimap.insert('c', 1);

        let mut iter = bimap.left_values();
        assert_eq!(iter.next_back(), Some(&'c'));
        assert_eq!(iter.next_back(), Some(&'b'));
        assert_eq!(iter.next_back(), Some(&'a'));
    }

    #[test]
    fn right_values() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 3);
        bimap.insert('b', 2);
        bimap.insert('c', 1);
        let right_values = bimap.right_values().cloned().collect::<Vec<_>>();
        assert_eq!(right_values, vec![1, 2, 3])
    }

    #[test]
    fn right_values_rev() {
        let mut bimap = BiBTreeMap::new();
        bimap.insert('a', 3);
        bimap.insert('b', 2);
        bimap.insert('c', 1);

        let mut iter = bimap.right_values();
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next_back(), Some(&2));
        assert_eq!(iter.next_back(), Some(&1));
    }

    #[test]
    fn clear() {
        let mut bimap = BiBTreeMap::from_iter(vec![('a', 1)]);
        assert_eq!(bimap.len(), 1);
        assert!(!bimap.is_empty());

        bimap.clear();

        assert_eq!(bimap.len(), 0);
        assert!(bimap.is_empty());
    }

    #[test]
    fn get_contains() {
        let bimap = BiBTreeMap::from_iter(vec![('a', 1)]);

        assert_eq!(bimap.get_by_left(&'a'), Some(&1));
        assert!(bimap.contains_left(&'a'));

        assert_eq!(bimap.get_by_left(&'b'), None);
        assert!(!bimap.contains_left(&'b'));

        assert_eq!(bimap.get_by_right(&1), Some(&'a'));
        assert!(bimap.contains_right(&1));

        assert_eq!(bimap.get_by_right(&2), None);
        assert!(!bimap.contains_right(&2));
    }

    #[test]
    fn insert() {
        let mut bimap = BiBTreeMap::new();

        assert_eq!(bimap.insert('a', 1), Overwritten::Neither);
        assert_eq!(bimap.insert('a', 2), Overwritten::Left('a', 1));
        assert_eq!(bimap.insert('b', 2), Overwritten::Right('a', 2));
        assert_eq!(bimap.insert('b', 2), Overwritten::Pair('b', 2));

        assert_eq!(bimap.insert('c', 3), Overwritten::Neither);
        assert_eq!(bimap.insert('b', 3), Overwritten::Both(('b', 2), ('c', 3)));
    }

    #[test]
    fn insert_no_overwrite() {
        let mut bimap = BiBTreeMap::new();

        assert!(bimap.insert_no_overwrite('a', 1).is_ok());
        assert!(bimap.insert_no_overwrite('a', 2).is_err());
        assert!(bimap.insert_no_overwrite('b', 1).is_err());
    }
}
