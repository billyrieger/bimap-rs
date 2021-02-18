use core::borrow::Borrow;
use core::fmt;
use core::iter::FromIterator;
use core::marker::PhantomData;
use core::ops::{Deref, RangeBounds};
use std::iter::FusedIterator;

use crate::maps;
use crate::traits::*;
use crate::util::{deref_pair, swap_pair, Ref};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Overwritten<L, R> {
    One((L, R)),
    Two((L, R), (L, R)),
}

/// A bidirectional map.
#[derive(Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BiMap<LMap, RMap> {
    lmap: LMap,
    rmap: RMap,
}

impl<L, R, LMap, RMap> BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    pub fn new() -> Self {
        Self {
            lmap: LMap::new(),
            rmap: RMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.lmap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.lmap.is_empty()
    }

    pub fn iter(&self) -> Iter<'_, L, R, LMap, RMap> {
        Iter {
            iter: self.lmap.map_iter(),
            marker: PhantomData,
        }
    }

    pub fn try_insert(&mut self, l: L, r: R) -> Result<(), (L, R)> {
        if self.lmap.contains(&l) || self.rmap.contains(&r) {
            Err((l, r))
        } else {
            self.insert_unchecked(l, r);
            Ok(())
        }
    }

    pub fn insert(&mut self, l: L, r: R) -> Option<Overwritten<L, R>> {
        let overwritten = match (self.remove_left(&l), self.remove_right(&r)) {
            (None, None) => None,
            (Some(pair), None) | (None, Some(pair)) => Some(Overwritten::One(pair)),
            (Some(lpair), Some(rpair)) => Some(Overwritten::Two(lpair, rpair)),
        };
        self.insert_unchecked(l, r);
        overwritten
    }

    fn insert_unchecked(&mut self, l: L, r: R) {
        let (l0, l1) = Ref::new(l);
        let (r0, r1) = Ref::new(r);
        self.lmap.insert((l0, r0));
        self.rmap.insert((r1, l1));
    }

    pub fn contains_pair(&self, l: &LMap::Key, r: &RMap::Key) -> bool
    where
        L: Eq,
        R: Eq,
    {
        self.get_left(l) == Some(r)
    }
}

/// # Map methods for the left map
impl<L, R, LMap, RMap> BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    pub fn contains_left<Q: ?Sized>(&self, l: &Q) -> bool
    where
        LMap: Contains<Q>,
    {
        self.lmap.contains(l)
    }

    pub fn get_left<Q: ?Sized>(&self, l: &Q) -> Option<&R>
    where
        LMap: Get<Q>,
    {
        self.lmap.get(l).map(Deref::deref)
    }

    pub fn remove_left<Q: ?Sized>(&mut self, l: &Q) -> Option<(L, R)>
    where
        LMap: Remove<Q>,
    {
        self.lmap.remove(l).map(|(l0, r0)| {
            let (r1, l1) = self.rmap.remove(&r0).unwrap();
            (Ref::join(l0, l1), Ref::join(r0, r1))
        })
    }

    pub fn iter_left(&self) -> IterLeft<'_, L, R, LMap> {
        IterLeft {
            iter: self.lmap.map_iter(),
        }
    }
}

/// # Map methods on the right map
impl<L, R, LMap, RMap> BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    pub fn contains_right<Q: ?Sized>(&self, r: &Q) -> bool
    where
        RMap: Contains<Q>,
    {
        self.rmap.contains(r)
    }

    pub fn get_right<Q: ?Sized>(&self, r: &Q) -> Option<&L>
    where
        RMap: Get<Q>,
    {
        self.rmap.get(r).map(Deref::deref)
    }

    pub fn remove_right<Q: ?Sized>(&mut self, r: &Q) -> Option<(L, R)>
    where
        RMap: Remove<Q>,
    {
        self.rmap.remove(r).map(|(r0, l0)| {
            let (l1, r1) = self.lmap.remove(&l0).unwrap();
            (Ref::join(l0, l1), Ref::join(r0, r1))
        })
    }

    pub fn iter_right(&self) -> IterRight<'_, L, R, RMap> {
        IterRight {
            iter: self.rmap.map_iter(),
        }
    }
}

impl<L, R, RMap> BiMap<maps::btree::InnerMap<L, R>, RMap> {
    pub fn left_range<T: ?Sized, A>(&self, range: A) -> LeftRange<'_, L, R>
    where
        L: Ord + Borrow<T>,
        T: Ord,
        A: RangeBounds<T>,
    {
        LeftRange {
            iter: self.lmap.range(range),
        }
    }
}

impl<L, R, LMap> BiMap<LMap, maps::btree::InnerMap<R, L>> {
    pub fn right_range<T: ?Sized, A>(&self, range: A) -> RightRange<'_, L, R>
    where
        R: Ord + Borrow<T>,
        T: Ord,
        A: RangeBounds<T>,
    {
        RightRange {
            iter: self.rmap.range(range),
        }
    }
}

impl<L, R, LMap, RMap> Clone for BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
    L: Clone,
    R: Clone,
{
    fn clone(&self) -> Self {
        let mut new = Self::new();
        for (l, r) in self {
            new.insert_unchecked(l.clone(), r.clone());
        }
        new
    }
}

impl<L, R, LMap, RMap> Default for BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<L, R, LMap, RMap> fmt::Debug for BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
    L: fmt::Debug,
    R: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self).finish()
    }
}

impl<L, R, LMap, RMap> FromIterator<(L, R)> for BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (L, R)>,
    {
        let mut new = Self::new();
        for (l, r) in iter {
            new.insert(l, r);
        }
        new
    }
}

impl<L, R, LMap, RMap> Extend<(L, R)> for BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (L, R)>,
    {
        for (l, r) in iter {
            self.insert(l, r);
        }
    }
}

// impl<L, R, LMap, RMap> IntoIterator for BiMap<LMap, RMap>
// where
//     LMap: Map<Key = L, Value = R>,
//     RMap: Map<Key = R, Value = L>,
// {
//     type Item = (L, R);
//     type IntoIter = IntoIter<L, R, LMap, RMap>;

//     fn into_iter(self) -> Self::IntoIter {
//         self.into_iter()
//     }
// }

impl<'a, L: 'a, R: 'a, LMap, RMap> IntoIterator for &'a BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    type Item = (&'a L, &'a R);
    type IntoIter = Iter<'a, L, R, LMap, RMap>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct Iter<'a, L: 'a, R: 'a, LMap: Map, RMap: Map> {
    iter: LMap::MapIter<'a, L, R>,
    marker: PhantomData<(LMap, RMap)>,
}

impl<'a, L, R, LMap, RMap> Iterator for Iter<'a, L, R, LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(deref_pair)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct IterLeft<'a, L: 'a, R: 'a, LMap: Map> {
    iter: LMap::MapIter<'a, L, R>,
}

impl<'a, L, R, LMap> Iterator for IterLeft<'a, L, R, LMap>
where
    LMap: Map<Key = L, Value = R>,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(deref_pair)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, L, R, LMap> DoubleEndedIterator for IterLeft<'a, L, R, LMap>
where
    LMap: Map<Key = L, Value = R>,
    LMap::MapIter<'a, L, R>: DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(deref_pair)
    }
}

impl<'a, L, R, LMap> ExactSizeIterator for IterLeft<'a, L, R, LMap>
where
    LMap: Map<Key = L, Value = R>,
    LMap::MapIter<'a, L, R>: ExactSizeIterator,
{
}

impl<'a, L, R, LMap> FusedIterator for IterLeft<'a, L, R, LMap>
where
    LMap: Map<Key = L, Value = R>,
    LMap::MapIter<'a, L, R>: FusedIterator,
{
}

pub struct IterRight<'a, L: 'a, R: 'a, RMap: Map> {
    iter: RMap::MapIter<'a, R, L>,
}

impl<'a, L: 'a, R: 'a, RMap> Iterator for IterRight<'a, L, R, RMap>
where
    RMap: Map<Key = R, Value = L>,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(deref_pair).map(swap_pair)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct LeftRange<'a, L: 'a, R: 'a> {
    iter: maps::btree::Range<'a, L, R>,
}

impl<'a, L, R> Iterator for LeftRange<'a, L, R> {
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(deref_pair)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

pub struct RightRange<'a, L: 'a, R: 'a> {
    iter: maps::btree::Range<'a, R, L>,
}

impl<'a, L, R> Iterator for RightRange<'a, L, R> {
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(deref_pair).map(swap_pair)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
