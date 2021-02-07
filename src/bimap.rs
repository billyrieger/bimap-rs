use core::borrow::Borrow;
use core::iter::FusedIterator;
use core::ops::RangeBounds;

use crate::maps::{btree_map, BTreeMap};
use crate::mem::Ref;
use crate::traits::*;

/// A generic bidirectional map.
#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

    pub fn iter_left<'a>(&'a self) -> LMap::Iter<'a, L, R>
    where
        L: 'a,
        R: 'a,
    {
        self.lmap.iter()
    }

    pub fn iter_right<'a>(&'a self) -> Flipped<RMap::Iter<'a, R, L>>
    where
        L: 'a,
        R: 'a,
    {
        Flipped(self.rmap.iter())
    }

    pub fn contains_left<Q: ?Sized>(&self, l: &Q) -> bool
    where
        LMap: Contains<Q>,
    {
        self.lmap.contains(l)
    }

    pub fn contains_right<Q: ?Sized>(&self, r: &Q) -> bool
    where
        RMap: Contains<Q>,
    {
        self.rmap.contains(r)
    }

    pub fn get_left<Q: ?Sized>(&self, l: &Q) -> Option<&R>
    where
        LMap: Get<Q>,
    {
        self.lmap.get(l)
    }

    pub fn get_right<Q: ?Sized>(&self, r: &Q) -> Option<&L>
    where
        RMap: Get<Q>,
    {
        self.rmap.get(r)
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

    pub fn remove_right<Q: ?Sized>(&mut self, r: &Q) -> Option<(L, R)>
    where
        RMap: Remove<Q>,
    {
        self.rmap.remove(r).map(|(r0, l0)| {
            let (l1, r1) = self.lmap.remove(&l0).unwrap();
            (Ref::join(l0, l1), Ref::join(r0, r1))
        })
    }

    pub fn try_insert(&mut self, l: L, r: R) -> Result<(), (L, R)> {
        if self.lmap.contains(&l) || self.rmap.contains(&r) {
            Err((l, r))
        } else {
            unsafe {
                self.insert_unchecked(l, r);
            }
            Ok(())
        }
    }

    pub unsafe fn insert_unchecked(&mut self, l: L, r: R) {
        let (l0, l1) = Ref::new(l);
        let (r0, r1) = Ref::new(r);
        self.lmap.insert(l0, r0);
        self.rmap.insert(r1, l1);
    }
}

impl<L, R, RMap> BiMap<BTreeMap<L, R>, RMap>
where
    RMap: Map<Key = R, Value = L>,
{
    pub fn range_left<T: ?Sized, A>(&self, range: A) -> btree_map::Range<'_, L, R>
    where
        L: Ord + Borrow<T>,
        A: RangeBounds<T>,
        T: Ord,
    {
        self.lmap.range(range)
    }
}

impl<L, R, LMap> BiMap<LMap, BTreeMap<R, L>>
where
    LMap: Map<Key = L, Value = R>,
{
    pub fn range_right<T: ?Sized, A>(&self, range: A) -> Flipped<btree_map::Range<'_, R, L>>
    where
        R: Ord + Borrow<T>,
        A: RangeBounds<T>,
        T: Ord,
    {
        Flipped(self.rmap.range(range))
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
        let mut new = Self {
            lmap: LMap::new(),
            rmap: RMap::new(),
        };
        for (l, r) in self.lmap.iter() {
            unsafe {
                new.insert_unchecked(l.clone(), r.clone());
            }
        }
        new
    }
}

#[derive(Clone, Debug)]
pub struct Flipped<I>(I);

impl<I, L, R> Iterator for Flipped<I>
where
    I: Iterator<Item = (R, L)>,
{
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(r, l)| (l, r))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<I, L, R> DoubleEndedIterator for Flipped<I>
where
    I: DoubleEndedIterator<Item = (R, L)>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(r, l)| (l, r))
    }
}

impl<I, L, R> ExactSizeIterator for Flipped<I> where I: ExactSizeIterator<Item = (R, L)> {}

impl<I, L, R> FusedIterator for Flipped<I> where I: FusedIterator<Item = (R, L)> {}
