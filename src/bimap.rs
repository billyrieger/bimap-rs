use core::iter::FusedIterator;

use crate::mem::Ref;
use crate::traits::*;

pub enum Overwritten<L, R> {
    Zero,
    One((L, R)),
    Two((L, R), (L, R)),
}

/// A generic bidirectional map.
#[derive(Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

    pub fn iter_left<'a>(&'a self) -> IterLeft<'a, LMap>
    where
        L: 'a,
        R: 'a,
    {
        IterLeft {
            inner: self.lmap.iter(),
        }
    }

    pub fn iter_right<'a>(&'a self) -> IterRight<'a, RMap>
    where
        L: 'a,
        R: 'a,
    {
        IterRight {
            inner: self.rmap.iter(),
        }
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

    pub fn insert(&mut self, l: L, r: R) -> Overwritten<L, R> {
        let overwritten = match (self.remove_left(&l), self.remove_right(&r)) {
            (None, None) => Overwritten::Zero,
            (Some(pair), None) | (None, Some(pair)) => Overwritten::One(pair),
            (Some(lpair), Some(rpair)) => Overwritten::Two(lpair, rpair),
        };
        unsafe {
            self.insert_unchecked(l, r);
        }
        overwritten
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

#[derive(Debug)]
pub struct IterLeft<'a, LMap: Map + 'a> {
    inner: LMap::Iter<'a, LMap::Key, LMap::Value>,
}

impl<'a, L: 'a, R: 'a, LMap: 'a> Clone for IterLeft<'a, LMap>
where
    LMap: Map<Key = L, Value = R>,
    LMap::Iter<'a, L, R>: Clone,
{
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, L: 'a, R: 'a, LMap: 'a> Iterator for IterLeft<'a, LMap>
where
    LMap: Map<Key = L, Value = R>,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, L: 'a, R: 'a, LMap: 'a> DoubleEndedIterator for IterLeft<'a, LMap>
where
    LMap: Map<Key = L, Value = R>,
    LMap::Iter<'a, L, R>: DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, L: 'a, R: 'a, LMap: 'a> ExactSizeIterator for IterLeft<'a, LMap>
where
    LMap: Map<Key = L, Value = R>,
    LMap::Iter<'a, L, R>: ExactSizeIterator,
{
}

impl<'a, L: 'a, R: 'a, LMap: 'a> FusedIterator for IterLeft<'a, LMap>
where
    LMap: Map<Key = L, Value = R>,
    LMap::Iter<'a, L, R>: ExactSizeIterator,
{
}

#[derive(Clone, Debug)]
pub struct IterRight<'a, RMap: Map + 'a> {
    inner: RMap::Iter<'a, RMap::Key, RMap::Value>,
}

impl<'a, L: 'a, R: 'a, RMap: 'a> Iterator for IterRight<'a, RMap>
where
    RMap: Map<Key = R, Value = L>,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(r, l)| (l, r))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, L: 'a, R: 'a, RMap: 'a> DoubleEndedIterator for IterRight<'a, RMap>
where
    RMap: Map<Key = R, Value = L>,
    RMap::Iter<'a, R, L>: DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(r, l)| (l, r))
    }
}

impl<'a, L: 'a, R: 'a, RMap: 'a> ExactSizeIterator for IterRight<'a, RMap>
where
    RMap: Map<Key = R, Value = L>,
    RMap::Iter<'a, R, L>: ExactSizeIterator,
{
}

impl<'a, L: 'a, R: 'a, RMap: 'a> FusedIterator for IterRight<'a, RMap>
where
    RMap: Map<Key = R, Value = L>,
    RMap::Iter<'a, R, L>: FusedIterator,
{
}

#[cfg(test)]
mod tests {
    #![allow(dead_code)]

    use super::*;

    use crate::maps::BTreeMap;
    use core::iter::FusedIterator;
    use static_assertions::assert_impl_all;

    type L = u8;
    type R = char;

    type Bi = crate::BiBTreeMap<L, R>;

    type LMap = BTreeMap<L, R>;
    type RMap = BTreeMap<R, L>;

    assert_impl_all!(Bi: Clone, Ord);

    assert_impl_all!(IterLeft<'_, LMap>: Iterator, DoubleEndedIterator, ExactSizeIterator, FusedIterator);
    assert_impl_all!(IterRight<'_, RMap>: Iterator, DoubleEndedIterator, ExactSizeIterator, FusedIterator);
}
