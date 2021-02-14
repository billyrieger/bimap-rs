use alloc::collections::{btree_map, BTreeMap};
use core::borrow::Borrow;
use core::iter::FusedIterator;
use core::ops::RangeBounds;

use crate::mem::{Ref, Wrapper};
use crate::traits::*;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BTreeKind;

impl<K, V> MapKind<K, V> for BTreeKind
where
    K: Ord,
{
    type Map = InnerBTreeMap<K, V>;
}

#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct InnerBTreeMap<K, V> {
    inner: BTreeMap<Ref<K>, Ref<V>>,
}

impl<K, V> InnerBTreeMap<K, V>
where
    K: Ord,
{
    pub fn range<T: ?Sized, R>(&self, range: R) -> Range<'_, K, V>
    where
        T: Ord,
        K: Ord + Borrow<T>,
        R: RangeBounds<T>,
    {
        let (start, end) = (range.start_bound(), range.end_bound());
        let range = (Wrapper::wrap_bound(start), Wrapper::wrap_bound(end));
        Range {
            inner: self.inner.range::<Wrapper<_>, _>(range),
        }
    }
}

impl<K, V> MapIterator for InnerBTreeMap<K, V>
where
    K: Ord,
{
    type MapIter<'a, KK: 'a, VV: 'a> = Iter<'a, KK, VV>;
    type MapIntoIter<KK, VV> = IntoIter<KK, VV>;

    fn map_iter(&self) -> Self::MapIter<'_, K, V> {
        Iter {
            inner: self.inner.iter(),
        }
    }

    fn map_into_iter(self) -> Self::MapIntoIter<K, V> {
        IntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

impl<K, V> New for InnerBTreeMap<K, V>
where
    K: Ord,
{
    fn new() -> Self {
        Self {
            inner: BTreeMap::new(),
        }
    }
}

impl<K, V> CoreMap for InnerBTreeMap<K, V>
where
    K: Ord,
{
    type Key = K;
    type Value = V;
}

impl<K, V> Insert for InnerBTreeMap<K, V>
where
    K: Ord,
{
    fn insert(&mut self, key: Ref<K>, value: Ref<V>) {
        self.inner.insert(key, value);
    }
}

impl<K, V, Q: ?Sized> Contains<Q> for InnerBTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord,
{
    fn contains(&self, k: &Q) -> bool {
        self.inner.contains_key(Wrapper::wrap(k))
    }
}

impl<K, V, Q: ?Sized> Get<Q> for InnerBTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord,
{
    fn get(&self, k: &Q) -> Option<&Ref<V>> {
        self.inner.get(Wrapper::wrap(k))
    }
}

impl<K, V, Q: ?Sized> Remove<Q> for InnerBTreeMap<K, V>
where
    K: Ord + Borrow<Q>,
    Q: Ord,
{
    fn remove(&mut self, k: &Q) -> Option<(Ref<K>, Ref<V>)> {
        self.inner.remove_entry(Wrapper::wrap(k))
    }
}

#[derive(Debug)]
pub struct IntoIter<K, V> {
    inner: btree_map::IntoIter<Ref<K>, Ref<V>>,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (Ref<K>, Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {}

impl<K, V> FusedIterator for IntoIter<K, V> {}

#[derive(Debug)]
pub struct Iter<'a, K, V> {
    inner: btree_map::Iter<'a, Ref<K>, Ref<V>>,
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a Ref<K>, &'a Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}

impl<'a, K, V> FusedIterator for Iter<'a, K, V> {}

#[derive(Debug)]
pub struct Range<'a, K, V> {
    inner: btree_map::Range<'a, Ref<K>, Ref<V>>,
}

impl<'a, K, V> Clone for Range<'a, K, V> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<'a, K, V> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, v)| (&**k, &**v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(k, v)| (&**k, &**v))
    }
}

impl<'a, K, V> ExactSizeIterator for Range<'a, K, V> {}

impl<'a, K, V> FusedIterator for Range<'a, K, V> {}
