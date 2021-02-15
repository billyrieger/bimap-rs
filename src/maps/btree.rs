use alloc::collections::{btree_map, BTreeMap};
use core::borrow::Borrow;
use core::iter::FusedIterator;

use crate::mem::{Ref, Wrapper};
use crate::traits::*;

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

impl<K, V> Core for InnerBTreeMap<K, V>
where
    K: Ord,
{
    type Key = K;
    type Value = V;
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