use std::borrow::Borrow;
use std::collections::{hash_map, HashMap};
use std::hash::{BuildHasher, Hash};
use std::iter::FusedIterator;

use crate::traits::*;
use crate::util::{Ref, Wrapper};

#[derive(Debug)]
pub struct InnerHashMap<K, V, S> {
    inner: HashMap<Ref<K>, Ref<V>, S>,
}

impl<K, V, S> Core for InnerHashMap<K, V, S> {
    type Key = K;
    type Value = V;
}

impl<K, V, S> New for InnerHashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    fn new() -> Self {
        Self {
            inner: HashMap::with_hasher(S::default()),
        }
    }
}

impl<K, V, S> Length for InnerHashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    fn len(&self) -> usize {
        self.inner.len()
    }

    fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl<K, V, S> Insert for InnerHashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    fn insert(&mut self, key: Ref<K>, value: Ref<V>) {
        self.inner.insert(key, value);
    }
}

impl<K, V, S, Q: ?Sized> Contains<Q> for InnerHashMap<K, V, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
    S: BuildHasher + Default,
{
    fn contains(&self, key: &Q) -> bool {
        self.inner.contains_key(Wrapper::wrap(key))
    }
}

impl<K, V, S, Q: ?Sized> Get<Q> for InnerHashMap<K, V, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
    S: BuildHasher + Default,
{
    fn get(&self, key: &Q) -> Option<&Ref<V>> {
        self.inner.get(Wrapper::wrap(key))
    }
}

impl<K, V, S, Q: ?Sized> Remove<Q> for InnerHashMap<K, V, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
    S: BuildHasher + Default,
{
    fn remove(&mut self, key: &Q) -> Option<(Ref<K>, Ref<V>)> {
        self.inner.remove_entry(Wrapper::wrap(key))
    }
}

impl<K, V, S> MapIterator for InnerHashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    type MapIntoIter<K_, V_> = MapIntoIter<K_, V_>;
    type MapIter<'a, K_: 'a, V_: 'a> = MapIter<'a, K_, V_>;

    fn map_into_iter(self) -> MapIntoIter<K, V> {
        MapIntoIter {
            inner: self.inner.into_iter(),
        }
    }

    fn map_iter(&self) -> MapIter<'_, K, V> {
        MapIter {
            inner: self.inner.iter(),
        }
    }
}

pub struct MapIntoIter<K, V> {
    inner: hash_map::IntoIter<Ref<K>, Ref<V>>,
}

impl<K, V> Iterator for MapIntoIter<K, V> {
    type Item = (Ref<K>, Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<K, V> ExactSizeIterator for MapIntoIter<K, V> {}

impl<K, V> FusedIterator for MapIntoIter<K, V> {}

pub struct MapIter<'a, K: 'a, V: 'a> {
    inner: hash_map::Iter<'a, Ref<K>, Ref<V>>,
}

impl<'a, K: 'a, V: 'a> Iterator for MapIter<'a, K, V> {
    type Item = (&'a Ref<K>, &'a Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K, V> ExactSizeIterator for MapIter<'a, K, V> {}

impl<'a, K, V> FusedIterator for MapIter<'a, K, V> {}
