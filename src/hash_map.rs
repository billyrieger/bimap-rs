use std::borrow::Borrow;
use std::collections::{hash_map, HashMap};
use std::hash::{BuildHasher, Hash};
use std::marker::PhantomData;

use hash_map::RandomState;

use crate::mem::{Ref, Wrapper};
use crate::traits::*;

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HashKind<S = RandomState> {
    marker: PhantomData<S>,
}

impl<K, V, S> MapKind<K, V> for HashKind<S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    type Map = InnerHashMap<K, V, S>;
}

#[derive(Debug)]
pub struct InnerHashMap<K, V, S> {
    inner: HashMap<Ref<K>, Ref<V>, S>,
}

impl<K, V, S> CoreMap for InnerHashMap<K, V, S> {
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
    fn remove(&mut self, key: &Q) -> Option<(Ref<Self::Key>, Ref<Self::Value>)> {
        self.inner.remove_entry(Wrapper::wrap(key))
    }
}

impl<K, V, S> MapIterator for InnerHashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    type MapIter<'a, KK: 'a, VV: 'a> = MapIter<'a, KK, VV>;
    type MapIntoIter<KK, VV> = MapIntoIter<KK, VV>;

    fn map_iter(&self) -> MapIter<'_, K, V> {
        MapIter {
            inner: self.inner.iter(),
        }
    }

    fn map_into_iter(self) -> MapIntoIter<K, V> {
        MapIntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

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
