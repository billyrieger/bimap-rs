use alloc::vec;
use core::slice;

use crate::mem::Ref;
use crate::traits::*;

type Slot<K, V> = Option<(Ref<K>, Ref<V>)>;

pub struct VecKind;

impl<V> MapKind<usize, V> for VecKind {
    type Map = VecMap<usize, V>;
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct VecMap<K, V> {
    values: Vec<Slot<K, V>>,
}

impl<V> Core for VecMap<usize, V> {
    type Key = usize;
    type Value = V;
}

impl<V> New for VecMap<usize, V> {
    fn new() -> Self {
        Self { values: vec![] }
    }
}

impl<V> Insert for VecMap<usize, V> {
    fn insert(&mut self, key: Ref<usize>, value: Ref<V>) {
        let index: usize = *key;
        if index + 1 > self.values.len() {
            self.values.resize_with(index + 1, || None);
        }
        self.values[index] = Some((key, value));
    }
}

impl<V> Contains<usize> for VecMap<usize, V> {
    fn contains(&self, key: &usize) -> bool {
        self.values.get(*key).is_some()
    }
}

impl<V> Get<usize> for VecMap<usize, V> {
    fn get(&self, key: &usize) -> Option<&Ref<V>> {
        self.values
            .get(*key)
            .and_then(|slot| slot.as_ref())
            .map(|(_, v)| v)
    }
}

impl<V> Remove<usize> for VecMap<usize, V> {
    fn remove(&mut self, key: &usize) -> Option<(Ref<usize>, Ref<V>)> {
        self.values.get_mut(*key).and_then(|slot| slot.take())
    }
}

impl<V> MapIterator for VecMap<usize, V> {
    type MapIntoIter<KK, VV> = MapIntoIter<KK, VV>;
    type MapIter<'a, KK: 'a, VV: 'a> = MapIter<'a, KK, VV>;

    fn map_iter(&self) -> MapIter<'_, usize, V> {
        MapIter {
            iter: self.values.iter(),
        }
    }

    fn map_into_iter(self) -> MapIntoIter<usize, V> {
        MapIntoIter {
            iter: self.values.into_iter(),
        }
    }
}

pub struct MapIter<'a, K, V> {
    iter: slice::Iter<'a, Slot<K, V>>,
}

impl<'a, K, V> Iterator for MapIter<'a, K, V> {
    type Item = (&'a Ref<K>, &'a Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(slot) = self.iter.next() {
            match slot {
                None => continue,
                Some((k, v)) => {
                    return Some((k, v));
                }
            }
        }
        None
    }
}

pub struct MapIntoIter<K, V> {
    iter: vec::IntoIter<Slot<K, V>>,
}

impl<K, V> Iterator for MapIntoIter<K, V> {
    type Item = (Ref<K>, Ref<V>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(slot) = self.iter.next() {
            match slot {
                None => continue,
                Some(item) => {
                    return Some(item);
                }
            }
        }
        None
    }
}
