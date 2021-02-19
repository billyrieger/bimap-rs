use alloc::vec::{self, Vec};
use core::slice;

use crate::traits::*;
use crate::util::Ref;

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Slot<K, V> {
    Full(Ref<K>, Ref<V>),
    Empty,
}

impl<K, V> Slot<K, V> {
    fn is_full(&self) -> bool {
        match self {
            Slot::Full(_, _) => true,
            Slot::Empty => false,
        }
    }

    fn is_empty(&self) -> bool {
        match self {
            Slot::Full(_, _) => false,
            Slot::Empty => true,
        }
    }

    fn take(&mut self) -> Option<(Ref<K>, Ref<V>)> {
        match core::mem::replace(self, Slot::Empty) {
            Slot::Empty => None,
            Slot::Full(k, v) => Some((k, v)),
        }
    }
}

#[derive(Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InnerMap<K, V> {
    values: Vec<Slot<K, V>>,
}

impl<V> Core for InnerMap<usize, V> {
    type Key = usize;
    type Value = V;
    type MapIntoIter<K_, V_> = MapIntoIter<K_, V_>;
    type MapIter<'a, K_: 'a, V_: 'a> = MapIter<'a, K_, V_>;

    fn new() -> Self {
        Self { values: Vec::new() }
    }

    fn len(&self) -> usize {
        self.values.iter().filter(|slot| slot.is_full()).count()
    }

    fn is_empty(&self) -> bool {
        self.values.iter().all(|slot| slot.is_empty())
    }

    fn clear(&mut self) {
        self.values.clear()
    }

    fn insert(&mut self, (key, value): (Ref<usize>, Ref<V>)) {
        let index: usize = *key;
        if index + 1 > self.values.len() {
            self.values.resize_with(index + 1, || Slot::Empty);
        }
        self.values[index] = Slot::Full(key, value);
    }

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

impl<V> Contains for InnerMap<usize, V> {
    fn contains(&self, key: &usize) -> bool {
        self.values.get(*key).is_some()
    }
}

impl<V> Get for InnerMap<usize, V> {
    fn get(&self, key: &usize) -> Option<&Ref<V>> {
        match self.values.get(*key)? {
            Slot::Empty => None,
            Slot::Full(_, v) => Some(v),
        }
    }
}

impl<V> Remove for InnerMap<usize, V> {
    fn remove(&mut self, key: &usize) -> Option<(Ref<usize>, Ref<V>)> {
        self.values.get_mut(*key).and_then(|slot| slot.take())
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
                Slot::Empty => continue,
                Slot::Full(k, v) => {
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
                Slot::Empty => continue,
                Slot::Full(k, v) => {
                    return Some((k, v));
                }
            }
        }
        None
    }
}
