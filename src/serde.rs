//! Implementations of `serde::Serialize` and `serde::Deserialize` for
//! `BiHashMap` and `BiBTreeMap`

use crate::{BiHashMap, BiBTreeMap};
use serde::{Serializer, Serialize, Deserializer, Deserialize};
use serde::de::{Visitor, MapAccess};
use std::hash::Hash;
use std::fmt::{Formatter, Result as FmtResult};
use std::marker::PhantomData;
use std::default::Default;

/// Serializer for `BiHashMap`
impl<L, R> Serialize for BiHashMap<L, R>
where
    L: Serialize + Eq + Hash,
    R: Serialize + Eq + Hash,
{
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        ser.collect_map(self.iter())
    }
}

/// Visitor to construct `BiHashMap` from serialized map entries
struct BiHashMapVisitor<L, R> {
    marker: PhantomData<BiHashMap<L, R>>
}

impl<'de, L, R> Visitor<'de> for BiHashMapVisitor<L, R>
where
    L: Deserialize<'de> + Eq + Hash,
    R: Deserialize<'de> + Eq + Hash,
{
    fn expecting(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "a map")
    }

    type Value = BiHashMap<L, R>;
    fn visit_map<A: MapAccess<'de>>(self, mut entries: A) -> Result<Self::Value, A::Error> {
        let mut map = match entries.size_hint() {
            Some(s) => BiHashMap::with_capacity(s),
            None => BiHashMap::new()
        };
        while let Some((l, r)) = entries.next_entry()? {
            map.insert(l, r);
        }
        Ok(map)
    }
}

/// Deserializer for `BiHashMap`
impl<'de, L, R> Deserialize<'de> for BiHashMap<L, R>
where
    L: Deserialize<'de> + Eq + Hash,
    R: Deserialize<'de> + Eq + Hash,
{
    fn deserialize<D: Deserializer<'de>>(de: D) -> Result<Self, D::Error> {
        de.deserialize_map(BiHashMapVisitor { marker: PhantomData::default() })
    }
}

/// Serializer for `BiBTreeMap`
impl<L, R> Serialize for BiBTreeMap<L, R>
where
    L: Serialize + Ord,
    R: Serialize + Ord,
{
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        ser.collect_map(self.iter())
    }
}

/// Visitor to construct `BiBTreeMap` from serialized map entries
struct BiBTreeMapVisitor<L, R> {
    marker: PhantomData<BiBTreeMap<L, R>>
}

impl<'de, L, R> Visitor<'de> for BiBTreeMapVisitor<L, R>
where
    L: Deserialize<'de> + Ord,
    R: Deserialize<'de> + Ord,
{
    fn expecting(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "a map")
    }

    type Value = BiBTreeMap<L, R>;
    fn visit_map<A: MapAccess<'de>>(self, mut entries: A) -> Result<Self::Value, A::Error> {
        let mut map = BiBTreeMap::new();
        while let Some((l, r)) = entries.next_entry()? {
            map.insert(l, r);
        }
        Ok(map)
    }
}

/// Deserializer for `BiBTreeMap`
impl<'de, L, R> Deserialize<'de> for BiBTreeMap<L, R>
where
    L: Deserialize<'de> + Ord,
    R: Deserialize<'de> + Ord,
{
    fn deserialize<D: Deserializer<'de>>(de: D) -> Result<Self, D::Error> {
        de.deserialize_map(BiBTreeMapVisitor { marker: PhantomData::default() })
    }
}