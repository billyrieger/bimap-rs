use crate::traits::*;
use crate::BiMap;

use core::fmt;
use core::marker::PhantomData;

use serde::de::{MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

impl<L, R, LMap, RMap> Serialize for BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
    L: Serialize,
    R: Serialize,
{
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self)
    }
}

pub struct BiMapVisitor<LMap, RMap> {
    marker: PhantomData<(LMap, RMap)>,
}

impl<'de, L, R, LMap, RMap> Visitor<'de> for BiMapVisitor<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
    L: Deserialize<'de>,
    R: Deserialize<'de>,
{
    fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a map")
    }

    type Value = BiMap<LMap, RMap>;

    fn visit_map<A: MapAccess<'de>>(self, mut entries: A) -> Result<Self::Value, A::Error> {
        let mut map = BiMap::new();
        while let Some((l, r)) = entries.next_entry()? {
            map.insert(l, r);
        }
        Ok(map)
    }
}

impl<'de, L, R, LMap, RMap> Deserialize<'de> for BiMap<LMap, RMap>
where
    LMap: Map<Key = L, Value = R>,
    RMap: Map<Key = R, Value = L>,
    L: Deserialize<'de>,
    R: Deserialize<'de>,
{
    fn deserialize<D: Deserializer<'de>>(de: D) -> Result<Self, D::Error> {
        de.deserialize_map(BiMapVisitor {
            marker: PhantomData,
        })
    }
}
