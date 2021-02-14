use crate::mem::Ref;

pub trait MapKind<K, V> {
    type Map: Map<Key = K, Value = V>;
}

pub trait Map: CoreMap + New + Insert + Contains + Get + Remove + MapIterator {}

impl<M> Map for M where M: CoreMap + New + Insert + Contains + Get + Remove + MapIterator {}

pub trait CoreMap {
    type Key;
    type Value;
}

pub trait New: CoreMap {
    fn new() -> Self;
}

pub trait Insert: CoreMap {
    fn insert(&mut self, key: Ref<Self::Key>, value: Ref<Self::Value>);
}

pub trait Contains<Q: ?Sized = <Self as CoreMap>::Key>: CoreMap {
    fn contains(&self, key: &Q) -> bool;
}

pub trait Get<Q: ?Sized = <Self as CoreMap>::Key>: CoreMap {
    fn get(&self, key: &Q) -> Option<&Ref<Self::Value>>;
}

pub trait Remove<Q: ?Sized = <Self as CoreMap>::Key>: CoreMap {
    fn remove(&mut self, key: &Q) -> Option<(Ref<Self::Key>, Ref<Self::Value>)>;
}

pub trait MapIterator: CoreMap {
    type MapIter<'a, K: 'a, V: 'a>: Iterator<Item = (&'a Ref<K>, &'a Ref<V>)>;
    type MapIntoIter<K, V>: Iterator<Item = (Ref<K>, Ref<V>)>;

    fn map_iter(&self) -> Self::MapIter<'_, Self::Key, Self::Value>;
    fn map_into_iter(self) -> Self::MapIntoIter<Self::Key, Self::Value>;
}
