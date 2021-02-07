use crate::mem::Ref;

pub trait MapKind<K, V> {
    type Map: Map<Key = K, Value = V>;
}

pub trait Map: CoreMap + Contains + Get + Remove {}

impl<M> Map for M where M: CoreMap + Contains + Get + Remove {}

pub trait CoreMap {
    type Key;
    type Value;
    type IntoIter<K, V>: Iterator<Item = (Ref<K>, Ref<V>)>;
    type Iter<'a, K: 'a, V: 'a>: Iterator<Item = (&'a K, &'a V)>;

    fn new() -> Self;
    fn iter(&self) -> Self::Iter<'_, Self::Key, Self::Value>;
    fn into_iter(self) -> Self::IntoIter<Self::Key, Self::Value>;
    fn insert(&mut self, key: Ref<Self::Key>, value: Ref<Self::Value>);
}

pub trait Contains<Q: ?Sized = <Self as CoreMap>::Key>: CoreMap {
    fn contains(&self, key: &Q) -> bool;
}

pub trait Get<Q: ?Sized = <Self as CoreMap>::Key>: CoreMap {
    fn get(&self, key: &Q) -> Option<&Self::Value>;
}

pub trait Remove<Q: ?Sized = <Self as CoreMap>::Key>: CoreMap {
    fn remove(&mut self, key: &Q) -> Option<(Ref<Self::Key>, Ref<Self::Value>)>;
}
