// Since this is a private module, all of the traits here are *sealed*.
//
// # See also
//
// The [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/future-proofing.html#sealed-traits-protect-against-downstream-implementations-c-sealed)
// have more information on the usage of sealed traits.
use crate::util::Ref;

// This makes some of the method arguments and return types less unwieldy.
type RefPair<L, R> = (Ref<L>, Ref<R>);

pub trait Map: Core + New + Length + Insert + Contains + Get + Remove + MapIterator {}

impl<M> Map for M where
    M: Core + New + Length + Insert + Contains + Get + Remove + MapIterator
{
}

pub trait Core {
    type Key;
    type Value;
}

pub trait New: Core {
    fn new() -> Self;
}

pub trait Length: Core {
    fn len(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub trait Clear: Core {
    fn clear(&mut self);
}

pub trait Insert: Core {
    fn insert(&mut self, pair: RefPair<Self::Key, Self::Value>);
}

pub trait Contains<Q: ?Sized = <Self as Core>::Key>: Core {
    fn contains(&self, key: &Q) -> bool;
}

pub trait Get<Q: ?Sized = <Self as Core>::Key>: Core {
    fn get(&self, key: &Q) -> Option<&Ref<Self::Value>>;
}

pub trait Remove<Q: ?Sized = <Self as Core>::Key>: Core {
    fn remove(&mut self, key: &Q) -> Option<RefPair<Self::Key, Self::Value>>;
}

pub trait MapIterator: Core {
    type MapIter<'a, K: 'a, V: 'a>: Iterator<Item = (&'a Ref<K>, &'a Ref<V>)>;
    type MapIntoIter<K, V>: Iterator<Item = (Ref<K>, Ref<V>)>;

    fn map_iter(&self) -> Self::MapIter<'_, Self::Key, Self::Value>;
    fn map_into_iter(self) -> Self::MapIntoIter<Self::Key, Self::Value>;
}
