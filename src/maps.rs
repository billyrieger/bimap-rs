pub mod btree;
pub mod vec;

#[cfg(feature = "std")]
pub mod hash;

#[cfg(feature = "std")]
use std::{
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hash},
    marker::PhantomData,
};

use crate::traits::*;

pub trait MapKind<K, V> {
    type Map: Map<Key = K, Value = V>;
}

pub struct BTreeKind;

impl<K, V> MapKind<K, V> for BTreeKind
where
    K: Ord,
{
    type Map = btree::InnerMap<K, V>;
}

pub struct VecKind;

impl<V> MapKind<usize, V> for VecKind {
    type Map = vec::InnerMap<usize, V>;
}

#[cfg(feature = "std")]
pub struct HashKind<S = RandomState> {
    marker: PhantomData<S>,
}

#[cfg(feature = "std")]
impl<K, V, S> MapKind<K, V> for HashKind<S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
{
    type Map = hash::InnerMap<K, V, S>;
}
