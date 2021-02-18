//! Bidirectional maps.
#![feature(generic_associated_types)]
#![allow(incomplete_features)]
#![cfg_attr(not(feature = "std"), no_std)]

// Necessary to support no_std setups
extern crate alloc;

pub mod bimap;
pub mod maps;

mod traits;
mod util;

#[cfg(feature = "serde")]
mod serde;
#[cfg(feature = "std")]
use std::{
    collections::hash_map::RandomState,
    hash::{BuildHasher, Hash},
    marker::PhantomData,
};

use traits::*;

pub trait MapKind<K, V> {
    type Map: Map<Key = K, Value = V>;
}

pub struct BTreeKind;

impl<K, V> MapKind<K, V> for BTreeKind
where
    K: Ord,
{
    type Map = maps::btree::InnerMap<K, V>;
}

pub struct VecKind;

impl<V> MapKind<usize, V> for VecKind {
    type Map = maps::vec::InnerMap<usize, V>;
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
    type Map = maps::hash::InnerMap<K, V, S>;
}

#[doc(inline)]
pub use crate::bimap::BiMap;

pub type Generic<L, R, LKind, RKind> =
    BiMap<<LKind as MapKind<L, R>>::Map, <RKind as MapKind<R, L>>::Map>;

/// A bidirectional `BTreeMap`.
pub type BiBTreeMap<L, R> = Generic<L, R, BTreeKind, BTreeKind>;

/// A bidirectional `HashMap`.
#[cfg(feature = "std")]
pub type BiHashMap<L, R> = Generic<L, R, HashKind, HashKind>;

/// A bidirectional `VecMap`.
pub type BiVecMap = Generic<usize, usize, VecKind, VecKind>;

#[cfg(test)]
mod tests {}
