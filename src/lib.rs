//! Generic bidirectional maps.
#![feature(btree_retain, generic_associated_types)]
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

#[doc(inline)]
pub use crate::bimap::BiMap;

pub type Generic<L, R, LKind, RKind> =
    BiMap<<LKind as maps::MapKind<L, R>>::Map, <RKind as maps::MapKind<R, L>>::Map>;

/// A bidirectional `BTreeMap`.
pub type BiBTreeMap<L, R> = Generic<L, R, maps::BTreeKind, maps::BTreeKind>;

/// A bidirectional `HashMap`.
#[cfg(feature = "std")]
pub type BiHashMap<L, R> = Generic<L, R, maps::HashKind, maps::HashKind>;