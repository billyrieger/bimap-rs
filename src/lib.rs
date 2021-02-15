#![feature(generic_associated_types)]
#![allow(incomplete_features)]
#![cfg_attr(not(feature = "std"), no_std)]

// Necessary to support no_std setups
extern crate alloc;

pub mod bimap;

// Modules containing the individual map types.
pub mod btree_map;
pub mod hash_map;
pub mod vec_map;

mod mem;
mod traits;

use traits::*;

#[doc(inline)]
pub use crate::bimap::BiMap;

#[doc(inline)]
pub use crate::btree_map::BTreeKind;

#[doc(inline)]
pub use crate::hash_map::HashKind;

pub type Generic<L, R, LKind, RKind> =
    BiMap<<LKind as MapKind<L, R>>::Map, <RKind as MapKind<R, L>>::Map>;

/// A bidirectional `BTreeMap`.
pub type BiBTreeMap<L, R> = Generic<L, R, BTreeKind, BTreeKind>;

/// A bidirectional `HashMap`.
pub type BiHashMap<L, R> = Generic<L, R, HashKind, HashKind>;
