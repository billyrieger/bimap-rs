#![feature(generic_associated_types)]
#![allow(incomplete_features)]
#![cfg_attr(not(feature = "std"), no_std)]

// Necessary to support no_std setups
extern crate alloc;

pub mod bimap;

// Modules containing the individual map types.
pub mod maps;

mod mem;
mod traits;

use traits::*;

#[doc(inline)]
pub use crate::bimap::BiMap;

#[doc(inline)]
pub use crate::maps::btree::BTreeKind;

#[doc(inline)]
pub use crate::maps::hash::HashKind;

#[doc(inline)]
pub use crate::maps::vec::VecKind;

pub type Generic<L, R, LKind, RKind> =
    BiMap<<LKind as MapKind<L, R>>::Map, <RKind as MapKind<R, L>>::Map>;

/// A bidirectional `BTreeMap`.
pub type BiBTreeMap<L, R> = Generic<L, R, BTreeKind, BTreeKind>;

/// A bidirectional `HashMap`.
pub type BiHashMap<L, R> = Generic<L, R, HashKind, HashKind>;
