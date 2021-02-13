#![feature(generic_associated_types)]
#![allow(incomplete_features)]
#![cfg_attr(not(feature = "std"), no_std)]

// Necessary to support no_std setups
extern crate alloc;

pub mod bimap;
pub mod maps;
pub mod mem;
pub mod traits;

use maps::BTreeKind;
use traits::*;

#[doc(inline)]
pub use crate::bimap::BiMap;

pub type Generic<L, R, LKind, RKind> =
    BiMap<<LKind as MapKind<L, R>>::Map, <RKind as MapKind<R, L>>::Map>;

/// A bidirectional `BTreeMap`.
pub type BiBTreeMap<L, R> = Generic<L, R, BTreeKind, BTreeKind>;