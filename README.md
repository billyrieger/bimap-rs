[![Build Status](https://travis-ci.org/wrieger93/bimap-rs.svg?branch=master)](https://travis-ci.org/wrieger93/bimap-rs)
[![Documentation](https://docs.rs/bimap/badge.svg)](https://docs.rs/bimap/)
[![crates.io](https://img.shields.io/crates/v/bimap.svg)](https://crates.io/crates/bimap)

# bimap-rs: a fast two-way bijective map for Rust

## Examples

```rust
use bimap::Bimap;

let mut elements = Bimap::new();

// insert chemicals and their corresponding symbols
elements.insert("hydrogen", "H");
elements.insert("carbon", "C");
elements.insert("bromine", "Br");
elements.insert("neodymium", "Nd");

// retrieve chemical symbol by name (left to right)
assert_eq!(elements.get_by_left(&"bromine"), Some(&"Br"));
assert_eq!(elements.get_by_left(&"oxygen"), None);

// retrieve name by chemical symbol (right to left)
assert_eq!(elements.get_by_right(&"C"), Some(&"carbon"));
assert_eq!(elements.get_by_right(&"Al"), None);

// check membership
assert!(elements.contains_left(&"hydrogen"));
assert!(!elements.contains_right(&"He"));

// remove elements
assert_eq!(elements.remove_by_left(&"neodymium"), Some(("neodymium", "Nd")));
assert_eq!(elements.remove_by_right(&"Nd"), None);

// iterate over elements
for (left, right) in &elements {
    println!("the chemical symbol for {} is {}", left, right);
}
```
