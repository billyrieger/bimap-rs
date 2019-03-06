[![Build status](https://img.shields.io/travis/com/billyrieger/bimap-rs.svg)](https://travis-ci.com/billyrieger/bimap-rs)
[![Coverage](https://img.shields.io/codecov/c/github/billyrieger/bimap-rs.svg)](https://codecov.io/gh/billyrieger/bimap-rs/branch/master)
[![Lines of code](https://tokei.rs/b1/github/billyrieger/bimap-rs)](https://github.com/Aaronepower/tokei)
[![Version](https://img.shields.io/crates/v/bimap.svg)](https://crates.io/crates/bimap)
[![Documentation](https://docs.rs/bimap/badge.svg)](https://docs.rs/bimap/)
[![License](https://img.shields.io/crates/l/bimap.svg)](https://github.com/billyrieger/bimap/blob/master/LICENSE-MIT)
[![Dependency status](https://deps.rs/repo/github/billyrieger/bimap-rs/status.svg)](https://deps.rs/repo/github/billyrieger/bimap-rs)
[![Rust version](https://img.shields.io/badge/rust-stable-lightgrey.svg)](https://www.rust-lang.org/)

# bimap-rs

`bimap-rs` is a two-way bijective map implementation for Rust.

## Usage

### Installation

To use `bimap-rs` in your Rust project, add the following to your `Cargo.toml`:

```toml
bimap = "0.2"
```

### `no_std` compatibility

To use `bimap-rs` without the Rust standard library, add the following to your `Cargo.toml`:

```toml
bimap = { version = "0.2", default-features = false }
```

Note that you'll need to use Rust nightly due to the use of the `alloc` feature.
If you do use `bimap` without the standard library, there is no `BiHashMap`, only `BiBTreeMap`.

### Example

```rust
use bimap::BiMap;

let mut elements = BiMap::new();

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
assert_eq!(
elements.remove_by_left(&"neodymium"),
Some(("neodymium", "Nd"))
);
assert_eq!(elements.remove_by_right(&"Nd"), None);

// iterate over elements
for (left, right) in &elements {
println!("the chemical symbol for {} is {}", left, right);
}
```

See [the docs](https://docs.rs/bimap/) for more details.

## License

`bimap-rs` is licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
 * MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the
work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
