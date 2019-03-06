[![Build Status](https://travis-ci.org/wrieger93/bimap-rs.svg?branch=master)](https://travis-ci.org/wrieger93/bimap-rs)
[![crates.io](https://img.shields.io/crates/v/bimap.svg)](https://crates.io/crates/bimap)
[![Documentation](https://docs.rs/bimap/badge.svg)](https://docs.rs/bimap/)

# bimap-rs

bimap-rs is a two-way bijective map implementation for Rust.

## Usage

### Installation

To use bimap-rs in your Rust project, add the following to your `Cargo.toml`:

```toml
bimap = "0.1"
```

See [the docs](https://docs.rs/bimap/) for more details and example code.

### `no_std` compatibility

To use `bimap-rs` without the Rust standard library, add the following to your `Cargo.toml`:

```toml
bimap = { version = "0.1", default-features = false }
```

Note that you'll need to use Rust nightly due to the use of the `alloc` feature.

## License

`bimap-rs` is licensed under either of

 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
 * MIT license ([LICENSE-MIT](LICENSE-MIT))

at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the
work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
