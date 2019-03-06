[![Build status](https://img.shields.io/travis/com/billyrieger/bimap-rs.svg)](https://travis-ci.com/billyrieger/bimap-rs)
[![Coverage](https://img.shields.io/codecov/c/github/billyrieger/bimap-rs.svg)](https://codecov.io/gh/billyrieger/bimap-rs/branch/master)
[![Lines of code](https://tokei.rs/b1/github/billyrieger/bimap-rs)](https://github.com/Aaronepower/tokei)
[![Version](https://img.shields.io/crates/v/bimap.svg)](https://crates.io/crates/bimap)
[![Documentation](https://docs.rs/bimap/badge.svg)](https://docs.rs/bimap/)
[![License](https://img.shields.io/crates/l/bimap.svg)](https://github.com/billyrieger/bimap/blob/master/LICENSE-MIT)
[![Dependency status](https://deps.rs/repo/github/billyrieger/bimap-rs/status.svg)](https://deps.rs/repo/github/billyrieger/bimap-rs)
[![Rust version](https://img.shields.io/badge/rust-stable-lightgrey.svg)](https://www.rust-lang.org/)

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
