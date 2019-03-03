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

## License

bimap-rs is dual licensed under the Apache-2.0 and MIT licenses.
