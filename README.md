# `bimap-rs`

<!-- badges -->

<!--
[![version](https://img.shields.io/crates/v/bimap)][crates.io]
[![license](https://img.shields.io/crates/l/bimap)](#license)
[![dependency status](https://deps.rs/crate/bimap/0.6.0/status.svg)](https://deps.rs/crate/bimap/0.6.0)
[![documentation](https://img.shields.io/docsrs/bimap)][docs.rs]
-->

`bimap-rs` is a pure Rust library for dealing with bijective maps, aiming to
feel like an extension of the standard library's data structures whenever
possible. There are no external dependencies by default but [Serde] and
[`no_std`] compatibility are available through feature flags.

1. [Quick start](#quick-start)
1. [Feature flags](#feature-flags)
1. [Documentation](#documentation)
1. [Contributing](#contributing)
1. [Semantic versioning](#semantic-versioning)
1. [License](#license)

## Quick start

To use the latest version of `bimap-rs` with the default features, add this to
your project's `Cargo.toml` file:

```toml
[dependencies]
bimap = "0.6.0"
```

You can now run the `bimap-rs` Hello World!

```rust
fn main() {
    // A bijective map between letters of the English alphabet and their positions.
    let mut alphabet = bimap::BiMap::<char, u8>::new();

    alphabet.insert('A', 1);
    // ...
    alphabet.insert('Z', 26);

    println!("A is at position {}", alphabet.get_by_left(&'A').unwrap());
    println!("{} is at position 26", alphabet.get_by_right(&26).unwrap());
}
```

## Feature flags

| Flag name | Description                        | Enabled by default? |
| --------- | ---------------------------------- | ------------------- |
| `std`     | Standard library usage (`HashMap`) | yes                 |
| `serde`   | (De)serialization using [Serde]    | no                  |

This `Cargo.toml` shows how these features can be enabled and disabled.

```toml
[dependencies]
# I just want to use `bimap-rs`.
bimap = "0.6.0"

# I want to use `bimap-rs` without the Rust standard library.
bimap = { version = "0.6.0", default-features = false }

# I want to use `bimap-rs` with Serde support.
bimap = { version = "0.6.0", features = ["serde"] }
```

## Documentation

Documentation for the latest version of `bimap-rs` is available on [docs.rs].

## Contributing

Thank you for your interest in improving `bimap-rs`! Please read the [code of
conduct] and the [contributing guidelines] before submitting an issue or
opening a pull request.

## Semantic versioning

`bimap-rs` adheres to the de-facto Rust variety of Semantic Versioning.

## License

`bimap-rs` is dual-licensed under the [Apache License](LICENSE_APACHE)
and the [MIT License](LICENSE_MIT).
As a library user, this means that you are free to choose either license when
using `bimap-rs`. As a library contributor, this means that any work you
contribute to `bimap-rs` will be similarly dual-licensed.

<!-- external links -->

[crates.io]: https://crates.io/crates/bimap
[docs.rs]: https://docs.rs/bimap/
[`no_std`]: https://rust-embedded.github.io/book/intro/no-std.html
[serde]: https://serde.rs/

<!-- local files -->

[code of conduct]: CODE_OF_CONDUCT.md
[contributing guidelines]: CONTRIBUTING.md
