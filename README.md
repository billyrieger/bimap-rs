# `bimap-rs`

<!-- badges -->
[![version][version badge]][lib.rs]
[![documentation][documentation badge]][docs.rs]
[![license][license badge]](#license)

<!-- external links -->
[lib.rs]: https://lib.rs/crates/bimap
[docs.rs]: https://docs.rs/bimap/0.4.0/bimap/

<!-- static badge images -->
[version badge]: https://img.shields.io/static/v1?label=latest%20version&message=lib.rs&color=blueviolet
[documentation badge]: https://img.shields.io/static/v1?label=documentation&message=docs.rs&color=blueviolet
[license badge]: https://img.shields.io/static/v1?label=license&message=Apache-2.0/MIT&color=blueviolet

`bimap-rs` is a pure Rust library for dealing with bijective maps, aiming to
feel like an extension of [`std::collections`] whenever possible. There are no
external dependencies by default but [Serde] and [`no_std`]
compatibility are available through feature gates.

[`no_std`]: https://rust-embedded.github.io/book/intro/no-std.html
[Serde]: https://serde.rs/
[`std::collections`]: https://doc.rust-lang.org/std/collections/index.html

1. [Quick start](#quick-start)
1. [Documentation](#documentation)
1. [Contributing](#contributing)
1. [Semantic versioning](#semantic-versioning)
1. [License](#license)

## Quick start

To use the latest version of `bimap-rs` with the default features, add this to
your project's `Cargo.toml` file:

```toml
[dependencies]
bimap = "0.5.0"
```

## Documentation

Documentation for the latest version of `bimap-rs` is available on [docs.rs].

## Contributing

Thank you for your interest in helping `bimap-rs`!

## Semantic versioning

`bimap-rs` adheres to the de-facto Rust variety of Semantic Versioning.

## License

`bimap-rs` is dual-licensed under the [MIT License] and the [Apache License].
As a library user, this means that you are free to choose either license when
using `bimap-rs`. As a library contributor, this means that any work you
contribute to `bimap-rs` will be similarly dual-licensed.

[Apache License]: LICENSE_APACHE
[MIT License]: LICENSE_MIT
