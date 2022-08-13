# upcast-arithmetic

[![Crates.io](https://img.shields.io/crates/v/upcast-arithmetic)](https://crates.io/crates/upcast-arithmetic)
[![docs.rs](https://img.shields.io/docsrs/upcast-arithmetic)](https://docs.rs/upcast-arithmetic/latest/upcast_arithmetic/)
[![GitHub license](https://img.shields.io/github/license/umgefahren/upcast-arithmetic)](https://github.com/umgefahren/upcast-arithmetic/blob/main/LICENSE)
[![Rust](https://github.com/umgefahren/upcast-arithmetic/actions/workflows/rust.yml/badge.svg)](https://github.com/umgefahren/upcast-arithmetic/actions/workflows/rust.yml)

Utility library for dealing with arithmetic on type limits by upcasting into types with higher
limits.

## Examples

###  Without `upcast_arithmetic` (panics)
```rust
let a = u8::MAX;
let b = 2u8;

let modulo = u8::MAX;

let res = (a + b) % modulo;
assert_eq!(res, 2);
```
### With `upcast_arithmetic`
```rust
use upcast_arithmetic::*;

let a = u8::MAX;
let b = 2u8;

let modulo = u8::MAX;

let res = a.upcast_add_mod(b, modulo);
assert_eq!(res, 2);
```

## Performance
The performance overhead is very small. In benchmarks it seems like there is only a neglegible
performance penelty, compared to assuming no overflow occurs.

## `no_std`
The crate is fully `#![no_std]` compatible.

## Unsafe
There is no unsafe code and the flag `#![deny(unsafe_code)]` is set.

License: MIT
