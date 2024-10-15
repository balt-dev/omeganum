[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/balt-dev/omeganum/.github%2Fworkflows%2Frust.yml?branch=master&style=flat&label=tests)](https://github.com/balt-dev/omeganum/actions/)
[![Coverage](https://coveralls.io/repos/github/balt-dev/omeganum/badge.svg?branch=master)](https://coveralls.io/github/balt-dev/omeganum/)
[![Documentation](https://docs.rs/omeganum/badge.svg)](https://docs.rs/omeganum)
[![Repository](https://img.shields.io/badge/-GitHub-%23181717?style=flat&logo=github&labelColor=%23555555&color=%23181717)](https://github.com/balt-dev/omeganum)
[![Latest version](https://img.shields.io/crates/v/omeganum.svg)](https://crates.io/crates/omeganum)
[![License](https://img.shields.io/crates/l/omeganum.svg)](https://github.com/balt-dev/omeganum/blob/master/LICENSE)
[![unsafe forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg)](https://github.com/rust-secure-code/safety-dance/)

# OmegaNum.rs


This is a direct port of [Naruyoko's OmegaNum.js](https://github.com/Naruyoko/OmegaNum.js/tree/master) to Rust.

Using this library, you are able to store numbers up to 10{N}9e15 in [Bower's operator notation](https://handwiki.org/wiki/Bowers%27s_operators), with no hard limit on N.
Note that some functions (for example, the gamma function) are left unimplemented. I may add them in later.

This crate supports `#![no-std]`.

## Features

- `default`: Enables `std`
- `std`: Enables using the standard library
- `error_in_core`: Enables implementing the recently stabilized[^1] `core::error::Error` on error types when `std` is not enabled
- `libm`: Required without `std` enabled for math
- `serde`: Enables support for `serde::Serialize` and `serde::Deserialize`
- `f16`: Enables support for converting from the experimental `f16` type

An `f128` feature is planned for when that type gains the necessary method `log10`.

[^1]: in Rust version 1.81.0

## Usage
```rust
use omeganum::{OmegaNum, constant};
use std::borrow::Cow;

// Create constants like this:
const ONE: OmegaNum = constant!(1);
// or like this:
const TEN_E_TWENTY: OmegaNum = OmegaNum::from_parts(
    // The base and array are stored separately,
    // which makes numerous operations much faster by avoiding
    // accessing the heap
    1.0, Cow::Borrowed(&[20.0])
);

// Numbers will coerce to OmegaNum when operated with them
assert_eq!(ONE + 1, 2); 
// ONE + OmegaNum::from(1) == OmegaNum::from(2)

// Math operations move the value, requiring explicitly defined cloning
let seventeen = OmegaNum::from(17);
let log10_17 = seventeen.log10();
// The below code doesn't work, as log10 consumed seventeen
// println!("log10 {seventeen} is {log10_seventeen}");

// Instead, do this:
let seventeen = OmegaNum::from(17);
let log10_17 = seventeen.clone().log10();
println!("log10 {seventeen} is {log10_17}");

// Constants store their arrays statically:
let c = constant!(7);
assert!(matches!(c.into_parts().1, Cow::Borrowed(_)));
```

## Licensing
This project is under the MIT license, which can be found at the root of the repository under `LICENSE`.
Additionally, the license of [OmegaNum.js](https://github.com/Naruyoko/OmegaNum.js/tree/master), the work this is derived from, can be found at `LICENSE-OMEGANUM` - it is also licensed under the MIT license.
