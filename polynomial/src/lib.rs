//! This crate implements functions for manipulating polynomials over finite
//! fields, including FFTs.
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(
    unused,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms,
    rust_2021_compatibility
)]
#![forbid(unsafe_code)]
#![allow(
    clippy::many_single_char_names,
    clippy::suspicious_op_assign_impl,
    clippy::suspicious_arithmetic_impl
)]

#[macro_use]
extern crate derivative;

#[macro_use]
extern crate ark_std;
extern crate std;

pub mod evaluations;
pub mod polynomials;

pub use evaluations::
multivariate::{
    DenseMultilinearExtension, MultilinearExtension, SparseMultilinearExtension,
};
pub use polynomials::{multivariate, DenseMVPolynomial, DenseUVPolynomial, Polynomial, DenseMVGroupPolynomial, DenseUVGroupPolynomial, GroupPolynomial};