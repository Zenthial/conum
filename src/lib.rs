// Credit: https://mathsanew.com/articles/implementing_large_integers_introduction.pdf

#![deny(clippy::pedantic, clippy::perf, clippy::style, clippy::unwrap_used)]
#![allow(clippy::many_single_char_names)]
pub mod errors;
pub mod float;
pub mod int;
mod num_from;
mod to_digit;

pub use int::Num;
pub use num_from::NumFrom;
