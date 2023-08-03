use crate::Num;
use std::fmt::{Display, Formatter, Result};

#[derive(Debug)]
pub enum MathError<const N: usize> {
    Overflow(Num<N>),
    ConversionError,
}

impl<const N: usize> Display for MathError<N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            MathError::Overflow(_) => write!(f, "Overflow"),
            MathError::ConversionError => write!(f, "Conversion Error"),
        }
    }
}
