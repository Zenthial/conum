use crate::Num;
use std::fmt::{Display, Formatter, Result};

#[derive(Debug)]
pub enum MathError {
    Overflow(Num),
    ConversionError,
}

impl Display for MathError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            MathError::Overflow(_) => write!(f, "Overflow"),
            MathError::ConversionError => write!(f, "Conversion Error"),
        }
    }
}
