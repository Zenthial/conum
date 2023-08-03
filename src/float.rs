use crate::{errors::MathError, Num};

use std::ops::{Add, Mul};

pub struct Float<const N: usize, const W: usize> {
    pub(crate) number: Num<N>,
    pub(crate) decimal: Num<W>,
}

impl<const N: usize, const W: usize> Float<N, W>
where
    [(); N + W]:,
{
    #[must_use]
    pub fn new(num: i32, deci: i32) -> Self {
        Float {
            number: Num::from(num),
            decimal: Num::from(deci),
        }
    }

    #[must_use]
    pub fn zero() -> Self {
        Float {
            number: Num::zero(),
            decimal: Num::zero(),
        }
    }

    fn actual_mul(&self, rhs: &Self) -> Self {
        let mut num_vec = Vec::from(*self.number.digits);
        let mut deci_vec = Vec::from(*self.decimal.digits);
        num_vec.append(&mut deci_vec);

        let scaled_self: Num<{ N + W }> = Num::new(&num_vec.to_owned());

        todo!()
    }
}

impl<const N: usize, const W: usize> Add for Float<N, W>
where
    [(); N + W]:,
{
    type Output = Float<N, W>;
    fn add(self, rhs: Self) -> Self::Output {
        let mut r: Self = Float::zero();

        match self.number.checked_add(&rhs.number) {
            Ok(num) => {
                r.number = num;
            }
            Err(e) => panic!("{}", e),
        }

        match self.decimal.checked_add(&rhs.decimal) {
            Ok(deci) => {
                r.decimal = deci;
            }
            Err(e) => match e {
                MathError::Overflow(o) => {
                    r.decimal = o;
                    r.number += 1;
                }
                MathError::ConversionError => panic!("{}", e),
            },
        }

        r
    }
}

const fn sum(n: usize, w: usize) -> usize {
    n + w
}

impl<const N: usize, const W: usize> Mul for Float<N, W>
where
    [(); N + W]:,
{
    type Output = Float<N, W>;
    fn mul(self, rhs: Self) -> Self::Output {
        return self.actual_mul(&rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let f1: Float<3, 1> = Float::new(100, 0);
        let f2: Float<3, 1> = Float::new(100, 0);
        assert_eq!(*(f1 + f2).number.digits, [2, 0, 0]);
    }

    #[test]
    fn test_add_decimal_overflow() {
        let f1: Float<3, 1> = Float::new(100, 1);
        let f2: Float<3, 1> = Float::new(100, 9);
        let res = f1 + f2;
        assert_eq!(*res.number.digits, [2, 0, 1]);
        assert_eq!(*res.decimal.digits, [0]);
    }
}
