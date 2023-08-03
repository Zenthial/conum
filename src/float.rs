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

    fn scale(&self) -> Num<{ N + W }> {
        let mut num_vec = Vec::from(&self.number.digits[self.number.msd..]);
        let mut deci_vec = Vec::from(&self.decimal.digits[self.decimal.msd..]);
        num_vec.append(&mut deci_vec);
        println!("{num_vec:?}");

        Num::new(&*num_vec)
    }

    fn actual_mul(&self, rhs: &Self) -> Self {
        let scaled_self = self.scale();
        let scaled_rhs = rhs.scale();
        println!("{}{}", scaled_rhs.msd, scaled_self.msd);
        let mul = scaled_self * scaled_rhs;

        let new_num: Num<N> = Num::new(&mul.digits[0..N]);
        let new_deci: Num<W> = Num::new(&mul.digits[N..]);

        Self {
            number: new_num,
            decimal: new_deci,
        }
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

    #[test]
    fn test_float_mul() {
        let f1: Float<3, 2> = Float::new(3, 5);
        let f2: Float<3, 2> = Float::new(2, 5);
        let res = f1 * f2;
        assert_eq!(*res.number.digits, [0, 0, 8]);
        assert_eq!(*res.decimal.digits, [7, 5]);
    }
}
