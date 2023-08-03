use crate::{errors::MathError, num_from::FromSize, Num};

use std::ops::{Add, Mul};

pub struct Float {
    pub(crate) number: Num,
    pub(crate) decimal: Num,
    pub(crate) num_digits: usize,
    pub(crate) deci_digits: usize,
}

impl Float {
    #[must_use]
    pub fn new(num: i32, deci: i32, num_digits: usize, deci_digits: usize) -> Self {
        Float {
            number: Num::from_with_size(num, num_digits),
            decimal: Num::from_with_size(deci, deci_digits),
            num_digits,
            deci_digits,
        }
    }

    #[must_use]
    pub fn zero(num_digits: usize, deci_digits: usize) -> Self {
        Float {
            number: Num::zero(num_digits),
            decimal: Num::zero(deci_digits),
            num_digits,
            deci_digits,
        }
    }

    fn scale(&self) -> Num {
        let mut num_vec = Vec::from(&*self.number.digits);
        let mut deci_vec = Vec::from(&*self.decimal.digits);
        num_vec.append(&mut deci_vec);

        Num::new(&num_vec.to_owned(), num_vec.len())
    }

    fn actual_mul(&self, rhs: &Self) -> Self {
        let scaled_self = self.scale();
        let scaled_rhs = rhs.scale();
        let mul = scaled_self * scaled_rhs;
        let new_num = &mul.digits[0..self.num_digits];
        let new_deci = &mul.digits[self.num_digits..self.deci_digits];

        Self {
            number: Num::new(new_num, self.num_digits),
            decimal: Num::new(new_deci, self.deci_digits),
            num_digits: self.num_digits,
            deci_digits: self.deci_digits,
        }
    }
}

impl Add for Float {
    type Output = Float;
    fn add(self, rhs: Self) -> Self::Output {
        let mut r: Self = Float::zero(self.num_digits, self.deci_digits);

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

impl Mul for Float {
    type Output = Float;
    fn mul(self, rhs: Self) -> Self::Output {
        return self.actual_mul(&rhs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        let f1 = Float::new(100, 0, 3, 1);
        let f2 = Float::new(100, 0, 3, 1);
        assert_eq!(*(f1 + f2).number.digits, [2, 0, 0]);
    }

    #[test]
    fn test_add_decimal_overflow() {
        let f1 = Float::new(100, 1, 3, 1);
        let f2 = Float::new(100, 9, 3, 1);
        let res = f1 + f2;
        assert_eq!(*res.number.digits, [2, 0, 1]);
        assert_eq!(*res.decimal.digits, [0]);
    }

    #[test]
    fn test_mul() {
        let f1 = Float::new(2, 5, 3, 2);
        let f2 = Float::new(3, 5, 3, 2);
        let res = f1 * f2;
        assert_eq!(*res.number.digits, [0, 0, 8]);
        assert_eq!(*res.decimal.digits, [7, 5]);
    }
}
