// Credit: https://mathsanew.com/articles/implementing_large_integers_introduction.pdf

#![deny(clippy::pedantic, clippy::perf, clippy::style, clippy::unwrap_used)]
#![allow(unused)]

use std::cmp::Ordering;
use std::fmt::Display;
use std::ops::{Add, AddAssign, Sub, SubAssign};

pub enum Comp {
    Eq,
    Ge,
    Le,
}

// const B: u64 = u32::MAX as u64;
const B: u64 = 10;

fn digits_inner(n: u32, xs: &mut Vec<u32>) {
    if n >= 10 {
        digits_inner(n / 10, xs);
    }
    xs.push(n % 10);
}

fn to_digits(n: u32) -> Vec<u32> {
    let mut xs = Vec::new();
    digits_inner(n, &mut xs);
    xs
}

#[derive(Clone)]
pub struct Num<const WIDTH: usize> {
    pub(crate) digits: Box<[u32; WIDTH]>,
    pub(crate) msd: usize,
    pub(crate) neg: bool,
}

impl<const WIDTH: usize> Num<WIDTH> {
    #[must_use]
    pub fn new(digits: &[u32]) -> Self {
        let mut dig = [0_u32; WIDTH];

        // digits.reverse();
        for (i, d) in digits.iter().enumerate() {
            dig[WIDTH - (digits.len() - i)] = *d;
        }

        Self {
            digits: Box::new(dig),
            msd: WIDTH - digits.len(),
            neg: false,
        }
    }

    fn update_msd(&mut self) {
        for i in 0..self.digits.len() {
            let d = self.digits[i];
            if d != 0 {
                self.msd = i;
                break;
            }
        }
    }

    fn len(&self) -> usize {
        WIDTH - self.msd
    }

    fn cmp(&self, other: &Self) -> Ordering {
        if self.msd == other.msd {
            let self_digits = self.digits.iter();
            let other_digits = other.digits.iter();
            let zip = self_digits.zip(other_digits);

            for (s, o) in zip {
                match s.cmp(o) {
                    Ordering::Less => return Ordering::Less,
                    Ordering::Greater => return Ordering::Greater,
                    Ordering::Equal => {}
                }
            }

            return Ordering::Equal;
        }

        self.msd.cmp(&other.msd)
    }
}

impl<const WIDTH: usize> Add for Num<WIDTH> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut r: Num<WIDTH> = Self::new(&[]);
        let mut carry = false;

        for i in (self.msd..WIDTH).rev() {
            let mut d = u64::from(self.digits[i]);

            if carry || i >= rhs.msd {
                if carry {
                    d += 1;
                }

                if i >= rhs.msd {
                    d += u64::from(rhs.digits[i]);
                }

                if d >= B {
                    carry = true;
                    d -= B;
                } else {
                    carry = false;
                }
            }

            r.digits[i] = u32::try_from(d).expect("overflow error");
        }

        if carry {
            if self.msd == 0 {
                panic!("add overflow");
            } else {
                r.digits[self.msd - 1] = 1;
                r.msd = self.msd - 1;
            }
        } else {
            r.msd = self.msd;
        }

        r
    }
}

impl<const WIDTH: usize> AddAssign for Num<WIDTH> {
    fn add_assign(&mut self, rhs: Self) {
        let c = self.clone();
        *self = c.add(rhs);
    }
}

impl<const WIDTH: usize> Sub for Num<WIDTH> {
    type Output = Self;

    fn sub(self, rhs: Num<WIDTH>) -> Self::Output {
        let mut r: Num<WIDTH> = Self::new(&[]);
        let mut borrow = false;
        let mut neg = false;

        if let Ordering::Less = self.cmp(&rhs) {
            neg = true;
        }

        for i in (self.msd..WIDTH).rev() {
            let mut d = i64::from(self.digits[i]);

            if borrow || i >= rhs.msd {
                if borrow {
                    d -= 1;
                }

                if i >= rhs.msd {
                    d -= i64::from(rhs.digits[i]);
                }

                if d < 0 {
                    borrow = true;
                    d += i64::try_from(B).expect("impossible to fail");
                } else {
                    borrow = false;
                }
            }

            r.digits[i] = u32::try_from(d).expect("subtraction failed");
        }

        r.update_msd();
        r.neg = neg;
        r
    }
}

impl<const WIDTH: usize> SubAssign for Num<WIDTH> {
    fn sub_assign(&mut self, rhs: Self) {
        let c = self.clone();
        *self = c.sub(rhs);
    }
}

impl<const WIDTH: usize> From<u32> for Num<WIDTH> {
    fn from(n: u32) -> Self {
        let digits = to_digits(n);
        Self::new(&digits)
    }
}

impl<const WIDTH: usize> From<String> for Num<WIDTH> {
    fn from(s: String) -> Self {
        let digits: Vec<u32> = s
            .chars()
            .collect::<Vec<char>>()
            .iter()
            .map(|c| c.to_digit(10).expect("not a digit"))
            .collect();
        Self::new(&digits)
    }
}

impl<const WIDTH: usize> From<&str> for Num<WIDTH> {
    fn from(s: &str) -> Self {
        Self::from(s.to_string())
    }
}

impl<const WIDTH: usize> Display for Num<WIDTH> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        for i in self.msd..WIDTH {
            s += &format!("{}", self.digits[i]);
        }

        write!(f, "{s}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_msd_width_3() {
        let num: Num<3> = Num::new(&[1, 2, 3]);
        assert_eq!(0, num.msd);
    }

    #[test]
    fn check_msd_width_200() {
        let num: Num<200> = Num::new(&[1, 2, 3]);
        assert_eq!(197, num.msd);
        assert_eq!(1, num.digits[num.msd]);
        assert_eq!(2, num.digits[num.msd + 1]);
        assert_eq!(3, num.digits[num.msd + 2]);
    }

    #[test]
    fn check_from() {
        let num1: Num<200> = Num::new(&[1, 2, 3]);
        let num2: Num<200> = Num::from(123);
        assert_eq!(num1.digits, num2.digits);
    }

    #[test]
    fn check_from_string() {
        let num1: Num<200> = Num::from(123);
        let num2: Num<200> = Num::from("123");
        assert_eq!(num1.digits, num2.digits);
    }

    #[test]
    fn test_add() {
        let num1: Num<200> = Num::from(123);
        let num2: Num<200> = Num::from(123);
        let expected_result: Num<200> = Num::from(123 + 123);
        assert_eq!((num1 + num2).digits, expected_result.digits);
    }

    #[test]
    fn test_add_assign() {
        let mut num1: Num<200> = Num::from(123);
        let num2: Num<200> = Num::from(123);
        let expected_result: Num<200> = Num::from(123 + 123);
        num1 += num2;
        assert_eq!(num1.digits, expected_result.digits);
    }

    #[test]
    fn test_sub() {
        let num1: Num<200> = Num::from(123);
        let num2: Num<200> = Num::from(100);
        let expected_result: Num<200> = Num::from(123 - 100);
        assert_eq!((num1 - num2).digits, expected_result.digits);
    }

    #[test]
    fn test_sub_assign() {
        let mut num1: Num<200> = Num::from(123);
        let num2: Num<200> = Num::from(100);
        let expected_result: Num<200> = Num::from(123 - 100);
        num1 -= num2;
        assert_eq!(num1.digits, expected_result.digits);
    }

    #[test]
    fn test_sub_underflow() {
        let num1: Num<200> = Num::from(123);
        let num2: Num<200> = Num::from(100);
        assert!((num2 - num1).neg);
    }

    #[test]
    fn test_add_overflow() {
        let num1: Num<200> = Num::from(129);
        let num2: Num<200> = Num::from(123);
        let expected_result: Num<200> = Num::from(129 + 123);
        assert_eq!((num1 + num2).digits, expected_result.digits);
    }

    #[test]
    fn assert_len() {
        let n: Num<5> = Num::from(100);
        assert_eq!(n.len(), 3);
    }

    #[test]
    fn assert_print() {
        let n: Num<5> = Num::from(100);
        assert_eq!(format!("The number is: {n}"), "The number is: 100");
    }
}
