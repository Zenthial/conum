// Credit: https://mathsanew.com/articles/implementing_large_integers_introduction.pdf

#![deny(clippy::pedantic, clippy::perf, clippy::style, clippy::unwrap_used)]
// #![allow(unused)]

use std::cmp::Ordering;
use std::fmt::Display;
use std::ops::{Add, AddAssign, Div, Mul, Sub, SubAssign};

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
pub struct Num<const N: usize> {
    pub(crate) digits: Box<[u32; N]>,
    pub(crate) msd: usize,
    pub(crate) neg: bool,
}

impl<const N: usize> Num<N> {
    #[must_use]
    pub fn new(digits: &[u32]) -> Self {
        let mut dig = [0_u32; N];

        for (i, d) in digits.iter().enumerate() {
            dig[N - (digits.len() - i)] = *d;
        }

        Self {
            digits: Box::new(dig),
            msd: N - digits.len(),
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
        N - self.msd
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

    fn mul_digit(&self, s: u32, r: &mut Self) {
        let mut carry = 0_u64;
        if s == 0 {
            return;
        }

        let s_conv = u64::from(s);
        for i in (self.msd..N).rev() {
            let d = u64::from(self.digits[i]) * s_conv + carry;

            carry = d / B;
            r.digits[i] = u32::try_from(d % B).expect("modulo failed");
        }

        if carry == 0 {
            r.msd = self.msd;
        } else {
            assert!(self.msd != 0, "multiply_digit overflow");

            r.digits[self.msd - 1] = u32::try_from(carry).expect("yo");
            r.msd = self.msd - 1;
        }
    }

    fn shift_left(&mut self, n: usize) {
        assert!(self.msd >= n, "shift left overflow");
        if self.msd == N {
            // equals zero
            return;
        }

        let len = self.len();
        let base = self.msd - n;
        self.digits.copy_within(self.msd.., base);
        self.digits[self.msd - n + len..].fill(0);
        self.msd = base;
    }

    fn prefix(&mut self, src: &[u32]) {
        self.msd = self.msd - src.len();
        for i in self.msd..self.msd + src.len() {
            self.digits[i] = src[i - self.msd];
        }
    }

    fn is_zero(&self) -> bool {
        self.msd == (N - 1)
    }
}

impl<const N: usize> Add for Num<N> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if rhs.len() > self.len() {
            return rhs.add(self);
        }

        let mut r: Num<N> = Self::new(&[]);
        let mut carry = false;

        for i in (self.msd..N).rev() {
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

impl<const N: usize> AddAssign for Num<N> {
    fn add_assign(&mut self, rhs: Self) {
        let c = self.clone();
        *self = c.add(rhs);
    }
}

impl<const N: usize> Sub for Num<N> {
    type Output = Self;

    fn sub(self, rhs: Num<N>) -> Self::Output {
        let mut r: Num<N> = Self::new(&[]);
        let mut borrow = false;
        let mut neg = false;

        if let Ordering::Less = self.cmp(&rhs) {
            neg = true;
        }

        for i in (self.msd..N).rev() {
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

impl<const N: usize> SubAssign for Num<N> {
    fn sub_assign(&mut self, rhs: Self) {
        let c = self.clone();
        *self = c.sub(rhs);
    }
}

impl<const N: usize> Mul for Num<N> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        if self.len() < rhs.len() {
            return rhs.mul(self);
        }

        let mut big_r: Num<N> = Self::new(&[]);
        let mut r: Num<N> = Self::new(&[]);
        self.mul_digit(rhs.digits[N - 1], &mut big_r);
        for i in (self.msd..N).rev() {
            self.mul_digit(rhs.digits[i], &mut big_r);
            big_r.shift_left(N - 1 - i);
            r += big_r.clone();
        }

        r
    }
}

fn yz_from_x<const N: usize>(x: &Num<N>, w: usize) -> u32 {
    let iy = N - w;
    let y;
    let z;

    if iy >= x.msd {
        y = x.digits[iy];
    } else {
        y = 0;
    }

    if iy + 1 >= x.msd {
        z = x.digits[iy + 1];
    } else {
        z = 0
    }

    let b = u32::try_from(B).expect("");
    y * b + z
}

fn correct_d_and_subtract<const N: usize>(x: &mut Num<N>, b: &Num<N>, d: &mut u32) {
    let mut t: Num<N> = Num::from(0);
    if u64::from(*d) > B - 1 {
        *d = u32::try_from(B - 1).unwrap();
    }
}

impl<const N: usize> Div for Num<N> {
    type Output = (Self, Self);

    fn div(mut self, mut divisor: Self) -> Self::Output {
        let mut qt: Num<N> = Self::from(0);
        let mut rm: Num<N> = Self::from(0);
        let mut af: Num<N> = Self::from(0);
        let mut bf: Num<N> = Self::from(0);
        let mut x: Num<N> = Self::from(0);

        if divisor.is_zero() {
            panic!("divide by zero error");
        }

        if self.len() < divisor.len() {
            rm = self;
            return (qt, rm);
        }

        let mut e = divisor.digits[divisor.msd];
        let b = u32::try_from(B).unwrap();

        if divisor.len() > 1 && e < b / 2 {
            let f = b / (e + 1);
            self.mul_digit(f, &mut af);
            divisor.mul_digit(f, &mut bf);
            self = af;
            divisor = bf;
            e = divisor.digits[divisor.msd];
        }

        let a_len = self.len();
        let b_len = divisor.len();

        qt.msd = N - (a_len - b_len + 1);

        let mut m = 0;
        while m < a_len {
            if m == 0 {
                m = b_len;
                x.prefix(&self.digits[self.msd..self.msd + m]);
            } else {
                x.shift_left(1);
                x.digits[N - 1] = self.digits[self.msd + m];
                m += 1;
            }

            let yz = yz_from_x(&x, b_len + 1);
            let mut d = yz / e;

            if b_len > 1 {
                correct_d_and_subtract(&mut x, &divisor, &mut d);
            }
        }

        todo!()
    }
}

impl<const N: usize> From<u32> for Num<N> {
    fn from(n: u32) -> Self {
        let digits = to_digits(n);
        Self::new(&digits)
    }
}

impl<const N: usize> From<String> for Num<N> {
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

impl<const N: usize> From<&str> for Num<N> {
    fn from(s: &str) -> Self {
        Self::from(s.to_string())
    }
}

impl<const N: usize> Display for Num<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        for i in self.msd..N {
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
    fn test_add_empty() {
        let num1: Num<200> = Num::from(123);
        let num2: Num<200> = Num::new(&[]);
        let expected_result: Num<200> = Num::from(123);
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
    fn test_mul_digit() {
        let num1: Num<10> = Num::from(55);
        let mut r: Num<10> = Num::new(&[]);
        let expected_result: Num<10> = Num::from(55 * 9);
        num1.mul_digit(9, &mut r);
        assert_eq!(r.digits, expected_result.digits);
    }

    #[test]
    fn test_shift_left() {
        let mut num1: Num<10> = Num::from(55);
        let expected_result: Num<10> = Num::from(5500);
        num1.shift_left(2);
        assert_eq!(num1.digits, expected_result.digits);
    }

    #[test]
    fn test_shift_left_2() {
        let mut num1: Num<10> = Num::from(5);
        let expected_result: Num<10> = Num::from(50);
        num1.shift_left(1);
        assert_eq!(num1.digits, expected_result.digits);
    }

    #[test]
    fn test_mul() {
        let num1: Num<10> = Num::from(5);
        let num2: Num<10> = Num::from(5);
        let expected_result: Num<10> = Num::from(5 * 5);
        assert_eq!((num1 * num2).digits, expected_result.digits);
    }

    #[test]
    fn assert_len() {
        let n: Num<5> = Num::from(100);
        assert_eq!(n.len(), 3);
    }

    #[test]
    fn test_msd_zero() {
        let n: Num<5> = Num::from(0);
        assert_eq!(n.msd, 4);
    }

    #[test]
    fn test_prefix() {
        let mut n: Num<5> = Num::from(0);
        let expected_result: Num<5> = Num::from(1110);
        n.prefix(&[1, 1, 1]);
        assert_eq!(n.digits, expected_result.digits);
    }

    #[test]
    fn assert_print() {
        let n: Num<5> = Num::from(100);
        assert_eq!(format!("The number is: {n}"), "The number is: 100");
    }
}
