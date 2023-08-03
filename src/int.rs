use std::cmp::Ordering;
use std::fmt::Display;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Sub, SubAssign};

use crate::errors::MathError;
use crate::num_from::NumFrom;
use crate::to_digit::ToDigit;

const B: u64 = 10;

#[derive(Clone, Debug)]
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

    #[must_use]
    pub fn zero() -> Self {
        let dig = [0_u32; N];
        Self {
            digits: Box::new(dig),
            msd: N - 1,
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

    fn mul_digit(&self, s: u32, r: &mut Self) -> Result<(), MathError<N>> {
        let mut carry = 0_u64;
        if s == 0 {
            return Ok(());
        }

        let s_conv = u64::from(s);
        for i in (self.msd..N).rev() {
            let d = u64::from(self.digits[i]) * s_conv + carry;

            carry = d / B;
            r.digits[i] = if let Ok(n) = u32::try_from(d % B) {
                n
            } else {
                return Err(MathError::ConversionError);
            };
        }

        if carry == 0 {
            r.msd = self.msd;
        } else {
            if self.msd == 0 {
                r.msd = 0;
                return Err(MathError::Overflow(r.clone()));
            }
            // assert!(self.msd != 0, "multiply_digit overflow");

            r.digits[self.msd - 1] = if let Ok(n) = u32::try_from(carry) {
                n
            } else {
                return Err(MathError::ConversionError);
            };
            r.msd = self.msd - 1;
        }

        Ok(())
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
        self.msd -= src.len();
        for i in self.msd..self.msd + src.len() {
            self.digits[i] = src[i - self.msd];
        }
    }

    fn is_zero(&self) -> bool {
        self.msd == (N - 1)
    }

    #[must_use]
    pub fn get_n(&self) -> usize {
        N
    }

    #[must_use]
    pub fn to_zeroed_string(&self) -> String {
        let mut s = "0".repeat(N);
        for i in self.msd..N {
            s.replace_range(i..=i, &format!("{}", self.digits[i]));
        }

        s
    }

    /// # Errors
    /// todo!
    pub fn checked_add(&self, rhs: &Self) -> Result<Self, MathError<N>> {
        if rhs.len() > self.len() {
            return rhs.checked_add(self);
        }

        let mut r: Num<N> = Num::new(&[]);
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

            r.digits[i] = if let Ok(n) = u32::try_from(d) {
                n
            } else {
                return Err(MathError::ConversionError);
            };
        }

        if carry {
            if self.msd == 0 {
                r.msd = 0;
                return Err(MathError::Overflow(r));
            }

            r.digits[self.msd - 1] = 1;
            r.msd = self.msd - 1;
        } else {
            r.msd = self.msd;
        }

        Ok(r)
    }

    /// # Errors
    /// todo!
    pub fn checked_mul(&self, rhs: &Self) -> Result<Self, MathError<N>> {
        if self.len() < rhs.len() {
            return rhs.checked_mul(self);
        }

        let mut big_r: Num<N> = Self::zero();
        let mut r: Num<N> = Self::zero();
        self.mul_digit(rhs.digits[N - 1], &mut r)?;
        for i in (rhs.msd..N - 1).rev() {
            self.mul_digit(rhs.digits[i], &mut big_r)?;
            big_r.shift_left(N - 1 - i);
            r += &big_r;
        }

        Ok(r)
    }
}

impl<const N: usize> Eq for Num<N> {}

impl<const N: usize> PartialEq for Num<N> {
    fn eq(&self, other: &Self) -> bool {
        if self.msd == other.msd {
            let self_digits = self.digits.iter();
            let other_digits = other.digits.iter();
            let zip = self_digits.zip(other_digits);

            for (s, o) in zip {
                if *s != *o {
                    return false;
                }
            }

            return true;
        }

        false
    }
}

impl<const N: usize> PartialOrd for Num<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const N: usize> Ord for Num<N> {
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

        other.msd.cmp(&self.msd)
    }
}

impl<const N: usize> Add for Num<N> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        (&self).add(&rhs)
    }
}

impl<const N: usize> Add<&Num<N>> for &Num<N> {
    type Output = Num<N>;

    fn add(self, rhs: &Num<N>) -> Self::Output {
        match self.checked_add(rhs) {
            Ok(output) => output,
            Err(e) => panic!("{}", e),
        }
    }
}

impl<const N: usize> AddAssign<i32> for Num<N> {
    fn add_assign(&mut self, rhs: i32) {
        let c = self.clone();
        *self = c.add(Self::from(rhs));
    }
}

impl<const N: usize> AddAssign<u32> for Num<N> {
    fn add_assign(&mut self, rhs: u32) {
        let c = self.clone();
        *self = c.add(Self::from(rhs));
    }
}

impl<const N: usize> AddAssign<&Num<N>> for Num<N> {
    fn add_assign(&mut self, rhs: &Num<N>) {
        let c = &self.clone();
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
        match self.checked_mul(&rhs) {
            Ok(output) => output,
            Err(e) => panic!("{}", e),
        }
    }
}

impl<const N: usize> MulAssign for Num<N> {
    fn mul_assign(&mut self, rhs: Self) {
        let c = self.clone();
        *self = c.mul(rhs);
    }
}

impl<const N: usize> MulAssign<&Num<N>> for Num<N> {
    fn mul_assign(&mut self, rhs: &Num<N>) {
        let c = self.clone();
        let real_rhs = rhs.clone();
        *self = c.mul(real_rhs);
    }
}

impl<const N: usize> MulAssign<u32> for Num<N> {
    fn mul_assign(&mut self, rhs: u32) {
        let c = self.clone();
        let real_rhs = Self::from(rhs);
        *self = c.mul(real_rhs);
    }
}

fn yz_from_x<const N: usize>(x: &Num<N>, w: usize) -> u32 {
    let iy = N - w;

    let y = if iy >= x.msd { x.digits[iy] } else { 0 };

    let z = if iy + 1 >= x.msd { x.digits[iy + 1] } else { 0 };

    let b = u32::try_from(B).expect("");
    y * b + z
}

#[allow(unused)]
fn correct_d_and_subtract<const N: usize>(x: &mut Num<N>, b: &Num<N>, d: &mut u32) {
    let mut t: Num<N> = Num::from(0);
    if u64::from(*d) > B - 1 {
        *d = u32::try_from(B - 1).expect("u32 overflow");
    }
}

impl<const N: usize> Div for Num<N> {
    type Output = (Self, Self);

    #[allow(unused)]
    fn div(mut self, mut divisor: Self) -> Self::Output {
        let mut qt: Num<N> = Self::from(0);
        let mut rm: Num<N> = Self::from(0);
        let mut af: Num<N> = Self::from(0);
        let mut bf: Num<N> = Self::from(0);
        let mut x: Num<N> = Self::from(0);

        assert!(!divisor.is_zero(), "divide by zero error");

        if self.len() < divisor.len() {
            rm = self;
            return (qt, rm);
        }

        let mut e = divisor.digits[divisor.msd];
        let b = u32::try_from(B).expect("u32 overflow");

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

// impl<const N: usize, const W: usize> From<Num<W>> for Num<N> where N != W {
//     fn from(n: Num<W>) -> Self {
//         let digits = n.to_digits();
//         Self::new(&digits)
//     }
// }

impl<const N: usize> From<u32> for Num<N> {
    fn from(n: u32) -> Self {
        let digits = n.to_digits();
        Self::new(&digits)
    }
}

impl<const N: usize> From<i32> for Num<N> {
    fn from(rhs: i32) -> Self {
        let signed = rhs < 0;
        let i = if signed {
            u32::try_from(-rhs).expect("shouldnt fail")
        } else {
            u32::try_from(rhs).expect("shouldn't fail")
        };

        let mut real_rhs = Self::from(i);
        real_rhs.neg = signed;
        real_rhs
    }
}

impl<const N: usize, const W: usize> NumFrom<N, W> for Num<N> {
    type O<'a> = &'a Num<W>;

    fn convert(&self, other: Self::O<'_>) -> Self {
        if W > N {
            return self.truncate(other);
        }

        Self::new(&other.digits[other.msd..W])
    }

    // W is always bigger here, which means that [u32; W] can be shrunk from W - N .. W
    fn truncate(&self, other: Self::O<'_>) -> Self {
        let slice = *other.digits;
        let start_index = W - N;
        let new_slice = &slice[start_index..W];

        Self::new(new_slice)
    }
}

impl<const N: usize> From<u128> for Num<N> {
    fn from(n: u128) -> Self {
        let digits = n.to_digits();
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

#[allow(clippy::unwrap_used)]
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
        num1 += &num2;
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
        num1.mul_digit(9, &mut r).unwrap();
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
    fn test_zero_constructor() {
        let n: Num<5> = Num::zero();
        let z: Num<5> = Num::from(0);
        assert_eq!(n.digits, z.digits);
        assert_eq!(n.msd, z.msd);
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

    #[test]
    fn factorial() {
        let max = 20;
        let mut i = 1_u32;
        let mut fact: Num<20> = Num::new(&[1]);
        let result: u128 = (1..=u128::from(max)).product();

        loop {
            if i >= max {
                break;
            }

            i += 1;
            fact *= i;
        }

        let r = Num::from(result);
        assert_eq!(fact, r);
    }

    #[test]
    fn test_convert_truncate() {
        let n: Num<5> = Num::zero();
        let z: Num<6> = Num::from(111_111);
        let conv = n.convert(&z);
        assert_eq!(n.get_n(), conv.get_n());
        assert_eq!(*conv.digits, [1, 1, 1, 1, 1]);
    }

    #[test]
    fn test_convert_upscale() {
        let n: Num<100> = Num::zero();
        let z: Num<6> = Num::from(111_111);
        let conv = n.convert(&z);
        let mut digits_cmp = "0"
            .repeat(94)
            .chars()
            .map(|c| c.to_digit(10).unwrap())
            .collect::<Vec<u32>>();
        digits_cmp.append(&mut vec![1, 1, 1, 1, 1, 1]);
        assert_eq!(n.get_n(), conv.get_n());
        assert_eq!(Vec::from(*conv.digits), digits_cmp);
    }

    #[test]
    fn test_convert_upscale_two() {
        const N: usize = 18;
        const Z: usize = 3;
        let n: Num<N> = Num::zero();
        let z: Num<Z> = Num::from(1);
        let conv = n.convert(&z);
        assert_eq!(N - conv.msd, Z - z.msd);
    }

    #[test]
    fn factorial_upscale() {
        let max: Num<2> = Num::from(16);
        let mut i: Num<2> = Num::from(1);
        let mut fact: Num<18> = Num::new(&[1]);
        let result: u128 = (1..=16).product();

        loop {
            if i >= max {
                break;
            }
            println!("{i}: {fact}");

            i += 1;
            let conv = fact.convert(&i);
            fact *= conv;
        }

        let r = Num::from(result);
        assert_eq!(fact, r);
    }
}
