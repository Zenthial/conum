use std::cmp::Ordering;
use std::fmt::Display;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Sub, SubAssign};

use crate::errors::MathError;
use crate::num_from::{FromSize, NumFrom};
use crate::to_digit::ToDigit;

const B: u64 = 10;

#[derive(Clone, Debug)]
pub struct Num {
    pub(crate) digits: Box<[u32]>,
    pub(crate) msd: usize,
    pub(crate) neg: bool,
    pub(crate) size: usize,
}

impl Num {
    #[must_use]
    pub fn new(digits: &[u32], size: usize) -> Self {
        // let mut dig = [0_u32; N];
        let mut dig = Vec::with_capacity(size);

        for (i, d) in digits.iter().enumerate() {
            dig[size - (digits.len() - i)] = *d;
        }

        Self {
            digits: dig.into_boxed_slice(),
            msd: size - digits.len(),
            size,
            neg: false,
        }
    }

    #[must_use]
    pub fn zero(size: usize) -> Self {
        let dig = vec![0_u32; size];
        Self {
            digits: dig.into_boxed_slice(),
            msd: size - 1,
            size,
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
        self.size - self.msd
    }

    fn mul_digit(&self, s: u32, r: &mut Self) -> Result<(), MathError> {
        let mut carry = 0_u64;
        if s == 0 {
            return Ok(());
        }

        let s_conv = u64::from(s);
        for i in (self.msd..self.size).rev() {
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
        if self.is_zero() {
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
        self.msd == (self.size - 1) && self.digits[self.msd] == 0
    }

    #[must_use]
    pub fn get_n(&self) -> usize {
        self.size
    }

    #[must_use]
    pub fn to_zeroed_string(&self) -> String {
        let mut s = "0".repeat(self.size);
        for i in self.msd..self.size {
            s.replace_range(i..=i, &format!("{}", self.digits[i]));
        }

        s
    }

    /// # Errors
    /// todo!
    pub fn checked_add(&self, rhs: &Self) -> Result<Self, MathError> {
        if rhs.len() > self.len() {
            return rhs.checked_add(self);
        }

        let mut r = Num::new(&[], self.size);
        let mut carry = false;

        for i in (self.msd..self.size).rev() {
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
    pub fn checked_mul(&self, rhs: &Self) -> Result<Self, MathError> {
        if self.len() < rhs.len() {
            return rhs.checked_mul(self);
        }

        let mut big_r: Num = Self::zero(self.size);
        let mut r: Num = Self::zero(self.size);
        self.mul_digit(rhs.digits[self.size - 1], &mut r)?;
        for i in (rhs.msd..self.size - 1).rev() {
            self.mul_digit(rhs.digits[i], &mut big_r)?;
            big_r.shift_left(self.size - 1 - i);
            r += &big_r;
        }

        Ok(r)
    }
}

impl Eq for Num {}

impl PartialEq for Num {
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

impl PartialOrd for Num {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Num {
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

impl Add for Num {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        (&self).add(&rhs)
    }
}

impl Add<&Num> for &Num {
    type Output = Num;

    fn add(self, rhs: &Num) -> Self::Output {
        match self.checked_add(rhs) {
            Ok(output) => output,
            Err(e) => panic!("{}", e),
        }
    }
}

impl AddAssign<i32> for Num {
    fn add_assign(&mut self, rhs: i32) {
        let c = self.clone();
        *self = c.add(Self::from_with_size(rhs, self.size));
    }
}

impl AddAssign<u32> for Num {
    fn add_assign(&mut self, rhs: u32) {
        let c = self.clone();
        *self = c.add(Self::from_with_size(rhs, self.size));
    }
}

impl AddAssign<&Num> for Num {
    fn add_assign(&mut self, rhs: &Num) {
        let c = &self.clone();
        *self = c.add(rhs);
    }
}

impl Sub for Num {
    type Output = Self;

    fn sub(self, rhs: Num) -> Self::Output {
        let mut r: Num = Self::new(&[], self.size);
        let mut borrow = false;
        let mut neg = false;

        if let Ordering::Less = self.cmp(&rhs) {
            neg = true;
        }

        for i in (self.msd..self.size).rev() {
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

impl SubAssign for Num {
    fn sub_assign(&mut self, rhs: Self) {
        let c = self.clone();
        *self = c.sub(rhs);
    }
}

impl Mul for Num {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match self.checked_mul(&rhs) {
            Ok(output) => output,
            Err(e) => panic!("{}", e),
        }
    }
}

impl MulAssign for Num {
    fn mul_assign(&mut self, rhs: Self) {
        let c = self.clone();
        *self = c.mul(rhs);
    }
}

impl MulAssign<&Num> for Num {
    fn mul_assign(&mut self, rhs: &Num) {
        let c = self.clone();
        let real_rhs = rhs.clone();
        *self = c.mul(real_rhs);
    }
}

impl MulAssign<u32> for Num {
    fn mul_assign(&mut self, rhs: u32) {
        let c = self.clone();
        let real_rhs = Self::from_with_size(rhs, self.size);
        *self = c.mul(real_rhs);
    }
}

fn yz_from_x(x: &Num, w: usize) -> u32 {
    let iy = x.size - w;

    let y = if iy >= x.msd { x.digits[iy] } else { 0 };

    let z = if iy + 1 >= x.msd { x.digits[iy + 1] } else { 0 };

    let b = u32::try_from(B).expect("");
    y * b + z
}

fn correct_d_and_subtract(x: &mut Num, b: &Num, d: &mut u32) {
    let mut t: Num = Num::from_with_size(0, x.size);
    if u64::from(*d) > B - 1 {
        *d = u32::try_from(B - 1).expect("u32 overflow");
    }

    b.mul_digit(*d, &mut t).unwrap();

    if t > *x {
        *d -= 1;
        t -= b.clone();
        if t > *x {
            *d -= 1;
            t -= b.clone();
        }
    }

    *x -= t;
}

impl Div for Num {
    type Output = (Self, Self);

    fn div(mut self, mut divisor: Self) -> Self::Output {
        let mut qt: Num = Self::from_with_size(0, self.size);
        let rm: Num;
        let mut af: Num = Self::from_with_size(0, self.size);
        let mut bf: Num = Self::from_with_size(0, self.size);
        let mut x: Num = Self::new(&[], self.size);
        let mut f = 1;

        assert!(!divisor.is_zero(), "divide by zero error");

        if self.len() < divisor.len() {
            rm = self;
            return (qt, rm);
        }

        let mut e = divisor.digits[divisor.msd];
        let b = u32::try_from(B).expect("u32 overflow");

        if divisor.len() > 1 && e < b / 2 {
            f = b / (e + 1);
            self.mul_digit(f, &mut af).unwrap();
            divisor.mul_digit(f, &mut bf).unwrap();
            self = af;
            divisor = bf;
            e = divisor.digits[divisor.msd];
        }

        let a_len = self.len();
        let b_len = divisor.len();

        qt.msd = self.size - (a_len - b_len + 1);

        let mut m = 0;
        while m < a_len {
            if m == 0 {
                m = b_len;
                x.prefix(&self.digits[self.msd..self.msd + m]);
            } else {
                m += 1;
                x.shift_left(1);
                x.digits[self.size - 1] = self.digits[self.msd + m - 1];
            }

            let mut yz = yz_from_x(&x, b_len + 1);
            let mut d = yz / e;

            if b_len > 1 {
                correct_d_and_subtract(&mut x, &divisor, &mut d);
            } else {
                yz -= e * d;
                x = Num::from_with_size(yz, self.size);
            }

            qt.digits[qt.msd + m - b_len] = d;
        }

        qt.update_msd();

        if f > 1 {
            let t1: Num = Self::from_with_size(f, self.size);
            let (r_rm, _) = x.div(t1);
            rm = r_rm;
        } else {
            rm = x;
        }

        return (qt, rm);
    }
}

// impl<const N: usize, const W: usize> From<Num<W>> for Num where N != W {
//     fn from_with_size(n: Num<W>) -> Self {
//         let digits = n.to_digits();
//         Self::new(&digits)
//     }
// }

impl FromSize<u32> for Num {
    fn from_with_size(n: u32, size: usize) -> Self {
        let digits = n.to_digits();
        Self::new(&digits, size)
    }
}

impl FromSize<i32> for Num {
    fn from_with_size(rhs: i32, size: usize) -> Self {
        let signed = rhs < 0;
        let i = if signed {
            u32::try_from(-rhs).expect("shouldnt fail")
        } else {
            u32::try_from(rhs).expect("shouldn't fail")
        };

        let mut real_rhs = Self::from_with_size(i, size);
        real_rhs.neg = signed;
        real_rhs
    }
}

impl NumFrom for Num {
    type O<'a> = &'a Num;

    fn convert(&self, other: Self::O<'_>) -> Self {
        if other.size > self.size {
            return self.truncate(other);
        }

        Self::new(&other.digits[other.msd..other.size], self.size)
    }

    // W is always bigger here, which means that [u32; W] can be shrunk from W - N .. W
    fn truncate(&self, other: Self::O<'_>) -> Self {
        let slice = &other.digits;
        let start_index = other.size - self.size;
        let new_slice = &slice[start_index..other.size];

        Self::new(new_slice, self.size)
    }
}

impl FromSize<u128> for Num {
    fn from_with_size(n: u128, size: usize) -> Self {
        let digits = n.to_digits();
        Self::new(&digits, size)
    }
}

impl FromSize<String> for Num {
    fn from_with_size(s: String, size: usize) -> Self {
        let digits: Vec<u32> = s
            .chars()
            .collect::<Vec<char>>()
            .iter()
            .map(|c| c.to_digit(10).expect("not a digit"))
            .collect();
        Self::new(&digits, size)
    }
}

impl FromSize<&str> for Num {
    fn from_with_size(s: &str, size: usize) -> Self {
        Self::from_with_size(s.to_string(), size)
    }
}

impl Display for Num {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        for i in self.msd..self.size {
            s += &format!("{}", self.digits[i]);
        }

        write!(f, "{s}")
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests {
    use super::*;
    use rand::{thread_rng, Rng};

    #[test]
    fn check_msd_width_3() {
        let num = Num::new(&[1, 2, 3], 3);
        assert_eq!(0, num.msd);
    }

    #[test]
    fn check_msd_width_200() {
        let num = Num::new(&[1, 2, 3], 200);
        assert_eq!(197, num.msd);
        assert_eq!(1, num.digits[num.msd]);
        assert_eq!(2, num.digits[num.msd + 1]);
        assert_eq!(3, num.digits[num.msd + 2]);
    }

    #[test]
    fn check_from() {
        let num1 = Num::new(&[1, 2, 3], 200);
        let num2 = Num::from_with_size(123, 200);
        assert_eq!(num1.digits, num2.digits);
    }

    #[test]
    fn check_from_string() {
        let num1 = Num::from_with_size(123, 200);
        let num2 = Num::from_with_size("123", 200);
        assert_eq!(num1.digits, num2.digits);
    }

    #[test]
    fn test_add() {
        let num1 = Num::from_with_size(123, 200);
        let num2 = Num::from_with_size(123, 200);
        let expected_result = Num::from_with_size(123 + 123, 200);
        assert_eq!((num1 + num2).digits, expected_result.digits);
    }

    #[test]
    fn test_add_empty() {
        let num1 = Num::from_with_size(123, 200);
        let num2 = Num::new(&[], 200);
        let expected_result = Num::from_with_size(123, 200);
        assert_eq!((num1 + num2).digits, expected_result.digits);
    }

    #[test]
    fn test_add_assign() {
        let mut num1 = Num::from_with_size(123, 200);
        let num2 = Num::from_with_size(123, 200);
        let expected_result = Num::from_with_size(123 + 123, 200);
        num1 += &num2;
        assert_eq!(num1.digits, expected_result.digits);
    }

    #[test]
    fn test_sub() {
        let num1 = Num::from_with_size(123, 200);
        let num2 = Num::from_with_size(100, 200);
        let expected_result = Num::from_with_size(123 - 100, 200);
        assert_eq!((num1 - num2).digits, expected_result.digits);
    }

    #[test]
    fn test_sub_assign() {
        let mut num1 = Num::from_with_size(123, 200);
        let num2 = Num::from_with_size(100, 200);
        let expected_result = Num::from_with_size(123 - 100, 200);
        num1 -= num2;
        assert_eq!(num1.digits, expected_result.digits);
    }

    #[test]
    fn test_sub_underflow() {
        let num1 = Num::from_with_size(123, 200);
        let num2 = Num::from_with_size(100, 200);
        assert!((num2 - num1).neg);
    }

    #[test]
    fn test_add_overflow() {
        let num1 = Num::from_with_size(129, 200);
        let num2 = Num::from_with_size(123, 200);
        let expected_result = Num::from_with_size(129 + 123, 200);
        assert_eq!((num1 + num2).digits, expected_result.digits);
    }

    #[test]
    fn test_mul_digit() {
        let num1 = Num::from_with_size(55, 10);
        let mut r = Num::new(&[], 10);
        let expected_result = Num::from_with_size(55 * 9, 10);
        num1.mul_digit(9, &mut r).unwrap();
        assert_eq!(r.digits, expected_result.digits);
    }

    #[test]
    fn test_shift_left() {
        let mut num1 = Num::from_with_size(55, 10);
        let expected_result = Num::from_with_size(5500, 10);
        num1.shift_left(2);
        assert_eq!(num1.digits, expected_result.digits);
    }

    #[test]
    fn test_shift_left_2() {
        let mut num1 = Num::from_with_size(5, 10);
        let expected_result = Num::from_with_size(50, 10);
        num1.shift_left(1);
        assert_eq!(num1.digits, expected_result.digits);
    }

    #[test]
    fn test_mul() {
        let num1 = Num::from_with_size(5, 10);
        let num2 = Num::from_with_size(5, 10);
        let expected_result = Num::from_with_size(5 * 5, 10);
        assert_eq!((num1 * num2).digits, expected_result.digits);
    }

    #[test]
    fn assert_len() {
        let n = Num::from_with_size(100, 5);
        assert_eq!(n.len(), 3);
    }

    #[test]
    fn test_msd_zero() {
        let n = Num::from_with_size(0, 5);
        assert_eq!(n.msd, 4);
    }

    #[test]
    fn test_zero_constructor() {
        let n = Num::zero(5);
        let z = Num::from_with_size(5, 5);
        assert_eq!(n.digits, z.digits);
        assert_eq!(n.msd, z.msd);
    }

    #[test]
    fn test_prefix() {
        let mut n = Num::from_with_size(0, 5);
        let expected_result = Num::from_with_size(1110, 5);
        n.prefix(&[1, 1, 1]);
        assert_eq!(n.digits, expected_result.digits);
    }

    #[test]
    fn assert_print() {
        let n = Num::from_with_size(100, 5);
        assert_eq!(format!("The number is: {n}"), "The number is: 100");
    }

    #[test]
    fn factorial() {
        let max = 20;
        let mut i = 1_u32;
        let mut fact = Num::new(&[1], 20);
        let result: u128 = (1..=u128::from(max)).product();

        loop {
            if i >= max {
                break;
            }

            i += 1;
            fact *= i;
        }

        let r = Num::from_with_size(result, 18);
        assert_eq!(fact, r);
    }

    #[test]
    fn test_convert_truncate() {
        let n = Num::zero(5);
        let z = Num::from_with_size(111_111, 6);
        let conv = n.convert(&z);
        assert_eq!(n.get_n(), conv.get_n());
        assert_eq!(*conv.digits, [1, 1, 1, 1, 1]);
    }

    #[test]
    fn test_convert_upscale() {
        let n = Num::zero(100);
        let z = Num::from_with_size(111_111, 6);
        let conv = n.convert(&z);
        let mut digits_cmp = "0"
            .repeat(94)
            .chars()
            .map(|c| c.to_digit(10).unwrap())
            .collect::<Vec<u32>>();
        digits_cmp.append(&mut vec![1, 1, 1, 1, 1, 1]);
        assert_eq!(n.get_n(), conv.get_n());
        assert_eq!(Vec::from(&*conv.digits), digits_cmp);
    }

    #[test]
    fn test_convert_upscale_two() {
        const N: usize = 18;
        const Z: usize = 3;
        let n: Num = Num::zero(2);
        let z = Num::from_with_size(1, Z);
        let conv = n.convert(&z);
        assert_eq!(N - conv.msd, Z - z.msd);
    }

    #[test]
    fn factorial_upscale() {
        let max = Num::from_with_size(16, 2);
        let mut i = Num::from_with_size(1, 2);
        let mut fact = Num::new(&[1], 18);
        let result: u128 = (1..=16).product();

        loop {
            if i >= max {
                break;
            }

            i += 1;
            let conv = fact.convert(&i);
            fact *= conv;
        }

        let r = Num::from_with_size(result, 18);
        assert_eq!(fact, r);
    }

    #[test]
    fn div() {
        let z = Num::from_with_size(2, 2);
        let y = Num::from_with_size(8, 2);
        let (qt, _rm) = y / z;
        assert_eq!(*qt.digits, [0, 4]);
    }

    #[test]
    fn div_large() {
        let z = Num::from_with_size(2, 10);
        let y = Num::from_with_size(800, 10);
        let (qt, _rm) = y / z;
        assert_eq!(*qt.digits, [0, 0, 0, 0, 0, 0, 0, 4, 0, 0]);
    }

    #[test]
    #[allow(non_snake_case)]
    fn div_random() {
        let mut rng = thread_rng();
        for _ in 0..100 {
            let Z = rng.gen_range(1..=10000);
            let Y = rng.gen_range(1..Z);
            let z = Num::from_with_size(Z, 5);
            let y = Num::from_with_size(Y, 5);
            let (qt, _rm) = z / y;
            let result = Num::from_with_size(Z / Y, 5);
            assert_eq!(*qt.digits, *result.digits);
        }
    }

    #[test]
    fn div_large_reverse() {
        let z = Num::from_with_size(2, 10);
        let y = Num::from_with_size(800, 10);
        let (qt, _rm) = z / y;
        assert_eq!(*qt.digits, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    }
}
