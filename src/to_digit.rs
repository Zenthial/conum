pub trait ToDigit {
    fn to_digits(self) -> Vec<u32>;
    fn digits_inner(self, xs: &mut Vec<u32>);
}

impl ToDigit for u32 {
    fn to_digits(self: u32) -> Vec<u32> {
        let mut xs = Vec::new();
        self.digits_inner(&mut xs);
        xs
    }

    fn digits_inner(self, xs: &mut Vec<u32>) {
        let n = self;
        if n >= 10 {
            Self::digits_inner(n / 10, xs);
        }
        xs.push(n % 10);
    }
}

impl ToDigit for u128 {
    fn to_digits(self: u128) -> Vec<u32> {
        let mut xs = Vec::new();
        self.digits_inner(&mut xs);
        xs
    }

    fn digits_inner(self, xs: &mut Vec<u32>) {
        let n = self;
        if n >= 10 {
            Self::digits_inner(n / 10, xs);
        }
        xs.push(u32::try_from(n % 10).expect("cant fail"));
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_digit_u128() {
        let digits = 100_000_000_000_000_000_000_000_000_000_u128.to_digits();
        let digits_str = "100000000000000000000000000000";
        let digits_cmp = digits_str
            .chars()
            .map(|c| c.to_digit(10).unwrap())
            .collect::<Vec<u32>>();
        assert_eq!(digits, digits_cmp);
    }
}
