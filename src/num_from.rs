pub trait NumFrom {
    type O<'a>;
    #[must_use]
    fn convert(&self, other: Self::O<'_>) -> Self;
    #[must_use]
    fn truncate(&self, other: Self::O<'_>) -> Self;
}

pub trait FromSize<T> {
    fn from_with_size(n: T, size: usize) -> Self;
}
