pub trait NumFrom<const N: usize, const W: usize> {
    type O<'a>;
    #[must_use]
    fn convert(&self, other: Self::O<'_>) -> Self;
    #[must_use]
    fn truncate(&self, other: Self::O<'_>) -> Self;
}
