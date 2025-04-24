use crate::NonZeroChar;
use core::ops::RangeInclusive;
use core::iter::FusedIterator;

#[inline]
fn pack(x: Option<char>) -> Option<NonZeroChar> {
    x.map(|ch| {
        // SAFETY: create this iter by NonZeroChar::MIN
        unsafe { NonZeroChar::new_unchecked(ch) }
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RangeInclusiveIter {
    pub(crate) iter: <RangeInclusive<char> as IntoIterator>::IntoIter,
}

impl RangeInclusiveIter {
    pub fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }

    pub fn contains<U>(&self, item: &U) -> bool
    where U: PartialOrd<char> + ?Sized,
          char: PartialOrd<U>,
    {
        self.iter.contains(item)
    }
}

impl Default for RangeInclusiveIter {
    fn default() -> Self {
        let min = NonZeroChar::MIN.get();
        let iter = min..=min;
        Self { iter: iter.into_iter() }
    }
}

impl Iterator for RangeInclusiveIter {
    type Item = NonZeroChar;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        pack(self.iter.next())
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        pack(self.iter.nth(n))
    }

    #[inline]
    fn min(self) -> Option<Self::Item> {
        pack(self.iter.min())
    }

    #[inline]
    fn max(self) -> Option<Self::Item> {
        pack(self.iter.max())
    }

    #[inline]
    fn is_sorted(self) -> bool {
        self.iter.is_sorted()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl DoubleEndedIterator for RangeInclusiveIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        pack(self.iter.next_back())
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        pack(self.iter.nth_back(n))
    }
}

impl FusedIterator for RangeInclusiveIter { }

#[test]
fn iter_all() {
    let mut last = '\0';
    for ch in NonZeroChar::MIN.iter_inclusive(NonZeroChar::MAX) {
        last = ch.get();
    }
    assert_ne!(last, '\0')
}
