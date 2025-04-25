use crate::NonZeroChar;
use core::error::Error;
use core::fmt::Display;
use core::ops::RangeInclusive;
use core::iter::FusedIterator;

#[inline]
fn pack(x: Option<char>) -> Option<NonZeroChar> {
    x.map(|ch| {
        // SAFETY: create this iter by NonZeroChar::MIN
        unsafe { NonZeroChar::new_unchecked(ch) }
    })
}

/// This struct is created by the [`iter_inclusive`] method on [`NonZeroChar`].
/// See its documentation for more.
///
/// [`iter_inclusive`]: NonZeroChar::iter_inclusive
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

/// Decode Utf16 errors, created by the [`DecodeUtf16::next`]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodeUtf16Error {
    error: Option<core::char::DecodeUtf16Error>,
}

impl From<core::char::DecodeUtf16Error> for DecodeUtf16Error {
    fn from(error: core::char::DecodeUtf16Error) -> Self {
        Self { error: error.into() }
    }
}

impl DecodeUtf16Error {
    /// Returns the unpaired surrogate which caused this error.
    pub fn unpaired_surrogate(&self) -> Option<u16> {
        self.error.as_ref()
            .map(|e| e.unpaired_surrogate())
    }

    /// Returns error code
    pub fn code(&self) -> u16 {
        self.unpaired_surrogate()
            .unwrap_or(0)
    }
}

impl Display for DecodeUtf16Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Some(e) = &self.error {
            write!(f, "unpaired surrogate found: {:x}", e.unpaired_surrogate())
        } else {
            write!(f, "decode char by zero")
        }
    }
}

impl Error for DecodeUtf16Error {
    fn description(&self) -> &str {
        if self.error.is_some() {
            "unpaired surrogate found"
        } else {
            "decode char by zero"
        }
    }
}

/// This struct is created by the [`decode_utf16`] method on [`NonZeroChar`].
/// See its documentation for more.
///
/// [`decode_utf16`]: NonZeroChar::decode_utf16
#[derive(Debug, Clone)]
pub struct DecodeUtf16<I: Iterator<Item = u16>> {
    pub(crate) iter: core::char::DecodeUtf16<I>,
}

impl<I: Iterator<Item = u16>> Iterator for DecodeUtf16<I> {
    type Item = Result<NonZeroChar, DecodeUtf16Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let ch = self.iter.next()?;
        ch.map_err(Into::into)
            .and_then(|ch| NonZeroChar::new(ch)
                .ok_or(DecodeUtf16Error { error: None }))
            .into()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[test]
fn iter_all() {
    let mut last = '\0';
    for ch in NonZeroChar::MIN.iter_inclusive(NonZeroChar::MAX) {
        last = ch.get();
    }
    assert_ne!(last, '\0')
}
