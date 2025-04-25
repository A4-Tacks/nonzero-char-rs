extern crate alloc;

use core::{error::Error, fmt::Display};

use crate::NonZeroChar;
use alloc::{borrow::Cow, boxed::Box, string::String};

macro_rules! impl_froms {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl From<NonZeroChar> for $ty {
                fn from(value: NonZeroChar) -> Self {
                    value.get().into()
                }
            }
        )+
    };
}
macro_rules! impl_try_froms {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl TryFrom<NonZeroChar> for $ty {
                type Error = <$ty as TryFrom<char>>::Error;

                fn try_from(value: NonZeroChar) -> Result<Self, Self::Error> {
                    value.get().try_into()
                }
            }
        )+
    };
}
macro_rules! impl_fromiters {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl FromIterator<NonZeroChar> for $ty {
                fn from_iter<T: IntoIterator<Item = NonZeroChar>>(iter: T) -> Self {
                    iter.into_iter()
                        .map(NonZeroChar::get)
                        .collect()
                }
            }
            impl<'a> FromIterator<&'a NonZeroChar> for $ty {
                fn from_iter<T: IntoIterator<Item = &'a NonZeroChar>>(iter: T) -> Self {
                    iter.into_iter()
                        .copied()
                        .map(NonZeroChar::get)
                        .collect()
                }
            }
        )+
    };
}

/// Try from byte errors
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TryFromByteError(());
#[allow(deprecated)]
impl Display for TryFromByteError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.description().fmt(f)
    }
}
impl Error for TryFromByteError {
    fn description(&self) -> &str {
        "converted integer out of range for `NonZeroChar`"
    }
}

impl_froms! {
    u32,
    u64,
    u128,
    String,
}
impl_try_froms! {
    u8,
    u16,
}
impl_fromiters! {
    String,
    Box<str>,
    Cow<'_, str>,
}
impl TryFrom<u8> for NonZeroChar {
    type Error = TryFromByteError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        NonZeroChar::new(value.into())
            .ok_or(TryFromByteError(()))
    }
}
impl TryFrom<u32> for NonZeroChar {
    type Error = TryFromByteError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        match value.try_into() {
            Ok(ch) => {
                NonZeroChar::new(ch)
                    .ok_or(TryFromByteError(()))
            },
            Err(_) => Err(TryFromByteError(())),
        }
    }
}
impl Extend<NonZeroChar> for String {
    fn extend<T: IntoIterator<Item = NonZeroChar>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(NonZeroChar::get));
    }
}
impl<'a> Extend<&'a NonZeroChar> for String {
    fn extend<T: IntoIterator<Item = &'a NonZeroChar>>(&mut self, iter: T) {
        self.extend(iter.into_iter().copied().map(NonZeroChar::get));
    }
}
