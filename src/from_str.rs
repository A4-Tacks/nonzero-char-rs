#![allow(deprecated)]

use crate::NonZeroChar;
use core::char::ParseCharError;
use core::error::Error;
use core::fmt::{self, Display};
use core::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq)]
enum ParseNonZeroCharErrorInner {
    ParseCharError(ParseCharError),
    ByZeroError,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseNonZeroCharError {
    error: ParseNonZeroCharErrorInner,
}
impl From<ParseCharError> for ParseNonZeroCharError {
    fn from(v: ParseCharError) -> Self {
        ParseNonZeroCharErrorInner::ParseCharError(v).into()
    }
}
impl From<ParseNonZeroCharErrorInner> for ParseNonZeroCharError {
    fn from(error: ParseNonZeroCharErrorInner) -> Self {
        Self { error }
    }
}
impl Error for ParseNonZeroCharError {
    fn description(&self) -> &str {
        match &self.error {
            ParseNonZeroCharErrorInner::ParseCharError(e) => {
                e.description()
            },
            ParseNonZeroCharErrorInner::ByZeroError => {
                "parsed char by zero"
            },
        }
    }
}
impl Display for ParseNonZeroCharError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.description().fmt(f)
    }
}
impl FromStr for NonZeroChar {
    type Err = ParseNonZeroCharError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let ch = char::from_str(s)?;
        NonZeroChar::new(ch)
            .ok_or(ParseNonZeroCharErrorInner::ByZeroError.into())
    }
}
