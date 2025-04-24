#![no_std]
#![doc = include_str!("../README.md")]

extern crate alloc;

pub mod iter;
pub mod from_str;
pub mod convert;

use core::{
    char::*,
    cmp::Ordering,
    fmt::{self, Debug, Display},
    num::NonZeroU32,
};


#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NonZeroChar(NonZeroU32);

impl Debug for NonZeroChar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.get(), f)
    }
}
impl Display for NonZeroChar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.get(), f)
    }
}
impl PartialEq<char> for NonZeroChar {
    fn eq(&self, other: &char) -> bool {
        self.get() == *other
    }
}
impl PartialEq<NonZeroChar> for char {
    fn eq(&self, other: &NonZeroChar) -> bool {
        *self == other.get()
    }
}
impl PartialOrd<char> for NonZeroChar {
    fn partial_cmp(&self, other: &char) -> Option<Ordering> {
        self.get().partial_cmp(other)
    }

    fn lt(&self, other: &char) -> bool {
        self.get().lt(other)
    }

    fn le(&self, other: &char) -> bool {
        self.get().le(other)
    }

    fn gt(&self, other: &char) -> bool {
        self.get().gt(other)
    }

    fn ge(&self, other: &char) -> bool {
        self.get().ge(other)
    }
}
impl PartialOrd<NonZeroChar> for char {
    fn partial_cmp(&self, other: &NonZeroChar) -> Option<Ordering> {
        self.partial_cmp(&other.get())
    }

    fn lt(&self, other: &NonZeroChar) -> bool {
        self.lt(&other.get())
    }

    fn le(&self, other: &NonZeroChar) -> bool {
        self.le(&other.get())
    }

    fn gt(&self, other: &NonZeroChar) -> bool {
        self.gt(&other.get())
    }

    fn ge(&self, other: &NonZeroChar) -> bool {
        self.ge(&other.get())
    }
}

// The methods and documentation are sourced from
// [Rust](https://github.com/rust-lang/rust) STD.
// Some of the documentation and implement has been modified,
// and most of the methods have been directly forwarded to char
// Rust uses MIT+APACHE license
impl NonZeroChar {
    /// Creates a non-zero if the given value is not zero.
    ///
    /// # Examples
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert_eq!(NonZeroChar::new('a').map(NonZeroChar::get), Some('a'));
    /// assert_eq!(NonZeroChar::new('\0').map(NonZeroChar::get), None);
    /// ```
    pub const fn new(ch: char) -> Option<Self> {
        match NonZeroU32::new(ch as u32) {
            Some(ch) => Some(Self(ch)),
            None => None,
        }
    }

    /// Creates a non-zero without checking whether the value is non-zero. This results in
    /// undefined behavior if the value is zero.
    ///
    /// # Safety
    /// The value must not be zero ('\0').
    pub const unsafe fn new_unchecked(ch: char) -> Self {
        #[cfg(debug_assertions)]
        debug_assert!(Self::new(ch).is_some());
        unsafe {
            Self(NonZeroU32::new_unchecked(ch as u32))
        }
    }

    /// Returns the contained value as a primitive type.
    pub const fn get(self) -> char {
        // SAFETY: Assume on create this type
        unsafe { char::from_u32_unchecked(self.0.get()) }
    }

    /// Like `self..=max`
    ///
    /// # Examples
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let mut iter = NonZeroChar::new('a').unwrap()
    ///     .iter_inclusive(NonZeroChar::new('c').unwrap());
    /// assert_eq!(iter.next(), Some(NonZeroChar::new('a').unwrap()));
    /// assert_eq!(iter.next(), Some(NonZeroChar::new('b').unwrap()));
    /// assert_eq!(iter.next(), Some(NonZeroChar::new('c').unwrap()));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_inclusive(self, max: Self) -> iter::RangeInclusiveIter {
        let iter = self.get()..=max.get();
        iter::RangeInclusiveIter { iter: iter.into_iter() }
    }

    /// The lowest valid code point a [`NonZeroChar`] can have, `'\x01'`.
    ///
    /// Unlike integer types, `char` actually has a gap in the middle,
    /// meaning that the range of possible `char`s is smaller than you
    /// might expect. Ranges of `char` will automatically hop this gap
    /// for you:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let dist = u32::from(char::MAX) - u32::from(char::MIN);
    /// let size = (char::MIN..=char::MAX).count() as u32;
    /// assert!(size < dist);
    /// ```
    ///
    /// Despite this gap, the `MIN` and [`MAX`] values can be used as bounds for
    /// all `char` values.
    ///
    /// [`MAX`]: char::MAX
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// # fn something_which_returns_char() -> char { 'a' }
    /// let c: char = something_which_returns_char();
    /// assert!(char::MIN <= c);
    ///
    /// let value_at_min = u32::from(NonZeroChar::MIN);
    /// assert_eq!(char::from_u32(value_at_min), Some('\x01'));
    /// ```
    pub const MIN: Self = Self::new('\x01').unwrap();

    /// The highest valid code point a `char` can have, `'\u{10FFFF}'`.
    ///
    /// Unlike integer types, `char` actually has a gap in the middle,
    /// meaning that the range of possible `char`s is smaller than you
    /// might expect. Ranges of `char` will automatically hop this gap
    /// for you:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let dist = u32::from(NonZeroChar::MAX) - u32::from(NonZeroChar::MIN);
    /// let size = NonZeroChar::MIN.iter_inclusive(NonZeroChar::MAX).count() as u32;
    /// assert!(size < dist);
    /// ```
    ///
    /// Despite this gap, the [`MIN`] and `MAX` values can be used as bounds for
    /// all `char` values.
    ///
    /// [`MIN`]: NonZeroChar::MIN
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// # fn something_which_returns_char() -> char { 'a' }
    /// let c: char = something_which_returns_char();
    /// assert!(c <= char::MAX);
    ///
    /// let value_at_max = u32::from(NonZeroChar::MAX);
    /// assert_eq!(char::from_u32(value_at_max), Some('\u{10FFFF}'));
    /// assert_eq!(NonZeroChar::from_u32(value_at_max + 1), None);
    /// ```
    pub const MAX: Self = Self::new('\u{10FFFF}').unwrap();

    /// `U+FFFD REPLACEMENT CHARACTER` (�) is used in Unicode to represent a
    /// decoding error.
    ///
    /// It can occur, for example, when giving ill-formed UTF-8 bytes to
    /// [`String::from_utf8_lossy`](alloc::string::String::from_utf8_lossy).
    pub const REPLACEMENT_CHARACTER: Self = Self::new('\u{FFFD}').unwrap();

    /// The version of [Unicode](https://www.unicode.org/) that the Unicode parts of
    /// `char` and `str` methods are based on.
    ///
    /// New versions of Unicode are released regularly and subsequently all methods
    /// in the standard library depending on Unicode are updated. Therefore the
    /// behavior of some `char` and `str` methods and the value of this constant
    /// changes over time. This is *not* considered to be a breaking change.
    ///
    /// The version numbering scheme is explained in
    /// [Unicode 11.0 or later, Section 3.1 Versions of the Unicode Standard](https://www.unicode.org/versions/Unicode11.0.0/ch03.pdf#page=4).
    pub const UNICODE_VERSION: (u8, u8, u8) = char::UNICODE_VERSION;

    /// Creates an iterator over the native endian UTF-16 encoded code points in `iter`,
    /// returning unpaired surrogates as `Err`s.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = [
    ///     0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0xDD1E, 0x0069, 0x0063, 0xD834,
    /// ];
    ///
    /// assert_eq!(
    ///     char::decode_utf16(v)
    ///         .map(|r| r.map_err(|e| e.unpaired_surrogate()))
    ///         .collect::<Vec<_>>(),
    ///     vec![
    ///         Ok('𝄞'),
    ///         Ok('m'), Ok('u'), Ok('s'),
    ///         Err(0xDD1E),
    ///         Ok('i'), Ok('c'),
    ///         Err(0xD834)
    ///     ]
    /// );
    /// ```
    ///
    /// A lossy decoder can be obtained by replacing `Err` results with the replacement character:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = [
    ///     0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0xDD1E, 0x0069, 0x0063, 0xD834,
    /// ];
    ///
    /// assert_eq!(
    ///     char::decode_utf16(v)
    ///        .map(|r| r.unwrap_or(char::REPLACEMENT_CHARACTER))
    ///        .collect::<String>(),
    ///     "𝄞mus�ic�"
    /// );
    /// ```
    #[inline]
    pub fn decode_utf16<I: IntoIterator<Item = u16>>(iter: I) -> DecodeUtf16<I::IntoIter> {
        char::decode_utf16(iter)
    }

    /// Converts a `NonZeroChar` to a `NonZeroU32`
    ///
    /// # Examples
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// # use core::num::NonZeroU32;
    /// let ch = NonZeroChar::new('\x1b').unwrap();
    /// let num = NonZeroU32::new(0x1b).unwrap();
    /// assert_eq!(ch.as_nonzero_u32(), num);
    /// ```
    pub fn as_nonzero_u32(self) -> NonZeroU32 {
        self.0
    }

    /// Converts a `NonZeroChar` to a `u32`
    ///
    /// # Examples
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// # use core::num::NonZeroU32;
    /// let ch = NonZeroChar::new('\x1b').unwrap();
    /// assert_eq!(ch.as_u32(), 0x1b);
    /// ```
    pub fn as_u32(self) -> u32 {
        self.as_nonzero_u32().get()
    }

    /// Converts a `u32` to a `NonZeroChar`.
    ///
    /// Note that all `NonZeroChar`s are valid [`u32`]s,
    /// and can be cast to one with [`as_u32`](#method.as_u32):
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let c = '💯';
    /// let i = c as u32;
    ///
    /// assert_eq!(128175, i);
    /// ```
    ///
    /// However, the reverse is not true: not all valid [`u32`]s are valid
    /// `char`s. `from_u32()` will return `None` if the input is not a valid value
    /// for a `char`.
    ///
    /// For an unsafe version of this function which ignores these checks, see
    /// [`from_u32_unchecked`].
    ///
    /// [`from_u32_unchecked`]: #method.from_u32_unchecked
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let c = NonZeroChar::from_u32(0x2764);
    ///
    /// assert_eq!(Some(NonZeroChar::new('❤').unwrap()), c);
    /// ```
    ///
    /// Returning `None` when the input is not a valid `char`:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let c = NonZeroChar::from_u32(0x110000);
    ///
    /// assert_eq!(None, c);
    /// ```
    ///
    /// Returning `None` when the input by zero:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let c = NonZeroChar::from_u32(0);
    ///
    /// assert_eq!(None, c);
    /// ```
    #[must_use]
    #[inline]
    pub const fn from_u32(i: u32) -> Option<Self> {
        match char::from_u32(i) {
            Some(ch) => Self::new(ch),
            None => None,
        }
    }

    /// Converts a `u32` to a `char`, ignoring validity.
    ///
    /// Note that all `char`s are valid [`u32`]s, and can be cast to one with
    /// `as`:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let c = '💯';
    /// let i = c as u32;
    ///
    /// assert_eq!(128175, i);
    /// ```
    ///
    /// However, the reverse is not true: not all valid [`u32`]s are valid
    /// `char`s. `from_u32_unchecked()` will ignore this, and blindly cast to
    /// `char`, possibly creating an invalid one.
    ///
    /// # Safety
    ///
    /// This function is unsafe, as it may construct invalid `char` values.
    ///
    /// For a safe version of this function, see the [`from_u32`] function.
    ///
    /// [`from_u32`]: #method.from_u32
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let c = unsafe { NonZeroChar::from_u32_unchecked(0x2764) };
    ///
    /// assert_eq!(NonZeroChar::new('❤').unwrap(), c);
    /// ```
    #[must_use]
    #[inline]
    pub const unsafe fn from_u32_unchecked(i: u32) -> Self {
        unsafe {
            Self(NonZeroU32::new_unchecked(i))
        }
    }

    /// Converts a digit in the given radix to a `char`.
    ///
    /// A 'radix' here is sometimes also called a 'base'. A radix of two
    /// indicates a binary number, a radix of ten, decimal, and a radix of
    /// sixteen, hexadecimal, to give some common values. Arbitrary
    /// radices are supported.
    ///
    /// `from_digit()` will return `None` if the input is not a digit in
    /// the given radix.
    ///
    /// # Panics
    ///
    /// Panics if given a radix larger than 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let c = NonZeroChar::from_digit(4, 10);
    /// let d = NonZeroChar::new('4').unwrap();
    ///
    /// assert_eq!(Some(d), c);
    ///
    /// // Decimal 11 is a single digit in base 16
    /// let c = NonZeroChar::from_digit(11, 16);
    /// let d = NonZeroChar::new('b').unwrap();
    ///
    /// assert_eq!(Some(d), c);
    /// ```
    ///
    /// Returning `None` when the input is not a digit:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let c = NonZeroChar::from_digit(20, 10);
    ///
    /// assert_eq!(None, c);
    /// ```
    ///
    /// Passing a large radix, causing a panic:
    ///
    /// ```should_panic
    /// # use nonzero_char::NonZeroChar;
    /// // this panics
    /// let _c = NonZeroChar::from_digit(1, 37);
    /// ```
    #[must_use]
    #[inline]
    pub const fn from_digit(num: u32, radix: u32) -> Option<Self> {
        match char::from_digit(num, radix) {
            Some(ch) => {
                // SAFETY: Digit != '\0'
                unsafe { Some(Self::new_unchecked(ch)) }
            },
            None => None,
        }
    }

    /// Checks if a `char` is a digit in the given radix.
    ///
    /// A 'radix' here is sometimes also called a 'base'. A radix of two
    /// indicates a binary number, a radix of ten, decimal, and a radix of
    /// sixteen, hexadecimal, to give some common values. Arbitrary
    /// radices are supported.
    ///
    /// Compared to [`is_numeric()`], this function only recognizes the characters
    /// `0-9`, `a-z` and `A-Z`.
    ///
    /// 'Digit' is defined to be only the following characters:
    ///
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// For a more comprehensive understanding of 'digit', see [`is_numeric()`].
    ///
    /// [`is_numeric()`]: #method.is_numeric
    ///
    /// # Panics
    ///
    /// Panics if given a radix smaller than 2 or larger than 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert!('1'.is_digit(10));
    /// assert!('f'.is_digit(16));
    /// assert!(!'f'.is_digit(10));
    /// ```
    ///
    /// Passing a large radix, causing a panic:
    ///
    /// ```should_panic
    /// # use nonzero_char::NonZeroChar;
    /// // this panics
    /// '1'.is_digit(37);
    /// ```
    ///
    /// Passing a small radix, causing a panic:
    ///
    /// ```should_panic
    /// # use nonzero_char::NonZeroChar;
    /// // this panics
    /// '1'.is_digit(1);
    /// ```
    #[inline]
    pub fn is_digit(self, radix: u32) -> bool {
        self.get().is_digit(radix)
    }

    /// Converts a `char` to a digit in the given radix.
    ///
    /// A 'radix' here is sometimes also called a 'base'. A radix of two
    /// indicates a binary number, a radix of ten, decimal, and a radix of
    /// sixteen, hexadecimal, to give some common values. Arbitrary
    /// radices are supported.
    ///
    /// 'Digit' is defined to be only the following characters:
    ///
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// # Errors
    ///
    /// Returns `None` if the `char` does not refer to a digit in the given radix.
    ///
    /// # Panics
    ///
    /// Panics if given a radix smaller than 2 or larger than 36.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert_eq!('1'.to_digit(10), Some(1));
    /// assert_eq!('f'.to_digit(16), Some(15));
    /// ```
    ///
    /// Passing a non-digit results in failure:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert_eq!('f'.to_digit(10), None);
    /// assert_eq!('z'.to_digit(16), None);
    /// ```
    ///
    /// Passing a large radix, causing a panic:
    ///
    /// ```should_panic
    /// # use nonzero_char::NonZeroChar;
    /// // this panics
    /// let _ = '1'.to_digit(37);
    /// ```
    /// Passing a small radix, causing a panic:
    ///
    /// ```should_panic
    /// # use nonzero_char::NonZeroChar;
    /// // this panics
    /// let _ = '1'.to_digit(1);
    /// ```
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[inline]
    pub const fn to_digit(self, radix: u32) -> Option<u32> {
        self.get().to_digit(radix)
    }

    /// Returns an iterator that yields the hexadecimal Unicode escape of a
    /// character as `char`s.
    ///
    /// This will escape characters with the Rust syntax of the form
    /// `\u{NNNNNN}` where `NNNNNN` is a hexadecimal representation.
    ///
    /// # Examples
    ///
    /// As an iterator:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// for c in '❤'.escape_unicode() {
    ///     print!("{c}");
    /// }
    /// println!();
    /// ```
    ///
    /// Using `println!` directly:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("{}", '❤'.escape_unicode());
    /// ```
    ///
    /// Both are equivalent to:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("\\u{{2764}}");
    /// ```
    ///
    /// Using [`to_string`](../std/string/trait.ToString.html#tymethod.to_string):
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert_eq!('❤'.escape_unicode().to_string(), "\\u{2764}");
    /// ```
    #[must_use = "this returns the escaped char as an iterator, \
                  without modifying the original"]
    #[inline]
    pub fn escape_unicode(self) -> EscapeUnicode {
        self.get().escape_unicode()
    }

    /// Returns an iterator that yields the literal escape code of a character
    /// as `char`s.
    ///
    /// This will escape the characters similar to the [`Debug`] implementations
    /// of `str` or `char`.
    ///
    /// # Examples
    ///
    /// As an iterator:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// for c in '\n'.escape_debug() {
    ///     print!("{c}");
    /// }
    /// println!();
    /// ```
    ///
    /// Using `println!` directly:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("{}", '\n'.escape_debug());
    /// ```
    ///
    /// Both are equivalent to:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("\\n");
    /// ```
    ///
    /// Using [`to_string`](../std/string/trait.ToString.html#tymethod.to_string):
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert_eq!('\n'.escape_debug().to_string(), "\\n");
    /// ```
    #[must_use = "this returns the escaped char as an iterator, \
                  without modifying the original"]
    #[inline]
    pub fn escape_debug(self) -> EscapeDebug {
        self.get().escape_debug()
    }

    /// Returns an iterator that yields the literal escape code of a character
    /// as `char`s.
    ///
    /// The default is chosen with a bias toward producing literals that are
    /// legal in a variety of languages, including C++11 and similar C-family
    /// languages. The exact rules are:
    ///
    /// * Tab is escaped as `\t`.
    /// * Carriage return is escaped as `\r`.
    /// * Line feed is escaped as `\n`.
    /// * Single quote is escaped as `\'`.
    /// * Double quote is escaped as `\"`.
    /// * Backslash is escaped as `\\`.
    /// * Any character in the 'printable ASCII' range `0x20` .. `0x7e`
    ///   inclusive is not escaped.
    /// * All other characters are given hexadecimal Unicode escapes; see
    ///   [`escape_unicode`].
    ///
    /// [`escape_unicode`]: #method.escape_unicode
    ///
    /// # Examples
    ///
    /// As an iterator:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// for c in '"'.escape_default() {
    ///     print!("{c}");
    /// }
    /// println!();
    /// ```
    ///
    /// Using `println!` directly:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("{}", '"'.escape_default());
    /// ```
    ///
    /// Both are equivalent to:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("\\\"");
    /// ```
    ///
    /// Using [`to_string`](../std/string/trait.ToString.html#tymethod.to_string):
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert_eq!('"'.escape_default().to_string(), "\\\"");
    /// ```
    #[must_use = "this returns the escaped char as an iterator, \
                  without modifying the original"]
    #[inline]
    pub fn escape_default(self) -> EscapeDefault {
        self.get().escape_default()
    }

    /// Returns the number of bytes this `char` would need if encoded in UTF-8.
    ///
    /// That number of bytes is always between 1 and 4, inclusive.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let len = 'A'.len_utf8();
    /// assert_eq!(len, 1);
    ///
    /// let len = 'ß'.len_utf8();
    /// assert_eq!(len, 2);
    ///
    /// let len = 'ℝ'.len_utf8();
    /// assert_eq!(len, 3);
    ///
    /// let len = '💣'.len_utf8();
    /// assert_eq!(len, 4);
    /// ```
    ///
    /// The `&str` type guarantees that its contents are UTF-8, and so we can compare the length it
    /// would take if each code point was represented as a `char` vs in the `&str` itself:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// // as chars
    /// let eastern = '東';
    /// let capital = '京';
    ///
    /// // both can be represented as three bytes
    /// assert_eq!(3, eastern.len_utf8());
    /// assert_eq!(3, capital.len_utf8());
    ///
    /// // as a &str, these two are encoded in UTF-8
    /// let tokyo = "東京";
    ///
    /// let len = eastern.len_utf8() + capital.len_utf8();
    ///
    /// // we can see that they take six bytes total...
    /// assert_eq!(6, tokyo.len());
    ///
    /// // ... just like the &str
    /// assert_eq!(len, tokyo.len());
    /// ```
    #[inline]
    #[must_use]
    pub const fn len_utf8(self) -> usize {
        self.get().len_utf8()
    }

    /// Returns the number of 16-bit code units this `char` would need if
    /// encoded in UTF-16.
    ///
    /// That number of code units is always either 1 or 2, for unicode scalar values in
    /// the [basic multilingual plane] or [supplementary planes] respectively.
    ///
    /// See the documentation for [`len_utf8()`] for more explanation of this
    /// concept. This function is a mirror, but for UTF-16 instead of UTF-8.
    ///
    /// [basic multilingual plane]: http://www.unicode.org/glossary/#basic_multilingual_plane
    /// [supplementary planes]: http://www.unicode.org/glossary/#supplementary_planes
    /// [`len_utf8()`]: #method.len_utf8
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let n = 'ß'.len_utf16();
    /// assert_eq!(n, 1);
    ///
    /// let len = '💣'.len_utf16();
    /// assert_eq!(len, 2);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len_utf16(self) -> usize {
        self.get().len_utf16()
    }

    /// Encodes this character as UTF-8 into the provided byte buffer,
    /// and then returns the subslice of the buffer that contains the encoded character.
    ///
    /// # Panics
    ///
    /// Panics if the buffer is not large enough.
    /// A buffer of length four is large enough to encode any `char`.
    ///
    /// # Examples
    ///
    /// In both of these examples, 'ß' takes two bytes to encode.
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let mut b = [0; 2];
    ///
    /// let result = 'ß'.encode_utf8(&mut b);
    ///
    /// assert_eq!(result, "ß");
    ///
    /// assert_eq!(result.len(), 2);
    /// ```
    ///
    /// A buffer that's too small:
    ///
    /// ```should_panic
    /// # use nonzero_char::NonZeroChar;
    /// let mut b = [0; 1];
    ///
    /// // this panics
    /// 'ß'.encode_utf8(&mut b);
    /// ```
    #[inline]
    pub const fn encode_utf8(self, dst: &mut [u8]) -> &mut str {
        self.get().encode_utf8(dst)
    }

    /// Encodes this character as native endian UTF-16 into the provided `u16` buffer,
    /// and then returns the subslice of the buffer that contains the encoded character.
    ///
    /// # Panics
    ///
    /// Panics if the buffer is not large enough.
    /// A buffer of length 2 is large enough to encode any `char`.
    ///
    /// # Examples
    ///
    /// In both of these examples, '𝕊' takes two `u16`s to encode.
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let mut b = [0; 2];
    ///
    /// let result = '𝕊'.encode_utf16(&mut b);
    ///
    /// assert_eq!(result.len(), 2);
    /// ```
    ///
    /// A buffer that's too small:
    ///
    /// ```should_panic
    /// # use nonzero_char::NonZeroChar;
    /// let mut b = [0; 1];
    ///
    /// // this panics
    /// '𝕊'.encode_utf16(&mut b);
    /// ```
    #[inline]
    pub const fn encode_utf16(self, dst: &mut [u16]) -> &mut [u16] {
        self.get().encode_utf16(dst)
    }

    /// Returns `true` if this `char` has the `Alphabetic` property.
    ///
    /// `Alphabetic` is described in Chapter 4 (Character Properties) of the [Unicode Standard] and
    /// specified in the [Unicode Character Database][ucd] [`DerivedCoreProperties.txt`].
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`DerivedCoreProperties.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert!('a'.is_alphabetic());
    /// assert!('京'.is_alphabetic());
    ///
    /// let c = '💝';
    /// // love is many things, but it is not alphabetic
    /// assert!(!c.is_alphabetic());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_alphabetic(self) -> bool {
        self.get().is_alphabetic()
    }

    /// Returns `true` if this `char` has the `Lowercase` property.
    ///
    /// `Lowercase` is described in Chapter 4 (Character Properties) of the [Unicode Standard] and
    /// specified in the [Unicode Character Database][ucd] [`DerivedCoreProperties.txt`].
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`DerivedCoreProperties.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert!('a'.is_lowercase());
    /// assert!('δ'.is_lowercase());
    /// assert!(!'A'.is_lowercase());
    /// assert!(!'Δ'.is_lowercase());
    ///
    /// // The various Chinese scripts and punctuation do not have case, and so:
    /// assert!(!'中'.is_lowercase());
    /// assert!(!' '.is_lowercase());
    /// ```
    ///
    /// In a const context:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// const CAPITAL_DELTA_IS_LOWERCASE: bool = 'Δ'.is_lowercase();
    /// assert!(!CAPITAL_DELTA_IS_LOWERCASE);
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_lowercase(self) -> bool {
        self.get().is_lowercase()
    }

    /// Returns `true` if this `char` has the `Uppercase` property.
    ///
    /// `Uppercase` is described in Chapter 4 (Character Properties) of the [Unicode Standard] and
    /// specified in the [Unicode Character Database][ucd] [`DerivedCoreProperties.txt`].
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`DerivedCoreProperties.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/DerivedCoreProperties.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert!(!'a'.is_uppercase());
    /// assert!(!'δ'.is_uppercase());
    /// assert!('A'.is_uppercase());
    /// assert!('Δ'.is_uppercase());
    ///
    /// // The various Chinese scripts and punctuation do not have case, and so:
    /// assert!(!'中'.is_uppercase());
    /// assert!(!' '.is_uppercase());
    /// ```
    ///
    /// In a const context:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// const CAPITAL_DELTA_IS_UPPERCASE: bool = 'Δ'.is_uppercase();
    /// assert!(CAPITAL_DELTA_IS_UPPERCASE);
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_uppercase(self) -> bool {
        self.get().is_uppercase()
    }

    /// Returns `true` if this `char` has the `White_Space` property.
    ///
    /// `White_Space` is specified in the [Unicode Character Database][ucd] [`PropList.txt`].
    ///
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`PropList.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/PropList.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert!(' '.is_whitespace());
    ///
    /// // line break
    /// assert!('\n'.is_whitespace());
    ///
    /// // a non-breaking space
    /// assert!('\u{A0}'.is_whitespace());
    ///
    /// assert!(!'越'.is_whitespace());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_whitespace(self) -> bool {
        self.get().is_whitespace()
    }

    /// Returns `true` if this `char` satisfies either [`is_alphabetic()`] or [`is_numeric()`].
    ///
    /// [`is_alphabetic()`]: #method.is_alphabetic
    /// [`is_numeric()`]: #method.is_numeric
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert!('٣'.is_alphanumeric());
    /// assert!('7'.is_alphanumeric());
    /// assert!('৬'.is_alphanumeric());
    /// assert!('¾'.is_alphanumeric());
    /// assert!('①'.is_alphanumeric());
    /// assert!('K'.is_alphanumeric());
    /// assert!('و'.is_alphanumeric());
    /// assert!('藏'.is_alphanumeric());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_alphanumeric(self) -> bool {
        self.get().is_alphanumeric()
    }

    /// Returns `true` if this `char` has the general category for control codes.
    ///
    /// Control codes (code points with the general category of `Cc`) are described in Chapter 4
    /// (Character Properties) of the [Unicode Standard] and specified in the [Unicode Character
    /// Database][ucd] [`UnicodeData.txt`].
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`UnicodeData.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// // U+009C, STRING TERMINATOR
    /// assert!(''.is_control());
    /// assert!(!'q'.is_control());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_control(self) -> bool {
        self.get().is_control()
    }

    /// Returns `true` if this `char` has one of the general categories for numbers.
    ///
    /// The general categories for numbers (`Nd` for decimal digits, `Nl` for letter-like numeric
    /// characters, and `No` for other numeric characters) are specified in the [Unicode Character
    /// Database][ucd] [`UnicodeData.txt`].
    ///
    /// This method doesn't cover everything that could be considered a number, e.g. ideographic numbers like '三'.
    /// If you want everything including characters with overlapping purposes then you might want to use
    /// a unicode or language-processing library that exposes the appropriate character properties instead
    /// of looking at the unicode categories.
    ///
    /// If you want to parse ASCII decimal digits (0-9) or ASCII base-N, use
    /// `is_ascii_digit` or `is_digit` instead.
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`UnicodeData.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert!('٣'.is_numeric());
    /// assert!('7'.is_numeric());
    /// assert!('৬'.is_numeric());
    /// assert!('¾'.is_numeric());
    /// assert!('①'.is_numeric());
    /// assert!(!'K'.is_numeric());
    /// assert!(!'و'.is_numeric());
    /// assert!(!'藏'.is_numeric());
    /// assert!(!'三'.is_numeric());
    /// ```
    #[must_use]
    #[inline]
    pub fn is_numeric(self) -> bool {
        self.get().is_numeric()
    }

    /// Returns an iterator that yields the lowercase mapping of this `char` as one or more
    /// `char`s.
    ///
    /// If this `char` does not have a lowercase mapping, the iterator yields the same `char`.
    ///
    /// If this `char` has a one-to-one lowercase mapping given by the [Unicode Character
    /// Database][ucd] [`UnicodeData.txt`], the iterator yields that `char`.
    ///
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`UnicodeData.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt
    ///
    /// If this `char` requires special considerations (e.g. multiple `char`s) the iterator yields
    /// the `char`(s) given by [`SpecialCasing.txt`].
    ///
    /// [`SpecialCasing.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/SpecialCasing.txt
    ///
    /// This operation performs an unconditional mapping without tailoring. That is, the conversion
    /// is independent of context and language.
    ///
    /// In the [Unicode Standard], Chapter 4 (Character Properties) discusses case mapping in
    /// general and Chapter 3 (Conformance) discusses the default algorithm for case conversion.
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    ///
    /// # Examples
    ///
    /// As an iterator:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// for c in 'İ'.to_lowercase() {
    ///     print!("{c}");
    /// }
    /// println!();
    /// ```
    ///
    /// Using `println!` directly:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("{}", 'İ'.to_lowercase());
    /// ```
    ///
    /// Both are equivalent to:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("i\u{307}");
    /// ```
    ///
    /// Using [`to_string`](../std/string/trait.ToString.html#tymethod.to_string):
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert_eq!('C'.to_lowercase().to_string(), "c");
    ///
    /// // Sometimes the result is more than one character:
    /// assert_eq!('İ'.to_lowercase().to_string(), "i\u{307}");
    ///
    /// // Characters that do not have both uppercase and lowercase
    /// // convert into themselves.
    /// assert_eq!('山'.to_lowercase().to_string(), "山");
    /// ```
    #[must_use = "this returns the lowercase character as a new iterator, \
                  without modifying the original"]
    #[inline]
    pub fn to_lowercase(self) -> ToLowercase {
        self.get().to_lowercase()
    }

    /// Returns an iterator that yields the uppercase mapping of this `char` as one or more
    /// `char`s.
    ///
    /// If this `char` does not have an uppercase mapping, the iterator yields the same `char`.
    ///
    /// If this `char` has a one-to-one uppercase mapping given by the [Unicode Character
    /// Database][ucd] [`UnicodeData.txt`], the iterator yields that `char`.
    ///
    /// [ucd]: https://www.unicode.org/reports/tr44/
    /// [`UnicodeData.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/UnicodeData.txt
    ///
    /// If this `char` requires special considerations (e.g. multiple `char`s) the iterator yields
    /// the `char`(s) given by [`SpecialCasing.txt`].
    ///
    /// [`SpecialCasing.txt`]: https://www.unicode.org/Public/UCD/latest/ucd/SpecialCasing.txt
    ///
    /// This operation performs an unconditional mapping without tailoring. That is, the conversion
    /// is independent of context and language.
    ///
    /// In the [Unicode Standard], Chapter 4 (Character Properties) discusses case mapping in
    /// general and Chapter 3 (Conformance) discusses the default algorithm for case conversion.
    ///
    /// [Unicode Standard]: https://www.unicode.org/versions/latest/
    ///
    /// # Examples
    ///
    /// As an iterator:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// for c in 'ß'.to_uppercase() {
    ///     print!("{c}");
    /// }
    /// println!();
    /// ```
    ///
    /// Using `println!` directly:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("{}", 'ß'.to_uppercase());
    /// ```
    ///
    /// Both are equivalent to:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// println!("SS");
    /// ```
    ///
    /// Using [`to_string`](../std/string/trait.ToString.html#tymethod.to_string):
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// assert_eq!('c'.to_uppercase().to_string(), "C");
    ///
    /// // Sometimes the result is more than one character:
    /// assert_eq!('ß'.to_uppercase().to_string(), "SS");
    ///
    /// // Characters that do not have both uppercase and lowercase
    /// // convert into themselves.
    /// assert_eq!('山'.to_uppercase().to_string(), "山");
    /// ```
    ///
    /// # Note on locale
    ///
    /// In Turkish, the equivalent of 'i' in Latin has five forms instead of two:
    ///
    /// * 'Dotless': I / ı, sometimes written ï
    /// * 'Dotted': İ / i
    ///
    /// Note that the lowercase dotted 'i' is the same as the Latin. Therefore:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let upper_i = 'i'.to_uppercase().to_string();
    /// ```
    ///
    /// The value of `upper_i` here relies on the language of the text: if we're
    /// in `en-US`, it should be `"I"`, but if we're in `tr_TR`, it should
    /// be `"İ"`. `to_uppercase()` does not take this into account, and so:
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let upper_i = 'i'.to_uppercase().to_string();
    ///
    /// assert_eq!(upper_i, "I");
    /// ```
    ///
    /// holds across languages.
    #[must_use = "this returns the uppercase character as a new iterator, \
                  without modifying the original"]
    #[inline]
    pub fn to_uppercase(self) -> ToUppercase {
        self.get().to_uppercase()
    }

    /// Checks if the value is within the ASCII range.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let ascii = 'a';
    /// let non_ascii = '❤';
    ///
    /// assert!(ascii.is_ascii());
    /// assert!(!non_ascii.is_ascii());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii(&self) -> bool {
        self.get().is_ascii()
    }

    /// Makes a copy of the value in its ASCII upper case equivalent.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To uppercase the value in-place, use [`make_ascii_uppercase()`].
    ///
    /// To uppercase ASCII characters in addition to non-ASCII characters, use
    /// [`to_uppercase()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let ascii = 'a';
    /// let non_ascii = '❤';
    ///
    /// assert_eq!('A', ascii.to_ascii_uppercase());
    /// assert_eq!('❤', non_ascii.to_ascii_uppercase());
    /// ```
    ///
    /// [`make_ascii_uppercase()`]: #method.make_ascii_uppercase
    /// [`to_uppercase()`]: #method.to_uppercase
    #[must_use = "to uppercase the value in-place, use `make_ascii_uppercase()`"]
    #[inline]
    pub const fn to_ascii_uppercase(&self) -> Self {
        let ch = self.get().to_ascii_uppercase();
        // SAFETY: only '\0'.to_ascii_uppercase() is '\0'
        unsafe { Self::new_unchecked(ch) }
    }

    /// Makes a copy of the value in its ASCII lower case equivalent.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To lowercase the value in-place, use [`make_ascii_lowercase()`].
    ///
    /// To lowercase ASCII characters in addition to non-ASCII characters, use
    /// [`to_lowercase()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let ascii = 'A';
    /// let non_ascii = '❤';
    ///
    /// assert_eq!('a', ascii.to_ascii_lowercase());
    /// assert_eq!('❤', non_ascii.to_ascii_lowercase());
    /// ```
    ///
    /// [`make_ascii_lowercase()`]: #method.make_ascii_lowercase
    /// [`to_lowercase()`]: #method.to_lowercase
    #[must_use = "to lowercase the value in-place, use `make_ascii_lowercase()`"]
    #[inline]
    pub const fn to_ascii_lowercase(&self) -> Self {
        let ch = self.get().to_ascii_lowercase();
        // SAFETY: only '\0'.to_ascii_lowercase() is '\0'
        unsafe { Self::new_unchecked(ch) }
    }

    /// Checks that two values are an ASCII case-insensitive match.
    ///
    /// Equivalent to <code>[to_ascii_lowercase]\(a) == [to_ascii_lowercase]\(b)</code>.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let upper_a = 'A';
    /// let lower_a = 'a';
    /// let lower_z = 'z';
    ///
    /// assert!(upper_a.eq_ignore_ascii_case(&lower_a));
    /// assert!(upper_a.eq_ignore_ascii_case(&upper_a));
    /// assert!(!upper_a.eq_ignore_ascii_case(&lower_z));
    /// ```
    ///
    /// [to_ascii_lowercase]: #method.to_ascii_lowercase
    #[inline]
    pub const fn eq_ignore_ascii_case(&self, other: &char) -> bool {
        self.get().eq_ignore_ascii_case(other)
    }

    /// Converts this type to its ASCII upper case equivalent in-place.
    ///
    /// ASCII letters 'a' to 'z' are mapped to 'A' to 'Z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new uppercased value without modifying the existing one, use
    /// [`to_ascii_uppercase()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let mut ascii = 'a';
    ///
    /// ascii.make_ascii_uppercase();
    ///
    /// assert_eq!('A', ascii);
    /// ```
    ///
    /// [`to_ascii_uppercase()`]: #method.to_ascii_uppercase
    #[inline]
    pub const fn make_ascii_uppercase(&mut self) {
        let mut ch = self.get();
        ch.make_ascii_uppercase();
        // SAFETY: only '\0' upper is '\0'
        *self = unsafe { Self::new_unchecked(ch) }
    }

    /// Converts this type to its ASCII lower case equivalent in-place.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z',
    /// but non-ASCII letters are unchanged.
    ///
    /// To return a new lowercased value without modifying the existing one, use
    /// [`to_ascii_lowercase()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let mut ascii = 'A';
    ///
    /// ascii.make_ascii_lowercase();
    ///
    /// assert_eq!('a', ascii);
    /// ```
    ///
    /// [`to_ascii_lowercase()`]: #method.to_ascii_lowercase
    #[inline]
    pub const fn make_ascii_lowercase(&mut self) {
        let mut ch = self.get();
        ch.make_ascii_lowercase();
        // SAFETY: only '\0' lower is '\0'
        *self = unsafe { Self::new_unchecked(ch) }
    }

    /// Checks if the value is an ASCII alphabetic character:
    ///
    /// - U+0041 'A' ..= U+005A 'Z', or
    /// - U+0061 'a' ..= U+007A 'z'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_alphabetic());
    /// assert!(uppercase_g.is_ascii_alphabetic());
    /// assert!(a.is_ascii_alphabetic());
    /// assert!(g.is_ascii_alphabetic());
    /// assert!(!zero.is_ascii_alphabetic());
    /// assert!(!percent.is_ascii_alphabetic());
    /// assert!(!space.is_ascii_alphabetic());
    /// assert!(!lf.is_ascii_alphabetic());
    /// assert!(!esc.is_ascii_alphabetic());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_alphabetic(&self) -> bool {
        self.get().is_ascii_alphabetic()
    }

    /// Checks if the value is an ASCII uppercase character:
    /// U+0041 'A' ..= U+005A 'Z'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_uppercase());
    /// assert!(uppercase_g.is_ascii_uppercase());
    /// assert!(!a.is_ascii_uppercase());
    /// assert!(!g.is_ascii_uppercase());
    /// assert!(!zero.is_ascii_uppercase());
    /// assert!(!percent.is_ascii_uppercase());
    /// assert!(!space.is_ascii_uppercase());
    /// assert!(!lf.is_ascii_uppercase());
    /// assert!(!esc.is_ascii_uppercase());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_uppercase(&self) -> bool {
        self.get().is_ascii_uppercase()
    }

    /// Checks if the value is an ASCII lowercase character:
    /// U+0061 'a' ..= U+007A 'z'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_lowercase());
    /// assert!(!uppercase_g.is_ascii_lowercase());
    /// assert!(a.is_ascii_lowercase());
    /// assert!(g.is_ascii_lowercase());
    /// assert!(!zero.is_ascii_lowercase());
    /// assert!(!percent.is_ascii_lowercase());
    /// assert!(!space.is_ascii_lowercase());
    /// assert!(!lf.is_ascii_lowercase());
    /// assert!(!esc.is_ascii_lowercase());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_lowercase(&self) -> bool {
        self.get().is_ascii_lowercase()
    }

    /// Checks if the value is an ASCII alphanumeric character:
    ///
    /// - U+0041 'A' ..= U+005A 'Z', or
    /// - U+0061 'a' ..= U+007A 'z', or
    /// - U+0030 '0' ..= U+0039 '9'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_alphanumeric());
    /// assert!(uppercase_g.is_ascii_alphanumeric());
    /// assert!(a.is_ascii_alphanumeric());
    /// assert!(g.is_ascii_alphanumeric());
    /// assert!(zero.is_ascii_alphanumeric());
    /// assert!(!percent.is_ascii_alphanumeric());
    /// assert!(!space.is_ascii_alphanumeric());
    /// assert!(!lf.is_ascii_alphanumeric());
    /// assert!(!esc.is_ascii_alphanumeric());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_alphanumeric(&self) -> bool {
        self.get().is_ascii_alphanumeric()
    }

    /// Checks if the value is an ASCII decimal digit:
    /// U+0030 '0' ..= U+0039 '9'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_digit());
    /// assert!(!uppercase_g.is_ascii_digit());
    /// assert!(!a.is_ascii_digit());
    /// assert!(!g.is_ascii_digit());
    /// assert!(zero.is_ascii_digit());
    /// assert!(!percent.is_ascii_digit());
    /// assert!(!space.is_ascii_digit());
    /// assert!(!lf.is_ascii_digit());
    /// assert!(!esc.is_ascii_digit());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_digit(&self) -> bool {
        self.get().is_ascii_digit()
    }

    /// Checks if the value is an ASCII hexadecimal digit:
    ///
    /// - U+0030 '0' ..= U+0039 '9', or
    /// - U+0041 'A' ..= U+0046 'F', or
    /// - U+0061 'a' ..= U+0066 'f'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_hexdigit());
    /// assert!(!uppercase_g.is_ascii_hexdigit());
    /// assert!(a.is_ascii_hexdigit());
    /// assert!(!g.is_ascii_hexdigit());
    /// assert!(zero.is_ascii_hexdigit());
    /// assert!(!percent.is_ascii_hexdigit());
    /// assert!(!space.is_ascii_hexdigit());
    /// assert!(!lf.is_ascii_hexdigit());
    /// assert!(!esc.is_ascii_hexdigit());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_hexdigit(&self) -> bool {
        self.get().is_ascii_hexdigit()
    }

    /// Checks if the value is an ASCII punctuation character:
    ///
    /// - U+0021 ..= U+002F `! " # $ % & ' ( ) * + , - . /`, or
    /// - U+003A ..= U+0040 `: ; < = > ? @`, or
    /// - U+005B ..= U+0060 ``[ \ ] ^ _ ` ``, or
    /// - U+007B ..= U+007E `{ | } ~`
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_punctuation());
    /// assert!(!uppercase_g.is_ascii_punctuation());
    /// assert!(!a.is_ascii_punctuation());
    /// assert!(!g.is_ascii_punctuation());
    /// assert!(!zero.is_ascii_punctuation());
    /// assert!(percent.is_ascii_punctuation());
    /// assert!(!space.is_ascii_punctuation());
    /// assert!(!lf.is_ascii_punctuation());
    /// assert!(!esc.is_ascii_punctuation());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_punctuation(&self) -> bool {
        self.get().is_ascii_punctuation()
    }

    /// Checks if the value is an ASCII graphic character:
    /// U+0021 '!' ..= U+007E '~'.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(uppercase_a.is_ascii_graphic());
    /// assert!(uppercase_g.is_ascii_graphic());
    /// assert!(a.is_ascii_graphic());
    /// assert!(g.is_ascii_graphic());
    /// assert!(zero.is_ascii_graphic());
    /// assert!(percent.is_ascii_graphic());
    /// assert!(!space.is_ascii_graphic());
    /// assert!(!lf.is_ascii_graphic());
    /// assert!(!esc.is_ascii_graphic());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_graphic(&self) -> bool {
        self.get().is_ascii_graphic()
    }

    /// Checks if the value is an ASCII whitespace character:
    /// U+0020 SPACE, U+0009 HORIZONTAL TAB, U+000A LINE FEED,
    /// U+000C FORM FEED, or U+000D CARRIAGE RETURN.
    ///
    /// Rust uses the WhatWG Infra Standard's [definition of ASCII
    /// whitespace][infra-aw]. There are several other definitions in
    /// wide use. For instance, [the POSIX locale][pct] includes
    /// U+000B VERTICAL TAB as well as all the above characters,
    /// but—from the very same specification—[the default rule for
    /// "field splitting" in the Bourne shell][bfs] considers *only*
    /// SPACE, HORIZONTAL TAB, and LINE FEED as whitespace.
    ///
    /// If you are writing a program that will process an existing
    /// file format, check what that format's definition of whitespace is
    /// before using this function.
    ///
    /// [infra-aw]: https://infra.spec.whatwg.org/#ascii-whitespace
    /// [pct]: https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap07.html#tag_07_03_01
    /// [bfs]: https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_06_05
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_whitespace());
    /// assert!(!uppercase_g.is_ascii_whitespace());
    /// assert!(!a.is_ascii_whitespace());
    /// assert!(!g.is_ascii_whitespace());
    /// assert!(!zero.is_ascii_whitespace());
    /// assert!(!percent.is_ascii_whitespace());
    /// assert!(space.is_ascii_whitespace());
    /// assert!(lf.is_ascii_whitespace());
    /// assert!(!esc.is_ascii_whitespace());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_whitespace(&self) -> bool {
        self.get().is_ascii_whitespace()
    }

    /// Checks if the value is an ASCII control character:
    /// U+0000 NUL ..= U+001F UNIT SEPARATOR, or U+007F DELETE.
    /// Note that most ASCII whitespace characters are control
    /// characters, but SPACE is not.
    ///
    /// # Examples
    ///
    /// ```
    /// # use nonzero_char::NonZeroChar;
    /// let uppercase_a = 'A';
    /// let uppercase_g = 'G';
    /// let a = 'a';
    /// let g = 'g';
    /// let zero = '0';
    /// let percent = '%';
    /// let space = ' ';
    /// let lf = '\n';
    /// let esc = '\x1b';
    ///
    /// assert!(!uppercase_a.is_ascii_control());
    /// assert!(!uppercase_g.is_ascii_control());
    /// assert!(!a.is_ascii_control());
    /// assert!(!g.is_ascii_control());
    /// assert!(!zero.is_ascii_control());
    /// assert!(!percent.is_ascii_control());
    /// assert!(!space.is_ascii_control());
    /// assert!(lf.is_ascii_control());
    /// assert!(esc.is_ascii_control());
    /// ```
    #[must_use]
    #[inline]
    pub const fn is_ascii_control(&self) -> bool {
        self.get().is_ascii_control()
    }
}

#[test]
fn test_control_upper() {
    let _ = (
        NonZeroChar::MIN,
        NonZeroChar::MAX,
        NonZeroChar::REPLACEMENT_CHARACTER,
        NonZeroChar::UNICODE_VERSION,
    );
    assert_eq!('\x01'.to_ascii_uppercase(), '\x01');
}

#[test]
fn test_npo() {
    assert_eq!(size_of::<Option<NonZeroChar>>(), size_of::<NonZeroChar>());
}
