//! Utility library for dealing with arithmetic on type limits by upcasting into types with higher
//! limits.
//!
//! # Examples
//!
//! ##  Without `upcast_arithmetic`
//! ```should_panic
//! let a = u8::MAX;
//! let b = 2u8;
//!
//! let modulo = u8::MAX;
//!
//! # #[allow(arithmetic_overflow)]
//! let res = (a + b) % modulo;
//! assert_eq!(res, 2);
//! ```
//! ## With `upcast_arithmetic`
//! ```
//! use upcast_arithmetic::*;
//!
//! let a = u8::MAX;
//! let b = 2u8;
//!
//! let modulo = u8::MAX;
//!
//! let res = a.upcast_add_mod(b, modulo);
//! assert_eq!(res, 2);
//! ```
#![no_std]

use core::ops::{Add, Mul, MulAssign, Rem, Sub};

#[allow(clippy::doc_markdown)]
/// Performs checked addition. Maps directly to the integers checked_add method. (i.e.
/// [`u8::checked_add`]) Consult the docs of the primitive methods to learn more.
pub trait CheckedAdd: Add + Sized {
    fn checked_add(self, rhs: Self) -> Option<Self>;
}

#[allow(clippy::doc_markdown)]
/// Performs checked substraction. Maps directly to the integers checked_sub method. (i.e.
/// [`u8::checked_sub`]) Consult the docs of the primitive methods to learn more.
pub trait CheckedSub: Sub + Sized {
    fn checked_sub(self, rhs: Self) -> Option<Self>;
}

#[allow(clippy::doc_markdown)]
/// Performs checked multiplication. Maps directly to the integers checked_mul method. (i.e.
/// [`u8::checked_mul`]) Consult the docs of the primitive methods to learn more.
pub trait CheckedMul: Mul + Sized {
    fn checked_mul(self, rhs: Self) -> Option<Self>;
}

#[allow(clippy::doc_markdown)]
/// Performs checked power. Maps directly to the integers checked_pow method. (i.e.
/// [`u8::checked_pow`]) Consult the docs of the primitive methods to learn more.
pub trait CheckedPow: Sized {
    fn checked_pow(self, exp: u32) -> Option<Self>;
}

macro_rules! checked_impl {
    ($t:ty) => {
        impl CheckedAdd for $t {
            #[inline]
            fn checked_add(self, rhs: Self) -> Option<Self> {
                Self::checked_add(self, rhs)
            }
        }

        impl CheckedSub for $t {
            #[inline]
            fn checked_sub(self, rhs: Self) -> Option<Self> {
                Self::checked_sub(self, rhs)
            }
        }

        impl CheckedMul for $t {
            #[inline]
            fn checked_mul(self, rhs: Self) -> Option<Self> {
                Self::checked_mul(self, rhs)
            }
        }

        impl CheckedPow for $t {
            #[inline]
            fn checked_pow(self, exp: u32) -> Option<Self> {
                Self::checked_pow(self, exp)
            }
        }
    };
}

checked_impl!(u8);
checked_impl!(u16);
checked_impl!(u32);
checked_impl!(u64);
checked_impl!(i8);
checked_impl!(i16);
checked_impl!(i32);
checked_impl!(i64);

/// Performs power (self ^ exp). Maps directly to the underlaying integer method.
///
/// # Panics
///
/// Panics if the calculation overflows.
pub trait Pow: Sized {
    #[must_use]
    fn pow(self, exp: u32) -> Self;
}

macro_rules! pow_impl {
    ($t:ty) => {
        impl Pow for $t {
            #[inline]
            fn pow(self, exp: u32) -> Self {
                Self::pow(self, exp)
            }
        }
    };
}

pow_impl!(u8);
pow_impl!(u16);
pow_impl!(u32);
pow_impl!(u64);
pow_impl!(u128);
pow_impl!(i8);
pow_impl!(i16);
pow_impl!(i32);
pow_impl!(i64);
pow_impl!(i128);

/// Performs upcasting to type with higher (and/or lower) limits.
///
/// i.e. casts u8 to u16
pub trait Upcast: Sized {
    /// The higher type casted to (if Self is u8, this is u16).
    type Higher;

    /// Casts self to higher.
    fn upcast(self) -> Self::Higher;
    /// Attempts to cast down to lower from higher. Returns [`Option::None`] if inp exceeds the
    /// limits of Self.
    fn downcast(inp: Self::Higher) -> Option<Self>;
}

macro_rules! upcast_impl {
    ($t:ty, $h:ty) => {
        impl Upcast for $t {
            type Higher = $h;

            #[inline]
            fn upcast(self) -> Self::Higher {
                self.into()
            }

            #[inline]
            fn downcast(inp: Self::Higher) -> Option<Self> {
                inp.try_into().ok()
            }
        }
    };
}

upcast_impl!(u8, u16);
upcast_impl!(u16, u32);
upcast_impl!(u32, u64);
upcast_impl!(u64, u128);
upcast_impl!(i8, i16);
upcast_impl!(i16, i32);
upcast_impl!(i32, i64);
upcast_impl!(i64, i128);

/// Trait for the one value of a type.
pub trait One {
    /// Associated constant.
    const ONE: Self;
}

macro_rules! one_impl {
    ($t:ty) => {
        impl One for $t {
            const ONE: Self = 1;
        }
    };
}

one_impl!(u8);
one_impl!(u16);
one_impl!(u32);
one_impl!(u64);
one_impl!(u128);
one_impl!(i8);
one_impl!(i16);
one_impl!(i32);
one_impl!(i64);
one_impl!(i128);

/// Trait to implement upcast add. (Casting up when type bounds are hit during arithmetic)
pub trait UpcastAdd<H: Add<Output = H> + Rem<Output = H>>:
    Upcast<Higher = H> + CheckedAdd + Copy
{
    /// performs the operation `self + rhs` and returns value as type H.
    ///
    /// ```
    /// # use upcast_arithmetic::UpcastAdd;
    /// let a = u8::MAX;
    /// let b = u8::MAX;
    ///
    /// // a + b would panic
    /// let res = a.upcast_add(b);
    ///
    /// let expected = (a as u16) * 2;
    /// assert_eq!(res, expected);
    /// ```
    #[must_use]
    #[inline]
    fn upcast_add(self, rhs: Self) -> H {
        self.checked_add(rhs)
            .map_or_else(|| self.upcast() + rhs.upcast(), Upcast::upcast)
    }

    /// performs the operation `(self + rhs) % modulo` and returns the value as type Self.
    ///
    /// ```
    /// # use upcast_arithmetic::UpcastAdd;
    /// let a = u8::MAX;
    /// let b = 10;
    /// let modulo = u8::MAX;
    ///
    /// let expected = b;
    ///
    /// let res = a.upcast_add_mod(b, modulo);
    /// assert_eq!(res, expected);
    #[must_use]
    #[inline]
    fn upcast_add_mod(self, rhs: Self, modulo: Self) -> Self {
        Self::downcast(Self::upcast_add(self, rhs).rem(modulo.upcast())).unwrap()
    }
}

/// Trait to implement upcast sub. (Casting up when type bounds are hit during arithmetic)
pub trait UpcastSub<H: Sub<Output = H> + Rem<Output = H>>:
    Upcast<Higher = H> + CheckedSub + Copy
{
    /// performs the operatoin `self - rhs` and returns value as type H.
    ///
    /// ```
    /// # use upcast_arithmetic::UpcastSub;
    /// let a = i8::MIN;
    /// let b = 10;
    ///
    /// let expected = i8::MIN as i16 - 10;
    ///
    /// let res = a.upcast_sub(b);
    /// assert_eq!(res, expected);
    /// ```
    ///
    /// # Panics
    /// Panics if the operation still exceeds the higher types limit.
    ///
    /// ```should_panic
    /// # use upcast_arithmetic::UpcastSub;
    /// let a = 1u8;
    /// let b = 2u8;
    ///
    /// let _ = a.upcast_sub(b);
    /// ```
    #[must_use]
    #[inline]
    fn upcast_sub(self, rhs: Self) -> H {
        self.checked_sub(rhs)
            .map_or_else(|| self.upcast() - rhs.upcast(), Upcast::upcast)
    }

    /// performs the operation `(self - rhs) % modulo` and returns value as type Self.
    ///
    /// ```
    /// # use upcast_arithmetic::UpcastSub;
    /// let a = i8::MIN;
    /// let b = 10;
    /// let modulo = i8::MIN;
    ///
    /// let expected = -10;
    ///
    /// let res = a.upcast_sub_mod(b, modulo);
    /// assert_eq!(res, expected);
    /// ```
    #[must_use]
    #[inline]
    fn upcast_sub_mod(self, rhs: Self, modulo: Self) -> Self {
        Self::downcast(Self::upcast_sub(self, rhs).rem(modulo.upcast())).unwrap()
    }
}

/// Trait to implement upcast mul. (Casting up when type bounds are hit during arithmetic)
pub trait UpcastMul<H: Mul<Output = H> + Rem<Output = H>>:
    Upcast<Higher = H> + CheckedMul + Rem<Output = Self> + Copy
{
    /// performs the operation `self * rhs` and returns a value of type H.
    ///
    /// ```
    /// # use upcast_arithmetic::UpcastMul;
    /// let a = u8::MAX;
    /// let b = 2;
    ///
    /// let expected = u8::MAX as u16 * 2;
    ///
    /// let res = a.upcast_mul(b);
    /// assert_eq!(res, expected);
    /// ```
    #[must_use]
    #[inline]
    fn upcast_mul(self, rhs: Self) -> H {
        self.checked_mul(rhs)
            .map_or_else(|| self.upcast() * rhs.upcast(), Upcast::upcast)
    }

    /// performs the operation `(self * rhs) % modulo` and returns the a value of type Self.
    #[must_use]
    #[inline]
    fn upcast_mul_mod(self, rhs: Self, modulo: Self) -> Self {
        Self::downcast(Self::upcast_mul(self, rhs).rem(modulo.upcast())).unwrap()
    }
}

/// Trait to perform upcast pow. (Casting up when type bounds are hit during arithmetic)
///
/// # Why the additional bounds?
/// The algorithm to perform `(self % rhs) % modulo` is not as straightforward as the other
/// algorithms. The reason behind this is a more complex algorithm used to calculate `(self * rhs)
/// % modulo`.
pub trait UpcastPow<H>: Upcast<Higher = H> + CheckedPow + Copy + Rem<Output = Self>
where
    H: Pow + One + PartialOrd + Rem<Output = H> + MulAssign + Copy,
{
    /// performs the operation `self * rhs` and returns a value of type H.
    #[must_use]
    #[inline]
    fn upcast_pow(self, exp: u32) -> H {
        self.checked_pow(exp)
            .map_or_else(|| self.upcast().pow(32), Upcast::upcast)
    }

    /// performs the operation `(self * rhs) % modulo` and returns a value of type Self.
    ///
    /// The implementation uses the [Right-to-left binary
    /// method](https://en.wikipedia.org/wiki/Modular_exponentiation#Right-to-left_binary_method).
    #[must_use]
    #[inline]
    fn upcast_pow_mod(self, mut exp: u32, modulo: Self) -> Self {
        self.checked_pow(exp).map_or_else(
            || {
                let mut res: H = H::ONE;
                let mut x_upcast = self.upcast();
                while exp > 0 {
                    if exp % 2 == 1 {
                        res *= x_upcast;
                    }
                    exp >>= 1;
                    x_upcast *= x_upcast;
                }
                Self::downcast(res % modulo.upcast()).unwrap()
            },
            |e| e % modulo,
        )
    }
}

macro_rules! upcast_arith_impl {
    ($t:ty, $h:ty) => {
        impl UpcastAdd<$h> for $t {}
        impl UpcastMul<$h> for $t {}
        impl UpcastPow<$h> for $t {}
        impl UpcastSub<$h> for $t {}
    };
}

upcast_arith_impl!(u8, u16);
upcast_arith_impl!(u16, u32);
upcast_arith_impl!(u32, u64);
upcast_arith_impl!(u64, u128);
upcast_arith_impl!(i8, i16);
upcast_arith_impl!(i16, i32);
upcast_arith_impl!(i32, i64);
upcast_arith_impl!(i64, i128);

/// utilities for performing upcast arithmetic in `const`.
pub mod constant {
    macro_rules! gen_upcast_arith {
        ($t:ty, $h:ty, $i:ident, $o:ident, $m:ident, $e:tt) => {
            #[must_use]
            pub const fn $i(lhs: $t, rhs: $t) -> $h {
                match lhs.$m(rhs) {
                    Some(e) => e as $h,
                    None => (lhs as $h) $e (rhs as $h),
                }
            }

            #[must_use]
            pub const fn $o(lhs: $t, rhs: $t, modulo: $t) -> $t {
                match lhs.$m(rhs) {
                    Some(e) => e % modulo,
                    None => (((lhs as $h) $e (rhs as $h)) % (modulo as $h)) as $t,
                }
            }
        };
    }
    macro_rules! gen_upcast_add_impl {
        ($t:ty, $h:ty, $i:ident, $o:ident) => {
            gen_upcast_arith!($t, $h, $i, $o, checked_add, +);

        };
    }
    macro_rules! gen_upcast_sub_impl {
        ($t:ty, $h:ty, $i:ident, $o:ident) => {
            gen_upcast_arith!($t, $h, $i, $o, checked_sub, -);
        };
    }

    macro_rules! gen_upcast_mul_impl {
        ($t:ty, $h:ty, $i:ident, $o:ident) => {
            gen_upcast_arith!($t, $h, $i, $o, checked_mul, *);
        };
    }

    gen_upcast_add_impl!(u8, u16, upcast_add_u8, upcast_add_mod_u8);
    gen_upcast_add_impl!(u16, u32, upcast_add_u16, upcast_add_mod_u16);
    gen_upcast_add_impl!(u32, u64, upcast_add_u32, upcast_add_mod_u32);
    gen_upcast_add_impl!(u64, u128, upcast_add_u64, upcast_add_mod_u64);
    gen_upcast_add_impl!(i8, i16, upcast_add_i8, upcast_add_mod_i8);
    gen_upcast_add_impl!(i16, i32, upcast_add_i16, upcast_add_mod_i16);
    gen_upcast_add_impl!(i32, i64, upcast_add_i32, upcast_add_mod_i32);
    gen_upcast_add_impl!(i64, i128, upcast_add_i64, upcast_add_mod_i64);

    gen_upcast_sub_impl!(u8, u16, upcast_sub_u8, upcast_sub_mod_u8);
    gen_upcast_sub_impl!(u16, u32, upcast_sub_u16, upcast_sub_mod_u16);
    gen_upcast_sub_impl!(u32, u64, upcast_sub_u32, upcast_sub_mod_u32);
    gen_upcast_sub_impl!(u64, u128, upcast_sub_u64, upcast_sub_mod_u64);
    gen_upcast_sub_impl!(i8, i16, upcast_sub_i8, upcast_sub_mod_i8);
    gen_upcast_sub_impl!(i16, i32, upcast_sub_i16, upcast_sub_mod_i16);
    gen_upcast_sub_impl!(i32, i64, upcast_sub_i32, upcast_sub_mod_i32);
    gen_upcast_sub_impl!(i64, i128, upcast_sub_i64, upcast_sub_mod_i64);

    gen_upcast_mul_impl!(u8, u16, upcast_mul_u8, upcast_mul_mod_u8);
    gen_upcast_mul_impl!(u16, u32, upcast_mul_u16, upcast_mul_mod_u16);
    gen_upcast_mul_impl!(u32, u64, upcast_mul_u32, upcast_mul_mod_u32);
    gen_upcast_mul_impl!(u64, u128, upcast_mul_u64, upcast_mul_mod_u64);
    gen_upcast_mul_impl!(i8, i16, upcast_mul_i8, upcast_mul_mod_i8);
    gen_upcast_mul_impl!(i16, i32, upcast_mul_i16, upcast_mul_mod_i16);
    gen_upcast_mul_impl!(i32, i64, upcast_mul_i32, upcast_mul_mod_i32);
    gen_upcast_mul_impl!(i64, i128, upcast_mul_i64, upcast_mul_mod_i64);
}
