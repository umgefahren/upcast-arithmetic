use std::ops::{Add, Mul, Rem, Sub};

pub trait CheckedAdd: Add + Sized {
    fn checked_add(self, rhs: Self) -> Option<Self>;
}

pub trait CheckedSub: Sub + Sized {
    fn checked_sub(self, rhs: Self) -> Option<Self>;
}

pub trait CheckedMul: Mul + Sized {
    fn checked_mul(self, rhs: Self) -> Option<Self>;
}

pub trait CheckedPow: Sized {
    fn checked_pow(self, exp: u32) -> Option<Self>;
}

macro_rules! checked_impl {
    ($t:ty) => {
        impl CheckedAdd for $t {
            fn checked_add(self, rhs: Self) -> Option<Self> {
                <$t>::checked_add(self, rhs)
            }
        }

        impl CheckedSub for $t {
            fn checked_sub(self, rhs: Self) -> Option<Self> {
                <$t>::checked_sub(self, rhs)
            }
        }

        impl CheckedMul for $t {
            fn checked_mul(self, rhs: Self) -> Option<Self> {
                <$t>::checked_mul(self, rhs)
            }
        }

        impl CheckedPow for $t {
            fn checked_pow(self, exp: u32) -> Option<Self> {
                <$t>::checked_pow(self, exp)
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

pub trait Pow: Sized {
    fn pow(self, exp: u32) -> Self;
}

macro_rules! pow_impl {
    ($t:ty) => {
        impl Pow for $t {
            fn pow(self, exp: u32) -> Self {
                <$t>::pow(self, exp)
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

pub trait Upcast: Sized {
    type Higher;

    fn upcast(self) -> Self::Higher;
    fn downcast(inp: Self::Higher) -> Option<Self>;
}

macro_rules! upcast_impl {
    ($t:ty, $h:ty) => {
        impl Upcast for $t {
            type Higher = $h;

            fn upcast(self) -> Self::Higher {
                self.into()
            }

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

pub trait One {
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

pub trait UpcastAdd<H: Add<Output = H> + Rem<Output = H>>:
    Upcast<Higher = H> + CheckedAdd + Copy
{
    fn upcast_add(self, rhs: Self) -> H {
        self.checked_add(rhs)
            .map(|e| e.upcast())
            .unwrap_or_else(|| self.upcast() + rhs.upcast())
    }

    fn upcast_add_mod(self, rhs: Self, modulo: Self) -> Self {
        Self::downcast(Self::upcast_add(self, rhs).rem(modulo.upcast())).unwrap()
    }
}

pub trait UpcastSub<H: Sub<Output = H> + Rem<Output = H>>:
    Upcast<Higher = H> + CheckedSub + Copy
{
    fn upcast_sub(self, rhs: Self) -> H {
        self.checked_sub(rhs)
            .map(|e| e.upcast())
            .unwrap_or_else(|| self.upcast() - rhs.upcast())
    }

    fn upcast_sub_mod(self, rhs: Self, modulo: Self) -> Self {
        Self::downcast(Self::upcast_sub(self, rhs).rem(modulo.upcast())).unwrap()
    }
}

pub trait UpcastMul<H: Mul<Output = H> + Rem<Output = H>>:
    Upcast<Higher = H> + CheckedMul + Copy
{
    fn upcast_mul(self, rhs: Self) -> H {
        self.checked_mul(rhs)
            .map(|e| e.upcast())
            .unwrap_or_else(|| self.upcast() * rhs.upcast())
    }

    fn upcast_mul_mod(self, rhs: Self, modulo: Self) -> Self {
        Self::downcast(Self::upcast_mul(self, rhs).rem(modulo.upcast())).unwrap()
    }
}

pub trait UpcastPow<H>: Upcast<Higher = H> + CheckedPow + Copy + Rem<Output = Self>
where
    H:  Pow + One + PartialOrd + Rem<Output = H> + Mul<Output = H> + Copy,
{
    fn upcast_pow(self, exp: u32) -> H {
        self.checked_pow(exp)
            .map(|e| e.upcast())
            .unwrap_or_else(|| self.upcast().pow(32))
    }

    fn upcast_pow_mod(self, mut exp: u32, modulo: Self) -> Self {
        self.checked_pow(exp)
            .map(|e| e % modulo)
            .unwrap_or_else(|| {
                let mut res: H = H::ONE;
                let mut x_upcast = self.upcast();

                while exp > 0 {
                    if exp % 2 == 1 {
                        res = res * x_upcast;
                    }

                    exp = exp >> 1;

                    x_upcast = x_upcast * x_upcast;
                }

                Self::downcast(res % modulo.upcast()).unwrap()
            })
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