macro_rules! gen_add_mod_test {
    ($t:ty) => {
        #[test]
        fn add_mod() {
            let res = <$t>::MAX.upcast_add_mod(1, <$t>::MAX);
            assert_eq!(res, 1);
            let res = <$t>::MAX.upcast_add_mod(<$t>::MAX, <$t>::MAX);
            assert_eq!(res, 0);
            const ONE: $t = 1;
            let res = ONE.upcast_add_mod(ONE, 3);
            assert_eq!(res, 2);
            let res = ONE.upcast_add_mod(ONE, 2);
            assert_eq!(res, 0);
        }
    };
}

macro_rules! gen_add_test {
    ($t:ty, $h:ty) => {
        #[test]
        fn add() {
            const EXPECTED: $h = <$t>::MAX as $h + <$t>::MAX as $h;
            let res = <$t>::MAX.upcast_add(<$t>::MAX);
            assert_eq!(EXPECTED, res);
            const ONE: $t = 1;
            let low: $t = ONE.upcast_add(ONE).try_into().unwrap();
            assert_eq!(2, low);
        }
    };
}

macro_rules! gen_module {
    ($t:ty, $h:ty, $i:ident) => {
        mod $i {
            use upcast_arithmetic::UpcastAdd;

            gen_add_mod_test!($t);
            gen_add_test!($t, $h);
        }
    };
}

gen_module!(u8, u16, u8);
gen_module!(u16, u32, u16);
gen_module!(u32, u64, u32);
gen_module!(u64, u128, u64);
gen_module!(i8, i16, i8);
gen_module!(i16, i32, i16);
gen_module!(i32, i64, i32);
gen_module!(i64, i128, i64);
