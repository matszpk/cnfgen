// arith.rs - integer expression structures.

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module contains operators definitions.

use std::fmt::Debug;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};
use std::ops::{Div, Rem};
use std::ops::{Mul, MulAssign, Neg, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

use generic_array::typenum::*;
use generic_array::*;

use super::*;
use crate::VarLit;
use crate::{impl_int_ipty, impl_int_upty};

impl<T, N: ArrayLength<usize>> IntVar<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Calculation of an absolute value. It returns unsigned expression node.
    pub fn abs(&self) -> IntVar<T, N, false> {
        IntVar::<T, N, false>(self.0.clone().abs())
    }
}

impl<T, N, const SIGN: bool> Not for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn not(self) -> Self {
        Self(!self.0)
    }
}

impl<T, N, const SIGN: bool> Not for &IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = <IntVar<T, N, SIGN> as Not>::Output;

    fn not(self) -> Self::Output {
        IntVar(!self.0.clone())
    }
}

impl<T, N> IntModNeg for IntVar<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn mod_neg(self) -> Self {
        Self((self.0.as_signed().mod_neg()).as_unsigned())
    }
}

impl<T, N> IntModNeg for &IntVar<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = <IntVar<T, N, false> as IntModNeg>::Output;

    fn mod_neg(self) -> Self::Output {
        IntVar((self.0.clone().as_signed().mod_neg()).as_unsigned())
    }
}

impl<T, N> IntModNeg for IntVar<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn mod_neg(self) -> Self {
        Self(self.0.mod_neg())
    }
}

impl<T, N> IntModNeg for &IntVar<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = <IntVar<T, N, true> as IntModNeg>::Output;

    fn mod_neg(self) -> Self::Output {
        IntVar(self.0.clone().mod_neg())
    }
}

impl<T, N> Neg for IntVar<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn neg(self) -> Self {
        Self((self.0.as_signed().mod_neg()).as_unsigned())
    }
}

impl<T, N> Neg for &IntVar<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = <IntVar<T, N, false> as Neg>::Output;

    fn neg(self) -> Self::Output {
        IntVar((self.0.clone().as_signed().mod_neg()).as_unsigned())
    }
}

impl<T, N> Neg for IntVar<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn neg(self) -> Self {
        Self(self.0.mod_neg())
    }
}

impl<T, N> Neg for &IntVar<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = <IntVar<T, N, true> as Neg>::Output;

    fn neg(self) -> Self::Output {
        IntVar(self.0.clone().mod_neg())
    }
}

impl<T, N> IntCondNeg for IntVar<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;
    type OutputCond = BoolVar<T>;

    fn cond_neg(self) -> (Self::Output, Self::OutputCond) {
        let (r, c) = self.0.cond_neg();
        (Self(r), c.into())
    }
}

impl<T, N> IntCondNeg for &IntVar<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = <IntVar<T, N, true> as IntCondNeg>::Output;
    type OutputCond = <IntVar<T, N, true> as IntCondNeg>::OutputCond;

    fn cond_neg(self) -> (Self::Output, Self::OutputCond) {
        let (r, c) = self.0.clone().cond_neg();
        (IntVar(r), c.into())
    }
}

//////////
// Add/Sub implementation

impl<T, N: ArrayLength<usize>, const SIGN: bool> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Returns result of modular addition with input carry `in_carry` and output carry.
    pub fn addc_with_carry(&self, rhs: &Self, in_carry: &BoolVar<T>) -> (Self, BoolVar<T>) {
        let (s, c) = self
            .0
            .clone()
            .addc_with_carry(rhs.0.clone(), in_carry.clone().into());
        (Self(s), c.into())
    }

    /// Returns result of modular addition with input carry.
    pub fn addc(&self, rhs: &Self, in_carry: &BoolVar<T>) -> Self {
        Self(self.0.clone().addc(rhs.0.clone(), in_carry.clone().into()))
    }

    /// Returns result of modular subtraction with input carry - it performs `(A + !B) + carry`.
    pub fn subc(&self, rhs: &Self, in_carry: &BoolVar<T>) -> Self {
        Self(self.0.clone().subc(rhs.0.clone(), in_carry.clone().into()))
    }

    /// Returns result of modular addition of self and same carry.
    pub fn add_same_carry(&self, in_carry: &BoolVar<T>) -> Self {
        Self(self.0.clone().add_same_carry(in_carry.clone().into()))
    }

    /// Returns result of modular addition with input carry `in_carry` and output carry.
    pub fn addc_with_carry_c<BT: Into<BoolVar<T>>>(
        &self,
        rhs: Self,
        in_carry: BT,
    ) -> (Self, BoolVar<T>) {
        let (s, c) = self
            .0
            .clone()
            .addc_with_carry(rhs.0.clone(), in_carry.into().into());
        (Self(s), c.into())
    }

    /// Returns result of modular addition with input carry.
    pub fn addc_c<BT: Into<BoolVar<T>>>(&self, rhs: Self, in_carry: BT) -> Self {
        Self(self.0.clone().addc(rhs.0.clone(), in_carry.into().into()))
    }

    /// Returns result of modular subtraction with input carry - it performs `(A + !B) + carry`.
    pub fn subc_c<BT: Into<BoolVar<T>>>(&self, rhs: Self, in_carry: BT) -> Self {
        Self(self.0.clone().subc(rhs.0.clone(), in_carry.into().into()))
    }

    /// Returns result of modular addition of self and same carry.
    pub fn add_same_carry_c<BT: Into<BoolVar<T>>>(&self, in_carry: BT) -> Self {
        Self(self.0.clone().add_same_carry(in_carry.into().into()))
    }
}

macro_rules! new_op_impl {
    ($t:ident, $u:ident, $v:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<IntVar<T, N, SIGN>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
                Self(self.0.$v(rhs.0))
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<&IntVar<T, N, SIGN>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
                Self(self.0.$v(rhs.0.clone()))
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<IntVar<T, N, SIGN>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
                IntVar::<T, N, SIGN>(self.0.clone().$v(rhs.0))
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<&IntVar<T, N, SIGN>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
                IntVar::<T, N, SIGN>(self.0.clone().$v(rhs.0.clone()))
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T, N: ArrayLength<usize>> $t<$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: $pty) -> Self::Output {
                        self.$u(Self::from(rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: &$pty) -> Self::Output {
                        self.$u(Self::from(*rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<$pty> for &IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: $pty) -> Self::Output {
                        self.$u(IntVar::<T, N, $sign>::from(rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&$pty> for &IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: &$pty) -> Self::Output {
                        self.$u(IntVar::<T, N, $sign>::from(*rhs))
                    }
                }

                impl<T, N: ArrayLength<usize>> $t<IntVar<T, N, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&IntVar<T, N, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<IntVar<T, N, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(*self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&IntVar<T, N, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    fn $u(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(*self).$u(rhs)
                    }
                }
            };
        }

        macro_rules! $macro_upty {
            ($pty:ty) => {
                $macro_gen!(false, $pty);
            };
        }
        macro_rules! $macro_ipty {
            ($pty:ty) => {
                $macro_gen!(true, $pty);
            };
        }

        impl_int_upty!($macro_upty);
        impl_int_ipty!($macro_ipty);
    };
}

new_op_impl!(BitAnd, bitand, bitand, bitand_gen, bitand_upty, bitand_ipty);
new_op_impl!(BitOr, bitor, bitor, bitor_gen, bitor_upty, bitor_ipty);
new_op_impl!(BitXor, bitxor, bitxor, bitxor_gen, bitxor_upty, bitxor_ipty);
new_op_impl!(
    IntModAdd,
    mod_add,
    mod_add,
    modadd_gen,
    modadd_upty,
    modadd_ipty
);
new_op_impl!(Add, add, mod_add, add_gen, add_upty, add_ipty);
new_op_impl!(
    IntModSub,
    mod_sub,
    mod_sub,
    modsub_gen,
    modsub_upty,
    modsub_ipty
);
new_op_impl!(Sub, sub, mod_sub, sub_gen, sub_upty, sub_ipty);
new_op_impl!(
    IntModMul,
    mod_mul,
    mod_mul,
    modmul_gen,
    modmul_upty,
    modmul_ipty
);
new_op_impl!(Mul, mul, mod_mul, mul_gen, mul_upty, mul_ipty);

macro_rules! new_opassign_impl {
    ($t:ident, $u:ident, $v:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<IntVar<T, N, SIGN>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $u(&mut self, rhs: IntVar<T, N, SIGN>) {
                self.0.$v(rhs.0);
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<&IntVar<T, N, SIGN>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $u(&mut self, rhs: &IntVar<T, N, SIGN>) {
                self.0.$v(rhs.0.clone());
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T, N: ArrayLength<usize>> $t<$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    fn $u(&mut self, rhs: $pty) {
                        self.$u(Self::from(rhs));
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    fn $u(&mut self, rhs: &$pty) {
                        self.$u(Self::from(*rhs));
                    }
                }
            };
        }

        macro_rules! $macro_upty {
            ($pty:ty) => {
                $macro_gen!(false, $pty);
            };
        }
        macro_rules! $macro_ipty {
            ($pty:ty) => {
                $macro_gen!(true, $pty);
            };
        }

        impl_int_upty!($macro_upty);
        impl_int_ipty!($macro_ipty);
    };
}

new_opassign_impl!(
    BitAndAssign,
    bitand_assign,
    bitand_assign,
    bitand_assign_gen,
    bitand_assign_upty,
    bitand_assign_ipty
);
new_opassign_impl!(
    BitOrAssign,
    bitor_assign,
    bitor_assign,
    bitor_assign_gen,
    bitor_assign_upty,
    bitor_assign_ipty
);
new_opassign_impl!(
    BitXorAssign,
    bitxor_assign,
    bitxor_assign,
    bitxor_assign_gen,
    bitxor_assign_upty,
    bitxor_assign_ipty
);
new_opassign_impl!(
    IntModAddAssign,
    mod_add_assign,
    mod_add_assign,
    modadd_assign_gen,
    modadd_assign_upty,
    modadd_assign_ipty
);
new_opassign_impl!(
    AddAssign,
    add_assign,
    mod_add_assign,
    add_assign_gen,
    add_assign_upty,
    add_assign_ipty
);
new_opassign_impl!(
    IntModSubAssign,
    mod_sub_assign,
    mod_sub_assign,
    modsub_assign_gen,
    modsub_assign_upty,
    modsub_assign_ipty
);
new_opassign_impl!(
    SubAssign,
    sub_assign,
    mod_sub_assign,
    sub_assign_gen,
    sub_assign_upty,
    sub_assign_ipty
);
new_opassign_impl!(
    IntModMulAssign,
    mod_mul_assign,
    mod_mul_assign,
    modmul_assign_gen,
    modmul_assign_upty,
    modmul_assign_ipty
);
new_opassign_impl!(
    MulAssign,
    mul_assign,
    mod_mul_assign,
    mul_assign_gen,
    mul_assign_upty,
    mul_assign_ipty
);

macro_rules! new_condop_impl {
    ($t:ident, $u:ident, $v:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<IntVar<T, N, SIGN>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: IntVar<T, N, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$v(rhs.0);
                (IntVar(r), c.into())
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<&IntVar<T, N, SIGN>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &IntVar<T, N, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$v(rhs.0.clone());
                (IntVar(r), c.into())
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<IntVar<T, N, SIGN>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: IntVar<T, N, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$v(rhs.0);
                (IntVar(r), c.into())
            }
        }
        impl<T, N: ArrayLength<usize>, const SIGN: bool> $t<&IntVar<T, N, SIGN>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &IntVar<T, N, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$v(rhs.0.clone());
                (IntVar(r), c.into())
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T, N: ArrayLength<usize>> $t<$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                        self.$u(Self::from(rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                        self.$u(Self::from(*rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<$pty> for &IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                        self.$u(IntVar::<T, N, $sign>::from(rhs))
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&$pty> for &IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                        self.$u(IntVar::<T, N, $sign>::from(*rhs))
                    }
                }

                impl<T, N: ArrayLength<usize>> $t<IntVar<T, N, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                        IntVar::<T, N, $sign>::from(self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&IntVar<T, N, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                        IntVar::<T, N, $sign>::from(self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<IntVar<T, N, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                        IntVar::<T, N, $sign>::from(*self).$u(rhs)
                    }
                }
                impl<T, N: ArrayLength<usize>> $t<&IntVar<T, N, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = IntVar<T, N, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                        IntVar::<T, N, $sign>::from(*self).$u(rhs)
                    }
                }
            };
        }

        macro_rules! $macro_upty {
            ($pty:ty) => {
                $macro_gen!(false, $pty);
            };
        }
        macro_rules! $macro_ipty {
            ($pty:ty) => {
                $macro_gen!(true, $pty);
            };
        }

        impl_int_upty!($macro_upty);
        impl_int_ipty!($macro_ipty);
    };
}

new_condop_impl!(
    IntCondAdd,
    cond_add,
    cond_add,
    condadd_gen,
    condadd_upty,
    condadd_ipty
);
new_condop_impl!(
    IntCondSub,
    cond_sub,
    cond_sub,
    condsub_gen,
    condsub_upty,
    condsub_ipty
);

macro_rules! condmul_varvar {
    ($sign:expr) => {
        impl<T, N: ArrayLength<usize>> IntCondMul<IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.cond_mul(rhs.0);
                (IntVar(r), c.into())
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<&IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.cond_mul(rhs.0.clone());
                (IntVar(r), c.into())
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().cond_mul(rhs.0);
                (IntVar(r), c.into())
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<&IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().cond_mul(rhs.0.clone());
                (IntVar(r), c.into())
            }
        }
    };
}

condmul_varvar!(false);
condmul_varvar!(true);

macro_rules! condmul_gen {
    ($sign:expr, $pty:ty) => {
        impl<T, N: ArrayLength<usize>> IntCondMul<$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                self.cond_mul(Self::from(rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<&$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                self.cond_mul(Self::from(*rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                self.cond_mul(IntVar::<T, N, $sign>::from(rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<&$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                self.cond_mul(IntVar::<T, N, $sign>::from(*rhs))
            }
        }

        impl<T, N: ArrayLength<usize>> IntCondMul<IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                IntVar::<T, N, $sign>::from(self).cond_mul(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<&IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                IntVar::<T, N, $sign>::from(self).cond_mul(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                IntVar::<T, N, $sign>::from(*self).cond_mul(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntCondMul<&IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &IntVar<T, N, $sign>) -> (Self::Output, Self::OutputCond) {
                IntVar::<T, N, $sign>::from(*self).cond_mul(rhs)
            }
        }
    };
}

macro_rules! condmul_upty {
    ($pty:ty) => {
        condmul_gen!(false, $pty);
    };
}
macro_rules! condmul_ipty {
    ($pty:ty) => {
        condmul_gen!(true, $pty);
    };
}

impl_int_upty!(condmul_upty);
impl_int_ipty!(condmul_ipty);

// Shifts
macro_rules! new_shiftop_impl {
    ($t:ident, $u:ident, $mimm:ident) => {
        impl<T, N, N2, const SIGN: bool, const SIGN2: bool> $t<IntVar<T, N2, SIGN2>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
        {
            type Output = Self;
            fn $u(self, rhs: IntVar<T, N2, SIGN2>) -> Self::Output {
                Self(self.0.$u(rhs.0))
            }
        }
        impl<T, N, N2, const SIGN: bool, const SIGN2: bool> $t<&IntVar<T, N2, SIGN2>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
        {
            type Output = Self;
            fn $u(self, rhs: &IntVar<T, N2, SIGN2>) -> Self::Output {
                Self(self.0.$u(rhs.0.clone()))
            }
        }
        impl<T, N, N2, const SIGN: bool, const SIGN2: bool> $t<IntVar<T, N2, SIGN2>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: IntVar<T, N2, SIGN2>) -> Self::Output {
                IntVar::<T, N, SIGN>(self.0.clone().$u(rhs.0))
            }
        }
        impl<T, N, N2, const SIGN: bool, const SIGN2: bool> $t<&IntVar<T, N2, SIGN2>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
        {
            type Output = IntVar<T, N, SIGN>;
            fn $u(self, rhs: &IntVar<T, N2, SIGN2>) -> Self::Output {
                IntVar::<T, N, SIGN>(self.0.clone().$u(rhs.0.clone()))
            }
        }

        macro_rules! $mimm {
            ($ty:ty) => {
                impl<T, N, const SIGN: bool> $t<$ty> for IntVar<T, N, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    type Output = Self;
                    fn $u(self, rhs: $ty) -> Self::Output {
                        Self(self.0.$u(rhs))
                    }
                }
                impl<T, N, const SIGN: bool> $t<&$ty> for IntVar<T, N, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    type Output = Self;
                    fn $u(self, rhs: &$ty) -> Self::Output {
                        Self(self.0.$u(*rhs))
                    }
                }
                impl<T, N, const SIGN: bool> $t<$ty> for &IntVar<T, N, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    type Output = IntVar<T, N, SIGN>;
                    fn $u(self, rhs: $ty) -> Self::Output {
                        IntVar::<T, N, SIGN>(self.0.clone().$u(rhs))
                    }
                }
                impl<T, N, const SIGN: bool> $t<&$ty> for &IntVar<T, N, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    type Output = IntVar<T, N, SIGN>;
                    fn $u(self, rhs: &$ty) -> Self::Output {
                        IntVar::<T, N, SIGN>(self.0.clone().$u(*rhs))
                    }
                }
            };
        }

        impl_int_upty!($mimm);
        impl_int_ipty!($mimm);
    };
}

macro_rules! new_shiftop_selfimm_impl {
    ($t:ident, $u:ident, $mselfimm:ident) => {
        macro_rules! $mselfimm {
            ($sign:expr, $ty:ty, $bits:ty) => {
                impl<T, N, const SIGN: bool> $t<IntVar<T, N, SIGN>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    type Output = IntVar<T, $bits, $sign>;
                    fn $u(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
                        IntVar::<T, $bits, $sign>(self.$u(rhs.0))
                    }
                }
                impl<T, N, const SIGN: bool> $t<&IntVar<T, N, SIGN>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    type Output = IntVar<T, $bits, $sign>;
                    fn $u(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
                        IntVar::<T, $bits, $sign>(self.$u(rhs.0.clone()))
                    }
                }
                impl<T, N, const SIGN: bool> $t<IntVar<T, N, SIGN>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    type Output = IntVar<T, $bits, $sign>;
                    fn $u(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
                        IntVar::<T, $bits, $sign>((*self).$u(rhs.0))
                    }
                }
                impl<T, N, const SIGN: bool> $t<&IntVar<T, N, SIGN>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    type Output = IntVar<T, $bits, $sign>;
                    fn $u(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
                        IntVar::<T, $bits, $sign>((*self).$u(rhs.0.clone()))
                    }
                }
            };
        }

        $mselfimm!(false, u8, U8);
        $mselfimm!(false, u16, U16);
        $mselfimm!(false, u32, U32);
        #[cfg(target_pointer_width = "32")]
        $mselfimm!(false, usize, U32);
        #[cfg(target_pointer_width = "64")]
        $mselfimm!(false, usize, U64);
        $mselfimm!(false, u64, U64);
        $mselfimm!(false, u128, U128);

        $mselfimm!(true, i8, U8);
        $mselfimm!(true, i16, U16);
        $mselfimm!(true, i32, U32);
        #[cfg(target_pointer_width = "32")]
        $mselfimm!(true, isize, U32);
        #[cfg(target_pointer_width = "64")]
        $mselfimm!(true, isize, U64);
        $mselfimm!(true, i64, U64);
        $mselfimm!(true, i128, U128);
    };
}

new_shiftop_impl!(Shl, shl, impl_shl_imm);
new_shiftop_selfimm_impl!(Shl, shl, impl_shl_self_imm);
new_shiftop_impl!(Shr, shr, impl_shr_imm);
new_shiftop_selfimm_impl!(Shr, shr, impl_shr_self_imm);
new_shiftop_impl!(IntRol, rotate_left, impl_rol_imm);
new_shiftop_impl!(IntRor, rotate_right, impl_ror_imm);

// CondShifts
macro_rules! new_condshiftop_impl {
    ($t:ident, $u:ident, $mselfimm:ident) => {
        impl<T, N, N2, const SIGN: bool, const SIGN2: bool> $t<IntVar<T, N2, SIGN2>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
            IntExprNode<T, N2, SIGN2>: TryFrom<IntExprNode<T, U64, false>>,
            <IntExprNode<T, N2, SIGN2> as TryFrom<IntExprNode<T, U64, false>>>::Error: Debug,
            IntExprNode<T, N2, SIGN2>: IntOrd<Output = BoolExprNode<T>>,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: IntVar<T, N2, SIGN2>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$u(rhs.0);
                (Self(r), c.into())
            }
        }
        impl<T, N, N2, const SIGN: bool, const SIGN2: bool> $t<&IntVar<T, N2, SIGN2>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
            IntExprNode<T, N2, SIGN2>: TryFrom<IntExprNode<T, U64, false>>,
            <IntExprNode<T, N2, SIGN2> as TryFrom<IntExprNode<T, U64, false>>>::Error: Debug,
            IntExprNode<T, N2, SIGN2>: IntOrd<Output = BoolExprNode<T>>,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &IntVar<T, N2, SIGN2>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$u(rhs.0.clone());
                (Self(r), c.into())
            }
        }
        impl<T, N, N2, const SIGN: bool, const SIGN2: bool> $t<IntVar<T, N2, SIGN2>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
            IntExprNode<T, N2, SIGN2>: TryFrom<IntExprNode<T, U64, false>>,
            <IntExprNode<T, N2, SIGN2> as TryFrom<IntExprNode<T, U64, false>>>::Error: Debug,
            IntExprNode<T, N2, SIGN2>: IntOrd<Output = BoolExprNode<T>>,
        {
            type Output = IntVar<T, N, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: IntVar<T, N2, SIGN2>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$u(rhs.0);
                (IntVar::<T, N, SIGN>(r), c.into())
            }
        }
        impl<T, N, N2, const SIGN: bool, const SIGN2: bool> $t<&IntVar<T, N2, SIGN2>>
            for &IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
            IntExprNode<T, N2, SIGN2>: TryFrom<IntExprNode<T, U64, false>>,
            <IntExprNode<T, N2, SIGN2> as TryFrom<IntExprNode<T, U64, false>>>::Error: Debug,
            IntExprNode<T, N2, SIGN2>: IntOrd<Output = BoolExprNode<T>>,
        {
            type Output = IntVar<T, N, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &IntVar<T, N2, SIGN2>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$u(rhs.0.clone());
                (IntVar::<T, N, SIGN>(r), c.into())
            }
        }

        macro_rules! $mselfimm {
            ($sign:expr, $ty:ty, $bits:ty) => {
                impl<T, N, const SIGN: bool> $t<IntVar<T, N, SIGN>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntExprNode<T, $bits, $sign>: IntConstant<T, $ty>,
                    IntExprNode<T, N, SIGN>: TryFrom<IntExprNode<T, U64, false>>,
                    <IntExprNode<T, N, SIGN> as TryFrom<IntExprNode<T, U64, false>>>::Error: Debug,
                    IntExprNode<T, N, SIGN>: IntOrd<Output = BoolExprNode<T>>,
                {
                    type Output = IntVar<T, $bits, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: IntVar<T, N, SIGN>) -> (Self::Output, Self::OutputCond) {
                        let (r, c) = self.$u(rhs.0);
                        (IntVar::<T, $bits, $sign>(r), c.into())
                    }
                }
                impl<T, N, const SIGN: bool> $t<&IntVar<T, N, SIGN>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntExprNode<T, $bits, $sign>: IntConstant<T, $ty>,
                    IntExprNode<T, N, SIGN>: TryFrom<IntExprNode<T, U64, false>>,
                    <IntExprNode<T, N, SIGN> as TryFrom<IntExprNode<T, U64, false>>>::Error: Debug,
                    IntExprNode<T, N, SIGN>: IntOrd<Output = BoolExprNode<T>>,
                {
                    type Output = IntVar<T, $bits, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &IntVar<T, N, SIGN>) -> (Self::Output, Self::OutputCond) {
                        let (r, c) = self.$u(rhs.0.clone());
                        (IntVar::<T, $bits, $sign>(r), c.into())
                    }
                }
                impl<T, N, const SIGN: bool> $t<IntVar<T, N, SIGN>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntExprNode<T, $bits, $sign>: IntConstant<T, $ty>,
                    IntExprNode<T, N, SIGN>: TryFrom<IntExprNode<T, U64, false>>,
                    <IntExprNode<T, N, SIGN> as TryFrom<IntExprNode<T, U64, false>>>::Error: Debug,
                    IntExprNode<T, N, SIGN>: IntOrd<Output = BoolExprNode<T>>,
                {
                    type Output = IntVar<T, $bits, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: IntVar<T, N, SIGN>) -> (Self::Output, Self::OutputCond) {
                        let (r, c) = (*self).$u(rhs.0);
                        (IntVar::<T, $bits, $sign>(r), c.into())
                    }
                }
                impl<T, N, const SIGN: bool> $t<&IntVar<T, N, SIGN>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntExprNode<T, $bits, $sign>: IntConstant<T, $ty>,
                    IntExprNode<T, N, SIGN>: TryFrom<IntExprNode<T, U64, false>>,
                    <IntExprNode<T, N, SIGN> as TryFrom<IntExprNode<T, U64, false>>>::Error: Debug,
                    IntExprNode<T, N, SIGN>: IntOrd<Output = BoolExprNode<T>>,
                {
                    type Output = IntVar<T, $bits, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &IntVar<T, N, SIGN>) -> (Self::Output, Self::OutputCond) {
                        let (r, c) = (*self).$u(rhs.0.clone());
                        (IntVar::<T, $bits, $sign>(r), c.into())
                    }
                }
            };
        }

        $mselfimm!(false, u8, U8);
        $mselfimm!(false, u16, U16);
        $mselfimm!(false, u32, U32);
        #[cfg(target_pointer_width = "32")]
        $mselfimm!(false, usize, U32);
        #[cfg(target_pointer_width = "64")]
        $mselfimm!(false, usize, U64);
        $mselfimm!(false, u64, U64);
        $mselfimm!(false, u128, U128);

        $mselfimm!(true, i8, U8);
        $mselfimm!(true, i16, U16);
        $mselfimm!(true, i32, U32);
        #[cfg(target_pointer_width = "32")]
        $mselfimm!(true, isize, U32);
        #[cfg(target_pointer_width = "64")]
        $mselfimm!(true, isize, U64);
        $mselfimm!(true, i64, U64);
        $mselfimm!(true, i128, U128);
    };
}

new_condshiftop_impl!(IntCondShl, cond_shl, cond_shl_self_imm);
new_condshiftop_impl!(IntCondShr, cond_shr, cond_shr_self_imm);

// Shift assigns
macro_rules! impl_int_shx_assign {
    ($trait:ident, $op:ident, $op_assign:ident, $macro:ident) => {
        impl<T, N, const SIGN: bool, N2, const SIGN2: bool> $trait<IntVar<T, N2, SIGN2>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
        {
            fn $op_assign(&mut self, rhs: IntVar<T, N2, SIGN2>) {
                *self = self.clone().$op(rhs)
            }
        }
        impl<T, N, const SIGN: bool, N2, const SIGN2: bool> $trait<&IntVar<T, N2, SIGN2>>
            for IntVar<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
        {
            fn $op_assign(&mut self, rhs: &IntVar<T, N2, SIGN2>) {
                *self = self.clone().$op(rhs.clone())
            }
        }

        macro_rules! $macro {
            ($ty:ty) => {
                impl<T, N, const SIGN: bool> $trait<$ty> for IntVar<T, N, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    fn $op_assign(&mut self, rhs: $ty) {
                        *self = self.clone().$op(rhs)
                    }
                }
                impl<T, N, const SIGN: bool> $trait<&$ty> for IntVar<T, N, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                {
                    fn $op_assign(&mut self, rhs: &$ty) {
                        *self = self.clone().$op(*rhs)
                    }
                }
            };
        }

        impl_int_upty!($macro);
        impl_int_ipty!($macro);
    };
}

impl_int_shx_assign!(ShlAssign, shl, shl_assign, impl_int_shl_assign_imm);
impl_int_shx_assign!(ShrAssign, shr, shr_assign, impl_int_shr_assign_imm);

// Fullmul
macro_rules! impl_fullmul_sign {
    ($sign:expr) => {
        impl<T, N> FullMul<IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;

            fn fullmul(self, rhs: Self) -> Self::Output {
                IntVar::<T, operator_aliases::Sum<N, N>, $sign>(self.0.fullmul(rhs.0))
            }
        }
        impl<T, N> FullMul<&IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;

            fn fullmul(self, rhs: &Self) -> Self::Output {
                IntVar::<T, operator_aliases::Sum<N, N>, $sign>(self.0.fullmul(rhs.0.clone()))
            }
        }
        impl<T, N> FullMul<IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;

            fn fullmul(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, operator_aliases::Sum<N, N>, $sign>(self.0.clone().fullmul(rhs.0))
            }
        }
        impl<T, N> FullMul<&IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;

            fn fullmul(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, operator_aliases::Sum<N, N>, $sign>(
                    self.0.clone().fullmul(rhs.0.clone()),
                )
            }
        }
    };
}

impl_fullmul_sign!(false);
impl_fullmul_sign!(true);

macro_rules! impl_int_fullmul_pty {
    ($sign:expr, $pty:ty) => {
        impl<T, N> FullMul<$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;
            fn fullmul(self, rhs: $pty) -> Self::Output {
                self.fullmul(Self::from(rhs))
            }
        }
        impl<T, N> FullMul<&$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;
            fn fullmul(self, rhs: &$pty) -> Self::Output {
                self.fullmul(Self::from(*rhs))
            }
        }
        impl<T, N> FullMul<$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;
            fn fullmul(self, rhs: $pty) -> Self::Output {
                self.fullmul(IntVar::<T, N, $sign>::from(rhs))
            }
        }
        impl<T, N> FullMul<&$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;
            fn fullmul(self, rhs: &$pty) -> Self::Output {
                self.fullmul(IntVar::<T, N, $sign>::from(*rhs))
            }
        }

        impl<T, N> FullMul<IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;
            fn fullmul(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self).fullmul(rhs)
            }
        }
        impl<T, N> FullMul<&IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;
            fn fullmul(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self).fullmul(rhs.clone())
            }
        }
        impl<T, N> FullMul<IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;
            fn fullmul(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).fullmul(rhs)
            }
        }
        impl<T, N> FullMul<&IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize> + Add,
            <N as Add>::Output: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, operator_aliases::Sum<N, N>, $sign>;
            fn fullmul(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).fullmul(rhs.clone())
            }
        }
    };
}

macro_rules! impl_int_fullmul_upty {
    ($pty:ty) => {
        impl_int_fullmul_pty!(false, $pty);
    };
}
macro_rules! impl_int_fullmul_ipty {
    ($pty:ty) => {
        impl_int_fullmul_pty!(true, $pty);
    };
}
impl_int_upty!(impl_int_fullmul_upty);
impl_int_ipty!(impl_int_fullmul_ipty);

// DivMod
macro_rules! impl_divmod_sign {
    ($sign:expr) => {
        impl<T, N> DivMod<IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: Self) -> (Self::Output, Self::Output, Self::OutputCond) {
                let (d, m, c) = self.0.divmod(rhs.0);
                (Self(d), Self(m), c.into())
            }
        }
        impl<T, N> DivMod<&IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: &Self) -> (Self::Output, Self::Output, Self::OutputCond) {
                let (d, m, c) = self.0.divmod(rhs.0.clone());
                (Self(d), Self(m), c.into())
            }
        }
        impl<T, N> DivMod<IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: IntVar<T, N, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                let (d, m, c) = self.0.clone().divmod(rhs.0);
                (IntVar(d), IntVar(m), c.into())
            }
        }
        impl<T, N> DivMod<&IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: &IntVar<T, N, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                let (d, m, c) = self.0.clone().divmod(rhs.0.clone());
                (IntVar(d), IntVar(m), c.into())
            }
        }
    };
}

impl_divmod_sign!(false);
impl_divmod_sign!(true);

macro_rules! impl_int_divmod_pty {
    ($sign:expr, $pty:ty) => {
        impl<T, N> DivMod<$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: $pty) -> (Self::Output, Self::Output, Self::OutputCond) {
                self.divmod(Self::from(rhs))
            }
        }
        impl<T, N> DivMod<&$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: &$pty) -> (Self::Output, Self::Output, Self::OutputCond) {
                self.divmod(Self::from(*rhs))
            }
        }
        impl<T, N> DivMod<$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: $pty) -> (Self::Output, Self::Output, Self::OutputCond) {
                self.divmod(IntVar::<T, N, $sign>::from(rhs))
            }
        }
        impl<T, N> DivMod<&$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: &$pty) -> (Self::Output, Self::Output, Self::OutputCond) {
                self.divmod(IntVar::<T, N, $sign>::from(*rhs))
            }
        }

        impl<T, N> DivMod<IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: IntVar<T, N, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                IntVar::<T, N, $sign>::from(self).divmod(rhs)
            }
        }
        impl<T, N> DivMod<&IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: &IntVar<T, N, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                IntVar::<T, N, $sign>::from(self).divmod(rhs.clone())
            }
        }
        impl<T, N> DivMod<IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: IntVar<T, N, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                IntVar::<T, N, $sign>::from(*self).divmod(rhs)
            }
        }
        impl<T, N> DivMod<&IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = IntVar<T, N, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: &IntVar<T, N, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                IntVar::<T, N, $sign>::from(*self).divmod(rhs.clone())
            }
        }
    };
}

macro_rules! impl_int_divmod_upty {
    ($pty:ty) => {
        impl_int_divmod_pty!(false, $pty);
    };
}
macro_rules! impl_int_divmod_ipty {
    ($pty:ty) => {
        impl_int_divmod_pty!(true, $pty);
    };
}
impl_int_upty!(impl_int_divmod_upty);
impl_int_ipty!(impl_int_divmod_ipty);

// Division and remainder

macro_rules! impl_int_div_mod {
    ($sign:expr) => {
        impl<T, N> Div<IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (Self, BoolVar<T>);
            fn div(self, rhs: Self) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }
        impl<T, N> Div<&IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (Self, BoolVar<T>);
            fn div(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }
        impl<T, N> Div<IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (IntVar<T, N, $sign>, BoolVar<T>);
            fn div(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }
        impl<T, N> Div<&IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (IntVar<T, N, $sign>, BoolVar<T>);
            fn div(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }

        impl<T, N> Rem<IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (Self, BoolVar<T>);
            fn rem(self, rhs: Self) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
        impl<T, N> Rem<&IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (Self, BoolVar<T>);
            fn rem(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
        impl<T, N> Rem<IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (IntVar<T, N, $sign>, BoolVar<T>);
            fn rem(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
        impl<T, N> Rem<&IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (IntVar<T, N, $sign>, BoolVar<T>);
            fn rem(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
    };
}

impl_int_div_mod!(false);
impl_int_div_mod!(true);

macro_rules! impl_int_div_mod_op {
    ($trait:ident, $op:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T, N> $trait<$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = (Self, BoolVar<T>);
                    fn $op(self, rhs: $pty) -> Self::Output {
                        self.$op(Self::from(rhs))
                    }
                }
                impl<T, N> $trait<&$pty> for IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = (Self, BoolVar<T>);
                    fn $op(self, rhs: &$pty) -> Self::Output {
                        self.$op(Self::from(*rhs))
                    }
                }
                impl<T, N> $trait<$pty> for &IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = (IntVar<T, N, $sign>, BoolVar<T>);
                    fn $op(self, rhs: $pty) -> Self::Output {
                        self.$op(IntVar::<T, N, $sign>::from(rhs))
                    }
                }
                impl<T, N> $trait<&$pty> for &IntVar<T, N, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = (IntVar<T, N, $sign>, BoolVar<T>);
                    fn $op(self, rhs: &$pty) -> Self::Output {
                        self.$op(IntVar::<T, N, $sign>::from(*rhs))
                    }
                }

                impl<T, N> $trait<IntVar<T, N, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = (IntVar<T, N, $sign>, BoolVar<T>);
                    fn $op(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(self).$op(rhs)
                    }
                }
                impl<T, N> $trait<&IntVar<T, N, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = (IntVar<T, N, $sign>, BoolVar<T>);
                    fn $op(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(self).$op(rhs)
                    }
                }
                impl<T, N> $trait<IntVar<T, N, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = (IntVar<T, N, $sign>, BoolVar<T>);
                    fn $op(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(*self).$op(rhs)
                    }
                }
                impl<T, N> $trait<&IntVar<T, N, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    N: ArrayLength<usize>,
                    IntVar<T, N, $sign>: From<$pty>,
                {
                    type Output = (IntVar<T, N, $sign>, BoolVar<T>);
                    fn $op(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                        IntVar::<T, N, $sign>::from(*self).$op(rhs)
                    }
                }
            };
        }

        macro_rules! $macro_upty {
            ($pty:ty) => {
                $macro_gen!(false, $pty);
            };
        }
        macro_rules! $macro_ipty {
            ($pty:ty) => {
                $macro_gen!(true, $pty);
            };
        }

        impl_int_upty!($macro_upty);
        impl_int_ipty!($macro_ipty);
    };
}

impl_int_div_mod_op!(Div, div, int_div_pty, int_div_upty, int_div_ipty);
impl_int_div_mod_op!(Rem, rem, int_rem_pty, int_rem_upty, int_rem_ipty);

// Extra arith
impl<T, N, const SIGN: bool> ExtraOps for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;
    type BoolOutput = BoolVar<T>;

    fn count_zeros(self) -> Self::Output {
        Self(self.0.count_zeros())
    }

    fn count_ones(self) -> Self::Output {
        Self(self.0.count_ones())
    }

    fn leading_zeros(self) -> Self::Output {
        Self(self.0.leading_zeros())
    }

    fn leading_ones(self) -> Self::Output {
        Self(self.0.leading_ones())
    }

    fn trailing_zeros(self) -> Self::Output {
        Self(self.0.trailing_zeros())
    }

    fn trailing_ones(self) -> Self::Output {
        Self(self.0.trailing_ones())
    }

    fn is_power_of_two(self) -> Self::BoolOutput {
        self.0.is_power_of_two().into()
    }

    fn reverse_bits(self) -> Self::Output {
        Self(self.0.reverse_bits())
    }
}

impl<T, N, const SIGN: bool> ExtraOps for &IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = IntVar<T, N, SIGN>;
    type BoolOutput = BoolVar<T>;

    fn count_zeros(self) -> Self::Output {
        IntVar(self.0.clone().count_zeros())
    }

    fn count_ones(self) -> Self::Output {
        IntVar(self.0.clone().count_ones())
    }

    fn leading_zeros(self) -> Self::Output {
        IntVar(self.0.clone().leading_zeros())
    }

    fn leading_ones(self) -> Self::Output {
        IntVar(self.0.clone().leading_ones())
    }

    fn trailing_zeros(self) -> Self::Output {
        IntVar(self.0.clone().trailing_zeros())
    }

    fn trailing_ones(self) -> Self::Output {
        IntVar(self.0.clone().trailing_ones())
    }

    fn is_power_of_two(self) -> Self::BoolOutput {
        self.0.clone().is_power_of_two().into()
    }

    fn reverse_bits(self) -> Self::Output {
        IntVar(self.0.clone().reverse_bits())
    }
}
