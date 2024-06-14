// arith.rs - integer expression structures.
//
// cnfgen - Generate the DIMACS CNF formula from operations
// Copyright (C) 2022  Mateusz Szpakowski
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public
// License as published by the Free Software Foundation; either
// version 2.1 of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License along with this library; if not, write to the Free Software
// Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module contains operators definitions.

use std::fmt::Debug;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};
use std::ops::{Div, Rem};
use std::ops::{Mul, MulAssign, Neg, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign};

use super::*;
use crate::VarLit;
use crate::{impl_int_ipty, impl_int_upty};

impl<T> DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Calculation of an absolute value. It returns unsigned expression node.
    pub fn abs(&self) -> DynIntVar<T, false> {
        DynIntVar::<T, false>(self.0.clone().abs())
    }
}

impl<T, const SIGN: bool> Not for DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn not(self) -> Self {
        Self(!self.0)
    }
}

impl<T, const SIGN: bool> Not for &DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, SIGN> as Not>::Output;

    fn not(self) -> Self::Output {
        DynIntVar(!self.0.clone())
    }
}

impl<T> IntModNeg for DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mod_neg(self) -> Self {
        Self((self.0.as_signed().mod_neg()).as_unsigned())
    }
}

impl<T> IntModNeg for &DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, false> as IntModNeg>::Output;

    fn mod_neg(self) -> Self::Output {
        DynIntVar((self.0.clone().as_signed().mod_neg()).as_unsigned())
    }
}

impl<T> IntModNeg for DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mod_neg(self) -> Self {
        Self(self.0.mod_neg())
    }
}

impl<T> IntModNeg for &DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, true> as IntModNeg>::Output;

    fn mod_neg(self) -> Self::Output {
        DynIntVar(self.0.clone().mod_neg())
    }
}

impl<T> Neg for DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn neg(self) -> Self {
        Self((self.0.as_signed().mod_neg()).as_unsigned())
    }
}

impl<T> Neg for &DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, false> as Neg>::Output;

    fn neg(self) -> Self::Output {
        DynIntVar((self.0.clone().as_signed().mod_neg()).as_unsigned())
    }
}

impl<T> Neg for DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn neg(self) -> Self {
        Self(self.0.mod_neg())
    }
}

impl<T> Neg for &DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, true> as Neg>::Output;

    fn neg(self) -> Self::Output {
        DynIntVar(self.0.clone().mod_neg())
    }
}

impl<T> IntCondNeg for DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolVar<T>;

    fn cond_neg(self) -> (Self::Output, Self::OutputCond) {
        let (r, c) = self.0.cond_neg();
        (Self(r), c.into())
    }
}

impl<T> IntCondNeg for &DynIntVar<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = <DynIntVar<T, true> as IntCondNeg>::Output;
    type OutputCond = <DynIntVar<T, true> as IntCondNeg>::OutputCond;

    fn cond_neg(self) -> (Self::Output, Self::OutputCond) {
        let (r, c) = self.0.clone().cond_neg();
        (DynIntVar(r), c.into())
    }
}

//////////
// Add/Sub implementation

impl<T, const SIGN: bool> DynIntVar<T, SIGN>
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
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: DynIntVar<T, SIGN>) -> Self::Output {
                Self(self.0.$v(rhs.0))
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: &DynIntVar<T, SIGN>) -> Self::Output {
                Self(self.0.$v(rhs.0.clone()))
            }
        }
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: DynIntVar<T, SIGN>) -> Self::Output {
                DynIntVar::<T, SIGN>(self.0.clone().$v(rhs.0))
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: &DynIntVar<T, SIGN>) -> Self::Output {
                DynIntVar::<T, SIGN>(self.0.clone().$v(rhs.0.clone()))
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T> $t<$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: $pty) -> Self::Output {
                        let r = self.constant(rhs);
                        self.$u(r)
                    }
                }
                impl<T> $t<&$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &$pty) -> Self::Output {
                        let r = self.constant(*rhs);
                        self.$u(r)
                    }
                }
                impl<T> $t<$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: $pty) -> Self::Output {
                        self.$u(self.constant(rhs))
                    }
                }
                impl<T> $t<&$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &$pty) -> Self::Output {
                        self.$u(self.constant(*rhs))
                    }
                }

                impl<T> $t<DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(self).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(self).$u(rhs)
                    }
                }
                impl<T> $t<DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(*self).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(*self).$u(rhs)
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
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $u(&mut self, rhs: DynIntVar<T, SIGN>) {
                self.0.$v(rhs.0);
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $u(&mut self, rhs: &DynIntVar<T, SIGN>) {
                self.0.$v(rhs.0.clone());
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T> $t<$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    fn $u(&mut self, rhs: $pty) {
                        self.$u(self.constant(rhs));
                    }
                }
                impl<T> $t<&$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    fn $u(&mut self, rhs: &$pty) {
                        self.$u(self.constant(*rhs));
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
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: DynIntVar<T, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$v(rhs.0);
                (DynIntVar(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &DynIntVar<T, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$v(rhs.0.clone());
                (DynIntVar(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: DynIntVar<T, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$v(rhs.0);
                (DynIntVar(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &DynIntVar<T, SIGN>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$v(rhs.0.clone());
                (DynIntVar(r), c.into())
            }
        }

        macro_rules! $macro_gen {
            ($sign:expr, $pty:ty) => {
                impl<T> $t<$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                        let r = self.constant(rhs);
                        self.$u(r)
                    }
                }
                impl<T> $t<&$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                        let r = self.constant(*rhs);
                        self.$u(r)
                    }
                }
                impl<T> $t<$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                        self.$u(self.constant(rhs))
                    }
                }
                impl<T> $t<&$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                        self.$u(self.constant(*rhs))
                    }
                }

                impl<T> $t<DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                        rhs.constant(self).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                        rhs.constant(self).$u(rhs)
                    }
                }
                impl<T> $t<DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                        rhs.constant(*self).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                        rhs.constant(*self).$u(rhs)
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
        impl<T> IntCondMul<DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.cond_mul(rhs.0);
                (DynIntVar(r), c.into())
            }
        }
        impl<T> IntCondMul<&DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.cond_mul(rhs.0.clone());
                (DynIntVar(r), c.into())
            }
        }
        impl<T> IntCondMul<DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().cond_mul(rhs.0);
                (DynIntVar(r), c.into())
            }
        }
        impl<T> IntCondMul<&DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().cond_mul(rhs.0.clone());
                (DynIntVar(r), c.into())
            }
        }
    };
}

condmul_varvar!(false);
condmul_varvar!(true);

macro_rules! condmul_gen {
    ($sign:expr, $pty:ty) => {
        impl<T> IntCondMul<$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                let r = self.constant(rhs);
                self.cond_mul(r)
            }
        }
        impl<T> IntCondMul<&$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                let r = self.constant(*rhs);
                self.cond_mul(r)
            }
        }
        impl<T> IntCondMul<$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: $pty) -> (Self::Output, Self::OutputCond) {
                self.cond_mul(self.constant(rhs))
            }
        }
        impl<T> IntCondMul<&$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &$pty) -> (Self::Output, Self::OutputCond) {
                self.cond_mul(self.constant(*rhs))
            }
        }

        impl<T> IntCondMul<DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                rhs.constant(self).cond_mul(rhs)
            }
        }
        impl<T> IntCondMul<&DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                rhs.constant(self).cond_mul(rhs)
            }
        }
        impl<T> IntCondMul<DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                rhs.constant(*self).cond_mul(rhs)
            }
        }
        impl<T> IntCondMul<&DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn cond_mul(self, rhs: &DynIntVar<T, $sign>) -> (Self::Output, Self::OutputCond) {
                rhs.constant(*self).cond_mul(rhs)
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

// shifts

// Shifts
macro_rules! new_shiftop_impl {
    ($t:ident, $u:ident) => {
        impl<T, const SIGN: bool, const SIGN2: bool> $t<DynIntVar<T, SIGN2>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = Self;
            fn $u(self, rhs: DynIntVar<T, SIGN2>) -> Self::Output {
                Self(self.0.$u(rhs.0))
            }
        }
        impl<T, const SIGN: bool, const SIGN2: bool> $t<&DynIntVar<T, SIGN2>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = Self;
            fn $u(self, rhs: &DynIntVar<T, SIGN2>) -> Self::Output {
                Self(self.0.$u(rhs.0.clone()))
            }
        }
        impl<T, const SIGN: bool, const SIGN2: bool> $t<DynIntVar<T, SIGN2>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: DynIntVar<T, SIGN2>) -> Self::Output {
                DynIntVar::<T, SIGN>(self.0.clone().$u(rhs.0))
            }
        }
        impl<T, const SIGN: bool, const SIGN2: bool> $t<&DynIntVar<T, SIGN2>>
            for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, SIGN>;
            fn $u(self, rhs: &DynIntVar<T, SIGN2>) -> Self::Output {
                DynIntVar::<T, SIGN>(self.0.clone().$u(rhs.0.clone()))
            }
        }
    };
}

new_shiftop_impl!(Shl, shl);
new_shiftop_impl!(Shr, shr);
new_shiftop_impl!(IntRol, rotate_left);
new_shiftop_impl!(IntRor, rotate_right);

macro_rules! new_shiftop_selfimm_impl {
    ($t:ident, $u:ident, $mselfimm:ident) => {
        macro_rules! $mselfimm {
            ($sign:expr, $ty:ty, $bits:expr) => {
                impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: DynIntVar<T, SIGN>) -> Self::Output {
                        DynIntVar::<T, $sign>::from_n(self, $bits).$u(rhs)
                    }
                }
                impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &DynIntVar<T, SIGN>) -> Self::Output {
                        DynIntVar::<T, $sign>::from_n(self, $bits).$u(rhs.clone())
                    }
                }
                impl<T, const SIGN: bool> $t<DynIntVar<T, SIGN>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: DynIntVar<T, SIGN>) -> Self::Output {
                        DynIntVar::<T, $sign>::from_n(*self, $bits).$u(rhs)
                    }
                }
                impl<T, const SIGN: bool> $t<&DynIntVar<T, SIGN>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                {
                    type Output = DynIntVar<T, $sign>;
                    fn $u(self, rhs: &DynIntVar<T, SIGN>) -> Self::Output {
                        DynIntVar::<T, $sign>::from_n(*self, $bits).$u(rhs.clone())
                    }
                }
            };
        }

        $mselfimm!(false, u8, 8);
        $mselfimm!(false, u16, 16);
        $mselfimm!(false, u32, 32);
        #[cfg(target_pointer_width = "32")]
        $mselfimm!(false, usize, 32);
        #[cfg(target_pointer_width = "64")]
        $mselfimm!(false, usize, 64);
        $mselfimm!(false, u64, 64);
        $mselfimm!(false, u128, 128);

        $mselfimm!(true, i8, 8);
        $mselfimm!(true, i16, 16);
        $mselfimm!(true, i32, 32);
        #[cfg(target_pointer_width = "32")]
        $mselfimm!(true, isize, 32);
        #[cfg(target_pointer_width = "64")]
        $mselfimm!(true, isize, 64);
        $mselfimm!(true, i64, 64);
        $mselfimm!(true, i128, 128);
    };
}

new_shiftop_selfimm_impl!(Shl, shl, impl_shl_self_imm);
new_shiftop_selfimm_impl!(Shr, shr, impl_shr_self_imm);

// shift imm

macro_rules! impl_int_shl_imm {
    ($ty:ty) => {
        impl<T, const SIGN: bool> Shl<$ty> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = Self;
            fn shl(self, rhs: $ty) -> Self::Output {
                let n = self.bitnum();
                // check whether zeroes
                #[allow(unused_comparisons)]
                if rhs < 0 || (rhs as usize) >= n {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                DynIntVar::from_iter(
                    std::iter::repeat(false.into())
                        .take(usize_rhs)
                        .chain(self.iter().take(n - usize_rhs)),
                )
            }
        }
        impl<T, const SIGN: bool> Shl<&$ty> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = Self;
            fn shl(self, rhs: &$ty) -> Self::Output {
                self << *rhs
            }
        }
        impl<T, const SIGN: bool> Shl<$ty> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = DynIntVar<T, SIGN>;
            fn shl(self, rhs: $ty) -> Self::Output {
                self.clone() << rhs
            }
        }
        impl<T, const SIGN: bool> Shl<&$ty> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = DynIntVar<T, SIGN>;
            fn shl(self, rhs: &$ty) -> Self::Output {
                self.clone() << *rhs
            }
        }
    };
}

impl_int_upty!(impl_int_shl_imm);
impl_int_ipty!(impl_int_shl_imm);

macro_rules! impl_int_shr_imm {
    ($ty:ty) => {
        impl<T, const SIGN: bool> Shr<$ty> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = Self;
            fn shr(self, rhs: $ty) -> Self::Output {
                let n = self.bitnum();
                // check whether zeroes
                #[allow(unused_comparisons)]
                if rhs < 0 || (rhs as usize) >= n {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                DynIntVar::from_iter(
                    self.iter().skip(usize_rhs).chain(
                        std::iter::repeat(if SIGN { self.bit(n - 1) } else { false.into() })
                            .take(n - usize_rhs),
                    ),
                )
            }
        }
        impl<T, const SIGN: bool> Shr<&$ty> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = Self;
            fn shr(self, rhs: &$ty) -> Self::Output {
                self >> *rhs
            }
        }
        impl<T, const SIGN: bool> Shr<$ty> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = DynIntVar<T, SIGN>;
            fn shr(self, rhs: $ty) -> Self::Output {
                self.clone() >> rhs
            }
        }
        impl<T, const SIGN: bool> Shr<&$ty> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = DynIntVar<T, SIGN>;
            fn shr(self, rhs: &$ty) -> Self::Output {
                self.clone() >> *rhs
            }
        }
    };
}

impl_int_upty!(impl_int_shr_imm);
impl_int_ipty!(impl_int_shr_imm);

macro_rules! impl_int_rol_imm {
    ($ty:ty) => {
        impl<T, const SIGN: bool> IntRol<$ty> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = Self;
            fn rotate_left(self, rhs: $ty) -> Self::Output {
                let n = self.bitnum();
                // check whether zeroes
                #[allow(unused_comparisons)]
                if rhs < 0 || (rhs as usize) >= n {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                DynIntVar::from_iter(
                    self.iter()
                        .skip(n - usize_rhs)
                        .chain(self.iter().take(n - usize_rhs)),
                )
            }
        }
        impl<T, const SIGN: bool> IntRol<&$ty> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = Self;
            fn rotate_left(self, rhs: &$ty) -> Self::Output {
                self.rotate_left(*rhs)
            }
        }
        impl<T, const SIGN: bool> IntRol<$ty> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = DynIntVar<T, SIGN>;
            fn rotate_left(self, rhs: $ty) -> Self::Output {
                self.clone().rotate_left(rhs)
            }
        }
        impl<T, const SIGN: bool> IntRol<&$ty> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = DynIntVar<T, SIGN>;
            fn rotate_left(self, rhs: &$ty) -> Self::Output {
                self.clone().rotate_left(*rhs)
            }
        }
    };
}

impl_int_upty!(impl_int_rol_imm);
impl_int_ipty!(impl_int_rol_imm);

macro_rules! impl_int_ror_imm {
    ($ty:ty) => {
        impl<T, const SIGN: bool> IntRor<$ty> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = Self;
            fn rotate_right(self, rhs: $ty) -> Self::Output {
                let n = self.bitnum();
                // check whether zeroes
                #[allow(unused_comparisons)]
                if rhs < 0 || (rhs as usize) >= n {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                DynIntVar::from_iter(
                    self.iter()
                        .skip(usize_rhs)
                        .chain(self.iter().take(usize_rhs)),
                )
            }
        }
        impl<T, const SIGN: bool> IntRor<&$ty> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = Self;
            fn rotate_right(self, rhs: &$ty) -> Self::Output {
                self.rotate_right(*rhs)
            }
        }
        impl<T, const SIGN: bool> IntRor<$ty> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = DynIntVar<T, SIGN>;
            fn rotate_right(self, rhs: $ty) -> Self::Output {
                self.clone().rotate_right(rhs)
            }
        }
        impl<T, const SIGN: bool> IntRor<&$ty> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            BoolVar<T>: From<bool>,
        {
            type Output = DynIntVar<T, SIGN>;
            fn rotate_right(self, rhs: &$ty) -> Self::Output {
                self.clone().rotate_right(*rhs)
            }
        }
    };
}

impl_int_upty!(impl_int_ror_imm);
impl_int_ipty!(impl_int_ror_imm);

// CondShifts
macro_rules! new_condshiftop_impl {
    ($t:ident, $u:ident, $mselfimm:ident) => {
        impl<T, const SIGN: bool> $t<DynIntVar<T, false>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: DynIntVar<T, false>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$u(rhs.0);
                (Self(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, false>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &DynIntVar<T, false>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$u(rhs.0.clone());
                (Self(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<DynIntVar<T, false>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: DynIntVar<T, false>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$u(rhs.0);
                (DynIntVar::<T, SIGN>(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, false>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &DynIntVar<T, false>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$u(rhs.0.clone());
                (DynIntVar::<T, SIGN>(r), c.into())
            }
        }

        impl<T, const SIGN: bool> $t<DynIntVar<T, true>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: DynIntVar<T, true>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$u(rhs.0);
                (Self(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, true>> for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &DynIntVar<T, true>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.$u(rhs.0.clone());
                (Self(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<DynIntVar<T, true>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: DynIntVar<T, true>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$u(rhs.0);
                (DynIntVar::<T, SIGN>(r), c.into())
            }
        }
        impl<T, const SIGN: bool> $t<&DynIntVar<T, true>> for &DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
        {
            type Output = DynIntVar<T, SIGN>;
            type OutputCond = BoolVar<T>;
            fn $u(self, rhs: &DynIntVar<T, true>) -> (Self::Output, Self::OutputCond) {
                let (r, c) = self.0.clone().$u(rhs.0.clone());
                (DynIntVar::<T, SIGN>(r), c.into())
            }
        }

        macro_rules! $mselfimm {
            ($sign:expr, $ty:ty, $bits:expr) => {
                impl<T> $t<DynIntVar<T, false>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                    DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: DynIntVar<T, false>) -> (Self::Output, Self::OutputCond) {
                        DynIntVar::<T, $sign>::from_n(self, $bits).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, false>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                    DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &DynIntVar<T, false>) -> (Self::Output, Self::OutputCond) {
                        DynIntVar::<T, $sign>::from_n(self, $bits).$u(rhs.clone())
                    }
                }
                impl<T> $t<DynIntVar<T, false>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                    DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: DynIntVar<T, false>) -> (Self::Output, Self::OutputCond) {
                        DynIntVar::<T, $sign>::from_n(*self, $bits).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, false>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                    DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &DynIntVar<T, false>) -> (Self::Output, Self::OutputCond) {
                        DynIntVar::<T, $sign>::from_n(*self, $bits).$u(rhs.clone())
                    }
                }

                impl<T> $t<DynIntVar<T, true>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                    DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: DynIntVar<T, true>) -> (Self::Output, Self::OutputCond) {
                        DynIntVar::<T, $sign>::from_n(self, $bits).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, true>> for $ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                    DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &DynIntVar<T, true>) -> (Self::Output, Self::OutputCond) {
                        DynIntVar::<T, $sign>::from_n(self, $bits).$u(rhs.clone())
                    }
                }
                impl<T> $t<DynIntVar<T, true>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                    DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: DynIntVar<T, true>) -> (Self::Output, Self::OutputCond) {
                        DynIntVar::<T, $sign>::from_n(*self, $bits).$u(rhs)
                    }
                }
                impl<T> $t<&DynIntVar<T, true>> for &$ty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: FromNSized<$ty>,
                    DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
                {
                    type Output = DynIntVar<T, $sign>;
                    type OutputCond = BoolVar<T>;
                    fn $u(self, rhs: &DynIntVar<T, true>) -> (Self::Output, Self::OutputCond) {
                        DynIntVar::<T, $sign>::from_n(*self, $bits).$u(rhs.clone())
                    }
                }
            };
        }

        $mselfimm!(false, u8, 8);
        $mselfimm!(false, u16, 16);
        $mselfimm!(false, u32, 32);
        #[cfg(target_pointer_width = "32")]
        $mselfimm!(false, usize, 32);
        #[cfg(target_pointer_width = "64")]
        $mselfimm!(false, usize, 64);
        $mselfimm!(false, u64, 64);
        $mselfimm!(false, u128, 128);

        $mselfimm!(true, i8, 8);
        $mselfimm!(true, i16, 16);
        $mselfimm!(true, i32, 32);
        #[cfg(target_pointer_width = "32")]
        $mselfimm!(true, isize, 32);
        #[cfg(target_pointer_width = "64")]
        $mselfimm!(true, isize, 64);
        $mselfimm!(true, i64, 64);
        $mselfimm!(true, i128, 128);
    };
}

new_condshiftop_impl!(IntCondShl, cond_shl, cond_shl_self_imm);
new_condshiftop_impl!(IntCondShr, cond_shr, cond_shr_self_imm);

// Shift assigns
macro_rules! impl_int_shx_assign {
    ($trait:ident, $op:ident, $op_assign:ident, $macro:ident) => {
        impl<T, const SIGN: bool, const SIGN2: bool> $trait<DynIntVar<T, SIGN2>>
            for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $op_assign(&mut self, rhs: DynIntVar<T, SIGN2>) {
                *self = self.clone().$op(rhs)
            }
        }
        impl<T, const SIGN: bool, const SIGN2: bool> $trait<&DynIntVar<T, SIGN2>>
            for DynIntVar<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $op_assign(&mut self, rhs: &DynIntVar<T, SIGN2>) {
                *self = self.clone().$op(rhs.clone())
            }
        }

        macro_rules! $macro {
            ($ty:ty) => {
                impl<T, const SIGN: bool> $trait<$ty> for DynIntVar<T, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    BoolVar<T>: From<bool>,
                {
                    fn $op_assign(&mut self, rhs: $ty) {
                        *self = self.clone().$op(rhs)
                    }
                }
                impl<T, const SIGN: bool> $trait<&$ty> for DynIntVar<T, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    BoolVar<T>: From<bool>,
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

// shifts

// Fullmul
macro_rules! impl_fullmul_sign {
    ($sign:expr) => {
        impl<T> FullMul<DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;

            fn fullmul(self, rhs: Self) -> Self::Output {
                DynIntVar::<T, $sign>(self.0.fullmul(rhs.0))
            }
        }
        impl<T> FullMul<&DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;

            fn fullmul(self, rhs: &Self) -> Self::Output {
                DynIntVar::<T, $sign>(self.0.fullmul(rhs.0.clone()))
            }
        }
        impl<T> FullMul<DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;

            fn fullmul(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                DynIntVar::<T, $sign>(self.0.clone().fullmul(rhs.0))
            }
        }
        impl<T> FullMul<&DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;

            fn fullmul(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                DynIntVar::<T, $sign>(self.0.clone().fullmul(rhs.0.clone()))
            }
        }
    };
}

impl_fullmul_sign!(false);
impl_fullmul_sign!(true);

macro_rules! impl_int_fullmul_pty {
    ($sign:expr, $pty:ty) => {
        impl<T> FullMul<$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            fn fullmul(self, rhs: $pty) -> Self::Output {
                let r = self.constant(rhs);
                self.fullmul(r)
            }
        }
        impl<T> FullMul<&$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            fn fullmul(self, rhs: &$pty) -> Self::Output {
                let r = self.constant(*rhs);
                self.fullmul(r)
            }
        }
        impl<T> FullMul<$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            fn fullmul(self, rhs: $pty) -> Self::Output {
                self.fullmul(self.constant(rhs))
            }
        }
        impl<T> FullMul<&$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            fn fullmul(self, rhs: &$pty) -> Self::Output {
                self.fullmul(self.constant(*rhs))
            }
        }

        impl<T> FullMul<DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            fn fullmul(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self).fullmul(rhs)
            }
        }
        impl<T> FullMul<&DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            fn fullmul(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self).fullmul(rhs.clone())
            }
        }
        impl<T> FullMul<DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            fn fullmul(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).fullmul(rhs)
            }
        }
        impl<T> FullMul<&DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            fn fullmul(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).fullmul(rhs.clone())
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
        impl<T> DivMod<DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: Self) -> (Self::Output, Self::Output, Self::OutputCond) {
                let (d, m, c) = self.0.divmod(rhs.0);
                (Self(d), Self(m), c.into())
            }
        }
        impl<T> DivMod<&DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = Self;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: &Self) -> (Self::Output, Self::Output, Self::OutputCond) {
                let (d, m, c) = self.0.divmod(rhs.0.clone());
                (Self(d), Self(m), c.into())
            }
        }
        impl<T> DivMod<DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: DynIntVar<T, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                let (d, m, c) = self.0.clone().divmod(rhs.0);
                (DynIntVar(d), DynIntVar(m), c.into())
            }
        }
        impl<T> DivMod<&DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: &DynIntVar<T, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                let (d, m, c) = self.0.clone().divmod(rhs.0.clone());
                (DynIntVar(d), DynIntVar(m), c.into())
            }
        }
    };
}

impl_divmod_sign!(false);
impl_divmod_sign!(true);

macro_rules! impl_int_divmod_pty {
    ($sign:expr, $pty:ty) => {
        impl<T> DivMod<$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: $pty) -> (Self::Output, Self::Output, Self::OutputCond) {
                let r = self.constant(rhs);
                self.divmod(r)
            }
        }
        impl<T> DivMod<&$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: &$pty) -> (Self::Output, Self::Output, Self::OutputCond) {
                let r = self.constant(*rhs);
                self.divmod(r)
            }
        }
        impl<T> DivMod<$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: $pty) -> (Self::Output, Self::Output, Self::OutputCond) {
                self.divmod(self.constant(rhs))
            }
        }
        impl<T> DivMod<&$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(self, rhs: &$pty) -> (Self::Output, Self::Output, Self::OutputCond) {
                self.divmod(self.constant(*rhs))
            }
        }

        impl<T> DivMod<DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: DynIntVar<T, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                rhs.constant(self).divmod(rhs)
            }
        }
        impl<T> DivMod<&DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: &DynIntVar<T, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                rhs.constant(self).divmod(rhs.clone())
            }
        }
        impl<T> DivMod<DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: DynIntVar<T, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                rhs.constant(*self).divmod(rhs)
            }
        }
        impl<T> DivMod<&DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = DynIntVar<T, $sign>;
            type OutputCond = BoolVar<T>;
            fn divmod(
                self,
                rhs: &DynIntVar<T, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                rhs.constant(*self).divmod(rhs.clone())
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
        impl<T> Div<DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (Self, BoolVar<T>);
            fn div(self, rhs: Self) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }
        impl<T> Div<&DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (Self, BoolVar<T>);
            fn div(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }
        impl<T> Div<DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (DynIntVar<T, $sign>, BoolVar<T>);
            fn div(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }
        impl<T> Div<&DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (DynIntVar<T, $sign>, BoolVar<T>);
            fn div(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }

        impl<T> Rem<DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (Self, BoolVar<T>);
            fn rem(self, rhs: Self) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
        impl<T> Rem<&DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (Self, BoolVar<T>);
            fn rem(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
        impl<T> Rem<DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (DynIntVar<T, $sign>, BoolVar<T>);
            fn rem(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
        impl<T> Rem<&DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (DynIntVar<T, $sign>, BoolVar<T>);
            fn rem(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
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
                impl<T> $trait<$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = (Self, BoolVar<T>);
                    fn $op(self, rhs: $pty) -> Self::Output {
                        let r = self.constant(rhs);
                        self.$op(r)
                    }
                }
                impl<T> $trait<&$pty> for DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = (Self, BoolVar<T>);
                    fn $op(self, rhs: &$pty) -> Self::Output {
                        let r = self.constant(*rhs);
                        self.$op(r)
                    }
                }
                impl<T> $trait<$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = (DynIntVar<T, $sign>, BoolVar<T>);
                    fn $op(self, rhs: $pty) -> Self::Output {
                        self.$op(self.constant(rhs))
                    }
                }
                impl<T> $trait<&$pty> for &DynIntVar<T, $sign>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = (DynIntVar<T, $sign>, BoolVar<T>);
                    fn $op(self, rhs: &$pty) -> Self::Output {
                        self.$op(self.constant(*rhs))
                    }
                }

                impl<T> $trait<DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = (DynIntVar<T, $sign>, BoolVar<T>);
                    fn $op(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(self).$op(rhs)
                    }
                }
                impl<T> $trait<&DynIntVar<T, $sign>> for $pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = (DynIntVar<T, $sign>, BoolVar<T>);
                    fn $op(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(self).$op(rhs)
                    }
                }
                impl<T> $trait<DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = (DynIntVar<T, $sign>, BoolVar<T>);
                    fn $op(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(*self).$op(rhs)
                    }
                }
                impl<T> $trait<&DynIntVar<T, $sign>> for &$pty
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                    DynIntVar<T, $sign>: SelfConstant<$pty>,
                {
                    type Output = (DynIntVar<T, $sign>, BoolVar<T>);
                    fn $op(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                        rhs.constant(*self).$op(rhs)
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
impl<T, const SIGN: bool> ExtraOps for DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
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

impl<T, const SIGN: bool> ExtraOps for &DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = DynIntVar<T, SIGN>;
    type BoolOutput = BoolVar<T>;

    fn count_zeros(self) -> Self::Output {
        DynIntVar(self.0.clone().count_zeros())
    }

    fn count_ones(self) -> Self::Output {
        DynIntVar(self.0.clone().count_ones())
    }

    fn leading_zeros(self) -> Self::Output {
        DynIntVar(self.0.clone().leading_zeros())
    }

    fn leading_ones(self) -> Self::Output {
        DynIntVar(self.0.clone().leading_ones())
    }

    fn trailing_zeros(self) -> Self::Output {
        DynIntVar(self.0.clone().trailing_zeros())
    }

    fn trailing_ones(self) -> Self::Output {
        DynIntVar(self.0.clone().trailing_ones())
    }

    fn is_power_of_two(self) -> Self::BoolOutput {
        self.0.clone().is_power_of_two().into()
    }

    fn reverse_bits(self) -> Self::Output {
        DynIntVar(self.0.clone().reverse_bits())
    }
}
