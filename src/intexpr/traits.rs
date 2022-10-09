// traits.rs - integer expression structures.
//
// cnfgen - Generate the DIMACS CNF formulae from operations
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
//! The module to generate CNF clauses from integer expressions.

use std::cell::RefCell;
use std::fmt::Debug;
use std::iter;
use std::ops::Neg;
use std::rc::Rc;

use generic_array::typenum::*;
use generic_array::*;

use super::*;
use crate::{impl_int_ipty, impl_int_ipty_ty1, impl_int_upty, impl_int_upty_ty1};
use crate::{BoolEqual, BoolExprNode, BoolImpl, ExprCreator, VarLit};

/// Equality operator for boolean expressions and boolean words.
pub trait IntEqual<Rhs = Self> {
    type Output;

    fn equal(self, rhs: Rhs) -> Self::Output;
    fn nequal(self, rhs: Rhs) -> Self::Output;
}

/// Equality operator for integers.
macro_rules! int_equal_impl {
    ($t: ty) => {
        impl IntEqual for $t {
            type Output = bool;

            fn equal(self, rhs: $t) -> bool {
                self == rhs
            }
            fn nequal(self, rhs: $t) -> bool {
                self != rhs
            }
        }
    };
}

impl_int_upty!(int_equal_impl);
impl_int_ipty!(int_equal_impl);

pub trait IntOrd<Rhs = Self> {
    type Output;

    fn less_than(self, rhs: Rhs) -> Self::Output;
    fn less_equal(self, rhs: Rhs) -> Self::Output;
    fn greater_than(self, rhs: Rhs) -> Self::Output;
    fn greater_equal(self, rhs: Rhs) -> Self::Output;
}

/// Equality operator for integers.
macro_rules! int_ord_impl {
    ($t: ty) => {
        impl IntOrd for $t {
            type Output = bool;

            fn less_than(self, rhs: $t) -> bool {
                self < rhs
            }
            fn less_equal(self, rhs: $t) -> bool {
                self <= rhs
            }
            fn greater_than(self, rhs: $t) -> bool {
                self > rhs
            }
            fn greater_equal(self, rhs: $t) -> bool {
                self >= rhs
            }
        }
    };
}

impl_int_upty!(int_ord_impl);
impl_int_ipty!(int_ord_impl);

pub trait IntConstant<T: VarLit, U> {
    fn constant(creator: Rc<RefCell<ExprCreator<T>>>, v: U) -> Self;
}

pub trait BitVal {
    type Output;

    fn bitnum(self) -> usize;
    fn bit(self, n: usize) -> Self::Output;
}

macro_rules! impl_int_bitval_upty {
    ($pty:ty) => {
        impl BitVal for $pty {
            type Output = bool;

            #[inline]
            fn bitnum(self) -> usize {
                <$pty>::BITS as usize
            }

            #[inline]
            fn bit(self, x: usize) -> Self::Output {
                if x < <$pty>::BITS as usize {
                    ((self & (1 << x)) != 0)
                } else {
                    false
                }
            }
        }
    };
}

impl_int_upty!(impl_int_bitval_upty);

macro_rules! impl_int_bitval_ipty {
    ($pty:ty) => {
        impl BitVal for $pty {
            type Output = bool;

            #[inline]
            fn bitnum(self) -> usize {
                <$pty>::BITS as usize
            }

            #[inline]
            fn bit(self, x: usize) -> Self::Output {
                if x < <$pty>::BITS as usize {
                    ((self & (1 << x)) != 0)
                } else {
                    ((self & (1 << ((<$pty>::BITS - 1) as usize))) != 0)
                }
            }
        }
    };
}

impl_int_ipty!(impl_int_bitval_ipty);

pub trait BitMask<T> {
    fn bitmask(bit: T) -> Self;
}

macro_rules! impl_int_bitmask_pty {
    ($pty:ty) => {
        impl BitMask<bool> for $pty {
            fn bitmask(bit: bool) -> Self {
                // if signed: sign (MIN) and max-positive -> enable all bits
                // if unsigned: MIN is zero
                if bit {
                    Self::MAX | Self::MIN
                } else {
                    0
                }
            }
        }
    };
}

impl_int_upty!(impl_int_bitmask_pty);
impl_int_ipty!(impl_int_bitmask_pty);

pub trait FullMul<Rhs = Self> {
    type Output;

    fn fullmul(self, rhs: Rhs) -> Self::Output;
}

macro_rules! impl_int_fullmul_pty_pty_simple {
    ($pty:ty, $opty:ty) => {
        impl FullMul for $pty {
            type Output = $opty;

            fn fullmul(self, rhs: Self) -> Self::Output {
                let biga = <$opty>::try_from(self).unwrap();
                let bigb = <$opty>::try_from(rhs).unwrap();
                biga * bigb
            }
        }
    };
}

impl_int_fullmul_pty_pty_simple!(u8, u16);
impl_int_fullmul_pty_pty_simple!(u16, u32);
impl_int_fullmul_pty_pty_simple!(u32, u64);
#[cfg(target_pointer_width = "32")]
impl_int_fullmul_pty_pty_simple!(usize, u64);
#[cfg(target_pointer_width = "64")]
impl_int_fullmul_pty_pty_simple!(usize, u128);
impl_int_fullmul_pty_pty_simple!(u64, u128);
impl_int_fullmul_pty_pty_simple!(i8, i16);
impl_int_fullmul_pty_pty_simple!(i16, i32);
impl_int_fullmul_pty_pty_simple!(i32, i64);
#[cfg(target_pointer_width = "32")]
impl_int_fullmul_pty_pty_simple!(isize, i64);
#[cfg(target_pointer_width = "64")]
impl_int_fullmul_pty_pty_simple!(isize, i128);
impl_int_fullmul_pty_pty_simple!(i64, i128);

pub trait DivMod<Rhs = Self> {
    type Output;
    type OutputCond;

    fn divmod(self, rhs: Rhs) -> (Self::Output, Self::Output, Self::OutputCond);
}

macro_rules! impl_int_divmod_pty_pty {
    ($pty:ty) => {
        impl DivMod for $pty {
            type Output = $pty;
            type OutputCond = bool;

            fn divmod(self, rhs: Self) -> (Self::Output, Self::Output, Self::OutputCond) {
                if let Some(divres) = self.checked_div(rhs) {
                    (divres, self % rhs, true)
                } else {
                    (0, 0, false)
                }
            }
        }
    };
}

impl_int_upty!(impl_int_divmod_pty_pty);
impl_int_ipty!(impl_int_divmod_pty_pty);

pub trait IntModAdd<Rhs = Self> {
    type Output;

    fn mod_add(self, rhs: Rhs) -> Self::Output;
}

pub trait IntModSub<Rhs = Self> {
    type Output;

    fn mod_sub(self, rhs: Rhs) -> Self::Output;
}

pub trait IntModMul<Rhs = Self> {
    type Output;

    fn mod_mul(self, rhs: Rhs) -> Self::Output;
}

pub trait IntModAddAssign<Rhs = Self> {
    fn mod_add_assign(&mut self, rhs: Rhs);
}

pub trait IntModSubAssign<Rhs = Self> {
    fn mod_sub_assign(&mut self, rhs: Rhs);
}

pub trait IntModMulAssign<Rhs = Self> {
    fn mod_mul_assign(&mut self, rhs: Rhs);
}

macro_rules! impl_int_mod_arith_pty_pty {
    ($pty:ty) => {
        impl IntModAdd for $pty {
            type Output = Self;

            fn mod_add(self, rhs: Self) -> Self {
                self.overflowing_add(rhs).0
            }
        }

        impl IntModSub for $pty {
            type Output = Self;

            fn mod_sub(self, rhs: Self) -> Self {
                self.overflowing_sub(rhs).0
            }
        }

        impl IntModMul for $pty {
            type Output = Self;

            fn mod_mul(self, rhs: Self) -> Self {
                self.overflowing_mul(rhs).0
            }
        }

        impl IntModAddAssign for $pty {
            fn mod_add_assign(&mut self, rhs: Self) {
                *self = self.overflowing_add(rhs).0;
            }
        }

        impl IntModSubAssign for $pty {
            fn mod_sub_assign(&mut self, rhs: Self) {
                *self = self.overflowing_sub(rhs).0;
            }
        }

        impl IntModMulAssign for $pty {
            fn mod_mul_assign(&mut self, rhs: Self) {
                *self = self.overflowing_mul(rhs).0;
            }
        }
    };
}

impl_int_upty!(impl_int_mod_arith_pty_pty);
impl_int_ipty!(impl_int_mod_arith_pty_pty);

// expr node implementation

impl<'a, T, N, const SIGN: bool> BitVal for &'a ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolExprNode<T>;

    #[inline]
    fn bitnum(self) -> usize {
        N::USIZE
    }

    fn bit(self, x: usize) -> Self::Output {
        BoolExprNode::new(self.creator.clone(), self.indexes[x])
    }
}

impl<T, N, const SIGN: bool> BitMask<BoolExprNode<T>> for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    fn bitmask(t: BoolExprNode<T>) -> Self {
        ExprNode {
            creator: t.creator.clone(),
            indexes: GenericArray::from_exact_iter(iter::repeat(t.index).take(N::USIZE)).unwrap(),
        }
    }
}

macro_rules! impl_int_uconstant {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl<T: VarLit, $( $gparams ),* > IntConstant<T, $pty> for ExprNode<T, $ty, false>
        where
            $ty: ArrayLength<usize>,
        {
            fn constant(creator: Rc<RefCell<ExprCreator<T>>>, v: $pty) -> Self {
                ExprNode{ creator, indexes: GenericArray::from_exact_iter(
                    (0..<$ty>::USIZE).into_iter().map(|x| {
                        // return 1 - true node index, 0 - false node index
                        if x < <$pty>::BITS as usize {
                            usize::from((v & (1<<x)) != 0)
                        } else { 0 }
                    })
                ).unwrap() }
            }
        }
    }
}

impl_int_upty_ty1!(impl_int_uconstant);

macro_rules! impl_int_iconstant {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl<T: VarLit, $( $gparams ),* > IntConstant<T, $pty> for ExprNode<T, $ty, true>
        where
            $ty: ArrayLength<usize>,
        {
            fn constant(creator: Rc<RefCell<ExprCreator<T>>>, v: $pty) -> Self {
                ExprNode{ creator, indexes: GenericArray::from_exact_iter(
                    (0..<$ty>::USIZE).into_iter().map(|x| {
                        // return 1 - true node index, 0 - false node index
                        if x < <$pty>::BITS as usize {
                            usize::from((v & (1<<x)) != 0)
                        } else {
                            usize::from((v & (1<<((<$pty>::BITS-1) as usize))) != 0)
                        }
                    })
                ).unwrap() }
            }
        }
    }
}

impl_int_ipty_ty1!(impl_int_iconstant);

// ///////////////////
// IntEqual

impl<T, N, const SIGN: bool> IntEqual for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolExprNode<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        let mut xp = BoolExprNode::single(self.creator.clone(), true);
        for i in 0..N::USIZE {
            xp &= self.bit(i).bequal(rhs.bit(i));
        }
        xp
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        let mut xp = BoolExprNode::single(self.creator.clone(), false);
        for i in 0..N::USIZE {
            xp |= self.bit(i) ^ rhs.bit(i);
        }
        xp
    }
}

macro_rules! impl_int_equal_pty {
    ($sign:expr, $pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl<T, $( $gparams ),* > IntEqual<$pty> for ExprNode<T, $ty, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn equal(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.equal(Self::constant(creator, rhs))
            }

            fn nequal(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.nequal(Self::constant(creator, rhs))
            }
        }

        impl<T, $( $gparams ),* > IntEqual<ExprNode<T, $ty, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn equal(self, rhs: ExprNode<T, $ty, $sign>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, $sign>::constant(creator, self).equal(rhs)
            }

            fn nequal(self, rhs: ExprNode<T, $ty, $sign>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, $sign>::constant(creator, self).nequal(rhs)
            }
        }
    }
}

macro_rules! impl_int_equal_upty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl_int_equal_pty!(false, $pty, $ty, $( $gparams ),*);
    }
}
macro_rules! impl_int_equal_ipty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl_int_equal_pty!(true, $pty, $ty, $( $gparams ),*);
    }
}

impl_int_upty_ty1!(impl_int_equal_upty);
impl_int_ipty_ty1!(impl_int_equal_ipty);

// ///////////////////
// IntOrd

impl<T, N> IntOrd for ExprNode<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolExprNode<T>;

    fn less_than(self, rhs: Self) -> Self::Output {
        let mut xp = (!self.bit(0)) & rhs.bit(0);
        for i in 1..self.indexes.len() {
            xp = (self.bit(i).bequal(rhs.bit(i)) & xp) | ((!self.bit(i)) & rhs.bit(i));
        }
        xp
    }

    fn less_equal(self, rhs: Self) -> Self::Output {
        let mut xp = self.bit(0).imp(rhs.bit(0));
        for i in 1..self.indexes.len() {
            xp = (self.bit(i).bequal(rhs.bit(i)) & xp) | ((!self.bit(i)) & rhs.bit(i));
        }
        xp
    }

    fn greater_than(self, rhs: Self) -> Self::Output {
        rhs.less_than(self)
    }

    fn greater_equal(self, rhs: Self) -> Self::Output {
        rhs.less_equal(self)
    }
}

impl<T, N> IntOrd for ExprNode<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolExprNode<T>;

    fn less_than(self, rhs: Self) -> Self::Output {
        let lhs_sign = self.bit(N::USIZE - 1);
        let rhs_sign = rhs.bit(N::USIZE - 1);
        let (lhs_num, rhs_num) = {
            let mut lhs_num = self.as_unsigned();
            let mut rhs_num = rhs.as_unsigned();
            *lhs_num.indexes.last_mut().unwrap() = 0;
            *rhs_num.indexes.last_mut().unwrap() = 0;
            (lhs_num, rhs_num)
        };
        (lhs_sign.clone() & (!rhs_sign.clone()))
            | (lhs_sign.clone().bequal(rhs_sign) & lhs_num.less_than(rhs_num))
    }

    fn less_equal(self, rhs: Self) -> Self::Output {
        let lhs_sign = self.bit(N::USIZE - 1);
        let rhs_sign = rhs.bit(N::USIZE - 1);
        let (lhs_num, rhs_num) = {
            let mut lhs_num = self.as_unsigned();
            let mut rhs_num = rhs.as_unsigned();
            *lhs_num.indexes.last_mut().unwrap() = 0;
            *rhs_num.indexes.last_mut().unwrap() = 0;
            (lhs_num, rhs_num)
        };
        (lhs_sign.clone() & (!rhs_sign.clone()))
            | (lhs_sign.clone().bequal(rhs_sign) & lhs_num.less_equal(rhs_num))
    }

    fn greater_than(self, rhs: Self) -> Self::Output {
        rhs.less_than(self)
    }

    fn greater_equal(self, rhs: Self) -> Self::Output {
        rhs.less_equal(self)
    }
}

macro_rules! impl_int_ord_upty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl<T, $( $gparams ),* > IntOrd<$pty> for ExprNode<T, $ty, false>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn less_than(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.less_than(Self::constant(creator, rhs))
            }
            fn less_equal(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.less_equal(Self::constant(creator, rhs))
            }
            fn greater_than(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.greater_than(Self::constant(creator, rhs))
            }
            fn greater_equal(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.greater_equal(Self::constant(creator, rhs))
            }
        }

        impl<T, $( $gparams ),* > IntOrd<ExprNode<T, $ty, false>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn less_than(self, rhs: ExprNode<T, $ty, false>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, false>::constant(creator, self).less_than(rhs)
            }
            fn less_equal(self, rhs: ExprNode<T, $ty, false>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, false>::constant(creator, self).less_equal(rhs)
            }
            fn greater_than(self, rhs: ExprNode<T, $ty, false>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, false>::constant(creator, self).greater_than(rhs)
            }
            fn greater_equal(self, rhs: ExprNode<T, $ty, false>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, false>::constant(creator, self).greater_equal(rhs)
            }
        }
    }
}

macro_rules! impl_int_ord_ipty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl<T, $( $gparams ),* > IntOrd<$pty> for ExprNode<T, $ty, true>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn less_than(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.less_than(Self::constant(creator, rhs))
            }
            fn less_equal(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.less_equal(Self::constant(creator, rhs))
            }
            fn greater_than(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.greater_than(Self::constant(creator, rhs))
            }
            fn greater_equal(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.greater_equal(Self::constant(creator, rhs))
            }
        }

        impl<T, $( $gparams ),* > IntOrd<ExprNode<T, $ty, true>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn less_than(self, rhs: ExprNode<T, $ty, true>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, true>::constant(creator, self).less_than(rhs)
            }
            fn less_equal(self, rhs: ExprNode<T, $ty, true>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, true>::constant(creator, self).less_equal(rhs)
            }
            fn greater_than(self, rhs: ExprNode<T, $ty, true>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, true>::constant(creator, self).greater_than(rhs)
            }
            fn greater_equal(self, rhs: ExprNode<T, $ty, true>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, true>::constant(creator, self).greater_equal(rhs)
            }
        }
    }
}

impl_int_upty_ty1!(impl_int_ord_upty);
impl_int_ipty_ty1!(impl_int_ord_ipty);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolexpr::test_utils::*;

    #[test]
    fn test_int_equal_prim_types() {
        assert_eq!(4.equal(6), 4 == 6);
        assert_eq!(4.equal(4), 4 == 4);
        assert_eq!(4.nequal(6), 4 != 6);
        assert_eq!(4.nequal(4), 4 != 4);
    }

    #[test]
    fn test_int_ord_prim_types() {
        assert_eq!(4.less_than(6), 4 < 6);
        assert_eq!(4.less_than(4), 4 < 4);
        assert_eq!(4.less_than(3), 4 < 3);
        assert_eq!(4.less_equal(6), 4 <= 6);
        assert_eq!(4.less_equal(4), 4 <= 4);
        assert_eq!(4.less_equal(3), 4 <= 3);
        assert_eq!(4.greater_than(6), 4 > 6);
        assert_eq!(4.greater_than(4), 4 > 4);
        assert_eq!(4.greater_than(3), 4 > 3);
        assert_eq!(4.greater_equal(6), 4 >= 6);
        assert_eq!(4.greater_equal(4), 4 >= 4);
        assert_eq!(4.greater_equal(3), 4 >= 3);
    }

    #[test]
    fn test_int_bitval_prim_types() {
        assert_eq!(25u16.bit(1), false);
        assert_eq!(25u16.bit(4), true);
        assert_eq!(25u16.bit(19), false);
        assert_eq!(0xff00u16.bit(19), false);
    }

    #[test]
    fn test_int_bitmask_prim_types() {
        assert_eq!(25i16.bit(1), false);
        assert_eq!(25i16.bit(4), true);
        assert_eq!(25i16.bit(19), false);
        assert_eq!((-0x100i16).bit(19), true);

        assert_eq!(<u16 as BitMask<bool>>::bitmask(false), 0);
        assert_eq!(<u16 as BitMask<bool>>::bitmask(true), 0xffffu16);
        assert_eq!(<i16 as BitMask<bool>>::bitmask(false), 0);
        assert_eq!(<i16 as BitMask<bool>>::bitmask(true) as u16, 0xffffu16);
    }

    #[test]
    fn test_int_fullmul_prim_types() {
        assert_eq!(42u8.fullmul(65), 42 * 65);
        assert_eq!(71i8.fullmul(-25), 71 * -25);
        assert_eq!(5688u16.fullmul(6241), 5688 * 6241);
        assert_eq!((-5688i16).fullmul(6241), -5688 * 6241);
        assert_eq!(55812145u32.fullmul(583021521), 55812145 * 583021521);
        assert_eq!(55812145i32.fullmul(-583021521), 55812145 * -583021521);
    }

    #[test]
    fn test_int_divmod_prim_types() {
        assert_eq!(134u8.divmod(31), (134 / 31, 134 % 31, true));
        assert_eq!(134u8.divmod(0), (0, 0, false));
        assert_eq!(74i8.divmod(21), (74 / 21, 74 % 21, true));
        assert_eq!(42134u16.divmod(552), (42134 / 552, 42134 % 552, true));
        assert_eq!((-22134i16).divmod(552), (-22134 / 552, -22134 % 552, true));
    }

    #[test]
    fn test_expr_node_bitval() {
        let ec = ExprCreator::new();
        let x1 = ExprNode::<isize, U7, false>::variable(ec.clone());
        assert_eq!(x1.bit(2), BoolExprNode::single(ec.clone(), 3));
        assert_eq!(x1.bit(6), BoolExprNode::single(ec.clone(), 7));
        let x1 = ExprNode::<isize, U7, true>::variable(ec.clone());
        assert_eq!(x1.bit(3), BoolExprNode::single(ec.clone(), 11));
    }

    #[test]
    fn test_expr_node_bitmask() {
        let ec = ExprCreator::new();
        let bx1 = BoolExprNode::variable(ec.clone());
        let bx2 = BoolExprNode::variable(ec.clone());
        let bxp1 = bx1 ^ bx2;
        assert_eq!(
            ExprNode::filled_expr(bxp1.clone()),
            <ExprNode<isize, U8, false> as BitMask<BoolExprNode<isize>>>::bitmask(bxp1.clone())
        );
        assert_eq!(
            ExprNode::filled_expr(bxp1.clone()),
            <ExprNode<isize, U8, true> as BitMask<BoolExprNode<isize>>>::bitmask(bxp1.clone())
        );
    }

    #[test]
    fn test_expr_node_int_constant() {
        let ec = ExprCreator::new();
        let x1 = ExprNode::<isize, U9, false>::constant(ec.clone(), 0b11011001);
        assert_eq!([1, 0, 0, 1, 1, 0, 1, 1, 0], *x1.indexes);
        let x1 = ExprNode::<isize, U8, true>::constant(ec.clone(), 0b00111001);
        assert_eq!([1, 0, 0, 1, 1, 1, 0, 0], *x1.indexes);
        let x1 = ExprNode::<isize, U10, true>::constant(ec.clone(), -15);
        assert_eq!([1, 0, 0, 0, 1, 1, 1, 1, 1, 1], *x1.indexes);
        let x1 = ExprNode::<isize, U64, false>::constant(ec.clone(), 1848549293434211u64);
        assert_eq!(
            (0..64)
                .into_iter()
                .map(|x| ((1848549293434211u64 >> x) & 1) as usize)
                .collect::<Vec<_>>()
                .as_slice(),
            x1.indexes.as_slice()
        );
    }

    #[test]
    fn test_expr_node_int_equal() {
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let x3 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let x4 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let reseq = x1.equal(x2);
            let resne = x3.nequal(x4);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 20);
            let expeq = bvs[0].clone().bequal(bvs[5].clone())
                & bvs[1].clone().bequal(bvs[6].clone())
                & bvs[2].clone().bequal(bvs[7].clone())
                & bvs[3].clone().bequal(bvs[8].clone())
                & bvs[4].clone().bequal(bvs[9].clone());
            let expne = (bvs[10].clone() ^ bvs[15].clone())
                | (bvs[11].clone() ^ bvs[16].clone())
                | (bvs[12].clone() ^ bvs[17].clone())
                | (bvs[13].clone() ^ bvs[18].clone())
                | (bvs[14].clone() ^ bvs[19].clone());

            assert_eq!(expeq, reseq);
            assert_eq!(expne, resne);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        let exp_ec = ExprCreator::new();
        let bvs = alloc_boolvars(exp_ec.clone(), 18);
        let expeq = bvs[0].clone()
            & bvs[1].clone()
            & bvs[2].clone()
            & !bvs[3].clone()
            & !bvs[4].clone()
            & !bvs[5].clone()
            & !bvs[6].clone()
            & bvs[7].clone()
            & !bvs[8].clone();
        let expne = bvs[9].clone()
            | !bvs[10].clone()
            | bvs[11].clone()
            | !bvs[12].clone()
            | bvs[13].clone()
            | bvs[14].clone()
            | !bvs[15].clone()
            | bvs[16].clone()
            | bvs[17].clone();

        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U9, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U9, false>::variable(ec.clone());
            let reseq = x1.equal(135);
            let resne = x2.nequal(74);
            assert_eq!(expeq, reseq);
            assert_eq!(expne, resne);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U9, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U9, false>::variable(ec.clone());
            let reseq = 135.equal(x1);
            let resne = 74.nequal(x2);
            assert_eq!(expeq, reseq);
            assert_eq!(expne, resne);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        let exp_ec = ExprCreator::new();
        let bvs = alloc_boolvars(exp_ec.clone(), 18);
        let expeq = bvs[0].clone()
            & bvs[1].clone()
            & bvs[2].clone()
            & !bvs[3].clone()
            & !bvs[4].clone()
            & !bvs[5].clone()
            & !bvs[6].clone()
            & bvs[7].clone()
            & bvs[8].clone();
        let expne = bvs[9].clone()
            | !bvs[10].clone()
            | bvs[11].clone()
            | !bvs[12].clone()
            | bvs[13].clone()
            | bvs[14].clone()
            | !bvs[15].clone()
            | !bvs[16].clone()
            | !bvs[17].clone();
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U9, true>::variable(ec.clone());
            let x2 = ExprNode::<isize, U9, true>::variable(ec.clone());
            let reseq = x1.equal(-121);
            let resne = x2.nequal(-54);
            assert_eq!(expeq, reseq);
            assert_eq!(expne, resne);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U9, true>::variable(ec.clone());
            let x2 = ExprNode::<isize, U9, true>::variable(ec.clone());
            let reseq = (-121).equal(x1);
            let resne = (-54).nequal(x2);
            assert_eq!(expeq, reseq);
            assert_eq!(expne, resne);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
    }

    fn gen_less_x_chain(
        bva: &[BoolExprNode<isize>],
        bvb: &[BoolExprNode<isize>],
        with_equal: bool,
    ) -> BoolExprNode<isize> {
        let mut s0 = if with_equal {
            bva[0].clone().imp(bvb[0].clone())
        } else {
            !bva[0].clone() & bvb[0].clone()
        };
        for i in 1..bva.len() {
            s0 = (bva[i].clone().bequal(bvb[i].clone()) & s0.clone())
                | (!bva[i].clone() & bvb[i].clone());
        }
        s0
    }

    #[test]
    fn test_expr_node_unsigned_int_ord() {
        {
            let ec = ExprCreator::new();
            let xv = (0..8)
                .into_iter()
                .map(|_| ExprNode::<isize, U5, false>::variable(ec.clone()))
                .collect::<Vec<_>>();
            let reslt = xv[0].clone().less_than(xv[1].clone());
            let resle = xv[2].clone().less_equal(xv[3].clone());
            let resgt = xv[4].clone().greater_than(xv[5].clone());
            let resge = xv[6].clone().greater_equal(xv[7].clone());

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 40);
            let explt = gen_less_x_chain(&bvs[0..5], &bvs[5..10], false);
            let exple = gen_less_x_chain(&bvs[10..15], &bvs[15..20], true);
            let expgt = gen_less_x_chain(&bvs[25..30], &bvs[20..25], false);
            let expge = gen_less_x_chain(&bvs[35..40], &bvs[30..35], true);

            assert_eq!(explt, reslt);
            assert_eq!(exple, resle);
            assert_eq!(expgt, resgt);
            assert_eq!(expge, resge);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        let exp_ec = ExprCreator::new();
        let bvs = alloc_boolvars(exp_ec.clone(), 40);
        let explt = gen_less_x_chain(
            &bvs[0..10],
            (0..10)
                .into_iter()
                .map(|i| BoolExprNode::single_value(exp_ec.clone(), (155 & (1 << i)) != 0))
                .collect::<Vec<_>>()
                .as_slice(),
            false,
        );
        let exple = gen_less_x_chain(
            &bvs[10..20],
            (0..10)
                .into_iter()
                .map(|i| BoolExprNode::single_value(exp_ec.clone(), (51 & (1 << i)) != 0))
                .collect::<Vec<_>>()
                .as_slice(),
            true,
        );
        let expgt = gen_less_x_chain(
            (0..10)
                .into_iter()
                .map(|i| BoolExprNode::single_value(exp_ec.clone(), (79 & (1 << i)) != 0))
                .collect::<Vec<_>>()
                .as_slice(),
            &bvs[20..30],
            false,
        );
        let expge = gen_less_x_chain(
            (0..10)
                .into_iter()
                .map(|i| BoolExprNode::single_value(exp_ec.clone(), (210 & (1 << i)) != 0))
                .collect::<Vec<_>>()
                .as_slice(),
            &bvs[30..40],
            true,
        );

        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let x3 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let x4 = ExprNode::<isize, U10, false>::variable(ec.clone());

            let reslt = x1.clone().less_than(155);
            let resle = x2.clone().less_equal(51);
            let resgt = x3.clone().greater_than(79);
            let resge = x4.clone().greater_equal(210);

            assert_eq!(explt, reslt);
            assert_eq!(exple, resle);
            assert_eq!(expgt, resgt);
            assert_eq!(expge, resge);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let x3 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let x4 = ExprNode::<isize, U10, false>::variable(ec.clone());

            let reslt = 155.greater_than(x1.clone());
            let resle = 51.greater_equal(x2.clone());
            let resgt = 79.less_than(x3.clone());
            let resge = 210.less_equal(x4.clone());

            assert_eq!(explt, reslt);
            assert_eq!(exple, resle);
            assert_eq!(expgt, resgt);
            assert_eq!(expge, resge);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
    }

    #[test]
    fn test_expr_node_signed_int_ord() {
        {
            let ec = ExprCreator::new();
            let xv = (0..8)
                .into_iter()
                .map(|_| ExprNode::<isize, U5, true>::variable(ec.clone()))
                .collect::<Vec<_>>();
            let reslt = xv[0].clone().less_than(xv[1].clone());
            let resle = xv[2].clone().less_equal(xv[3].clone());
            let resgt = xv[4].clone().greater_than(xv[5].clone());
            let resge = xv[6].clone().greater_equal(xv[7].clone());

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 40);
            let explt = (bvs[4].clone() & !bvs[9].clone())
                | (bvs[4].clone().bequal(bvs[9].clone())
                    & gen_less_x_chain(&bvs[0..4], &bvs[5..9], false));

            let exple = (bvs[14].clone() & !bvs[19].clone())
                | (bvs[14].clone().bequal(bvs[19].clone())
                    & gen_less_x_chain(&bvs[10..14], &bvs[15..19], true));

            let expgt = (bvs[29].clone() & !bvs[24].clone())
                | (bvs[29].clone().bequal(bvs[24].clone())
                    & gen_less_x_chain(&bvs[25..29], &bvs[20..24], false));

            let expge = (bvs[39].clone() & !bvs[34].clone())
                | (bvs[39].clone().bequal(bvs[34].clone())
                    & gen_less_x_chain(&bvs[35..39], &bvs[30..34], true));

            assert_eq!(explt, reslt);
            assert_eq!(exple, resle);
            assert_eq!(expgt, resgt);
            assert_eq!(expge, resge);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        let exp_ec = ExprCreator::new();
        let bvs = alloc_boolvars(exp_ec.clone(), 40);
        let bnfalse = BoolExprNode::single_value(exp_ec.clone(), false);
        let bntrue = BoolExprNode::single_value(exp_ec.clone(), true);
        let explt = (bvs[9].clone() & !bntrue.clone())
            | (bvs[9].clone().bequal(bntrue.clone())
                & gen_less_x_chain(
                    &bvs[0..9],
                    (0..9)
                        .into_iter()
                        .map(|i| BoolExprNode::single_value(exp_ec.clone(), (-42 & (1 << i)) != 0))
                        .collect::<Vec<_>>()
                        .as_slice(),
                    false,
                ));
        let exple = (bvs[19].clone() & !bnfalse.clone())
            | (bvs[19].clone().bequal(bnfalse.clone())
                & gen_less_x_chain(
                    &bvs[10..19],
                    (0..9)
                        .into_iter()
                        .map(|i| BoolExprNode::single_value(exp_ec.clone(), (75 & (1 << i)) != 0))
                        .collect::<Vec<_>>()
                        .as_slice(),
                    true,
                ));
        let expgt = (bntrue.clone() & !bvs[29].clone())
            | (bntrue.clone().bequal(bvs[29].clone())
                & gen_less_x_chain(
                    (0..9)
                        .into_iter()
                        .map(|i| BoolExprNode::single_value(exp_ec.clone(), (-89 & (1 << i)) != 0))
                        .collect::<Vec<_>>()
                        .as_slice(),
                    &bvs[20..29],
                    false,
                ));
        let expge = (bnfalse.clone() & !bvs[39].clone())
            | (bnfalse.clone().bequal(bvs[39].clone())
                & gen_less_x_chain(
                    (0..9)
                        .into_iter()
                        .map(|i| BoolExprNode::single_value(exp_ec.clone(), (52 & (1 << i)) != 0))
                        .collect::<Vec<_>>()
                        .as_slice(),
                    &bvs[30..39],
                    true,
                ));

        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let x3 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let x4 = ExprNode::<isize, U10, true>::variable(ec.clone());

            let reslt = x1.clone().less_than(-42);
            let resle = x2.clone().less_equal(75);
            let resgt = x3.clone().greater_than(-89);
            let resge = x4.clone().greater_equal(52);

            assert_eq!(explt, reslt);
            assert_eq!(exple, resle);
            assert_eq!(expgt, resgt);
            assert_eq!(expge, resge);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let x3 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let x4 = ExprNode::<isize, U10, true>::variable(ec.clone());

            let reslt = (-42).greater_than(x1.clone());
            let resle = 75.greater_equal(x2.clone());
            let resgt = (-89).less_than(x3.clone());
            let resge = 52.less_equal(x4.clone());

            assert_eq!(explt, reslt);
            assert_eq!(exple, resle);
            assert_eq!(expgt, resgt);
            assert_eq!(expge, resge);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
    }
}
