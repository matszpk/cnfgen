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
//! The module contains traits to integer expression nodes.
//!
//! They provides additional operations that
//! that can be made on integers.

use std::cell::RefCell;
use std::fmt::Debug;
use std::iter;
use std::ops::Neg;
use std::rc::Rc;

use generic_array::typenum::*;
use generic_array::*;

use super::*;
use crate::boolexpr::{BoolEqual, BoolImpl};
use crate::{impl_int_ipty, impl_int_ipty_ty1, impl_int_upty, impl_int_upty_ty1};

/// Equality operator for integer expressions.
///
/// It defined for IntIntExprNode and DynIntIntExprNode. Type `Rhs` can be various than Self.
/// This trait also defines `Output` that can be different than Self.
pub trait IntEqual<Rhs = Self> {
    type Output;

    /// A method to make equality.
    fn equal(self, rhs: Rhs) -> Self::Output;
    /// A method to make inequality.
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

/// Orderings for integer expressions.
///
/// It defined for IntIntExprNode and DynIntIntExprNode. Type `Rhs` can be various than Self.
/// This trait also defines `Output` that can be different than Self.
pub trait IntOrd<Rhs = Self> {
    type Output;

    /// A method to make 'less than'.
    fn less_than(self, rhs: Rhs) -> Self::Output;
    /// A method to make 'less or equal'.
    fn less_equal(self, rhs: Rhs) -> Self::Output;
    /// A method to make 'greater than'.
    fn greater_than(self, rhs: Rhs) -> Self::Output;
    /// A method to make 'greater or equal'.
    fn greater_equal(self, rhs: Rhs) -> Self::Output;
}

/// Ordering operators for integers.
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

/// Trait to make object from primitive integer (constant).
pub trait IntConstant<T: VarLit, U> {
    fn constant(creator: Rc<RefCell<ExprCreator<T>>>, v: U) -> Self;
}

/// Trait to try make object from primitive integer (constant).
pub trait TryIntConstant<T: VarLit, U>: Sized {
    fn try_constant(creator: Rc<RefCell<ExprCreator<T>>>, v: U) -> Result<Self, IntError>;
}

/// Trait to get a bit value from object and get number of bits for object.
///
/// It defined for IntIntExprNode and DynIntIntExprNode. The defines `Output` that can be
/// BoolExprNode.
pub trait BitVal {
    type Output;

    /// Get number of bits of object.
    fn bitnum(self) -> usize;
    /// Get bit value.
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

/// Special trait to make BitMask from boolean expression.
///
/// A bitmask can have all bits set or zeroed. It defined only for IntIntExprNode.
pub trait BitMask<T> {
    /// Make bit-mask from boolean expression.
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

/// Trait to make full multiplication.
///
/// Full multiplication generates output have twice size of input arguments.
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait FullMul<Rhs = Self> {
    type Output;

    /// A method to make full multiplication.
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

/// Trait to make division and remainder (modulo) in one operation.
///
/// Due to division or remainder needs some condition to evaluate, the method divmod
/// returns result of division, result of remainder and condition to evaluate these operation.
/// Same condition is a boolean expression describes these condtions.
/// This condition should be used to force condition in boolean formulae:
/// it can be done by adding condition to root of conjunction (ANDs).
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait DivMod<Rhs = Self> {
    type Output;
    /// Type of output condition.
    type OutputCond;

    /// A method to make division and remainder.
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

/// Trait to modular addition.
///
/// A modular addition make this same addition like processor addition - it returns
/// truncated sum of two arguments.
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait IntModAdd<Rhs = Self> {
    type Output;

    /// A method to make modular addition.
    fn mod_add(self, rhs: Rhs) -> Self::Output;
}

/// Trait to modular subtraction.
///
/// A modular subtraction make this same subtraction like processor's subtraction - it returns
/// truncated difference.
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait IntModSub<Rhs = Self> {
    type Output;

    /// A method to make modular subtraction.
    fn mod_sub(self, rhs: Rhs) -> Self::Output;
}

/// Trait to modular multiplication.
///
/// A modular multiplication make this same truncated multiplication to size of input argument.
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait IntModMul<Rhs = Self> {
    type Output;

    /// A method to make modular multiplication.
    fn mod_mul(self, rhs: Rhs) -> Self::Output;
}

/// Trait to modular addition and assignment. Similar to AddAssign.
pub trait IntModAddAssign<Rhs = Self> {
    /// A method to modular addition and assignment.
    fn mod_add_assign(&mut self, rhs: Rhs);
}

/// Trait to modular subtraction and assignment. Similar to SubAssign.
pub trait IntModSubAssign<Rhs = Self> {
    /// A method to modular subtraction and assignment.
    fn mod_sub_assign(&mut self, rhs: Rhs);
}

/// Trait to modular multiplication and assignment. Similar to MulAssign.
pub trait IntModMulAssign<Rhs = Self> {
    /// A method to modular multiplication and assignment.
    fn mod_mul_assign(&mut self, rhs: Rhs);
}

macro_rules! impl_int_mod_arith_pty_pty {
    ($pty:ty) => {
        impl IntModAdd for $pty {
            type Output = Self;

            #[inline]
            fn mod_add(self, rhs: Self) -> Self {
                self.overflowing_add(rhs).0
            }
        }

        impl IntModSub for $pty {
            type Output = Self;

            #[inline]
            fn mod_sub(self, rhs: Self) -> Self {
                self.overflowing_sub(rhs).0
            }
        }

        impl IntModMul for $pty {
            type Output = Self;

            #[inline]
            fn mod_mul(self, rhs: Self) -> Self {
                self.overflowing_mul(rhs).0
            }
        }

        impl IntModAddAssign for $pty {
            #[inline]
            fn mod_add_assign(&mut self, rhs: Self) {
                *self = self.mod_add(rhs);
            }
        }

        impl IntModSubAssign for $pty {
            #[inline]
            fn mod_sub_assign(&mut self, rhs: Self) {
                *self = self.mod_sub(rhs);
            }
        }

        impl IntModMulAssign for $pty {
            #[inline]
            fn mod_mul_assign(&mut self, rhs: Self) {
                *self = self.mod_mul(rhs);
            }
        }
    };
}

impl_int_upty!(impl_int_mod_arith_pty_pty);
impl_int_ipty!(impl_int_mod_arith_pty_pty);

/// Trait to modular negation.
///
/// A modular negation just make negation ignoring wrong result for minimal value
/// (for example for 8-bit is -128). It can be used internally for some expressions.
/// Generally should be avoided.
/// It defined for signed IntIntExprNode and signed DynIntIntExprNode.
pub trait IntModNeg {
    type Output;

    /// A method to make modular negation.
    fn mod_neg(self) -> Self::Output;
}

macro_rules! impl_int_mod_neg_pty {
    ($pty:ty) => {
        impl IntModNeg for $pty {
            type Output = Self;

            #[inline]
            fn mod_neg(self) -> Self {
                self.overflowing_neg().0
            }
        }
    };
}

impl_int_ipty!(impl_int_mod_neg_pty);

/// Trait to modular addition with condition.
///
/// A `cond_add` just returns result of modular addition and condition when no overflow happened.
/// This condition can force evaluation only if result is in input size type.
/// This condition should be used to force condition in boolean formulae:
/// it can be done by adding condition to root of conjunction (ANDs).
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait IntCondAdd<Rhs = Self> {
    type Output;
    /// Type of output condition.
    type OutputCond;

    /// A method to make conditional addition.
    fn cond_add(self, rhs: Rhs) -> (Self::Output, Self::OutputCond);
}

/// Trait to modular subtraction with condition.
///
/// A `cond_sub` just returns result of modular subtraction and condition when
/// no overflow happened.
/// This condition can force evaluation only if result is in input size type.
/// This condition should be used to force condition in boolean formulae:
/// it can be done by adding condition to root of conjunction (ANDs).
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait IntCondSub<Rhs = Self> {
    type Output;
    /// Type of output condition.
    type OutputCond;

    /// A method to make conditional subtraction.
    fn cond_sub(self, rhs: Rhs) -> (Self::Output, Self::OutputCond);
}

/// Trait to modular multiplication with condition.
///
/// A `cond_mul` just returns result of modular multiplication and condition when
/// no overflow happened.
/// This condition can force evaluation only if result is in input size type.
/// This condition should be used to force condition in boolean formulae:
/// it can be done by adding condition to root of conjunction (ANDs).
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait IntCondMul<Rhs = Self> {
    type Output;
    /// Type of output condition.
    type OutputCond;

    /// A method to make conditional multiplication.
    fn cond_mul(self, rhs: Rhs) -> (Self::Output, Self::OutputCond);
}

macro_rules! impl_int_cond_arith_pty_pty {
    ($pty:ty) => {
        impl IntCondAdd for $pty {
            type Output = Self;
            type OutputCond = bool;

            #[inline]
            fn cond_add(self, rhs: Self) -> (Self, bool) {
                let (r, c) = self.overflowing_add(rhs);
                (r, !c)
            }
        }

        impl IntCondSub for $pty {
            type Output = Self;
            type OutputCond = bool;

            #[inline]
            fn cond_sub(self, rhs: Self) -> (Self, bool) {
                let (r, c) = self.overflowing_sub(rhs);
                (r, !c)
            }
        }

        impl IntCondMul for $pty {
            type Output = Self;
            type OutputCond = bool;

            #[inline]
            fn cond_mul(self, rhs: Self) -> (Self, bool) {
                let (r, c) = self.overflowing_mul(rhs);
                (r, !c)
            }
        }
    };
}

impl_int_upty!(impl_int_cond_arith_pty_pty);
impl_int_ipty!(impl_int_cond_arith_pty_pty);

/// Trait to modular negation with condition.
///
/// A `cond_neg` just returns result of modular negation and condition when
/// no overflow happened.
/// This condition can force evaluation only if result is in input size type.
/// This condition should be used to force condition in boolean formulae:
/// it can be done by adding condition to root of conjunction (ANDs).
/// It defined for signed IntIntExprNode and signed DynIntIntExprNode.
pub trait IntCondNeg {
    type Output;
    /// Type of output condition.
    type OutputCond;

    fn cond_neg(self) -> (Self::Output, Self::OutputCond);
}

macro_rules! impl_int_cond_neg_pty {
    ($pty:ty) => {
        impl IntCondNeg for $pty {
            type Output = Self;
            type OutputCond = bool;

            #[inline]
            fn cond_neg(self) -> (Self, bool) {
                let (r, c) = self.overflowing_neg();
                (r, !c)
            }
        }
    };
}

impl_int_ipty!(impl_int_cond_neg_pty);

/// Trait to left shift with condition.
///
/// A `cond_shl` just returns result of modular multiplication and condition when
/// no right argument is lower than number of bits of left argument.
/// This condition should be used to force condition in boolean formulae:
/// it can be done by adding condition to root of conjunction (ANDs).
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait IntCondShl<Rhs = Self> {
    type Output;
    /// Type of output condition.
    type OutputCond;

    fn cond_shl(self, rhs: Rhs) -> (Self::Output, Self::OutputCond);
}

/// Trait to right shift with condition.
///
/// A `cond_shr` just returns result of modular multiplication and condition when
/// no right argument is lower than number of bits of left argument.
/// This condition should be used to force condition in boolean formulae:
/// it can be done by adding condition to root of conjunction (ANDs).
/// It defined for IntIntExprNode and DynIntIntExprNode.
pub trait IntCondShr<Rhs = Self> {
    type Output;
    /// Type of output condition.
    type OutputCond;

    fn cond_shr(self, rhs: Rhs) -> (Self::Output, Self::OutputCond);
}

macro_rules! impl_int_cond_shift_pty_pty {
    ($pty:ty) => {
        impl IntCondShl<u32> for $pty {
            type Output = Self;
            type OutputCond = bool;

            #[inline]
            fn cond_shl(self, rhs: u32) -> (Self, bool) {
                let (r, c) = self.overflowing_shl(rhs);
                (r, !c)
            }
        }

        impl IntCondShr<u32> for $pty {
            type Output = Self;
            type OutputCond = bool;

            #[inline]
            fn cond_shr(self, rhs: u32) -> (Self, bool) {
                let (r, c) = self.overflowing_shr(rhs);
                (r, !c)
            }
        }
    };
}

impl_int_upty!(impl_int_cond_shift_pty_pty);

// ///////////////////////////////
// expr node implementation

impl<'a, T, N, const SIGN: bool> BitVal for &'a IntExprNode<T, N, SIGN>
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

impl<T, N, const SIGN: bool> BitMask<BoolExprNode<T>> for IntExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    fn bitmask(t: BoolExprNode<T>) -> Self {
        IntExprNode {
            creator: t.creator.clone(),
            indexes: GenericArray::from_exact_iter(iter::repeat(t.index).take(N::USIZE)).unwrap(),
        }
    }
}

macro_rules! impl_int_uconstant {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl<T: VarLit, $( $gparams ),* > IntConstant<T, $pty> for IntExprNode<T, $ty, false>
        where
            $ty: ArrayLength<usize>,
        {
            fn constant(creator: Rc<RefCell<ExprCreator<T>>>, v: $pty) -> Self {
                IntExprNode{ creator, indexes: GenericArray::from_exact_iter(
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
        impl<T: VarLit, $( $gparams ),* > IntConstant<T, $pty> for IntExprNode<T, $ty, true>
        where
            $ty: ArrayLength<usize>,
        {
            fn constant(creator: Rc<RefCell<ExprCreator<T>>>, v: $pty) -> Self {
                IntExprNode{ creator, indexes: GenericArray::from_exact_iter(
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

macro_rules! impl_int_try_uconstant {
    ($pty:ty) => {
        impl<T, N> TryIntConstant<T, $pty> for IntExprNode<T, N, false>
        where
            T: VarLit,
            N: ArrayLength<usize>,
        {
            fn try_constant(
                creator: Rc<RefCell<ExprCreator<T>>>,
                v: $pty,
            ) -> Result<Self, IntError> {
                let n = N::USIZE;
                let bits = <$pty>::BITS as usize;
                // for n < bits, check whether highest bits are zero.
                if n < bits && (v & ((((1 as $pty) << (bits - n)).overflowing_sub(1).0) << n)) != 0
                {
                    return Err(IntError::BitOverflow);
                }
                Ok(IntExprNode {
                    creator,
                    indexes: GenericArray::from_exact_iter((0..n).into_iter().map(|x| {
                        // return 1 - true node index, 0 - false node index
                        if x < bits {
                            usize::from((v & (1 << x)) != 0)
                        } else {
                            0
                        }
                    }))
                    .unwrap(),
                })
            }
        }
    };
}

impl_int_upty!(impl_int_try_uconstant);

macro_rules! impl_int_try_iconstant {
    ($pty:ty) => {
        impl<T, N> TryIntConstant<T, $pty> for IntExprNode<T, N, true>
        where
            T: VarLit,
            N: ArrayLength<usize>,
        {
            fn try_constant(
                creator: Rc<RefCell<ExprCreator<T>>>,
                v: $pty,
            ) -> Result<Self, IntError> {
                let n = N::USIZE;
                let bits = <$pty>::BITS as usize;
                if n < bits {
                    // for n < bits, check whether highest bits are zero if positive number or
                    // if ones if negative number.
                    let mask = ((((1 as $pty) << (bits - n)).overflowing_sub(1).0) << n);
                    let signmask = if v < 0 { mask } else { 0 };
                    if (v & mask) != signmask {
                        return Err(IntError::BitOverflow);
                    }
                }
                Ok(IntExprNode {
                    creator,
                    indexes: GenericArray::from_exact_iter((0..n).into_iter().map(|x| {
                        // return 1 - true node index, 0 - false node index
                        if x < bits {
                            usize::from((v & (1 << x)) != 0)
                        } else {
                            usize::from((v & (1 << ((<$pty>::BITS - 1) as usize))) != 0)
                        }
                    }))
                    .unwrap(),
                })
            }
        }
    };
}

impl_int_ipty!(impl_int_try_iconstant);

// ///////////////////
// IntEqual

impl<T, N, const SIGN: bool> IntEqual for IntExprNode<T, N, SIGN>
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
        impl<T, $( $gparams ),* > IntEqual<$pty> for IntExprNode<T, $ty, $sign>
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

        impl<T, $( $gparams ),* > IntEqual<IntExprNode<T, $ty, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn equal(self, rhs: IntExprNode<T, $ty, $sign>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, $sign>::constant(creator, self).equal(rhs)
            }

            fn nequal(self, rhs: IntExprNode<T, $ty, $sign>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, $sign>::constant(creator, self).nequal(rhs)
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

impl<T, N> IntOrd for IntExprNode<T, N, false>
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

impl<T, N> IntOrd for IntExprNode<T, N, true>
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
            | (lhs_sign.bequal(rhs_sign) & lhs_num.less_than(rhs_num))
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
            | (lhs_sign.bequal(rhs_sign) & lhs_num.less_equal(rhs_num))
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
        impl<T, $( $gparams ),* > IntOrd<$pty> for IntExprNode<T, $ty, false>
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

        impl<T, $( $gparams ),* > IntOrd<IntExprNode<T, $ty, false>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn less_than(self, rhs: IntExprNode<T, $ty, false>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, false>::constant(creator, self).less_than(rhs)
            }
            fn less_equal(self, rhs: IntExprNode<T, $ty, false>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, false>::constant(creator, self).less_equal(rhs)
            }
            fn greater_than(self, rhs: IntExprNode<T, $ty, false>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, false>::constant(creator, self).greater_than(rhs)
            }
            fn greater_equal(self, rhs: IntExprNode<T, $ty, false>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, false>::constant(creator, self).greater_equal(rhs)
            }
        }
    }
}

macro_rules! impl_int_ord_ipty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl<T, $( $gparams ),* > IntOrd<$pty> for IntExprNode<T, $ty, true>
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

        impl<T, $( $gparams ),* > IntOrd<IntExprNode<T, $ty, true>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = BoolExprNode<T>;

            fn less_than(self, rhs: IntExprNode<T, $ty, true>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, true>::constant(creator, self).less_than(rhs)
            }
            fn less_equal(self, rhs: IntExprNode<T, $ty, true>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, true>::constant(creator, self).less_equal(rhs)
            }
            fn greater_than(self, rhs: IntExprNode<T, $ty, true>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, true>::constant(creator, self).greater_than(rhs)
            }
            fn greater_equal(self, rhs: IntExprNode<T, $ty, true>) -> Self::Output {
                let creator = rhs.creator.clone();
                IntExprNode::<T, $ty, true>::constant(creator, self).greater_equal(rhs)
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
        assert_eq!(25i16.bit(1), false);
        assert_eq!(25i16.bit(4), true);
        assert_eq!(25i16.bit(15), false);
        assert_eq!(25i16.bit(19), false);
        assert_eq!((-25i16).bit(1), true);
        assert_eq!((-25i16).bit(4), false);
        assert_eq!((-25i16).bit(14), true);
        assert_eq!((-25i16).bit(19), true);
        assert_eq!((-0x100i16).bit(19), true);
    }

    #[test]
    fn test_int_bitmask_prim_types() {
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
        assert_eq!(55812145u32.fullmul(583021521), 55812145u64 * 583021521u64);
        assert_eq!(55812145i32.fullmul(-583021521), 55812145i64 * -583021521i64);
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
    fn test_int_mod_arith_prim_types() {
        assert_eq!(54u8.mod_add(45), 99u8);
        assert_eq!(54u8.mod_add(245), 43u8);
        assert_eq!(154u8.mod_sub(11), 143u8);
        assert_eq!(154u8.mod_sub(245), 165u8);
        assert_eq!(67u8.mod_mul(3), 201u8);
        assert_eq!(67u8.mod_mul(11), 225u8);

        assert_eq!(54i8.mod_add(45), 99i8);
        assert_eq!(54i8.mod_add(99), -103i8);
        assert_eq!(77i8.mod_sub(11), 66i8);
        assert_eq!((-100i8).mod_sub(32), 124i8);
        assert_eq!((-30i8).mod_mul(4), -120i8);
        assert_eq!((-30i8).mod_mul(11), -74i8);

        let mut a = 54u8;
        a.mod_add_assign(45);
        assert_eq!(a, 99u8);
        let mut a = 154u8;
        a.mod_sub_assign(11);
        assert_eq!(a, 143u8);
        let mut a = 67u8;
        a.mod_mul_assign(3);
        assert_eq!(a, 201u8);

        assert_eq!(53i8.mod_neg(), -53i8);
        assert_eq!((-128i8).mod_neg(), -128i8);
    }

    #[test]
    fn test_int_cond_arith_prim_types() {
        assert_eq!(54u8.cond_add(45), (99u8, true));
        assert_eq!(54u8.cond_add(245), (43u8, false));
        assert_eq!(154u8.cond_sub(11), (143u8, true));
        assert_eq!(154u8.cond_sub(245), (165u8, false));
        assert_eq!(67u8.cond_mul(3), (201u8, true));
        assert_eq!(67u8.cond_mul(11), (225u8, false));

        assert_eq!(54i8.cond_add(45), (99i8, true));
        assert_eq!(54i8.cond_add(99), (-103i8, false));
        assert_eq!(77i8.cond_sub(11), (66i8, true));
        assert_eq!((-100i8).cond_sub(32), (124i8, false));
        assert_eq!((-30i8).cond_mul(4), (-120i8, true));
        assert_eq!((-30i8).cond_mul(11), (-74i8, false));

        assert_eq!(53i8.cond_neg(), (-53i8, true));
        assert_eq!((-128i8).cond_neg(), (-128i8, false));
    }

    #[test]
    fn test_int_cond_shift_prim_types() {
        assert_eq!(7u32.cond_shl(10), (7 << 10, true));
        assert_eq!(7u32.cond_shl(31), (0x80000000u32, true));
        assert_eq!(7u32.cond_shl(32), (7, false));
        assert_eq!(0xe0000000u32.cond_shr(10), (0xe0000000u32 >> 10, true));
        assert_eq!(0xe0000000u32.cond_shr(31), (1u32, true));
        assert_eq!(0xe0000000u32.cond_shr(32), (0xe0000000u32, false));
    }

    #[test]
    fn test_expr_node_bitval() {
        let ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U7, false>::variable(ec.clone());
        assert_eq!(x1.bit(2), BoolExprNode::single(ec.clone(), 3));
        assert_eq!(x1.bit(6), BoolExprNode::single(ec.clone(), 7));
        let x1 = IntExprNode::<isize, U7, true>::variable(ec.clone());
        assert_eq!(x1.bit(3), BoolExprNode::single(ec.clone(), 11));
    }

    #[test]
    fn test_expr_node_bitmask() {
        let ec = ExprCreator::new();
        let bx1 = BoolExprNode::variable(ec.clone());
        let bx2 = BoolExprNode::variable(ec.clone());
        let bxp1 = bx1 ^ bx2;
        assert_eq!(
            IntExprNode::filled_expr(bxp1.clone()),
            <IntExprNode<isize, U8, false> as BitMask<BoolExprNode<isize>>>::bitmask(bxp1.clone())
        );
        assert_eq!(
            IntExprNode::filled_expr(bxp1.clone()),
            <IntExprNode<isize, U8, true> as BitMask<BoolExprNode<isize>>>::bitmask(bxp1.clone())
        );
    }

    #[test]
    fn test_expr_node_int_constant() {
        let ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U9, false>::constant(ec.clone(), 0b11011001);
        assert_eq!([1, 0, 0, 1, 1, 0, 1, 1, 0], *x1.indexes);
        let x1 = IntExprNode::<isize, U8, true>::constant(ec.clone(), 0b00111001);
        assert_eq!([1, 0, 0, 1, 1, 1, 0, 0], *x1.indexes);
        let x1 = IntExprNode::<isize, U10, true>::constant(ec.clone(), -15);
        assert_eq!([1, 0, 0, 0, 1, 1, 1, 1, 1, 1], *x1.indexes);
        let x1 = IntExprNode::<isize, U64, false>::constant(ec.clone(), 1848549293434211u64);
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
    fn test_expr_node_try_int_constant() {
        let ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U9, false>::try_constant(ec.clone(), 0b11011001u16).unwrap();
        assert_eq!([1, 0, 0, 1, 1, 0, 1, 1, 0], *x1.indexes);
        let x1 = IntExprNode::<isize, U8, true>::try_constant(ec.clone(), 0b00111001i16).unwrap();
        assert_eq!([1, 0, 0, 1, 1, 1, 0, 0], *x1.indexes);
        let x1 = IntExprNode::<isize, U10, true>::try_constant(ec.clone(), -15i8).unwrap();
        assert_eq!([1, 0, 0, 0, 1, 1, 1, 1, 1, 1], *x1.indexes);
        let x1 = IntExprNode::<isize, U64, false>::try_constant(ec.clone(), 1848549293434211u64)
            .unwrap();
        assert_eq!(
            (0..64)
                .into_iter()
                .map(|x| ((1848549293434211u64 >> x) & 1) as usize)
                .collect::<Vec<_>>()
                .as_slice(),
            x1.indexes.as_slice()
        );
        let x1 = IntExprNode::<isize, U1, true>::try_constant(ec.clone(), 0i64).unwrap();
        assert_eq!([0], *x1.indexes);
        for i in 4..16 {
            assert_eq!(
                Err("Bit overflow".to_string()),
                IntExprNode::<isize, U4, false>::try_constant(ec.clone(), 14u16 | (1u16 << i))
                    .map_err(|x| x.to_string())
            );
        }
        for i in 4..16 {
            assert_eq!(
                Err("Bit overflow".to_string()),
                IntExprNode::<isize, U4, true>::try_constant(ec.clone(), 6i16 | (1i16 << i))
                    .map_err(|x| x.to_string())
            );
        }
        for i in 4..16 {
            assert_eq!(
                Err("Bit overflow".to_string()),
                IntExprNode::<isize, U4, true>::try_constant(ec.clone(), (-6i16) ^ (1i16 << i))
                    .map_err(|x| x.to_string())
            );
        }
    }

    #[test]
    fn test_expr_node_int_equal() {
        {
            let ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U5, false>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U5, false>::variable(ec.clone());
            let x3 = IntExprNode::<isize, U5, false>::variable(ec.clone());
            let x4 = IntExprNode::<isize, U5, false>::variable(ec.clone());
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
            let x1 = IntExprNode::<isize, U9, false>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U9, false>::variable(ec.clone());
            let reseq = x1.equal(135);
            let resne = x2.nequal(74);
            assert_eq!(expeq, reseq);
            assert_eq!(expne, resne);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U9, false>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U9, false>::variable(ec.clone());
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
            let x1 = IntExprNode::<isize, U9, true>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U9, true>::variable(ec.clone());
            let reseq = x1.equal(-121);
            let resne = x2.nequal(-54);
            assert_eq!(expeq, reseq);
            assert_eq!(expne, resne);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U9, true>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U9, true>::variable(ec.clone());
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
                .map(|_| IntExprNode::<isize, U5, false>::variable(ec.clone()))
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
            let x1 = IntExprNode::<isize, U10, false>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U10, false>::variable(ec.clone());
            let x3 = IntExprNode::<isize, U10, false>::variable(ec.clone());
            let x4 = IntExprNode::<isize, U10, false>::variable(ec.clone());

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
            let x1 = IntExprNode::<isize, U10, false>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U10, false>::variable(ec.clone());
            let x3 = IntExprNode::<isize, U10, false>::variable(ec.clone());
            let x4 = IntExprNode::<isize, U10, false>::variable(ec.clone());

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
                .map(|_| IntExprNode::<isize, U5, true>::variable(ec.clone()))
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
            let x1 = IntExprNode::<isize, U10, true>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U10, true>::variable(ec.clone());
            let x3 = IntExprNode::<isize, U10, true>::variable(ec.clone());
            let x4 = IntExprNode::<isize, U10, true>::variable(ec.clone());

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
            let x1 = IntExprNode::<isize, U10, true>::variable(ec.clone());
            let x2 = IntExprNode::<isize, U10, true>::variable(ec.clone());
            let x3 = IntExprNode::<isize, U10, true>::variable(ec.clone());
            let x4 = IntExprNode::<isize, U10, true>::variable(ec.clone());

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
