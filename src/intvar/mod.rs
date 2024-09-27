// mod.rs - integer expression structures.
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
//! The module to generate CNF clauses from integer expressions better than `intexpr` module.
//! It offers same functionality as `intexpr`, reference support, simpler conversion
//! from integers, improved concatenation, standard binary arithmetic operators overloading.
//! To write some formula `boolvar::call16`, `boolvar::call32` or `boolvar::callsys` should be
//! used to call routine that generates formula by using this module.
//!
//! IMPORTANT: About overloading standard arithmetic operators. Any operations done in modular
//! arithmetic without checking carry, overflow and underflow. Therefore IntVar type should be
//! treat as modular arithmetic type.
//!
//! About usage of immediates with `IntVar`. it easier than in `IntExprNode`. Regardless
//! what is length of integer, any conversion from integer with same signess be done
//! automatically. It just possible to write: `a + 12u8` and `a` can have any length.
//! If conversion fails then program panicked.
//!
//! The simple example of usage:
//! ```
//! use cnfgen::boolvar::*;
//! use cnfgen::intvar::*;
//! use cnfgen::writer::{CNFError, CNFWriter};
//! use std::io;
//! fn write_diophantine_equation() -> Result<(), CNFError> {
//!     let formula: BoolVar32 = call32(|| {
//!         // define variables - signed 32-bit wide.
//!         let x = I32Var32::var();
//!         let y = I32Var32::var();
//!         let z = I32Var32::var();
//!         // define equation: x^2 + y^2 - 77*z^2 = 0
//!         let powx = (&x).fullmul(&x);  // x^2
//!         let powy = (&y).fullmul(&y);  // y^2
//!         let powz = (&z).fullmul(&z);  // z^2
//!         // We use cond_mul to get product and required condition to avoid overflow.
//!         let (prod, cond0) = powz.cond_mul(77i64);
//!         // Similary, we use conditional addition and conditional subtraction.
//!         let (sum1, cond1) = powx.cond_add(powy);
//!         let (diff2, cond2) = sum1.cond_sub(prod);
//!         // define final formula with required conditions.
//!         diff2.equal(0) & cond0 & cond1 & cond2
//!     });
//!     // write CNF to stdout.
//!     formula.write(&mut CNFWriter::new(io::stdout()))
//! }
//! ```

use std::cmp;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};

use generic_array::typenum::*;
use generic_array::*;

use crate::boolexpr::BoolExprNode;
use crate::boolvar::{BoolVar, EXPR_CREATOR_16, EXPR_CREATOR_32, EXPR_CREATOR_SYS};
use crate::dynintexpr::DynIntExprNode;
use crate::dynintvar::DynIntVar;
use crate::intexpr::{IntError, IntExprNode};
use crate::writer::{Literal, VarLit};
use crate::{impl_int_ipty, impl_int_ty1_lt_ty2, impl_int_upty};

use crate::intexpr;
pub use crate::intexpr::traits::*;

pub mod arith;
pub use arith::*;

/// The main structure that represents integer expression, subexpression or integer value.
///
/// It provides same operations as IntExprNode but they are easier to use
/// thanks simpler and easier to use interface that allow references and implements
/// standard arithmetic operators like addition, subtraction but with modular arithmetic rules.
/// Simple examples:
///
/// * `((x1 << x2) + x3).equal(x3)`
/// * `x1.fullmul(x1) + x2.fullmul(x2)`
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntVar<T: VarLit + Debug, N: ArrayLength<usize>, const SIGN: bool>(
    IntExprNode<T, N, SIGN>,
);

impl<T, N: ArrayLength<usize>, const SIGN: bool> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Number of BITS.
    pub const BITS: usize = N::USIZE;
    /// SIGN of integer. It can be false - unsigned, or true - signed.
    pub const SIGN: bool = SIGN;
    /// Internally used logarithm of number of bits.
    pub const LOG_BITS: usize = IntExprNode::<T, N, SIGN>::LOG_BITS;
}

macro_rules! impl_create_var {
    ($t:ident, $creator:ident) => {
        impl<N: ArrayLength<usize>, const SIGN: bool> IntVar<$t, N, SIGN> {
            pub fn var() -> Self {
                $creator.with_borrow(|ec| {
                    Self(IntExprNode::<$t, N, SIGN>::variable(ec.clone().unwrap()))
                })
            }

            pub fn filled_lit(v: impl Into<Literal<$t>>) -> Self {
                $creator.with_borrow(|ec| {
                    Self(IntExprNode::<$t, N, SIGN>::filled(ec.clone().unwrap(), v))
                })
            }
        }
    };
}

impl_create_var!(i16, EXPR_CREATOR_16);
impl_create_var!(i32, EXPR_CREATOR_32);
impl_create_var!(isize, EXPR_CREATOR_SYS);

impl<T, N: ArrayLength<usize>, const SIGN: bool> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer from boolean expressions. An argument is object convertible into
    /// iterator of `BoolExprNode`.
    pub fn from_iter<ITP: Into<BoolVar<T>>>(iter: impl IntoIterator<Item = ITP>) -> Option<Self> {
        IntExprNode::from_boolexprs(iter.into_iter().map(|x| BoolExprNode::from(x.into())))
            .map(|x| Self(x))
    }

    pub fn filled(v: impl Into<BoolVar<T>>) -> Self {
        Self(IntExprNode::filled_expr(BoolExprNode::from(v.into())))
    }

    /// Casts integer into unsigned integer.
    pub fn as_unsigned(self) -> IntVar<T, N, false> {
        IntVar::<T, N, false>::from(self.0.as_unsigned())
    }

    /// Casts integer into signed integer.
    pub fn as_signed(self) -> IntVar<T, N, true> {
        IntVar::<T, N, true>::from(self.0.as_signed())
    }
}

impl<T, N: ArrayLength<usize>> IntVar<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer that contains `N2` bits starting from `start`.
    pub fn subvalue<N2>(&self, start: usize) -> IntVar<T, N2, false>
    where
        N2: ArrayLength<usize>,
    {
        IntVar::<T, N2, false>(self.0.subvalue::<N2>(start))
    }

    /// Creates integer that contains `N2` bits starting from `start`.
    pub fn subv<N2>(&self, start: usize) -> IntVar<T, N2, false>
    where
        N2: ArrayLength<usize>,
    {
        IntVar::<T, N2, false>(self.0.subvalue::<N2>(start))
    }

    /// Creates integer that contains `N2` selected bits. List of bits given in
    /// object that can be converted into iterator of indexes. It returns None if
    /// number of elements in iterator doesn't match.
    pub fn select_bits<N2, I>(&self, iter: I) -> Option<IntVar<T, N2, false>>
    where
        N2: ArrayLength<usize>,
        I: IntoIterator<Item = usize>,
    {
        self.0.select_bits::<N2, I>(iter).map(|x| x.into())
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn concat<N2>(self, rest: IntVar<T, N2, false>) -> IntVar<T, Sum<N, N2>, false>
    where
        N: Add<N2>,
        N2: ArrayLength<usize>,
        Sum<N, N2>: ArrayLength<usize>,
    {
        IntVar::<T, Sum<N, N2>, false>(self.0.concat::<N2>(rest.into()))
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn cat<N2>(self, rest: IntVar<T, N2, false>) -> IntVar<T, Sum<N, N2>, false>
    where
        N: Add<N2>,
        N2: ArrayLength<usize>,
        Sum<N, N2>: ArrayLength<usize>,
    {
        IntVar::<T, Sum<N, N2>, false>(self.0.concat::<N2>(rest.into()))
    }

    /// Creates integer of concatenation of iterator
    pub fn concat_iter<N2>(
        iter: impl IntoIterator<Item = Self>,
    ) -> Option<IntVar<T, Prod<N, N2>, false>>
    where
        N: Mul<N2>,
        N2: ArrayLength<usize>,
        Prod<N, N2>: ArrayLength<usize>,
    {
        IntVar::<T, Prod<N, N2>, false>::from_iter(
            iter.into_iter()
                .map(|x| {
                    let v = x.iter().collect::<Vec<_>>();
                    v.into_iter()
                })
                .flatten(),
        )
    }

    /// Creates integer of concatenation of iterator
    pub fn cat_iter<N2>(
        iter: impl IntoIterator<Item = Self>,
    ) -> Option<IntVar<T, Prod<N, N2>, false>>
    where
        N: Mul<N2>,
        N2: ArrayLength<usize>,
        Prod<N, N2>: ArrayLength<usize>,
    {
        Self::concat_iter(iter)
    }

    /// Splits integer into two parts: the first with `K` bits and second with rest of bits.
    pub fn split<K>(
        self,
    ) -> (
        IntVar<T, K, false>,
        IntVar<T, operator_aliases::Diff<N, K>, false>,
    )
    where
        N: Sub<K>,
        K: ArrayLength<usize>,
        operator_aliases::Diff<N, K>: ArrayLength<usize>,
    {
        let (s1, s2) = self.0.split::<K>();
        (
            IntVar::<T, K, false>(s1),
            IntVar::<T, operator_aliases::Diff<N, K>, false>(s2),
        )
    }
}

impl<T> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn to_int1(self) -> IntVar<T, U1, false> {
        IntVar::filled(self)
    }
}

// TryFrom implementation
macro_rules! impl_int_try_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                TryFrom<IntVar<T, $ty2, SIGN2>> for IntVar<T, $ty1, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntVar<T, $ty2, SIGN2>) -> Result<Self, Self::Error> {
                IntExprNode::<T, $ty1, false>::try_from(v.0).map(|x| Self(x))
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntVar<T, $ty2, false>> for IntVar<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntVar<T, $ty2, false>) -> Result<Self, Self::Error> {
                IntExprNode::<T, $ty1, true>::try_from(v.0).map(|x| Self(x))
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntVar<T, $ty2, true>> for IntVar<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntVar<T, $ty2, true>) -> Result<Self, Self::Error> {
                IntExprNode::<T, $ty1, true>::try_from(v.0).map(|x| Self(x))
            }
        }

        // try from for rest
        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntVar<T, $ty1, true>> for IntVar<T, $ty2, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntVar<T, $ty1, true>) -> Result<Self, Self::Error> {
                IntExprNode::<T, $ty2, false>::try_from(v.0).map(|x| Self(x))
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_try_from);

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<IntVar<T, N, false>> for IntVar<T, N, true> {
    type Error = IntError;

    fn try_from(v: IntVar<T, N, false>) -> Result<Self, Self::Error> {
        IntExprNode::<T, N, true>::try_from(v.0).map(|x| Self(x))
    }
}

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<IntVar<T, N, true>> for IntVar<T, N, false> {
    type Error = IntError;

    fn try_from(v: IntVar<T, N, true>) -> Result<Self, Self::Error> {
        IntExprNode::<T, N, false>::try_from(v.0).map(|x| Self(x))
    }
}

// From implementation
macro_rules! impl_int_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                From<IntVar<T, $ty1, false>> for IntVar<T, $ty2, SIGN2>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: IntVar<T, $ty1, false>) -> Self {
                Self(IntExprNode::<T, $ty2, SIGN2>::from(v.0))
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                From<IntVar<T, $ty1, true>> for IntVar<T, $ty2, true>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: IntVar<T, $ty1, true>) -> Self {
                Self(IntExprNode::<T, $ty2, true>::from(v.0))
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_from);

impl<T, N, const SIGN: bool> From<IntVar<T, N, SIGN>> for IntExprNode<T, N, SIGN>
where
    T: VarLit + Debug,
    N: ArrayLength<usize>,
{
    fn from(t: IntVar<T, N, SIGN>) -> Self {
        t.0
    }
}

impl<T, N, const SIGN: bool> From<IntExprNode<T, N, SIGN>> for IntVar<T, N, SIGN>
where
    T: VarLit + Debug,
    N: ArrayLength<usize>,
{
    fn from(t: IntExprNode<T, N, SIGN>) -> Self {
        Self(t)
    }
}

impl<T: VarLit, N: ArrayLength<usize>, const SIGN: bool> TryFrom<DynIntVar<T, SIGN>>
    for IntVar<T, N, SIGN>
{
    type Error = IntError;

    fn try_from(v: DynIntVar<T, SIGN>) -> Result<Self, Self::Error> {
        DynIntExprNode::from(v).try_into().map(|x| Self(x))
    }
}

// conversion from integers

macro_rules! impl_xint_from {
    ($t:ident, $creator:ident) => {
        macro_rules! impl_uint_from_x {
            ($pty:ty) => {
                impl<N> From<$pty> for IntVar<$t, N, false>
                where
                    N: ArrayLength<usize>,
                    IntExprNode<$t, N, false>: TryIntConstant<$t, $pty>,
                {
                    fn from(value: $pty) -> Self {
                        $creator.with_borrow(|ec| {
                            IntExprNode::<$t, N, false>::try_constant(ec.clone().unwrap(), value)
                                .map(|x| Self(x))
                                .unwrap()
                        })
                    }
                }
            };
        }

        impl_int_upty!(impl_uint_from_x);

        macro_rules! impl_int_from_x {
            ($pty:ty) => {
                impl<N> From<$pty> for IntVar<$t, N, true>
                where
                    N: ArrayLength<usize>,
                    IntExprNode<$t, N, true>: TryIntConstant<$t, $pty>,
                {
                    fn from(value: $pty) -> Self {
                        $creator.with_borrow(|ec| {
                            IntExprNode::<$t, N, true>::try_constant(ec.clone().unwrap(), value)
                                .map(|x| Self(x))
                                .unwrap()
                        })
                    }
                }
            };
        }

        impl_int_ipty!(impl_int_from_x);
    };
}

impl_xint_from!(i16, EXPR_CREATOR_16);
impl_xint_from!(i32, EXPR_CREATOR_32);
impl_xint_from!(isize, EXPR_CREATOR_SYS);

macro_rules! impl_default {
    ($t:ident, $creator:ident) => {
        impl<N> Default for IntVar<$t, N, false>
        where
            N: ArrayLength<usize>,
            IntExprNode<$t, N, false>: TryIntConstant<$t, u8>,
        {
            fn default() -> Self {
                Self::from(0u8)
            }
        }

        impl<N> Default for IntVar<$t, N, true>
        where
            N: ArrayLength<usize>,
            IntExprNode<$t, N, true>: TryIntConstant<$t, i8>,
        {
            fn default() -> Self {
                Self::from(0i8)
            }
        }
    };
}

impl_default!(i16, EXPR_CREATOR_16);
impl_default!(i32, EXPR_CREATOR_32);
impl_default!(isize, EXPR_CREATOR_SYS);

impl<'a, T, N, const SIGN: bool> BitVal for &'a IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    #[inline]
    fn bitnum(self) -> usize {
        N::USIZE
    }

    fn bit(self, x: usize) -> Self::Output {
        BoolVar::from(self.0.bit(x))
    }
}

impl<T, N, const SIGN: bool> BitMask<BoolExprNode<T>> for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    fn bitmask(t: BoolExprNode<T>) -> Self {
        Self(IntExprNode::bitmask(t))
    }
}

impl<T, N, const SIGN: bool> BitMask<BoolVar<T>> for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    fn bitmask(t: BoolVar<T>) -> Self {
        Self(IntExprNode::bitmask(t.into()))
    }
}

// IntEqual

impl<T, N, const SIGN: bool> IntEqual for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.equal(rhs.0))
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.nequal(rhs.0))
    }
}

impl<T, N, const SIGN: bool> IntEqual<IntVar<T, N, SIGN>> for &IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
        BoolVar::from(self.0.clone().equal(rhs.0))
    }

    fn nequal(self, rhs: IntVar<T, N, SIGN>) -> Self::Output {
        BoolVar::from(self.0.clone().nequal(rhs.0))
    }
}

impl<T, N, const SIGN: bool> IntEqual<&IntVar<T, N, SIGN>> for IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
        BoolVar::from(self.0.equal(rhs.0.clone()))
    }

    fn nequal(self, rhs: &IntVar<T, N, SIGN>) -> Self::Output {
        BoolVar::from(self.0.nequal(rhs.0.clone()))
    }
}

impl<T, N, const SIGN: bool> IntEqual for &IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.clone().equal(rhs.0.clone()))
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.clone().nequal(rhs.0.clone()))
    }
}

macro_rules! int_equal_uint_x_sign {
    ($pty:ty, $sign:expr) => {
        impl<T, N: ArrayLength<usize>> IntEqual<$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: $pty) -> Self::Output {
                self.equal(Self::from(rhs))
            }

            fn nequal(self, rhs: $pty) -> Self::Output {
                self.nequal(Self::from(rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntEqual<&$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: &$pty) -> Self::Output {
                self.equal(Self::from(*rhs))
            }

            fn nequal(self, rhs: &$pty) -> Self::Output {
                self.nequal(Self::from(*rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntEqual<$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: $pty) -> Self::Output {
                self.equal(IntVar::<T, N, $sign>::from(rhs))
            }

            fn nequal(self, rhs: $pty) -> Self::Output {
                self.nequal(IntVar::<T, N, $sign>::from(rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntEqual<&$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: &$pty) -> Self::Output {
                self.equal(IntVar::<T, N, $sign>::from(*rhs))
            }

            fn nequal(self, rhs: &$pty) -> Self::Output {
                self.nequal(IntVar::<T, N, $sign>::from(*rhs))
            }
        }

        impl<T, N: ArrayLength<usize>> IntEqual<IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self).equal(rhs)
            }

            fn nequal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self).nequal(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntEqual<&IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self.clone()).equal(rhs)
            }

            fn nequal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self.clone()).nequal(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntEqual<IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).equal(rhs)
            }

            fn nequal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).nequal(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntEqual<&IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).equal(rhs)
            }

            fn nequal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).nequal(rhs)
            }
        }
    };
}

macro_rules! int_equal_uint_x_unsigned {
    ($pty:ty) => {
        int_equal_uint_x_sign!($pty, false);
    };
}

impl_int_upty!(int_equal_uint_x_unsigned);

macro_rules! int_equal_uint_x_signed {
    ($pty:ty) => {
        int_equal_uint_x_sign!($pty, true);
    };
}

impl_int_ipty!(int_equal_uint_x_signed);

// IntOrd

macro_rules! impl_selfxint_ord {
    ($sign:expr) => {
        impl<T, N> IntOrd for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.less_than(rhs.0))
            }

            fn less_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.less_equal(rhs.0))
            }

            fn greater_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.greater_than(rhs.0))
            }

            fn greater_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.greater_equal(rhs.0))
            }
        }

        impl<T, N> IntOrd<IntVar<T, N, $sign>> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().less_than(rhs.0))
            }

            fn less_equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().less_equal(rhs.0))
            }

            fn greater_than(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().greater_than(rhs.0))
            }

            fn greater_equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().greater_equal(rhs.0))
            }
        }

        impl<T, N> IntOrd<&IntVar<T, N, $sign>> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.less_than(rhs.0.clone()))
            }

            fn less_equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.less_equal(rhs.0.clone()))
            }

            fn greater_than(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.greater_than(rhs.0.clone()))
            }

            fn greater_equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                BoolVar::from(self.0.greater_equal(rhs.0.clone()))
            }
        }

        impl<T, N> IntOrd for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().less_than(rhs.0.clone()))
            }

            fn less_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().less_equal(rhs.0.clone()))
            }

            fn greater_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().greater_than(rhs.0.clone()))
            }

            fn greater_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().greater_equal(rhs.0.clone()))
            }
        }
    };
}

impl_selfxint_ord!(false);
impl_selfxint_ord!(true);

macro_rules! int_ord_uint_x_sign {
    ($pty:ty, $sign:expr) => {
        impl<T, N: ArrayLength<usize>> IntOrd<$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: $pty) -> Self::Output {
                self.less_than(Self::from(rhs))
            }

            fn less_equal(self, rhs: $pty) -> Self::Output {
                self.less_equal(Self::from(rhs))
            }

            fn greater_than(self, rhs: $pty) -> Self::Output {
                self.greater_than(Self::from(rhs))
            }

            fn greater_equal(self, rhs: $pty) -> Self::Output {
                self.greater_equal(Self::from(rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntOrd<&$pty> for IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &$pty) -> Self::Output {
                self.less_than(Self::from(*rhs))
            }

            fn less_equal(self, rhs: &$pty) -> Self::Output {
                self.less_equal(Self::from(*rhs))
            }

            fn greater_than(self, rhs: &$pty) -> Self::Output {
                self.greater_than(Self::from(*rhs))
            }

            fn greater_equal(self, rhs: &$pty) -> Self::Output {
                self.greater_equal(Self::from(*rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntOrd<$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: $pty) -> Self::Output {
                self.less_than(IntVar::<T, N, $sign>::from(rhs))
            }

            fn less_equal(self, rhs: $pty) -> Self::Output {
                self.less_equal(IntVar::<T, N, $sign>::from(rhs))
            }

            fn greater_than(self, rhs: $pty) -> Self::Output {
                self.greater_than(IntVar::<T, N, $sign>::from(rhs))
            }

            fn greater_equal(self, rhs: $pty) -> Self::Output {
                self.greater_equal(IntVar::<T, N, $sign>::from(rhs))
            }
        }
        impl<T, N: ArrayLength<usize>> IntOrd<&$pty> for &IntVar<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &$pty) -> Self::Output {
                self.less_than(IntVar::<T, N, $sign>::from(*rhs))
            }

            fn less_equal(self, rhs: &$pty) -> Self::Output {
                self.less_equal(IntVar::<T, N, $sign>::from(*rhs))
            }

            fn greater_than(self, rhs: &$pty) -> Self::Output {
                self.greater_than(IntVar::<T, N, $sign>::from(*rhs))
            }

            fn greater_equal(self, rhs: &$pty) -> Self::Output {
                self.greater_equal(IntVar::<T, N, $sign>::from(*rhs))
            }
        }

        impl<T, N: ArrayLength<usize>> IntOrd<IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self).less_than(rhs)
            }

            fn less_equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self).less_equal(rhs)
            }

            fn greater_than(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self).greater_than(rhs)
            }

            fn greater_equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self).greater_equal(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntOrd<&IntVar<T, N, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self.clone()).less_than(rhs)
            }

            fn less_equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self.clone()).less_equal(rhs)
            }

            fn greater_than(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self.clone()).greater_than(rhs)
            }

            fn greater_equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(self.clone()).greater_equal(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntOrd<IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).less_than(rhs)
            }

            fn less_equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).less_equal(rhs)
            }

            fn greater_than(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).greater_than(rhs)
            }

            fn greater_equal(self, rhs: IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).greater_equal(rhs)
            }
        }
        impl<T, N: ArrayLength<usize>> IntOrd<&IntVar<T, N, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            IntVar<T, N, $sign>: From<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).less_than(rhs)
            }

            fn less_equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).less_equal(rhs)
            }

            fn greater_than(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).greater_than(rhs)
            }

            fn greater_equal(self, rhs: &IntVar<T, N, $sign>) -> Self::Output {
                IntVar::<T, N, $sign>::from(*self).greater_equal(rhs)
            }
        }
    };
}

macro_rules! int_ord_uint_x_unsigned {
    ($pty:ty) => {
        int_ord_uint_x_sign!($pty, false);
    };
}

impl_int_upty!(int_ord_uint_x_unsigned);

macro_rules! int_ord_uint_x_signed {
    ($pty:ty) => {
        int_ord_uint_x_sign!($pty, true);
    };
}

impl_int_ipty!(int_ord_uint_x_signed);

pub use crate::intexpr::{int_ite, int_max, int_min};

pub fn int_ite_r<T, N: ArrayLength<usize>, const SIGN: bool>(
    c: &BoolVar<T>,
    t: &IntVar<T, N, SIGN>,
    e: &IntVar<T, N, SIGN>,
) -> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    int_ite(c.clone(), t.clone(), e.clone())
}

pub fn int_min_r<T, N: ArrayLength<usize>, const SIGN: bool>(
    t: &IntVar<T, N, SIGN>,
    e: &IntVar<T, N, SIGN>,
) -> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    IntVar<T, N, SIGN>: Clone + IntOrd<IntVar<T, N, SIGN>>,
    IntVar<T, N, SIGN>: BitMask<<IntVar<T, N, SIGN> as IntOrd>::Output>,
    IntVar<T, N, SIGN>: BitMask<<<IntVar<T, N, SIGN> as IntOrd>::Output as std::ops::Not>::Output>,
    <IntVar<T, N, SIGN> as IntOrd>::Output: Clone + std::ops::Not,
{
    int_min(t.clone(), e.clone())
}

pub fn int_max_r<T, N: ArrayLength<usize>, const SIGN: bool>(
    t: &IntVar<T, N, SIGN>,
    e: &IntVar<T, N, SIGN>,
) -> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    IntVar<T, N, SIGN>: Clone + IntOrd<IntVar<T, N, SIGN>>,
    IntVar<T, N, SIGN>: BitMask<<IntVar<T, N, SIGN> as IntOrd>::Output>,
    IntVar<T, N, SIGN>: BitMask<<<IntVar<T, N, SIGN> as IntOrd>::Output as std::ops::Not>::Output>,
    <IntVar<T, N, SIGN> as IntOrd>::Output: Clone + std::ops::Not,
{
    int_max(t.clone(), e.clone())
}

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions.
pub fn int_table<T, N, K, I, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    table_iter: I,
) -> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = IntVar<T, N, SIGN>>,
{
    IntVar::<T, N, SIGN>(intexpr::int_table(
        index.into(),
        table_iter.into_iter().map(|x| x.into()),
    ))
}

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
pub fn int_table_partial<T, N, K, I, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    table_iter: I,
    fill: IntVar<T, N, SIGN>,
) -> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = IntVar<T, N, SIGN>>,
{
    let tbl = table_iter
        .into_iter()
        .take(1 << K::USIZE)
        .map(|x| x.into())
        .collect::<Vec<_>>();
    let tbl_len = tbl.len();
    IntVar::<T, N, SIGN>(intexpr::int_table(
        index.into(),
        tbl.into_iter()
            .chain(std::iter::repeat(fill.into()).take((1 << K::USIZE) - tbl_len)),
    ))
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions.
pub fn int_booltable<T, K, I, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    table_iter: I,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = BoolVar<T>>,
{
    BoolVar::<T>::from(intexpr::int_booltable(
        index.into(),
        table_iter.into_iter().map(|x| x.into()),
    ))
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
pub fn int_booltable_partial<T, K, I, BTP, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    table_iter: I,
    fill: BTP,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = BoolVar<T>>,
    BTP: Into<BoolVar<T>>,
{
    let tbl = table_iter
        .into_iter()
        .take(1 << K::USIZE)
        .map(|x| x.into())
        .collect::<Vec<_>>();
    let tbl_len = tbl.len();
    BoolVar::<T>::from(intexpr::int_booltable(
        index.into(),
        tbl.into_iter()
            .chain(std::iter::repeat(fill.into().into()).take((1 << K::USIZE) - tbl_len)),
    ))
}

/// Demulitplexer - returns list of outputs of demulitplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn int_demux<T, N, K, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    value: IntVar<T, N, SIGN>,
) -> Vec<IntVar<T, N, SIGN>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
{
    intexpr::int_demux(index.into(), value.into())
        .into_iter()
        .map(|x| x.into())
        .collect::<Vec<_>>()
}

/// Demulitplexer - returns list of outputs of demulitplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn int_booldemux<T, K, BTP, const SIGN: bool>(
    index: IntVar<T, K, SIGN>,
    value: BTP,
) -> Vec<BoolVar<T>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
    BTP: Into<BoolVar<T>>,
{
    intexpr::int_booldemux(index.into(), value.into().into())
        .into_iter()
        .map(|x| x.into())
        .collect::<Vec<_>>()
}

// version with references

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions.
pub fn int_table_r<T, N, K, I, const SIGN: bool>(
    index: &IntVar<T, K, SIGN>,
    table_iter: I,
) -> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = IntVar<T, N, SIGN>>,
{
    int_table(index.clone(), table_iter)
}

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
pub fn int_table_partial_r<T, N, K, I, const SIGN: bool>(
    index: &IntVar<T, K, SIGN>,
    table_iter: I,
    fill: &IntVar<T, N, SIGN>,
) -> IntVar<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = IntVar<T, N, SIGN>>,
{
    int_table_partial(index.clone(), table_iter, fill.clone())
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions.
pub fn int_booltable_r<T, K, I, const SIGN: bool>(
    index: &IntVar<T, K, SIGN>,
    table_iter: I,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = BoolVar<T>>,
{
    int_booltable::<T, K, I, SIGN>(index.clone(), table_iter)
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
pub fn int_booltable_partial_r<T, K, I, const SIGN: bool>(
    index: &IntVar<T, K, SIGN>,
    table_iter: I,
    fill: &BoolVar<T>,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = BoolVar<T>>,
{
    int_booltable_partial::<T, K, I, BoolVar<T>, SIGN>(index.clone(), table_iter, fill.clone())
}

/// Demulitplexer - returns list of outputs of demulitplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn int_demux_r<T, N, K, const SIGN: bool>(
    index: &IntVar<T, K, SIGN>,
    value: &IntVar<T, N, SIGN>,
) -> Vec<IntVar<T, N, SIGN>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
{
    int_demux(index.clone(), value.clone())
}

/// Demulitplexer - returns list of outputs of demulitplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn int_booldemux_r<T, K, const SIGN: bool>(
    index: &IntVar<T, K, SIGN>,
    value: &BoolVar<T>,
) -> Vec<BoolVar<T>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
{
    int_booldemux(index.clone(), value.clone())
}

pub type IntVar16<N, const SIGN: bool> = IntVar<i16, N, SIGN>;

pub type UVar16<N> = IntVar<i16, N, false>;
pub type IVar16<N> = IntVar<i16, N, true>;

pub type U1Var16 = IntVar<i16, U1, false>;
pub type I1Var16 = IntVar<i16, U1, true>;
pub type U2Var16 = IntVar<i16, U2, false>;
pub type I2Var16 = IntVar<i16, U2, true>;
pub type U3Var16 = IntVar<i16, U3, false>;
pub type I3Var16 = IntVar<i16, U3, true>;
pub type U4Var16 = IntVar<i16, U4, false>;
pub type I4Var16 = IntVar<i16, U4, true>;
pub type U5Var16 = IntVar<i16, U5, false>;
pub type I5Var16 = IntVar<i16, U5, true>;
pub type U6Var16 = IntVar<i16, U6, false>;
pub type I6Var16 = IntVar<i16, U6, true>;
pub type U7Var16 = IntVar<i16, U7, false>;
pub type I7Var16 = IntVar<i16, U7, true>;
pub type U8Var16 = IntVar<i16, U8, false>;
pub type I8Var16 = IntVar<i16, U8, true>;
pub type U9Var16 = IntVar<i16, U9, false>;
pub type I9Var16 = IntVar<i16, U9, true>;
pub type U10Var16 = IntVar<i16, U10, false>;
pub type I10Var16 = IntVar<i16, U10, true>;
pub type U11Var16 = IntVar<i16, U11, false>;
pub type I11Var16 = IntVar<i16, U11, true>;
pub type U12Var16 = IntVar<i16, U12, false>;
pub type I12Var16 = IntVar<i16, U12, true>;
pub type U13Var16 = IntVar<i16, U13, false>;
pub type I13Var16 = IntVar<i16, U13, true>;
pub type U14Var16 = IntVar<i16, U14, false>;
pub type I14Var16 = IntVar<i16, U14, true>;
pub type U15Var16 = IntVar<i16, U15, false>;
pub type I15Var16 = IntVar<i16, U15, true>;
pub type U16Var16 = IntVar<i16, U16, false>;
pub type I16Var16 = IntVar<i16, U16, true>;
pub type U17Var16 = IntVar<i16, U17, false>;
pub type I17Var16 = IntVar<i16, U17, true>;
pub type U18Var16 = IntVar<i16, U18, false>;
pub type I18Var16 = IntVar<i16, U18, true>;
pub type U19Var16 = IntVar<i16, U19, false>;
pub type I19Var16 = IntVar<i16, U19, true>;
pub type U20Var16 = IntVar<i16, U20, false>;
pub type I20Var16 = IntVar<i16, U20, true>;
pub type U21Var16 = IntVar<i16, U21, false>;
pub type I21Var16 = IntVar<i16, U21, true>;
pub type U22Var16 = IntVar<i16, U22, false>;
pub type I22Var16 = IntVar<i16, U22, true>;
pub type U23Var16 = IntVar<i16, U23, false>;
pub type I23Var16 = IntVar<i16, U23, true>;
pub type U24Var16 = IntVar<i16, U24, false>;
pub type I24Var16 = IntVar<i16, U24, true>;
pub type U25Var16 = IntVar<i16, U25, false>;
pub type I25Var16 = IntVar<i16, U25, true>;
pub type U26Var16 = IntVar<i16, U26, false>;
pub type I26Var16 = IntVar<i16, U26, true>;
pub type U27Var16 = IntVar<i16, U27, false>;
pub type I27Var16 = IntVar<i16, U27, true>;
pub type U28Var16 = IntVar<i16, U28, false>;
pub type I28Var16 = IntVar<i16, U28, true>;
pub type U29Var16 = IntVar<i16, U29, false>;
pub type I29Var16 = IntVar<i16, U29, true>;
pub type U30Var16 = IntVar<i16, U30, false>;
pub type I30Var16 = IntVar<i16, U30, true>;
pub type U31Var16 = IntVar<i16, U31, false>;
pub type I31Var16 = IntVar<i16, U31, true>;
pub type U32Var16 = IntVar<i16, U32, false>;
pub type I32Var16 = IntVar<i16, U32, true>;
pub type U33Var16 = IntVar<i16, U33, false>;
pub type I33Var16 = IntVar<i16, U33, true>;
pub type U34Var16 = IntVar<i16, U34, false>;
pub type I34Var16 = IntVar<i16, U34, true>;
pub type U35Var16 = IntVar<i16, U35, false>;
pub type I35Var16 = IntVar<i16, U35, true>;
pub type U36Var16 = IntVar<i16, U36, false>;
pub type I36Var16 = IntVar<i16, U36, true>;
pub type U37Var16 = IntVar<i16, U37, false>;
pub type I37Var16 = IntVar<i16, U37, true>;
pub type U38Var16 = IntVar<i16, U38, false>;
pub type I38Var16 = IntVar<i16, U38, true>;
pub type U39Var16 = IntVar<i16, U39, false>;
pub type I39Var16 = IntVar<i16, U39, true>;
pub type U40Var16 = IntVar<i16, U40, false>;
pub type I40Var16 = IntVar<i16, U40, true>;
pub type U41Var16 = IntVar<i16, U41, false>;
pub type I41Var16 = IntVar<i16, U41, true>;
pub type U42Var16 = IntVar<i16, U42, false>;
pub type I42Var16 = IntVar<i16, U42, true>;
pub type U43Var16 = IntVar<i16, U43, false>;
pub type I43Var16 = IntVar<i16, U43, true>;
pub type U44Var16 = IntVar<i16, U44, false>;
pub type I44Var16 = IntVar<i16, U44, true>;
pub type U45Var16 = IntVar<i16, U45, false>;
pub type I45Var16 = IntVar<i16, U45, true>;
pub type U46Var16 = IntVar<i16, U46, false>;
pub type I46Var16 = IntVar<i16, U46, true>;
pub type U47Var16 = IntVar<i16, U47, false>;
pub type I47Var16 = IntVar<i16, U47, true>;
pub type U48Var16 = IntVar<i16, U48, false>;
pub type I48Var16 = IntVar<i16, U48, true>;
pub type U49Var16 = IntVar<i16, U49, false>;
pub type I49Var16 = IntVar<i16, U49, true>;
pub type U50Var16 = IntVar<i16, U50, false>;
pub type I50Var16 = IntVar<i16, U50, true>;
pub type U51Var16 = IntVar<i16, U51, false>;
pub type I51Var16 = IntVar<i16, U51, true>;
pub type U52Var16 = IntVar<i16, U52, false>;
pub type I52Var16 = IntVar<i16, U52, true>;
pub type U53Var16 = IntVar<i16, U53, false>;
pub type I53Var16 = IntVar<i16, U53, true>;
pub type U54Var16 = IntVar<i16, U54, false>;
pub type I54Var16 = IntVar<i16, U54, true>;
pub type U55Var16 = IntVar<i16, U55, false>;
pub type I55Var16 = IntVar<i16, U55, true>;
pub type U56Var16 = IntVar<i16, U56, false>;
pub type I56Var16 = IntVar<i16, U56, true>;
pub type U57Var16 = IntVar<i16, U57, false>;
pub type I57Var16 = IntVar<i16, U57, true>;
pub type U58Var16 = IntVar<i16, U58, false>;
pub type I58Var16 = IntVar<i16, U58, true>;
pub type U59Var16 = IntVar<i16, U59, false>;
pub type I59Var16 = IntVar<i16, U59, true>;
pub type U60Var16 = IntVar<i16, U60, false>;
pub type I60Var16 = IntVar<i16, U60, true>;
pub type U61Var16 = IntVar<i16, U61, false>;
pub type I61Var16 = IntVar<i16, U61, true>;
pub type U62Var16 = IntVar<i16, U62, false>;
pub type I62Var16 = IntVar<i16, U62, true>;
pub type U63Var16 = IntVar<i16, U63, false>;
pub type I63Var16 = IntVar<i16, U63, true>;
pub type U64Var16 = IntVar<i16, U64, false>;
pub type I64Var16 = IntVar<i16, U64, true>;
pub type U65Var16 = IntVar<i16, U65, false>;
pub type I65Var16 = IntVar<i16, U65, true>;
pub type U66Var16 = IntVar<i16, U66, false>;
pub type I66Var16 = IntVar<i16, U66, true>;
pub type U67Var16 = IntVar<i16, U67, false>;
pub type I67Var16 = IntVar<i16, U67, true>;
pub type U68Var16 = IntVar<i16, U68, false>;
pub type I68Var16 = IntVar<i16, U68, true>;
pub type U69Var16 = IntVar<i16, U69, false>;
pub type I69Var16 = IntVar<i16, U69, true>;
pub type U70Var16 = IntVar<i16, U70, false>;
pub type I70Var16 = IntVar<i16, U70, true>;
pub type U71Var16 = IntVar<i16, U71, false>;
pub type I71Var16 = IntVar<i16, U71, true>;
pub type U72Var16 = IntVar<i16, U72, false>;
pub type I72Var16 = IntVar<i16, U72, true>;
pub type U73Var16 = IntVar<i16, U73, false>;
pub type I73Var16 = IntVar<i16, U73, true>;
pub type U74Var16 = IntVar<i16, U74, false>;
pub type I74Var16 = IntVar<i16, U74, true>;
pub type U75Var16 = IntVar<i16, U75, false>;
pub type I75Var16 = IntVar<i16, U75, true>;
pub type U76Var16 = IntVar<i16, U76, false>;
pub type I76Var16 = IntVar<i16, U76, true>;
pub type U77Var16 = IntVar<i16, U77, false>;
pub type I77Var16 = IntVar<i16, U77, true>;
pub type U78Var16 = IntVar<i16, U78, false>;
pub type I78Var16 = IntVar<i16, U78, true>;
pub type U79Var16 = IntVar<i16, U79, false>;
pub type I79Var16 = IntVar<i16, U79, true>;
pub type U80Var16 = IntVar<i16, U80, false>;
pub type I80Var16 = IntVar<i16, U80, true>;
pub type U81Var16 = IntVar<i16, U81, false>;
pub type I81Var16 = IntVar<i16, U81, true>;
pub type U82Var16 = IntVar<i16, U82, false>;
pub type I82Var16 = IntVar<i16, U82, true>;
pub type U83Var16 = IntVar<i16, U83, false>;
pub type I83Var16 = IntVar<i16, U83, true>;
pub type U84Var16 = IntVar<i16, U84, false>;
pub type I84Var16 = IntVar<i16, U84, true>;
pub type U85Var16 = IntVar<i16, U85, false>;
pub type I85Var16 = IntVar<i16, U85, true>;
pub type U86Var16 = IntVar<i16, U86, false>;
pub type I86Var16 = IntVar<i16, U86, true>;
pub type U87Var16 = IntVar<i16, U87, false>;
pub type I87Var16 = IntVar<i16, U87, true>;
pub type U88Var16 = IntVar<i16, U88, false>;
pub type I88Var16 = IntVar<i16, U88, true>;
pub type U89Var16 = IntVar<i16, U89, false>;
pub type I89Var16 = IntVar<i16, U89, true>;
pub type U90Var16 = IntVar<i16, U90, false>;
pub type I90Var16 = IntVar<i16, U90, true>;
pub type U91Var16 = IntVar<i16, U91, false>;
pub type I91Var16 = IntVar<i16, U91, true>;
pub type U92Var16 = IntVar<i16, U92, false>;
pub type I92Var16 = IntVar<i16, U92, true>;
pub type U93Var16 = IntVar<i16, U93, false>;
pub type I93Var16 = IntVar<i16, U93, true>;
pub type U94Var16 = IntVar<i16, U94, false>;
pub type I94Var16 = IntVar<i16, U94, true>;
pub type U95Var16 = IntVar<i16, U95, false>;
pub type I95Var16 = IntVar<i16, U95, true>;
pub type U96Var16 = IntVar<i16, U96, false>;
pub type I96Var16 = IntVar<i16, U96, true>;
pub type U97Var16 = IntVar<i16, U97, false>;
pub type I97Var16 = IntVar<i16, U97, true>;
pub type U98Var16 = IntVar<i16, U98, false>;
pub type I98Var16 = IntVar<i16, U98, true>;
pub type U99Var16 = IntVar<i16, U99, false>;
pub type I99Var16 = IntVar<i16, U99, true>;
pub type U100Var16 = IntVar<i16, U100, false>;
pub type I100Var16 = IntVar<i16, U100, true>;
pub type U101Var16 = IntVar<i16, U101, false>;
pub type I101Var16 = IntVar<i16, U101, true>;
pub type U102Var16 = IntVar<i16, U102, false>;
pub type I102Var16 = IntVar<i16, U102, true>;
pub type U103Var16 = IntVar<i16, U103, false>;
pub type I103Var16 = IntVar<i16, U103, true>;
pub type U104Var16 = IntVar<i16, U104, false>;
pub type I104Var16 = IntVar<i16, U104, true>;
pub type U105Var16 = IntVar<i16, U105, false>;
pub type I105Var16 = IntVar<i16, U105, true>;
pub type U106Var16 = IntVar<i16, U106, false>;
pub type I106Var16 = IntVar<i16, U106, true>;
pub type U107Var16 = IntVar<i16, U107, false>;
pub type I107Var16 = IntVar<i16, U107, true>;
pub type U108Var16 = IntVar<i16, U108, false>;
pub type I108Var16 = IntVar<i16, U108, true>;
pub type U109Var16 = IntVar<i16, U109, false>;
pub type I109Var16 = IntVar<i16, U109, true>;
pub type U110Var16 = IntVar<i16, U110, false>;
pub type I110Var16 = IntVar<i16, U110, true>;
pub type U111Var16 = IntVar<i16, U111, false>;
pub type I111Var16 = IntVar<i16, U111, true>;
pub type U112Var16 = IntVar<i16, U112, false>;
pub type I112Var16 = IntVar<i16, U112, true>;
pub type U113Var16 = IntVar<i16, U113, false>;
pub type I113Var16 = IntVar<i16, U113, true>;
pub type U114Var16 = IntVar<i16, U114, false>;
pub type I114Var16 = IntVar<i16, U114, true>;
pub type U115Var16 = IntVar<i16, U115, false>;
pub type I115Var16 = IntVar<i16, U115, true>;
pub type U116Var16 = IntVar<i16, U116, false>;
pub type I116Var16 = IntVar<i16, U116, true>;
pub type U117Var16 = IntVar<i16, U117, false>;
pub type I117Var16 = IntVar<i16, U117, true>;
pub type U118Var16 = IntVar<i16, U118, false>;
pub type I118Var16 = IntVar<i16, U118, true>;
pub type U119Var16 = IntVar<i16, U119, false>;
pub type I119Var16 = IntVar<i16, U119, true>;
pub type U120Var16 = IntVar<i16, U120, false>;
pub type I120Var16 = IntVar<i16, U120, true>;
pub type U121Var16 = IntVar<i16, U121, false>;
pub type I121Var16 = IntVar<i16, U121, true>;
pub type U122Var16 = IntVar<i16, U122, false>;
pub type I122Var16 = IntVar<i16, U122, true>;
pub type U123Var16 = IntVar<i16, U123, false>;
pub type I123Var16 = IntVar<i16, U123, true>;
pub type U124Var16 = IntVar<i16, U124, false>;
pub type I124Var16 = IntVar<i16, U124, true>;
pub type U125Var16 = IntVar<i16, U125, false>;
pub type I125Var16 = IntVar<i16, U125, true>;
pub type U126Var16 = IntVar<i16, U126, false>;
pub type I126Var16 = IntVar<i16, U126, true>;
pub type U127Var16 = IntVar<i16, U127, false>;
pub type I127Var16 = IntVar<i16, U127, true>;
pub type U128Var16 = IntVar<i16, U128, false>;
pub type I128Var16 = IntVar<i16, U128, true>;

pub type IntVar32<N, const SIGN: bool> = IntVar<i32, N, SIGN>;

pub type UVar32<N> = IntVar<i32, N, false>;
pub type IVar32<N> = IntVar<i32, N, true>;

pub type U1Var32 = IntVar<i32, U1, false>;
pub type I1Var32 = IntVar<i32, U1, true>;
pub type U2Var32 = IntVar<i32, U2, false>;
pub type I2Var32 = IntVar<i32, U2, true>;
pub type U3Var32 = IntVar<i32, U3, false>;
pub type I3Var32 = IntVar<i32, U3, true>;
pub type U4Var32 = IntVar<i32, U4, false>;
pub type I4Var32 = IntVar<i32, U4, true>;
pub type U5Var32 = IntVar<i32, U5, false>;
pub type I5Var32 = IntVar<i32, U5, true>;
pub type U6Var32 = IntVar<i32, U6, false>;
pub type I6Var32 = IntVar<i32, U6, true>;
pub type U7Var32 = IntVar<i32, U7, false>;
pub type I7Var32 = IntVar<i32, U7, true>;
pub type U8Var32 = IntVar<i32, U8, false>;
pub type I8Var32 = IntVar<i32, U8, true>;
pub type U9Var32 = IntVar<i32, U9, false>;
pub type I9Var32 = IntVar<i32, U9, true>;
pub type U10Var32 = IntVar<i32, U10, false>;
pub type I10Var32 = IntVar<i32, U10, true>;
pub type U11Var32 = IntVar<i32, U11, false>;
pub type I11Var32 = IntVar<i32, U11, true>;
pub type U12Var32 = IntVar<i32, U12, false>;
pub type I12Var32 = IntVar<i32, U12, true>;
pub type U13Var32 = IntVar<i32, U13, false>;
pub type I13Var32 = IntVar<i32, U13, true>;
pub type U14Var32 = IntVar<i32, U14, false>;
pub type I14Var32 = IntVar<i32, U14, true>;
pub type U15Var32 = IntVar<i32, U15, false>;
pub type I15Var32 = IntVar<i32, U15, true>;
pub type U16Var32 = IntVar<i32, U16, false>;
pub type I16Var32 = IntVar<i32, U16, true>;
pub type U17Var32 = IntVar<i32, U17, false>;
pub type I17Var32 = IntVar<i32, U17, true>;
pub type U18Var32 = IntVar<i32, U18, false>;
pub type I18Var32 = IntVar<i32, U18, true>;
pub type U19Var32 = IntVar<i32, U19, false>;
pub type I19Var32 = IntVar<i32, U19, true>;
pub type U20Var32 = IntVar<i32, U20, false>;
pub type I20Var32 = IntVar<i32, U20, true>;
pub type U21Var32 = IntVar<i32, U21, false>;
pub type I21Var32 = IntVar<i32, U21, true>;
pub type U22Var32 = IntVar<i32, U22, false>;
pub type I22Var32 = IntVar<i32, U22, true>;
pub type U23Var32 = IntVar<i32, U23, false>;
pub type I23Var32 = IntVar<i32, U23, true>;
pub type U24Var32 = IntVar<i32, U24, false>;
pub type I24Var32 = IntVar<i32, U24, true>;
pub type U25Var32 = IntVar<i32, U25, false>;
pub type I25Var32 = IntVar<i32, U25, true>;
pub type U26Var32 = IntVar<i32, U26, false>;
pub type I26Var32 = IntVar<i32, U26, true>;
pub type U27Var32 = IntVar<i32, U27, false>;
pub type I27Var32 = IntVar<i32, U27, true>;
pub type U28Var32 = IntVar<i32, U28, false>;
pub type I28Var32 = IntVar<i32, U28, true>;
pub type U29Var32 = IntVar<i32, U29, false>;
pub type I29Var32 = IntVar<i32, U29, true>;
pub type U30Var32 = IntVar<i32, U30, false>;
pub type I30Var32 = IntVar<i32, U30, true>;
pub type U31Var32 = IntVar<i32, U31, false>;
pub type I31Var32 = IntVar<i32, U31, true>;
pub type U32Var32 = IntVar<i32, U32, false>;
pub type I32Var32 = IntVar<i32, U32, true>;
pub type U33Var32 = IntVar<i32, U33, false>;
pub type I33Var32 = IntVar<i32, U33, true>;
pub type U34Var32 = IntVar<i32, U34, false>;
pub type I34Var32 = IntVar<i32, U34, true>;
pub type U35Var32 = IntVar<i32, U35, false>;
pub type I35Var32 = IntVar<i32, U35, true>;
pub type U36Var32 = IntVar<i32, U36, false>;
pub type I36Var32 = IntVar<i32, U36, true>;
pub type U37Var32 = IntVar<i32, U37, false>;
pub type I37Var32 = IntVar<i32, U37, true>;
pub type U38Var32 = IntVar<i32, U38, false>;
pub type I38Var32 = IntVar<i32, U38, true>;
pub type U39Var32 = IntVar<i32, U39, false>;
pub type I39Var32 = IntVar<i32, U39, true>;
pub type U40Var32 = IntVar<i32, U40, false>;
pub type I40Var32 = IntVar<i32, U40, true>;
pub type U41Var32 = IntVar<i32, U41, false>;
pub type I41Var32 = IntVar<i32, U41, true>;
pub type U42Var32 = IntVar<i32, U42, false>;
pub type I42Var32 = IntVar<i32, U42, true>;
pub type U43Var32 = IntVar<i32, U43, false>;
pub type I43Var32 = IntVar<i32, U43, true>;
pub type U44Var32 = IntVar<i32, U44, false>;
pub type I44Var32 = IntVar<i32, U44, true>;
pub type U45Var32 = IntVar<i32, U45, false>;
pub type I45Var32 = IntVar<i32, U45, true>;
pub type U46Var32 = IntVar<i32, U46, false>;
pub type I46Var32 = IntVar<i32, U46, true>;
pub type U47Var32 = IntVar<i32, U47, false>;
pub type I47Var32 = IntVar<i32, U47, true>;
pub type U48Var32 = IntVar<i32, U48, false>;
pub type I48Var32 = IntVar<i32, U48, true>;
pub type U49Var32 = IntVar<i32, U49, false>;
pub type I49Var32 = IntVar<i32, U49, true>;
pub type U50Var32 = IntVar<i32, U50, false>;
pub type I50Var32 = IntVar<i32, U50, true>;
pub type U51Var32 = IntVar<i32, U51, false>;
pub type I51Var32 = IntVar<i32, U51, true>;
pub type U52Var32 = IntVar<i32, U52, false>;
pub type I52Var32 = IntVar<i32, U52, true>;
pub type U53Var32 = IntVar<i32, U53, false>;
pub type I53Var32 = IntVar<i32, U53, true>;
pub type U54Var32 = IntVar<i32, U54, false>;
pub type I54Var32 = IntVar<i32, U54, true>;
pub type U55Var32 = IntVar<i32, U55, false>;
pub type I55Var32 = IntVar<i32, U55, true>;
pub type U56Var32 = IntVar<i32, U56, false>;
pub type I56Var32 = IntVar<i32, U56, true>;
pub type U57Var32 = IntVar<i32, U57, false>;
pub type I57Var32 = IntVar<i32, U57, true>;
pub type U58Var32 = IntVar<i32, U58, false>;
pub type I58Var32 = IntVar<i32, U58, true>;
pub type U59Var32 = IntVar<i32, U59, false>;
pub type I59Var32 = IntVar<i32, U59, true>;
pub type U60Var32 = IntVar<i32, U60, false>;
pub type I60Var32 = IntVar<i32, U60, true>;
pub type U61Var32 = IntVar<i32, U61, false>;
pub type I61Var32 = IntVar<i32, U61, true>;
pub type U62Var32 = IntVar<i32, U62, false>;
pub type I62Var32 = IntVar<i32, U62, true>;
pub type U63Var32 = IntVar<i32, U63, false>;
pub type I63Var32 = IntVar<i32, U63, true>;
pub type U64Var32 = IntVar<i32, U64, false>;
pub type I64Var32 = IntVar<i32, U64, true>;
pub type U65Var32 = IntVar<i32, U65, false>;
pub type I65Var32 = IntVar<i32, U65, true>;
pub type U66Var32 = IntVar<i32, U66, false>;
pub type I66Var32 = IntVar<i32, U66, true>;
pub type U67Var32 = IntVar<i32, U67, false>;
pub type I67Var32 = IntVar<i32, U67, true>;
pub type U68Var32 = IntVar<i32, U68, false>;
pub type I68Var32 = IntVar<i32, U68, true>;
pub type U69Var32 = IntVar<i32, U69, false>;
pub type I69Var32 = IntVar<i32, U69, true>;
pub type U70Var32 = IntVar<i32, U70, false>;
pub type I70Var32 = IntVar<i32, U70, true>;
pub type U71Var32 = IntVar<i32, U71, false>;
pub type I71Var32 = IntVar<i32, U71, true>;
pub type U72Var32 = IntVar<i32, U72, false>;
pub type I72Var32 = IntVar<i32, U72, true>;
pub type U73Var32 = IntVar<i32, U73, false>;
pub type I73Var32 = IntVar<i32, U73, true>;
pub type U74Var32 = IntVar<i32, U74, false>;
pub type I74Var32 = IntVar<i32, U74, true>;
pub type U75Var32 = IntVar<i32, U75, false>;
pub type I75Var32 = IntVar<i32, U75, true>;
pub type U76Var32 = IntVar<i32, U76, false>;
pub type I76Var32 = IntVar<i32, U76, true>;
pub type U77Var32 = IntVar<i32, U77, false>;
pub type I77Var32 = IntVar<i32, U77, true>;
pub type U78Var32 = IntVar<i32, U78, false>;
pub type I78Var32 = IntVar<i32, U78, true>;
pub type U79Var32 = IntVar<i32, U79, false>;
pub type I79Var32 = IntVar<i32, U79, true>;
pub type U80Var32 = IntVar<i32, U80, false>;
pub type I80Var32 = IntVar<i32, U80, true>;
pub type U81Var32 = IntVar<i32, U81, false>;
pub type I81Var32 = IntVar<i32, U81, true>;
pub type U82Var32 = IntVar<i32, U82, false>;
pub type I82Var32 = IntVar<i32, U82, true>;
pub type U83Var32 = IntVar<i32, U83, false>;
pub type I83Var32 = IntVar<i32, U83, true>;
pub type U84Var32 = IntVar<i32, U84, false>;
pub type I84Var32 = IntVar<i32, U84, true>;
pub type U85Var32 = IntVar<i32, U85, false>;
pub type I85Var32 = IntVar<i32, U85, true>;
pub type U86Var32 = IntVar<i32, U86, false>;
pub type I86Var32 = IntVar<i32, U86, true>;
pub type U87Var32 = IntVar<i32, U87, false>;
pub type I87Var32 = IntVar<i32, U87, true>;
pub type U88Var32 = IntVar<i32, U88, false>;
pub type I88Var32 = IntVar<i32, U88, true>;
pub type U89Var32 = IntVar<i32, U89, false>;
pub type I89Var32 = IntVar<i32, U89, true>;
pub type U90Var32 = IntVar<i32, U90, false>;
pub type I90Var32 = IntVar<i32, U90, true>;
pub type U91Var32 = IntVar<i32, U91, false>;
pub type I91Var32 = IntVar<i32, U91, true>;
pub type U92Var32 = IntVar<i32, U92, false>;
pub type I92Var32 = IntVar<i32, U92, true>;
pub type U93Var32 = IntVar<i32, U93, false>;
pub type I93Var32 = IntVar<i32, U93, true>;
pub type U94Var32 = IntVar<i32, U94, false>;
pub type I94Var32 = IntVar<i32, U94, true>;
pub type U95Var32 = IntVar<i32, U95, false>;
pub type I95Var32 = IntVar<i32, U95, true>;
pub type U96Var32 = IntVar<i32, U96, false>;
pub type I96Var32 = IntVar<i32, U96, true>;
pub type U97Var32 = IntVar<i32, U97, false>;
pub type I97Var32 = IntVar<i32, U97, true>;
pub type U98Var32 = IntVar<i32, U98, false>;
pub type I98Var32 = IntVar<i32, U98, true>;
pub type U99Var32 = IntVar<i32, U99, false>;
pub type I99Var32 = IntVar<i32, U99, true>;
pub type U100Var32 = IntVar<i32, U100, false>;
pub type I100Var32 = IntVar<i32, U100, true>;
pub type U101Var32 = IntVar<i32, U101, false>;
pub type I101Var32 = IntVar<i32, U101, true>;
pub type U102Var32 = IntVar<i32, U102, false>;
pub type I102Var32 = IntVar<i32, U102, true>;
pub type U103Var32 = IntVar<i32, U103, false>;
pub type I103Var32 = IntVar<i32, U103, true>;
pub type U104Var32 = IntVar<i32, U104, false>;
pub type I104Var32 = IntVar<i32, U104, true>;
pub type U105Var32 = IntVar<i32, U105, false>;
pub type I105Var32 = IntVar<i32, U105, true>;
pub type U106Var32 = IntVar<i32, U106, false>;
pub type I106Var32 = IntVar<i32, U106, true>;
pub type U107Var32 = IntVar<i32, U107, false>;
pub type I107Var32 = IntVar<i32, U107, true>;
pub type U108Var32 = IntVar<i32, U108, false>;
pub type I108Var32 = IntVar<i32, U108, true>;
pub type U109Var32 = IntVar<i32, U109, false>;
pub type I109Var32 = IntVar<i32, U109, true>;
pub type U110Var32 = IntVar<i32, U110, false>;
pub type I110Var32 = IntVar<i32, U110, true>;
pub type U111Var32 = IntVar<i32, U111, false>;
pub type I111Var32 = IntVar<i32, U111, true>;
pub type U112Var32 = IntVar<i32, U112, false>;
pub type I112Var32 = IntVar<i32, U112, true>;
pub type U113Var32 = IntVar<i32, U113, false>;
pub type I113Var32 = IntVar<i32, U113, true>;
pub type U114Var32 = IntVar<i32, U114, false>;
pub type I114Var32 = IntVar<i32, U114, true>;
pub type U115Var32 = IntVar<i32, U115, false>;
pub type I115Var32 = IntVar<i32, U115, true>;
pub type U116Var32 = IntVar<i32, U116, false>;
pub type I116Var32 = IntVar<i32, U116, true>;
pub type U117Var32 = IntVar<i32, U117, false>;
pub type I117Var32 = IntVar<i32, U117, true>;
pub type U118Var32 = IntVar<i32, U118, false>;
pub type I118Var32 = IntVar<i32, U118, true>;
pub type U119Var32 = IntVar<i32, U119, false>;
pub type I119Var32 = IntVar<i32, U119, true>;
pub type U120Var32 = IntVar<i32, U120, false>;
pub type I120Var32 = IntVar<i32, U120, true>;
pub type U121Var32 = IntVar<i32, U121, false>;
pub type I121Var32 = IntVar<i32, U121, true>;
pub type U122Var32 = IntVar<i32, U122, false>;
pub type I122Var32 = IntVar<i32, U122, true>;
pub type U123Var32 = IntVar<i32, U123, false>;
pub type I123Var32 = IntVar<i32, U123, true>;
pub type U124Var32 = IntVar<i32, U124, false>;
pub type I124Var32 = IntVar<i32, U124, true>;
pub type U125Var32 = IntVar<i32, U125, false>;
pub type I125Var32 = IntVar<i32, U125, true>;
pub type U126Var32 = IntVar<i32, U126, false>;
pub type I126Var32 = IntVar<i32, U126, true>;
pub type U127Var32 = IntVar<i32, U127, false>;
pub type I127Var32 = IntVar<i32, U127, true>;
pub type U128Var32 = IntVar<i32, U128, false>;
pub type I128Var32 = IntVar<i32, U128, true>;

pub type IntVarSys<N, const SIGN: bool> = IntVar<isize, N, SIGN>;

pub type UVarSys<N> = IntVar<isize, N, false>;
pub type IVarSys<N> = IntVar<isize, N, true>;

pub type U1VarSys = IntVar<isize, U1, false>;
pub type I1VarSys = IntVar<isize, U1, true>;
pub type U2VarSys = IntVar<isize, U2, false>;
pub type I2VarSys = IntVar<isize, U2, true>;
pub type U3VarSys = IntVar<isize, U3, false>;
pub type I3VarSys = IntVar<isize, U3, true>;
pub type U4VarSys = IntVar<isize, U4, false>;
pub type I4VarSys = IntVar<isize, U4, true>;
pub type U5VarSys = IntVar<isize, U5, false>;
pub type I5VarSys = IntVar<isize, U5, true>;
pub type U6VarSys = IntVar<isize, U6, false>;
pub type I6VarSys = IntVar<isize, U6, true>;
pub type U7VarSys = IntVar<isize, U7, false>;
pub type I7VarSys = IntVar<isize, U7, true>;
pub type U8VarSys = IntVar<isize, U8, false>;
pub type I8VarSys = IntVar<isize, U8, true>;
pub type U9VarSys = IntVar<isize, U9, false>;
pub type I9VarSys = IntVar<isize, U9, true>;
pub type U10VarSys = IntVar<isize, U10, false>;
pub type I10VarSys = IntVar<isize, U10, true>;
pub type U11VarSys = IntVar<isize, U11, false>;
pub type I11VarSys = IntVar<isize, U11, true>;
pub type U12VarSys = IntVar<isize, U12, false>;
pub type I12VarSys = IntVar<isize, U12, true>;
pub type U13VarSys = IntVar<isize, U13, false>;
pub type I13VarSys = IntVar<isize, U13, true>;
pub type U14VarSys = IntVar<isize, U14, false>;
pub type I14VarSys = IntVar<isize, U14, true>;
pub type U15VarSys = IntVar<isize, U15, false>;
pub type I15VarSys = IntVar<isize, U15, true>;
pub type U16VarSys = IntVar<isize, U16, false>;
pub type I16VarSys = IntVar<isize, U16, true>;
pub type U17VarSys = IntVar<isize, U17, false>;
pub type I17VarSys = IntVar<isize, U17, true>;
pub type U18VarSys = IntVar<isize, U18, false>;
pub type I18VarSys = IntVar<isize, U18, true>;
pub type U19VarSys = IntVar<isize, U19, false>;
pub type I19VarSys = IntVar<isize, U19, true>;
pub type U20VarSys = IntVar<isize, U20, false>;
pub type I20VarSys = IntVar<isize, U20, true>;
pub type U21VarSys = IntVar<isize, U21, false>;
pub type I21VarSys = IntVar<isize, U21, true>;
pub type U22VarSys = IntVar<isize, U22, false>;
pub type I22VarSys = IntVar<isize, U22, true>;
pub type U23VarSys = IntVar<isize, U23, false>;
pub type I23VarSys = IntVar<isize, U23, true>;
pub type U24VarSys = IntVar<isize, U24, false>;
pub type I24VarSys = IntVar<isize, U24, true>;
pub type U25VarSys = IntVar<isize, U25, false>;
pub type I25VarSys = IntVar<isize, U25, true>;
pub type U26VarSys = IntVar<isize, U26, false>;
pub type I26VarSys = IntVar<isize, U26, true>;
pub type U27VarSys = IntVar<isize, U27, false>;
pub type I27VarSys = IntVar<isize, U27, true>;
pub type U28VarSys = IntVar<isize, U28, false>;
pub type I28VarSys = IntVar<isize, U28, true>;
pub type U29VarSys = IntVar<isize, U29, false>;
pub type I29VarSys = IntVar<isize, U29, true>;
pub type U30VarSys = IntVar<isize, U30, false>;
pub type I30VarSys = IntVar<isize, U30, true>;
pub type U31VarSys = IntVar<isize, U31, false>;
pub type I31VarSys = IntVar<isize, U31, true>;
pub type U32VarSys = IntVar<isize, U32, false>;
pub type I32VarSys = IntVar<isize, U32, true>;
pub type U33VarSys = IntVar<isize, U33, false>;
pub type I33VarSys = IntVar<isize, U33, true>;
pub type U34VarSys = IntVar<isize, U34, false>;
pub type I34VarSys = IntVar<isize, U34, true>;
pub type U35VarSys = IntVar<isize, U35, false>;
pub type I35VarSys = IntVar<isize, U35, true>;
pub type U36VarSys = IntVar<isize, U36, false>;
pub type I36VarSys = IntVar<isize, U36, true>;
pub type U37VarSys = IntVar<isize, U37, false>;
pub type I37VarSys = IntVar<isize, U37, true>;
pub type U38VarSys = IntVar<isize, U38, false>;
pub type I38VarSys = IntVar<isize, U38, true>;
pub type U39VarSys = IntVar<isize, U39, false>;
pub type I39VarSys = IntVar<isize, U39, true>;
pub type U40VarSys = IntVar<isize, U40, false>;
pub type I40VarSys = IntVar<isize, U40, true>;
pub type U41VarSys = IntVar<isize, U41, false>;
pub type I41VarSys = IntVar<isize, U41, true>;
pub type U42VarSys = IntVar<isize, U42, false>;
pub type I42VarSys = IntVar<isize, U42, true>;
pub type U43VarSys = IntVar<isize, U43, false>;
pub type I43VarSys = IntVar<isize, U43, true>;
pub type U44VarSys = IntVar<isize, U44, false>;
pub type I44VarSys = IntVar<isize, U44, true>;
pub type U45VarSys = IntVar<isize, U45, false>;
pub type I45VarSys = IntVar<isize, U45, true>;
pub type U46VarSys = IntVar<isize, U46, false>;
pub type I46VarSys = IntVar<isize, U46, true>;
pub type U47VarSys = IntVar<isize, U47, false>;
pub type I47VarSys = IntVar<isize, U47, true>;
pub type U48VarSys = IntVar<isize, U48, false>;
pub type I48VarSys = IntVar<isize, U48, true>;
pub type U49VarSys = IntVar<isize, U49, false>;
pub type I49VarSys = IntVar<isize, U49, true>;
pub type U50VarSys = IntVar<isize, U50, false>;
pub type I50VarSys = IntVar<isize, U50, true>;
pub type U51VarSys = IntVar<isize, U51, false>;
pub type I51VarSys = IntVar<isize, U51, true>;
pub type U52VarSys = IntVar<isize, U52, false>;
pub type I52VarSys = IntVar<isize, U52, true>;
pub type U53VarSys = IntVar<isize, U53, false>;
pub type I53VarSys = IntVar<isize, U53, true>;
pub type U54VarSys = IntVar<isize, U54, false>;
pub type I54VarSys = IntVar<isize, U54, true>;
pub type U55VarSys = IntVar<isize, U55, false>;
pub type I55VarSys = IntVar<isize, U55, true>;
pub type U56VarSys = IntVar<isize, U56, false>;
pub type I56VarSys = IntVar<isize, U56, true>;
pub type U57VarSys = IntVar<isize, U57, false>;
pub type I57VarSys = IntVar<isize, U57, true>;
pub type U58VarSys = IntVar<isize, U58, false>;
pub type I58VarSys = IntVar<isize, U58, true>;
pub type U59VarSys = IntVar<isize, U59, false>;
pub type I59VarSys = IntVar<isize, U59, true>;
pub type U60VarSys = IntVar<isize, U60, false>;
pub type I60VarSys = IntVar<isize, U60, true>;
pub type U61VarSys = IntVar<isize, U61, false>;
pub type I61VarSys = IntVar<isize, U61, true>;
pub type U62VarSys = IntVar<isize, U62, false>;
pub type I62VarSys = IntVar<isize, U62, true>;
pub type U63VarSys = IntVar<isize, U63, false>;
pub type I63VarSys = IntVar<isize, U63, true>;
pub type U64VarSys = IntVar<isize, U64, false>;
pub type I64VarSys = IntVar<isize, U64, true>;
pub type U65VarSys = IntVar<isize, U65, false>;
pub type I65VarSys = IntVar<isize, U65, true>;
pub type U66VarSys = IntVar<isize, U66, false>;
pub type I66VarSys = IntVar<isize, U66, true>;
pub type U67VarSys = IntVar<isize, U67, false>;
pub type I67VarSys = IntVar<isize, U67, true>;
pub type U68VarSys = IntVar<isize, U68, false>;
pub type I68VarSys = IntVar<isize, U68, true>;
pub type U69VarSys = IntVar<isize, U69, false>;
pub type I69VarSys = IntVar<isize, U69, true>;
pub type U70VarSys = IntVar<isize, U70, false>;
pub type I70VarSys = IntVar<isize, U70, true>;
pub type U71VarSys = IntVar<isize, U71, false>;
pub type I71VarSys = IntVar<isize, U71, true>;
pub type U72VarSys = IntVar<isize, U72, false>;
pub type I72VarSys = IntVar<isize, U72, true>;
pub type U73VarSys = IntVar<isize, U73, false>;
pub type I73VarSys = IntVar<isize, U73, true>;
pub type U74VarSys = IntVar<isize, U74, false>;
pub type I74VarSys = IntVar<isize, U74, true>;
pub type U75VarSys = IntVar<isize, U75, false>;
pub type I75VarSys = IntVar<isize, U75, true>;
pub type U76VarSys = IntVar<isize, U76, false>;
pub type I76VarSys = IntVar<isize, U76, true>;
pub type U77VarSys = IntVar<isize, U77, false>;
pub type I77VarSys = IntVar<isize, U77, true>;
pub type U78VarSys = IntVar<isize, U78, false>;
pub type I78VarSys = IntVar<isize, U78, true>;
pub type U79VarSys = IntVar<isize, U79, false>;
pub type I79VarSys = IntVar<isize, U79, true>;
pub type U80VarSys = IntVar<isize, U80, false>;
pub type I80VarSys = IntVar<isize, U80, true>;
pub type U81VarSys = IntVar<isize, U81, false>;
pub type I81VarSys = IntVar<isize, U81, true>;
pub type U82VarSys = IntVar<isize, U82, false>;
pub type I82VarSys = IntVar<isize, U82, true>;
pub type U83VarSys = IntVar<isize, U83, false>;
pub type I83VarSys = IntVar<isize, U83, true>;
pub type U84VarSys = IntVar<isize, U84, false>;
pub type I84VarSys = IntVar<isize, U84, true>;
pub type U85VarSys = IntVar<isize, U85, false>;
pub type I85VarSys = IntVar<isize, U85, true>;
pub type U86VarSys = IntVar<isize, U86, false>;
pub type I86VarSys = IntVar<isize, U86, true>;
pub type U87VarSys = IntVar<isize, U87, false>;
pub type I87VarSys = IntVar<isize, U87, true>;
pub type U88VarSys = IntVar<isize, U88, false>;
pub type I88VarSys = IntVar<isize, U88, true>;
pub type U89VarSys = IntVar<isize, U89, false>;
pub type I89VarSys = IntVar<isize, U89, true>;
pub type U90VarSys = IntVar<isize, U90, false>;
pub type I90VarSys = IntVar<isize, U90, true>;
pub type U91VarSys = IntVar<isize, U91, false>;
pub type I91VarSys = IntVar<isize, U91, true>;
pub type U92VarSys = IntVar<isize, U92, false>;
pub type I92VarSys = IntVar<isize, U92, true>;
pub type U93VarSys = IntVar<isize, U93, false>;
pub type I93VarSys = IntVar<isize, U93, true>;
pub type U94VarSys = IntVar<isize, U94, false>;
pub type I94VarSys = IntVar<isize, U94, true>;
pub type U95VarSys = IntVar<isize, U95, false>;
pub type I95VarSys = IntVar<isize, U95, true>;
pub type U96VarSys = IntVar<isize, U96, false>;
pub type I96VarSys = IntVar<isize, U96, true>;
pub type U97VarSys = IntVar<isize, U97, false>;
pub type I97VarSys = IntVar<isize, U97, true>;
pub type U98VarSys = IntVar<isize, U98, false>;
pub type I98VarSys = IntVar<isize, U98, true>;
pub type U99VarSys = IntVar<isize, U99, false>;
pub type I99VarSys = IntVar<isize, U99, true>;
pub type U100VarSys = IntVar<isize, U100, false>;
pub type I100VarSys = IntVar<isize, U100, true>;
pub type U101VarSys = IntVar<isize, U101, false>;
pub type I101VarSys = IntVar<isize, U101, true>;
pub type U102VarSys = IntVar<isize, U102, false>;
pub type I102VarSys = IntVar<isize, U102, true>;
pub type U103VarSys = IntVar<isize, U103, false>;
pub type I103VarSys = IntVar<isize, U103, true>;
pub type U104VarSys = IntVar<isize, U104, false>;
pub type I104VarSys = IntVar<isize, U104, true>;
pub type U105VarSys = IntVar<isize, U105, false>;
pub type I105VarSys = IntVar<isize, U105, true>;
pub type U106VarSys = IntVar<isize, U106, false>;
pub type I106VarSys = IntVar<isize, U106, true>;
pub type U107VarSys = IntVar<isize, U107, false>;
pub type I107VarSys = IntVar<isize, U107, true>;
pub type U108VarSys = IntVar<isize, U108, false>;
pub type I108VarSys = IntVar<isize, U108, true>;
pub type U109VarSys = IntVar<isize, U109, false>;
pub type I109VarSys = IntVar<isize, U109, true>;
pub type U110VarSys = IntVar<isize, U110, false>;
pub type I110VarSys = IntVar<isize, U110, true>;
pub type U111VarSys = IntVar<isize, U111, false>;
pub type I111VarSys = IntVar<isize, U111, true>;
pub type U112VarSys = IntVar<isize, U112, false>;
pub type I112VarSys = IntVar<isize, U112, true>;
pub type U113VarSys = IntVar<isize, U113, false>;
pub type I113VarSys = IntVar<isize, U113, true>;
pub type U114VarSys = IntVar<isize, U114, false>;
pub type I114VarSys = IntVar<isize, U114, true>;
pub type U115VarSys = IntVar<isize, U115, false>;
pub type I115VarSys = IntVar<isize, U115, true>;
pub type U116VarSys = IntVar<isize, U116, false>;
pub type I116VarSys = IntVar<isize, U116, true>;
pub type U117VarSys = IntVar<isize, U117, false>;
pub type I117VarSys = IntVar<isize, U117, true>;
pub type U118VarSys = IntVar<isize, U118, false>;
pub type I118VarSys = IntVar<isize, U118, true>;
pub type U119VarSys = IntVar<isize, U119, false>;
pub type I119VarSys = IntVar<isize, U119, true>;
pub type U120VarSys = IntVar<isize, U120, false>;
pub type I120VarSys = IntVar<isize, U120, true>;
pub type U121VarSys = IntVar<isize, U121, false>;
pub type I121VarSys = IntVar<isize, U121, true>;
pub type U122VarSys = IntVar<isize, U122, false>;
pub type I122VarSys = IntVar<isize, U122, true>;
pub type U123VarSys = IntVar<isize, U123, false>;
pub type I123VarSys = IntVar<isize, U123, true>;
pub type U124VarSys = IntVar<isize, U124, false>;
pub type I124VarSys = IntVar<isize, U124, true>;
pub type U125VarSys = IntVar<isize, U125, false>;
pub type I125VarSys = IntVar<isize, U125, true>;
pub type U126VarSys = IntVar<isize, U126, false>;
pub type I126VarSys = IntVar<isize, U126, true>;
pub type U127VarSys = IntVar<isize, U127, false>;
pub type I127VarSys = IntVar<isize, U127, true>;
pub type U128VarSys = IntVar<isize, U128, false>;
pub type I128VarSys = IntVar<isize, U128, true>;
