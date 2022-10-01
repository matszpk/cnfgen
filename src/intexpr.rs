// intexpr.rs - integer expression structures.
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
//! The module to generate CNF clauses from boolean expressions.

use std::cell::RefCell;
use std::cmp;
use std::fmt::Debug;
use std::iter;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Mul, MulAssign,
    Neg, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use std::rc::Rc;

use generic_array::typenum::*;
use generic_array::*;

use crate::boolexpr::{
    bool_ite, full_adder, half_adder, BoolEqual, BoolImpl, ExprNode as BoolExprNode,
};
use crate::boolexpr_creator::ExprCreator;
use crate::VarLit;
use crate::{impl_int_ipty_ty1, impl_int_ty1_lt_ty2, impl_int_upty_ty1};

#[derive(thiserror::Error, Debug)]
pub enum IntError {
    #[error("Bit overflow")]
    BitOverflow,
}

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

int_equal_impl!(u8);
int_equal_impl!(i8);
int_equal_impl!(u16);
int_equal_impl!(i16);
int_equal_impl!(u32);
int_equal_impl!(i32);
int_equal_impl!(u64);
int_equal_impl!(i64);
int_equal_impl!(usize);
int_equal_impl!(isize);
int_equal_impl!(u128);
int_equal_impl!(i128);

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

int_ord_impl!(u8);
int_ord_impl!(i8);
int_ord_impl!(u16);
int_ord_impl!(i16);
int_ord_impl!(u32);
int_ord_impl!(i32);
int_ord_impl!(u64);
int_ord_impl!(i64);
int_ord_impl!(usize);
int_ord_impl!(isize);
int_ord_impl!(u128);
int_ord_impl!(i128);

pub trait IntConstant<T: VarLit, U> {
    fn constant(creator: Rc<RefCell<ExprCreator<T>>>, v: U) -> Self;
}

pub trait BitVal {
    type Output;

    fn bit(self, n: usize) -> Self::Output;
}

macro_rules! impl_int_bitval_upty {
    ($pty:ty) => {
        impl BitVal for $pty {
            type Output = bool;

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

impl_int_bitval_upty!(u8);
impl_int_bitval_upty!(u16);
impl_int_bitval_upty!(u32);
impl_int_bitval_upty!(usize);
impl_int_bitval_upty!(u64);
impl_int_bitval_upty!(u128);

macro_rules! impl_int_bitval_ipty {
    ($pty:ty) => {
        impl BitVal for $pty {
            type Output = bool;

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

impl_int_bitval_ipty!(i8);
impl_int_bitval_ipty!(i16);
impl_int_bitval_ipty!(i32);
impl_int_bitval_ipty!(isize);
impl_int_bitval_ipty!(i64);
impl_int_bitval_ipty!(i128);

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

impl_int_bitmask_pty!(u8);
impl_int_bitmask_pty!(u16);
impl_int_bitmask_pty!(u32);
impl_int_bitmask_pty!(u64);
impl_int_bitmask_pty!(usize);
impl_int_bitmask_pty!(u128);
impl_int_bitmask_pty!(i8);
impl_int_bitmask_pty!(i16);
impl_int_bitmask_pty!(i32);
impl_int_bitmask_pty!(i64);
impl_int_bitmask_pty!(isize);
impl_int_bitmask_pty!(i128);

// ExprNode - main node
//
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprNode<T: VarLit + Debug, N: ArrayLength<usize>, const SIGN: bool> {
    creator: Rc<RefCell<ExprCreator<T>>>,
    pub(super) indexes: GenericArray<usize, N>,
}

impl<T, N: ArrayLength<usize>, const SIGN: bool> ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub const BITS: usize = N::USIZE;
    pub const SIGN: bool = SIGN;
    // Creates new variable as expression node.
    pub fn variable(creator: Rc<RefCell<ExprCreator<T>>>) -> Self {
        let mut indexes = GenericArray::<usize, N>::default();
        {
            let mut creator = creator.borrow_mut();
            indexes.iter_mut().for_each(|x| {
                let l = creator.new_variable();
                *x = creator.single(l);
            });
        }
        ExprNode { creator, indexes }
    }

    pub fn as_unsigned(self) -> ExprNode<T, N, false> {
        ExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }

    pub fn as_signed(self) -> ExprNode<T, N, true> {
        ExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }
    
    pub fn addc_with_carry(self, rhs: Self, in_carry :BoolExprNode<T>) -> (Self, BoolExprNode<T>) {
        let mut output = GenericArray::<usize, N>::default();
        let mut c = in_carry;
        for i in 0..N::USIZE {
            (output[i], c) = {
                let (s0, c0) = full_adder(self.bit(i), rhs.bit(i), c);
                (s0.index, c0)
            };
        }
        (ExprNode {
            creator: self.creator,
            indexes: output,
        }, c)
    }
    
    pub fn addc(self, rhs: Self, in_carry :BoolExprNode<T>) -> Self {
        let mut output = GenericArray::<usize, N>::default();
        let mut c = in_carry;
        for i in 0..N::USIZE - 1 {
            (output[i], c) = {
                let (s0, c0) = full_adder(self.bit(i), rhs.bit(i), c);
                (s0.index, c0)
            };
        }
        output[N::USIZE - 1] = (self.bit(N::USIZE - 1) ^ !rhs.bit(N::USIZE - 1) ^ c).index;
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl<T, N: ArrayLength<usize>> ExprNode<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn subvalue<N2>(&self, start: usize) -> ExprNode<T, N2, false>
    where
        N2: ArrayLength<usize>,
    {
        ExprNode {
            creator: self.creator.clone(),
            indexes: GenericArray::clone_from_slice(&self.indexes[start..start + N2::USIZE]),
        }
    }

    pub fn select_bits<N2, I>(&self, iter: I) -> Option<ExprNode<T, N2, false>>
    where
        N2: ArrayLength<usize>,
        I: IntoIterator<Item = usize>,
    {
        GenericArray::from_exact_iter(iter.into_iter().map(|x| self.indexes[x])).map(|indexes| {
            ExprNode {
                creator: self.creator.clone(),
                indexes,
            }
        })
    }

    pub fn concat<N2>(self, rest: ExprNode<T, N2, false>) -> ExprNode<T, Sum<N, N2>, false>
    where
        N: Add<N2>,
        N2: ArrayLength<usize>,
        Sum<N, N2>: ArrayLength<usize>,
    {
        use generic_array::sequence::*;
        assert_eq!(self.creator, rest.creator);
        ExprNode {
            creator: self.creator,
            indexes: self.indexes.concat(rest.indexes),
        }
    }

    pub fn split<K>(
        self,
    ) -> (
        ExprNode<T, K, false>,
        ExprNode<T, operator_aliases::Diff<N, K>, false>,
    )
    where
        N: Sub<K>,
        K: ArrayLength<usize>,
        operator_aliases::Diff<N, K>: ArrayLength<usize>,
    {
        use generic_array::sequence::*;
        let (indexes1, indexes2) = self.indexes.split();
        (
            ExprNode {
                creator: self.creator.clone(),
                indexes: indexes1,
            },
            ExprNode {
                creator: self.creator,
                indexes: indexes2,
            },
        )
    }
}

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

// TryFrom implementation
macro_rules! impl_int_try_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                TryFrom<ExprNode<T, $ty2, SIGN2>> for ExprNode<T, $ty1, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: ExprNode<T, $ty2, SIGN2>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                // if all rest of bits are 0 - just false
                if !v.indexes.iter().skip(len1).all(|x| *x==0) {
                    return Err(IntError::BitOverflow);
                }
                Ok(ExprNode::<T, $ty1, false>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<ExprNode<T, $ty2, false>> for ExprNode<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: ExprNode<T, $ty2, false>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                // if all rest of bits are 0 - just false
                if !v.indexes.iter().skip(len1-1).all(|x| *x==0) {
                    return Err(IntError::BitOverflow);
                }
                Ok(ExprNode::<T, $ty1, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<ExprNode<T, $ty2, true>> for ExprNode<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: ExprNode<T, $ty2, true>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                let last_idx = v.indexes[len1-1];
                if !v.indexes.iter().skip(len1).all(|x| last_idx==*x) {
                    return Err(IntError::BitOverflow);
                }
                Ok(ExprNode::<T, $ty1, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        // try from for rest
        impl<T: VarLit, $( $gparams ),* >
                TryFrom<ExprNode<T, $ty1, true>> for ExprNode<T, $ty2, false>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            type Error = IntError;

            fn try_from(v: ExprNode<T, $ty1, true>) -> Result<Self, Self::Error> {
                if *v.indexes.last().unwrap() != 0 {
                    return Err(IntError::BitOverflow); // if minus
                }
                // default is zero - then is false - zero bit value
                let mut new_v = ExprNode::<T, $ty2, false>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                new_v.indexes[0..v.indexes.len()].copy_from_slice(v.indexes.as_slice());
                Ok(new_v)
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_try_from);

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<ExprNode<T, N, false>> for ExprNode<T, N, true> {
    type Error = IntError;

    fn try_from(v: ExprNode<T, N, false>) -> Result<Self, Self::Error> {
        if *v.indexes.last().unwrap() != 0 {
            // if input if higher than possible output
            return Err(IntError::BitOverflow);
        }
        Ok(ExprNode {
            creator: v.creator,
            indexes: v.indexes,
        })
    }
}

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<ExprNode<T, N, true>> for ExprNode<T, N, false> {
    type Error = IntError;

    fn try_from(v: ExprNode<T, N, true>) -> Result<Self, Self::Error> {
        if *v.indexes.last().unwrap() != 0 {
            // if input is lower than 0
            return Err(IntError::BitOverflow);
        }
        Ok(ExprNode {
            creator: v.creator,
            indexes: v.indexes,
        })
    }
}

// From implementation
macro_rules! impl_int_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                From<ExprNode<T, $ty1, false>> for ExprNode<T, $ty2, SIGN2>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: ExprNode<T, $ty1, false>) -> Self {
                // default is zero - then is false - zero bit value
                let mut new_v = ExprNode::<T, $ty2, SIGN2>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                new_v.indexes[0..v.indexes.len()].copy_from_slice(v.indexes.as_slice());
                new_v
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                From<ExprNode<T, $ty1, true>> for ExprNode<T, $ty2, true>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: ExprNode<T, $ty1, true>) -> Self {
                // default is zero - then is false - zero bit value
                let len = <$ty1>::USIZE;
                let mut new_v = ExprNode::<T, $ty2, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                new_v.indexes[0..len].copy_from_slice(v.indexes.as_slice());
                let last = *v.indexes.last().unwrap();
                // copy sign to rest
                new_v.indexes[len..].iter_mut().for_each(|x| *x = last);
                new_v
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_from);

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
            xp = xp & self.bit(i).equal(rhs.bit(i));
        }
        xp
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        let mut xp = BoolExprNode::single(self.creator.clone(), false);
        for i in 0..N::USIZE {
            xp = xp | (self.bit(i) ^ rhs.bit(i));
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
            xp = (self.bit(i).equal(rhs.bit(i)) & xp) | ((!self.bit(i)) & rhs.bit(i));
        }
        xp
    }

    fn less_equal(self, rhs: Self) -> Self::Output {
        let mut xp = self.bit(0).imp(rhs.bit(0));
        for i in 1..self.indexes.len() {
            xp = (self.bit(i).equal(rhs.bit(i)) & xp) | ((!self.bit(i)) & rhs.bit(i));
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
            let mut lhs_num = self.as_unsigned().clone();
            let mut rhs_num = rhs.as_unsigned().clone();
            *lhs_num.indexes.last_mut().unwrap() = 0;
            *rhs_num.indexes.last_mut().unwrap() = 0;
            (lhs_num, rhs_num)
        };
        (lhs_sign.clone() & (!rhs_sign.clone()))
            | (lhs_sign.clone().equal(rhs_sign) &
            // if negative
            ((lhs_sign.clone() & lhs_num.clone().greater_than(rhs_num.clone()))
            // if positive
            | (!lhs_sign & lhs_num.less_than(rhs_num))))
    }

    fn less_equal(self, rhs: Self) -> Self::Output {
        let lhs_sign = self.bit(N::USIZE - 1);
        let rhs_sign = rhs.bit(N::USIZE - 1);
        let (lhs_num, rhs_num) = {
            let mut lhs_num = self.as_unsigned().clone();
            let mut rhs_num = rhs.as_unsigned().clone();
            *lhs_num.indexes.last_mut().unwrap() = 0;
            *rhs_num.indexes.last_mut().unwrap() = 0;
            (lhs_num, rhs_num)
        };
        (lhs_sign.clone() & (!rhs_sign.clone()))
            | (lhs_sign.clone().equal(rhs_sign) &
            // if negative
            ((lhs_sign.clone() & lhs_num.clone().greater_equal(rhs_num.clone()))
            // if positive
            | (!lhs_sign & lhs_num.less_equal(rhs_num))))
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

// macro helpers for binary operation traits.
macro_rules! impl_int_bitop {
    ($d:tt, $trait:ident, $op:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {
        /// Binary operation traits implementation.
        impl<T, N, const SIGN: bool> $trait for ExprNode<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = Self;

            fn $op(self, rhs: Self) -> Self::Output {
                ExprNode {
                    creator: self.creator.clone(),
                    indexes: GenericArray::from_exact_iter(
                        (0..N::USIZE)
                            .into_iter()
                            .map(|x| (self.bit(x).$op(rhs.bit(x))).index),
                    )
                    .unwrap(),
                }
            }
        }

        macro_rules! $macro_gen {
                    ($sign:expr, $pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        /// Binary operation traits implementation.
                        impl<T, $d( $d gparams ),* > $trait< $pty > for ExprNode<T, $ty, $sign>
                        where
                            T: VarLit + Neg<Output = T> + Debug,
                            isize: TryFrom<T>,
                            <T as TryInto<usize>>::Error: Debug,
                            <T as TryFrom<usize>>::Error: Debug,
                            <isize as TryFrom<T>>::Error: Debug,
                            $ty: ArrayLength<usize>,
                        {
                            type Output = Self;

                            fn $op(self, rhs: $pty) -> Self::Output {
                                ExprNode {
                                    creator: self.creator.clone(),
                                    indexes: GenericArray::from_exact_iter(
                                        (0..<$ty>::USIZE)
                                            .into_iter()
                                            .map(|x| (self.bit(x).$op(rhs.bit(x))).index),
                                    )
                                    .unwrap(),
                                }
                            }
                        }

                        /// Binary operation traits implementation.
                        impl<T, $d( $d gparams ),* > $trait<ExprNode<T, $ty, $sign>> for $pty
                        where
                            T: VarLit + Neg<Output = T> + Debug,
                            isize: TryFrom<T>,
                            <T as TryInto<usize>>::Error: Debug,
                            <T as TryFrom<usize>>::Error: Debug,
                            <isize as TryFrom<T>>::Error: Debug,
                            $ty: ArrayLength<usize>,
                        {
                            type Output = ExprNode<T, $ty, $sign>;

                            fn $op(self, rhs: ExprNode<T, $ty, $sign>) -> Self::Output {
                                ExprNode {
                                    creator: rhs.creator.clone(),
                                    indexes: GenericArray::from_exact_iter(
                                        (0..<$ty>::USIZE)
                                            .into_iter()
                                            .map(|x| (self.bit(x).$op(rhs.bit(x))).index),
                                    )
                                    .unwrap(),
                                }
                            }
                        }
                    }
                }

        macro_rules! $macro_upty {
                    ($pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        $macro_gen!(false, $pty, $ty, $d( $d gparams ),*);
                    }
                }
        macro_rules! $macro_ipty {
                    ($pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        $macro_gen!(true, $pty, $ty, $d( $d gparams ),*);
                    }
                }

        impl_int_upty_ty1!($macro_upty);
        impl_int_ipty_ty1!($macro_ipty);
    };
}

impl_int_bitop!($, BitAnd, bitand, impl_int_bitand_pty, impl_int_bitand_upty, impl_int_bitand_ipty);
impl_int_bitop!($, BitOr, bitor, impl_int_bitor_pty, impl_int_bitor_upty, impl_int_bitor_ipty);
impl_int_bitop!($, BitXor, bitxor, impl_int_bitxor_pty, impl_int_bitxor_upty, impl_int_bitxor_ipty);

// macro helpers for binary operation and assign traits.
macro_rules! impl_int_bitop_assign {
    ($d:tt, $trait:ident, $op_assign:ident, $op:ident, $macro_gen:ident, $macro_upty:ident,
            $macro_ipty:ident) => {
        /// Binary operation and assign traits implementation.
        impl<T, N, const SIGN: bool> $trait for ExprNode<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            fn $op_assign(&mut self, rhs: Self) {
                *self = self.clone().$op(rhs);
            }
        }

        macro_rules! $macro_gen {
                    ($sign:expr, $pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        /// Binary operation and assign traits implementation.
                        impl<T, $d( $d gparams ),* > $trait< $pty > for ExprNode<T, $ty, $sign>
                        where
                            T: VarLit + Neg<Output = T> + Debug,
                            isize: TryFrom<T>,
                            <T as TryInto<usize>>::Error: Debug,
                            <T as TryFrom<usize>>::Error: Debug,
                            <isize as TryFrom<T>>::Error: Debug,
                            $ty: ArrayLength<usize>,
                        {
                            fn $op_assign(&mut self, rhs: $pty) {
                                *self = self.clone().$op(rhs);
                            }
                        }
                    }
                }

        macro_rules! $macro_upty {
                    ($pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        $macro_gen!(false, $pty, $ty, $d( $d gparams ),*);
                    }
                }
        macro_rules! $macro_ipty {
                    ($pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        $macro_gen!(true, $pty, $ty, $d( $d gparams ),*);
                    }
                }

        impl_int_upty_ty1!($macro_upty);
        impl_int_ipty_ty1!($macro_ipty);
    };
}

impl_int_bitop_assign!($, BitAndAssign, bitand_assign, bitand, impl_int_bitand_assign_pty,
        impl_int_bitand_assign_upty, impl_int_bitand_assign_ipty);
impl_int_bitop_assign!($, BitOrAssign, bitor_assign, bitor, impl_int_bitor_assign_pty,
        impl_int_bitor_assign_upty, impl_int_bitor_assign_ipty);
impl_int_bitop_assign!($, BitXorAssign, bitxor_assign, bitxor, impl_int_bitxor_assign_pty,
        impl_int_bitxor_assign_upty, impl_int_bitxor_assign_ipty);

/// Not trait implementation.
impl<T, N, const SIGN: bool> Not for ExprNode<T, N, SIGN>
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
        ExprNode {
            creator: self.creator.clone(),
            indexes: GenericArray::from_exact_iter(
                (0..N::USIZE).into_iter().map(|x| (!self.bit(x)).index),
            )
            .unwrap(),
        }
    }
}

/// Shift left implementation.
impl<T, N, N2, const SIGN: bool, const SIGN2: bool> Shl<ExprNode<T, N2, SIGN2>>
    for ExprNode<T, N, SIGN>
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

    fn shl(self, rhs: ExprNode<T, N2, SIGN2>) -> Self::Output {
        let nbits = {
            let nbits = usize::BITS - N::USIZE.leading_zeros();
            if (1 << (nbits - 1)) == N::USIZE {
                nbits - 1
            } else {
                nbits
            }
        } as usize;
        // check whether zeroes in sign and in unused bits in Rhs
        if (SIGN2 && *rhs.indexes.last().unwrap() != 0)
            || !rhs.indexes.iter().skip(nbits).all(|x| *x == 0)
        {
            panic!("this arithmetic operation will overflow");
        }
        let nbits = cmp::min(nbits, N2::USIZE - usize::from(SIGN2));
        let mut output = GenericArray::default();
        for i in 0..nbits {
            output.iter_mut().enumerate().for_each(|(x, out)| {
                *out = bool_ite(
                    rhs.bit(i),
                    // if no overflow then get bit(v)
                    if x >= (1usize << i) {
                        self.bit(x - (1 << i))
                    } else {
                        BoolExprNode::new(self.creator.clone(), 0)
                    },
                    self.bit(x),
                )
                .index
            });
        }
        ExprNode {
            creator: self.creator.clone(),
            indexes: output,
        }
    }
}

macro_rules! impl_int_shl_immu {
    ($ty:ty) => {
        impl<T, N, const SIGN: bool> Shl<$ty> for ExprNode<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = Self;

            fn shl(self, rhs: $ty) -> Self::Output {
                // check whether zeroes
                if (rhs as usize) < N::USIZE {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                let mut output = GenericArray::default();
                output[usize_rhs..].copy_from_slice(&self.indexes[0..(N::USIZE - usize_rhs)]);
                ExprNode {
                    creator: self.creator.clone(),
                    indexes: output,
                }
            }
        }
    };
}

impl_int_shl_immu!(u8);
impl_int_shl_immu!(u16);
impl_int_shl_immu!(u32);
impl_int_shl_immu!(usize);
impl_int_shl_immu!(u64);
impl_int_shl_immu!(u128);

macro_rules! impl_int_shl_immi {
    ($ty:ty) => {
        impl<T, N, const SIGN: bool> Shl<$ty> for ExprNode<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = Self;

            fn shl(self, rhs: $ty) -> Self::Output {
                // check whether zeroes and sign in rhs
                if rhs < 0 || (rhs as usize) < N::USIZE {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                let mut output = GenericArray::default();
                output[usize_rhs..].copy_from_slice(&self.indexes[0..(N::USIZE - usize_rhs)]);
                ExprNode {
                    creator: self.creator.clone(),
                    indexes: output,
                }
            }
        }
    };
}

impl_int_shl_immi!(i8);
impl_int_shl_immi!(i16);
impl_int_shl_immi!(i32);
impl_int_shl_immi!(isize);
impl_int_shl_immi!(i64);
impl_int_shl_immi!(i128);

macro_rules! impl_int_shl_self_imm {
    ($ty:ty, $bits:ty) => {
        impl<T, N, const SIGN: bool> Shl<ExprNode<T, N, SIGN>> for $ty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            ExprNode<T, $bits, SIGN>: IntConstant<T, $ty>,
        {
            type Output = ExprNode<T, $bits, SIGN>;

            fn shl(self, rhs: ExprNode<T, N, SIGN>) -> Self::Output {
                ExprNode::<T, $bits, SIGN>::constant(rhs.creator.clone(), self) << rhs
            }
        }
    };
}

impl_int_shl_self_imm!(u8, U8);
impl_int_shl_self_imm!(u16, U16);
impl_int_shl_self_imm!(u32, U32);
#[cfg(target_pointer_width = "32")]
impl_int_shl_self_imm!(usize, U32);
#[cfg(target_pointer_width = "64")]
impl_int_shl_self_imm!(usize, U64);
impl_int_shl_self_imm!(u64, U64);
impl_int_shl_self_imm!(u128, U128);

impl_int_shl_self_imm!(i8, U8);
impl_int_shl_self_imm!(i16, U16);
impl_int_shl_self_imm!(i32, U32);
#[cfg(target_pointer_width = "32")]
impl_int_shl_self_imm!(isize, U32);
#[cfg(target_pointer_width = "64")]
impl_int_shl_self_imm!(isize, U64);
impl_int_shl_self_imm!(i64, U64);
impl_int_shl_self_imm!(i128, U128);

/// Shift right implementation.
impl<T, N, const SIGN: bool, N2, const SIGN2: bool> Shr<ExprNode<T, N2, SIGN2>>
    for ExprNode<T, N, SIGN>
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

    fn shr(self, rhs: ExprNode<T, N2, SIGN2>) -> Self::Output {
        let nbits = {
            let nbits = usize::BITS - N::USIZE.leading_zeros();
            if (1 << (nbits - 1)) == N::USIZE {
                nbits - 1
            } else {
                nbits
            }
        } as usize;
        // check whether zeroes in sign and in unused bits in Rhs
        if (SIGN2 && *rhs.indexes.last().unwrap() != 0)
            || !rhs.indexes.iter().skip(nbits).all(|x| *x == 0)
        {
            panic!("this arithmetic operation will overflow");
        }
        let nbits = cmp::min(nbits, N2::USIZE - usize::from(SIGN2));
        let mut output = GenericArray::default();
        for i in 0..nbits {
            output.iter_mut().enumerate().for_each(|(x, out)| {
                *out = bool_ite(
                    rhs.bit(i),
                    // if no overflow then get bit(v)
                    if x + (1usize << i) < N::USIZE {
                        self.bit(x + (1 << i))
                    } else {
                        BoolExprNode::new(
                            self.creator.clone(),
                            if SIGN {
                                *self.indexes.last().unwrap()
                            } else {
                                0
                            },
                        )
                    },
                    self.bit(x),
                )
                .index
            });
        }
        ExprNode {
            creator: self.creator.clone(),
            indexes: output,
        }
    }
}

macro_rules! impl_int_shr_immu {
    ($ty:ty) => {
        impl<T, N, const SIGN: bool> Shr<$ty> for ExprNode<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = Self;

            fn shr(self, rhs: $ty) -> Self::Output {
                // check whether zeroes
                if (rhs as usize) < N::USIZE {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                let mut output = GenericArray::from_exact_iter(
                    iter::repeat(if SIGN {
                        *self.indexes.last().unwrap()
                    } else {
                        0
                    })
                    .take(N::USIZE),
                )
                .unwrap();
                output[0..(N::USIZE - usize_rhs)].copy_from_slice(&self.indexes[usize_rhs..]);
                ExprNode {
                    creator: self.creator.clone(),
                    indexes: output,
                }
            }
        }
    };
}

impl_int_shr_immu!(u8);
impl_int_shr_immu!(u16);
impl_int_shr_immu!(u32);
impl_int_shr_immu!(usize);
impl_int_shr_immu!(u64);
impl_int_shr_immu!(u128);

macro_rules! impl_int_shr_immi {
    ($ty:ty) => {
        impl<T, N, const SIGN: bool> Shr<$ty> for ExprNode<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = Self;

            fn shr(self, rhs: $ty) -> Self::Output {
                // check whether zeroes
                if rhs < 0 || (rhs as usize) < N::USIZE {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                let mut output = GenericArray::from_exact_iter(
                    iter::repeat(if SIGN {
                        *self.indexes.last().unwrap()
                    } else {
                        0
                    })
                    .take(N::USIZE),
                )
                .unwrap();
                output[0..(N::USIZE - usize_rhs)].copy_from_slice(&self.indexes[usize_rhs..]);
                ExprNode {
                    creator: self.creator.clone(),
                    indexes: output,
                }
            }
        }
    };
}

impl_int_shr_immi!(i8);
impl_int_shr_immi!(i16);
impl_int_shr_immi!(i32);
impl_int_shr_immi!(isize);
impl_int_shr_immi!(i64);
impl_int_shr_immi!(i128);

macro_rules! impl_int_shr_self_imm {
    ($ty:ty, $bits:ty) => {
        impl<T, N, const SIGN: bool> Shr<ExprNode<T, N, SIGN>> for $ty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            ExprNode<T, $bits, SIGN>: IntConstant<T, $ty>,
        {
            type Output = ExprNode<T, $bits, SIGN>;

            fn shr(self, rhs: ExprNode<T, N, SIGN>) -> Self::Output {
                ExprNode::<T, $bits, SIGN>::constant(rhs.creator.clone(), self) >> rhs
            }
        }
    };
}

impl_int_shr_self_imm!(u8, U8);
impl_int_shr_self_imm!(u16, U16);
impl_int_shr_self_imm!(u32, U32);
#[cfg(target_pointer_width = "32")]
impl_int_shr_self_imm!(usize, U32);
#[cfg(target_pointer_width = "64")]
impl_int_shr_self_imm!(usize, U64);
impl_int_shr_self_imm!(u64, U64);
impl_int_shr_self_imm!(u128, U128);

impl_int_shr_self_imm!(i8, U8);
impl_int_shr_self_imm!(i16, U16);
impl_int_shr_self_imm!(i32, U32);
#[cfg(target_pointer_width = "32")]
impl_int_shr_self_imm!(isize, U32);
#[cfg(target_pointer_width = "64")]
impl_int_shr_self_imm!(isize, U64);
impl_int_shr_self_imm!(i64, U64);
impl_int_shr_self_imm!(i128, U128);

// ShlAssign
macro_rules! impl_int_shx_assign {
    ($trait:ident, $op:ident, $op_assign:ident, $macro:ident) => {
        impl<T, N, const SIGN: bool, N2, const SIGN2: bool> $trait<ExprNode<T, N2, SIGN2>>
            for ExprNode<T, N, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            N2: ArrayLength<usize>,
        {
            fn $op_assign(&mut self, rhs: ExprNode<T, N2, SIGN2>) {
                *self = self.clone().$op(rhs)
            }
        }

        macro_rules! $macro {
            ($ty:ty) => {
                impl<T, N, const SIGN: bool> $trait<$ty> for ExprNode<T, N, SIGN>
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
            };
        }

        $macro!(u8);
        $macro!(u16);
        $macro!(u32);
        $macro!(usize);
        $macro!(u64);
        $macro!(u128);
        $macro!(i8);
        $macro!(i16);
        $macro!(i32);
        $macro!(isize);
        $macro!(i64);
        $macro!(i128);
    };
}

impl_int_shx_assign!(ShlAssign, shl, shl_assign, impl_int_shl_assign_imm);
impl_int_shx_assign!(ShrAssign, shr, shr_assign, impl_int_shr_assign_imm);

//////////
// Add/Sub implementation

impl<T, N, const SIGN: bool> Add<ExprNode<T, N, SIGN>> for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut output = GenericArray::<usize, N>::default();
        let mut c = BoolExprNode::new(self.creator.clone(), 0); // false
        for i in 0..N::USIZE - 1 {
            (output[i], c) = {
                let (s0, c0) = full_adder(self.bit(i), rhs.bit(i), c);
                (s0.index, c0)
            };
        }
        output[N::USIZE - 1] = (self.bit(N::USIZE - 1) ^ rhs.bit(N::USIZE - 1) ^ c).index;
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

macro_rules! impl_int_binary_op {
    ($d:tt, $trait:ident, $op:ident, $macro_gen:ident, $macro_upty:ident, $macro_ipty:ident) => {

        macro_rules! $macro_gen {
                    ($sign:expr, $pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        /// Binary operation traits implementation.
                        impl<T, $d( $d gparams ),* > $trait< $pty > for ExprNode<T, $ty, $sign>
                        where
                            T: VarLit + Neg<Output = T> + Debug,
                            isize: TryFrom<T>,
                            <T as TryInto<usize>>::Error: Debug,
                            <T as TryFrom<usize>>::Error: Debug,
                            <isize as TryFrom<T>>::Error: Debug,
                            $ty: ArrayLength<usize>,
                        {
                            type Output = Self;

                            fn $op(self, rhs: $pty) -> Self::Output {
                                let creator = self.creator.clone();
                                self.$op(Self::constant(creator, rhs))
                            }
                        }

                        /// Binary operation traits implementation.
                        impl<T, $d( $d gparams ),* > $trait<ExprNode<T, $ty, $sign>> for $pty
                        where
                            T: VarLit + Neg<Output = T> + Debug,
                            isize: TryFrom<T>,
                            <T as TryInto<usize>>::Error: Debug,
                            <T as TryFrom<usize>>::Error: Debug,
                            <isize as TryFrom<T>>::Error: Debug,
                            $ty: ArrayLength<usize>,
                        {
                            type Output = ExprNode<T, $ty, $sign>;

                            fn $op(self, rhs: ExprNode<T, $ty, $sign>) -> Self::Output {
                                let creator = rhs.creator.clone();
                                ExprNode::<T, $ty, $sign>::constant(creator, self).$op(rhs)
                            }
                        }
                    }
                }

        macro_rules! $macro_upty {
                    ($pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        $macro_gen!(false, $pty, $ty, $d( $d gparams ),*);
                    }
                }
        macro_rules! $macro_ipty {
                    ($pty:ty, $ty:ty, $d($d gparams:ident),*) => {
                        $macro_gen!(true, $pty, $ty, $d( $d gparams ),*);
                    }
                }

        impl_int_upty_ty1!($macro_upty);
        impl_int_ipty_ty1!($macro_ipty);
    }
}

impl_int_binary_op!($, Add, add, impl_int_add_pty, impl_int_add_upty, impl_int_add_ipty);

impl<T, N, const SIGN: bool> Sub<ExprNode<T, N, SIGN>> for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut output = GenericArray::<usize, N>::default();
        let mut c = BoolExprNode::new(self.creator.clone(), 1); // true
        for i in 0..N::USIZE - 1 {
            (output[i], c) = {
                let (s0, c0) = full_adder(self.bit(i), !rhs.bit(i), c);
                (s0.index, c0)
            };
        }
        output[N::USIZE - 1] = (self.bit(N::USIZE - 1) ^ !rhs.bit(N::USIZE - 1) ^ c).index;
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl_int_binary_op!($, Sub, sub, impl_int_sub_pty, impl_int_sub_upty, impl_int_sub_ipty);

// AddAssign,  SubAssign
impl_int_bitop_assign!($, AddAssign, add_assign, add, impl_int_add_assign_pty,
        impl_int_add_assign_upty, impl_int_add_assign_ipty);
impl_int_bitop_assign!($, SubAssign, sub_assign, sub, impl_int_sub_assign_pty,
        impl_sub_add_assign_upty, impl_int_sub_assign_ipty);

// Neg impl

impl<T, N> Neg for ExprNode<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        let mut output = GenericArray::<usize, N>::default();
        let mut c = BoolExprNode::new(self.creator.clone(), 1); // true
        for i in 0..N::USIZE-1 {
            (output[i], c) = {
                let (s0, c0) = half_adder(!self.bit(i), c);
                (s0.index, c0)
            };
        }
        output[N::USIZE-1] = (!self.bit(N::USIZE-1) ^ c).index;
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

/// Most advanced: multiplication.

fn gen_dadda_mult<T>(creator: Rc<RefCell<ExprCreator<T>>>, matrix: &mut [Vec<usize>]) -> Vec<usize>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    let max_col_size = matrix.iter().map(|col| col.len()).max().unwrap();
    let mut step_sizes = vec![];
    {
        let mut max_step_size = 2usize;
        while max_step_size < max_col_size {
            step_sizes.push(max_step_size);
            max_step_size += max_step_size >> 1;
        }
    }
    let mut extracol: Vec<usize> = vec![];
    let mut next_extracol: Vec<usize> = vec![];
    // main routine
    let matrixlen = matrix.len();
    for new_column_size in step_sizes.iter().rev() {
        for (coli, col) in matrix.iter_mut().enumerate() {
            extracol.clear();
            if col.len() + extracol.len() > *new_column_size {
                let cells_to_reduce = extracol.len() + col.len() - *new_column_size;
                let mut src = col.len() - cells_to_reduce - ((cells_to_reduce + 1) >> 1);
                let mut dest = src;
                while src < col.len() {
                    let a = BoolExprNode::new(creator.clone(), col[src]);
                    let b = BoolExprNode::new(creator.clone(), col[src + 1]);
                    if coli + 1 < matrixlen {
                        let (s, c) = if src + 2 < col.len() {
                            // full adder
                            full_adder(a, b, BoolExprNode::new(creator.clone(), col[src + 2]))
                        } else {
                            // half adder
                            half_adder(a, b)
                        };
                        col[dest] = s.index;
                        next_extracol.push(c.index);
                    } else {
                        // only sum, ignore carry
                        col[dest] = if src + 2 < col.len() {
                            // full adder
                            a ^ b ^ BoolExprNode::new(creator.clone(), col[src + 2])
                        } else {
                            // half adder
                            a ^ b
                        }
                        .index;
                    }
                    src += 3;
                    dest += 1;
                }
                col.resize(dest, 0);
            }
            col.extend(extracol.iter());
            std::mem::swap(&mut extracol, &mut next_extracol);
        }
    }

    // last phase
    let mut output = vec![0; matrix.len()];
    let mut c = BoolExprNode::new(creator.clone(), 0); // false
    for (i, col) in matrix.iter().enumerate() {
        (output[i], c) = if col.len() == 2 {
            let (s0, c0) = full_adder(
                BoolExprNode::new(creator.clone(), col[0]),
                BoolExprNode::new(creator.clone(), col[1]),
                c,
            );
            (s0.index, c0)
        } else {
            let (s0, c0) = half_adder(BoolExprNode::new(creator.clone(), col[0]), c);
            (s0.index, c0)
        };
    }
    let col = matrix.last().unwrap();
    output[matrix.len() - 1] = if col.len() == 2 {
        BoolExprNode::new(creator.clone(), col[0]) ^ BoolExprNode::new(creator.clone(), col[1]) ^ c
    } else {
        BoolExprNode::new(creator.clone(), col[0]) ^ c
    }
    .index;

    output
}

fn gen_dadda_matrix<'a, T>(
    creator: Rc<RefCell<ExprCreator<T>>>,
    avector: &'a [usize],
    bvector: &'a [usize],
    col_num: usize,
) -> Vec<Vec<usize>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    let mut matrix = (0..col_num).into_iter().map(|_| vec![]).collect::<Vec<_>>();
    for (i, a) in avector.iter().enumerate() {
        for (j, b) in bvector.iter().enumerate() {
            if i + j < col_num {
                matrix[i + j][i] = (BoolExprNode::new(creator.clone(), *a)
                    & BoolExprNode::new(creator.clone(), *b))
                .index
            }
        }
    }
    matrix
}

impl<T, N, const SIGN: bool> Mul<ExprNode<T, N, SIGN>> for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut matrix = gen_dadda_matrix(
            self.creator.clone(),
            &self.indexes,
            &rhs.indexes.as_slice(),
            N::USIZE,
        );
        let mut res = gen_dadda_mult(self.creator.clone(), &mut matrix);
        ExprNode {
            creator: self.creator,
            indexes: GenericArray::from_exact_iter(res.drain(..)).unwrap(),
        }
    }
}

impl_int_binary_op!($, Mul, mul, impl_int_mul_pty, impl_int_mul_upty, impl_int_mul_ipty);
impl_int_bitop_assign!($, MulAssign, mul_assign, mul, impl_int_mul_assign_pty,
        impl_int_mul_assign_upty, impl_int_mul_assign_ipty);

/// Returns result of the If-Then-Else (ITE) - integer version.
pub fn int_ite<C, T, E>(
    c: C,
    t: T,
    e: E,
) -> <<T as BitAnd>::Output as BitOr<<E as BitAnd>::Output>>::Output
where
    C: BitAnd<T> + Not + Clone,
    T: BitAnd + BitMask<C>,
    E: BitAnd + BitMask<<C as Not>::Output>,
    <C as Not>::Output: BitAnd<E>,
    <T as BitAnd<T>>::Output: BitOr<<E as BitAnd<E>>::Output>,
{
    (<T as BitMask<C>>::bitmask(c.clone()) & t)
        | (<E as BitMask<<C as Not>::Output>>::bitmask(!c) & e)
}
