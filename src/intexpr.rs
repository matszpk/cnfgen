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
use std::fmt::Debug;
use std::ops::Neg;
use std::rc::Rc;

use generic_array::typenum::*;
use generic_array::*;

use crate::boolexpr::{BoolEqual, ExprNode as BoolExprNode};
use crate::boolexpr_creator::ExprCreator;
use crate::VarLit;

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

/// Equality operator for PartialEq.
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

    #[inline]
    pub fn bit(&self, n: usize) -> BoolExprNode<T> {
        BoolExprNode::new(self.creator.clone(), self.indexes[n])
    }
}

macro_rules! impl_int_ty1_lt_ty2 {
    ($impl_mac:ident) => {
        $impl_mac!(UInt<N, B0>, UInt<N, B1>, );
        $impl_mac!(UInt<UInt<N, B0>, BX0>, UInt<UInt<N, B1>, BX0>, BX0);
        $impl_mac!(UInt<UInt<UInt<N, B0>, BX1>, BX0>, UInt<UInt<UInt<N, B1>, BX1>, BX0>, BX0, BX1);
        $impl_mac!(UInt<UInt<UInt<UInt<N, B0>, BX2>, BX1>, BX0>,
                UInt<UInt<UInt<UInt<N, B1>, BX2>, BX1>, BX0>, BX0, BX1, BX2);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<N, B0>, BX3>, BX2>, BX1>, BX0>,
                UInt<UInt<UInt<UInt<UInt<N, B1>, BX3>, BX2>, BX1>, BX0>, BX0, BX1, BX2, BX3);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<N, B0>, BX4>, BX3>, BX2>, BX1>, BX0>,
                UInt<UInt<UInt<UInt<UInt<UInt<N, B1>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>,
                        BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>,
                        BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<N, B0>,
                        BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<N, B1>,
                        BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<N, B0>,
                        BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>,
                        BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<N, B1>,
                        BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>,
                        BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<N, B0>,
                        BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>,
                        BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<N, B1>,
                        BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>,
                        BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<N, B0>,
                        BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>,
                        BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<N, B1>,
                        BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>,
                        BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15, BX16);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>,
                        BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>, BX7>,
                        BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15, BX16, BX17);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>,
                        BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>, BX8>,
                        BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15, BX16, BX17, BX18);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>,
                        BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>, BX9>,
                        BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15, BX16, BX17, BX18, BX19);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX20>, BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>,
                        BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX20>, BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>, BX10>,
                        BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15, BX16, BX17, BX18, BX19, BX20);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX21>, BX20>, BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>,
                        BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX21>, BX20>, BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>, BX11>,
                        BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15, BX16, BX17, BX18, BX19, BX20, BX21);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX22>, BX21>, BX20>, BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>,
                        BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX22>, BX21>, BX20>, BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>, BX12>,
                        BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>, BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15, BX16, BX17, BX18, BX19, BX20, BX21, BX22);
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B0>,
                        BX23>, BX22>, BX21>, BX20>, BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>,
                        BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>,
                        BX0>,
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                    UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<N, B1>,
                        BX23>, BX22>, BX21>, BX20>, BX19>, BX18>, BX17>, BX16>, BX15>, BX14>, BX13>,
                        BX12>, BX11>, BX10>, BX9>, BX8>, BX7>, BX6>, BX5>, BX4>, BX3>, BX2>, BX1>,
                        BX0>,
                    BX0, BX1, BX2, BX3, BX4, BX5, BX6, BX7, BX8, BX9, BX10, BX11, BX12, BX13, BX14,
                    BX15, BX16, BX17, BX18, BX19, BX20, BX21, BX22, BX23);
    }
}

// TryFrom implementation
macro_rules! impl_int_try_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, N: ArrayLength<usize>, const SIGN2: bool, $( $gparams ),* >
                TryFrom<ExprNode<T, $ty2, SIGN2>> for ExprNode<T, $ty1, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: ExprNode<T, $ty2, SIGN2>) -> Result<Self, Self::Error> {
                let mut new_v = ExprNode::<T, $ty1, false>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                let len1 = new_v.indexes.len();
                // if all rest of bits are 0 - just false
                if !v.indexes.iter().skip(len1).all(|x| *x==0) {
                    return Err(IntError::BitOverflow);
                }
                new_v.indexes.copy_from_slice(&v.indexes[0..len1]);
                Ok(new_v)
            }
        }

        impl<T: VarLit, N: ArrayLength<usize>, $( $gparams ),* >
                TryFrom<ExprNode<T, $ty2, false>> for ExprNode<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: ExprNode<T, $ty2, false>) -> Result<Self, Self::Error> {
                let mut new_v = ExprNode::<T, $ty1, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                let len1 = new_v.indexes.len();
                // if all rest of bits are 0 - just false
                if !v.indexes.iter().skip(len1-1).all(|x| *x==0) {
                    return Err(IntError::BitOverflow);
                }
                new_v.indexes.copy_from_slice(&v.indexes[0..len1]);
                Ok(new_v)
            }
        }

        impl<T: VarLit, N: ArrayLength<usize>, $( $gparams ),* >
                TryFrom<ExprNode<T, $ty2, true>> for ExprNode<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: ExprNode<T, $ty2, true>) -> Result<Self, Self::Error> {
                let mut new_v = ExprNode::<T, $ty1, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                let len1 = new_v.indexes.len();
                let last_idx = v.indexes[len1-1];
                if !v.indexes.iter().skip(len1).all(|x| last_idx==*x) {
                    return Err(IntError::BitOverflow);
                }
                new_v.indexes.copy_from_slice(&v.indexes[0..len1]);
                Ok(new_v)
            }
        }

        // try from for rest
        impl<T: VarLit, N: ArrayLength<usize>, $( $gparams ),* >
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
        impl<T: VarLit, N: ArrayLength<usize>, const SIGN2: bool, $( $gparams ),* >
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

        impl<T: VarLit, N: ArrayLength<usize>, $( $gparams ),* >
                From<ExprNode<T, $ty1, true>> for ExprNode<T, $ty2, true>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: ExprNode<T, $ty1, true>) -> Self {
                // default is zero - then is false - zero bit value
                let mut new_v = ExprNode::<T, $ty2, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                let len = v.indexes.len();
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

impl<T, N: ArrayLength<usize>, const SIGN: bool> IntEqual for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        let mut xp = BoolExprNode::single(self.creator.clone(), true);
        for i in 0..self.indexes.len() {
            xp = xp & self.bit(i).equal(rhs.bit(i));
        }
        xp
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        let mut xp = BoolExprNode::single(self.creator.clone(), false);
        for i in 0..self.indexes.len() {
            xp = xp | (self.bit(i) ^ rhs.bit(i));
        }
        xp
    }
}
