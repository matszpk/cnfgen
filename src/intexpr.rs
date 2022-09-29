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
        // 1 < 0b1Y
        $impl_mac!(U1, UInt<UInt<UTerm, B1>, Y0>, Y0);
        // 1 < 0b1YY
        $impl_mac!(U1, UInt<UInt<UInt<UTerm, B1>, Y1>, Y0>, Y0, Y1);
        // 1 < 0b1YYY
        $impl_mac!(U1, UInt<UInt<UInt<UInt<UTerm, B1>, Y2>, Y1>, Y0>, Y0, Y1, Y2);
        // 1 < 0b1YYYY
        $impl_mac!(U1, UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y3>, Y2>, Y1>, Y0>,
                Y0, Y1, Y2, Y3);
        // 1 < 0b1YYYYY
        $impl_mac!(U1, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y4>, Y3>, Y2>, Y1>, Y0>,
                Y0, Y1, Y2, Y3, Y4);
        // 1 < 0b1YYYYYY
        $impl_mac!(U1, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>,
                Y1>, Y0>, Y0, Y1, Y2, Y3, Y4, Y5);
        // 1 < 0b1YYYYYYY
        $impl_mac!(U1, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>,
                Y3>, Y2>, Y1>, Y0>, Y0, Y1, Y2, Y3, Y4, Y5, Y6);
        // 1 < 0b1YYYYYYYY
        $impl_mac!(U1, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y7>, Y6>, Y5>,
                Y4>, Y3>, Y2>, Y1>, Y0>, Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7);
        
        //---------------------
        // 2 < 3
        $impl_mac!(U2, U3, );
        // 0b1X < 0b1YY
        $impl_mac!(UInt<UInt<UTerm, B1>, X0>, UInt<UInt<UInt<UTerm, B1>, Y1>, Y0>,
                X0, Y0, Y1);
        // 0b1X < 0b1YYY
        $impl_mac!(UInt<UInt<UTerm, B1>, X0>, UInt<UInt<UInt<UInt<UTerm, B1>, Y2>, Y1>, Y0>,
                X0, Y0, Y1, Y2);
        // 0b1X < 0b1YYYY
        $impl_mac!(UInt<UInt<UTerm, B1>, X0>, UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y3>, Y2>,
                Y1>, Y0>, X0, Y0, Y1, Y2, Y3);
        // 0b1X < 0b1YYYYY
        $impl_mac!(UInt<UInt<UTerm, B1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y4>,
                Y3>, Y2>, Y1>, Y0>, X0, Y0, Y1, Y2, Y3, Y4);
        // 0b1X < 0b1YYYYYY
        $impl_mac!(UInt<UInt<UTerm, B1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>,
                Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, Y0, Y1, Y2, Y3, Y4, Y5);
        // 0b1X < 0b1YYYYYYY
        $impl_mac!(UInt<UInt<UTerm, B1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm,
                B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, Y0, Y1, Y2, Y3, Y4, Y5,
                Y6);
        // 0b1X < 0b1YYYYYYYY
        $impl_mac!(UInt<UInt<UTerm, B1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<
                UTerm, B1>, Y7>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, Y0, Y1, Y2,
                Y3, Y4, Y5, Y6, Y7);
        
        //---------------------
        // 0b100 < 0b101
        $impl_mac!(U4, U5, );
        // 0b10X < 0b11Y
        $impl_mac!(UInt<UInt<UInt<UTerm, B1>, B0>, X0>, UInt<UInt<UInt<UTerm, B1>, B1>, Y0>,
                X0, Y0);
        // 0b110 < 0b111
        $impl_mac!(U6, U7, );
        //---------------------
        // 0b1XX < 0b1YYY
        $impl_mac!(UInt<UInt<UInt<UTerm, B1>, X1>, X0>, UInt<UInt<UInt<UInt<UTerm, B1>, Y2>,
                Y1>, Y0>, X0, X1, Y0, Y1, Y2);
        // 0b1XX < 0b1YYYY
        $impl_mac!(UInt<UInt<UInt<UTerm, B1>, X1>, X0>, UInt<UInt<UInt<UInt<UInt<UTerm, B1>,
                Y3>, Y2>, Y1>, Y0>, X0, X1, Y0, Y1, Y2, Y3);
        // 0b1XX < 0b1YYYYY
        $impl_mac!(UInt<UInt<UInt<UTerm, B1>, X1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UTerm,
                B1>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1, Y0, Y1, Y2, Y3, Y4);
        // 0b1XX < 0b1YYYYYY
        $impl_mac!(UInt<UInt<UInt<UTerm, B1>, X1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UInt
                <UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1, Y0, Y1, Y2, Y3,
                Y4, Y5);
        // 0b1XX < 0b1YYYYYYY
        $impl_mac!(UInt<UInt<UInt<UTerm, B1>, X1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UInt
                <UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1, Y0, Y1,
                Y2, Y3, Y4, Y5, Y6);
        // 0b1XX < 0b1YYYYYYYY
        $impl_mac!(UInt<UInt<UInt<UTerm, B1>, X1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UInt
                <UInt<UInt<UTerm, B1>, Y7>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1,
                Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7);
        
        //---------------------
        // 0b1000 < 0b1001
        $impl_mac!(U8, U9, );
        // 0b100X < 0b101Y
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y0>, X0, Y0);
        // 0b100X < 0b11YY
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>, X0, Y0, Y1);
        // 0b1010 < 0b1011
        $impl_mac!(U10, U11, );
        // 0b101X < 0b11YY
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y1>, Y0>, X0, Y0, Y1);
        // 0b1100 < 0b1101
        $impl_mac!(U12, U13, );
        // 0b110X < 0b111Y
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, X0>,
                UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y0>, X0, Y0);
        // 0b1100 < 0b1111
        $impl_mac!(U14, U15, );
        //---------------------
        // 0b1XXX < 0b1YYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>, UInt<UInt<UInt<UInt<UInt
                <UTerm, B1>, Y3>, Y2>, Y1>, Y0>, X0, X1, X2, Y0, Y1, Y2, Y3);
        // 0b1XXX < 0b1YYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>, UInt<UInt<UInt<UInt<UInt
                <UInt<UTerm, B1>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1, X2, Y0, Y1, Y2,
                Y3, Y4);
        // 0b1XXX < 0b1YYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>, UInt<UInt<UInt<UInt<UInt
                <UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1, X2, Y0,
                Y1, Y2, Y3, Y4, Y5);
        // 0b1XXX < 0b1YYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>, UInt<UInt<UInt<UInt<UInt
                <UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1,
                X2, Y0, Y1, Y2, Y3, Y4, Y5, Y6);
        // 0b1XXX < 0b1YYYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UTerm, B1>, X2>, X1>, X0>, UInt<UInt<UInt<UInt<UInt
                <UInt<UInt <UInt<UInt<UTerm, B1>, Y7>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
                X0, X1, X2, Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7);
        
        //---------------------
        // 0b10000 < 0b10001
        $impl_mac!(U16, U17, );
        // 0b1000X < 0b1001Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, Y0>, X0, Y0);
        // 0b1000X < 0b101YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y1>, Y0>, X0, Y0, Y1);
        // 0b1000X < 0b11YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y2>, Y1>, Y0>, X0, Y0, Y1, Y2);
        // 0b10010 < 0b10011
        $impl_mac!(U18, U19, );
        // 0b1001X < 0b101YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y1>, Y0>, X0, Y0, Y1);
        // 0b1001X < 0b11YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y2>, Y1>, Y0>, X0, Y0, Y1, Y2);
        // 0b10100 < 0b10101
        $impl_mac!(U20, U21, );
        // 0b1010X < 0b1011Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B1>, Y0>, X0, Y0);
        // 0b10100 < 0b10111
        $impl_mac!(U22, U23, );
        // 0b101XX < 0b11YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, X1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y2>, Y1>, Y0>, X0, X1, Y0, Y1,
                Y2);
        // 0b11000 < 0b11001
        $impl_mac!(U24, U25, );
        // 0b1100X < 0b1101Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, Y0>, X0, Y0);
        // 0b1100X < 0b111YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y1>, Y0>, X0, Y0, Y1);
        // 0b11010 < 0b11011
        $impl_mac!(U26, U27, );
        // 0b1101X < 0b111YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y1>, Y0>, X0, Y0, Y1);
        // 0b11100 < 0b11101
        $impl_mac!(U28, U29, );
        // 0b1110X < 0b1111Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, Y0>, X0, Y0);
        // 0b11110 < 0b11111
        $impl_mac!(U30, U31, );
        //---------------------
        // 0b1XXXX < 0b1YYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>, UInt<UInt<UInt
                <UInt<UInt <UInt<UTerm, B1>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1, X2, X3,
                Y0, Y1, Y2, Y3, Y4);
        // 0b1XXXX < 0b1YYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>, UInt<UInt<UInt
                <UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1,
                X2, X3, Y0, Y1, Y2, Y3, Y4, Y5);
        // 0b1XXXX < 0b1YYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>, UInt<UInt<UInt
                <UInt<UInt <UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>,
                X0, X1, X2, X3, Y0, Y1, Y2, Y3, Y4, Y5, Y6);
        // 0b1XXXX < 0b1YYYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X3>, X2>, X1>, X0>, UInt<UInt<UInt
                <UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y7>, Y6>, Y5>, Y4>, Y3>, Y2>,
                Y1>, Y0>, X0, X1, X2, X3, Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7);
        
        
        //---------------------
        // 0b100000 < 0b100001
        $impl_mac!(U32, U33, );
        // 0b10000X < 0b10001Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B1>, Y0>, X0, Y0);
        // 0b10000X < 0b1001YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, Y1>, Y0>, X0, Y0,
                Y1);
        // 0b10000X < 0b101YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y2>, Y1>, Y0>, X0, Y0,
                Y1, Y2);
        // 0b10000X < 0b11YYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y3>, Y2>, Y1>, Y0>, X0, Y0,
                Y1, Y2, Y3);
        // 0b100010 < 0b100011
        $impl_mac!(U34, U35, );
        // 0b10001X < 0b1001YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, Y1>, Y0>, X0, Y0,
                Y1);
        // 0b10001X < 0b101YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y2>, Y1>, Y0>, X0, Y0,
                Y1, Y2);
        // 0b10001X < 0b11YYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y3>, Y2>, Y1>, Y0>, X0, Y0,
                Y1, Y2, Y3);
        // 0b100100 < 0b100101
        $impl_mac!(U36, U37, );
        // 0b10010X < 0b10011Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, B1>, Y0>, X0, Y0);
        // 0b100100 < 0b100111
        $impl_mac!(U38, U39, );
        // 0b1001XX < 0b101YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, X1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, Y2>, Y1>, Y0>, X0, X1,
                Y0, Y1, Y2);
        // 0b1001XX < 0b11YYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B1>, X1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y3>, Y2>, Y1>, Y0>, X0, X1,
                Y0, Y1, Y2, Y3);
        //---------------------
        // 0b101000 < 0b101001
        $impl_mac!(U40, U41, );
        // 0b10100X < 0b10101Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B1>, Y0>, X0, Y0);
        // 0b10100X < 0b1011YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B1>, Y1>, Y0>, X0, Y0, Y1);
        // 0b101010 < 0b101011
        $impl_mac!(U42, U43, );
        // 0b10101X < 0b1011YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B1>, Y1>, Y0>, X0, Y0, Y1);
        // 0b101100 < 0b101101
        $impl_mac!(U44, U45, );
        // 0b10110X < 0b10111Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B1>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, B1>, B1>, Y0>, X0, Y0);
        // 0b101100 < 0b101111
        $impl_mac!(U46, U47, );
        // 0b101XXX < 0b11YYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B1>, X2>, X1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, Y3>, Y2>, Y1>, Y0>, X0, X1,
                X2, Y0, Y1, Y2, Y3);
        //---------------------
        // 0b110000 < 0b110001
        $impl_mac!(U48, U49, );
        // 0b11000X < 0b11001Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>, Y0>, X0, Y0);
        // 0b11000X < 0b1101YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, Y1>, Y0>, X0, Y0,
                Y1);
        // 0b11000X < 0b111YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y2>, Y1>, Y0>, X0, Y0,
                Y1, Y2);
        // 0b110010 < 0b110011
        $impl_mac!(U50, U51, );
        // 0b11001X < 0b1101YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, Y1>, Y0>, X0, Y0,
                Y1);
        // 0b11001X < 0b111YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y2>, Y1>, Y0>, X0, Y0,
                Y1, Y2);
        // 0b110100 < 0b110101
        $impl_mac!(U52, U53, );
        // 0b11010X < 0b11011Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, B1>, Y0>, X0, Y0);
        // 0b110100 < 0b110111
        $impl_mac!(U54, U55, );
        // 0b1101XX < 0b111YYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B0>, B1>, X1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, Y2>, Y1>, Y0>, X0, X1,
                Y0, Y1, Y2);
        // 0b111000 < 0b111001
        $impl_mac!(U56, U57, );
        // 0b11100X < 0b11101Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B0>, B1>, Y0>, X0, Y0);
        // 0b11100X < 0b1111YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B0>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, Y1>, Y0>, X0, Y0,
                Y1);
        // 0b111010 < 0b111011
        $impl_mac!(U58, U59, );
        // 0b11101X < 0b1111YY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B0>, B1>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, Y1>, Y0>, X0, Y0,
                Y1);
        // 0b111100 < 0b111101
        $impl_mac!(U60, U61, );
        // 0b11110X < 0b11111Y
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, B0>, X0>,
                UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B1>, B1>, B1>, B1>, Y0>, X0, Y0);
        // 0b111110 < 0b111111
        $impl_mac!(U62, U63, );
        //---------------------
        // 0b1XXXXX < 0b1YYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>, UInt
                <UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y5>, Y4>, Y3>, Y2>, Y1>,
                Y0>, X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Y5);
        // 0b1XXXXX < 0b1YYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>, UInt
                <UInt<UInt<UInt<UInt <UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>, Y2>,
                Y1>, Y0>, X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Y5, Y6);
        // 0b1XXXXX < 0b1YYYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X4>, X3>, X2>, X1>, X0>, UInt
                <UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y7>, Y6>, Y5>, Y4>,
                Y3>, Y2>, Y1>, Y0>, X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4, Y5,
                Y6, Y7);
        
        //---------------------
        // 0b1XXXXXX < 0b1YYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>,
                X0>, UInt<UInt<UInt<UInt<UInt <UInt<UInt<UInt<UTerm, B1>, Y6>, Y5>, Y4>, Y3>,
                Y2>, Y1>, Y0>, X0, X1, X2, X3, X4, X5, Y0, Y1, Y2, Y3, Y4, Y5, Y6);
        // 0b1XXXXXX < 0b1YYYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X5>, X4>, X3>, X2>, X1>,
                X0>, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y7>, Y6>, Y5>,
                Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1, X2, X3, X4, X5, Y0, Y1, Y2, Y3,
                Y4, Y5, Y6, Y7);
        
        //---------------------
        // 0b1XXXXXXX < 0b1YYYYYYYY
        $impl_mac!(UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, X6>, X5>, X4>, X3>,
                X2>, X1>, X0>, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, Y7>,
                Y6>, Y5>, Y4>, Y3>, Y2>, Y1>, Y0>, X0, X1, X2, X3, X4, X5, X6, Y0,
                Y1, Y2, Y3, Y4, Y5, Y6, Y7);
    }
}

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

        impl<T: VarLit, $( $gparams ),* >
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

        impl<T: VarLit, $( $gparams ),* >
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

fn test_xxx() {
    let ec = ExprCreator::new();
    let v1 = ExprNode::<isize, U167, false>::variable(ec.clone());
    let tv1 = ExprNode::<isize, U6, false>::try_from(v1).unwrap();
}
