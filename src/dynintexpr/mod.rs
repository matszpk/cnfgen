// dynintexpr.rs - dynamic integer expression structures.
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
//! The module to generate CNF clauses from dynamic integer expressions.
//!
//! This module contains traits and main structure to operate on integer expressions:
//! `DynIntExprNode`. It is similar to IntExprNode, but have some specific features.
//! Size of integer can be defined dynamically at runtime. This type can be used while
//! writing generators which generates formulae from source in higher-level language likes
//! CVC4.
//!
//! Two generic parameters determines type of IntExprNode.
//! The first T parameter is just variable literal type - it can be omitted.
//! The second parameter is sign - true if signed integer or false if unsigned integer.
//! Type of DynIntExprNode can be written in form: `DynIntExprNode<i32, false>` -
//! DynIntExprNode for unsigned integer with 32-bit variable literals.
//! You can use `IDynExprNode` or `UDynExprNode` to omit second parameter.
//!
//! Operations on this expression node are similar to operations that can be done on
//! IntExprNode, except integer constant that can't be joined with DynIntExprNode.
//! However, it is possible conversion from integer into DynIntExprNode thanks
//! `TryIntConstantN` trait that provides method to that conversion.
//!
//! The simple example of usage:
//! ```
//! use cnfgen::boolexpr::*;
//! use cnfgen::dynintexpr::*;
//! use cnfgen::writer::{CNFError, CNFWriter};
//! use std::io;
//! fn write_diophantine_equation() -> Result<(), CNFError> {
//!     // define ExprCreator.
//!     let creator = ExprCreator32::new();
//!     // define variables - signed 200-bit wide.
//!     let x = IDynExprNode::variable(creator.clone(), 200);
//!     let y = IDynExprNode::variable(creator.clone(), 200);
//!     let z = IDynExprNode::variable(creator.clone(), 200);
//!     // define equation: x^2 + y^2 - 77*z^2 = 0
//!     let powx = x.clone().fullmul(x);  // x^2
//!     let powy = y.clone().fullmul(y);  // y^2
//!     let powz = z.clone().fullmul(z);  // z^2
//!     let v77 = IDynExprNode::try_constant_n(creator.clone(), 400, 77).unwrap();
//!     // We use cond_mul to get product and required condition to avoid overflow.
//!     let (prod, cond0) = powz.cond_mul(v77);
//!     // Similary, we use conditional addition and conditional subtraction.
//!     let (sum1, cond1) = powx.cond_add(powy);
//!     let (diff2, cond2) = sum1.cond_sub(prod);
//!     // define final formulae with required conditions.
//!     let zero = IDynExprNode::try_constant_n(creator.clone(), 400, 0).unwrap();
//!     let formulae: BoolExprNode<_> = diff2.equal(zero) & cond0 & cond1 & cond2;
//!     // write CNF to stdout.
//!     formulae.write(&mut CNFWriter::new(io::stdout()))
//! }
//! ```
//!
//! Look up module `intexpr` to figure out about possible operations.
//!
//! ## Conversion between types.
//!
//! It is possible conversion between various DynIntExprNodes that have various sizes and signs.
//! Conversions are implemented by using `TryFromNSized` traits which define
//! a method 'try_from_n` where argument `n` defines bits of destination.

use std::cell::RefCell;
use std::fmt::Debug;
use std::ops::Neg;
use std::rc::Rc;

use generic_array::*;

use crate::boolexpr::{bool_ite, half_adder, BoolEqual, BoolExprNode, BoolImpl};
pub use crate::boolexpr_creator::{ExprCreator, ExprCreator32, ExprCreatorSys};
use crate::int_utils::*;
pub use crate::intexpr::{
    BitVal, DivMod, ExtraOps, FullMul, IntCondAdd, IntCondMul, IntCondNeg, IntCondShl, IntCondShr,
    IntCondSub, IntEqual, IntError, IntExprNode, IntModAdd, IntModAddAssign, IntModMul,
    IntModMulAssign, IntModNeg, IntModSub, IntModSubAssign, IntOrd, IntRol, IntRor,
};
use crate::writer::{Literal, VarLit};
use crate::{impl_int_ipty, impl_int_upty};

pub mod arith;
pub use arith::*;

pub mod extra_arith;
pub use extra_arith::*;

/// The main structure that represents dynamic integer expression, subexpression or integer value.
///
/// It joined with the ExprCreator that holds all expressions.
/// Creation of new expression is naturally simple thanks operators. However, expression nodes
/// must be cloned before using in other expressions if they will be used more than once.
/// Simple examples:
///
/// * `(x1 << x2).mod_add(x3.clone()).equal(x3)`
/// * `x1.clone().fullmul(x1).mod_add(x2.clone().fullmul(x2))`
///
/// The size of DynIntExprNode can be determined at runtime.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DynIntExprNode<T: VarLit + Debug, const SIGN: bool> {
    pub(super) creator: Rc<RefCell<ExprCreator<T>>>,
    pub(super) indexes: Vec<usize>,
}

impl<T, const SIGN: bool> DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// SIGN of integer. It can be false - unsigned, or true - signed.
    pub const SIGN: bool = SIGN;

    /// Creates new variable as expression node. `n` is number of bits.
    pub fn variable(creator: Rc<RefCell<ExprCreator<T>>>, n: usize) -> Self {
        let indexes = {
            let mut creator = creator.borrow_mut();
            (0..n)
                .into_iter()
                .map(|_| {
                    let l = creator.new_variable();
                    creator.single(l)
                })
                .collect::<Vec<_>>()
        };
        DynIntExprNode { creator, indexes }
    }

    /// Creates integer from boolean expressions. An argument is object convertible into
    /// iterator of `BoolExprNode`.
    pub fn from_boolexprs(iter: impl IntoIterator<Item = BoolExprNode<T>>) -> Self {
        let mut creator = None;
        let indexes = iter
            .into_iter()
            .map(|x| {
                // check creator - whether this same
                if let Some(c) = creator.clone() {
                    assert_eq!(Rc::as_ptr(&c), Rc::as_ptr(&x.creator));
                } else {
                    creator = Some(x.creator.clone());
                }
                x.index
            })
            .collect::<Vec<_>>();
        DynIntExprNode {
            creator: creator.unwrap(),
            indexes,
        }
    }

    /// Creates filled integer from from Literal. `n` is number of bits.
    pub fn filled(
        creator: Rc<RefCell<ExprCreator<T>>>,
        n: usize,
        v: impl Into<Literal<T>>,
    ) -> Self {
        DynIntExprNode {
            creator: creator.clone(),
            indexes: vec![creator.borrow_mut().single(v); n],
        }
    }

    /// Creates filled integer from from a boolean value. `n` is number of bits.
    pub fn filled_expr(n: usize, v: BoolExprNode<T>) -> Self {
        DynIntExprNode {
            creator: v.creator.clone(),
            indexes: vec![v.index; n],
        }
    }

    /// Casts integer into unsigned integer.
    pub fn as_unsigned(self) -> DynIntExprNode<T, false> {
        DynIntExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }

    /// Casts integer into signed integer.
    pub fn as_signed(self) -> DynIntExprNode<T, true> {
        DynIntExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }

    /// Returns length - number of bits.
    #[inline]
    pub fn len(&self) -> usize {
        self.indexes.len()
    }

    /// Returns true if length is zero - number of bits is zero.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.indexes.is_empty()
    }
}

impl<T> DynIntExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer that contains `n` bits starting from `start`.
    pub fn subvalue(&self, start: usize, n: usize) -> Self {
        DynIntExprNode {
            creator: self.creator.clone(),
            indexes: Vec::from(&self.indexes[start..start + n]),
        }
    }

    /// Creates integer that contains selected bits. List of bits given in
    /// object that can be converted into iterator of indexes.
    pub fn select_bits(&self, iter: impl IntoIterator<Item = usize>) -> Self {
        DynIntExprNode {
            creator: self.creator.clone(),
            indexes: iter
                .into_iter()
                .map(|x| self.indexes[x])
                .collect::<Vec<_>>(),
        }
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn concat(self, rest: Self) -> Self {
        assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rest.creator));
        DynIntExprNode {
            creator: self.creator.clone(),
            indexes: self
                .indexes
                .into_iter()
                .chain(rest.indexes.into_iter())
                .collect::<Vec<_>>(),
        }
    }

    /// Splits integer into two parts: the first with `k` bits and second with rest of bits.
    pub fn split(self, k: usize) -> (Self, Self) {
        (
            DynIntExprNode {
                creator: self.creator.clone(),
                indexes: Vec::from(&self.indexes[0..k]),
            },
            DynIntExprNode {
                creator: self.creator.clone(),
                indexes: Vec::from(&self.indexes[k..]),
            },
        )
    }
}

/// Trait to convert DynDynIntExprNode to other DynDynIntExprNode with different number of bits.
pub trait TryFromNSized<T>: Sized {
    type Error;

    /// Try to convert from input. `n` is number of bits of destination. It returns
    /// `Ok(dest)` if conversion can be done, otherwise it returns error.
    fn try_from_n(input: T, n: usize) -> Result<Self, Self::Error>;
}

impl<T: VarLit> TryFromNSized<DynIntExprNode<T, false>> for DynIntExprNode<T, false> {
    type Error = IntError;

    fn try_from_n(input: DynIntExprNode<T, false>, n: usize) -> Result<Self, IntError> {
        if n < input.indexes.len() {
            if !input.indexes.iter().skip(n).all(|x| *x == 0) {
                return Err(IntError::BitOverflow);
            }
            Ok(DynIntExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            let mut indexes = Vec::from(input.indexes.as_slice());
            indexes.resize(n, 0);
            Ok(DynIntExprNode {
                creator: input.creator,
                indexes,
            })
        }
    }
}

impl<T: VarLit> TryFromNSized<DynIntExprNode<T, true>> for DynIntExprNode<T, false> {
    type Error = IntError;

    fn try_from_n(input: DynIntExprNode<T, true>, n: usize) -> Result<Self, IntError> {
        if n < input.indexes.len() {
            if !input.indexes.iter().skip(n).all(|x| *x == 0) {
                return Err(IntError::BitOverflow);
            }
            Ok(DynIntExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            if *input.indexes.last().unwrap() != 0 {
                return Err(IntError::CanBeNegative);
            }
            let mut indexes = Vec::from(input.indexes.as_slice());
            indexes.resize(n, 0);
            Ok(DynIntExprNode {
                creator: input.creator,
                indexes,
            })
        }
    }
}

impl<T: VarLit> TryFromNSized<DynIntExprNode<T, false>> for DynIntExprNode<T, true> {
    type Error = IntError;

    fn try_from_n(input: DynIntExprNode<T, false>, n: usize) -> Result<Self, IntError> {
        if n <= input.indexes.len() {
            if !input.indexes.iter().skip(n - 1).all(|x| *x == 0) {
                return Err(IntError::BitOverflow);
            }
            Ok(DynIntExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            let mut indexes = Vec::from(input.indexes.as_slice());
            indexes.resize(n, 0);
            Ok(DynIntExprNode {
                creator: input.creator,
                indexes,
            })
        }
    }
}

impl<T: VarLit> TryFromNSized<DynIntExprNode<T, true>> for DynIntExprNode<T, true> {
    type Error = IntError;

    fn try_from_n(input: DynIntExprNode<T, true>, n: usize) -> Result<Self, IntError> {
        if n < input.indexes.len() {
            let last_idx = input.indexes[n - 1];
            if !input.indexes.iter().skip(n).all(|x| last_idx == *x) {
                return Err(IntError::BitOverflow);
            }
            Ok(DynIntExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            let last = *input.indexes.last().unwrap();
            let mut indexes = Vec::from(input.indexes.as_slice());
            indexes.resize(n, last);
            Ok(DynIntExprNode {
                creator: input.creator,
                indexes,
            })
        }
    }
}

impl<T, N, const SIGN: bool> From<IntExprNode<T, N, SIGN>> for DynIntExprNode<T, SIGN>
where
    T: VarLit,
    N: ArrayLength<usize>,
{
    fn from(v: IntExprNode<T, N, SIGN>) -> Self {
        DynIntExprNode {
            creator: v.creator,
            indexes: Vec::from(v.indexes.as_slice()),
        }
    }
}

/// Trait to convert primitive integer into object (`DynIntExprNode`).
/// It returns `Ok(result)` if integer will be match to size given in `n`.
pub trait TryIntConstantN<T: VarLit, U>: Sized {
    /// Try to perform conversion into expression node. `n` is number of bits of destination.
    /// `v` is constant value to convert.
    fn try_constant_n(
        creator: Rc<RefCell<ExprCreator<T>>>,
        n: usize,
        v: U,
    ) -> Result<Self, IntError>;
}

macro_rules! impl_int_try_uconstant_n {
    ($pty:ty) => {
        impl<T: VarLit> TryIntConstantN<T, $pty> for DynIntExprNode<T, false> {
            fn try_constant_n(
                creator: Rc<RefCell<ExprCreator<T>>>,
                n: usize,
                v: $pty,
            ) -> Result<Self, IntError> {
                let bits = <$pty>::BITS as usize;
                // for n < bits, check whether highest bits are zero.
                if n < bits && (v & ((((1 as $pty) << (bits - n)).overflowing_sub(1).0) << n)) != 0
                {
                    return Err(IntError::BitOverflow);
                }
                Ok(DynIntExprNode {
                    creator,
                    indexes: (0..n)
                        .into_iter()
                        .map(|x| {
                            // return 1 - true node index, 0 - false node index
                            if x < bits {
                                usize::from((v & (1 << x)) != 0)
                            } else {
                                0
                            }
                        })
                        .collect::<Vec<_>>(),
                })
            }
        }
    };
}

impl_int_upty!(impl_int_try_uconstant_n);

macro_rules! impl_int_try_iconstant_n {
    ($pty:ty) => {
        impl<T: VarLit> TryIntConstantN<T, $pty> for DynIntExprNode<T, true> {
            fn try_constant_n(
                creator: Rc<RefCell<ExprCreator<T>>>,
                n: usize,
                v: $pty,
            ) -> Result<Self, IntError> {
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
                Ok(DynIntExprNode {
                    creator,
                    indexes: (0..n)
                        .into_iter()
                        .map(|x| {
                            // return 1 - true node index, 0 - false node index
                            if x < bits {
                                usize::from((v & (1 << x)) != 0)
                            } else {
                                usize::from((v & (1 << ((<$pty>::BITS - 1) as usize))) != 0)
                            }
                        })
                        .collect::<Vec<_>>(),
                })
            }
        }
    };
}

impl_int_ipty!(impl_int_try_iconstant_n);

impl<'a, T, const SIGN: bool> BitVal for &'a DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bitnum(self) -> usize {
        self.indexes.len()
    }

    fn bit(self, x: usize) -> Self::Output {
        BoolExprNode::new(self.creator.clone(), self.indexes[x])
    }
}

// ///////////////////
// IntEqual

impl<T, const SIGN: bool> IntEqual for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut xp = BoolExprNode::single(self.creator.clone(), true);
        for i in 0..self.indexes.len() {
            xp &= self.bit(i).bequal(rhs.bit(i));
        }
        xp
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut xp = BoolExprNode::single(self.creator.clone(), false);
        for i in 0..self.indexes.len() {
            xp |= self.bit(i) ^ rhs.bit(i);
        }
        xp
    }
}

impl<T> IntOrd for DynIntExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn less_than(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut xp = (!self.bit(0)) & rhs.bit(0);
        for i in 1..self.indexes.len() {
            xp = (self.bit(i).bequal(rhs.bit(i)) & xp) | ((!self.bit(i)) & rhs.bit(i));
        }
        xp
    }

    fn less_equal(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
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

impl<T> IntOrd for DynIntExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn less_than(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let lhs_sign = self.bit(self.indexes.len() - 1);
        let rhs_sign = rhs.bit(self.indexes.len() - 1);
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
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let lhs_sign = self.bit(self.indexes.len() - 1);
        let rhs_sign = rhs.bit(self.indexes.len() - 1);
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

// types

/// DynIntExprNode for unsinged integer.
pub type UDynExprNode<T> = DynIntExprNode<T, false>;
/// DynIntExprNode for singed integer.
pub type IDynExprNode<T> = DynIntExprNode<T, true>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intexpr::IntExprNode;
    use generic_array::typenum::*;
    use std::iter;

    #[test]
    fn test_expr_node() {
        let ec = ExprCreator::new();
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 7);
        assert_eq!([2, 3, 4, 5, 6, 7, 8], *x1.indexes);
        assert_eq!([2, 3, 4, 5, 6, 7, 8], *(x1.clone().as_signed()).indexes);
        assert_eq!([2, 3, 4, 5, 6, 7, 8], *(x1.as_unsigned()).indexes);
        let x2 = DynIntExprNode::<isize, true>::variable(ec.clone(), 7);
        assert_eq!([9, 10, 11, 12, 13, 14, 15], *x2.indexes);
        assert_eq!(
            [9, 10, 11, 12, 13, 14, 15],
            *(x2.clone().as_unsigned()).indexes
        );
        assert_eq!([9, 10, 11, 12, 13, 14, 15], *(x2.as_signed()).indexes);

        let b1 = BoolExprNode::variable(ec.clone());
        let x3 = DynIntExprNode::<isize, false>::filled(ec.clone(), 4, b1.varlit().unwrap());
        assert_eq!([16, 16, 16, 16], *x3.indexes);
        let b1 = BoolExprNode::variable(ec.clone());
        let b2 = BoolExprNode::variable(ec.clone());
        let bxp = b1.clone() ^ b2.clone();
        let x4 = DynIntExprNode::<isize, false>::filled_expr(4, bxp.clone());
        assert_eq!(
            iter::repeat(bxp.index)
                .take(4)
                .collect::<Vec<_>>()
                .as_slice(),
            x4.indexes.as_slice()
        );

        //
        let b3 = BoolExprNode::variable(ec.clone());
        let b4 = BoolExprNode::variable(ec.clone());
        let bxps = [
            b1.clone() & b2.clone(),
            b1.clone() | b2.clone(),
            b1.clone() ^ b2.clone(),
            b1 | b2.clone() | b3.clone(),
            b3.clone() & b4.clone(),
            b3.clone() | b4.clone(),
            b3.clone() ^ b4.clone(),
            b2 | b3 | b4,
        ];

        let x5 = DynIntExprNode::<isize, false>::from_boolexprs(bxps.clone());
        assert_eq!(
            bxps.iter().map(|x| x.index).collect::<Vec<_>>().as_slice(),
            x5.indexes.as_slice()
        );
    }

    #[test]
    fn test_expr_node_manip() {
        let ec = ExprCreator::new();
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 16);
        let x2 = x1.subvalue(7, 6);
        assert_eq!([9, 10, 11, 12, 13, 14], *x2.indexes);
        let x3 = x1.select_bits([3, 8, 9, 0, 3, 4, 12, 14, 15]);
        assert_eq!([5, 10, 11, 2, 5, 6, 14, 16, 17], *x3.indexes);

        let y1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 8);
        let z1 = x1.clone().concat(y1.clone());
        assert_eq!(
            (2..(2 + 24)).into_iter().collect::<Vec<usize>>().as_slice(),
            z1.indexes.as_slice()
        );
        let z1 = y1.concat(x1);
        assert_eq!(
            ((2 + 16)..(2 + 24))
                .into_iter()
                .chain((2..18).into_iter())
                .collect::<Vec<usize>>()
                .as_slice(),
            z1.indexes.as_slice()
        );
        let (xt1, xt2) = z1.split(5);
        assert_eq!([18, 19, 20, 21, 22], *xt1.indexes);
        assert_eq!(
            ((2 + 16 + 5)..(2 + 24))
                .into_iter()
                .chain((2..18).into_iter())
                .collect::<Vec<usize>>()
                .as_slice(),
            xt2.indexes.as_slice()
        );
    }

    #[test]
    fn test_expr_node_from_int_expr_node() {
        let ec = ExprCreator::new();
        let ix1 = IntExprNode::<isize, U10, false>::variable(ec.clone());
        let dix1 = DynIntExprNode::<isize, false>::from(ix1.clone());
        assert_eq!(ix1.indexes.as_slice(), dix1.indexes.as_slice());
    }

    #[test]
    fn test_expr_node_try_from_n_uncond() {
        let ec = ExprCreator::new();
        // Unsigned N -> Unsigned N+X
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 8);
        let x2 = DynIntExprNode::<isize, false>::try_from_n(x1.clone(), 14).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0], *x2.indexes);
        // Unsigned N -> Signed N+X
        let ix2 = DynIntExprNode::<isize, true>::try_from_n(x1.clone(), 14).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0], *ix2.indexes);
        let ix1 = DynIntExprNode::<isize, true>::variable(ec.clone(), 8);
        // Signed N, where SIGN=var -> Signed N+X
        let ix2 = DynIntExprNode::<isize, true>::try_from_n(ix1.clone(), 12).unwrap();
        assert_eq!(
            [10, 11, 12, 13, 14, 15, 16, 17, 17, 17, 17, 17],
            *ix2.indexes
        );
    }

    #[test]
    fn test_expr_node_try_from_n() {
        let ec = ExprCreator::new();
        let ix1 = DynIntExprNode::<isize, true>::try_from_n(
            DynIntExprNode::<isize, false>::variable(ec.clone(), 7),
            8,
        )
        .unwrap();
        // Signed N, SIGN=0 -> Unsigned N
        let x1 = DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 8).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0], *x1.indexes);
        // Signed N, SIGN=0 -> Unsigned N+X
        let x2 = DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 9).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0, 0], *x2.indexes);
        let x2 = DynIntExprNode::<isize, false>::try_from_n(ix1, 10).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0, 0, 0], *x2.indexes);

        let ix1 = DynIntExprNode::<isize, true>::try_from_n(
            DynIntExprNode::<isize, true>::variable(ec.clone(), 7),
            8,
        )
        .unwrap();
        // Signed N, SIGN=var -> Unsigned N
        assert_eq!(
            Err("Value can be negative".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 8).map_err(|x| x.to_string())
        );
        // Signed N, SIGN=var -> Unsigned N+X
        assert_eq!(
            Err("Value can be negative".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 9).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Value can be negative".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ix1, 10).map_err(|x| x.to_string())
        );

        let x1 = DynIntExprNode::<isize, false>::try_from_n(
            DynIntExprNode::<isize, false>::variable(ec.clone(), 7),
            8,
        )
        .unwrap();
        // Unsigned N, LAST=0 -> Signed N
        let ix2 = DynIntExprNode::<isize, true>::try_from_n(x1.clone(), 8).unwrap();
        assert_eq!([16, 17, 18, 19, 20, 21, 22, 0], *ix2.indexes);
        // Unsigned N, LAST=0 -> Signed N+X
        let ix2 = DynIntExprNode::<isize, true>::try_from_n(x1.clone(), 9).unwrap();
        assert_eq!([16, 17, 18, 19, 20, 21, 22, 0, 0], *ix2.indexes);

        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 8);
        // Unsinged N, LAST=var -> Signed N+X
        let ix2 = DynIntExprNode::<isize, true>::try_from_n(x1.clone(), 9).unwrap();
        assert_eq!([23, 24, 25, 26, 27, 28, 29, 30, 0], *ix2.indexes);
        // Unsinged N, LAST=var -> Signed N
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, true>::try_from_n(x1.clone(), 8).map_err(|x| x.to_string())
        );

        //
        // V[N-X..] = 0, LASTS = 0
        let ux1 = DynIntExprNode::<isize, false>::try_from_n(
            DynIntExprNode::<isize, false>::variable(ec.clone(), 6),
            8,
        )
        .unwrap();
        // Unsigned N, LASTS=0 -> Unsigned N-X
        let x2 = DynIntExprNode::<isize, false>::try_from_n(ux1.clone(), 6).unwrap();
        assert_eq!([31, 32, 33, 34, 35, 36], *x2.indexes);
        // Unsigned N, LASTS=0, V[N-X-1]=var -> Unsigned N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ux1.clone(), 5).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ux1.clone(), 4).map_err(|x| x.to_string())
        );
        let ix2 = DynIntExprNode::<isize, true>::try_from_n(ux1.clone(), 7).unwrap();
        // Unsigned N, LASTS=0 -> Signed N-X+1
        assert_eq!([31, 32, 33, 34, 35, 36, 0], *ix2.indexes);
        // Unsigned N, LASTS=0 -> Signed N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, true>::try_from_n(ux1.clone(), 6).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, true>::try_from_n(ux1.clone(), 5).map_err(|x| x.to_string())
        );

        let ix1 = DynIntExprNode::<isize, true>::try_from_n(
            DynIntExprNode::<isize, false>::variable(ec.clone(), 6),
            8,
        )
        .unwrap();
        // Signed N, LASTS=0 -> Unsigned N-X
        let x2 = DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 6).unwrap();
        assert_eq!([37, 38, 39, 40, 41, 42], *x2.indexes);
        // Signed N, LASTS=0 -> Unsigned N-X-1
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );
        // Signed N, LASTS=0 -> Signed N-X+1
        let ix2 = DynIntExprNode::<isize, true>::try_from_n(ix1.clone(), 7).unwrap();
        assert_eq!([37, 38, 39, 40, 41, 42, 0], *ix2.indexes);
        // Signed N, LASTS=0 -> Signed N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, true>::try_from_n(ix1.clone(), 6).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, true>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );

        // constvar - this same var for all LASTS bits
        let ix1 = DynIntExprNode::<isize, true>::try_from_n(
            DynIntExprNode::<isize, true>::variable(ec.clone(), 6),
            8,
        )
        .unwrap();
        // Signed N, LASTS=constvar -> Unsigned N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 6).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );
        // Signed N, LASTS=constvar -> Unsigned N-X+1
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, false>::try_from_n(ix1.clone(), 7).map_err(|x| x.to_string())
        );
        let ix2 = DynIntExprNode::<isize, true>::try_from_n(ix1.clone(), 6).unwrap();
        // Signed N, LASTS=constvar -> Signed N-X
        assert_eq!([43, 44, 45, 46, 47, 48], *ix2.indexes);
        // Signed N, LASTS=constvar -> Signed N-X-1
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, true>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            DynIntExprNode::<isize, true>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );
    }

    #[test]
    fn test_expr_node_try_int_constant_n() {
        let ec = ExprCreator::new();
        let x1 =
            DynIntExprNode::<isize, false>::try_constant_n(ec.clone(), 9, 0b11011001u16).unwrap();
        assert_eq!([1, 0, 0, 1, 1, 0, 1, 1, 0], *x1.indexes);
        let x1 =
            DynIntExprNode::<isize, true>::try_constant_n(ec.clone(), 8, 0b00111001i16).unwrap();
        assert_eq!([1, 0, 0, 1, 1, 1, 0, 0], *x1.indexes);
        let x1 = DynIntExprNode::<isize, true>::try_constant_n(ec.clone(), 10, -15i8).unwrap();
        assert_eq!([1, 0, 0, 0, 1, 1, 1, 1, 1, 1], *x1.indexes);
        let x1 =
            DynIntExprNode::<isize, false>::try_constant_n(ec.clone(), 64, 1848549293434211u64)
                .unwrap();
        assert_eq!(
            (0..64)
                .into_iter()
                .map(|x| ((1848549293434211u64 >> x) & 1) as usize)
                .collect::<Vec<_>>()
                .as_slice(),
            x1.indexes.as_slice()
        );
        let x1 = DynIntExprNode::<isize, true>::try_constant_n(ec.clone(), 1, 0i64).unwrap();
        assert_eq!([0], *x1.indexes);
        for i in 4..16 {
            assert_eq!(
                Err("Bit overflow".to_string()),
                DynIntExprNode::<isize, false>::try_constant_n(ec.clone(), 4, 14u16 | (1u16 << i))
                    .map_err(|x| x.to_string())
            );
        }
        for i in 4..16 {
            assert_eq!(
                Err("Bit overflow".to_string()),
                DynIntExprNode::<isize, true>::try_constant_n(ec.clone(), 4, 6i16 | (1i16 << i))
                    .map_err(|x| x.to_string())
            );
        }
        for i in 4..16 {
            assert_eq!(
                Err("Bit overflow".to_string()),
                DynIntExprNode::<isize, true>::try_constant_n(ec.clone(), 4, (-6i16) ^ (1i16 << i))
                    .map_err(|x| x.to_string())
            );
        }
    }

    #[test]
    fn test_expr_node_bitval() {
        let ec = ExprCreator::new();
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 7);
        assert_eq!(x1.bit(2), BoolExprNode::single(ec.clone(), 3));
        assert_eq!(x1.bit(6), BoolExprNode::single(ec.clone(), 7));
        let x1 = DynIntExprNode::<isize, true>::variable(ec.clone(), 7);
        assert_eq!(x1.bit(3), BoolExprNode::single(ec.clone(), 11));
    }

    #[test]
    fn test_expr_node_int_equal() {
        let ec = ExprCreator::new();
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 5);
        let x2 = DynIntExprNode::<isize, false>::variable(ec.clone(), 5);
        let x3 = DynIntExprNode::<isize, false>::variable(ec.clone(), 5);
        let x4 = DynIntExprNode::<isize, false>::variable(ec.clone(), 5);
        let reseq = x1.equal(x2);
        let resne = x3.nequal(x4);

        let exp_ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U5, false>::variable(exp_ec.clone());
        let x2 = IntExprNode::<isize, U5, false>::variable(exp_ec.clone());
        let x3 = IntExprNode::<isize, U5, false>::variable(exp_ec.clone());
        let x4 = IntExprNode::<isize, U5, false>::variable(exp_ec.clone());
        let expeq = x1.equal(x2);
        let expne = x3.nequal(x4);

        assert_eq!(expeq, reseq);
        assert_eq!(expne, resne);
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    macro_rules! test_int_ord_macro {
        ($sign:expr) => {
            let ec = ExprCreator::new();
            let xv = (0..8)
                .into_iter()
                .map(|_| DynIntExprNode::<isize, $sign>::variable(ec.clone(), 5))
                .collect::<Vec<_>>();
            let reslt = xv[0].clone().less_than(xv[1].clone());
            let resle = xv[2].clone().less_equal(xv[3].clone());
            let resgt = xv[4].clone().greater_than(xv[5].clone());
            let resge = xv[6].clone().greater_equal(xv[7].clone());

            let exp_ec = ExprCreator::new();
            let xv = (0..8)
                .into_iter()
                .map(|_| IntExprNode::<isize, U5, $sign>::variable(exp_ec.clone()))
                .collect::<Vec<_>>();
            let explt = xv[0].clone().less_than(xv[1].clone());
            let exple = xv[2].clone().less_equal(xv[3].clone());
            let expgt = xv[4].clone().greater_than(xv[5].clone());
            let expge = xv[6].clone().greater_equal(xv[7].clone());

            assert_eq!(explt, reslt);
            assert_eq!(exple, resle);
            assert_eq!(expgt, resgt);
            assert_eq!(expge, resge);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_int_ord() {
        test_int_ord_macro!(false);
        test_int_ord_macro!(true);
    }
}
