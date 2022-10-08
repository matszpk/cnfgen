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
//! The module to generate CNF clauses from integer expressions.

use std::cell::RefCell;
use std::cmp;
use std::fmt::Debug;
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Mul, MulAssign,
    Neg, Not, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use std::rc::Rc;

use generic_array::*;

use crate::boolexpr::half_adder;
use crate::int_utils::*;
use crate::intexpr::IntError;
use crate::{impl_int_ipty, impl_int_upty};
use crate::{
    BitVal, BoolEqual, BoolExprNode, BoolImpl, ExprCreator, FullMul, IntEqual, IntExprNode, IntOrd,
    Literal, VarLit,
};

// ExprNode - main node
//
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprNode<T: VarLit + Debug, const SIGN: bool> {
    pub(super) creator: Rc<RefCell<ExprCreator<T>>>,
    pub(super) indexes: Vec<usize>,
}

impl<T, const SIGN: bool> ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub const SIGN: bool = SIGN;

    // Creates new variable as expression node.
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
        ExprNode { creator, indexes }
    }

    pub fn from_boolexprs(iter: impl IntoIterator<Item = BoolExprNode<T>>) -> Self {
        let mut creator = None;
        let indexes = iter
            .into_iter()
            .map(|x| {
                // check creator - whether this same
                if let Some(c) = creator.clone() {
                    assert_eq!(c, x.creator.clone());
                } else {
                    creator = Some(x.creator.clone());
                }
                x.index
            })
            .collect::<Vec<_>>();
        ExprNode {
            creator: creator.unwrap(),
            indexes,
        }
    }

    pub fn filled(
        creator: Rc<RefCell<ExprCreator<T>>>,
        n: usize,
        v: impl Into<Literal<T>>,
    ) -> Self {
        ExprNode {
            creator: creator.clone(),
            indexes: vec![creator.borrow_mut().single(v); n],
        }
    }

    pub fn filled_expr(n: usize, v: BoolExprNode<T>) -> Self {
        ExprNode {
            creator: v.creator.clone(),
            indexes: vec![v.index; n],
        }
    }

    pub fn as_unsigned(self) -> ExprNode<T, false> {
        ExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }

    pub fn as_signed(self) -> ExprNode<T, true> {
        ExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.indexes.len()
    }
}

impl<T> ExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn subvalue(&self, start: usize, n: usize) -> Self {
        ExprNode {
            creator: self.creator.clone(),
            indexes: Vec::from(&self.indexes[start..start + n]),
        }
    }

    pub fn select_bits(&self, iter: impl IntoIterator<Item = usize>) -> Self {
        ExprNode {
            creator: self.creator.clone(),
            indexes: iter
                .into_iter()
                .map(|x| self.indexes[x])
                .collect::<Vec<_>>(),
        }
    }

    pub fn concat(self, rest: Self) -> Self {
        assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rest.creator));
        ExprNode {
            creator: self.creator.clone(),
            indexes: self
                .indexes
                .into_iter()
                .chain(rest.indexes.into_iter())
                .collect::<Vec<_>>(),
        }
    }

    pub fn split(self, k: usize) -> (Self, Self) {
        (
            ExprNode {
                creator: self.creator.clone(),
                indexes: Vec::from(&self.indexes[0..k]),
            },
            ExprNode {
                creator: self.creator.clone(),
                indexes: Vec::from(&self.indexes[k..]),
            },
        )
    }
}

pub trait TryFromNSized<T>: Sized {
    type Error;

    fn try_from_n(input: T, n: usize) -> Result<Self, Self::Error>;
}

impl<T: VarLit> TryFromNSized<ExprNode<T, false>> for ExprNode<T, false> {
    type Error = IntError;

    fn try_from_n(input: ExprNode<T, false>, n: usize) -> Result<Self, IntError> {
        if n < input.indexes.len() {
            if !input.indexes.iter().skip(n).all(|x| *x == 0) {
                return Err(IntError::BitOverflow);
            }
            Ok(ExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            let mut indexes = Vec::from(input.indexes.as_slice());
            indexes.resize(n, 0);
            Ok(ExprNode {
                creator: input.creator,
                indexes,
            })
        }
    }
}

impl<T: VarLit> TryFromNSized<ExprNode<T, true>> for ExprNode<T, false> {
    type Error = IntError;

    fn try_from_n(input: ExprNode<T, true>, n: usize) -> Result<Self, IntError> {
        if n < input.indexes.len() {
            if !input.indexes.iter().skip(n).all(|x| *x == 0) {
                return Err(IntError::BitOverflow);
            }
            Ok(ExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            if *input.indexes.last().unwrap() != 0 {
                return Err(IntError::CanBeNegative);
            }
            let mut indexes = Vec::from(input.indexes.as_slice());
            indexes.resize(n, 0);
            Ok(ExprNode {
                creator: input.creator,
                indexes,
            })
        }
    }
}

impl<T: VarLit> TryFromNSized<ExprNode<T, false>> for ExprNode<T, true> {
    type Error = IntError;

    fn try_from_n(input: ExprNode<T, false>, n: usize) -> Result<Self, IntError> {
        if n < input.indexes.len() {
            if !input.indexes.iter().skip(n).all(|x| *x == 0) {
                return Err(IntError::BitOverflow);
            }
            Ok(ExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            if *input.indexes.last().unwrap() != 0 {
                return Err(IntError::BitOverflow);
            }
            let mut indexes = Vec::from(input.indexes.as_slice());
            indexes.resize(n, 0);
            Ok(ExprNode {
                creator: input.creator,
                indexes,
            })
        }
    }
}

impl<T: VarLit> TryFromNSized<ExprNode<T, true>> for ExprNode<T, true> {
    type Error = IntError;

    fn try_from_n(input: ExprNode<T, true>, n: usize) -> Result<Self, IntError> {
        let last = *input.indexes.last().unwrap();
        if n < input.indexes.len() {
            if !input.indexes.iter().skip(n).all(|x| *x == last) {
                return Err(IntError::BitOverflow);
            }
            Ok(ExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            let mut indexes = Vec::from(input.indexes.as_slice());
            indexes.resize(n, last);
            Ok(ExprNode {
                creator: input.creator,
                indexes,
            })
        }
    }
}

impl<T, N, const SIGN: bool> From<IntExprNode<T, N, SIGN>> for ExprNode<T, SIGN>
where
    T: VarLit,
    N: ArrayLength<usize>,
{
    fn from(v: IntExprNode<T, N, SIGN>) -> Self {
        ExprNode {
            creator: v.creator,
            indexes: Vec::from(v.indexes.as_slice()),
        }
    }
}

trait TryIntConstant<T: VarLit, U>: Sized {
    fn try_constant(creator: Rc<RefCell<ExprCreator<T>>>, v: U, n: usize)
        -> Result<Self, IntError>;
}

macro_rules! impl_int_try_uconstant {
    ($pty:ty) => {
        impl<T: VarLit> TryIntConstant<T, $pty> for ExprNode<T, false> {
            fn try_constant(
                creator: Rc<RefCell<ExprCreator<T>>>,
                v: $pty,
                n: usize,
            ) -> Result<Self, IntError> {
                let bits = <$pty>::BITS as usize;
                if n < bits && (v & ((1 << (bits - n) - 1) << n)) != 0 {
                    return Err(IntError::BitOverflow);
                }
                Ok(ExprNode {
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

impl_int_upty!(impl_int_try_uconstant);

macro_rules! impl_int_try_iconstant {
    ($pty:ty) => {
        impl<T: VarLit> TryIntConstant<T, $pty> for ExprNode<T, true> {
            fn try_constant(
                creator: Rc<RefCell<ExprCreator<T>>>,
                v: $pty,
                n: usize,
            ) -> Result<Self, IntError> {
                let bits = <$pty>::BITS as usize;
                let mask = ((1 << (bits - n) - 1) << n);
                let signmask = if v < 0 { mask } else { 0 };
                if n < bits && (v & mask) != signmask {
                    return Err(IntError::BitOverflow);
                }
                Ok(ExprNode {
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

impl_int_ipty!(impl_int_try_iconstant);

impl<'a, T, const SIGN: bool> BitVal for &'a ExprNode<T, SIGN>
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

impl<T, const SIGN: bool> IntEqual for ExprNode<T, SIGN>
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

impl<T> IntOrd for ExprNode<T, false>
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

impl<T> IntOrd for ExprNode<T, true>
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
            | (lhs_sign.clone().bequal(rhs_sign) & lhs_num.less_than(rhs_num))
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
            | (lhs_sign.clone().bequal(rhs_sign) & lhs_num.less_equal(rhs_num))
    }

    fn greater_than(self, rhs: Self) -> Self::Output {
        rhs.less_than(self)
    }

    fn greater_equal(self, rhs: Self) -> Self::Output {
        rhs.less_equal(self)
    }
}

macro_rules! impl_dynint_bitop {
    ($trait:ident, $op:ident) => {
        impl<T, const SIGN: bool> $trait for ExprNode<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = Self;

            fn $op(self, rhs: Self) -> Self::Output {
                assert_eq!(self.indexes.len(), rhs.indexes.len());
                ExprNode {
                    creator: self.creator.clone(),
                    indexes: (0..self.indexes.len())
                        .into_iter()
                        .map(|x| (self.bit(x).$op(rhs.bit(x))).index)
                        .collect::<Vec<_>>(),
                }
            }
        }
    };
}

impl_dynint_bitop!(BitAnd, bitand);
impl_dynint_bitop!(BitOr, bitor);
impl_dynint_bitop!(BitXor, bitxor);

macro_rules! impl_dynint_bitop_assign {
    ($trait:ident, $op:ident, $op_assign:ident) => {
        impl<T, const SIGN: bool> $trait for ExprNode<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $op_assign(&mut self, rhs: Self) {
                *self = self.clone().$op(rhs);
            }
        }
    };
}

impl_dynint_bitop_assign!(BitAndAssign, bitand, bitand_assign);
impl_dynint_bitop_assign!(BitOrAssign, bitor, bitor_assign);
impl_dynint_bitop_assign!(BitXorAssign, bitxor, bitxor_assign);

/// Not trait implementation.
impl<T, const SIGN: bool> Not for ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn not(self) -> Self {
        ExprNode {
            creator: self.creator.clone(),
            indexes: (0..self.indexes.len())
                .into_iter()
                .map(|x| (!self.bit(x)).index)
                .collect::<Vec<_>>(),
        }
    }
}

// shift operations

impl<T, const SIGN: bool, const SIGN2: bool> Shl<ExprNode<T, SIGN2>> for ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn shl(self, rhs: ExprNode<T, SIGN2>) -> Self::Output {
        let n = self.indexes.len();
        let n2 = rhs.indexes.len();
        let nbits = calc_log_bits(n);
        // check whether zeroes in sign and in unused bits in Rhs
        if (SIGN2 && *rhs.indexes.last().unwrap() != 0)
            || !rhs.indexes.iter().skip(nbits).all(|x| *x == 0)
        {
            panic!("this arithmetic operation will overflow");
        }
        let nbits = cmp::min(nbits, n2 - usize::from(SIGN2));

        let mut input = ExprNode {
            creator: self.creator.clone(),
            indexes: vec![0; n],
        };
        let mut output = self.clone();
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_left(&mut output.indexes, &input, rhs.bit(i), i);
        }
        output
    }
}

macro_rules! impl_dynint_shl_imm {
    ($ty:ty) => {
        impl<T, const SIGN: bool> Shl<$ty> for ExprNode<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = Self;

            fn shl(self, rhs: $ty) -> Self::Output {
                // check whether zeroes
                let n = self.indexes.len();
                #[allow(unused_comparisons)]
                if rhs < 0 || (rhs as usize) >= n {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                let mut output = vec![0; n];
                output[usize_rhs..].copy_from_slice(&self.indexes[0..(n - usize_rhs)]);
                ExprNode {
                    creator: self.creator.clone(),
                    indexes: output,
                }
            }
        }
    };
}

impl_int_upty!(impl_dynint_shl_imm);
impl_int_ipty!(impl_dynint_shl_imm);

/// Shift right implementation.
impl<T, const SIGN: bool, const SIGN2: bool> Shr<ExprNode<T, SIGN2>> for ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn shr(self, rhs: ExprNode<T, SIGN2>) -> Self::Output {
        let n = self.indexes.len();
        let n2 = rhs.indexes.len();
        let nbits = calc_log_bits(n);
        // check whether zeroes in sign and in unused bits in Rhs
        if (SIGN2 && *rhs.indexes.last().unwrap() != 0)
            || !rhs.indexes.iter().skip(nbits).all(|x| *x == 0)
        {
            panic!("this arithmetic operation will overflow");
        }
        let nbits = cmp::min(nbits, n2 - usize::from(SIGN2));

        let mut input = ExprNode {
            creator: self.creator.clone(),
            indexes: vec![0; n],
        };
        let mut output = self.clone();
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_right(&mut output.indexes, &input, rhs.bit(i), i, SIGN);
        }
        output
    }
}

macro_rules! impl_dynint_shr_imm {
    ($ty:ty) => {
        impl<T, const SIGN: bool> Shr<$ty> for ExprNode<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = Self;

            fn shr(self, rhs: $ty) -> Self::Output {
                let n = self.indexes.len();
                // check whether zeroes
                #[allow(unused_comparisons)]
                if rhs < 0 || (rhs as usize) >= n {
                    panic!("this arithmetic operation will overflow");
                }
                let usize_rhs = rhs as usize;
                let mut output = vec![
                    if SIGN {
                        *self.indexes.last().unwrap()
                    } else {
                        0
                    };
                    n
                ];
                output[0..(n - usize_rhs)].copy_from_slice(&self.indexes[usize_rhs..]);
                ExprNode {
                    creator: self.creator.clone(),
                    indexes: output,
                }
            }
        }
    };
}

impl_int_upty!(impl_dynint_shr_imm);
impl_int_ipty!(impl_dynint_shr_imm);

// ShlAssign
macro_rules! impl_dynint_shx_assign {
    ($trait:ident, $op:ident, $op_assign:ident, $macro:ident) => {
        impl<T, const SIGN: bool, const SIGN2: bool> $trait<ExprNode<T, SIGN2>>
            for ExprNode<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $op_assign(&mut self, rhs: ExprNode<T, SIGN2>) {
                *self = self.clone().$op(rhs)
            }
        }

        macro_rules! $macro {
            ($ty:ty) => {
                impl<T, const SIGN: bool> $trait<$ty> for ExprNode<T, SIGN>
                where
                    T: VarLit + Neg<Output = T> + Debug,
                    isize: TryFrom<T>,
                    <T as TryInto<usize>>::Error: Debug,
                    <T as TryFrom<usize>>::Error: Debug,
                    <isize as TryFrom<T>>::Error: Debug,
                {
                    fn $op_assign(&mut self, rhs: $ty) {
                        *self = self.clone().$op(rhs)
                    }
                }
            };
        }

        impl_int_upty!($macro);
        impl_int_ipty!($macro);
    };
}

impl_dynint_shx_assign!(ShlAssign, shl, shl_assign, impl_dynint_shl_assign_imm);
impl_dynint_shx_assign!(ShrAssign, shr, shr_assign, impl_dynint_shr_assign_imm);

/// Returns result of the If-Then-Else (ITE) - integer version.
pub fn dynint_ite<T, const SIGN: bool>(
    c: BoolExprNode<T>,
    t: ExprNode<T, SIGN>,
    e: ExprNode<T, SIGN>,
) -> ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    (ExprNode::<T, SIGN>::filled_expr(t.len(), c.clone()) & t.clone())
        | (ExprNode::<T, SIGN>::filled_expr(t.len(), !c) & e)
}

// absolute value

impl<T> ExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn abs(self) -> ExprNode<T, false> {
        // if sign then -self else self
        dynint_ite(self.bit(self.indexes.len() - 1), -self.clone(), self).as_unsigned()
    }
}

//////////
// Add/Sub implementation

impl<T, const SIGN: bool> ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn addc_with_carry(self, rhs: Self, in_carry: BoolExprNode<T>) -> (Self, BoolExprNode<T>) {
        let mut output = vec![0; self.indexes.len()];
        let c = helper_addc_cout(&mut output, &self, &rhs, in_carry);
        (
            ExprNode {
                creator: self.creator,
                indexes: output,
            },
            c,
        )
    }

    pub fn addc(self, rhs: Self, in_carry: BoolExprNode<T>) -> Self {
        let mut output = vec![0; self.indexes.len()];
        helper_addc(&mut output, &self, &rhs, in_carry);
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }

    pub fn subc(self, rhs: Self, in_carry: BoolExprNode<T>) -> Self {
        let mut output = vec![0; self.indexes.len()];
        helper_subc(&mut output, &self, &rhs, in_carry);
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }

    pub fn add_same_carry(self, in_carry: BoolExprNode<T>) -> Self {
        let n = self.indexes.len();
        let mut output = vec![0; n];
        let mut c = in_carry;
        for i in 0..(n - 1) {
            (output[i], c) = {
                let (s0, c0) = half_adder(self.bit(i), c);
                (s0.index, c0)
            };
        }
        output[n - 1] = (self.bit(n - 1) ^ c).index;
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl<T, const SIGN: bool> Add<ExprNode<T, SIGN>> for ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut output = vec![0; self.indexes.len()];
        helper_addc(
            &mut output,
            &self,
            &rhs,
            BoolExprNode::single_value(self.creator.clone(), false),
        );
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl<T, const SIGN: bool> Sub<ExprNode<T, SIGN>> for ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut output = vec![0; self.indexes.len()];
        helper_subc(
            &mut output,
            &self,
            &rhs,
            BoolExprNode::single_value(self.creator.clone(), true),
        );
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl_dynint_bitop_assign!(AddAssign, add, add_assign);
impl_dynint_bitop_assign!(SubAssign, sub, sub_assign);

// Neg impl

impl<T> Neg for ExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        let trueval = BoolExprNode::new(self.creator.clone(), 1);
        (!self).add_same_carry(trueval)
    }
}

/// Most advanced: multiplication.

impl<T, const SIGN: bool> Mul<ExprNode<T, SIGN>> for ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut matrix = gen_dadda_matrix(
            self.creator.clone(),
            &self.indexes,
            &rhs.indexes,
            self.indexes.len(),
        );
        let res = gen_dadda_mult(self.creator.clone(), &mut matrix);
        ExprNode {
            creator: self.creator,
            indexes: res,
        }
    }
}

impl_dynint_bitop_assign!(MulAssign, mul, mul_assign);

/// Full multiplication

impl<T> FullMul<ExprNode<T, false>> for ExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = ExprNode<T, false>;

    fn fullmul(self, rhs: Self) -> Self::Output {
        let mut matrix = gen_dadda_matrix(
            self.creator.clone(),
            &self.indexes,
            &rhs.indexes,
            2 * self.indexes.len(),
        );
        let res = gen_dadda_mult(self.creator.clone(), &mut matrix);
        ExprNode {
            creator: self.creator,
            indexes: res,
        }
    }
}
