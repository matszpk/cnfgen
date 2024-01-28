// arith.rs - dynamic integer arithmetic.
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

use std::cmp;
use std::fmt::Debug;
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, Neg, Not, Rem, Shl,
    ShlAssign, Shr, ShrAssign,
};

use super::*;

macro_rules! impl_dynint_bitop {
    ($trait:ident, $op:ident) => {
        impl<T, const SIGN: bool> $trait for DynIntExprNode<T, SIGN>
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
                DynIntExprNode {
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
        impl<T, const SIGN: bool> $trait for DynIntExprNode<T, SIGN>
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
impl<T, const SIGN: bool> Not for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn not(self) -> Self {
        DynIntExprNode {
            creator: self.creator.clone(),
            indexes: (0..self.indexes.len())
                .into_iter()
                .map(|x| (!self.bit(x)).index)
                .collect::<Vec<_>>(),
        }
    }
}

// shift operations

impl<T, const SIGN: bool, const SIGN2: bool> Shl<DynIntExprNode<T, SIGN2>>
    for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn shl(self, rhs: DynIntExprNode<T, SIGN2>) -> Self::Output {
        let n = self.indexes.len();
        let n2 = rhs.indexes.len();
        let nbits = calc_log_bits(n);
        // check whether zeroes in sign and in unused bits in Rhs
        if (SIGN2 && *rhs.indexes.last().unwrap() != 0)
            || !rhs.indexes.iter().skip(nbits).all(|x| *x == 0)
            || ((1 << nbits) != n && rhs.indexes[nbits - 1] != 0)
        {
            panic!("this arithmetic operation will overflow");
        }
        let nbits = cmp::min(nbits, n2 - usize::from(SIGN2));

        let mut input = DynIntExprNode {
            creator: self.creator.clone(),
            indexes: vec![0; n],
        };
        let mut output = self;
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_left(&mut output.indexes, &input, rhs.bit(i), i);
        }
        output
    }
}

/// Shift left implementation.
impl<T, const SIGN: bool> IntCondShl<DynIntExprNode<T, false>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_shl(self, rhs: DynIntExprNode<T, false>) -> (Self::Output, Self::OutputCond) {
        let n = self.indexes.len();
        let n2 = rhs.indexes.len();
        let nbits = calc_log_bits(n);
        let nbits = cmp::min(nbits, n2);

        let mut input = DynIntExprNode {
            creator: self.creator.clone(),
            indexes: vec![0; n],
        };
        let mut output = self.clone();
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_left(&mut output.indexes, &input, rhs.bit(i), i);
        }
        let nexpr = DynIntExprNode::<T, false>::try_constant_n(self.creator, n2, n - 1).unwrap();
        (output, rhs.less_equal(nexpr))
    }
}

impl<T, const SIGN: bool> IntCondShl<DynIntExprNode<T, true>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_shl(self, rhs: DynIntExprNode<T, true>) -> (Self::Output, Self::OutputCond) {
        let n = self.indexes.len();
        let n2 = rhs.indexes.len();
        let nbits = calc_log_bits(n);
        let nbits = cmp::min(nbits, n2 - 1);

        let mut input = DynIntExprNode {
            creator: self.creator.clone(),
            indexes: vec![0; n],
        };
        let mut output = self.clone();
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_left(&mut output.indexes, &input, rhs.bit(i), i);
        }
        let nexpr =
            DynIntExprNode::<T, true>::try_constant_n(self.creator, n2, (n - 1) as isize).unwrap();
        (output, (!rhs.bit(n2 - 1)) & rhs.less_equal(nexpr))
    }
}

macro_rules! impl_dynint_shl_imm {
    ($ty:ty) => {
        impl<T, const SIGN: bool> Shl<$ty> for DynIntExprNode<T, SIGN>
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
                DynIntExprNode {
                    creator: self.creator,
                    indexes: output,
                }
            }
        }
    };
}

impl_int_upty!(impl_dynint_shl_imm);
impl_int_ipty!(impl_dynint_shl_imm);

/// Shift right implementation.
impl<T, const SIGN: bool, const SIGN2: bool> Shr<DynIntExprNode<T, SIGN2>>
    for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn shr(self, rhs: DynIntExprNode<T, SIGN2>) -> Self::Output {
        let n = self.indexes.len();
        let n2 = rhs.indexes.len();
        let nbits = calc_log_bits(n);
        // check whether zeroes in sign and in unused bits in Rhs
        if (SIGN2 && *rhs.indexes.last().unwrap() != 0)
            || !rhs.indexes.iter().skip(nbits).all(|x| *x == 0)
            || ((1 << nbits) != n && rhs.indexes[nbits - 1] != 0)
        {
            panic!("this arithmetic operation will overflow");
        }
        let nbits = cmp::min(nbits, n2 - usize::from(SIGN2));

        let mut input = DynIntExprNode {
            creator: self.creator.clone(),
            indexes: vec![0; n],
        };
        let mut output = self;
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_right(&mut output.indexes, &input, rhs.bit(i), i, SIGN);
        }
        output
    }
}

/// Shift right implementation.
impl<T, const SIGN: bool> IntCondShr<DynIntExprNode<T, false>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    DynIntExprNode<T, false>: TryIntConstantN<T, usize>,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_shr(self, rhs: DynIntExprNode<T, false>) -> (Self::Output, Self::OutputCond) {
        let n = self.indexes.len();
        let n2 = rhs.indexes.len();
        let nbits = calc_log_bits(n);
        let nbits = cmp::min(nbits, n2);

        let mut input = DynIntExprNode {
            creator: self.creator.clone(),
            indexes: vec![0; n],
        };
        let mut output = self.clone();
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_right(&mut output.indexes, &input, rhs.bit(i), i, SIGN);
        }
        let nexpr = DynIntExprNode::<T, false>::try_constant_n(self.creator, n2, n - 1).unwrap();
        (output, rhs.less_equal(nexpr))
    }
}

impl<T, const SIGN: bool> IntCondShr<DynIntExprNode<T, true>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    DynIntExprNode<T, true>: TryIntConstantN<T, isize>,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_shr(self, rhs: DynIntExprNode<T, true>) -> (Self::Output, Self::OutputCond) {
        let n = self.indexes.len();
        let n2 = rhs.indexes.len();
        let nbits = calc_log_bits(n);
        let nbits = cmp::min(nbits, n2 - 1);

        let mut input = DynIntExprNode {
            creator: self.creator.clone(),
            indexes: vec![0; n],
        };
        let mut output = self.clone();
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_right(&mut output.indexes, &input, rhs.bit(i), i, SIGN);
        }
        let nexpr =
            DynIntExprNode::<T, true>::try_constant_n(self.creator, n2, (n - 1) as isize).unwrap();
        (output, (!rhs.bit(n2 - 1)) & rhs.less_equal(nexpr))
    }
}

macro_rules! impl_dynint_shr_imm {
    ($ty:ty) => {
        impl<T, const SIGN: bool> Shr<$ty> for DynIntExprNode<T, SIGN>
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
                DynIntExprNode {
                    creator: self.creator,
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
        impl<T, const SIGN: bool, const SIGN2: bool> $trait<DynIntExprNode<T, SIGN2>>
            for DynIntExprNode<T, SIGN>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $op_assign(&mut self, rhs: DynIntExprNode<T, SIGN2>) {
                *self = self.clone().$op(rhs)
            }
        }

        macro_rules! $macro {
            ($ty:ty) => {
                impl<T, const SIGN: bool> $trait<$ty> for DynIntExprNode<T, SIGN>
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
    t: DynIntExprNode<T, SIGN>,
    e: DynIntExprNode<T, SIGN>,
) -> DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    (DynIntExprNode::<T, SIGN>::filled_expr(t.len(), c.clone()) & t.clone())
        | (DynIntExprNode::<T, SIGN>::filled_expr(t.len(), !c) & e)
}

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions.
pub fn dynint_table<T, I, const SIGN: bool>(
    index: DynIntExprNode<T, SIGN>,
    table_iter: I,
) -> DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntExprNode<T, SIGN>>,
{
    let mut ites = vec![];
    let mut iter = table_iter.into_iter();
    while let Some(v) = iter.next() {
        if let Some(v2) = iter.next() {
            ites.push(dynint_ite(index.bit(0), v2, v));
        } else {
            panic!("Odd number of elements");
        }
    }

    for step in 1..(index.len()) {
        if (ites.len() & 1) != 0 {
            panic!("Odd number of elements");
        }
        for i in 0..(ites.len() >> 1) {
            ites[i] = dynint_ite(
                index.bit(step),
                ites[(i << 1) + 1].clone(),
                ites[i << 1].clone(),
            );
        }
        ites.resize(
            ites.len() >> 1,
            DynIntExprNode::filled(index.creator.clone(), ites[0].len(), false),
        );
    }

    ites.pop().unwrap()
}

// absolute value

impl<T> DynIntExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Calculation of an absolute value. It returns unsigned expression node.
    pub fn abs(self) -> DynIntExprNode<T, false> {
        // if sign then -self else self
        dynint_ite(
            self.bit(self.indexes.len() - 1),
            self.clone().mod_neg(),
            self,
        )
        .as_unsigned()
    }
}

//////////
// Add/Sub implementation

impl<T, const SIGN: bool> DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Returns result of modular addition with input carry `in_carry` and output carry.
    pub fn addc_with_carry(self, rhs: Self, in_carry: BoolExprNode<T>) -> (Self, BoolExprNode<T>) {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut output = vec![0; self.indexes.len()];
        let (c, _) = helper_addc_cout(&mut output, &self, &rhs, in_carry);
        (
            DynIntExprNode {
                creator: self.creator,
                indexes: output,
            },
            c,
        )
    }

    /// Returns result of modular addition with input carry.
    pub fn addc(self, rhs: Self, in_carry: BoolExprNode<T>) -> Self {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut output = vec![0; self.indexes.len()];
        helper_addc(&mut output, &self, &rhs, in_carry);
        DynIntExprNode {
            creator: self.creator,
            indexes: output,
        }
    }

    /// Returns result of modular subtraction with input carry - it performs `(A + !B) + carry`.
    pub fn subc(self, rhs: Self, in_carry: BoolExprNode<T>) -> Self {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut output = vec![0; self.indexes.len()];
        helper_subc(&mut output, &self, &rhs, in_carry);
        DynIntExprNode {
            creator: self.creator,
            indexes: output,
        }
    }

    /// Returns result of modular addition of self and same carry.
    pub fn add_same_carry(self, in_carry: BoolExprNode<T>) -> Self {
        let n = self.indexes.len();
        let mut output = vec![0; n];
        let mut c = in_carry;
        for (i, out) in output.iter_mut().enumerate().take(n - 1) {
            (*out, c) = {
                let (s0, c0) = half_adder(self.bit(i), c);
                (s0.index, c0)
            };
        }
        output[n - 1] = (self.bit(n - 1) ^ c).index;
        DynIntExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl<T, const SIGN: bool> IntModAdd<DynIntExprNode<T, SIGN>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mod_add(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut output = vec![0; self.indexes.len()];
        helper_addc(
            &mut output,
            &self,
            &rhs,
            BoolExprNode::single_value(self.creator.clone(), false),
        );
        DynIntExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl<T, const SIGN: bool> IntCondAdd<DynIntExprNode<T, SIGN>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_add(self, rhs: Self) -> (Self::Output, Self::OutputCond) {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut output = vec![0; self.indexes.len()];
        let (c, csign) = helper_addc_cout(
            &mut output,
            &self,
            &rhs,
            BoolExprNode::single_value(self.creator.clone(), false),
        );
        (
            DynIntExprNode {
                creator: self.creator,
                indexes: output,
            },
            if SIGN {
                // overflow: carry_out ^ carry_at_sign, we need negation of overflow
                c.bequal(csign)
            } else {
                !c // good if no carry
            },
        )
    }
}

impl<T, const SIGN: bool> IntModSub<DynIntExprNode<T, SIGN>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mod_sub(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut output = vec![0; self.indexes.len()];
        helper_subc(
            &mut output,
            &self,
            &rhs,
            BoolExprNode::single_value(self.creator.clone(), true),
        );
        DynIntExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl<T, const SIGN: bool> IntCondSub<DynIntExprNode<T, SIGN>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_sub(self, rhs: Self) -> (Self::Output, Self::OutputCond) {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut output = vec![0; self.indexes.len()];
        let (c, csign) = helper_subc_cout(
            &mut output,
            &self,
            &rhs,
            BoolExprNode::single_value(self.creator.clone(), true),
        );
        (
            DynIntExprNode {
                creator: self.creator,
                indexes: output,
            },
            if SIGN {
                // overflow: carry_out ^ carry_at_sign, we need negation of overflow
                c.bequal(csign)
            } else {
                c // good if carry
            },
        )
    }
}

impl_dynint_bitop_assign!(IntModAddAssign, mod_add, mod_add_assign);
impl_dynint_bitop_assign!(IntModSubAssign, mod_sub, mod_sub_assign);

impl<T> IntModNeg for DynIntExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mod_neg(self) -> Self {
        let trueval = BoolExprNode::new(self.creator.clone(), 1);
        (!self).add_same_carry(trueval)
    }
}

impl<T> IntCondNeg for DynIntExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_neg(self) -> (Self::Output, Self::OutputCond) {
        let lastbit = self.len() - 1;
        let self_sign = self.bit(lastbit);
        let negres = self.mod_neg();
        let negres_sign = negres.bit(lastbit);
        (negres, self_sign ^ negres_sign)
    }
}

/// Most advanced: multiplication.

impl<T, const SIGN: bool> IntModMul<DynIntExprNode<T, SIGN>> for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn mod_mul(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut matrix = gen_dadda_matrix(
            self.creator.clone(),
            &self.indexes,
            &rhs.indexes,
            self.indexes.len(),
        );
        let res = gen_dadda_mult(self.creator.clone(), &mut matrix);
        DynIntExprNode {
            creator: self.creator,
            indexes: res,
        }
    }
}

impl_dynint_bitop_assign!(IntModMulAssign, mod_mul, mod_mul_assign);

impl<T> IntCondMul<DynIntExprNode<T, false>> for DynIntExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_mul(self, rhs: Self) -> (Self::Output, Self::OutputCond) {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let n = self.indexes.len();
        let mut matrix = gen_dadda_matrix(self.creator.clone(), &self.indexes, &rhs.indexes, 2 * n);
        let res = gen_dadda_mult(self.creator.clone(), &mut matrix);
        let reshi = DynIntExprNode::<T, false> {
            creator: self.creator.clone(),
            indexes: Vec::from(&res[n..]),
        };
        (
            DynIntExprNode {
                creator: self.creator.clone(),
                indexes: Vec::from(&res[0..n]),
            },
            reshi.equal(DynIntExprNode::filled(self.creator, n, false)),
        )
    }
}

impl<T> IntCondMul<DynIntExprNode<T, true>> for DynIntExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn cond_mul(self, rhs: Self) -> (Self::Output, Self::OutputCond) {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let n = self.indexes.len();
        let expsign = self.bit(n - 1) ^ rhs.bit(n - 1);
        let (res, resc) = self.clone().abs().cond_mul(rhs.abs());
        let res = dynint_ite(
            expsign.clone(),
            res.clone().as_signed().mod_neg(),
            res.as_signed(),
        );
        let ressign = res.bit(n - 1);
        (
            res.clone(),
            // condition: higher part of absolute product must be zero,
            // result is zero (sign of result doesn't matter) or sign must be match.
            resc & (expsign.bequal(ressign)
                | res.equal(DynIntExprNode::filled(self.creator, n, false))),
        )
    }
}

/// Full multiplication

impl<T> FullMul<DynIntExprNode<T, false>> for DynIntExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = DynIntExprNode<T, false>;

    fn fullmul(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let mut matrix = gen_dadda_matrix(
            self.creator.clone(),
            &self.indexes,
            &rhs.indexes,
            2 * self.indexes.len(),
        );
        let res = gen_dadda_mult(self.creator.clone(), &mut matrix);
        DynIntExprNode {
            creator: self.creator,
            indexes: res,
        }
    }
}

impl<T> FullMul<DynIntExprNode<T, true>> for DynIntExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = DynIntExprNode<T, true>;

    fn fullmul(self, rhs: Self) -> Self::Output {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let expsign = self.bit(self.indexes.len() - 1) ^ rhs.bit(self.indexes.len() - 1);
        let res = self.abs().fullmul(rhs.abs());
        dynint_ite(expsign, res.clone().as_signed().mod_neg(), res.as_signed())
    }
}

// DivMod - dividion and remainder all in one

impl<T> DivMod<DynIntExprNode<T, false>> for DynIntExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn divmod(self, rhs: Self) -> (Self::Output, Self::Output, Self::OutputCond) {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let n = self.indexes.len();
        let divres = DynIntExprNode::<T, false>::variable(self.creator.clone(), n);
        let mut matrix =
            gen_dadda_matrix(self.creator.clone(), &rhs.indexes, &divres.indexes, 2 * n);
        let mulres = gen_dadda_mult(self.creator.clone(), &mut matrix);

        // modv - division modulo
        let modv = DynIntExprNode::<T, false>::variable(self.creator.clone(), n);
        let modv_cond = modv.clone().less_than(rhs);

        // add modulo to mulres
        let (mulres_lo, carry) = DynIntExprNode::<T, false> {
            creator: self.creator.clone(),
            indexes: Vec::from(&mulres[0..n]),
        }
        .addc_with_carry(
            modv.clone(),
            BoolExprNode::single_value(self.creator.clone(), false),
        );
        let mulres_hi = DynIntExprNode::<T, false> {
            creator: self.creator.clone(),
            indexes: Vec::from(&mulres[n..]),
        }
        .add_same_carry(carry);
        // condition for mulres - mulres_lo = self,  mulres_hi = 0
        let creator = self.creator.clone();
        let mulres_cond =
            mulres_lo.equal(self) & mulres_hi.equal(DynIntExprNode::filled(creator, n, false));

        (divres, modv, modv_cond & mulres_cond)
    }
}

impl<T> DivMod<DynIntExprNode<T, true>> for DynIntExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn divmod(self, rhs: Self) -> (Self::Output, Self::Output, Self::OutputCond) {
        assert_eq!(self.indexes.len(), rhs.indexes.len());
        let n = self.indexes.len();
        let ua = self.clone().abs();
        let ub = rhs.clone().abs();
        let (udiv, umod, cond) = ua.divmod(ub);
        let (sign_a, sign_b) = (self.bit(n - 1), rhs.bit(n - 1));
        let exp_divsign = sign_a.clone() ^ sign_b;
        let divres = dynint_ite(
            exp_divsign.clone(),
            udiv.clone().as_signed().mod_neg(),
            udiv.as_signed(),
        );
        let divres_sign = divres.bit(n - 1);
        (
            divres.clone(),
            dynint_ite(sign_a, umod.clone().as_signed().mod_neg(), umod.as_signed()),
            // condition: from unsiged divmod,
            // result is zero (sign of result doesn't matter) or sign must be match.
            cond & (exp_divsign.bequal(divres_sign)
                | divres.equal(DynIntExprNode::<T, true>::filled(self.creator, n, false))),
        )
    }
}

macro_rules! impl_dynint_div_mod {
    ($sign:expr) => {
        impl<T> Div<DynIntExprNode<T, $sign>> for DynIntExprNode<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (Self, BoolExprNode<T>);

            fn div(self, rhs: Self) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }

        impl<T> Rem<DynIntExprNode<T, $sign>> for DynIntExprNode<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = (Self, BoolExprNode<T>);

            fn rem(self, rhs: Self) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
    };
}

impl_dynint_div_mod!(false);
impl_dynint_div_mod!(true);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intexpr::{int_ite, int_table, IntExprNode};
    use generic_array::typenum::*;

    macro_rules! test_expr_node_binaryop {
        ($sign:expr, $op:ident, $op_assign:ident) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x2 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let mut res_x3 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x4 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let res = x1.$op(x2);
            res_x3.$op_assign(x4);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let mut exp_x3 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x4 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = x1.$op(x2);
            exp_x3.$op_assign(x4);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(exp_x3.indexes.as_slice(), res_x3.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_bitand() {
        test_expr_node_binaryop!(false, bitand, bitand_assign);
    }

    #[test]
    fn test_expr_node_bitor() {
        test_expr_node_binaryop!(false, bitor, bitor_assign);
    }

    #[test]
    fn test_expr_node_bitxor() {
        test_expr_node_binaryop!(false, bitxor, bitxor_assign);
    }

    #[test]
    fn test_expr_node_not() {
        let ec = ExprCreator::new();
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 10);
        let res = !x1;

        let exp_ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let exp = !x1;

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_expr_node_dynint_ite() {
        let ec = ExprCreator::new();
        let c = BoolExprNode::<isize>::variable(ec.clone());
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 10);
        let x2 = DynIntExprNode::<isize, false>::variable(ec.clone(), 10);
        let res = dynint_ite(c, x1, x2);

        let exp_ec = ExprCreator::new();
        let c = BoolExprNode::<isize>::variable(exp_ec.clone());
        let x1 = IntExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let x2 = IntExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let exp = int_ite(c, x1, x2);

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_expr_node_dynint_table() {
        let ec = ExprCreator::new();
        let idx = DynIntExprNode::<isize, false>::variable(ec.clone(), 5);
        let values = (0..(1 << 5))
            .into_iter()
            .map(|_| DynIntExprNode::<isize, false>::variable(ec.clone(), 10))
            .collect::<Vec<_>>();
        let res = dynint_table(idx, values);

        let exp_ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U5, false>::variable(exp_ec.clone());
        let values = (0..(1 << 5))
            .into_iter()
            .map(|_| IntExprNode::<isize, U10, false>::variable(exp_ec.clone()))
            .collect::<Vec<_>>();
        let exp = int_table(idx, values);

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    macro_rules! test_expr_node_shiftop {
        ($sign:expr, $op:ident, $op_assign:ident) => {{
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let x2 = DynIntExprNode::<isize, false>::variable(ec.clone(), 4);
            let mut res_x3 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let x4 = DynIntExprNode::<isize, false>::variable(ec.clone(), 4);
            let res = x1.$op(x2);
            res_x3.$op_assign(x4);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U4, false>::variable(exp_ec.clone());
            let mut exp_x3 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let x4 = IntExprNode::<isize, U4, false>::variable(exp_ec.clone());
            let exp = x1.$op(x2);
            exp_x3.$op_assign(x4);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(exp_x3.indexes.as_slice(), res_x3.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let x2 = DynIntExprNode::<isize, false>::variable(ec.clone(), 3);
            let mut res_x3 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let x4 = DynIntExprNode::<isize, false>::variable(ec.clone(), 3);
            let res = x1.$op(x2);
            res_x3.$op_assign(x4);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U3, false>::variable(exp_ec.clone());
            let mut exp_x3 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let x4 = IntExprNode::<isize, U3, false>::variable(exp_ec.clone());
            let exp = x1.$op(x2);
            exp_x3.$op_assign(x4);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(exp_x3.indexes.as_slice(), res_x3.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let x2 = DynIntExprNode::<isize, true>::try_from_n(
                DynIntExprNode::<isize, false>::variable(ec.clone(), 4),
                5,
            )
            .unwrap();
            let mut res_x3 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let x4 = DynIntExprNode::<isize, true>::try_from_n(
                DynIntExprNode::<isize, false>::variable(ec.clone(), 4),
                5,
            )
            .unwrap();
            let res = x1.$op(x2);
            res_x3.$op_assign(x4);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U5, true>::from(
                IntExprNode::<isize, U4, false>::variable(exp_ec.clone()),
            );
            let mut exp_x3 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let x4 = IntExprNode::<isize, U5, true>::from(
                IntExprNode::<isize, U4, false>::variable(exp_ec.clone()),
            );
            let exp = x1.$op(x2);
            exp_x3.$op_assign(x4);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(exp_x3.indexes.as_slice(), res_x3.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let x2 = DynIntExprNode::<isize, true>::try_from_n(
                DynIntExprNode::<isize, false>::variable(ec.clone(), 3),
                4,
            )
            .unwrap();
            let mut res_x3 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let x4 = DynIntExprNode::<isize, true>::try_from_n(
                DynIntExprNode::<isize, false>::variable(ec.clone(), 3),
                4,
            )
            .unwrap();
            let res = x1.$op(x2);
            res_x3.$op_assign(x4);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U4, true>::from(
                IntExprNode::<isize, U3, false>::variable(exp_ec.clone()),
            );
            let mut exp_x3 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let x4 = IntExprNode::<isize, U4, true>::from(
                IntExprNode::<isize, U3, false>::variable(exp_ec.clone()),
            );
            let exp = x1.$op(x2);
            exp_x3.$op_assign(x4);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(exp_x3.indexes.as_slice(), res_x3.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let mut res_x3 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let res = x1.$op(11u8);
            res_x3.$op_assign(10u8);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let mut exp_x3 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let exp = x1.$op(11u8);
            exp_x3.$op_assign(10u8);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(exp_x3.indexes.as_slice(), res_x3.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let mut res_x3 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 16);
            let res = x1.$op(11i8);
            res_x3.$op_assign(10i8);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let mut exp_x3 = IntExprNode::<isize, U16, $sign>::variable(exp_ec.clone());
            let exp = x1.$op(11i8);
            exp_x3.$op_assign(10i8);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(exp_x3.indexes.as_slice(), res_x3.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    #[test]
    fn test_expr_node_shl() {
        test_expr_node_shiftop!(false, shl, shl_assign);
        test_expr_node_shiftop!(true, shl, shl_assign);
    }

    #[test]
    fn test_expr_node_shr() {
        test_expr_node_shiftop!(false, shr, shr_assign);
        test_expr_node_shiftop!(true, shr, shr_assign);
    }

    macro_rules! test_expr_node_cond_shl_5 {
        ($sign:expr, $signrhs:expr, $ty:ty, $torhs:ty, $bits:expr, $bits2:expr) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), $bits);
            let x2 = DynIntExprNode::<isize, $signrhs>::variable(ec.clone(), $bits2);
            let (res, resc) = x1.cond_shl(x2);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, $ty, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, $torhs, $signrhs>::variable(exp_ec.clone());
            let (exp, expc) = x1.cond_shl(x2);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(expc.index, resc.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_cond_shl() {
        test_expr_node_cond_shl_5!(false, false, U26, U5, 26, 5);
        test_expr_node_cond_shl_5!(true, false, U26, U5, 26, 5);
        test_expr_node_cond_shl_5!(false, false, U32, U5, 32, 5);
        test_expr_node_cond_shl_5!(true, false, U32, U5, 32, 5);
        test_expr_node_cond_shl_5!(false, false, U26, U7, 26, 7);
        test_expr_node_cond_shl_5!(true, false, U26, U7, 26, 7);
        test_expr_node_cond_shl_5!(false, false, U32, U7, 32, 7);
        test_expr_node_cond_shl_5!(true, false, U32, U7, 32, 7);

        test_expr_node_cond_shl_5!(false, true, U26, U6, 26, 6);
        test_expr_node_cond_shl_5!(true, true, U26, U6, 26, 6);
        test_expr_node_cond_shl_5!(false, true, U32, U6, 32, 6);
        test_expr_node_cond_shl_5!(true, true, U32, U6, 32, 6);
        test_expr_node_cond_shl_5!(false, true, U26, U7, 26, 7);
        test_expr_node_cond_shl_5!(true, true, U26, U7, 26, 7);
        test_expr_node_cond_shl_5!(false, true, U32, U7, 32, 7);
        test_expr_node_cond_shl_5!(true, true, U32, U7, 32, 7);
    }

    macro_rules! test_expr_node_cond_shr_5 {
        ($sign:expr, $signrhs:expr, $ty:ty, $torhs:ty, $bits:expr, $bits2:expr) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), $bits);
            let x2 = DynIntExprNode::<isize, $signrhs>::variable(ec.clone(), $bits2);
            let (res, resc) = x1.cond_shr(x2);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, $ty, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, $torhs, $signrhs>::variable(exp_ec.clone());
            let (exp, expc) = x1.cond_shr(x2);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(expc.index, resc.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_cond_shr() {
        test_expr_node_cond_shr_5!(false, false, U26, U5, 26, 5);
        test_expr_node_cond_shr_5!(true, false, U26, U5, 26, 5);
        test_expr_node_cond_shr_5!(false, false, U32, U5, 32, 5);
        test_expr_node_cond_shr_5!(true, false, U32, U5, 32, 5);
        test_expr_node_cond_shr_5!(false, false, U26, U7, 26, 7);
        test_expr_node_cond_shr_5!(true, false, U26, U7, 26, 7);
        test_expr_node_cond_shr_5!(false, false, U32, U7, 32, 7);
        test_expr_node_cond_shr_5!(true, false, U32, U7, 32, 7);

        test_expr_node_cond_shr_5!(false, true, U26, U6, 26, 6);
        test_expr_node_cond_shr_5!(true, true, U26, U6, 26, 6);
        test_expr_node_cond_shr_5!(false, true, U32, U6, 32, 6);
        test_expr_node_cond_shr_5!(true, true, U32, U6, 32, 6);
        test_expr_node_cond_shr_5!(false, true, U26, U7, 26, 7);
        test_expr_node_cond_shr_5!(true, true, U26, U7, 26, 7);
        test_expr_node_cond_shr_5!(false, true, U32, U7, 32, 7);
        test_expr_node_cond_shr_5!(true, true, U32, U7, 32, 7);
    }

    #[test]
    fn test_expr_node_addc_with_carry() {
        let ec = ExprCreator::new();
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 10);
        let x2 = DynIntExprNode::<isize, false>::variable(ec.clone(), 10);
        let c = BoolExprNode::<isize>::variable(ec.clone());
        let (res, resc) = x1.addc_with_carry(x2, c);

        let exp_ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let x2 = IntExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let c = BoolExprNode::<isize>::variable(exp_ec.clone());
        let (exp, expc) = x1.addc_with_carry(x2, c);

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(expc.index, resc.index);
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    macro_rules! test_expr_node_arith_carry {
        ($sign:expr, $op:ident) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x2 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let c = BoolExprNode::<isize>::variable(ec.clone());
            let res = x1.$op(x2, c);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let c = BoolExprNode::<isize>::variable(exp_ec.clone());
            let exp = x1.$op(x2, c);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_addc() {
        test_expr_node_arith_carry!(false, addc);
    }

    #[test]
    fn test_expr_node_subc() {
        test_expr_node_arith_carry!(false, subc);
    }

    #[test]
    fn test_expr_node_addc_same_carry() {
        let ec = ExprCreator::new();
        let x1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 10);
        let c = BoolExprNode::<isize>::variable(ec.clone());
        let res = x1.add_same_carry(c);

        let exp_ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let c = BoolExprNode::<isize>::variable(exp_ec.clone());
        let exp = x1.add_same_carry(c);

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_expr_node_mod_add() {
        test_expr_node_binaryop!(false, mod_add, mod_add_assign);
        test_expr_node_binaryop!(true, mod_add, mod_add_assign);
    }

    #[test]
    fn test_expr_node_mod_sub() {
        test_expr_node_binaryop!(false, mod_sub, mod_sub_assign);
        test_expr_node_binaryop!(true, mod_sub, mod_sub_assign);
    }

    macro_rules! test_expr_node_condop {
        ($sign:expr, $op:ident) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x2 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let (res, resc) = x1.$op(x2);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let (exp, expc) = x1.$op(x2);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(expc.index, resc.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_cond_add() {
        test_expr_node_condop!(false, cond_add);
        test_expr_node_condop!(true, cond_add);
    }

    #[test]
    fn test_expr_node_cond_sub() {
        test_expr_node_condop!(false, cond_sub);
        test_expr_node_condop!(true, cond_sub);
    }

    #[test]
    fn test_expr_node_unaryops() {
        let ec = ExprCreator::new();
        let x1 = DynIntExprNode::<isize, true>::variable(ec.clone(), 10);
        let x2 = DynIntExprNode::<isize, true>::variable(ec.clone(), 10);
        let x3 = DynIntExprNode::<isize, true>::variable(ec.clone(), 10);
        let resabs = x1.abs();
        let resneg = x2.mod_neg();
        let (resneg2, resneg2c) = x3.cond_neg();

        let exp_ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U10, true>::variable(exp_ec.clone());
        let x2 = IntExprNode::<isize, U10, true>::variable(exp_ec.clone());
        let x3 = IntExprNode::<isize, U10, true>::variable(exp_ec.clone());
        let expabs = x1.abs();
        let expneg = x2.mod_neg();
        let (expneg2, expneg2c) = x3.cond_neg();

        assert_eq!(expabs.indexes.as_slice(), resabs.indexes.as_slice());
        assert_eq!(expneg.indexes.as_slice(), resneg.indexes.as_slice());
        assert_eq!(expneg2.indexes.as_slice(), resneg2.indexes.as_slice());
        assert_eq!(expneg2c.index, resneg2c.index);
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_expr_node_mod_mul() {
        test_expr_node_binaryop!(false, mod_mul, mod_mul_assign);
        test_expr_node_binaryop!(true, mod_mul, mod_mul_assign);
    }

    #[test]
    fn test_expr_node_cond_mul() {
        test_expr_node_condop!(false, cond_mul);
        test_expr_node_condop!(true, cond_mul);
    }

    macro_rules! test_expr_node_fullmul {
        ($sign:expr) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x2 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let res = x1.fullmul(x2);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = x1.fullmul(x2);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_fullmul() {
        test_expr_node_fullmul!(false);
        test_expr_node_fullmul!(true);
    }

    macro_rules! test_expr_node_divmod {
        ($sign:expr) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x2 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let (resdiv, resmod, rescond) = x1.divmod(x2);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let (expdiv, expmod, expcond) = x1.divmod(x2);

            assert_eq!(expdiv.indexes.as_slice(), resdiv.indexes.as_slice());
            assert_eq!(expmod.indexes.as_slice(), resmod.indexes.as_slice());
            assert_eq!(expcond.index, rescond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_divmod() {
        test_expr_node_divmod!(false);
        test_expr_node_divmod!(true);
    }

    macro_rules! test_expr_node_divop {
        ($sign:expr, $op:ident) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x2 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let (res, resc) = x1.$op(x2);

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let (exp, expc) = x1.$op(x2);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(expc.index, resc.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_div() {
        test_expr_node_divop!(false, div);
        test_expr_node_divop!(true, div);
    }

    #[test]
    fn test_expr_node_rem() {
        test_expr_node_divop!(false, rem);
        test_expr_node_divop!(true, rem);
    }
}
