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
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, Mul,
    MulAssign, Neg, Not, Rem, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use super::*;

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

pub fn dynint_table<T, I, const SIGN: bool>(
    index: ExprNode<T, SIGN>,
    table_iter: I,
) -> ExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = ExprNode<T, SIGN>>,
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
                ites[(i << 1)].clone(),
            );
        }
        ites.resize(
            ites.len() >> 1,
            ExprNode::filled(index.creator.clone(), ites[0].len(), false),
        );
    }

    ites.pop().unwrap()
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

impl<T> FullMul<ExprNode<T, true>> for ExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = ExprNode<T, true>;

    fn fullmul(self, rhs: Self) -> Self::Output {
        let ua = self.clone().abs();
        let ub = rhs.clone().abs();
        let res = ua.fullmul(ub);
        dynint_ite(
            self.bit(self.indexes.len() - 1) ^ rhs.bit(self.indexes.len() - 1),
            -res.clone().as_signed(),
            res.as_signed(),
        )
    }
}

// DivMod - dividion and remainder all in one

impl<T> DivMod<ExprNode<T, false>> for ExprNode<T, false>
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
        let n = self.indexes.len();
        let divres = ExprNode::<T, false>::variable(self.creator.clone(), n);
        let mut matrix =
            gen_dadda_matrix(self.creator.clone(), &rhs.indexes, &divres.indexes, 2 * n);
        let mulres = gen_dadda_mult(self.creator.clone(), &mut matrix);

        // modv - division modulo
        let modv = ExprNode::<T, false>::variable(self.creator.clone(), n);
        let modv_cond = modv.clone().less_than(rhs);

        // add modulo to mulres
        let (mulres_lo, carry) = ExprNode::<T, false> {
            creator: self.creator.clone(),
            indexes: Vec::from(&mulres[0..n]),
        }
        .addc_with_carry(
            modv.clone(),
            BoolExprNode::single_value(self.creator.clone(), false),
        );
        let mulres_hi = ExprNode::<T, false> {
            creator: self.creator.clone(),
            indexes: Vec::from(&mulres[n..]),
        }
        .add_same_carry(carry);
        // condition for mulres - mulres_lo = self,  mulres_hi = 0
        let creator = self.creator.clone();
        let mulres_cond =
            mulres_lo.equal(self) & mulres_hi.equal(ExprNode::filled(creator, n, false));

        (divres, modv, modv_cond & mulres_cond)
    }
}

impl<T> DivMod<ExprNode<T, true>> for ExprNode<T, true>
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
        let n = self.indexes.len();
        let ua = self.clone().abs();
        let ub = rhs.clone().abs();
        let (udiv, umod, cond) = ua.divmod(ub);
        let (sign_a, sign_b) = (self.bit(n - 1), rhs.bit(n - 1));
        let exp_divsign = sign_a.clone() ^ sign_b;
        let divres = dynint_ite(
            exp_divsign.clone(),
            -(udiv.clone().as_signed()),
            udiv.as_signed(),
        );
        let divres_sign = divres.bit(n - 1);
        (
            divres.clone(),
            dynint_ite(sign_a, -(umod.clone().as_signed()), umod.as_signed()),
            cond & (exp_divsign.bequal(divres_sign)
                | divres.equal(ExprNode::<T, true>::filled(self.creator.clone(), n, false))),
        )
    }
}

macro_rules! impl_dynint_div_mod {
    ($sign:expr) => {
        impl<T> Div<ExprNode<T, $sign>> for ExprNode<T, $sign>
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

        impl<T> Rem<ExprNode<T, $sign>> for ExprNode<T, $sign>
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
    use crate::IntExprNode;
    use generic_array::typenum::*;
    
    macro_rules! test_expr_node_binaryop {
        ($sign:expr, $op:ident, $op_assign:ident) => {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x2 = ExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let mut res_x3 = ExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let x4 = ExprNode::<isize, $sign>::variable(ec.clone(), 10);
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
        }
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
    fn test_expr_node_add() {
        test_expr_node_binaryop!(false, add, add_assign);
    }
    
    #[test]
    fn test_expr_node_sub() {
        test_expr_node_binaryop!(false, sub, sub_assign);
    }
    
    #[test]
    fn test_expr_node_mul() {
        test_expr_node_binaryop!(false, mul, mul_assign);
    }
}
