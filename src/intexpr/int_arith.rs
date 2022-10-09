// int_arith.rs - integer expression structures.
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

use std::fmt::Debug;
use std::ops::{Div, Neg, Rem};

use generic_array::typenum::*;
use generic_array::*;

use super::*;
use crate::{impl_int_ipty_ty1, impl_int_upty_ty1};
use crate::{BoolEqual, BoolExprNode, VarLit};

impl<T, N: ArrayLength<usize>> ExprNode<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn abs(self) -> ExprNode<T, N, false> {
        // if sign then -self else self
        int_ite(self.bit(N::USIZE - 1), self.clone().mod_neg(), self).as_unsigned()
    }
}

//////////
// Add/Sub implementation

impl<T, N: ArrayLength<usize>, const SIGN: bool> ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn addc_with_carry(self, rhs: Self, in_carry: BoolExprNode<T>) -> (Self, BoolExprNode<T>) {
        let mut output = GenericArray::<usize, N>::default();
        let (c, _) = helper_addc_cout(&mut output, &self, &rhs, in_carry);
        (
            ExprNode {
                creator: self.creator,
                indexes: output,
            },
            c,
        )
    }

    pub fn addc(self, rhs: Self, in_carry: BoolExprNode<T>) -> Self {
        let mut output = GenericArray::<usize, N>::default();
        helper_addc(&mut output, &self, &rhs, in_carry);
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }

    pub fn subc(self, rhs: Self, in_carry: BoolExprNode<T>) -> Self {
        let mut output = GenericArray::<usize, N>::default();
        helper_subc(&mut output, &self, &rhs, in_carry);
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }

    pub fn add_same_carry(self, in_carry: BoolExprNode<T>) -> Self {
        let mut output = GenericArray::<usize, N>::default();
        let mut c = in_carry;
        for i in 0..N::USIZE - 1 {
            (output[i], c) = {
                let (s0, c0) = half_adder(self.bit(i), c);
                (s0.index, c0)
            };
        }
        output[N::USIZE - 1] = (self.bit(N::USIZE - 1) ^ c).index;
        ExprNode {
            creator: self.creator,
            indexes: output,
        }
    }
}

impl<T, N, const SIGN: bool> IntModAdd<ExprNode<T, N, SIGN>> for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn mod_add(self, rhs: Self) -> Self::Output {
        let mut output = GenericArray::<usize, N>::default();
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

impl_int_binary_op!($, IntModAdd, mod_add, impl_int_add_pty, impl_int_add_upty, impl_int_add_ipty);

impl<T, N, const SIGN: bool> IntModSub<ExprNode<T, N, SIGN>> for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn mod_sub(self, rhs: Self) -> Self::Output {
        let mut output = GenericArray::<usize, N>::default();
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

impl_int_binary_op!($, IntModSub, mod_sub, impl_int_sub_pty, impl_int_sub_upty, impl_int_sub_ipty);

// AddAssign,  SubAssign
impl_int_bitop_assign!($, IntModAddAssign, mod_add_assign, mod_add, impl_int_add_assign_pty,
        impl_int_add_assign_upty, impl_int_add_assign_ipty);
impl_int_bitop_assign!($, IntModSubAssign, mod_sub_assign, mod_sub, impl_int_sub_assign_pty,
        impl_int_sub_assign_upty, impl_int_sub_assign_ipty);

impl<T, N> IntModNeg for ExprNode<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn mod_neg(self) -> Self {
        let trueval = BoolExprNode::new(self.creator.clone(), 1);
        (!self).add_same_carry(trueval)
    }
}

/// Most advanced: multiplication.

impl<T, N, const SIGN: bool> IntModMul<ExprNode<T, N, SIGN>> for ExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;

    fn mod_mul(self, rhs: Self) -> Self::Output {
        let mut matrix =
            gen_dadda_matrix(self.creator.clone(), &self.indexes, &rhs.indexes, N::USIZE);
        let mut res = gen_dadda_mult(self.creator.clone(), &mut matrix);
        ExprNode {
            creator: self.creator,
            indexes: GenericArray::from_exact_iter(res.drain(..)).unwrap(),
        }
    }
}

impl_int_binary_op!($, IntModMul, mod_mul, impl_int_mul_pty, impl_int_mul_upty, impl_int_mul_ipty);
impl_int_bitop_assign!($, IntModMulAssign, mod_mul_assign, mod_mul, impl_int_mul_assign_pty,
        impl_int_mul_assign_upty, impl_int_mul_assign_ipty);

/// Full multiplication

impl<T, N> FullMul<ExprNode<T, N, false>> for ExprNode<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize> + Add,
    <N as Add>::Output: ArrayLength<usize>,
{
    type Output = ExprNode<T, operator_aliases::Sum<N, N>, false>;

    fn fullmul(self, rhs: Self) -> Self::Output {
        let mut matrix = gen_dadda_matrix(
            self.creator.clone(),
            &self.indexes,
            &rhs.indexes,
            2 * N::USIZE,
        );
        let mut res = gen_dadda_mult(self.creator.clone(), &mut matrix);
        ExprNode {
            creator: self.creator,
            indexes: GenericArray::from_exact_iter(res.drain(..)).unwrap(),
        }
    }
}

impl<T, N> FullMul<ExprNode<T, N, true>> for ExprNode<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize> + Add,
    <N as Add>::Output: ArrayLength<usize>,
{
    type Output = ExprNode<T, operator_aliases::Sum<N, N>, true>;

    fn fullmul(self, rhs: Self) -> ExprNode<T, operator_aliases::Sum<N, N>, true> {
        let ua = self.clone().abs();
        let ub = rhs.clone().abs();
        let res = ua.fullmul(ub);
        int_ite(
            self.bit(N::USIZE - 1) ^ rhs.bit(N::USIZE - 1),
            res.clone().as_signed().mod_neg(),
            res.as_signed(),
        )
    }
}

macro_rules! impl_int_fullmul_pty {
    ($sign:expr, $pty:ty, $ty:ty, $($gparams:ident),*) => {
        /// Binary operation traits implementation.
        impl<T, $( $gparams ),* > FullMul< $pty > for ExprNode<T, $ty, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize> + Add,
            <$ty as Add>::Output: ArrayLength<usize>,
        {
            type Output = ExprNode<T, operator_aliases::Sum<$ty, $ty>, $sign>;

            fn fullmul(self, rhs: $pty) -> Self::Output {
                let creator = self.creator.clone();
                self.fullmul(Self::constant(creator, rhs))
            }
        }

        /// Binary operation traits implementation.
        impl<T, $( $gparams ),* > FullMul<ExprNode<T, $ty, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize> + Add,
            <$ty as Add>::Output: ArrayLength<usize>,
        {
            type Output = ExprNode<T, operator_aliases::Sum<$ty, $ty>, $sign>;

            fn fullmul(self, rhs: ExprNode<T, $ty, $sign>) -> Self::Output {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, $sign>::constant(creator, self).fullmul(rhs)
            }
        }
    }
}

macro_rules! impl_int_fullmul_upty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl_int_fullmul_pty!(false, $pty, $ty, $($gparams ),*);
    }
}
macro_rules! impl_int_fullmul_ipty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl_int_fullmul_pty!(true, $pty, $ty, $($gparams ),*);
    }
}

impl_int_upty_ty1!(impl_int_fullmul_upty);
impl_int_ipty_ty1!(impl_int_fullmul_ipty);

// DivMod - dividion and remainder all in one

impl<T, N> DivMod<ExprNode<T, N, false>> for ExprNode<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn divmod(self, rhs: Self) -> (Self::Output, Self::Output, Self::OutputCond) {
        let divres = ExprNode::<T, N, false>::variable(self.creator.clone());
        let mut matrix = gen_dadda_matrix(
            self.creator.clone(),
            &rhs.indexes,
            &divres.indexes,
            2 * N::USIZE,
        );
        let mulres = gen_dadda_mult(self.creator.clone(), &mut matrix);

        // modv - division modulo
        let modv = ExprNode::<T, N, false>::variable(self.creator.clone());
        let modv_cond = modv.clone().less_than(rhs);

        // add modulo to mulres
        let (mulres_lo, carry) = ExprNode::<T, N, false> {
            creator: self.creator.clone(),
            indexes: GenericArray::clone_from_slice(&mulres[0..N::USIZE]),
        }
        .addc_with_carry(
            modv.clone(),
            BoolExprNode::single_value(self.creator.clone(), false),
        );
        let mulres_hi = ExprNode::<T, N, false> {
            creator: self.creator.clone(),
            indexes: GenericArray::clone_from_slice(&mulres[N::USIZE..]),
        }
        .add_same_carry(carry);
        // condition for mulres - mulres_lo = self,  mulres_hi = 0
        let creator = self.creator.clone();
        let mulres_cond = mulres_lo.equal(self) & mulres_hi.equal(ExprNode::filled(creator, false));

        (divres, modv, modv_cond & mulres_cond)
    }
}

impl<T, N> DivMod<ExprNode<T, N, true>> for ExprNode<T, N, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;
    type OutputCond = BoolExprNode<T>;

    fn divmod(self, rhs: Self) -> (Self::Output, Self::Output, Self::OutputCond) {
        let ua = self.clone().abs();
        let ub = rhs.clone().abs();
        let (udiv, umod, cond) = ua.divmod(ub);
        let (sign_a, sign_b) = (self.bit(N::USIZE - 1), rhs.bit(N::USIZE - 1));
        let exp_divsign = sign_a.clone() ^ sign_b;
        let divres = int_ite(
            exp_divsign.clone(),
            udiv.clone().as_signed().mod_neg(),
            udiv.as_signed(),
        );
        let divres_sign = divres.bit(N::USIZE - 1);
        (
            divres.clone(),
            int_ite(sign_a, umod.clone().as_signed().mod_neg(), umod.as_signed()),
            cond & (exp_divsign.bequal(divres_sign)
                | divres.equal(ExprNode::<T, N, true>::filled(self.creator.clone(), false))),
        )
    }
}

macro_rules! impl_int_divmodall_pty {
    ($sign:expr, $pty:ty, $ty:ty, $($gparams:ident),*) => {
        /// Binary operation traits implementation.
        impl<T, $( $gparams ),* > DivMod< $pty > for ExprNode<T, $ty, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = ExprNode<T, $ty, $sign>;
            type OutputCond = BoolExprNode<T>;

            fn divmod(
                self,
                rhs: $pty,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                let creator = self.creator.clone();
                self.divmod(Self::constant(creator, rhs))
            }
        }

        /// Binary operation traits implementation.
        impl<T, $( $gparams ),* > DivMod<ExprNode<T, $ty, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            $ty: ArrayLength<usize>,
        {
            type Output = ExprNode<T, $ty, $sign>;
            type OutputCond = BoolExprNode<T>;

            fn divmod(
                self,
                rhs: ExprNode<T, $ty, $sign>,
            ) -> (Self::Output, Self::Output, Self::OutputCond) {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, $sign>::constant(creator, self).divmod(rhs)
            }
        }
    }
}

macro_rules! impl_int_divmodall_upty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl_int_divmodall_pty!(false, $pty, $ty, $($gparams ),*);
    }
}
macro_rules! impl_int_divmodall_ipty {
    ($pty:ty, $ty:ty, $($gparams:ident),*) => {
        impl_int_divmodall_pty!(true, $pty, $ty, $($gparams ),*);
    }
}

impl_int_upty_ty1!(impl_int_divmodall_upty);
impl_int_ipty_ty1!(impl_int_divmodall_ipty);

/// Division and remainder

macro_rules! impl_int_div_mod {
    ($sign:expr) => {
        impl<T, N> Div<ExprNode<T, N, $sign>> for ExprNode<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (Self, BoolExprNode<T>);

            fn div(self, rhs: Self) -> Self::Output {
                let (d, _, c) = self.divmod(rhs);
                (d, c)
            }
        }

        impl<T, N> Rem<ExprNode<T, N, $sign>> for ExprNode<T, N, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
        {
            type Output = (Self, BoolExprNode<T>);

            fn rem(self, rhs: Self) -> Self::Output {
                let (_, r, c) = self.divmod(rhs);
                (r, c)
            }
        }
    };
}

impl_int_div_mod!(false);
impl_int_div_mod!(true);

macro_rules! impl_int_div_mod_op {
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
                            type Output = (Self, BoolExprNode<T>);

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
                            type Output = (ExprNode<T, $ty, $sign>, BoolExprNode<T>);

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

impl_int_div_mod_op!($, Div, div, impl_int_div_pty, impl_int_div_upty, impl_int_div_ipty);
impl_int_div_mod_op!($, Rem, rem, impl_int_rem_pty, impl_int_rem_upty, impl_int_rem_ipty);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolexpr::opt_full_adder;
    use crate::boolexpr::test_utils::*;

    #[test]
    fn test_expr_node_neg() {
        let ec = ExprCreator::new();
        let x1 = ExprNode::<isize, U5, true>::variable(ec.clone());
        let res = x1.mod_neg();

        let exp_ec = ExprCreator::new();
        let bvs = alloc_boolvars(exp_ec.clone(), 5)
            .into_iter()
            .map(|x| !x)
            .collect::<Vec<_>>();
        let bnfalse = BoolExprNode::single_value(exp_ec.clone(), false);
        let bntrue = BoolExprNode::single_value(exp_ec.clone(), true);
        let mut temp = vec![];
        temp.push(half_adder(bvs[0].clone(), bntrue));
        temp.push(half_adder(bvs[1].clone(), temp[0].clone().1));
        temp.push(half_adder(bvs[2].clone(), temp[1].clone().1));
        temp.push(half_adder(bvs[3].clone(), temp[2].clone().1));
        temp.push((bvs[4].clone() ^ temp[3].clone().1, bnfalse));
        let exp = temp.iter().map(|x| x.0.index).collect::<Vec<_>>();

        assert_eq!(exp.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_expr_node_abs() {
        let ec = ExprCreator::new();
        let x1 = ExprNode::<isize, U10, true>::variable(ec.clone());
        let res = x1.abs();

        let exp_ec = ExprCreator::new();
        let x1 = ExprNode::<isize, U10, true>::variable(exp_ec.clone());
        let exp = int_ite(x1.bit(9), x1.clone().mod_neg(), x1.clone());

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_expr_node_add_primitives() {
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let c1 = BoolExprNode::variable(ec.clone());
            let res = x1.addc_with_carry(x2, c1);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 11);
            let mut temp = vec![];
            temp.push(opt_full_adder(
                bvs[0].clone(),
                bvs[5].clone(),
                bvs[10].clone(),
            ));
            temp.push(opt_full_adder(
                bvs[1].clone(),
                bvs[6].clone(),
                temp[0].clone().1,
            ));
            temp.push(opt_full_adder(
                bvs[2].clone(),
                bvs[7].clone(),
                temp[1].clone().1,
            ));
            temp.push(opt_full_adder(
                bvs[3].clone(),
                bvs[8].clone(),
                temp[2].clone().1,
            ));
            temp.push(opt_full_adder(
                bvs[4].clone(),
                bvs[9].clone(),
                temp[3].clone().1,
            ));
            let exp = temp.iter().map(|x| x.0.index).collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.0.indexes.as_slice());
            assert_eq!(temp[4].1.index, res.1.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let c1 = BoolExprNode::variable(ec.clone());
            let res = x1.addc(x2, c1);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 11);
            let mut temp = vec![];

            let bnfalse = BoolExprNode::single_value(exp_ec.clone(), false);
            temp.push(opt_full_adder(
                bvs[0].clone(),
                bvs[5].clone(),
                bvs[10].clone(),
            ));
            temp.push(opt_full_adder(
                bvs[1].clone(),
                bvs[6].clone(),
                temp[0].clone().1,
            ));
            temp.push(opt_full_adder(
                bvs[2].clone(),
                bvs[7].clone(),
                temp[1].clone().1,
            ));
            temp.push(opt_full_adder(
                bvs[3].clone(),
                bvs[8].clone(),
                temp[2].clone().1,
            ));
            temp.push((bvs[4].clone() ^ bvs[9].clone() ^ temp[3].clone().1, bnfalse));
            let exp = temp.iter().map(|x| x.0.index).collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U5, false>::variable(ec.clone());
            let c1 = BoolExprNode::variable(ec.clone());
            let res = x1.subc(x2, c1);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 11);
            let mut temp = vec![];

            let bnfalse = BoolExprNode::single_value(exp_ec.clone(), false);
            temp.push(opt_full_adder(
                bvs[0].clone(),
                !bvs[5].clone(),
                bvs[10].clone(),
            ));
            temp.push(opt_full_adder(
                bvs[1].clone(),
                !bvs[6].clone(),
                temp[0].clone().1,
            ));
            temp.push(opt_full_adder(
                bvs[2].clone(),
                !bvs[7].clone(),
                temp[1].clone().1,
            ));
            temp.push(opt_full_adder(
                bvs[3].clone(),
                !bvs[8].clone(),
                temp[2].clone().1,
            ));
            temp.push((
                bvs[4].clone() ^ !bvs[9].clone() ^ temp[3].clone().1,
                bnfalse,
            ));
            let exp = temp.iter().map(|x| x.0.index).collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U5, true>::variable(ec.clone());
            let c1 = BoolExprNode::variable(ec.clone());
            let res = x1.add_same_carry(c1);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 6);
            let bnfalse = BoolExprNode::single_value(exp_ec.clone(), false);
            let mut temp = vec![];
            temp.push(half_adder(bvs[0].clone(), bvs[5].clone()));
            temp.push(half_adder(bvs[1].clone(), temp[0].clone().1));
            temp.push(half_adder(bvs[2].clone(), temp[1].clone().1));
            temp.push(half_adder(bvs[3].clone(), temp[2].clone().1));
            temp.push((bvs[4].clone() ^ temp[3].clone().1, bnfalse));
            let exp = temp.iter().map(|x| x.0.index).collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
    }

    macro_rules! test_expr_node_mod_add_and_assign_xx {
        ($sign:expr, $imm1:expr, $imm2:expr) => {{
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = x1.mod_add(x2);

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            x1_out.mod_add_assign(x2);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = x1.addc(x2, BoolExprNode::single_value(exp_ec.clone(), false));

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.indexes.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = x1.mod_add($imm1);

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            x1_out.mod_add_assign($imm1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = x1.addc(
                ExprNode::constant(exp_ec.clone(), $imm1),
                BoolExprNode::single_value(exp_ec.clone(), false),
            );

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.indexes.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = ($imm2).mod_add(x1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = ExprNode::constant(exp_ec.clone(), $imm2)
                .addc(x1, BoolExprNode::single_value(exp_ec.clone(), false));

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    #[test]
    fn test_expr_node_mod_add_and_assign() {
        test_expr_node_mod_add_and_assign_xx!(false, 71, 138);
        test_expr_node_mod_add_and_assign_xx!(true, 105, 62);
        test_expr_node_mod_add_and_assign_xx!(true, -69, -86);
    }

    macro_rules! test_expr_node_mod_sub_and_assign_xx {
        ($sign:expr, $imm1:expr, $imm2:expr) => {{
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = x1.mod_sub(x2);

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            x1_out.mod_sub_assign(x2);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = x1.subc(x2, BoolExprNode::single_value(exp_ec.clone(), true));

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.indexes.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = x1.mod_sub($imm1);

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            x1_out.mod_sub_assign($imm1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = x1.subc(
                ExprNode::constant(exp_ec.clone(), $imm1),
                BoolExprNode::single_value(exp_ec.clone(), true),
            );

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.indexes.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = ($imm2).mod_sub(x1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = ExprNode::constant(exp_ec.clone(), $imm2)
                .subc(x1, BoolExprNode::single_value(exp_ec.clone(), true));

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    #[test]
    fn test_expr_node_mod_sub_and_assign() {
        test_expr_node_mod_sub_and_assign_xx!(false, 85, 151);
        test_expr_node_mod_sub_and_assign_xx!(true, 56, 113);
        test_expr_node_mod_sub_and_assign_xx!(true, -89, -59);
    }

    macro_rules! test_expr_node_mod_mul_and_assign_xx {
        ($sign:expr, $imm1:expr, $imm2:expr) => {{
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = x1.mod_mul(x2);

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            x1_out.mod_mul_assign(x2);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let mut matrix = gen_dadda_matrix(exp_ec.clone(), &x1.indexes, &x2.indexes, 10);
            let exp = gen_dadda_mult(exp_ec.clone(), &mut matrix);

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = x1.mod_mul($imm1);

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, U10, $sign>::variable(ec2.clone());
            x1_out.mod_mul_assign($imm1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::constant(exp_ec.clone(), $imm1);
            let mut matrix = gen_dadda_matrix(exp_ec.clone(), &x1.indexes, &x2.indexes, 10);
            let exp = gen_dadda_mult(exp_ec.clone(), &mut matrix);

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let res = ($imm2).mod_mul(x1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::constant(exp_ec.clone(), $imm2);
            let mut matrix = gen_dadda_matrix(exp_ec.clone(), &x2.indexes, &x1.indexes, 10);
            let exp = gen_dadda_mult(exp_ec.clone(), &mut matrix);

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    #[test]
    fn test_expr_node_mod_mul_and_assign() {
        test_expr_node_mod_mul_and_assign_xx!(false, 167, 116);
        test_expr_node_mod_mul_and_assign_xx!(true, 83, 38);
        test_expr_node_mod_mul_and_assign_xx!(true, -69, -121);
    }

    #[test]
    fn test_expr_node_fullmul_unsigned() {
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let res = x1.fullmul(x2);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, false>::variable(exp_ec.clone());
            let mut matrix = gen_dadda_matrix(exp_ec.clone(), &x1.indexes, &x2.indexes, 20);
            let exp = gen_dadda_mult(exp_ec.clone(), &mut matrix);

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let res = x1.fullmul(93);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, false>::constant(exp_ec.clone(), 93);
            let mut matrix = gen_dadda_matrix(exp_ec.clone(), &x1.indexes, &x2.indexes, 20);
            let exp = gen_dadda_mult(exp_ec.clone(), &mut matrix);

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let res = 75.fullmul(x1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, false>::constant(exp_ec.clone(), 75);
            let mut matrix = gen_dadda_matrix(exp_ec.clone(), &x2.indexes, &x1.indexes, 20);
            let exp = gen_dadda_mult(exp_ec.clone(), &mut matrix);

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
    }

    fn fullmull_signed_u10(
        x1: ExprNode<isize, U10, true>,
        x2: ExprNode<isize, U10, true>,
    ) -> ExprNode<isize, U20, true> {
        let exp_ec = x1.creator.clone();
        let ux1 = x1.clone().abs();
        let ux2 = x2.clone().abs();
        let mut matrix = gen_dadda_matrix(exp_ec.clone(), &ux1.indexes, &ux2.indexes, 20);
        let temp = ExprNode::<isize, U20, true> {
            creator: exp_ec.clone(),
            indexes: GenericArray::clone_from_slice(&gen_dadda_mult(exp_ec.clone(), &mut matrix)),
        };
        int_ite(x1.bit(9) ^ x2.bit(9), temp.clone().mod_neg(), temp)
    }

    #[test]
    fn test_expr_node_fullmul_signed() {
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let res = x1.fullmul(x2);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, true>::variable(exp_ec.clone());
            let exp = fullmull_signed_u10(x1, x2);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let res = x1.fullmul(-56);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, true>::constant(exp_ec.clone(), -56);
            let exp = fullmull_signed_u10(x1, x2);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let res = (-73).fullmul(x1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, true>::constant(exp_ec.clone(), -73);
            let exp = fullmull_signed_u10(x2, x1);

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
    }

    fn divmod_u10_unsigned(
        x1: ExprNode<isize, U10, false>,
        x2: ExprNode<isize, U10, false>,
    ) -> (
        ExprNode<isize, U10, false>,
        ExprNode<isize, U10, false>,
        BoolExprNode<isize>,
    ) {
        let exp_ec = x1.creator.clone();
        let res = ExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let mul = x2.clone().fullmul(res.clone());
        let modv = ExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let modv_cond = modv.clone().less_than(x2.clone());
        let mulsum = mul.mod_add(ExprNode::<isize, U20, false>::from(modv.clone()));
        let mul_cond = mulsum.subvalue::<U10>(0).equal(x1) & mulsum.subvalue::<U10>(10).equal(0);
        (res, modv, modv_cond & mul_cond)
    }

    macro_rules! test_expr_node_divmod_xx {
        ($sign:expr, $imm1:expr, $imm2:expr, $test_divmod:ident) => {{
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, modr, cond) = x1.divmod(x2);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let (exp_divr, exp_modr, exp_cond) = $test_divmod(x1, x2);

            assert_eq!(exp_divr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_modr.indexes.as_slice(), modr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, modr, cond) = x1.divmod($imm1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::constant(exp_ec.clone(), $imm1);
            let (exp_divr, exp_modr, exp_cond) = $test_divmod(x1, x2);

            assert_eq!(exp_divr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_modr.indexes.as_slice(), modr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, modr, cond) = ($imm2).divmod(x1);

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::constant(exp_ec.clone(), $imm2);
            let (exp_divr, exp_modr, exp_cond) = $test_divmod(x2, x1);

            assert_eq!(exp_divr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_modr.indexes.as_slice(), modr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    fn divmod_u10_signed(
        x1: ExprNode<isize, U10, true>,
        x2: ExprNode<isize, U10, true>,
    ) -> (
        ExprNode<isize, U10, true>,
        ExprNode<isize, U10, true>,
        BoolExprNode<isize>,
    ) {
        let (udiv, umod, cond) = divmod_u10_unsigned(x1.clone().abs(), x2.clone().abs());
        let (sign_a, sign_b) = (x1.bit(9), x2.bit(9));
        let exp_divsign = sign_a.clone() ^ sign_b;
        let divres = int_ite(
            exp_divsign.clone(),
            (udiv.clone().as_signed()).mod_neg(),
            udiv.as_signed(),
        );
        let divres_sign = divres.bit(9);
        (
            divres.clone(),
            int_ite(
                sign_a,
                (umod.clone().as_signed()).mod_neg(),
                umod.as_signed(),
            ),
            cond & (exp_divsign.bequal(divres_sign) | divres.equal(0)),
        )
    }

    #[test]
    fn test_expr_node_divmod() {
        test_expr_node_divmod_xx!(false, 57, 97, divmod_u10_unsigned);
        test_expr_node_divmod_xx!(true, -59, 101, divmod_u10_signed);
    }

    macro_rules! test_expr_node_div_xx {
        ($sign:expr, $imm1:expr, $imm2:expr, $test_divmod:ident) => {{
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, cond) = x1 / x2;

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let (exp_divr, _, exp_cond) = $test_divmod(x1, x2);

            assert_eq!(exp_divr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, cond) = x1 / $imm1;

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::constant(exp_ec.clone(), $imm1);
            let (exp_divr, _, exp_cond) = $test_divmod(x1, x2);

            assert_eq!(exp_divr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, cond) = ($imm2) / x1;

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::constant(exp_ec.clone(), $imm2);
            let (exp_divr, _, exp_cond) = $test_divmod(x2, x1);

            assert_eq!(exp_divr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    #[test]
    fn test_expr_node_div() {
        test_expr_node_div_xx!(false, 76, 134, divmod_u10_unsigned);
        test_expr_node_div_xx!(true, 31, -52, divmod_u10_signed);
    }

    macro_rules! test_expr_node_mod_xx {
        ($sign:expr, $imm1:expr, $imm2:expr, $test_divmod:ident) => {{
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, cond) = x1 % x2;

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let (_, exp_modr, exp_cond) = $test_divmod(x1, x2);

            assert_eq!(exp_modr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, cond) = x1 % $imm1;

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::constant(exp_ec.clone(), $imm1);
            let (_, exp_modr, exp_cond) = $test_divmod(x1, x2);

            assert_eq!(exp_modr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(ec.clone());
            let (divr, cond) = ($imm2) % x1;

            let exp_ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let x2 = ExprNode::<isize, U10, $sign>::constant(exp_ec.clone(), $imm2);
            let (_, exp_modr, exp_cond) = $test_divmod(x2, x1);

            assert_eq!(exp_modr.indexes.as_slice(), divr.indexes.as_slice());
            assert_eq!(exp_cond.index, cond.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    #[test]
    fn test_expr_node_mod() {
        test_expr_node_mod_xx!(false, 99, 173, divmod_u10_unsigned);
        test_expr_node_mod_xx!(true, -81, 57, divmod_u10_signed);
    }
}
