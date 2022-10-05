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

use std::cell::RefCell;
use std::fmt::Debug;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, Sub, SubAssign};
use std::rc::Rc;

use generic_array::typenum::*;
use generic_array::*;

use super::*;
use crate::{impl_int_ipty_ty1, impl_int_upty_ty1};
use crate::{BoolExprNode, ExprCreator, VarLit};

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
        int_ite(self.bit(N::USIZE - 1), -self.clone(), self).as_unsigned()
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
        let mut c = in_carry;
        for i in 0..N::USIZE {
            (output[i], c) = {
                let (s0, c0) = opt_full_adder(self.bit(i), rhs.bit(i), c);
                (s0.index, c0)
            };
        }
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
        let mut c = in_carry;
        for i in 0..N::USIZE - 1 {
            (output[i], c) = {
                let (s0, c0) = opt_full_adder(self.bit(i), rhs.bit(i), c);
                (s0.index, c0)
            };
        }
        output[N::USIZE - 1] = (self.bit(N::USIZE - 1) ^ rhs.bit(N::USIZE - 1) ^ c).index;
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
                let (s0, c0) = opt_full_adder(self.bit(i), rhs.bit(i), c);
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
                let (s0, c0) = opt_full_adder(self.bit(i), !rhs.bit(i), c);
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
        let trueval = BoolExprNode::new(self.creator.clone(), 1);
        (!self).add_same_carry(trueval)
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
                            opt_full_adder(a, b, BoolExprNode::new(creator.clone(), col[src + 2]))
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
            let (s0, c0) = opt_full_adder(
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
        BoolExprNode::new(creator.clone(), col[0]) ^ BoolExprNode::new(creator, col[1]) ^ c
    } else {
        BoolExprNode::new(creator, col[0]) ^ c
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
        let mut matrix =
            gen_dadda_matrix(self.creator.clone(), &self.indexes, &rhs.indexes, N::USIZE);
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
            -res.clone().as_signed(),
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

    fn divmod(
        self,
        rhs: Self,
        get_div: bool,
        get_mod: bool,
    ) -> (Option<Self::Output>, Option<Self::Output>, Self::OutputCond) {
        let divres = ExprNode::<T, N, false>::variable(self.creator.clone());
        let mut matrix = gen_dadda_matrix(
            self.creator.clone(),
            &rhs.indexes,
            &divres.indexes,
            N::USIZE,
        );
        // modv - division modulo
        let modv = ExprNode::<T, N, false>::variable(self.creator.clone());
        let modv_cond = modv.clone().less_than(rhs);

        let mulres = gen_dadda_mult(self.creator.clone(), &mut matrix);
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

        (
            if get_div { Some(divres) } else { None },
            if get_mod { Some(modv) } else { None },
            modv_cond & mulres_cond,
        )
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

    fn divmod(
        self,
        rhs: Self,
        get_div: bool,
        get_mod: bool,
    ) -> (Option<Self::Output>, Option<Self::Output>, Self::OutputCond) {
        let ua = self.clone().abs();
        let ub = rhs.clone().abs();
        let (udiv, umod, cond) = ua.divmod(ub, get_div, get_mod);
        let (sign_a, sign_b) = (self.bit(N::USIZE - 1), rhs.bit(N::USIZE - 1));
        (
            udiv.map(|udiv| {
                int_ite(
                    sign_a.clone() ^ sign_b,
                    -(udiv.clone().as_signed()),
                    udiv.as_signed(),
                )
            }),
            umod.map(|umod| int_ite(sign_a, -(umod.clone().as_signed()), umod.as_signed())),
            cond,
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
                get_div: bool,
                get_mod: bool,
            ) -> (Option<Self::Output>, Option<Self::Output>, Self::OutputCond) {
                let creator = self.creator.clone();
                self.divmod(Self::constant(creator, rhs), get_div, get_mod)
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
                get_div: bool,
                get_mod: bool,
            ) -> (Option<Self::Output>, Option<Self::Output>, Self::OutputCond) {
                let creator = rhs.creator.clone();
                ExprNode::<T, $ty, $sign>::constant(creator, self).divmod(rhs, get_div, get_mod)
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
                let (d, _, c) = self.divmod(rhs, true, false);
                (d.unwrap(), c)
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
                let (_, r, c) = self.divmod(rhs, false, true);
                (r.unwrap(), c)
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
    use crate::boolexpr::test_utils::*;

    #[test]
    fn test_expr_node_neg() {
        let ec = ExprCreator::new();
        let x1 = ExprNode::<isize, U5, true>::variable(ec.clone());
        let res = -x1;

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
}
