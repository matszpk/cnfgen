// bin_arith.rs - integer expression structures.
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
use std::iter;
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Neg, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

use generic_array::typenum::*;
use generic_array::*;

use super::*;
use crate::VarLit;
use crate::{impl_int_ipty, impl_int_ipty_ty1, impl_int_upty, impl_int_upty_ty1};

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
#[macro_export]
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
        let nbits = Self::LOG_BITS;
        // check whether zeroes in sign and in unused bits in Rhs
        if (SIGN2 && *rhs.indexes.last().unwrap() != 0)
            || !rhs.indexes.iter().skip(nbits).all(|x| *x == 0)
        {
            panic!("this arithmetic operation will overflow");
        }
        let nbits = cmp::min(nbits, N2::USIZE - usize::from(SIGN2));

        let mut input = ExprNode {
            creator: self.creator.clone(),
            indexes: GenericArray::default(),
        };
        let mut output = self.clone();
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_left(&mut output.indexes, &input, rhs.bit(i), i);
        }
        output
    }
}

macro_rules! impl_int_shl_imm {
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
                #[allow(unused_comparisons)]
                if rhs < 0 || (rhs as usize) >= N::USIZE {
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

impl_int_upty!(impl_int_shl_imm);
impl_int_ipty!(impl_int_shl_imm);

macro_rules! impl_int_shl_self_imm {
    ($sign:expr, $ty:ty, $bits:ty) => {
        impl<T, N, const SIGN: bool> Shl<ExprNode<T, N, SIGN>> for $ty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            ExprNode<T, $bits, $sign>: IntConstant<T, $ty>,
        {
            type Output = ExprNode<T, $bits, $sign>;

            fn shl(self, rhs: ExprNode<T, N, SIGN>) -> Self::Output {
                ExprNode::<T, $bits, $sign>::constant(rhs.creator.clone(), self) << rhs
            }
        }
    };
}

impl_int_shl_self_imm!(false, u8, U8);
impl_int_shl_self_imm!(false, u16, U16);
impl_int_shl_self_imm!(false, u32, U32);
#[cfg(target_pointer_width = "32")]
impl_int_shl_self_imm!(false, usize, U32);
#[cfg(target_pointer_width = "64")]
impl_int_shl_self_imm!(false, usize, U64);
impl_int_shl_self_imm!(false, u64, U64);
impl_int_shl_self_imm!(false, u128, U128);

impl_int_shl_self_imm!(true, i8, U8);
impl_int_shl_self_imm!(true, i16, U16);
impl_int_shl_self_imm!(true, i32, U32);
#[cfg(target_pointer_width = "32")]
impl_int_shl_self_imm!(true, isize, U32);
#[cfg(target_pointer_width = "64")]
impl_int_shl_self_imm!(true, isize, U64);
impl_int_shl_self_imm!(true, i64, U64);
impl_int_shl_self_imm!(true, i128, U128);

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
        let nbits = Self::LOG_BITS;
        // check whether zeroes in sign and in unused bits in Rhs
        if (SIGN2 && *rhs.indexes.last().unwrap() != 0)
            || !rhs.indexes.iter().skip(nbits).all(|x| *x == 0)
        {
            panic!("this arithmetic operation will overflow");
        }
        let nbits = cmp::min(nbits, N2::USIZE - usize::from(SIGN2));

        let mut input = ExprNode {
            creator: self.creator.clone(),
            indexes: GenericArray::default(),
        };
        let mut output = self.clone();
        for i in 0..nbits {
            std::mem::swap(&mut input, &mut output);
            iter_shift_right(&mut output.indexes, &input, rhs.bit(i), i, SIGN);
        }
        output
    }
}

macro_rules! impl_int_shr_imm {
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
                #[allow(unused_comparisons)]
                if rhs < 0 || (rhs as usize) >= N::USIZE {
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

impl_int_upty!(impl_int_shr_imm);
impl_int_ipty!(impl_int_shr_imm);

macro_rules! impl_int_shr_self_imm {
    ($sign:expr, $ty:ty, $bits:ty) => {
        impl<T, N, const SIGN: bool> Shr<ExprNode<T, N, SIGN>> for $ty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            N: ArrayLength<usize>,
            ExprNode<T, $bits, $sign>: IntConstant<T, $ty>,
        {
            type Output = ExprNode<T, $bits, $sign>;

            fn shr(self, rhs: ExprNode<T, N, SIGN>) -> Self::Output {
                ExprNode::<T, $bits, $sign>::constant(rhs.creator.clone(), self) >> rhs
            }
        }
    };
}

impl_int_shr_self_imm!(false, u8, U8);
impl_int_shr_self_imm!(false, u16, U16);
impl_int_shr_self_imm!(false, u32, U32);
#[cfg(target_pointer_width = "32")]
impl_int_shr_self_imm!(false, usize, U32);
#[cfg(target_pointer_width = "64")]
impl_int_shr_self_imm!(false, usize, U64);
impl_int_shr_self_imm!(false, u64, U64);
impl_int_shr_self_imm!(false, u128, U128);

impl_int_shr_self_imm!(true, i8, U8);
impl_int_shr_self_imm!(true, i16, U16);
impl_int_shr_self_imm!(true, i32, U32);
#[cfg(target_pointer_width = "32")]
impl_int_shr_self_imm!(true, isize, U32);
#[cfg(target_pointer_width = "64")]
impl_int_shr_self_imm!(true, isize, U64);
impl_int_shr_self_imm!(true, i64, U64);
impl_int_shr_self_imm!(true, i128, U128);

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

        impl_int_upty!($macro);
        impl_int_ipty!($macro);
    };
}

impl_int_shx_assign!(ShlAssign, shl, shl_assign, impl_int_shl_assign_imm);
impl_int_shx_assign!(ShrAssign, shr, shr_assign, impl_int_shr_assign_imm);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolexpr::bool_ite;
    use crate::boolexpr::test_utils::*;

    macro_rules! test_expr_node_bitop {
        ($op:ident) => {{
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U6, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U6, false>::variable(ec.clone());
            let res = x1.$op(x2);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 12);
            let exp = (0..6)
                .into_iter()
                .map(|i| (bvs[i].clone().$op(bvs[i + 6].clone())).index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, false>::variable(ec.clone());
            let res = x1.$op(141);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 10);
            let exp = (0..10)
                .into_iter()
                .map(|i| (bvs[i].clone().$op((141 & (1 << i)) != 0)).index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U10, true>::variable(ec.clone());
            let res = (-46).$op(x1);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 10);
            let exp = (0..10)
                .into_iter()
                .map(|i| (bvs[i].clone().$op(((-46) & (1 << i)) != 0)).index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    #[test]
    fn test_expr_node_bitand() {
        test_expr_node_bitop!(bitand);
    }

    #[test]
    fn test_expr_node_bitor() {
        test_expr_node_bitop!(bitor);
    }

    #[test]
    fn test_expr_node_bitxor() {
        test_expr_node_bitop!(bitxor);
    }

    macro_rules! test_expr_node_bitop_assign {
        ($op:ident, $op_assign:ident) => {{
            let ec = ExprCreator::new();
            let mut x1 = ExprNode::<isize, U6, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U6, false>::variable(ec.clone());
            x1.$op_assign(x2);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 12);
            let exp = (0..6)
                .into_iter()
                .map(|i| (bvs[i].clone().$op(bvs[i + 6].clone())).index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), x1.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let mut x1 = ExprNode::<isize, U10, false>::variable(ec.clone());
            x1.$op_assign(141);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 10);
            let exp = (0..10)
                .into_iter()
                .map(|i| (bvs[i].clone().$op((141 & (1 << i)) != 0)).index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), x1.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        {
            let ec = ExprCreator::new();
            let mut x1 = ExprNode::<isize, U10, true>::variable(ec.clone());
            x1.$op_assign(-43);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 10);
            let exp = (0..10)
                .into_iter()
                .map(|i| (bvs[i].clone().$op(((-43) & (1 << i)) != 0)).index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), x1.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }};
    }

    #[test]
    fn test_expr_node_bitand_assign() {
        test_expr_node_bitop_assign!(bitand, bitand_assign);
    }

    #[test]
    fn test_expr_node_bitor_assign() {
        test_expr_node_bitop_assign!(bitor, bitor_assign);
    }

    #[test]
    fn test_expr_node_bitxor_assign() {
        test_expr_node_bitop_assign!(bitxor, bitxor_assign);
    }

    #[test]
    fn test_expr_node_not() {
        let ec = ExprCreator::new();
        let x1 = ExprNode::<isize, U5, false>::variable(ec.clone());
        let res = !x1;

        let exp_ec = ExprCreator::new();
        let bvs = alloc_boolvars(exp_ec.clone(), 5);
        let exp = (0..5)
            .into_iter()
            .map(|i| (!bvs[i].clone()).index)
            .collect::<Vec<_>>();

        assert_eq!(exp.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    fn shift_left_bits(
        bits: usize,
        bvs: &[BoolExprNode<isize>],
        cond: BoolExprNode<isize>,
        shift: usize,
    ) -> Vec<BoolExprNode<isize>> {
        (0..bits)
            .into_iter()
            .map(|i| {
                bool_ite(
                    cond.clone(),
                    if i >= shift {
                        bvs[i - shift].clone()
                    } else {
                        BoolExprNode::single_value(cond.creator.clone(), false)
                    },
                    bvs[i].clone(),
                )
            })
            .collect::<Vec<_>>()
    }

    macro_rules! test_expr_node_shl_assign_3 {
        ($sign:expr, $signrhs:expr, $ty:ty, $torhs:ty, $bits:expr) => {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, $ty, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U3, false>::variable(ec.clone()),
            );
            let res = x1 << x2;

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, $ty, $sign>::variable(ec2.clone());
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U3, false>::variable(ec2.clone()),
            );
            x1_out <<= x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), $bits + 3);
            let stage1 = shift_left_bits($bits, &bvs[0..$bits], bvs[$bits].clone(), 1);
            let stage2 = shift_left_bits($bits, &stage1[0..$bits], bvs[$bits + 1].clone(), 2);
            let exp = shift_left_bits($bits, &stage2[0..$bits], bvs[$bits + 2].clone(), 4)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        };
    }

    macro_rules! test_expr_node_shl_imm_3 {
        ($sign:expr, $signrhs:expr, $ty:ty, $pty:ty, $torhs:ty, $bits:expr, $imm:expr) => {
            let ec = ExprCreator::new();
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U3, false>::variable(ec.clone()),
            );
            let res: ExprNode<isize, $ty, $sign> = ($imm as $pty) << x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 3);
            let immnodes = (0..$bits)
                .into_iter()
                .map(|i| BoolExprNode::single_value(exp_ec.clone(), (($imm & (1 << i)) != 0)))
                .collect::<Vec<_>>();
            let stage1 = shift_left_bits($bits, &immnodes, bvs[0].clone(), 1);
            let stage2 = shift_left_bits($bits, &stage1[0..$bits], bvs[1].clone(), 2);
            let exp = shift_left_bits($bits, &stage2[0..$bits], bvs[2].clone(), 4)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    macro_rules! test_expr_node_shl_assign_rhs_imm {
        ($sign:expr, $ty:ty, $bits:expr, $shift:expr, $rhs_pty:ty) => {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, $ty, $sign>::variable(ec.clone());
            let res = x1 << (($shift) as $rhs_pty);

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, $ty, $sign>::variable(ec2.clone());
            x1_out <<= (($shift) as $rhs_pty);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), $bits);
            let exp = (0..$bits).into_iter().map(|x|
                                        if x >= $shift {
                                            bvs[x - $shift].clone()
                                        } else {
                                            BoolExprNode::single_value(exp_ec.clone(), false)
                                        }.index).collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        };
    }

    macro_rules! test_expr_node_shl_assign_5 {
        ($sign:expr, $signrhs:expr, $ty:ty, $torhs:ty, $bits:expr) => {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, $ty, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U5, false>::variable(ec.clone()),
            );
            let res = x1 << x2;

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, $ty, $sign>::variable(ec2.clone());
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U5, false>::variable(ec2.clone()),
            );
            x1_out <<= x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), $bits + 5);
            let stage1 = shift_left_bits($bits, &bvs[0..$bits], bvs[$bits].clone(), 1);
            let stage2 = shift_left_bits($bits, &stage1[0..$bits], bvs[$bits + 1].clone(), 2);
            let stage3 = shift_left_bits($bits, &stage2[0..$bits], bvs[$bits + 2].clone(), 4);
            let stage4 = shift_left_bits($bits, &stage3[0..$bits], bvs[$bits + 3].clone(), 8);
            let exp = shift_left_bits($bits, &stage4[0..$bits], bvs[$bits + 4].clone(), 16)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        };
    }

    macro_rules! test_expr_node_shl_imm_5 {
        ($sign:expr, $signrhs:expr, $ty:ty, $pty:ty, $torhs:ty, $bits:expr, $imm:expr) => {
            let ec = ExprCreator::new();
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U5, false>::variable(ec.clone()),
            );
            let res: ExprNode<isize, $ty, $sign> = ($imm as $pty) << x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 5);
            let immnodes = (0..$bits)
                .into_iter()
                .map(|i| BoolExprNode::single_value(exp_ec.clone(), (($imm & (1 << i)) != 0)))
                .collect::<Vec<_>>();
            let stage1 = shift_left_bits($bits, &immnodes, bvs[0].clone(), 1);
            let stage2 = shift_left_bits($bits, &stage1[0..$bits], bvs[1].clone(), 2);
            let stage3 = shift_left_bits($bits, &stage2[0..$bits], bvs[2].clone(), 4);
            let stage4 = shift_left_bits($bits, &stage3[0..$bits], bvs[3].clone(), 8);
            let exp = shift_left_bits($bits, &stage4[0..$bits], bvs[4].clone(), 16)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_shl_and_shl_assign() {
        test_expr_node_shl_assign_3!(false, false, U6, U3, 6);
        test_expr_node_shl_assign_3!(false, false, U8, U3, 8);
        test_expr_node_shl_assign_3!(false, false, U6, U5, 6);
        test_expr_node_shl_assign_3!(false, false, U8, U5, 8);
        test_expr_node_shl_assign_3!(true, false, U6, U3, 6);
        test_expr_node_shl_assign_3!(true, false, U8, U3, 8);
        test_expr_node_shl_assign_3!(true, false, U6, U5, 6);
        test_expr_node_shl_assign_3!(true, false, U8, U5, 8);

        test_expr_node_shl_assign_3!(false, true, U6, U4, 6);
        test_expr_node_shl_assign_3!(false, true, U8, U4, 8);
        test_expr_node_shl_assign_3!(true, true, U6, U4, 6);
        test_expr_node_shl_assign_3!(true, true, U8, U4, 8);

        // lhs is immediate - constant
        test_expr_node_shl_imm_3!(false, false, U8, u8, U3, 8, 172);
        test_expr_node_shl_imm_3!(false, false, U8, u8, U5, 8, 217);
        test_expr_node_shl_imm_3!(true, false, U8, i8, U3, 8, 72);
        test_expr_node_shl_imm_3!(true, false, U8, i8, U5, 8, 99);

        test_expr_node_shl_imm_3!(false, true, U8, u8, U4, 8, 172);
        test_expr_node_shl_imm_3!(true, true, U8, i8, U4, 8, 72);

        {
            // check if rhs have lower number of bits
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U8, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U2, false>::variable(ec.clone());
            let res = x1 << x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 8 + 2);
            let stage1 = shift_left_bits(8, &bvs[0..8], bvs[8].clone(), 1);
            let exp = shift_left_bits(8, &stage1[0..8], bvs[8 + 1].clone(), 2)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        test_expr_node_shl_assign_5!(false, false, U27, U5, 27);
        test_expr_node_shl_assign_5!(false, false, U32, U5, 32);
        test_expr_node_shl_assign_5!(false, false, U27, U8, 27);
        test_expr_node_shl_assign_5!(false, false, U32, U8, 32);

        test_expr_node_shl_assign_5!(true, false, U27, U5, 27);
        test_expr_node_shl_assign_5!(true, false, U32, U5, 32);
        test_expr_node_shl_assign_5!(true, false, U27, U8, 27);
        test_expr_node_shl_assign_5!(true, false, U32, U8, 32);

        test_expr_node_shl_assign_5!(false, true, U27, U6, 27);
        test_expr_node_shl_assign_5!(false, true, U32, U6, 32);
        test_expr_node_shl_assign_5!(true, true, U27, U6, 27);
        test_expr_node_shl_assign_5!(true, true, U32, U6, 32);

        // lhs is immediate - constant
        test_expr_node_shl_imm_5!(false, false, U32, u32, U5, 32, 2016568312);
        test_expr_node_shl_imm_5!(true, false, U32, i32, U5, 32, 1016068072);
        test_expr_node_shl_imm_5!(false, false, U32, u32, U7, 32, 2016568312);
        test_expr_node_shl_imm_5!(true, false, U32, i32, U7, 32, 1016068072);

        test_expr_node_shl_imm_5!(false, true, U32, u32, U6, 32, 2016568312);
        test_expr_node_shl_imm_5!(true, true, U32, i32, U6, 32, 1016068072);

        {
            // check if rhs have lower number of bits
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U32, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U3, false>::variable(ec.clone());
            let res = x1 << x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 32 + 3);
            let stage1 = shift_left_bits(32, &bvs[0..32], bvs[32].clone(), 1);
            let stage2 = shift_left_bits(32, &stage1[0..32], bvs[32 + 1].clone(), 2);
            let exp = shift_left_bits(32, &stage2[0..32], bvs[32 + 2].clone(), 4)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        // rhs is constant - immediate
        test_expr_node_shl_assign_rhs_imm!(false, U8, 8, 5, u8);
        test_expr_node_shl_assign_rhs_imm!(true, U8, 8, 5, u8);
        test_expr_node_shl_assign_rhs_imm!(false, U8, 8, 5, i8);
        test_expr_node_shl_assign_rhs_imm!(false, U8, 8, 5, u16);
        test_expr_node_shl_assign_rhs_imm!(false, U32, 32, 19, u8);
        test_expr_node_shl_assign_rhs_imm!(true, U32, 32, 19, u8);
    }

    fn shift_right_bits(
        bits: usize,
        bvs: &[BoolExprNode<isize>],
        cond: BoolExprNode<isize>,
        shift: usize,
        lhs_sign: bool,
    ) -> Vec<BoolExprNode<isize>> {
        (0..bits)
            .into_iter()
            .map(|i| {
                bool_ite(
                    cond.clone(),
                    if i + shift < bits {
                        bvs[i + shift].clone()
                    } else {
                        if lhs_sign {
                            bvs[bits - 1].clone()
                        } else {
                            BoolExprNode::single_value(cond.creator.clone(), false)
                        }
                    },
                    bvs[i].clone(),
                )
            })
            .collect::<Vec<_>>()
    }

    macro_rules! test_expr_node_shr_assign_3 {
        ($sign:expr, $signrhs:expr, $ty:ty, $torhs:ty, $bits:expr) => {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, $ty, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U3, false>::variable(ec.clone()),
            );
            let res = x1 >> x2;

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, $ty, $sign>::variable(ec2.clone());
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U3, false>::variable(ec2.clone()),
            );
            x1_out >>= x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), $bits + 3);
            let stage1 = shift_right_bits($bits, &bvs[0..$bits], bvs[$bits].clone(), 1, $sign);
            let stage2 =
                shift_right_bits($bits, &stage1[0..$bits], bvs[$bits + 1].clone(), 2, $sign);
            let exp = shift_right_bits($bits, &stage2[0..$bits], bvs[$bits + 2].clone(), 4, $sign)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        };
    }

    macro_rules! test_expr_node_shr_imm_3 {
        ($sign:expr, $signrhs:expr, $ty:ty, $pty:ty, $torhs:ty, $bits:expr, $imm:expr) => {
            let ec = ExprCreator::new();
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U3, false>::variable(ec.clone()),
            );
            let res: ExprNode<isize, $ty, $sign> = ($imm as $pty) >> x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 3);
            let immnodes = (0..$bits)
                .into_iter()
                .map(|i| BoolExprNode::single_value(exp_ec.clone(), (($imm & (1 << i)) != 0)))
                .collect::<Vec<_>>();
            let stage1 = shift_right_bits($bits, &immnodes, bvs[0].clone(), 1, $sign);
            let stage2 = shift_right_bits($bits, &stage1[0..$bits], bvs[1].clone(), 2, $sign);
            let exp = shift_right_bits($bits, &stage2[0..$bits], bvs[2].clone(), 4, $sign)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    macro_rules! test_expr_node_shr_assign_rhs_imm {
        ($sign:expr, $ty:ty, $bits:expr, $shift:expr, $rhs_pty:ty) => {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, $ty, $sign>::variable(ec.clone());
            let res = x1 >> (($shift) as $rhs_pty);

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, $ty, $sign>::variable(ec2.clone());
            x1_out >>= (($shift) as $rhs_pty);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), $bits);
            let exp = (0..$bits).into_iter().map(|x|
                                        if x + $shift < $bits {
                                            bvs[x + $shift].clone()
                                        } else {
                                            if $sign {
                                                bvs[$bits - 1].clone()
                                            } else {
                                                BoolExprNode::single_value(exp_ec.clone(), false)
                                            }
                                        }.index).collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        };
    }

    macro_rules! test_expr_node_shr_assign_5 {
        ($sign:expr, $signrhs:expr, $ty:ty, $torhs:ty, $bits:expr) => {
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, $ty, $sign>::variable(ec.clone());
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U5, false>::variable(ec.clone()),
            );
            let res = x1 >> x2;

            let ec2 = ExprCreator::new();
            let mut x1_out = ExprNode::<isize, $ty, $sign>::variable(ec2.clone());
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U5, false>::variable(ec2.clone()),
            );
            x1_out >>= x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), $bits + 5);
            let stage1 = shift_right_bits($bits, &bvs[0..$bits], bvs[$bits].clone(), 1, $sign);
            let stage2 =
                shift_right_bits($bits, &stage1[0..$bits], bvs[$bits + 1].clone(), 2, $sign);
            let stage3 =
                shift_right_bits($bits, &stage2[0..$bits], bvs[$bits + 2].clone(), 4, $sign);
            let stage4 =
                shift_right_bits($bits, &stage3[0..$bits], bvs[$bits + 3].clone(), 8, $sign);
            let exp = shift_right_bits($bits, &stage4[0..$bits], bvs[$bits + 4].clone(), 16, $sign)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            assert_eq!(exp.as_slice(), x1_out.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec2.borrow());
        };
    }

    macro_rules! test_expr_node_shr_imm_5 {
        ($sign:expr, $signrhs:expr, $ty:ty, $pty:ty, $torhs:ty, $bits:expr, $imm:expr) => {
            let ec = ExprCreator::new();
            let x2 = ExprNode::<isize, $torhs, $signrhs>::from(
                ExprNode::<isize, U5, false>::variable(ec.clone()),
            );
            let res: ExprNode<isize, $ty, $sign> = ($imm as $pty) >> x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 5);
            let immnodes = (0..$bits)
                .into_iter()
                .map(|i| BoolExprNode::single_value(exp_ec.clone(), (($imm & (1 << i)) != 0)))
                .collect::<Vec<_>>();
            let stage1 = shift_right_bits($bits, &immnodes, bvs[0].clone(), 1, $sign);
            let stage2 = shift_right_bits($bits, &stage1[0..$bits], bvs[1].clone(), 2, $sign);
            let stage3 = shift_right_bits($bits, &stage2[0..$bits], bvs[2].clone(), 4, $sign);
            let stage4 = shift_right_bits($bits, &stage3[0..$bits], bvs[3].clone(), 8, $sign);
            let exp = shift_right_bits($bits, &stage4[0..$bits], bvs[4].clone(), 16, $sign)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_shr_and_shr_assign() {
        test_expr_node_shr_assign_3!(false, false, U6, U3, 6);
        test_expr_node_shr_assign_3!(false, false, U8, U3, 8);
        test_expr_node_shr_assign_3!(false, false, U6, U5, 6);
        test_expr_node_shr_assign_3!(false, false, U8, U5, 8);
        test_expr_node_shr_assign_3!(true, false, U6, U3, 6);
        test_expr_node_shr_assign_3!(true, false, U8, U3, 8);
        test_expr_node_shr_assign_3!(true, false, U6, U5, 6);
        test_expr_node_shr_assign_3!(true, false, U8, U5, 8);

        test_expr_node_shr_assign_3!(false, true, U6, U4, 6);
        test_expr_node_shr_assign_3!(false, true, U8, U4, 8);
        test_expr_node_shr_assign_3!(true, true, U6, U4, 6);
        test_expr_node_shr_assign_3!(true, true, U8, U4, 8);

        // lhs is immediate - constant
        test_expr_node_shr_imm_3!(false, false, U8, u8, U3, 8, 172);
        test_expr_node_shr_imm_3!(false, false, U8, u8, U5, 8, 217);
        test_expr_node_shr_imm_3!(true, false, U8, i8, U3, 8, -72);
        test_expr_node_shr_imm_3!(true, false, U8, i8, U5, 8, 99);

        test_expr_node_shr_imm_3!(false, true, U8, u8, U4, 8, 172);
        test_expr_node_shr_imm_3!(true, true, U8, i8, U4, 8, 72);
        test_expr_node_shr_imm_3!(true, true, U8, i8, U4, 8, -67);

        {
            // check if rhs have lower number of bits
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U8, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U2, false>::variable(ec.clone());
            let res = x1 >> x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 8 + 2);
            let stage1 = shift_right_bits(8, &bvs[0..8], bvs[8].clone(), 1, false);
            let exp = shift_right_bits(8, &stage1[0..8], bvs[8 + 1].clone(), 2, false)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        test_expr_node_shr_assign_5!(false, false, U27, U5, 27);
        test_expr_node_shr_assign_5!(false, false, U32, U5, 32);
        test_expr_node_shr_assign_5!(false, false, U27, U8, 27);
        test_expr_node_shr_assign_5!(false, false, U32, U8, 32);

        test_expr_node_shr_assign_5!(true, false, U27, U5, 27);
        test_expr_node_shr_assign_5!(true, false, U32, U5, 32);
        test_expr_node_shr_assign_5!(true, false, U27, U8, 27);
        test_expr_node_shr_assign_5!(true, false, U32, U8, 32);

        test_expr_node_shr_assign_5!(false, true, U27, U6, 27);
        test_expr_node_shr_assign_5!(false, true, U32, U6, 32);
        test_expr_node_shr_assign_5!(true, true, U27, U6, 27);
        test_expr_node_shr_assign_5!(true, true, U32, U6, 32);

        // lhs is immediate - constant
        test_expr_node_shr_imm_5!(false, false, U32, u32, U5, 32, 2016568312);
        test_expr_node_shr_imm_5!(true, false, U32, i32, U5, 32, 1016068072);
        test_expr_node_shr_imm_5!(false, false, U32, u32, U7, 32, 2016568312);
        test_expr_node_shr_imm_5!(true, false, U32, i32, U7, 32, -116068072);
        test_expr_node_shr_imm_5!(true, false, U32, i32, U7, 32, 916068072);

        test_expr_node_shr_imm_5!(false, true, U32, u32, U6, 32, 2016568312);
        test_expr_node_shr_imm_5!(true, true, U32, i32, U6, 32, 1016068072);
        test_expr_node_shr_imm_5!(true, true, U32, i32, U6, 32, -905811331);

        {
            // check if rhs have lower number of bits
            let ec = ExprCreator::new();
            let x1 = ExprNode::<isize, U32, false>::variable(ec.clone());
            let x2 = ExprNode::<isize, U3, false>::variable(ec.clone());
            let res = x1 >> x2;

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 32 + 3);
            let stage1 = shift_right_bits(32, &bvs[0..32], bvs[32].clone(), 1, false);
            let stage2 = shift_right_bits(32, &stage1[0..32], bvs[32 + 1].clone(), 2, false);
            let exp = shift_right_bits(32, &stage2[0..32], bvs[32 + 2].clone(), 4, false)
                .into_iter()
                .map(|x| x.index)
                .collect::<Vec<_>>();

            assert_eq!(exp.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }

        // rhs is constant - immediate
        test_expr_node_shr_assign_rhs_imm!(false, U8, 8, 5, u8);
        test_expr_node_shr_assign_rhs_imm!(true, U8, 8, 5, u8);
        test_expr_node_shr_assign_rhs_imm!(false, U8, 8, 5, i8);
        test_expr_node_shr_assign_rhs_imm!(false, U8, 8, 5, u16);
        test_expr_node_shr_assign_rhs_imm!(false, U32, 32, 19, u8);
        test_expr_node_shr_assign_rhs_imm!(true, U32, 32, 19, u8);
    }
}
