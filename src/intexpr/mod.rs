// mod.rs - integer expression structures.
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
use std::iter;
use std::ops::{Add, BitAnd, BitOr, Neg, Not, Sub};
use std::rc::Rc;

use generic_array::typenum::*;
use generic_array::*;

use crate::boolexpr::half_adder;
use crate::int_utils::*;
use crate::{impl_int_bitop_assign, impl_int_ty1_lt_ty2};
use crate::{BoolExprNode, DynIntExprNode, ExprCreator, Literal, VarLit};

/// Integer error.
#[derive(thiserror::Error, Debug)]
pub enum IntError {
    /// If bit overflow - too many bits required.
    #[error("Bit overflow")]
    BitOverflow,
    /// A value can be negative - it can be happened when convert signed value into unsigned.
    #[error("Value can be negative")]
    CanBeNegative,
    #[error("Bit number mismatch")]
    BitsMismatch,
}

pub mod traits;
pub use traits::*;
pub mod bin_arith;
pub use bin_arith::*;
pub mod int_arith;
pub use int_arith::*;

// IntExprNode - main node
//
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntExprNode<T: VarLit + Debug, N: ArrayLength<usize>, const SIGN: bool> {
    pub(super) creator: Rc<RefCell<ExprCreator<T>>>,
    pub(super) indexes: GenericArray<usize, N>,
}

impl<T, N: ArrayLength<usize>, const SIGN: bool> IntExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Number of BITS.
    pub const BITS: usize = N::USIZE;
    /// SIGN of integer. It can be false - unsigned, or true - signed.
    pub const SIGN: bool = SIGN;
    /// Internally used logarithm of number of bits.
    pub const LOG_BITS: usize = calc_log_bits(Self::BITS);

    /// Creates new variable as expression node.
    pub fn variable(creator: Rc<RefCell<ExprCreator<T>>>) -> Self {
        let mut indexes = GenericArray::<usize, N>::default();
        {
            let mut creator = creator.borrow_mut();
            indexes.iter_mut().for_each(|x| {
                let l = creator.new_variable();
                *x = creator.single(l);
            });
        }
        IntExprNode { creator, indexes }
    }

    /// Creates integer from boolean expressions. An argument is object convertible into
    /// iterator of `BoolExprNode`.
    pub fn from_boolexprs(iter: impl IntoIterator<Item = BoolExprNode<T>>) -> Option<Self> {
        let mut creator = None;
        GenericArray::from_exact_iter(iter.into_iter().map(|x| {
            // check creator - whether this same
            if let Some(c) = creator.clone() {
                assert_eq!(Rc::as_ptr(&c), Rc::as_ptr(&x.creator));
            } else {
                creator = Some(x.creator.clone());
            }
            x.index
        }))
        .map(|indexes| IntExprNode {
            creator: creator.unwrap(),
            indexes,
        })
    }

    /// Creates filled integer from from Literal.
    pub fn filled(creator: Rc<RefCell<ExprCreator<T>>>, v: impl Into<Literal<T>>) -> Self {
        IntExprNode {
            creator: creator.clone(),
            indexes: GenericArray::from_exact_iter(
                iter::repeat(creator.borrow_mut().single(v)).take(N::USIZE),
            )
            .unwrap(),
        }
    }

    /// Creates filled integer from from a boolean value.
    pub fn filled_expr(v: BoolExprNode<T>) -> Self {
        IntExprNode {
            creator: v.creator.clone(),
            indexes: GenericArray::from_exact_iter(iter::repeat(v.index).take(N::USIZE)).unwrap(),
        }
    }

    /// Casts integer into unsigned integer.
    pub fn as_unsigned(self) -> IntExprNode<T, N, false> {
        IntExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }

    /// Casts integer into signed integer.
    pub fn as_signed(self) -> IntExprNode<T, N, true> {
        IntExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }
}

impl<T, N: ArrayLength<usize>> IntExprNode<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer that contains `N2` bits starting from `start`.
    pub fn subvalue<N2>(&self, start: usize) -> IntExprNode<T, N2, false>
    where
        N2: ArrayLength<usize>,
    {
        IntExprNode {
            creator: self.creator.clone(),
            indexes: GenericArray::clone_from_slice(&self.indexes[start..start + N2::USIZE]),
        }
    }

    /// Creates integer that contains `N2` selected bits. List of bits given in
    /// object that can be converted into iterator of indexes. It returns None if
    /// number of elements in iterator doesn't match.
    pub fn select_bits<N2, I>(&self, iter: I) -> Option<IntExprNode<T, N2, false>>
    where
        N2: ArrayLength<usize>,
        I: IntoIterator<Item = usize>,
    {
        GenericArray::from_exact_iter(iter.into_iter().map(|x| self.indexes[x])).map(|indexes| {
            IntExprNode {
                creator: self.creator.clone(),
                indexes,
            }
        })
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn concat<N2>(self, rest: IntExprNode<T, N2, false>) -> IntExprNode<T, Sum<N, N2>, false>
    where
        N: Add<N2>,
        N2: ArrayLength<usize>,
        Sum<N, N2>: ArrayLength<usize>,
    {
        use generic_array::sequence::*;
        assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rest.creator));
        IntExprNode {
            creator: self.creator,
            indexes: self.indexes.concat(rest.indexes),
        }
    }

    /// Splits integer into two parts: the first with `K` bits and second with rest of bits.
    pub fn split<K>(
        self,
    ) -> (
        IntExprNode<T, K, false>,
        IntExprNode<T, operator_aliases::Diff<N, K>, false>,
    )
    where
        N: Sub<K>,
        K: ArrayLength<usize>,
        operator_aliases::Diff<N, K>: ArrayLength<usize>,
    {
        use generic_array::sequence::*;
        let (indexes1, indexes2) = self.indexes.split();
        (
            IntExprNode {
                creator: self.creator.clone(),
                indexes: indexes1,
            },
            IntExprNode {
                creator: self.creator,
                indexes: indexes2,
            },
        )
    }
}

// TryFrom implementation
macro_rules! impl_int_try_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                TryFrom<IntExprNode<T, $ty2, SIGN2>> for IntExprNode<T, $ty1, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntExprNode<T, $ty2, SIGN2>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                // if all rest of bits are 0 - just false
                if !v.indexes.iter().skip(len1).all(|x| *x==0) {
                    return Err(IntError::BitOverflow);
                }
                Ok(IntExprNode::<T, $ty1, false>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntExprNode<T, $ty2, false>> for IntExprNode<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntExprNode<T, $ty2, false>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                // if all rest of bits are 0 - just false
                if !v.indexes.iter().skip(len1-1).all(|x| *x==0) {
                    return Err(IntError::BitOverflow);
                }
                Ok(IntExprNode::<T, $ty1, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntExprNode<T, $ty2, true>> for IntExprNode<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntExprNode<T, $ty2, true>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                let last_idx = v.indexes[len1-1];
                if !v.indexes.iter().skip(len1).all(|x| last_idx==*x) {
                    return Err(IntError::BitOverflow);
                }
                Ok(IntExprNode::<T, $ty1, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        // try from for rest
        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntExprNode<T, $ty1, true>> for IntExprNode<T, $ty2, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntExprNode<T, $ty1, true>) -> Result<Self, Self::Error> {
                if *v.indexes.last().unwrap() != 0 {
                    return Err(IntError::CanBeNegative); // if minus
                }
                // default is zero - then is false - zero bit value
                let mut new_v = IntExprNode::<T, $ty2, false>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                new_v.indexes[0..v.indexes.len()].copy_from_slice(v.indexes.as_slice());
                Ok(new_v)
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_try_from);

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<IntExprNode<T, N, false>>
    for IntExprNode<T, N, true>
{
    type Error = IntError;

    fn try_from(v: IntExprNode<T, N, false>) -> Result<Self, Self::Error> {
        if *v.indexes.last().unwrap() != 0 {
            // if input if higher than possible output
            return Err(IntError::BitOverflow);
        }
        Ok(IntExprNode {
            creator: v.creator,
            indexes: v.indexes,
        })
    }
}

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<IntExprNode<T, N, true>>
    for IntExprNode<T, N, false>
{
    type Error = IntError;

    fn try_from(v: IntExprNode<T, N, true>) -> Result<Self, Self::Error> {
        if *v.indexes.last().unwrap() != 0 {
            // if input is lower than 0
            return Err(IntError::CanBeNegative);
        }
        Ok(IntExprNode {
            creator: v.creator,
            indexes: v.indexes,
        })
    }
}

impl<T: VarLit, N: ArrayLength<usize>, const SIGN: bool> TryFrom<DynIntExprNode<T, SIGN>>
    for IntExprNode<T, N, SIGN>
{
    type Error = IntError;

    fn try_from(v: DynIntExprNode<T, SIGN>) -> Result<Self, Self::Error> {
        if N::USIZE != v.indexes.len() {
            return Err(IntError::BitsMismatch);
        }
        Ok(IntExprNode {
            creator: v.creator,
            indexes: GenericArray::clone_from_slice(&v.indexes),
        })
    }
}

// From implementation
macro_rules! impl_int_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                From<IntExprNode<T, $ty1, false>> for IntExprNode<T, $ty2, SIGN2>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: IntExprNode<T, $ty1, false>) -> Self {
                // default is zero - then is false - zero bit value
                let mut new_v = IntExprNode::<T, $ty2, SIGN2>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                new_v.indexes[0..v.indexes.len()].copy_from_slice(v.indexes.as_slice());
                new_v
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                From<IntExprNode<T, $ty1, true>> for IntExprNode<T, $ty2, true>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: IntExprNode<T, $ty1, true>) -> Self {
                // default is zero - then is false - zero bit value
                let len = <$ty1>::USIZE;
                let mut new_v = IntExprNode::<T, $ty2, true>{ creator: v.creator.clone(),
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

// types

pub type U8ExprNode<T> = IntExprNode<T, U8, false>;
pub type U16ExprNode<T> = IntExprNode<T, U16, false>;
pub type U32ExprNode<T> = IntExprNode<T, U32, false>;
pub type U64ExprNode<T> = IntExprNode<T, U64, false>;
pub type U128ExprNode<T> = IntExprNode<T, U128, false>;

pub type UExprNode<T, N> = IntExprNode<T, N, false>;
pub type IExprNode<T, N> = IntExprNode<T, N, true>;

pub type I8ExprNode<T> = IntExprNode<T, U8, true>;
pub type I16ExprNode<T> = IntExprNode<T, U16, true>;
pub type I32ExprNode<T> = IntExprNode<T, U32, true>;
pub type I64ExprNode<T> = IntExprNode<T, U64, true>;
pub type I128ExprNode<T> = IntExprNode<T, U128, true>;

/// Returns result of the If-Then-Else (ITE) - integer version.
pub fn int_ite<C, T, E>(
    c: C,
    t: T,
    e: E,
) -> <<T as BitAnd>::Output as BitOr<<E as BitAnd>::Output>>::Output
where
    C: Not + Clone,
    T: BitAnd + BitMask<C>,
    E: BitAnd + BitMask<<C as Not>::Output>,
    <T as BitAnd<T>>::Output: BitOr<<E as BitAnd<E>>::Output>,
{
    (<T as BitMask<C>>::bitmask(c.clone()) & t)
        | (<E as BitMask<<C as Not>::Output>>::bitmask(!c) & e)
}

pub fn int_table<T, N, K, I, const SIGN: bool>(
    index: IntExprNode<T, K, SIGN>,
    table_iter: I,
) -> IntExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = IntExprNode<T, N, SIGN>>,
{
    let mut ites = vec![];
    let mut iter = table_iter.into_iter();
    while let Some(v) = iter.next() {
        if let Some(v2) = iter.next() {
            ites.push(int_ite(index.bit(0), v2, v));
        } else {
            panic!("Odd number of elements");
        }
    }

    for step in 1..K::USIZE {
        if (ites.len() & 1) != 0 {
            panic!("Odd number of elements");
        }
        for i in 0..(ites.len() >> 1) {
            ites[i] = int_ite(
                index.bit(step),
                ites[(i << 1) + 1].clone(),
                ites[(i << 1)].clone(),
            );
        }
        ites.resize(
            ites.len() >> 1,
            IntExprNode::filled(index.creator.clone(), false),
        );
    }

    ites.pop().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BoolExprNode;

    #[test]
    fn test_expr_node() {
        let ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U8, false>::variable(ec.clone());
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9], *x1.indexes);
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9], *(x1.clone().as_signed()).indexes);
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9], *(x1.as_unsigned()).indexes);
        let x2 = IntExprNode::<isize, U8, true>::variable(ec.clone());
        assert_eq!([10, 11, 12, 13, 14, 15, 16, 17], *x2.indexes);
        assert_eq!(
            [10, 11, 12, 13, 14, 15, 16, 17],
            *(x2.clone().as_unsigned()).indexes
        );
        assert_eq!([10, 11, 12, 13, 14, 15, 16, 17], *(x2.as_signed()).indexes);

        let b1 = BoolExprNode::variable(ec.clone());
        let x3 = IntExprNode::<isize, U4, false>::filled(ec.clone(), b1.varlit().unwrap());
        assert_eq!([18, 18, 18, 18], *x3.indexes);
        let b1 = BoolExprNode::variable(ec.clone());
        let b2 = BoolExprNode::variable(ec.clone());
        let bxp = b1.clone() ^ b2.clone();
        let x4 = IntExprNode::<isize, U4, false>::filled_expr(bxp.clone());
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

        let x5 = IntExprNode::<isize, U8, false>::from_boolexprs(bxps.clone()).unwrap();
        assert_eq!(
            bxps.iter().map(|x| x.index).collect::<Vec<_>>().as_slice(),
            x5.indexes.as_slice()
        );
    }

    #[test]
    fn test_expr_node_manip() {
        let ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U16, false>::variable(ec.clone());
        let x2 = x1.subvalue::<U6>(7);
        assert_eq!([9, 10, 11, 12, 13, 14], *x2.indexes);
        let x3 = x1
            .select_bits::<U9, _>([3, 8, 9, 0, 3, 4, 12, 14, 15])
            .unwrap();
        assert_eq!([5, 10, 11, 2, 5, 6, 14, 16, 17], *x3.indexes);
        assert_eq!(None, x1.select_bits::<U9, _>([3, 8, 9, 0, 3, 4, 12, 14]));
        assert_eq!(
            None,
            x1.select_bits::<U9, _>([3, 8, 9, 0, 3, 4, 12, 14, 15, 0])
        );

        let y1 = IntExprNode::<isize, U8, false>::variable(ec.clone());
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
        let (xt1, xt2) = z1.split::<U5>();
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
    fn test_expr_node_from() {
        let ec = ExprCreator::new();
        // Unsigned N -> Unsigned N+X
        let x1 = IntExprNode::<isize, U8, false>::variable(ec.clone());
        let x2 = IntExprNode::<isize, U14, false>::from(x1.clone());
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0], *x2.indexes);
        // Unsigned N -> Signed N+X
        let ix2 = IntExprNode::<isize, U14, true>::from(x1.clone());
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0], *ix2.indexes);
        let ix1 = IntExprNode::<isize, U8, true>::variable(ec.clone());
        // Signed N, where SIGN=var -> Signed N+X
        let ix2 = IntExprNode::<isize, U12, true>::from(ix1.clone());
        assert_eq!(
            [10, 11, 12, 13, 14, 15, 16, 17, 17, 17, 17, 17],
            *ix2.indexes
        );
    }

    #[test]
    fn test_expr_node_try_from_dynint_expr_node() {
        use crate::DynIntExprNode;
        let ec = ExprCreator::new();
        let dix1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 10);
        let ix1 = IntExprNode::<isize, U10, false>::try_from(dix1.clone()).unwrap();
        assert_eq!(ix1.indexes.as_slice(), dix1.indexes.as_slice());
    }

    #[test]
    fn test_expr_node_try_from() {
        let ec = ExprCreator::new();
        let ix1 = IntExprNode::<isize, U8, true>::from(IntExprNode::<isize, U7, false>::variable(
            ec.clone(),
        ));
        // Signed N, SIGN=0 -> Unsigned N
        let x1 = IntExprNode::<isize, U8, false>::try_from(ix1.clone()).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0], *x1.indexes);
        // Signed N, SIGN=0 -> Unsigned N+X
        let x2 = IntExprNode::<isize, U9, false>::try_from(ix1.clone()).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0, 0], *x2.indexes);
        let x2 = IntExprNode::<isize, U10, false>::try_from(ix1).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0, 0, 0], *x2.indexes);

        let ix1 = IntExprNode::<isize, U8, true>::from(IntExprNode::<isize, U7, true>::variable(
            ec.clone(),
        ));
        // Signed N, SIGN=var -> Unsigned N
        assert_eq!(
            Err("Value can be negative".to_string()),
            IntExprNode::<isize, U8, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        // Signed N, SIGN=var -> Unsigned N+X
        assert_eq!(
            Err("Value can be negative".to_string()),
            IntExprNode::<isize, U9, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Value can be negative".to_string()),
            IntExprNode::<isize, U10, false>::try_from(ix1).map_err(|x| x.to_string())
        );

        let x1 = IntExprNode::<isize, U8, false>::from(IntExprNode::<isize, U7, false>::variable(
            ec.clone(),
        ));
        // Unsigned N, LAST=0 -> Signed N
        let ix2 = IntExprNode::<isize, U8, true>::try_from(x1.clone()).unwrap();
        assert_eq!([16, 17, 18, 19, 20, 21, 22, 0], *ix2.indexes);
        // Unsigned N, LAST=0 -> Signed N+X
        let ix2 = IntExprNode::<isize, U9, true>::try_from(x1.clone()).unwrap();
        assert_eq!([16, 17, 18, 19, 20, 21, 22, 0, 0], *ix2.indexes);

        let x1 = IntExprNode::<isize, U8, false>::variable(ec.clone());
        // Unsinged N, LAST=var -> Signed N+X
        let ix2 = IntExprNode::<isize, U9, true>::try_from(x1.clone()).unwrap();
        assert_eq!([23, 24, 25, 26, 27, 28, 29, 30, 0], *ix2.indexes);
        // Unsinged N, LAST=var -> Signed N
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U8, true>::try_from(x1.clone()).map_err(|x| x.to_string())
        );

        //
        // V[N-X..] = 0, LASTS = 0
        let ux1 = IntExprNode::<isize, U8, false>::from(IntExprNode::<isize, U6, false>::variable(
            ec.clone(),
        ));
        // Unsigned N, LASTS=0 -> Unsigned N-X
        let x2 = IntExprNode::<isize, U6, false>::try_from(ux1.clone()).unwrap();
        assert_eq!([31, 32, 33, 34, 35, 36], *x2.indexes);
        // Unsigned N, LASTS=0, V[N-X-1]=var -> Unsigned N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, false>::try_from(ux1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U4, false>::try_from(ux1.clone()).map_err(|x| x.to_string())
        );
        let ix2 = IntExprNode::<isize, U7, true>::try_from(ux1.clone()).unwrap();
        // Unsigned N, LASTS=0 -> Signed N-X+1
        assert_eq!([31, 32, 33, 34, 35, 36, 0], *ix2.indexes);
        // Unsigned N, LASTS=0 -> Signed N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U6, true>::try_from(ux1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, true>::try_from(ux1.clone()).map_err(|x| x.to_string())
        );

        let ix1 = IntExprNode::<isize, U8, true>::from(IntExprNode::<isize, U6, false>::variable(
            ec.clone(),
        ));
        // Signed N, LASTS=0 -> Unsigned N-X
        let x2 = IntExprNode::<isize, U6, false>::try_from(ix1.clone()).unwrap();
        assert_eq!([37, 38, 39, 40, 41, 42], *x2.indexes);
        // Signed N, LASTS=0 -> Unsigned N-X-1
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        // Signed N, LASTS=0 -> Signed N-X+1
        let ix2 = IntExprNode::<isize, U7, true>::try_from(ix1.clone()).unwrap();
        assert_eq!([37, 38, 39, 40, 41, 42, 0], *ix2.indexes);
        // Signed N, LASTS=0 -> Signed N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U6, true>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, true>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );

        // constvar - this same var for all LASTS bits
        let ix1 = IntExprNode::<isize, U8, true>::from(IntExprNode::<isize, U6, true>::variable(
            ec.clone(),
        ));
        // Signed N, LASTS=constvar -> Unsigned N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U6, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        // Signed N, LASTS=constvar -> Unsigned N-X+1
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U7, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        let ix2 = IntExprNode::<isize, U6, true>::try_from(ix1.clone()).unwrap();
        // Signed N, LASTS=constvar -> Signed N-X
        assert_eq!([43, 44, 45, 46, 47, 48], *ix2.indexes);
        // Signed N, LASTS=constvar -> Signed N-X-1
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, true>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U4, true>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
    }

    #[test]
    fn test_int_ite() {
        let ec = ExprCreator::new();
        let c1 = BoolExprNode::<isize>::variable(ec.clone());
        let x1 = IntExprNode::<isize, U7, false>::variable(ec.clone());
        let x2 = IntExprNode::<isize, U7, false>::variable(ec.clone());
        let res = int_ite(c1, x1, x2);

        let exp_ec = ExprCreator::new();
        let c1 = BoolExprNode::<isize>::variable(exp_ec.clone());
        let x1 = IntExprNode::<isize, U7, false>::variable(exp_ec.clone());
        let x2 = IntExprNode::<isize, U7, false>::variable(exp_ec.clone());
        let exp =
            (IntExprNode::filled_expr(c1.clone()) & x1) | (IntExprNode::filled_expr(!c1) & x2);

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_int_table() {
        let ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U5, false>::variable(ec.clone());
        let values = (0..(1 << 5))
            .into_iter()
            .map(|_| IntExprNode::<isize, U10, false>::variable(ec.clone()))
            .collect::<Vec<_>>();
        let res = int_table(idx, values);

        let exp_ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U5, false>::variable(exp_ec.clone());
        let values = (0..(1 << 5))
            .into_iter()
            .map(|_| IntExprNode::<isize, U10, false>::variable(exp_ec.clone()))
            .collect::<Vec<_>>();

        let mut selects0 = vec![];
        for i in 0..16 {
            selects0.push(int_ite(
                idx.bit(0),
                values[(i << 1) + 1].clone(),
                values[(i << 1)].clone(),
            ));
        }
        let mut selects1 = vec![];
        for i in 0..8 {
            selects1.push(int_ite(
                idx.bit(1),
                selects0[(i << 1) + 1].clone(),
                selects0[(i << 1)].clone(),
            ));
        }
        let mut selects2 = vec![];
        for i in 0..4 {
            selects2.push(int_ite(
                idx.bit(2),
                selects1[(i << 1) + 1].clone(),
                selects1[(i << 1)].clone(),
            ));
        }
        let mut selects3 = vec![];
        for i in 0..2 {
            selects3.push(int_ite(
                idx.bit(3),
                selects2[(i << 1) + 1].clone(),
                selects2[(i << 1)].clone(),
            ));
        }
        let exp = int_ite(idx.bit(4), selects3[1].clone(), selects3[0].clone());

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }
}
