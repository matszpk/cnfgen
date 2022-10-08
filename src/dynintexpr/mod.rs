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
use std::fmt::Debug;
use std::ops::Neg;
use std::rc::Rc;

use generic_array::*;

use crate::boolexpr::half_adder;
use crate::int_utils::*;
use crate::intexpr::IntError;
use crate::{impl_int_ipty, impl_int_upty};
use crate::{
    BitVal, BoolEqual, BoolExprNode, BoolImpl, DivMod, ExprCreator, FullMul, IntEqual, IntExprNode,
    IntOrd, Literal, VarLit,
};

pub mod arith;
pub use arith::*;

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
        if n <= input.indexes.len() {
            if !input.indexes.iter().skip(n - 1).all(|x| *x == 0) {
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

impl<T: VarLit> TryFromNSized<ExprNode<T, true>> for ExprNode<T, true> {
    type Error = IntError;

    fn try_from_n(input: ExprNode<T, true>, n: usize) -> Result<Self, IntError> {
        if n < input.indexes.len() {
            let last_idx = input.indexes[n - 1];
            if !input.indexes.iter().skip(n).all(|x| last_idx == *x) {
                return Err(IntError::BitOverflow);
            }
            Ok(ExprNode {
                creator: input.creator,
                indexes: Vec::from(&input.indexes[0..n]),
            })
        } else {
            let last = *input.indexes.last().unwrap();
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

pub trait TryIntConstant<T: VarLit, U>: Sized {
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter;

    #[test]
    fn test_expr_node() {
        let ec = ExprCreator::new();
        let x1 = ExprNode::<isize, false>::variable(ec.clone(), 7);
        assert_eq!([2, 3, 4, 5, 6, 7, 8], *x1.indexes);
        assert_eq!([2, 3, 4, 5, 6, 7, 8], *(x1.clone().as_signed()).indexes);
        assert_eq!([2, 3, 4, 5, 6, 7, 8], *(x1.as_unsigned()).indexes);
        let x2 = ExprNode::<isize, true>::variable(ec.clone(), 7);
        assert_eq!([9, 10, 11, 12, 13, 14, 15], *x2.indexes);
        assert_eq!(
            [9, 10, 11, 12, 13, 14, 15],
            *(x2.clone().as_unsigned()).indexes
        );
        assert_eq!([9, 10, 11, 12, 13, 14, 15], *(x2.as_signed()).indexes);

        let b1 = BoolExprNode::variable(ec.clone());
        let x3 = ExprNode::<isize, false>::filled(ec.clone(), 4, b1.varlit().unwrap());
        assert_eq!([16, 16, 16, 16], *x3.indexes);
        let b1 = BoolExprNode::variable(ec.clone());
        let b2 = BoolExprNode::variable(ec.clone());
        let bxp = b1.clone() ^ b2.clone();
        let x4 = ExprNode::<isize, false>::filled_expr(4, bxp.clone());
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

        let x5 = ExprNode::<isize, false>::from_boolexprs(bxps.clone());
        assert_eq!(
            bxps.iter().map(|x| x.index).collect::<Vec<_>>().as_slice(),
            x5.indexes.as_slice()
        );
    }

    #[test]
    fn test_expr_node_manip() {
        let ec = ExprCreator::new();
        let x1 = ExprNode::<isize, false>::variable(ec.clone(), 16);
        let x2 = x1.subvalue(7, 6);
        assert_eq!([9, 10, 11, 12, 13, 14], *x2.indexes);
        let x3 = x1.select_bits([3, 8, 9, 0, 3, 4, 12, 14, 15]);
        assert_eq!([5, 10, 11, 2, 5, 6, 14, 16, 17], *x3.indexes);

        let y1 = ExprNode::<isize, false>::variable(ec.clone(), 8);
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
    fn test_expr_node_try_from_n_uncond() {
        let ec = ExprCreator::new();
        // Unsigned N -> Unsigned N+X
        let x1 = ExprNode::<isize, false>::variable(ec.clone(), 8);
        let x2 = ExprNode::<isize, false>::try_from_n(x1.clone(), 14).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0], *x2.indexes);
        // Unsigned N -> Signed N+X
        let ix2 = ExprNode::<isize, true>::try_from_n(x1.clone(), 14).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0], *ix2.indexes);
        let ix1 = ExprNode::<isize, true>::variable(ec.clone(), 8);
        // Signed N, where SIGN=var -> Signed N+X
        let ix2 = ExprNode::<isize, true>::try_from_n(ix1.clone(), 12).unwrap();
        assert_eq!(
            [10, 11, 12, 13, 14, 15, 16, 17, 17, 17, 17, 17],
            *ix2.indexes
        );
    }

    #[test]
    fn test_expr_node_try_from_n() {
        let ec = ExprCreator::new();
        let ix1 = ExprNode::<isize, true>::try_from_n(
            ExprNode::<isize, false>::variable(ec.clone(), 7),
            8,
        )
        .unwrap();
        // Signed N, SIGN=0 -> Unsigned N
        let x1 = ExprNode::<isize, false>::try_from_n(ix1.clone(), 8).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0], *x1.indexes);
        // Signed N, SIGN=0 -> Unsigned N+X
        let x2 = ExprNode::<isize, false>::try_from_n(ix1.clone(), 9).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0, 0], *x2.indexes);
        let x2 = ExprNode::<isize, false>::try_from_n(ix1, 10).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0, 0, 0], *x2.indexes);

        let ix1 = ExprNode::<isize, true>::try_from_n(
            ExprNode::<isize, true>::variable(ec.clone(), 7),
            8,
        )
        .unwrap();
        // Signed N, SIGN=var -> Unsigned N
        assert_eq!(
            Err("Value can be negative".to_string()),
            ExprNode::<isize, false>::try_from_n(ix1.clone(), 8).map_err(|x| x.to_string())
        );
        // Signed N, SIGN=var -> Unsigned N+X
        assert_eq!(
            Err("Value can be negative".to_string()),
            ExprNode::<isize, false>::try_from_n(ix1.clone(), 9).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Value can be negative".to_string()),
            ExprNode::<isize, false>::try_from_n(ix1, 10).map_err(|x| x.to_string())
        );

        let x1 = ExprNode::<isize, false>::try_from_n(
            ExprNode::<isize, false>::variable(ec.clone(), 7),
            8,
        )
        .unwrap();
        // Unsigned N, LAST=0 -> Signed N
        let ix2 = ExprNode::<isize, true>::try_from_n(x1.clone(), 8).unwrap();
        assert_eq!([16, 17, 18, 19, 20, 21, 22, 0], *ix2.indexes);
        // Unsigned N, LAST=0 -> Signed N+X
        let ix2 = ExprNode::<isize, true>::try_from_n(x1.clone(), 9).unwrap();
        assert_eq!([16, 17, 18, 19, 20, 21, 22, 0, 0], *ix2.indexes);

        let x1 = ExprNode::<isize, false>::variable(ec.clone(), 8);
        // Unsinged N, LAST=var -> Signed N+X
        let ix2 = ExprNode::<isize, true>::try_from_n(x1.clone(), 9).unwrap();
        assert_eq!([23, 24, 25, 26, 27, 28, 29, 30, 0], *ix2.indexes);
        // Unsinged N, LAST=var -> Signed N
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, true>::try_from_n(x1.clone(), 8).map_err(|x| x.to_string())
        );

        //
        // V[N-X..] = 0, LASTS = 0
        let ux1 = ExprNode::<isize, false>::try_from_n(
            ExprNode::<isize, false>::variable(ec.clone(), 6),
            8,
        )
        .unwrap();
        // Unsigned N, LASTS=0 -> Unsigned N-X
        let x2 = ExprNode::<isize, false>::try_from_n(ux1.clone(), 6).unwrap();
        assert_eq!([31, 32, 33, 34, 35, 36], *x2.indexes);
        // Unsigned N, LASTS=0, V[N-X-1]=var -> Unsigned N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, false>::try_from_n(ux1.clone(), 5).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, false>::try_from_n(ux1.clone(), 4).map_err(|x| x.to_string())
        );
        let ix2 = ExprNode::<isize, true>::try_from_n(ux1.clone(), 7).unwrap();
        // Unsigned N, LASTS=0 -> Signed N-X+1
        assert_eq!([31, 32, 33, 34, 35, 36, 0], *ix2.indexes);
        // Unsigned N, LASTS=0 -> Signed N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, true>::try_from_n(ux1.clone(), 6).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, true>::try_from_n(ux1.clone(), 5).map_err(|x| x.to_string())
        );

        let ix1 = ExprNode::<isize, true>::try_from_n(
            ExprNode::<isize, false>::variable(ec.clone(), 6),
            8,
        )
        .unwrap();
        // Signed N, LASTS=0 -> Unsigned N-X
        let x2 = ExprNode::<isize, false>::try_from_n(ix1.clone(), 6).unwrap();
        assert_eq!([37, 38, 39, 40, 41, 42], *x2.indexes);
        // Signed N, LASTS=0 -> Unsigned N-X-1
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, false>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );
        // Signed N, LASTS=0 -> Signed N-X+1
        let ix2 = ExprNode::<isize, true>::try_from_n(ix1.clone(), 7).unwrap();
        assert_eq!([37, 38, 39, 40, 41, 42, 0], *ix2.indexes);
        // Signed N, LASTS=0 -> Signed N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, true>::try_from_n(ix1.clone(), 6).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, true>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );

        // constvar - this same var for all LASTS bits
        let ix1 = ExprNode::<isize, true>::try_from_n(
            ExprNode::<isize, true>::variable(ec.clone(), 6),
            8,
        )
        .unwrap();
        // Signed N, LASTS=constvar -> Unsigned N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, false>::try_from_n(ix1.clone(), 6).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, false>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );
        // Signed N, LASTS=constvar -> Unsigned N-X+1
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, false>::try_from_n(ix1.clone(), 7).map_err(|x| x.to_string())
        );
        let ix2 = ExprNode::<isize, true>::try_from_n(ix1.clone(), 6).unwrap();
        // Signed N, LASTS=constvar -> Signed N-X
        assert_eq!([43, 44, 45, 46, 47, 48], *ix2.indexes);
        // Signed N, LASTS=constvar -> Signed N-X-1
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, true>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            ExprNode::<isize, true>::try_from_n(ix1.clone(), 5).map_err(|x| x.to_string())
        );
    }
}
