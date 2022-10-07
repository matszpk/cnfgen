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

use crate::intexpr::IntError;
use crate::{impl_int_ipty, impl_int_upty};
use crate::{
    BitVal, BoolEqual, BoolExprNode, BoolImpl, ExprCreator, IntEqual, IntOrd, Literal, VarLit,
};

// ExprNode - main node
//
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprNode<T: VarLit + Debug, const SIGN: bool> {
    creator: Rc<RefCell<ExprCreator<T>>>,
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

impl<T> TryFromNSized<ExprNode<T, false>> for ExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
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

impl<T> TryFromNSized<ExprNode<T, true>> for ExprNode<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
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

impl<T> TryFromNSized<ExprNode<T, false>> for ExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
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

impl<T> TryFromNSized<ExprNode<T, true>> for ExprNode<T, true>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
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
