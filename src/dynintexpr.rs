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
use std::iter;
use std::ops::{Add, BitAnd, BitOr, Neg, Not, Sub};
use std::rc::Rc;

use crate::{BoolExprNode, ExprCreator, Literal, VarLit};

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
