// intexpr.rs - integer expression structures.
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
//! The module to generate CNF clauses from boolean expressions.

use std::cell::RefCell;
use std::fmt::Debug;
use std::rc::Rc;

use std::ops::Neg;

use crate::boolexpr::{BoolEqual, ExprNode as BoolExprNode};
use crate::boolexpr_creator::ExprCreator;
use crate::VarLit;

/// Equality operator for boolean expressions and boolean words.
pub trait IntEqual<Rhs = Self> {
    type Output;

    fn equal(self, rhs: Rhs) -> Self::Output;
    fn nequal(self, rhs: Rhs) -> Self::Output;
}

/// Equality operator for PartialEq.
macro_rules! int_equal_impl {
    ($t: ty) => {
        impl IntEqual for $t {
            type Output = bool;
            fn equal(self, rhs: $t) -> bool {
                self == rhs
            }
            fn nequal(self, rhs: $t) -> bool {
                self != rhs
            }
        }
    };
}

int_equal_impl!(u8);
int_equal_impl!(i8);
int_equal_impl!(u16);
int_equal_impl!(i16);
int_equal_impl!(u32);
int_equal_impl!(i32);
int_equal_impl!(u64);
int_equal_impl!(i64);
int_equal_impl!(usize);
int_equal_impl!(isize);
int_equal_impl!(u128);
int_equal_impl!(i128);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprNode<T: VarLit + Debug, const N: usize> {
    creator: Rc<RefCell<ExprCreator<T>>>,
    pub(super) index: usize,
}

impl<T, const N: usize> ExprNode<T, N>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    // Creates new variable as expression node.
    pub fn variable(creator: Rc<RefCell<ExprCreator<T>>>) -> Self {
        let index = {
            let mut creator = creator.borrow_mut();
            let l = creator.new_variable();
            let index = creator.single(l);
            for _ in 1..N {
                let l = creator.new_variable();
                creator.single(l);
            }
            index
        };
        ExprNode { creator, index }
    }

    pub fn bit(&self, n: usize) -> BoolExprNode<T> {
        BoolExprNode {
            creator: self.creator.clone(),
            index: self.index + n,
        }
    }
}

impl<T, const N: usize> IntEqual for ExprNode<T, N>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        let mut xp1 = self.bit(0).equal(rhs.bit(0));
        for i in 1..N {
            xp1 = xp1 & self.bit(i).equal(rhs.bit(i));
        }
        xp1
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        let mut xp1 = self.bit(0) ^ rhs.bit(0);
        for i in 1..N {
            xp1 = xp1 | self.bit(i) ^ rhs.bit(i);
        }
        xp1
    }
}
