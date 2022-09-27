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

use crate::boolexpr_creator::ExprCreator;
//use crate::boolexpr::ExprNode as BoolExprNode;

use crate::VarLit;

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
}
