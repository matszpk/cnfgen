// boolexpr.rs - main library
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
use std::ops::{BitAnd, BitOr, BitXor, Not};
use std::rc::Rc;

use crate::{Literal, VarLit};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Node<T: VarLit> {
    Single(Literal<T>),
    Negated(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    Equal(usize, usize),
}

#[derive(Debug, PartialEq, Eq)]
pub struct ExprCreator<T: VarLit> {
    var_count: T,
    nodes: Vec<Node<T>>,
}

macro_rules! new_xxx {
    ($t:ident, $u:ident) => {
        pub fn $t(&mut self, a_index: usize, b_index: usize) -> usize {
            assert!(a_index < self.nodes.len());
            assert!(b_index < self.nodes.len());
            self.nodes.push(Node::$u(a_index, b_index));
            self.nodes.len() - 1
        }
    };
}

impl<T: VarLit> ExprCreator<T> {
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(ExprCreator {
            var_count: T::empty(),
            nodes: vec![],
        }))
    }

    pub fn new_variable(&mut self) -> T {
        self.var_count = self.var_count.next_value().unwrap();
        self.var_count
    }

    pub fn new_single(&mut self, l: T) -> usize {
        assert!(l.positive().unwrap() <= self.var_count);
        self.nodes.push(Node::Single(Literal::VarLit(l)));
        self.nodes.len() - 1
    }

    pub fn new_not(&mut self, index: usize) -> usize {
        assert!(index < self.nodes.len());
        self.nodes.push(Node::Negated(index));
        self.nodes.len() - 1
    }

    new_xxx!(new_and, And);
    new_xxx!(new_or, Or);
    new_xxx!(new_xor, Xor);
    new_xxx!(new_equal, Equal);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprNode<T: VarLit> {
    creator: Rc<RefCell<ExprCreator<T>>>,
    index: usize,
}

impl<T: VarLit> ExprNode<T> {
    pub fn single(creator: Rc<RefCell<ExprCreator<T>>>, l: T) -> Self {
        let index = creator.borrow_mut().new_single(l);
        ExprNode { creator, index }
    }

    pub fn variable(creator: Rc<RefCell<ExprCreator<T>>>) -> Self {
        let index = {
            let mut creator = creator.borrow_mut();
            let l = creator.new_variable();
            creator.new_single(l)
        };
        ExprNode { creator, index }
    }

    pub fn equal(self, rhs: Self) -> Self {
        assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rhs.creator));
        let index = self.creator.borrow_mut().new_equal(self.index, rhs.index);
        ExprNode {
            creator: self.creator,
            index,
        }
    }
}

impl<T: VarLit> Not for ExprNode<T> {
    type Output = ExprNode<T>;

    fn not(self) -> Self::Output {
        let index = self.creator.borrow_mut().new_not(self.index);
        ExprNode {
            creator: self.creator,
            index,
        }
    }
}

macro_rules! new_op_impl {
    ($t:ident, $u:ident, $v:ident) => {
        impl<T: VarLit> $t for ExprNode<T> {
            type Output = ExprNode<T>;

            fn $v(self, rhs: Self) -> Self::Output {
                assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rhs.creator));
                let index = self.creator.borrow_mut().$u(self.index, rhs.index);
                ExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    };
}

new_op_impl!(BitAnd, new_and, bitand);
new_op_impl!(BitOr, new_or, bitor);
new_op_impl!(BitXor, new_xor, bitxor);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_nodes() {
        let ec = ExprCreator::<isize>::new();
        let v1 = ExprNode::variable(ec.clone());
        let v2 = ExprNode::variable(ec.clone());
        let v3 = ExprNode::variable(ec.clone());
        let xp1 = !v1.clone() & v2.clone();
        let _ = xp1.clone() | !v3.clone() ^ (v1.clone() | v2.clone());
        assert_eq!(
            ExprCreator {
                var_count: 3,
                nodes: vec![
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Negated(0),
                    Node::And(3, 1),
                    Node::Negated(2),
                    Node::Or(0, 1),
                    Node::Xor(5, 6),
                    Node::Or(4, 7),
                ]
            },
            *ec.borrow()
        );
        let _ = v1.clone() ^ v2.clone().equal(v3) | xp1;
        assert_eq!(
            ExprCreator {
                var_count: 3,
                nodes: vec![
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Negated(0),
                    Node::And(3, 1),
                    Node::Negated(2),
                    Node::Or(0, 1),
                    Node::Xor(5, 6),
                    Node::Or(4, 7),
                    Node::Equal(1, 2),
                    Node::Xor(0, 9),
                    Node::Or(10, 4),
                ]
            },
            *ec.borrow()
        );
    }
}
