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
use std::collections::HashMap;
use std::hash::Hash;
use std::ops::{BitAnd, BitOr, BitXor, Neg, Not};
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
pub struct ExprCreator<T: VarLit + Hash> {
    var_count: T,
    nodes: Vec<Node<T>>,
    lit_to_index: HashMap<T, usize>,
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

impl<T: VarLit + Hash> ExprCreator<T> {
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(ExprCreator {
            var_count: T::empty(),
            nodes: vec![
                Node::Single(Literal::Value(false)),
                Node::Single(Literal::Value(true)),
            ],
            lit_to_index: HashMap::new(),
        }))
    }

    pub fn new_variable(&mut self) -> Literal<T> {
        self.var_count = self.var_count.next_value().unwrap();
        self.var_count.into()
    }

    pub fn single(&mut self, l: impl Into<Literal<T>>) -> usize {
        match l.into() {
            Literal::Value(false) => 0,
            Literal::Value(true) => 1,
            Literal::VarLit(ll) => {
                assert!(ll.positive().unwrap() <= self.var_count);
                if let Some(index) = self.lit_to_index.get(&ll) {
                    *index
                } else {
                    self.nodes.push(Node::Single(Literal::VarLit(ll)));
                    self.lit_to_index.insert(ll, self.nodes.len() - 1);
                    self.nodes.len() - 1
                }
            }
        }
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

pub trait BoolEqual<Rhs = Self> {
    type Output;

    fn equal(self, rhs: Rhs) -> Self::Output;
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprNode<T: VarLit + Hash> {
    creator: Rc<RefCell<ExprCreator<T>>>,
    index: usize,
}

impl<T: VarLit + Hash> ExprNode<T> {
    pub fn single(creator: Rc<RefCell<ExprCreator<T>>>, l: impl Into<Literal<T>>) -> Self {
        let index = creator.borrow_mut().single(l);
        ExprNode { creator, index }
    }

    pub fn variable(creator: Rc<RefCell<ExprCreator<T>>>) -> Self {
        let index = {
            let mut creator = creator.borrow_mut();
            let l = creator.new_variable();
            creator.single(l)
        };
        ExprNode { creator, index }
    }
}

impl<T: VarLit + Hash> BoolEqual for ExprNode<T> {
    type Output = Self;

    fn equal(self, rhs: Self) -> Self {
        assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rhs.creator));
        let index = self.creator.borrow_mut().new_equal(self.index, rhs.index);
        ExprNode {
            creator: self.creator,
            index,
        }
    }
}

impl<T: VarLit + Hash + Neg<Output = T>> Not for ExprNode<T> {
    type Output = Self;

    fn not(self) -> Self::Output {
        let index = {
            let mut creator = self.creator.borrow_mut();
            match creator.nodes[self.index] {
                Node::Single(l) => creator.single(!l),
                _ => creator.new_not(self.index),
            }
        };
        ExprNode {
            creator: self.creator,
            index,
        }
    }
}

macro_rules! new_op_impl {
    ($t:ident, $u:ident, $v:ident) => {
        impl<T: VarLit + Hash> $t for ExprNode<T> {
            type Output = Self;

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

impl<T: VarLit + Hash, U: Into<Literal<T>>> BitAnd<U> for ExprNode<T> {
    type Output = ExprNode<T>;

    fn bitand(self, rhs: U) -> Self::Output {
        match rhs.into() {
            Literal::Value(false) => ExprNode {
                creator: self.creator,
                index: 0,
            },
            Literal::Value(true) => self,
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_and(self.index, index)
                };
                ExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

impl<T: VarLit + Hash> BitAnd<ExprNode<T>> for Literal<T> {
    type Output = ExprNode<T>;

    fn bitand(self, rhs: ExprNode<T>) -> Self::Output {
        rhs.bitand(self)
    }
}

macro_rules! new_op_l_xn_impl {
    ($t:ty, $u: ident, $v: ident) => {
        impl $u<ExprNode<$t>> for $t {
            type Output = ExprNode<$t>;

            fn $v(self, rhs: ExprNode<$t>) -> Self::Output {
                rhs.$v(Literal::from(self))
            }
        }
    };
}

macro_rules! new_all_op_l_xn_impls {
    ($u: ident, $v: ident) => {
        impl<T: VarLit + Hash + Neg<Output = T>> $u<ExprNode<T>> for bool {
            type Output = ExprNode<T>;

            fn $v(self, rhs: ExprNode<T>) -> Self::Output {
                rhs.$v(Literal::from(self))
            }
        }
        new_op_l_xn_impl!(i8, $u, $v);
        new_op_l_xn_impl!(i16, $u, $v);
        new_op_l_xn_impl!(i32, $u, $v);
        new_op_l_xn_impl!(i64, $u, $v);
        new_op_l_xn_impl!(isize, $u, $v);
    };
}

new_all_op_l_xn_impls!(BitAnd, bitand);

impl<T: VarLit + Hash, U: Into<Literal<T>>> BitOr<U> for ExprNode<T> {
    type Output = ExprNode<T>;

    fn bitor(self, rhs: U) -> Self::Output {
        match rhs.into() {
            Literal::Value(false) => self,
            Literal::Value(true) => ExprNode {
                creator: self.creator,
                index: 1,
            },
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_or(self.index, index)
                };
                ExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

impl<T: VarLit + Hash> BitOr<ExprNode<T>> for Literal<T> {
    type Output = ExprNode<T>;

    fn bitor(self, rhs: ExprNode<T>) -> Self::Output {
        rhs.bitor(self)
    }
}

new_all_op_l_xn_impls!(BitOr, bitor);

impl<T: VarLit + Hash + Neg<Output = T>, U: Into<Literal<T>>> BitXor<U> for ExprNode<T> {
    type Output = ExprNode<T>;

    fn bitxor(self, rhs: U) -> Self::Output {
        match rhs.into() {
            Literal::Value(false) => self,
            Literal::Value(true) => !self,
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_xor(self.index, index)
                };
                ExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

impl<T: VarLit + Hash + Neg<Output = T>> BitXor<ExprNode<T>> for Literal<T> {
    type Output = ExprNode<T>;

    fn bitxor(self, rhs: ExprNode<T>) -> Self::Output {
        rhs.bitxor(self)
    }
}

new_all_op_l_xn_impls!(BitXor, bitxor);

impl<T: VarLit + Hash + Neg<Output = T>, U: Into<Literal<T>>> BoolEqual<U> for ExprNode<T> {
    type Output = ExprNode<T>;

    fn equal(self, rhs: U) -> Self::Output {
        match rhs.into() {
            Literal::Value(false) => !self,
            Literal::Value(true) => self,
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_equal(self.index, index)
                };
                ExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

impl<T: VarLit + Hash + Neg<Output = T>> BoolEqual<ExprNode<T>> for Literal<T> {
    type Output = ExprNode<T>;

    fn equal(self, rhs: ExprNode<T>) -> Self::Output {
        rhs.equal(self)
    }
}

new_all_op_l_xn_impls!(BoolEqual, equal);

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
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::And(5, 3),
                    Node::Single(Literal::VarLit(-3)),
                    Node::Or(2, 3),
                    Node::Xor(7, 8),
                    Node::Or(6, 9),
                ],
                lit_to_index: HashMap::from([(1, 2), (2, 3), (3, 4), (-1, 5), (-3, 7)]),
            },
            *ec.borrow()
        );
        let _ = v1.clone() ^ v2.clone().equal(v3) | !xp1;
        assert_eq!(
            ExprCreator {
                var_count: 3,
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::And(5, 3),
                    Node::Single(Literal::VarLit(-3)),
                    Node::Or(2, 3),
                    Node::Xor(7, 8),
                    Node::Or(6, 9),
                    Node::Equal(3, 4),
                    Node::Xor(2, 11),
                    Node::Negated(6),
                    Node::Or(12, 13),
                ],
                lit_to_index: HashMap::from([(1, 2), (2, 3), (3, 4), (-1, 5), (-3, 7)]),
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_1() {
        let ec = ExprCreator::<isize>::new();
        let v1 = ExprNode::variable(ec.clone());
        let v2 = ExprNode::variable(ec.clone());
        let v3 = ExprNode::variable(ec.clone());
        let v4x = ec.borrow_mut().new_variable();
        let v5x = ec.borrow_mut().new_variable();
        let _ = Literal::from(v5x)
            | (v1.clone() ^ Literal::from(true))
            | (Literal::from(true) ^ v2)
            | (v3 & Literal::from(true))
            | (Literal::from(v4x) & v1)
            | Literal::from(false);
        assert_eq!(
            ExprCreator {
                var_count: 5,
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::Single(Literal::VarLit(5)),
                    Node::Or(5, 6),
                    Node::Single(Literal::VarLit(-2)),
                    Node::Or(7, 8),
                    Node::Or(9, 4),
                    Node::Single(Literal::VarLit(4)),
                    Node::And(2, 11),
                    Node::Or(10, 12),
                ],
                lit_to_index: HashMap::from([
                    (3, 4),
                    (1, 2),
                    (5, 6),
                    (2, 3),
                    (4, 11),
                    (-1, 5),
                    (-2, 8)
                ]),
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_2() {
        let ec = ExprCreator::<isize>::new();
        let v1 = ExprNode::variable(ec.clone());
        let v2 = ExprNode::variable(ec.clone());
        let v3 = ExprNode::variable(ec.clone());
        let v4x = ec.borrow_mut().new_variable().varlit().unwrap();
        let v5x = ec.borrow_mut().new_variable().varlit().unwrap();
        let _ = v5x | (v1.clone() ^ true) | (true ^ v2) | (v3 & true) | (v4x & v1) | false;
        assert_eq!(
            ExprCreator {
                var_count: 5,
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::Single(Literal::VarLit(5)),
                    Node::Or(5, 6),
                    Node::Single(Literal::VarLit(-2)),
                    Node::Or(7, 8),
                    Node::Or(9, 4),
                    Node::Single(Literal::VarLit(4)),
                    Node::And(2, 11),
                    Node::Or(10, 12),
                ],
                lit_to_index: HashMap::from([
                    (3, 4),
                    (1, 2),
                    (5, 6),
                    (2, 3),
                    (4, 11),
                    (-1, 5),
                    (-2, 8)
                ]),
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_3() {
        let ec = ExprCreator::<isize>::new();
        let v1 = ExprNode::variable(ec.clone());
        let v2 = ec.borrow_mut().new_variable().varlit().unwrap();
        let v3 = ExprNode::variable(ec.clone());
        let _ = v2.equal((!v1).equal(Literal::from(v2).equal(v3)));
        assert_eq!(
            ExprCreator {
                var_count: 3,
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Equal(3, 5),
                    Node::Equal(4, 6),
                    Node::Equal(7, 5),
                ],
                lit_to_index: HashMap::from([(1, 2), (-1, 4), (2, 5), (3, 3)]),
            },
            *ec.borrow()
        );
    }
}
