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
use std::fmt::Debug;
use std::io::Write;
use std::ops::{BitAnd, BitOr, BitXor, Neg, Not};
use std::rc::Rc;

use crate::writer;
use crate::{CNFWriter, Literal, VarLit};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Node<T: VarLit> {
    Single(Literal<T>),
    Negated(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    Equal(usize, usize),
    Impl(usize, usize),
}

// internals
#[derive(Default, Copy, Clone)]
struct DepNode {
    normal_usage: bool,
    negated_usage: bool,
    use_linkvar: bool,
}

enum OpJoin {
    NoJoin,
    AndJoin,
    OrJoin,
    NotJoin,
}

struct DepEntry {
    node_index: usize,
    join_index: usize,
    second_path: bool,
    op_join: OpJoin,
    normal_usage: bool,
    negated_usage: bool,
    negated: bool,
}

//

#[derive(Debug, PartialEq, Eq)]
pub struct ExprCreator<T: VarLit> {
    nodes: Vec<Node<T>>,
    lit_to_index: Vec<usize>,
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

impl<T> ExprCreator<T>
where
    T: VarLit,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(ExprCreator {
            nodes: vec![
                Node::Single(Literal::Value(false)),
                Node::Single(Literal::Value(true)),
            ],
            lit_to_index: vec![],
        }))
    }

    #[inline]
    pub fn var_count(&self) -> T {
        T::from_usize(self.lit_to_index.len() >> 1)
    }

    pub fn new_variable(&mut self) -> Literal<T> {
        self.lit_to_index.push(0); // zero - no variable
        self.lit_to_index.push(0);
        Literal::from(self.var_count())
    }

    pub fn single(&mut self, l: impl Into<Literal<T>>) -> usize {
        match l.into() {
            Literal::Value(false) => 0,
            Literal::Value(true) => 1,
            Literal::VarLit(ll) => {
                assert!(ll.positive().unwrap() <= self.var_count());
                let ltoi = ((ll.positive().unwrap().to_usize() - 1) << 1)
                    + if ll < T::empty() { 1 } else { 0 };
                let node_index = self.lit_to_index[ltoi];
                if node_index != 0 {
                    node_index
                } else {
                    self.nodes.push(Node::Single(Literal::VarLit(ll)));
                    self.lit_to_index[ltoi] = self.nodes.len() - 1;
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
    new_xxx!(new_impl, Impl);

    // TODO: try write, writer. first - determine real dependencies and
    // real usage (normal and negated) - and mark them.
    pub fn write<W: Write>(
        &self,
        start: usize,
        cnf: &mut CNFWriter<W>,
    ) -> Result<(), writer::Error> {
        let dep_nodes = vec![DepNode::default(); self.nodes.len()];
        {
            //let stack = vec![DepEntry::default()];
        }
        Ok(())
    }
}

pub trait BoolEqual<Rhs = Self> {
    type Output;

    fn equal(self, rhs: Rhs) -> Self::Output;
}

impl BoolEqual for bool {
    type Output = bool;
    fn equal(self, rhs: bool) -> Self::Output {
        !(self ^ rhs)
    }
}

pub trait BoolImpl<Rhs = Self> {
    type Output;

    fn imp(self, rhs: Rhs) -> Self::Output;
}

impl BoolImpl for bool {
    type Output = bool;
    fn imp(self, rhs: bool) -> Self::Output {
        (!self) | rhs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExprNode<T: VarLit> {
    creator: Rc<RefCell<ExprCreator<T>>>,
    index: usize,
}

impl<T> ExprNode<T>
where
    T: VarLit,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
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

impl<T> Not for ExprNode<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = Self;

    fn not(self) -> Self::Output {
        let node1 = {
            let mut creator = self.creator.borrow();
            creator.nodes[self.index]
        };
        match node1 {
            Node::Single(l) => ExprNode::single(self.creator, !l),
            Node::Negated(index1) => ExprNode {
                creator: self.creator,
                index: index1,
            },
            _ => {
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
    }
}

macro_rules! new_op_impl {
    // for argeqres - if None then use self
    ($t:ident, $u:ident, $v:ident, $argeqres:expr) => {
        impl<T> $t for ExprNode<T>
        where
            T: VarLit + Neg<Output = T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
        {
            type Output = Self;

            fn $v(self, rhs: Self) -> Self::Output {
                assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rhs.creator));
                if self.index == rhs.index {
                    if let Some(t) = $argeqres {
                        return ExprNode::single(self.creator, t);
                    } else {
                        return self;
                    }
                }
                let (node1, node2) = {
                    let creator = self.creator.borrow();
                    (creator.nodes[self.index], creator.nodes[rhs.index])
                };
                if let Node::Single(lit1) = node1 {
                    if let Node::Single(lit2) = node2 {
                        self.$v(lit2)
                    } else {
                        // lit1 op node2
                        lit1.$v(rhs)
                    }
                } else {
                    if let Node::Single(lit2) = node2 {
                        self.$v(lit2)
                    } else {
                        // complicated
                        let index = self.creator.borrow_mut().$u(self.index, rhs.index);
                        ExprNode {
                            creator: self.creator,
                            index,
                        }
                    }
                }
            }
        }
    };
}

// for argeqres - if None then use self
new_op_impl!(BitAnd, new_and, bitand, None::<bool>);
new_op_impl!(BitOr, new_or, bitor, None::<bool>);
new_op_impl!(BitXor, new_xor, bitxor, Some(false));
new_op_impl!(BoolEqual, new_equal, equal, Some(true));
new_op_impl!(BoolImpl, new_impl, imp, Some(true));

impl<T, U> BitAnd<U> for ExprNode<T>
where
    T: VarLit + Neg<Output = T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn bitand(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return ExprNode::single(self.creator, v1 & v2);
                    } else {
                        return v1 & ExprNode::single(self.creator, lit2);
                    }
                } else if lit1 == lit2 {
                    return self;
                } else if lit1 == !lit2 {
                    return ExprNode::single(self.creator, false);
                }
            }
        }
        match lit2 {
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

impl<T> BitAnd<ExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
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
        impl<T> $u<ExprNode<T>> for bool
        where
            T: VarLit + Neg<Output = T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
        {
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

impl<T, U> BitOr<U> for ExprNode<T>
where
    T: VarLit + Neg<Output = T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn bitor(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return ExprNode::single(self.creator, v1 | v2);
                    } else {
                        return v1 | ExprNode::single(self.creator, lit2);
                    }
                } else if lit1 == lit2 {
                    return self;
                } else if lit1 == !lit2 {
                    return ExprNode::single(self.creator, true);
                }
            }
        }
        match lit2 {
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

impl<T: VarLit> BitOr<ExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn bitor(self, rhs: ExprNode<T>) -> Self::Output {
        rhs.bitor(self)
    }
}

new_all_op_l_xn_impls!(BitOr, bitor);

impl<T, U> BitXor<U> for ExprNode<T>
where
    T: VarLit + Neg<Output = T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn bitxor(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return ExprNode::single(self.creator, v1 ^ v2);
                    } else {
                        return v1 ^ ExprNode::single(self.creator, lit2);
                    }
                } else if lit1 == lit2 {
                    return ExprNode::single(self.creator, false);
                } else if lit1 == !lit2 {
                    return ExprNode::single(self.creator, true);
                }
            }
        }
        match lit2 {
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

impl<T> BitXor<ExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn bitxor(self, rhs: ExprNode<T>) -> Self::Output {
        rhs.bitxor(self)
    }
}

new_all_op_l_xn_impls!(BitXor, bitxor);

impl<T, U> BoolEqual<U> for ExprNode<T>
where
    T: VarLit + Neg<Output = T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn equal(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return ExprNode::single(self.creator, v1.equal(v2));
                    } else {
                        return v1.equal(ExprNode::single(self.creator, lit2));
                    }
                } else if lit1 == lit2 {
                    return ExprNode::single(self.creator, true);
                } else if lit1 == !lit2 {
                    return ExprNode::single(self.creator, false);
                }
            }
        }
        match lit2 {
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

impl<T> BoolEqual<ExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn equal(self, rhs: ExprNode<T>) -> Self::Output {
        rhs.equal(self)
    }
}

new_all_op_l_xn_impls!(BoolEqual, equal);

impl<T, U> BoolImpl<U> for ExprNode<T>
where
    T: VarLit + Neg<Output = T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn imp(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return ExprNode::single(self.creator, v1.imp(v2));
                    } else {
                        return v1.imp(ExprNode::single(self.creator, lit2));
                    }
                } else if lit1 == lit2 {
                    return ExprNode::single(self.creator, true);
                } else if lit1 == !lit2 {
                    return ExprNode::single(self.creator, lit2);
                }
            }
        }
        match lit2 {
            Literal::Value(false) => !self,
            Literal::Value(true) => ExprNode {
                creator: self.creator,
                index: 1,
            },
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_impl(self.index, index)
                };
                ExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

impl<T> BoolImpl<ExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    type Output = ExprNode<T>;

    fn imp(self, rhs: ExprNode<T>) -> Self::Output {
        let lit1 = self.into();
        {
            let node2 = rhs.creator.borrow().nodes[rhs.index];
            if let Node::Single(lit2) = node2 {
                if lit1 == lit2 {
                    return ExprNode::single(rhs.creator, true);
                } else if lit1 == !lit2 {
                    return ExprNode::single(rhs.creator, lit2);
                }
            }
        }
        match lit1 {
            Literal::Value(false) => ExprNode {
                creator: rhs.creator,
                index: 1,
            },
            Literal::Value(true) => rhs,
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = rhs.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_impl(index, rhs.index)
                };
                ExprNode {
                    creator: rhs.creator,
                    index,
                }
            }
        }
    }
}

impl<T: VarLit> BoolImpl<ExprNode<T>> for bool {
    type Output = ExprNode<T>;

    fn imp(self, rhs: ExprNode<T>) -> Self::Output {
        if self {
            rhs
        } else {
            ExprNode {
                creator: rhs.creator,
                index: 1,
            }
        }
    }
}

macro_rules! new_impl_imp_impls {
    ($ty: ty) => {
        impl BoolImpl<ExprNode<$ty>> for $ty {
            type Output = ExprNode<$ty>;

            fn imp(self, rhs: ExprNode<$ty>) -> Self::Output {
                let lit1 = Literal::from(self);
                {
                    let node2 = rhs.creator.borrow().nodes[rhs.index];
                    if let Node::Single(lit2) = node2 {
                        if lit1 == lit2 {
                            return ExprNode::single(rhs.creator, true);
                        } else if lit1 == !lit2 {
                            return ExprNode::single(rhs.creator, lit2);
                        }
                    }
                }
                let index = {
                    let mut creator = rhs.creator.borrow_mut();
                    let index = creator.single(self);
                    creator.new_impl(index, rhs.index)
                };
                ExprNode {
                    creator: rhs.creator,
                    index,
                }
            }
        }
    };
}

new_impl_imp_impls!(i8);
new_impl_imp_impls!(i16);
new_impl_imp_impls!(i32);
new_impl_imp_impls!(i64);
new_impl_imp_impls!(isize);

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
                    Node::Xor(8, 7),
                    Node::Or(6, 9),
                ],
                lit_to_index: vec![2, 5, 3, 0, 4, 7],
            },
            *ec.borrow()
        );
        let _ = v1.clone() ^ v2.clone().equal(v3) | !xp1;
        assert_eq!(
            ExprCreator {
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
                    Node::Xor(8, 7),
                    Node::Or(6, 9),
                    Node::Equal(3, 4),
                    Node::Xor(11, 2),
                    Node::Negated(6),
                    Node::Or(12, 13),
                ],
                lit_to_index: vec![2, 5, 3, 0, 4, 7],
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
                lit_to_index: vec![2, 5, 3, 8, 4, 0, 11, 0, 6, 0],
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
                lit_to_index: vec![2, 5, 3, 8, 4, 0, 11, 0, 6, 0],
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
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Equal(3, 5),
                    Node::Equal(6, 4),
                    Node::Equal(7, 5),
                ],
                lit_to_index: vec![2, 4, 5, 0, 3, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_imp_equal() {
        let ec = ExprCreator::<isize>::new();
        let v1 = ExprNode::variable(ec.clone());
        let v2 = ExprNode::variable(ec.clone());
        let v3 = ExprNode::variable(ec.clone());
        let _ = v3.clone().equal(v1.imp(v2.equal(v3)));
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Equal(3, 4),
                    Node::Impl(2, 5),
                    Node::Equal(6, 4),
                ],
                lit_to_index: vec![2, 0, 3, 0, 4, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_not_simpls() {
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = ExprNode::variable(ec.clone());
            let v2 = ExprNode::variable(ec.clone());
            let xp1 = v1.imp(v2.clone());
            let xp2 = !xp1.clone();
            let _ = xp2.clone() & v2 & !xp2.clone();
            assert_eq!(!xp2.clone(), xp1.clone());
            assert_eq!(
                ExprCreator {
                    nodes: vec![
                        Node::Single(Literal::Value(false)),
                        Node::Single(Literal::Value(true)),
                        Node::Single(Literal::VarLit(1)),
                        Node::Single(Literal::VarLit(2)),
                        Node::Impl(2, 3),
                        Node::Negated(4),
                        Node::And(5, 3),
                        Node::And(6, 4),
                    ],
                    lit_to_index: vec![2, 0, 3, 0],
                },
                *ec.borrow()
            );
        }
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = ExprNode::variable(ec.clone());
            let v2 = ExprNode::variable(ec.clone());
            let np1 = !v1.clone();
            let _ = np1.clone() & v2 & !np1.clone();
            assert_eq!(!np1.clone(), v1);
            assert_eq!(!!np1.clone(), np1);
            assert_eq!(
                ExprCreator {
                    nodes: vec![
                        Node::Single(Literal::Value(false)),
                        Node::Single(Literal::Value(true)),
                        Node::Single(Literal::VarLit(1)),
                        Node::Single(Literal::VarLit(2)),
                        Node::Single(Literal::VarLit(-1)),
                        Node::And(4, 3),
                        Node::And(5, 2),
                    ],
                    lit_to_index: vec![2, 4, 3, 0],
                },
                *ec.borrow()
            );
        }
        {
            let ec = ExprCreator::<isize>::new();
            let np1 = ExprNode::single(ec.clone(), true);
            let np2 = !np1.clone();
            let np3 = !np2.clone();
            assert_eq!(np2, ExprNode::single(ec.clone(), false));
            assert_eq!(np3, np1);
            assert_eq!(
                ExprCreator {
                    nodes: vec![
                        Node::Single(Literal::Value(false)),
                        Node::Single(Literal::Value(true)),
                    ],
                    lit_to_index: vec![],
                },
                *ec.borrow()
            );
        }
    }

    #[test]
    fn test_expr_nodes_and_simpls() {
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = ExprNode::variable(ec.clone());
            let xpfalse = ExprNode::single(ec.clone(), false);
            let xptrue = ExprNode::single(ec.clone(), true);
            let nv1 = !v1.clone();

            assert_eq!(xptrue.clone() & true, xptrue);
            assert_eq!(true & xptrue.clone(), xptrue);
            assert_eq!(xptrue.clone() & Literal::from(true), xptrue);
            assert_eq!(Literal::from(true) & xptrue.clone(), xptrue);
            assert_eq!(xptrue.clone() & xptrue.clone(), xptrue);

            assert_eq!(v1.clone() & false, xpfalse);
            assert_eq!(false & v1.clone(), xpfalse);
            assert_eq!(v1.clone() & Literal::from(false), xpfalse);
            assert_eq!(Literal::from(false) & v1.clone(), xpfalse);
            assert_eq!(v1.clone() & xpfalse.clone(), xpfalse);
            assert_eq!(xpfalse.clone() & v1.clone(), xpfalse);

            assert_eq!(v1.clone() & true, v1);
            assert_eq!(true & v1.clone(), v1);
            assert_eq!(v1.clone() & Literal::from(true), v1);
            assert_eq!(Literal::from(true) & v1.clone(), v1);
            assert_eq!(v1.clone() & xptrue.clone(), v1);
            assert_eq!(xptrue.clone() & v1.clone(), v1);

            assert_eq!(-1 & v1.clone(), xpfalse);
            assert_eq!(v1.clone() & -1, xpfalse);
            assert_eq!(Literal::from(-1) & v1.clone(), xpfalse);
            assert_eq!(v1.clone() & Literal::from(-1), xpfalse);
            assert_eq!(nv1.clone() & v1.clone(), xpfalse);
            assert_eq!(v1.clone() & nv1.clone(), xpfalse);

            assert_eq!(1 & v1.clone(), v1);
            assert_eq!(v1.clone() & 1, v1);
            assert_eq!(Literal::from(1) & v1.clone(), v1);
            assert_eq!(v1.clone() & Literal::from(1), v1);
            assert_eq!(v1.clone() & v1.clone(), v1);
        }
    }

    #[test]
    fn test_expr_nodes_or_simpls() {
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = ExprNode::variable(ec.clone());
            let xpfalse = ExprNode::single(ec.clone(), false);
            let xptrue = ExprNode::single(ec.clone(), true);
            let nv1 = !v1.clone();

            assert_eq!(xptrue.clone() | true, xptrue);
            assert_eq!(true | xptrue.clone(), xptrue);
            assert_eq!(xptrue.clone() | Literal::from(true), xptrue);
            assert_eq!(Literal::from(true) | xptrue.clone(), xptrue);
            assert_eq!(xptrue.clone() | xptrue.clone(), xptrue);

            assert_eq!(v1.clone() | false, v1);
            assert_eq!(false | v1.clone(), v1);
            assert_eq!(v1.clone() | Literal::from(false), v1);
            assert_eq!(Literal::from(false) | v1.clone(), v1);
            assert_eq!(v1.clone() | xpfalse.clone(), v1);
            assert_eq!(xpfalse.clone() | v1.clone(), v1);

            assert_eq!(v1.clone() | true, xptrue);
            assert_eq!(true | v1.clone(), xptrue);
            assert_eq!(v1.clone() | Literal::from(true), xptrue);
            assert_eq!(Literal::from(true) | v1.clone(), xptrue);
            assert_eq!(v1.clone() | xptrue.clone(), xptrue);
            assert_eq!(xptrue.clone() | v1.clone(), xptrue);

            assert_eq!(-1 | v1.clone(), xptrue);
            assert_eq!(v1.clone() | -1, xptrue);
            assert_eq!(Literal::from(-1) | v1.clone(), xptrue);
            assert_eq!(v1.clone() | Literal::from(-1), xptrue);
            assert_eq!(nv1.clone() | v1.clone(), xptrue);
            assert_eq!(v1.clone() | nv1.clone(), xptrue);

            assert_eq!(1 | v1.clone(), v1);
            assert_eq!(v1.clone() | 1, v1);
            assert_eq!(Literal::from(1) | v1.clone(), v1);
            assert_eq!(v1.clone() | Literal::from(1), v1);
            assert_eq!(v1.clone() | v1.clone(), v1);
        }
    }

    #[test]
    fn test_expr_nodes_xor_simpls() {
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = ExprNode::variable(ec.clone());
            let nv1 = !v1.clone();
            let xpfalse = ExprNode::single(ec.clone(), false);
            let xptrue = ExprNode::single(ec.clone(), true);

            assert_eq!(xptrue.clone() ^ true, xpfalse);
            assert_eq!(true ^ xptrue.clone(), xpfalse);
            assert_eq!(xptrue.clone() ^ Literal::from(true), xpfalse);
            assert_eq!(Literal::from(true) ^ xptrue.clone(), xpfalse);
            assert_eq!(xptrue.clone() ^ xptrue.clone(), xpfalse);

            assert_eq!(v1.clone() ^ false, v1);
            assert_eq!(false ^ v1.clone(), v1);
            assert_eq!(v1.clone() ^ Literal::from(false), v1);
            assert_eq!(Literal::from(false) ^ v1.clone(), v1);
            assert_eq!(v1.clone() ^ xpfalse.clone(), v1);
            assert_eq!(xpfalse.clone() ^ v1.clone(), v1);

            assert_eq!(v1.clone() ^ true, nv1);
            assert_eq!(true ^ v1.clone(), nv1);
            assert_eq!(v1.clone() ^ Literal::from(true), nv1);
            assert_eq!(Literal::from(true) ^ v1.clone(), nv1);
            assert_eq!(v1.clone() ^ xptrue.clone(), nv1);
            assert_eq!(xptrue.clone() ^ v1.clone(), nv1);

            assert_eq!(-1 ^ v1.clone(), xptrue);
            assert_eq!(v1.clone() ^ -1, xptrue);
            assert_eq!(Literal::from(-1) ^ v1.clone(), xptrue);
            assert_eq!(v1.clone() ^ Literal::from(-1), xptrue);
            assert_eq!(nv1.clone() ^ v1.clone(), xptrue);
            assert_eq!(v1.clone() ^ nv1.clone(), xptrue);

            assert_eq!(1 ^ v1.clone(), xpfalse);
            assert_eq!(v1.clone() ^ 1, xpfalse);
            assert_eq!(Literal::from(1) ^ v1.clone(), xpfalse);
            assert_eq!(v1.clone() ^ Literal::from(1), xpfalse);
            assert_eq!(v1.clone() ^ v1.clone(), xpfalse);
        }
    }

    #[test]
    fn test_expr_nodes_equal_simpls() {
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = ExprNode::variable(ec.clone());
            let nv1 = !v1.clone();
            let xpfalse = ExprNode::single(ec.clone(), false);
            let xptrue = ExprNode::single(ec.clone(), true);

            assert_eq!(xptrue.clone().equal(true), xptrue);
            assert_eq!(true.equal(xptrue.clone()), xptrue);
            assert_eq!(xptrue.clone().equal(Literal::from(true)), xptrue);
            assert_eq!(Literal::from(true).equal(xptrue.clone()), xptrue);
            assert_eq!(xptrue.clone().equal(xptrue.clone()), xptrue);

            assert_eq!(v1.clone().equal(false), nv1);
            assert_eq!(false.equal(v1.clone()), nv1);
            assert_eq!(v1.clone().equal(Literal::from(false)), nv1);
            assert_eq!(Literal::from(false).equal(v1.clone()), nv1);
            assert_eq!(v1.clone().equal(xpfalse.clone()), nv1);
            assert_eq!(xpfalse.clone().equal(v1.clone()), nv1);

            assert_eq!(v1.clone().equal(true), v1);
            assert_eq!(true.equal(v1.clone()), v1);
            assert_eq!(v1.clone().equal(Literal::from(true)), v1);
            assert_eq!(Literal::from(true).equal(v1.clone()), v1);
            assert_eq!(v1.clone().equal(xptrue.clone()), v1);
            assert_eq!(xptrue.clone().equal(v1.clone()), v1);

            assert_eq!((-1).equal(v1.clone()), xpfalse);
            assert_eq!(v1.clone().equal(-1), xpfalse);
            assert_eq!(Literal::from(-1).equal(v1.clone()), xpfalse);
            assert_eq!(v1.clone().equal(Literal::from(-1)), xpfalse);
            assert_eq!(nv1.clone().equal(v1.clone()), xpfalse);
            assert_eq!(v1.clone().equal(nv1.clone()), xpfalse);

            assert_eq!(1.equal(v1.clone()), xptrue);
            assert_eq!(v1.clone().equal(1), xptrue);
            assert_eq!(Literal::from(1).equal(v1.clone()), xptrue);
            assert_eq!(v1.clone().equal(Literal::from(1)), xptrue);
            assert_eq!(v1.clone().equal(v1.clone()), xptrue);
        }
    }

    #[test]
    fn test_expr_nodes_impl_simpls() {
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = ExprNode::variable(ec.clone());
            let nv1 = !v1.clone();
            let xpfalse = ExprNode::single(ec.clone(), false);
            let xptrue = ExprNode::single(ec.clone(), true);

            assert_eq!(xptrue.clone().imp(true), xptrue);
            assert_eq!(true.imp(xptrue.clone()), xptrue);
            assert_eq!(xptrue.clone().imp(Literal::from(true)), xptrue);
            assert_eq!(Literal::from(true).imp(xptrue.clone()), xptrue);
            assert_eq!(xptrue.clone().imp(xptrue.clone()), xptrue);

            assert_eq!(v1.clone().imp(false), nv1);
            assert_eq!(false.imp(v1.clone()), xptrue);
            assert_eq!(v1.clone().imp(Literal::from(false)), nv1);
            assert_eq!(Literal::from(false).imp(v1.clone()), xptrue);
            assert_eq!(v1.clone().imp(xpfalse.clone()), nv1);
            assert_eq!(xpfalse.clone().imp(v1.clone()), xptrue);

            assert_eq!(v1.clone().imp(true), xptrue);
            assert_eq!(true.imp(v1.clone()), v1);
            assert_eq!(v1.clone().imp(Literal::from(true)), xptrue);
            assert_eq!(Literal::from(true).imp(v1.clone()), v1);
            assert_eq!(v1.clone().imp(xptrue.clone()), xptrue);
            assert_eq!(xptrue.clone().imp(v1.clone()), v1);

            assert_eq!((-1).imp(v1.clone()), v1);
            assert_eq!(v1.clone().imp(-1), nv1);
            assert_eq!(Literal::from(-1).imp(v1.clone()), v1);
            assert_eq!(v1.clone().imp(Literal::from(-1)), nv1);
            assert_eq!(nv1.clone().imp(v1.clone()), v1);
            assert_eq!(v1.clone().imp(nv1.clone()), nv1);

            assert_eq!(1.imp(v1.clone()), xptrue);
            assert_eq!(v1.clone().imp(1), xptrue);
            assert_eq!(Literal::from(1).imp(v1.clone()), xptrue);
            assert_eq!(v1.clone().imp(Literal::from(1)), xptrue);
            assert_eq!(v1.clone().imp(v1.clone()), xptrue);
        }
    }
}
