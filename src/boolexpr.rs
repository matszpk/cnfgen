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

use std::ops::{BitAnd, BitOr, BitXor, Neg, Not};

use crate::{Literal, VarLit};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Usage {
    Normal,
    Negated,
    Both,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NodeLink {
    NoLink,
    AndLink(isize),
    OrLink(isize),
    AndNotLink(isize),
    OrNotLink(isize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Node<T: VarLit> {
    lvar: T, // linking variable, 0 - no variable, must be positive
    usage: Usage,
    next: NodeLink,
    literal: Literal<T>, //literal of this node
}

struct Container<T: VarLit> {
    var_count: isize,
    nodes: Vec<Node<T>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExprNode<'a, T: VarLit> {
    Single(Literal<T>),
    Negated(&'a ExprNode<'a, T>),
    And(&'a ExprNode<'a, T>, &'a ExprNode<'a, T>),
    Or(&'a ExprNode<'a, T>, &'a ExprNode<'a, T>),
}

impl<'a, T: VarLit> ExprNode<'a, T> {
    pub fn new_not(a: &'a ExprNode<'a, T>) -> Self {
        ExprNode::Negated(a)
    }

    pub fn new_and(a: &'a ExprNode<'a, T>, b: &'a ExprNode<'a, T>) -> Self {
        ExprNode::And(a, b)
    }

    pub fn new_or(a: &'a ExprNode<'a, T>, b: &'a ExprNode<'a, T>) -> Self {
        ExprNode::Or(a, b)
    }

    pub fn is_negated(self) -> bool {
        matches!(self, ExprNode::Negated(_))
    }

    pub fn is_binary(self) -> bool {
        matches!(self, ExprNode::And(_, _) | ExprNode::Or(_, _))
    }
}

/*impl<'a, T: VarLit + Neg<Output = T>> Not for ExprNode<'a, T> {
    type Output = ExprNode<'a, T>;

    fn not(self) -> Self::Output {
        match self {
            ExprNode::Single(t) => ExprNode::Single(!t),
            ExprNode::Negated(t) => *t,
            ExprNode::And(_, _) | ExprNode::Or(_, _) => ExprNode::Negated(&self),
        }
    }
}*/

impl<'a, T: VarLit, U: Into<Literal<T>>> From<U> for ExprNode<'a, T> {
    fn from(t: U) -> Self {
        ExprNode::Single(t.into())
    }
}
