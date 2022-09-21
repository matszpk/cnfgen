// boolexpr_creator.rs - boolean expression creator.
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
use std::ops::Neg;
use std::rc::Rc;

use crate::writer;
use crate::{CNFWriter, Literal, VarLit};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Node<T: VarLit> {
    Single(Literal<T>),
    Negated(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    Equal(usize, usize),
    Impl(usize, usize),
}

impl<T: VarLit> Node<T> {
    fn first_path(&self) -> usize {
        match *self {
            Node::Single(_) => panic!("No first path for single node"),
            Node::Negated(first) => first,
            Node::And(first, _) => first,
            Node::Or(first, _) => first,
            Node::Xor(first, _) => first,
            Node::Equal(first, _) => first,
            Node::Impl(first, _) => first,
        }
    }

    fn second_path(&self) -> usize {
        match *self {
            Node::Single(_) => panic!("No second path for single node"),
            Node::Negated(_) => panic!("No second path for negated node"),
            Node::And(_, second) => second,
            Node::Or(_, second) => second,
            Node::Xor(_, second) => second,
            Node::Equal(_, second) => second,
            Node::Impl(_, second) => second,
        }
    }

    #[inline]
    fn is_unary(&self) -> bool {
        matches!(self, Node::Single(_) | Node::Negated(_))
    }

    /// Returns true if node represents And operation.
    #[inline]
    fn is_conj(&self) -> bool {
        matches!(self, Node::And(_, _))
    }

    /// Returns true if node represents Or or Implication operation.
    #[inline]
    fn is_disjunc(&self) -> bool {
        matches!(self, Node::Or(_, _) | Node::Impl(_, _))
    }

    #[inline]
    fn is_xor_or_equal(&self) -> bool {
        matches!(self, Node::Xor(_, _) | Node::Equal(_, _))
    }
}

// internals
#[derive(Copy, Clone)]
struct DepNode<T: VarLit> {
    normal_usage: bool,
    negated_usage: bool,
    linkvar: Option<T>,
    parent_count: usize,
}

impl<T: VarLit> Default for DepNode<T> {
    #[inline]
    fn default() -> Self {
        DepNode {
            normal_usage: false,
            negated_usage: false,
            linkvar: None,
            parent_count: 0,
        }
    }
}

impl<T: VarLit> DepNode<T> {
    #[inline]
    fn new_first() -> Self {
        DepNode {
            normal_usage: true,
            negated_usage: false,
            linkvar: None,
            parent_count: 0,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum OpJoin {
    Nothing,
    Conj,
    Disjunc,
}

//

#[derive(Debug, PartialEq, Eq)]
pub struct ExprCreator<T: VarLit> {
    pub(super) nodes: Vec<Node<T>>,
    pub(super) lit_to_index: Vec<usize>,
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
    T: VarLit + Neg<Output = T>,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
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
        let mut dep_nodes = vec![DepNode::default(); self.nodes.len()];
        let mut total_var_count = self.var_count();
        let mut clause_count: usize = 0;

        // parent count
        {
            struct SimpleEntry {
                node_index: usize,
                path: usize,
            }

            impl SimpleEntry {
                #[inline]
                fn new_root(start: usize) -> Self {
                    Self {
                        node_index: start,
                        path: 0,
                    }
                }
            }

            let mut visited = vec![false; self.nodes.len()];
            let mut stack = vec![SimpleEntry::new_root(start)];

            while !stack.is_empty() {
                let mut top = stack.last_mut().unwrap();
                let node_index = top.node_index;
                let node = self.nodes[top.node_index];

                if !visited[node_index] {
                    let first_path = top.path == 0 && !matches!(node, Node::Single(_));
                    let second_path = top.path == 1 && !node.is_unary();

                    if !node.is_unary() && second_path {
                        dep_nodes[node_index].parent_count += 1;
                        visited[node_index] = true;
                    }

                    if first_path {
                        top.path = 1;
                        stack.push(SimpleEntry {
                            node_index: node.first_path(),
                            path: 0,
                        });
                    } else if second_path {
                        top.path = 2;
                        stack.push(SimpleEntry {
                            node_index: node.second_path(),
                            path: 0,
                        });
                    } else {
                        stack.pop();
                    }
                } else {
                    stack.pop();
                }
            }
        }

        // count extra variables and determine clause usage
        {
            struct DepEntry {
                node_index: usize,
                path: usize,
                normal_usage: bool,
                negated_usage: bool,
                op_join: OpJoin,
                not_join: bool,
                negated: bool,
            }

            impl DepEntry {
                #[inline]
                fn new_root(start: usize) -> Self {
                    DepEntry {
                        node_index: start,
                        path: 0,
                        normal_usage: true,
                        negated_usage: false,
                        op_join: OpJoin::Nothing,
                        not_join: false,
                        negated: false,
                    }
                }
            }

            let mut stack = vec![DepEntry::new_root(start)];
            dep_nodes[start] = DepNode::new_first();

            while !stack.is_empty() {
                let mut top = stack.last_mut().unwrap();
                let mut dep_node = dep_nodes.get_mut(top.node_index).unwrap();

                let node = self.nodes[top.node_index];
                let first_path = top.path == 0 && !matches!(node, Node::Single(_));
                let second_path = top.path == 1 && !node.is_unary();

                if first_path {
                    // fix OpJoin
                    if top.negated
                        && ((node.is_conj() && top.op_join == OpJoin::Conj)
                            || (node.is_disjunc() && top.op_join == OpJoin::Disjunc))
                    {
                        top.op_join = OpJoin::Nothing;
                    }
                }

                if first_path || second_path {
                    let new_var = match node {
                        Node::Single(_) => false,
                        Node::Negated(_) => false,
                        Node::And(_, _) => top.op_join != OpJoin::Conj,
                        Node::Or(_, _) | Node::Impl(_, _) => top.op_join != OpJoin::Disjunc,
                        _ => true,
                    };

                    let new_var = new_var || dep_node.parent_count > 1;

                    if dep_node.linkvar.is_none() && new_var {
                        total_var_count = total_var_count.next_value().unwrap();
                        dep_node.linkvar = Some(total_var_count);
                    }
                }

                if (top.normal_usage && !dep_node.normal_usage)
                    || (top.negated_usage && !dep_node.negated_usage)
                {
                    if (node.is_unary() && first_path) || second_path {
                        dep_node.normal_usage |= top.normal_usage;
                        dep_node.negated_usage |= top.negated_usage;
                    }

                    if first_path || second_path {
                        let (normal_usage, negated_usage, not_join, op_join) = match node {
                            Node::Single(_) => (false, false, false, OpJoin::Nothing),
                            Node::Negated(_) => {
                                (top.negated_usage, top.normal_usage, true, top.op_join)
                            }
                            Node::And(_, _) => {
                                (top.normal_usage, top.negated_usage, false, OpJoin::Conj)
                            }
                            Node::Or(_, _) => {
                                (top.normal_usage, top.negated_usage, false, OpJoin::Disjunc)
                            }
                            Node::Xor(_, _) => (true, true, false, OpJoin::Nothing),
                            Node::Equal(_, _) => (true, true, false, OpJoin::Nothing),
                            Node::Impl(_, _) => {
                                if first_path {
                                    (top.negated_usage, top.normal_usage, true, OpJoin::Disjunc)
                                } else {
                                    (top.normal_usage, top.negated_usage, false, OpJoin::Disjunc)
                                }
                            }
                        };

                        let negated =
                            if top.not_join && not_join && matches!(node, Node::Negated(_)) {
                                !top.negated
                            } else {
                                not_join
                            };

                        if first_path {
                            top.path = 1;
                            stack.push(DepEntry {
                                node_index: node.first_path(),
                                path: 0,
                                normal_usage,
                                negated_usage,
                                op_join,
                                not_join,
                                negated,
                            });
                        } else if second_path {
                            top.path = 2;
                            stack.push(DepEntry {
                                node_index: node.second_path(),
                                path: 0,
                                normal_usage,
                                negated_usage,
                                op_join,
                                not_join,
                                negated,
                            });
                        }
                    } else {
                        stack.pop();
                    }
                } else {
                    stack.pop(); // back if everything done
                }
            }
        }

        // count clauses
        {
            struct DepEntry {
                node_index: usize,
                path: usize,
                op_join: OpJoin,
                not_join: bool,
                negated: bool,
            }

            impl DepEntry {
                #[inline]
                fn new_root(start: usize) -> Self {
                    DepEntry {
                        node_index: start,
                        path: 0,
                        op_join: OpJoin::Nothing,
                        not_join: false,
                        negated: false,
                    }
                }
            }

            let mut visited = vec![false; self.nodes.len()];
            let mut stack = vec![DepEntry::new_root(start)];

            while !stack.is_empty() {
                let mut top = stack.last_mut().unwrap();
                let node_index = top.node_index;
                let dep_node = dep_nodes.get(top.node_index).unwrap();

                let node = self.nodes.get(top.node_index).unwrap();
                let first_path = top.path == 0 && !matches!(node, Node::Single(_));
                let second_path = top.path == 1 && !node.is_unary();

                if !visited[node_index] {
                    if (node.is_unary() && first_path) || second_path {
                        visited[node_index] = true;
                    }
                    if first_path {
                        // fix OpJoin
                        if top.negated
                            && ((node.is_conj() && top.op_join == OpJoin::Conj)
                                || (node.is_disjunc() && top.op_join == OpJoin::Disjunc))
                        {
                            top.op_join = OpJoin::Nothing;
                        }
                    }

                    if first_path || second_path {
                        let conj = node.is_conj();
                        let disjunc = node.is_disjunc();

                        if (node.is_unary() && first_path) || second_path {
                            if dep_node.normal_usage
                                && ((top.op_join == OpJoin::Conj
                                    && (!conj || dep_node.linkvar.is_some()))
                                    || (disjunc && dep_node.linkvar.is_some()))
                            {
                                clause_count += 1;
                            }

                            if dep_node.negated_usage
                                && ((top.op_join == OpJoin::Disjunc
                                    && (!disjunc || dep_node.linkvar.is_some()))
                                    || (conj && dep_node.linkvar.is_some()))
                            {
                                clause_count += 1;
                            }

                            if matches!(node, Node::Xor(_, _) | Node::Equal(_, _)) {
                                if dep_node.normal_usage {
                                    clause_count += 2;
                                }
                                if dep_node.negated_usage {
                                    clause_count += 2;
                                }
                            }
                        }

                        let (not_join, op_join) = match node {
                            Node::Single(_) => (false, OpJoin::Nothing),
                            Node::Negated(_) => (true, top.op_join),
                            Node::And(_, _) => (false, OpJoin::Conj),
                            Node::Or(_, _) => (false, OpJoin::Disjunc),
                            Node::Xor(_, _) => (false, OpJoin::Nothing),
                            Node::Equal(_, _) => (false, OpJoin::Nothing),
                            Node::Impl(_, _) => {
                                if first_path {
                                    (true, OpJoin::Disjunc)
                                } else {
                                    (false, OpJoin::Disjunc)
                                }
                            }
                        };

                        let negated =
                            if top.not_join && not_join && matches!(node, Node::Negated(_)) {
                                !top.negated
                            } else {
                                not_join
                            };

                        if first_path {
                            top.path = 1;
                            stack.push(DepEntry {
                                node_index: node.first_path(),
                                path: 0,
                                op_join,
                                not_join,
                                negated,
                            });
                        } else if second_path {
                            top.path = 2;
                            stack.push(DepEntry {
                                node_index: node.second_path(),
                                path: 0,
                                op_join,
                                not_join,
                                negated,
                            });
                        }
                    } else {
                        stack.pop();
                    }
                } else {
                    stack.pop(); // back if everything done
                }
            }
        }

        // write header
        cnf.write_header(total_var_count.to_usize(), clause_count)?;

        // write clauses
        {
            #[derive(Clone)]
            enum JoiningClause<T: VarLit> {
                Nothing,
                Clause(Vec<Literal<T>>),
                Join(usize),
                XorEqual(Literal<T>, Literal<T>),
            }

            impl<T: VarLit> JoiningClause<T> {
                fn new(node: &Node<T>) -> Self {
                    if node.is_conj() || node.is_disjunc() {
                        Self::Clause(vec![])
                    } else if node.is_xor_or_equal() {
                        Self::XorEqual(Literal::from(T::empty()), Literal::from(T::empty()))
                    } else {
                        Self::Nothing
                    }
                }
            }

            struct DepEntry<T: VarLit> {
                node_index: usize,
                path: usize,
                normal_usage: bool,
                negated_usage: bool,
                op_join: OpJoin,
                not_join: bool,
                negated: bool,
                joining_clause: JoiningClause<T>,
            }

            impl<T: VarLit> DepEntry<T> {
                #[inline]
                fn new_root(start: usize) -> Self {
                    DepEntry {
                        node_index: start,
                        path: 0,
                        normal_usage: true,
                        negated_usage: false,
                        op_join: OpJoin::Nothing,
                        not_join: false,
                        negated: false,
                        joining_clause: JoiningClause::Nothing,
                    }
                }
            }

            let mut visited = vec![false; self.nodes.len()];
            let mut stack = vec![DepEntry::<T>::new_root(start)];
            dep_nodes[start] = DepNode::new_first();
            stack[0].joining_clause = JoiningClause::new(self.nodes.get(start).unwrap());

            while !stack.is_empty() {
                {
                    // push child parent node linkvar to joining clause
                    let negated = stack.last().unwrap().negated;
                    if let JoiningClause::Join(stackpos) = stack.last().unwrap().joining_clause {
                        let join_entry = stack.get_mut(stackpos).unwrap();
                        let linkvar = dep_nodes
                            .get(join_entry.node_index)
                            .unwrap()
                            .linkvar
                            .map(|x| Literal::VarLit(x))
                            .or(if let Node::Single(l) = self.nodes[join_entry.node_index] {
                                Some(l)
                            } else {
                                None
                            });
                        if let Some(linkvar) = linkvar {
                            let linkvar = if !negated { linkvar } else { !linkvar };

                            match &mut join_entry.joining_clause {
                                JoiningClause::Clause(ref mut v) => {
                                    v.push(linkvar);
                                }
                                JoiningClause::XorEqual(ref mut s1, ref mut s2) => {
                                    if *s1 == Literal::VarLit(T::empty()) {
                                        *s1 = linkvar;
                                    } else {
                                        *s2 = linkvar;
                                    }
                                }
                                _ => (),
                            }
                        }
                    }
                }

                let stacklen = stack.len() - 1;
                let mut top = stack.last_mut().unwrap();
                let dep_node = dep_nodes.get(top.node_index).unwrap();

                let node_index = top.node_index;
                let node = self.nodes[top.node_index];
                let first_path = top.path == 0 && !matches!(node, Node::Single(_));
                let second_path = top.path == 1 && !node.is_unary();

                let mut do_pop = false;

                if !visited[node_index] {
                    if (node.is_unary() && first_path) || second_path {
                        visited[node_index] = true;
                    }

                    if first_path {
                        // fix OpJoin
                        if top.negated
                            && ((node.is_conj() && top.op_join == OpJoin::Conj)
                                || (node.is_disjunc() && top.op_join == OpJoin::Disjunc))
                        {
                            top.op_join = OpJoin::Nothing;
                        }
                    }

                    /////////////
                    if top.path == 0 && dep_node.linkvar.is_some() {
                        top.joining_clause = JoiningClause::new(&node);
                    }
                    // generate joining clause for next
                    let next_clause =
                        if top.op_join == OpJoin::Conj && top.op_join == OpJoin::Disjunc {
                            if let JoiningClause::Join(_) = top.joining_clause {
                                top.joining_clause.clone()
                            } else {
                                JoiningClause::Join(stacklen - 1)
                            }
                        } else {
                            JoiningClause::Nothing
                        };
                    //////////////

                    if first_path || second_path {
                        let (normal_usage, negated_usage, not_join, op_join) = match node {
                            Node::Single(_) => (false, false, false, OpJoin::Nothing),
                            Node::Negated(_) => {
                                (top.negated_usage, top.normal_usage, true, top.op_join)
                            }
                            Node::And(_, _) => {
                                (top.normal_usage, top.negated_usage, false, OpJoin::Conj)
                            }
                            Node::Or(_, _) => {
                                (top.normal_usage, top.negated_usage, false, OpJoin::Disjunc)
                            }
                            Node::Xor(_, _) => (true, true, false, OpJoin::Nothing),
                            Node::Equal(_, _) => (true, true, false, OpJoin::Nothing),
                            Node::Impl(_, _) => {
                                if first_path {
                                    (top.negated_usage, top.normal_usage, true, OpJoin::Nothing)
                                } else {
                                    (top.normal_usage, top.negated_usage, false, OpJoin::Disjunc)
                                }
                            }
                        };

                        let negated =
                            if top.not_join && not_join && matches!(node, Node::Negated(_)) {
                                !top.negated
                            } else {
                                not_join
                            };

                        if first_path {
                            top.path = 1;
                            stack.push(DepEntry {
                                node_index: node.first_path(),
                                path: 0,
                                normal_usage,
                                negated_usage,
                                op_join,
                                not_join,
                                negated,
                                joining_clause: next_clause,
                            });
                        } else if second_path {
                            top.path = 2;
                            stack.push(DepEntry {
                                node_index: node.second_path(),
                                path: 0,
                                normal_usage,
                                negated_usage,
                                op_join,
                                not_join,
                                negated,
                                joining_clause: next_clause,
                            });
                        }
                    } else {
                        do_pop = true;
                    }
                } else {
                    stack.pop().unwrap();
                }

                if do_pop {
                    let top = stack.pop().unwrap();
                    let dep_node = dep_nodes.get(top.node_index).unwrap();
                    match top.joining_clause {
                        JoiningClause::Clause(literals) => match self.nodes[top.node_index] {
                            Node::And(_, _) => {
                                if dep_node.normal_usage {
                                    for l in &literals {
                                        if let Some(lvv) = dep_node.linkvar {
                                            cnf.write_literals([!Literal::from(lvv), *l])?;
                                        } else {
                                            cnf.write_literals([*l])?;
                                        }
                                    }
                                }
                                if dep_node.negated_usage {
                                    let mut out = vec![];
                                    if let Some(lvv) = dep_node.linkvar {
                                        out.push(Literal::from(lvv));
                                    }
                                    out.extend(literals.iter().map(|x| !*x));
                                    cnf.write_literals(out)?;
                                }
                            }
                            Node::Or(_, _) | Node::Impl(_, _) => {
                                if dep_node.negated_usage {
                                    for l in &literals {
                                        if let Some(lvv) = dep_node.linkvar {
                                            cnf.write_literals([Literal::from(lvv), !*l])?;
                                        } else {
                                            cnf.write_literals([!*l])?;
                                        }
                                    }
                                }
                                if dep_node.normal_usage {
                                    let mut out = vec![];
                                    if let Some(lvv) = dep_node.linkvar {
                                        out.push(!Literal::from(lvv));
                                    }
                                    out.extend(literals);
                                    cnf.write_literals(out)?;
                                }
                            }
                            _ => (),
                        },
                        JoiningClause::XorEqual(l1, ol2) => {
                            let mut l2 = ol2;
                            if let Node::Equal(_, _) = self.nodes[top.node_index] {
                                l2 = !l2;
                            }
                            if let Some(lvv) = dep_node.linkvar {
                                let lv = Literal::from(lvv);
                                let nlv = !Literal::from(lvv);
                                if dep_node.normal_usage {
                                    cnf.write_literals([nlv, l1, l2])?;
                                    cnf.write_literals([nlv, !l1, !l2])?;
                                }
                                if dep_node.negated_usage {
                                    cnf.write_literals([lv, l1, !l2])?;
                                    cnf.write_literals([lv, !l1, l2])?;
                                }
                            } else {
                                if dep_node.normal_usage {
                                    cnf.write_literals([l1, l2])?;
                                    cnf.write_literals([!l1, !l2])?;
                                }
                                if dep_node.negated_usage {
                                    cnf.write_literals([l1, !l2])?;
                                    cnf.write_literals([!l1, l2])?;
                                }
                            }
                        }
                        _ => (),
                    }
                }
            }
        }
        Ok(())
    }
}
