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

#[cfg(test)]
macro_rules! test_println {
    () => { println!(); };
    ($($arg:tt)*) => { println!($($arg)*); };
}

#[cfg(not(test))]
macro_rules! test_println {
    () => {};
    ($($arg:tt)*) => {};
}

use crate::{CNFError, CNFWriter, Literal, QuantSet, Quantifier, VarLit};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Node<T: VarLit + Debug> {
    Single(Literal<T>),
    Negated(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    Equal(usize, usize),
    Impl(usize, usize),
}

impl<T: VarLit + Debug> Node<T> {
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
            Node::And(_, second) => second,
            Node::Or(_, second) => second,
            Node::Xor(_, second) => second,
            Node::Equal(_, second) => second,
            Node::Impl(_, second) => second,
            _ => panic!("No second path for single node"),
        }
    }

    #[inline]
    fn is_single(&self) -> bool {
        matches!(self, Node::Single(_))
    }

    #[inline]
    fn is_negated(&self) -> bool {
        matches!(self, Node::Negated(_))
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
#[derive(Copy, Clone, Debug)]
struct DepNode<T: VarLit + Debug> {
    normal_usage: bool,
    negated_usage: bool,
    linkvar: Option<T>,
    parent_count: usize,
}

impl<T: VarLit + Debug> Default for DepNode<T> {
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

// Operation join -
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpJoin {
    Nothing,
    Conj,    // if tree of conjunctions
    Disjunc, // if tree of disjunctions
}

/// The ExprCreator holds all expressions which will be written later.
/// Main purpose of ExprCreator is maintenance state of expression with its variables
/// during creating that expression by using ExprNode.
/// An ExprCreator is used with ExprNode to create new expression.
#[derive(Debug, PartialEq, Eq)]
pub struct ExprCreator<T: VarLit + Debug> {
    pub(super) nodes: Vec<Node<T>>,
    pub(super) lit_to_index: Vec<usize>,
}

// macro to create new_* methods for ExprCreator.
macro_rules! new_xxx {
    ($t:ident, $u:ident) => {
        pub(super) fn $t(&mut self, a_index: usize, b_index: usize) -> usize {
            assert!(a_index < self.nodes.len());
            assert!(b_index < self.nodes.len());
            self.nodes.push(Node::$u(a_index, b_index));
            self.nodes.len() - 1
        }
    };
}

// Literal writer trait to share code to writing clauses.
// Two types of code - to count clauses and to write clauses.
trait LiteralsWriter {
    fn write_literals<T, I>(&mut self, iter: I) -> Result<(), CNFError>
    where
        T: VarLit + Neg<Output = T>,
        I: IntoIterator<Item = Literal<T>>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug;
}

struct ClauseCounter(usize);

impl LiteralsWriter for ClauseCounter {
    fn write_literals<T, I>(&mut self, _: I) -> Result<(), CNFError>
    where
        T: VarLit + Neg<Output = T>,
        I: IntoIterator<Item = Literal<T>>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug,
    {
        self.0 += 1;
        Ok(())
    }
}

impl<W: Write> LiteralsWriter for CNFWriter<W> {
    fn write_literals<T, I>(&mut self, iter: I) -> Result<(), CNFError>
    where
        T: VarLit + Neg<Output = T>,
        I: IntoIterator<Item = Literal<T>>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug,
    {
        self.write_literals(iter)
    }
}

impl<T> ExprCreator<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates new ExprCreator as returns it as RefCounter.
    pub fn new() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(ExprCreator {
            nodes: vec![
                Node::Single(Literal::Value(false)),
                Node::Single(Literal::Value(true)),
            ],
            lit_to_index: vec![],
        }))
    }

    /// Returns variable count.
    #[inline]
    pub fn var_count(&self) -> T {
        T::from_usize(self.lit_to_index.len() >> 1)
    }

    pub(super) fn new_variable(&mut self) -> Literal<T> {
        self.lit_to_index.push(0); // zero - no variable
        self.lit_to_index.push(0);
        Literal::from(self.var_count())
    }

    pub(super) fn single(&mut self, l: impl Into<Literal<T>>) -> usize {
        match l.into() {
            Literal::Value(false) => 0,
            Literal::Value(true) => 1,
            Literal::VarLit(ll) => {
                assert!(ll.positive().unwrap() <= self.var_count());
                let ltoi =
                    ((ll.positive().unwrap().to_usize() - 1) << 1) + usize::from(ll < T::empty());
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

    pub(super) fn new_not(&mut self, index: usize) -> usize {
        assert!(index < self.nodes.len());
        self.nodes.push(Node::Negated(index));
        self.nodes.len() - 1
    }

    new_xxx!(new_and, And);
    new_xxx!(new_or, Or);
    new_xxx!(new_xor, Xor);
    new_xxx!(new_equal, Equal);
    new_xxx!(new_impl, Impl);

    fn write_clauses<LW: LiteralsWriter>(
        &self,
        start: usize,
        dep_nodes: &[DepNode<T>],
        cnf: &mut LW,
    ) -> Result<(), CNFError> {
        if start == 0 {
            // if start from false, then write empty clause - UNSATISFIABLE
            return cnf.write_literals([]);
        }
        // Joining clause - structure to holds final subexpressions to join in one clause -
        // conjunction, disjunction, XOR or Equality.
        #[derive(Clone, Debug)]
        enum JoiningClause<T: VarLit + Debug> {
            Nothing,
            Clause(Vec<Literal<T>>),
            Join(usize),
            XorEqual(Literal<T>, Literal<T>),
        }

        impl<T: VarLit + Debug> JoiningClause<T> {
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

        struct DepEntry<T: VarLit + Debug> {
            node_index: usize,
            path: usize,
            normal_usage: bool,  // usage of clauses - not negated
            negated_usage: bool, // usage of clauses - negated - after Negated
            not_join: bool,      // true if chain Negated
            negated: bool,       // if negated
            start: bool,
            joining_clause: JoiningClause<T>,
        }

        impl<T: VarLit + Debug> DepEntry<T> {
            #[inline]
            fn new_root(start: usize) -> Self {
                DepEntry {
                    node_index: start,
                    path: 0,
                    normal_usage: true,
                    negated_usage: false,
                    not_join: false,
                    negated: false,
                    start: true,
                    joining_clause: JoiningClause::Nothing,
                }
            }
        }

        let mut visited = vec![false; self.nodes.len()];
        let mut stack = vec![DepEntry::<T>::new_root(start)];
        stack[0].joining_clause = JoiningClause::new(self.nodes.get(start).unwrap());

        test_println!("----------write");
        while !stack.is_empty() {
            if stack.last().unwrap().path == 0 {
                // push child parent node linkvar to joining clause
                let (negated, node_index) = {
                    let top = stack.last().unwrap();
                    (top.negated, top.node_index)
                };
                if let JoiningClause::Join(stackpos) = stack.last().unwrap().joining_clause {
                    let join_entry = stack.get_mut(stackpos).unwrap();
                    // get link variable or single literal.
                    let linkvar = dep_nodes
                        .get(node_index)
                        .unwrap()
                        .linkvar
                        .map(|x| Literal::VarLit(x))
                        .or(if let Node::Single(l) = self.nodes[node_index] {
                            Some(l)
                        } else {
                            None
                        });
                    test_println!("WcPZ {}: {:?} sp:{}", node_index, linkvar, stackpos);
                    if let Some(linkvar) = linkvar {
                        let linkvar = if !negated { linkvar } else { !linkvar };

                        match &mut join_entry.joining_clause {
                            // push literal into joining clause.
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

            // current stack position at last entry
            let stackpos = stack.len() - 1;
            let mut top = stack.last_mut().unwrap();
            let dep_node = dep_nodes.get(top.node_index).unwrap();

            let node_index = top.node_index;
            let node = self.nodes[top.node_index];
            let first_path = top.path == 0 && !node.is_single();
            let second_path = top.path == 1 && !node.is_unary();

            let mut do_pop = false;

            if !first_path || !visited[node_index] {
                if !node.is_unary() && first_path {
                    visited[node_index] = true;
                }

                let conj = node.is_conj();
                let disjunc = node.is_disjunc();

                /////////////
                if top.path == 0 && (top.start || dep_node.linkvar.is_some()) {
                    top.joining_clause = JoiningClause::new(&node);
                    test_println!(
                        "Wc: {} {}: {:?} {:?}",
                        node_index,
                        top.path,
                        dep_node.linkvar,
                        top.joining_clause
                    );
                }
                //////////////

                if first_path || second_path {
                    // generate joining clause for next
                    let next_clause = if conj || disjunc {
                        if let JoiningClause::Join(_) = top.joining_clause {
                            top.joining_clause.clone()
                        } else {
                            JoiningClause::Join(stackpos)
                        }
                    } else if node.is_xor_or_equal() {
                        JoiningClause::Join(stackpos)
                    } else if node.is_negated() {
                        top.joining_clause.clone()
                    } else {
                        JoiningClause::Nothing
                    };
                    test_println!(
                        "WcN: {} {} {}: {:?}",
                        node_index,
                        top.path,
                        stackpos,
                        next_clause
                    );

                    // determine clauses usage and not_join.
                    let (normal_usage, negated_usage, not_join) = match node {
                        Node::Single(_) => (false, false, false),
                        Node::Negated(_) => (top.negated_usage, top.normal_usage, true),
                        Node::And(_, _) => (top.normal_usage, top.negated_usage, false),
                        Node::Or(_, _) => (top.normal_usage, top.negated_usage, false),
                        Node::Xor(_, _) => (true, true, false),
                        Node::Equal(_, _) => (true, true, false),
                        Node::Impl(_, _) => {
                            if first_path {
                                (top.negated_usage, top.normal_usage, true)
                            } else {
                                (top.normal_usage, top.negated_usage, false)
                            }
                        }
                    };
                    let start = node.is_negated() && top.start;
                    // determine negation
                    let negated = if top.not_join && node.is_negated() {
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
                            not_join,
                            negated,
                            start,
                            joining_clause: next_clause,
                        });
                    } else if second_path {
                        top.path = 2;
                        stack.push(DepEntry {
                            node_index: node.second_path(),
                            path: 0,
                            normal_usage,
                            negated_usage,
                            not_join,
                            negated,
                            start,
                            joining_clause: next_clause,
                        });
                    }
                } else {
                    test_println!("WPP: {} {}", node_index, top.path);
                    do_pop = true;
                }
            } else {
                stack.pop().unwrap();
            }

            if do_pop {
                let top = stack.pop().unwrap();
                let dep_node = dep_nodes.get(top.node_index).unwrap();
                test_println!(
                    "WW {} {}: {:?}",
                    top.node_index,
                    top.path,
                    top.joining_clause
                );
                match top.joining_clause {
                    // generate clauses
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
        Ok(())
    }

    pub(super) fn write<W, QL, Q>(
        &self,
        start: usize,
        quants: QL,
        cnf: &mut CNFWriter<W>,
    ) -> Result<(), CNFError>
    where
        W: Write,
        QL: IntoIterator<Item = (Quantifier, Q)>,
        Q: QuantSet<T>,
    {
        let mut dep_nodes = vec![DepNode::default(); self.nodes.len()];
        let mut total_var_count = self.var_count();

        test_println!(
            "Debug nodes:\n{}",
            self.nodes
                .iter()
                .enumerate()
                .map(|(i, x)| format!("  {}: {:?}", i, x))
                .collect::<Vec<_>>()
                .join("\n")
        );
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

                let first_path = top.path == 0 && !node.is_single();
                let second_path = top.path == 1 && !node.is_unary();

                if !node.is_unary() && first_path {
                    dep_nodes[node_index].parent_count += 1;
                }

                if !first_path || !visited[node_index] {
                    if !node.is_unary() && first_path {
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

        test_println!(
            "DepNodes:\n{}",
            dep_nodes
                .iter()
                .enumerate()
                .map(|(i, x)| format!("  {}: {:?}", i, x))
                .collect::<Vec<_>>()
                .join("\n")
        );

        // count extra variables and determine clause usage
        {
            struct DepEntry {
                node_index: usize,
                path: usize,
                normal_usage: bool,  // normal usage of clauses
                negated_usage: bool, // negated usage of clauses - if after negated
                op_join: OpJoin,     // operation join - if we in path of join.
                not_join: bool,      // if negation chain
                negated: bool,       // if negated
                start: bool,
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
                        start: true,
                    }
                }
            }

            let mut stack = vec![DepEntry::new_root(start)];

            while !stack.is_empty() {
                let mut top = stack.last_mut().unwrap();
                let mut dep_node = dep_nodes.get_mut(top.node_index).unwrap();

                let node = self.nodes[top.node_index];
                let first_path = top.path == 0 && !node.is_single();
                let second_path = top.path == 1 && !node.is_unary();

                if first_path {
                    // fix OpJoin - if we have this same type of operation and this same
                    // type of subtree (opjoin) and this node is negated - then clear joining.
                    if top.negated
                        && ((node.is_conj() && top.op_join == OpJoin::Conj)
                            || (node.is_disjunc() && top.op_join == OpJoin::Disjunc))
                    {
                        top.op_join = OpJoin::Nothing;
                    }
                }

                if first_path {
                    let new_var = match node {
                        Node::Single(_) => false,
                        Node::Negated(_) => false,
                        Node::And(_, _) => top.op_join != OpJoin::Conj,
                        Node::Or(_, _) | Node::Impl(_, _) => top.op_join != OpJoin::Disjunc,
                        _ => true, // xor or equal
                    };

                    let new_var = !top.start && (new_var || dep_node.parent_count > 1);

                    if dep_node.linkvar.is_none() && new_var {
                        total_var_count = total_var_count.next_value().unwrap();
                        dep_node.linkvar = Some(total_var_count);
                    }
                }

                if !first_path
                    || (top.normal_usage && !dep_node.normal_usage)
                    || (top.negated_usage && !dep_node.negated_usage)
                {
                    if first_path {
                        // update usage of clauses for node.
                        dep_node.normal_usage |= top.normal_usage;
                        dep_node.negated_usage |= top.negated_usage;
                    }

                    if first_path || second_path {
                        // determine clauses usage, not_join and operation join.
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
                        let start = node.is_negated() && top.start;

                        let negated = if top.not_join && node.is_negated() {
                            !top.negated
                        } else {
                            not_join
                        };

                        test_println!(
                            "Dp: {}:{} {} {}: normu:{} negu:{} j:{:?} n:{}",
                            top.node_index,
                            top.path,
                            top.normal_usage,
                            top.negated_usage,
                            normal_usage,
                            negated_usage,
                            op_join,
                            negated
                        );

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
                                start,
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
                                start,
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

        test_println!(
            "DepNodes2:\n{}",
            dep_nodes
                .iter()
                .enumerate()
                .map(|(i, x)| format!("  {}: {:?}", i, x))
                .collect::<Vec<_>>()
                .join("\n")
        );

        // count clauses
        let mut clause_counter = ClauseCounter(0);
        self.write_clauses(start, &dep_nodes, &mut clause_counter)?;
        let clause_count = clause_counter.0;

        // write header
        cnf.write_header(total_var_count.to_usize(), clause_count)?;

        // write quantifiers
        let mut cquants = quants.into_iter().collect::<Vec<(Quantifier, Q)>>();

        if !cquants.is_empty() {
            let last = cquants.pop().unwrap();
            // write all except last
            cquants
                .drain(..)
                .try_for_each(|(q, qs)| cnf.write_quant(q, qs))?;

            let mut dest_last_qs = vec![];
            if last.0 == Quantifier::Exists {
                last.1.quant_for_each(|x| dest_last_qs.push(*x));
            } else {
                cnf.write_quant(last.0, last.1)?;
            }
            let mut t = self.var_count().next_value().unwrap();
            // add extra variables to last 'exists' quantifier
            while t <= total_var_count {
                dest_last_qs.push(t);
                t = t.next_value().unwrap();
            }
            if !dest_last_qs.is_empty() {
                cnf.write_quant(Quantifier::Exists, dest_last_qs)?;
            }
        }

        // write clauses
        self.write_clauses(start, &dep_nodes, cnf)?;

        assert_eq!(clause_count, cnf.written_clauses());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    macro_rules! expr_creator_testcase {
        ($ec: ident, $v: ident, $vars: expr, $expr: tt, $res: expr) => {
            let empty: [(Quantifier, Vec<isize>); 0] = [];
            expr_creator_testcase!($ec, $v, $vars, $expr, empty, $res);
        };

        ($ec: ident, $v: ident, $vars:expr, $expr: tt, $quants: expr, $res: expr) => {
            $ec = ExprCreator::<isize>::new();
            $v.clear();
            $v.push(BoolExprNode::single($ec.clone(), false));
            for _ in 0..$vars {
                $v.push(BoolExprNode::variable($ec.clone()));
            }
            let expr_index = $expr;
            let mut cnf_writer = CNFWriter::new(vec![]);
            test_println!("expr: {}", expr_index);
            $ec.borrow()
                .write(expr_index, $quants, &mut cnf_writer)
                .unwrap();
            assert_eq!($res, String::from_utf8_lossy(cnf_writer.inner()));
        };
    }

    #[test]
    fn test_expr_creator_trivial() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        // single operator testcases
        expr_creator_testcase!(ec, v, 1, { 0 }, "p cnf 1 1\n0\n");
        expr_creator_testcase!(ec, v, 1, { v[1].index }, "p cnf 1 0\n");
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() & v[2].clone()).index },
            concat!("p cnf 2 2\n", "1 0\n2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() | v[2].clone()).index },
            concat!("p cnf 2 1\n", "1 2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone().imp(v[2].clone())).index },
            concat!("p cnf 2 1\n", "-1 2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() ^ v[2].clone()).index },
            concat!("p cnf 2 2\n", "1 2 0\n-1 -2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone().bequal(v[2].clone())).index },
            concat!("p cnf 2 2\n", "1 -2 0\n-1 2 0\n")
        );

        // negation at root
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (!(v[1].clone() & v[2].clone())).index },
            concat!("p cnf 2 1\n", "-1 -2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let xp1 = v[1].clone() & v[2].clone();
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                ec.new_not(xp1)
            },
            concat!("p cnf 2 2\n", "1 0\n2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (!(v[1].clone() | v[2].clone())).index },
            concat!("p cnf 2 2\n", "-1 0\n-2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let xp1 = v[1].clone() | v[2].clone();
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                ec.new_not(xp1)
            },
            concat!("p cnf 2 1\n", "1 2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (!(v[1].clone() ^ v[2].clone())).index },
            concat!("p cnf 2 2\n", "1 -2 0\n-1 2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                ec.new_not(xp1)
            },
            concat!("p cnf 2 2\n", "1 2 0\n-1 -2 0\n")
        );

        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let mut ec = ec.borrow_mut();
                let nv1 = ec.new_not(v[1].index);
                ec.new_and(nv1, v[2].index)
            },
            concat!("p cnf 2 2\n", "-1 0\n2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            {
                let mut ec = ec.borrow_mut();
                let nv1 = ec.new_not(v[1].index);
                let nnv1 = ec.new_not(nv1);
                ec.new_and(v[2].index, nnv1)
            },
            concat!("p cnf 2 2\n", "2 0\n1 0\n")
        );
    }

    #[test]
    fn test_expr_creator_simple() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        // simple testcases
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()) | (v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 5\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()) & (v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 6\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 0\n5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()).imp(v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 5\n",
                "1 -2 4 0\n-1 2 4 0\n2 -3 -5 0\n-2 3 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((!(v[1].clone() ^ v[2].clone())) | (v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 5\n",
                "1 -2 4 0\n-1 2 4 0\n2 -3 -5 0\n-2 3 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[2].clone().bequal(v[3].clone());
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                let xp1 = ec.new_not(xp1);
                ec.new_or(xp1, xp2.index)
            },
            concat!(
                "p cnf 5 5\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((!(v[1].clone() ^ v[2].clone())).imp(v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 5\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[2].clone().bequal(v[3].clone());
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index);
                let xp1 = ec.new_not(xp1);
                ec.new_impl(xp1, xp2.index)
            },
            concat!(
                "p cnf 5 5\n",
                "1 -2 4 0\n-1 2 4 0\n2 -3 -5 0\n-2 3 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()) ^ (v[2].clone().bequal(v[3].clone()))).index },
            concat!(
                "p cnf 5 10\n",
                "1 2 -4 0\n-1 -2 -4 0\n1 -2 4 0\n-1 2 4 0\n",
                "2 -3 -5 0\n-2 3 -5 0\n2 3 5 0\n-2 -3 5 0\n4 5 0\n-4 -5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() & v[2].clone()) ^ (v[2].clone() & v[3].clone())).index },
            concat!(
                "p cnf 5 8\n",
                "1 -4 0\n2 -4 0\n-1 -2 4 0\n2 -5 0\n3 -5 0\n-2 -3 5 0\n4 5 0\n-4 -5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() | v[2].clone()) ^ (v[2].clone() | v[3].clone())).index },
            concat!(
                "p cnf 5 8\n",
                "-1 4 0\n-2 4 0\n1 2 -4 0\n-2 5 0\n-3 5 0\n2 3 -5 0\n4 5 0\n-4 -5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() & v[2].clone()).bequal(v[2].clone() & v[3].clone())).index },
            concat!(
                "p cnf 5 8\n",
                "1 -4 0\n2 -4 0\n-1 -2 4 0\n2 -5 0\n3 -5 0\n-2 -3 5 0\n4 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() | v[2].clone()).bequal(v[2].clone() | v[3].clone())).index },
            concat!(
                "p cnf 5 8\n",
                "-1 4 0\n-2 4 0\n1 2 -4 0\n-2 5 0\n-3 5 0\n2 3 -5 0\n4 -5 0\n-4 5 0\n"
            )
        );
    }

    #[test]
    fn test_expr_creator_more_complex() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        // more complicated, but simple
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()) | (v[3].clone() ^ v[4].clone()))
                    | ((v[5].clone() ^ v[6].clone()) | (v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 12 9\n",
                "1 2 -9 0\n-1 -2 -9 0\n3 4 -10 0\n-3 -4 -10 0\n5 6 -11 0\n-5 -6 -11 0\n",
                "7 8 -12 0\n-7 -8 -12 0\n9 10 11 12 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()) & (v[3].clone() ^ v[4].clone()))
                    & ((v[5].clone() ^ v[6].clone()) & (v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 12 12\n",
                "1 2 -9 0\n-1 -2 -9 0\n3 4 -10 0\n-3 -4 -10 0\n5 6 -11 0\n-5 -6 -11 0\n",
                "7 8 -12 0\n-7 -8 -12 0\n9 0\n10 0\n11 0\n12 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()).imp(v[3].clone() ^ v[4].clone()))
                    | ((v[5].clone() ^ v[6].clone()).imp(v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 12 9\n",
                "1 -2 9 0\n-1 2 9 0\n3 4 -10 0\n-3 -4 -10 0\n5 -6 11 0\n-5 6 11 0\n",
                "7 8 -12 0\n-7 -8 -12 0\n-9 10 -11 12 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()) | (v[3].clone() ^ v[4].clone()))
                    .imp((v[5].clone() ^ v[6].clone()) | (v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 13 11\n",
                "1 -2 10 0\n-1 2 10 0\n3 -4 11 0\n-3 4 11 0\n9 -10 0\n9 -11 0\n",
                "5 6 -12 0\n-5 -6 -12 0\n7 8 -13 0\n-7 -8 -13 0\n-9 12 13 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            8,
            {
                (((v[1].clone() ^ v[2].clone()) ^ (v[3].clone() ^ v[4].clone()))
                    ^ ((v[5].clone() ^ v[6].clone()) ^ (v[7].clone() ^ v[8].clone())))
                .index
            },
            concat!(
                "p cnf 14 26\n",
                "1 2 -10 0\n-1 -2 -10 0\n1 -2 10 0\n-1 2 10 0\n",
                "3 4 -11 0\n-3 -4 -11 0\n3 -4 11 0\n-3 4 11 0\n",
                "-9 10 11 0\n-9 -10 -11 0\n9 10 -11 0\n9 -10 11 0\n",
                "5 6 -13 0\n-5 -6 -13 0\n5 -6 13 0\n-5 6 13 0\n",
                "7 8 -14 0\n-7 -8 -14 0\n7 -8 14 0\n-7 8 14 0\n",
                "-12 13 14 0\n-12 -13 -14 0\n12 13 -14 0\n12 -13 14 0\n",
                "9 12 0\n-9 -12 0\n"
            )
        );
    }

    #[test]
    fn test_expr_creator_join_more_time() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) | (xp1 & xp2)).index
            },
            concat!(
                "p cnf 7 7\n",
                "1 2 -5 0\n-1 -2 -5 0\n3 4 -6 0\n-3 -4 -6 0\n5 -7 0\n6 -7 0\n5 6 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) | !(xp1 & xp2)).index
            },
            concat!(
                "p cnf 7 10\n",
                "1 2 -5 0\n-1 -2 -5 0\n1 -2 5 0\n-1 2 5 0\n",
                "3 4 -6 0\n-3 -4 -6 0\n3 -4 6 0\n-3 4 6 0\n",
                "-5 -6 7 0\n5 6 -7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) | (xp1.imp(xp2))).index
            },
            concat!(
                "p cnf 6 7\n",
                "1 2 -5 0\n-1 -2 -5 0\n1 -2 5 0\n-1 2 5 0\n3 4 -6 0\n-3 -4 -6 0\n1 -1 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) | ((!xp1) | xp2)).index
            },
            concat!(
                "p cnf 6 7\n",
                "1 2 -5 0\n-1 -2 -5 0\n1 -2 5 0\n-1 2 5 0\n3 4 -6 0\n-3 -4 -6 0\n1 -1 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() ^ v[2].clone();
                let xp2 = v[3].clone() ^ v[4].clone();
                ((xp1.clone() | xp2.clone()) & (xp1.imp(xp2))).index
            },
            concat!(
                "p cnf 8 10\n",
                "1 2 -6 0\n-1 -2 -6 0\n1 -2 6 0\n-1 2 6 0\n3 4 -7 0\n-3 -4 -7 0\n",
                "-5 6 7 0\n-6 7 -8 0\n5 0\n8 0\n"
            )
        );

        // not joining
        expr_creator_testcase!(
            ec,
            v,
            5,
            { (!((v[1].clone() | v[2].clone()).imp(v[3].clone())) | v[4].clone()).index },
            concat!("p cnf 7 4\n", "1 2 -7 0\n6 7 0\n-3 6 0\n4 -6 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            { (!((v[1].clone() | v[2].clone()).imp(v[2].clone())) | v[3].clone()).index },
            concat!("p cnf 6 4\n", "1 2 -6 0\n5 6 0\n-2 5 0\n3 -5 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            5,
            { (!((v[1].clone() | v[2].clone()) | (v[3].clone())) | v[4].clone()).index },
            concat!("p cnf 6 4\n", "-1 6 0\n-2 6 0\n-3 6 0\n4 -6 0\n")
        );

        // joinings of conjunction and disjunction
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((xp1.clone() | v[3].clone()) & (xp1 | v[4].clone())).index
            },
            concat!("p cnf 7 5\n", "1 2 -6 0\n3 -5 6 0\n4 6 -7 0\n5 0\n7 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((xp1.clone() | v[3].clone()) | (xp1 | v[4].clone())).index
            },
            concat!("p cnf 5 2\n", "1 2 -5 0\n3 4 5 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((xp1.clone() | v[3].clone()) & (!xp1 | v[4].clone())).index
            },
            concat!(
                "p cnf 7 7\n",
                "-1 6 0\n-2 6 0\n1 2 -6 0\n3 -5 6 0\n4 -6 -7 0\n5 0\n7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((xp1.clone() | v[3].clone()) | (!xp1 | v[4].clone())).index
            },
            concat!("p cnf 5 4\n", "-1 5 0\n-2 5 0\n1 2 -5 0\n1 -1 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() | v[2].clone();
                ((!xp1.clone() | v[3].clone()) | (xp1 | v[4].clone())).index
            },
            concat!("p cnf 5 4\n", "-1 5 0\n-2 5 0\n1 2 -5 0\n1 -1 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) | (xp1 & v[4].clone())).index
            },
            concat!(
                "p cnf 7 7\n",
                "1 -6 0\n2 -6 0\n-5 6 0\n3 -5 0\n6 -7 0\n4 -7 0\n5 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) & (xp1 & v[4].clone())).index
            },
            concat!("p cnf 5 6\n", "1 -5 0\n2 -5 0\n5 0\n3 0\n5 0\n4 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) | (!xp1 & v[4].clone())).index
            },
            concat!(
                "p cnf 7 8\n",
                "1 -6 0\n2 -6 0\n-1 -2 6 0\n-5 6 0\n3 -5 0\n-6 -7 0\n4 -7 0\n5 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) & (!xp1 & v[4].clone())).index
            },
            concat!(
                "p cnf 5 7\n",
                "1 -5 0\n2 -5 0\n-1 -2 5 0\n5 0\n3 0\n-5 0\n4 0\n"
            )
        );

        expr_creator_testcase!(
            ec,
            v,
            5,
            {
                let xp1 = (v[1].clone() | v[5].clone()).imp(v[2].clone());
                ((xp1.clone() | v[3].clone()) & (!xp1 | v[4].clone())).index
            },
            concat!(
                "p cnf 9 10\n",
                "-1 8 0\n-5 8 0\n1 5 -8 0\n7 8 0\n-2 7 0\n2 -7 -8 0\n",
                "3 -6 7 0\n4 -7 -9 0\n6 0\n9 0\n"
            )
        );
    }

    #[test]
    fn test_expr_creator_complex() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            3,
            {
                let xp1 = !v[1].clone() & v[2].clone();
                (xp1.clone() | !v[3].clone() ^ (v[1].clone() | v[2].clone())).index
            },
            concat!(
                "p cnf 6 8\n",
                "-1 -4 0\n2 -4 0\n-1 6 0\n-2 6 0\n1 2 -6 0\n-3 -5 6 0\n3 -5 -6 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            5,
            {
                let xp1 = v[1].clone().imp(v[2].clone());
                let xp2 = v[3].clone().imp(v[2].clone());
                let xp3 = (xp1.clone() ^ xp2.clone()) | v[4].clone();
                let xp4 = (xp1.clone().bequal(xp2.clone())) & v[5].clone();
                let xp5 = (xp1.clone() | xp3.clone()) & (xp2.clone() | xp4.clone());
                let xp6 = (xp1.clone() & !xp3.clone()) | (!xp2.clone() & xp4.clone());
                (xp6.clone().imp(xp5.clone())).index
            },
            concat!(
                "p cnf 17 25\n",
                "1 8 0\n-2 8 0\n-1 2 -8 0\n3 11 0\n-2 11 0\n2 -3 -11 0\n8 -10 11 0\n",
                "-8 -10 -11 0\n4 -9 10 0\n7 -8 9 0\n8 -11 -14 0\n-8 11 -14 0\n8 11 14 0\n",
                "-8 -11 14 0\n-13 14 0\n5 -13 0\n-5 13 -14 0\n11 12 -13 0\n6 -7 0\n",
                "6 -12 0\n8 9 -16 0\n11 13 -17 0\n-15 16 0\n-15 17 0\n-6 15 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            9,
            {
                let c1 =
                    ((v[2].clone() ^ v[3].clone()) & v[1].clone()) | (v[2].clone() & v[3].clone());
                let c2 = ((v[4].clone() ^ v[5].clone()) & c1) | (v[4].clone() & v[5].clone());
                let c3 = ((v[6].clone() ^ v[7].clone()) & c2) | (v[6].clone() & v[7].clone());
                (((v[8].clone() ^ v[9].clone()) & c3) | (v[8].clone() & v[9].clone())).index
            },
            concat!(
                "p cnf 24 28\n",
                "8 9 -11 0\n-8 -9 -11 0\n6 7 -14 0\n-6 -7 -14 0\n4 5 -17 0\n-4 -5 -17 0\n",
                "2 3 -20 0\n-2 -3 -20 0\n-19 20 0\n1 -19 0\n2 -21 0\n3 -21 0\n-18 19 21 0\n",
                "-16 17 0\n-16 18 0\n4 -22 0\n5 -22 0\n-15 16 22 0\n-13 14 0\n-13 15 0\n",
                "6 -23 0\n7 -23 0\n-12 13 23 0\n-10 11 0\n-10 12 0\n8 -24 0\n9 -24 0\n10 24 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            9,
            {
                let c1 =
                    ((v[2].clone() ^ v[3].clone()) & v[1].clone()) | (v[2].clone() & v[3].clone());
                let c2 = ((v[4].clone() ^ v[5].clone()) & c1) | (v[4].clone() & v[5].clone());
                let c3 =
                    ((v[6].clone() ^ v[7].clone()) & c2.clone()) | (v[6].clone() & v[7].clone());
                let c4 = ((v[8].clone() ^ v[9].clone()) & c3) | (v[8].clone() & v[9].clone());
                (c2.imp(c4)).index
            },
            concat!(
                "p cnf 24 40\n",
                "4 5 -12 0\n-4 -5 -12 0\n4 -5 12 0\n-4 5 12 0\n2 3 -15 0\n-2 -3 -15 0\n",
                "2 -3 15 0\n-2 3 15 0\n-14 15 0\n1 -14 0\n-1 14 -15 0\n2 -16 0\n3 -16 0\n",
                "-2 -3 16 0\n13 -14 0\n13 -16 0\n-13 14 16 0\n-11 12 0\n-11 13 0\n",
                "11 -12 -13 0\n4 -17 0\n5 -17 0\n-4 -5 17 0\n10 -11 0\n10 -17 0\n-10 11 17 0\n",
                "8 9 -19 0\n-8 -9 -19 0\n6 7 -22 0\n-6 -7 -22 0\n-21 22 0\n10 -21 0\n6 -23 0\n",
                "7 -23 0\n-20 21 23 0\n-18 19 0\n-18 20 0\n8 -24 0\n9 -24 0\n-10 18 24 0\n"
            )
        );
    }

    #[test]
    fn test_expr_creator_quantsets() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) | (!xp1 & v[4].clone())).index
            },
            [(Quantifier::Exists, [1]), (Quantifier::ForAll, [2])],
            concat!(
                "p cnf 7 8\n",
                "e 1 0\na 2 0\ne 5 6 7 0\n",
                "1 -6 0\n2 -6 0\n-1 -2 6 0\n-5 6 0\n3 -5 0\n-6 -7 0\n4 -7 0\n5 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            4,
            {
                let xp1 = v[1].clone() & v[2].clone();
                ((xp1.clone() & v[3].clone()) | (!xp1 & v[4].clone())).index
            },
            [
                (Quantifier::Exists, [1]),
                (Quantifier::ForAll, [2]),
                (Quantifier::Exists, [3])
            ],
            concat!(
                "p cnf 7 8\n",
                "e 1 0\na 2 0\ne 3 5 6 7 0\n",
                "1 -6 0\n2 -6 0\n-1 -2 6 0\n-5 6 0\n3 -5 0\n-6 -7 0\n4 -7 0\n5 7 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() & v[2].clone()).index },
            [(Quantifier::Exists, [1]), (Quantifier::ForAll, [2])],
            concat!("p cnf 2 2\n", "e 1 0\na 2 0\n", "1 0\n2 0\n")
        );
        expr_creator_testcase!(
            ec,
            v,
            5,
            { (!((v[1].clone() | v[2].clone()).imp(v[3].clone())) | v[4].clone()).index },
            [(Quantifier::Exists, [1, 2]), (Quantifier::ForAll, [3, 4])],
            concat!(
                "p cnf 7 4\n",
                "e 1 2 0\na 3 4 0\ne 6 7 0\n",
                "1 2 -7 0\n6 7 0\n-3 6 0\n4 -6 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            5,
            { (!((v[1].clone() | v[2].clone()).imp(v[3].clone())) | v[4].clone()).index },
            [(Quantifier::ForAll, [1, 2]), (Quantifier::Exists, [3, 4])],
            concat!(
                "p cnf 7 4\n",
                "a 1 2 0\ne 3 4 6 7 0\n",
                "1 2 -7 0\n6 7 0\n-3 6 0\n4 -6 0\n"
            )
        );
    }

    use generic_array::typenum::*;

    #[test]
    fn test_expr_creator_intexprs() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        // single operator testcases
        expr_creator_testcase!(
            ec,
            v,
            12,
            {
                let x1 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[1..7])).unwrap();
                let x2 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[7..13])).unwrap();
                (x1.equal(x2)).index
            },
            concat!(
                "p cnf 18 18\n",
                "1 -7 -13 0\n-1 7 -13 0\n2 -8 -14 0\n-2 8 -14 0\n3 -9 -15 0\n-3 9 -15 0\n",
                "4 -10 -16 0\n-4 10 -16 0\n5 -11 -17 0\n-5 11 -17 0\n6 -12 -18 0\n-6 12 -18 0\n",
                "13 0\n14 0\n15 0\n16 0\n17 0\n18 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            12,
            {
                let x1 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[1..7])).unwrap();
                let x2 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[7..13])).unwrap();
                (x1.less_than(x2)).index
            },
            concat!(
                "p cnf 31 36\n",
                "6 -12 -14 0\n-6 12 -14 0\n5 -11 -17 0\n-5 11 -17 0\n4 -10 -20 0\n-4 10 -20 0\n",
                "3 -9 -23 0\n-3 9 -23 0\n2 -8 -26 0\n-2 8 -26 0\n-25 26 0\n-1 -25 0\n7 -25 0\n",
                "-2 -27 0\n8 -27 0\n-24 25 27 0\n-22 23 0\n-22 24 0\n-3 -28 0\n9 -28 0\n",
                "-21 22 28 0\n-19 20 0\n-19 21 0\n-4 -29 0\n10 -29 0\n-18 19 29 0\n-16 17 0\n",
                "-16 18 0\n-5 -30 0\n11 -30 0\n-15 16 30 0\n-13 14 0\n-13 15 0\n-6 -31 0\n",
                "12 -31 0\n13 31 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            13,
            {
                let x1 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[1..7])).unwrap();
                let x2 =
                    IntExprNode::<isize, U6, false>::from_boolexprs(Vec::from(&v[7..13])).unwrap();
                (!x1.less_than(x2) ^ v[13].clone()).index
            },
            concat!(
                "p cnf 33 68\n6 -12 -16 0\n-6 12 -16 0\n6 12 16 0\n-6 -12 16 0\n5 -11 -19 0\n",
                "-5 11 -19 0\n5 11 19 0\n-5 -11 19 0\n4 -10 -22 0\n-4 10 -22 0\n4 10 22 0\n",
                "-4 -10 22 0\n3 -9 -25 0\n-3 9 -25 0\n3 9 25 0\n-3 -9 25 0\n2 -8 -28 0\n",
                "-2 8 -28 0\n2 8 28 0\n-2 -8 28 0\n-27 28 0\n-1 -27 0\n7 -27 0\n1 -7 27 -28 0\n",
                "-2 -29 0\n8 -29 0\n2 -8 29 0\n26 -27 0\n26 -29 0\n-26 27 29 0\n-24 25 0\n",
                "-24 26 0\n24 -25 -26 0\n-3 -30 0\n9 -30 0\n3 -9 30 0\n23 -24 0\n23 -30 0\n",
                "-23 24 30 0\n-21 22 0\n-21 23 0\n21 -22 -23 0\n-4 -31 0\n10 -31 0\n4 -10 31 0\n",
                "20 -21 0\n20 -31 0\n-20 21 31 0\n-18 19 0\n-18 20 0\n18 -19 -20 0\n-5 -32 0\n",
                "11 -32 0\n5 -11 32 0\n17 -18 0\n17 -32 0\n-17 18 32 0\n-15 16 0\n-15 17 0\n",
                "15 -16 -17 0\n-6 -33 0\n12 -33 0\n6 -12 33 0\n14 -15 0\n14 -33 0\n-14 15 33 0\n",
                "13 -14 0\n-13 14 0\n"
            )
        );
    }
}
