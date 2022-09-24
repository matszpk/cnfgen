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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpJoin {
    Nothing,
    Conj,
    Disjunc,
}

//

#[derive(Debug, PartialEq, Eq)]
pub struct ExprCreator<T: VarLit + Debug> {
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

trait LiteralsWriter {
    fn write_literals<T, I>(&mut self, iter: I) -> Result<(), writer::Error>
    where
        T: VarLit + Neg<Output = T>,
        I: IntoIterator<Item = Literal<T>>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug;
}

struct ClauseCounter(usize);

impl LiteralsWriter for ClauseCounter {
    fn write_literals<T, I>(&mut self, _: I) -> Result<(), writer::Error>
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
    fn write_literals<T, I>(&mut self, iter: I) -> Result<(), writer::Error>
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

    fn write_clauses<LW: LiteralsWriter>(
        &self,
        start: usize,
        dep_nodes: &Vec<DepNode<T>>,
        cnf: &mut LW,
    ) -> Result<(), writer::Error> {
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
            normal_usage: bool,
            negated_usage: bool,
            op_join: OpJoin,
            not_join: bool,
            negated: bool,
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
                    op_join: OpJoin::Nothing,
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

        while !stack.is_empty() {
            {
                // push child parent node linkvar to joining clause
                let (negated, node_index) = {
                    let top = stack.last().unwrap();
                    (top.negated, top.node_index)
                };
                if let JoiningClause::Join(stackpos) = stack.last().unwrap().joining_clause {
                    let join_entry = stack.get_mut(stackpos).unwrap();
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
                    println!("WcPZ {}: {:?} sp:{}", node_index, linkvar, stackpos);
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
                let conj = node.is_conj();
                let disjunc = node.is_disjunc();

                /////////////
                if top.path == 0 && (top.start || dep_node.linkvar.is_some()) {
                    top.joining_clause = JoiningClause::new(&node);
                    println!(
                        "Wc: {} {}: {:?} {:?}",
                        node_index, top.path, dep_node.linkvar, top.joining_clause
                    );
                }
                // generate joining clause for next
                let next_clause = if conj || disjunc {
                    if let JoiningClause::Join(_) = top.joining_clause {
                        top.joining_clause.clone()
                    } else {
                        JoiningClause::Join(stacklen)
                    }
                } else if node.is_xor_or_equal() {
                    JoiningClause::Join(stacklen)
                } else if matches!(node, Node::Negated(_)) {
                    top.joining_clause.clone()
                } else {
                    JoiningClause::Nothing
                };
                println!(
                    "WcN: {} {} {}: {:?} {:?}",
                    node_index, top.path, stacklen, next_clause, top.op_join
                );
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
                    let start = matches!(node, Node::Negated(_)) && top.start;

                    let negated = if top.not_join && not_join && matches!(node, Node::Negated(_)) {
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
                            op_join,
                            not_join,
                            negated,
                            start,
                            joining_clause: next_clause,
                        });
                    }
                } else {
                    println!("WPP: {} {}", node_index, top.path);
                    do_pop = true;
                    visited[node_index] = true;
                }
            } else {
                stack.pop().unwrap();
            }

            if do_pop {
                let top = stack.pop().unwrap();
                let dep_node = dep_nodes.get(top.node_index).unwrap();
                println!(
                    "WW {} {}: {:?}",
                    top.node_index, top.path, top.joining_clause
                );
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
        Ok(())
    }

    // TODO: try write, writer. first - determine real dependencies and
    // real usage (normal and negated) - and mark them.
    pub fn write<W: Write>(
        &self,
        start: usize,
        cnf: &mut CNFWriter<W>,
    ) -> Result<(), writer::Error> {
        let mut dep_nodes = vec![DepNode::default(); self.nodes.len()];
        let mut total_var_count = self.var_count();

        println!(
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

                if !visited[node_index] {
                    let first_path = top.path == 0 && !matches!(node, Node::Single(_));
                    let second_path = top.path == 1 && !node.is_unary();

                    if !node.is_unary() && second_path {
                        dep_nodes[node_index].parent_count += 1;
                        visited[node_index] = true;
                    }

                    //println!("Count: {}: {} {} {}", node_index, first_path, second_path,
                    //        dep_nodes[node_index].parent_count);

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

        println!(
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
                normal_usage: bool,
                negated_usage: bool,
                op_join: OpJoin,
                not_join: bool,
                negated: bool,
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
            //dep_nodes[start].normal_usage = true;

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

                    let new_var = !top.start && (new_var || dep_node.parent_count > 1);

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
                        let start = matches!(node, Node::Negated(_)) && top.start;

                        let negated =
                            if top.not_join && not_join && matches!(node, Node::Negated(_)) {
                                !top.negated
                            } else {
                                not_join
                            };

                        println!(
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

        println!(
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

        // write clauses
        self.write_clauses(start, &dep_nodes, cnf)?;

        assert_eq!(clause_count, cnf.written_clauses());
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolexpr::*;

    macro_rules! expr_creator_testcase {
        ($ec: ident, $v: ident, $vars:expr, $expr: tt, $res: expr) => {{
            $ec = ExprCreator::<isize>::new();
            $v.clear();
            $v.push(ExprNode::single($ec.clone(), false));
            for _ in 0..$vars {
                $v.push(ExprNode::variable($ec.clone()));
            }
            let expr_index = $expr;
            let mut cnf_writer = CNFWriter::new(vec![]);
            println!("expr: {}", expr_index);
            $ec.borrow().write(expr_index, &mut cnf_writer).unwrap();
            assert_eq!($res, String::from_utf8_lossy(cnf_writer.inner()));
        }};
    }

    #[test]
    fn test_expr_creator_simple() {
        let mut v = vec![];
        #[allow(unused_assignments)]
        let mut ec = ExprCreator::<isize>::new();
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() & v[2].clone()).index() },
            concat!(
                "p cnf 2 2\n",
                "1 0\n2 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() | v[2].clone()).index() },
            concat!(
                "p cnf 2 1\n",
                "1 2 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone().imp(v[2].clone())).index() },
            concat!(
                "p cnf 2 1\n",
                "-1 2 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone() ^ v[2].clone()).index() },
            concat!(
                "p cnf 2 2\n",
                "1 2 0\n-1 -2 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (v[1].clone().equal(v[2].clone())).index() },
            concat!(
                "p cnf 2 2\n",
                "1 -2 0\n-1 2 0\n"
            )
        );
        
        expr_creator_testcase!(
            ec,
            v,
            2,
            { (!(v[1].clone() & v[2].clone())).index() },
            concat!(
                "p cnf 2 1\n",
                "-1 -2 0\n"
            )
        );
        
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()) | (v[2].clone().equal(v[3].clone()))).index() },
            concat!(
                "p cnf 5 5\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()) & (v[2].clone().equal(v[3].clone()))).index() },
            concat!(
                "p cnf 5 6\n",
                "1 2 -4 0\n-1 -2 -4 0\n2 -3 -5 0\n-2 3 -5 0\n4 0\n5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() ^ v[2].clone()).imp(v[2].clone().equal(v[3].clone()))).index() },
            concat!(
                "p cnf 5 5\n",
                "1 -2 4 0\n-1 2 4 0\n2 -3 -5 0\n-2 3 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((!(v[1].clone() ^ v[2].clone())) | (v[2].clone().equal(v[3].clone()))).index() },
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
                let xp2 = v[2].clone().equal(v[3].clone());
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index());
                let xp1 = ec.new_not(xp1);
                ec.new_or(xp1, xp2.index())
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
            { ((!(v[1].clone() ^ v[2].clone())).imp(v[2].clone().equal(v[3].clone()))).index() },
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
                let xp2 = v[2].clone().equal(v[3].clone());
                let mut ec = ec.borrow_mut();
                let xp1 = ec.new_not(xp1.index());
                let xp1 = ec.new_not(xp1);
                ec.new_impl(xp1, xp2.index())
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
            { ((v[1].clone() ^ v[2].clone()) ^ (v[2].clone().equal(v[3].clone()))).index() },
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
            { ((v[1].clone() & v[2].clone()) ^ (v[2].clone() & v[3].clone())).index() },
            concat!(
                "p cnf 5 8\n",
                "1 -4 0\n2 -4 0\n-1 -2 4 0\n2 -5 0\n3 -5 0\n-2 -3 5 0\n4 5 0\n-4 -5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() | v[2].clone()) ^ (v[2].clone() | v[3].clone())).index() },
            concat!(
                "p cnf 5 8\n",
                "-1 4 0\n-2 4 0\n1 2 -4 0\n-2 5 0\n-3 5 0\n2 3 -5 0\n4 5 0\n-4 -5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() & v[2].clone()).equal(v[2].clone() & v[3].clone())).index() },
            concat!(
                "p cnf 5 8\n",
                "1 -4 0\n2 -4 0\n-1 -2 4 0\n2 -5 0\n3 -5 0\n-2 -3 5 0\n4 -5 0\n-4 5 0\n"
            )
        );
        expr_creator_testcase!(
            ec,
            v,
            3,
            { ((v[1].clone() | v[2].clone()).equal(v[2].clone() | v[3].clone())).index() },
            concat!(
                "p cnf 5 8\n",
                "-1 4 0\n-2 4 0\n1 2 -4 0\n-2 5 0\n-3 5 0\n2 3 -5 0\n4 -5 0\n-4 5 0\n"
            )
        );
    }
}
