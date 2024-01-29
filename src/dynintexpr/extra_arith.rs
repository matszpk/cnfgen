// extra_arith.rs - extra arithmetic for dynintexpr.
//
// cnfgen - Generate the DIMACS CNF formula from operations
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
//! The module contains extra operators definitions.

use std::fmt::Debug;

use crate::dynintexpr::DynIntExprNode;

use super::*;
use crate::VarLit;

impl<T, const SIGN: bool> ExtraOps for DynIntExprNode<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;
    type BoolOutput = BoolExprNode<T>;

    fn count_zeros(self) -> Self::Output {
        (!self).count_ones()
    }

    fn count_ones(self) -> Self::Output {
        let n = self.indexes.len();
        let mut elems = (0..n)
            .map(|x| DynIntExprNode::filled_expr(1, self.bit(x)))
            .collect::<Vec<_>>();
        let mut bits = 1;
        let creator = self.creator.clone();
        while bits < (n << 1) {
            let elem_len = elems.len();
            let mut new_elems = vec![];
            for i in 0..(elem_len >> 1) {
                // get elements: a + b with zero bit extension
                let a =
                    elems[i << 1]
                        .clone()
                        .concat(DynIntExprNode::filled(creator.clone(), 1, false));
                let b = elems[(i << 1) + 1].clone().concat(DynIntExprNode::filled(
                    creator.clone(),
                    1,
                    false,
                ));
                // summarize it
                new_elems.push(a.addc(b, BoolExprNode::single_value(creator.clone(), false)));
            }
            if (elem_len & 1) != 0 {
                // add last element if number of elements is odd
                new_elems.push(elems.last().unwrap().clone().concat(DynIntExprNode::filled(
                    creator.clone(),
                    1,
                    false,
                )));
            }
            elems = new_elems;
            bits <<= 1;
        }
        // conversion to int
        DynIntExprNode::from_boolexprs((0..n).map(|x| {
            if x < elems[0].bitnum() {
                elems[0].bit(x)
            } else {
                BoolExprNode::single_value(creator.clone(), false)
            }
        }))
    }

    fn leading_zeros(self) -> Self::Output {
        let n = self.indexes.len();
        let creator = self.creator.clone();
        let mut out_bits = vec![];
        let mut enable = BoolExprNode::single_value(creator.clone(), true);
        for i in 0..n {
            let b = !self.bit(n - i - 1) & enable;
            out_bits.push(b.clone());
            enable = b;
        }
        DynIntExprNode::from_boolexprs(out_bits).count_ones()
    }

    fn leading_ones(self) -> Self::Output {
        (!self).leading_zeros()
    }

    fn trailing_zeros(self) -> Self::Output {
        let n = self.indexes.len();
        let creator = self.creator.clone();
        let mut out_bits = vec![];
        let mut enable = BoolExprNode::single_value(creator.clone(), true);
        for i in 0..n {
            let b = !self.bit(i) & enable;
            out_bits.push(b.clone());
            enable = b;
        }
        DynIntExprNode::from_boolexprs(out_bits).count_ones()
    }

    fn trailing_ones(self) -> Self::Output {
        (!self).trailing_zeros()
    }

    fn is_power_of_two(self) -> Self::BoolOutput {
        let n = self.indexes.len();
        let creator = self.creator.clone();
        let mut s = BoolExprNode::single_value(creator.clone(), false);
        let mut c = BoolExprNode::single_value(creator.clone(), false);
        for i in 0..n {
            let (s1, c1) = half_adder(s.clone(), self.bit(i));
            s = s1;
            c |= c1;
        }
        s & !c
    }

    fn reverse_bits(self) -> Self::Output {
        let n = self.indexes.len();
        DynIntExprNode::from_boolexprs((0..n).map(|x| self.bit(n - x - 1)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intexpr::IntExprNode;
    use generic_array::typenum::*;

    macro_rules! test_expr_node_op {
        ($sign:expr, $op:ident) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 12);
            let res = x1.$op();

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U12, $sign>::variable(exp_ec.clone());
            let exp = x1.$op();

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let res = x1.$op();

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = x1.$op();

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 8);
            let res = x1.$op();

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U8, $sign>::variable(exp_ec.clone());
            let exp = x1.$op();

            assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    macro_rules! test_expr_node_bitop {
        ($sign:expr, $op:ident) => {
            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 12);
            let res = x1.$op();

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U12, $sign>::variable(exp_ec.clone());
            let exp = x1.$op();

            assert_eq!(exp.index, res.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 10);
            let res = x1.$op();

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U10, $sign>::variable(exp_ec.clone());
            let exp = x1.$op();

            assert_eq!(exp.index, res.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());

            let ec = ExprCreator::new();
            let x1 = DynIntExprNode::<isize, $sign>::variable(ec.clone(), 8);
            let res = x1.$op();

            let exp_ec = ExprCreator::new();
            let x1 = IntExprNode::<isize, U8, $sign>::variable(exp_ec.clone());
            let exp = x1.$op();

            assert_eq!(exp.index, res.index);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        };
    }

    #[test]
    fn test_expr_node_ops() {
        test_expr_node_op!(false, count_ones);
        test_expr_node_op!(true, count_ones);
        test_expr_node_op!(false, count_zeros);
        test_expr_node_op!(true, count_zeros);
        test_expr_node_op!(false, leading_zeros);
        test_expr_node_op!(true, leading_zeros);
        test_expr_node_op!(false, leading_ones);
        test_expr_node_op!(true, leading_ones);
        test_expr_node_op!(false, trailing_zeros);
        test_expr_node_op!(true, trailing_zeros);
        test_expr_node_op!(false, trailing_ones);
        test_expr_node_op!(true, trailing_ones);
        test_expr_node_op!(false, reverse_bits);
        test_expr_node_op!(true, reverse_bits);
        test_expr_node_bitop!(false, is_power_of_two);
        test_expr_node_bitop!(true, is_power_of_two);
    }
}
