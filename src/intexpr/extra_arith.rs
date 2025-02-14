// extra_arith.rs - extra arithmetic for intexpr.

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module contains extra operators definitions.

use std::fmt::Debug;

use crate::dynintexpr::DynIntExprNode;

use generic_array::*;

use super::*;
use crate::VarLit;

impl<T, N, const SIGN: bool> ExtraOps for IntExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
{
    type Output = Self;
    type BoolOutput = BoolExprNode<T>;

    fn count_zeros(self) -> Self::Output {
        (!self).count_ones()
    }

    fn count_ones(self) -> Self::Output {
        let mut elems = (0..N::USIZE)
            .map(|x| DynIntExprNode::filled_expr(1, self.bit(x)))
            .collect::<Vec<_>>();
        let mut bits = 1;
        let creator = self.creator.clone();
        while bits < (N::USIZE << 1) {
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
        IntExprNode::from_boolexprs((0..N::USIZE).map(|x| {
            if x < elems[0].bitnum() {
                elems[0].bit(x)
            } else {
                BoolExprNode::single_value(creator.clone(), false)
            }
        }))
        .unwrap()
    }

    fn leading_zeros(self) -> Self::Output {
        let creator = self.creator.clone();
        let mut out_bits = vec![];
        let mut enable = BoolExprNode::single_value(creator.clone(), true);
        for i in 0..N::USIZE {
            let b = !self.bit(N::USIZE - i - 1) & enable;
            out_bits.push(b.clone());
            enable = b;
        }
        IntExprNode::from_boolexprs(out_bits).unwrap().count_ones()
    }

    fn leading_ones(self) -> Self::Output {
        (!self).leading_zeros()
    }

    fn trailing_zeros(self) -> Self::Output {
        let creator = self.creator.clone();
        let mut out_bits = vec![];
        let mut enable = BoolExprNode::single_value(creator.clone(), true);
        for i in 0..N::USIZE {
            let b = !self.bit(i) & enable;
            out_bits.push(b.clone());
            enable = b;
        }
        IntExprNode::from_boolexprs(out_bits).unwrap().count_ones()
    }

    fn trailing_ones(self) -> Self::Output {
        (!self).trailing_zeros()
    }

    fn is_power_of_two(self) -> Self::BoolOutput {
        let creator = self.creator.clone();
        let mut s = BoolExprNode::single_value(creator.clone(), false);
        let mut c = BoolExprNode::single_value(creator.clone(), false);
        for i in 0..N::USIZE {
            let (s1, c1) = half_adder(s.clone(), self.bit(i));
            s = s1;
            c |= c1;
        }
        s & !c
    }

    fn reverse_bits(self) -> Self::Output {
        IntExprNode::from_boolexprs((0..N::USIZE).map(|x| self.bit(N::USIZE - x - 1))).unwrap()
    }
}
