// int_utils.rs - integer utilities
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
//! The module to generate CNF clauses from integer expressions.

use std::cell::RefCell;
use std::fmt::Debug;
use std::ops::Neg;
use std::rc::Rc;

use crate::boolexpr::{bool_ite, half_adder, opt_full_adder};
use crate::{BitVal, BoolExprNode, ExprCreator, VarLit};

pub(super) fn gen_dadda_mult<T>(
    creator: Rc<RefCell<ExprCreator<T>>>,
    matrix: &mut [Vec<usize>],
) -> Vec<usize>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    let max_col_size = matrix.iter().map(|col| col.len()).max().unwrap();
    let mut step_sizes = vec![];
    {
        let mut max_step_size = 2usize;
        while max_step_size < max_col_size {
            step_sizes.push(max_step_size);
            max_step_size += max_step_size >> 1;
        }
    }
    let mut extracol: Vec<usize> = vec![];
    let mut next_extracol: Vec<usize> = vec![];
    // main routine
    let matrixlen = matrix.len();
    for new_column_size in step_sizes.iter().rev() {
        for (coli, col) in matrix.iter_mut().enumerate() {
            next_extracol.clear();
            if col.len() + extracol.len() > *new_column_size {
                let cells_to_reduce = extracol.len() + col.len() - *new_column_size;
                let mut src = col.len() - cells_to_reduce - ((cells_to_reduce + 1) >> 1);
                let mut dest = src;
                while src < col.len() {
                    let a = BoolExprNode::new(creator.clone(), col[src]);
                    let b = BoolExprNode::new(creator.clone(), col[src + 1]);
                    // if src + 2 < col.len() {
                    //     println!(
                    //         "cell: {}: {}: {} {} {}",
                    //         new_column_size,
                    //         coli,
                    //         src,
                    //         src + 1,
                    //         src + 2
                    //     );
                    // } else {
                    //     println!("cell: {}: {}: {} {}", new_column_size, coli, src, src + 1);
                    // }
                    if coli + 1 < matrixlen {
                        let (s, c) = if src + 2 < col.len() {
                            // full adder
                            opt_full_adder(a, b, BoolExprNode::new(creator.clone(), col[src + 2]))
                        } else {
                            // half adder
                            half_adder(a, b)
                        };
                        col[dest] = s.index;
                        next_extracol.push(c.index);
                    } else {
                        // only sum, ignore carry
                        col[dest] = if src + 2 < col.len() {
                            // full adder
                            a ^ b ^ BoolExprNode::new(creator.clone(), col[src + 2])
                        } else {
                            // half adder
                            a ^ b
                        }
                        .index;
                    }
                    src += 3;
                    dest += 1;
                }
                col.resize(dest, 0);
            }
            col.extend(extracol.iter());
            std::mem::swap(&mut extracol, &mut next_extracol);
        }
    }

    // last phase
    let mut output = vec![0; matrix.len()];
    let mut c = BoolExprNode::new(creator.clone(), 0); // false
    for (i, col) in matrix.iter().enumerate().take(matrix.len() - 1) {
        (output[i], c) = if col.len() == 2 {
            let (s0, c0) = opt_full_adder(
                BoolExprNode::new(creator.clone(), col[0]),
                BoolExprNode::new(creator.clone(), col[1]),
                c,
            );
            (s0.index, c0)
        } else {
            let (s0, c0) = half_adder(BoolExprNode::new(creator.clone(), col[0]), c);
            (s0.index, c0)
        };
    }
    let col = matrix.last().unwrap();
    output[matrix.len() - 1] = if col.len() == 2 {
        BoolExprNode::new(creator.clone(), col[0]) ^ BoolExprNode::new(creator, col[1]) ^ c
    } else if col.len() == 1 {
        BoolExprNode::new(creator, col[0]) ^ c
    } else {
        c
    }
    .index;

    output
}

pub(super) fn gen_dadda_matrix<'a, T>(
    creator: Rc<RefCell<ExprCreator<T>>>,
    avector: &'a [usize],
    bvector: &'a [usize],
    col_num: usize,
) -> Vec<Vec<usize>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    let mut matrix = (0..col_num).into_iter().map(|_| vec![]).collect::<Vec<_>>();
    for (i, a) in avector.iter().enumerate() {
        for (j, b) in bvector.iter().enumerate() {
            if i + j < col_num {
                matrix[i + j].push(
                    (BoolExprNode::new(creator.clone(), *a)
                        & BoolExprNode::new(creator.clone(), *b))
                    .index,
                )
            }
        }
    }
    matrix
}

pub(super) const fn calc_log_bits(n: usize) -> usize {
    let nbits = usize::BITS - n.leading_zeros();
    if (1 << (nbits - 1)) == n {
        (nbits - 1) as usize
    } else {
        nbits as usize
    }
}

pub(super) fn iter_shift_left<T, BV>(
    output: &mut [usize],
    input: BV,
    rhs_bit: BoolExprNode<T>,
    i: usize,
) where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    BV: BitVal<Output = BoolExprNode<T>> + Copy,
{
    output.iter_mut().enumerate().for_each(|(x, out)| {
        *out = bool_ite(
            rhs_bit.clone(),
            // if no overflow then get bit(v)
            if x >= (1usize << i) {
                input.bit(x - (1 << i))
            } else {
                BoolExprNode::new(rhs_bit.creator.clone(), 0)
            },
            input.bit(x),
        )
        .index
    });
}

pub(super) fn iter_shift_right<T, BV>(
    output: &mut [usize],
    input: BV,
    rhs_bit: BoolExprNode<T>,
    i: usize,
    sign: bool,
) where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    BV: BitVal<Output = BoolExprNode<T>> + Copy,
{
    output.iter_mut().enumerate().for_each(|(x, out)| {
        *out = bool_ite(
            rhs_bit.clone(),
            // if no overflow then get bit(v)
            if x + (1usize << i) < input.bitnum() {
                input.bit(x + (1 << i))
            } else {
                if sign {
                    input.bit(input.bitnum() - 1)
                } else {
                    BoolExprNode::new(rhs_bit.creator.clone(), 0)
                }
            },
            input.bit(x),
        )
        .index
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolexpr::test_utils::*;

    use crate::IntExprNode;
    use generic_array::typenum::*;
    use generic_array::GenericArray;

    #[test]
    fn test_gen_dadda_matrix() {
        {
            let ec = ExprCreator::new();
            let a = IntExprNode::<isize, U3, false>::variable(ec.clone());
            let b = IntExprNode::<isize, U4, false>::variable(ec.clone());
            let res = gen_dadda_matrix(ec.clone(), &a.indexes, &b.indexes, 6);

            let exp_ec = ExprCreator::new();
            let a = alloc_boolvars(exp_ec.clone(), 3);
            let b = alloc_boolvars(exp_ec.clone(), 4);
            let a0b0 = a[0].clone() & b[0].clone();
            let a0b1 = a[0].clone() & b[1].clone();
            let a0b2 = a[0].clone() & b[2].clone();
            let a0b3 = a[0].clone() & b[3].clone();
            let a1b0 = a[1].clone() & b[0].clone();
            let a1b1 = a[1].clone() & b[1].clone();
            let a1b2 = a[1].clone() & b[2].clone();
            let a1b3 = a[1].clone() & b[3].clone();
            let a2b0 = a[2].clone() & b[0].clone();
            let a2b1 = a[2].clone() & b[1].clone();
            let a2b2 = a[2].clone() & b[2].clone();
            let a2b3 = a[2].clone() & b[3].clone();
            let exp = [
                vec![a0b0],
                vec![a0b1, a1b0],
                vec![a0b2, a1b1, a2b0],
                vec![a0b3, a1b2, a2b1],
                vec![a1b3, a2b2],
                vec![a2b3],
            ]
            .into_iter()
            .map(|c| {
                Vec::from(c)
                    .into_iter()
                    .map(|x| x.index)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

            assert_eq!(exp, res);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let a = IntExprNode::<isize, U3, false>::variable(ec.clone());
            let b = IntExprNode::<isize, U4, false>::variable(ec.clone());
            let res = gen_dadda_matrix(ec.clone(), &a.indexes, &b.indexes, 4);

            let exp_ec = ExprCreator::new();
            let a = alloc_boolvars(exp_ec.clone(), 3);
            let b = alloc_boolvars(exp_ec.clone(), 4);
            let a0b0 = a[0].clone() & b[0].clone();
            let a0b1 = a[0].clone() & b[1].clone();
            let a0b2 = a[0].clone() & b[2].clone();
            let a0b3 = a[0].clone() & b[3].clone();
            let a1b0 = a[1].clone() & b[0].clone();
            let a1b1 = a[1].clone() & b[1].clone();
            let a1b2 = a[1].clone() & b[2].clone();
            let a2b0 = a[2].clone() & b[0].clone();
            let a2b1 = a[2].clone() & b[1].clone();
            let exp = [
                vec![a0b0],
                vec![a0b1, a1b0],
                vec![a0b2, a1b1, a2b0],
                vec![a0b3, a1b2, a2b1],
            ]
            .into_iter()
            .map(|c| {
                Vec::from(c)
                    .into_iter()
                    .map(|x| x.index)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

            assert_eq!(exp, res);
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
    }

    #[test]
    fn test_gen_dadda_mult() {
        {
            let ec = ExprCreator::new();
            let bvs = alloc_boolvars(ec.clone(), 4 * 3);
            let mut matrix = vec![
                vec![bvs[0].index],
                vec![bvs[1].index, bvs[2].index],
                vec![bvs[3].index, bvs[4].index, bvs[5].index],
                vec![bvs[6].index, bvs[7].index, bvs[8].index],
                vec![bvs[9].index, bvs[10].index],
                vec![bvs[11].index],
            ];
            let res = gen_dadda_mult(ec.clone(), &mut matrix);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 4 * 3);
            //       5  8
            //    2  4  7 10
            // 0  1  3  6  9 11
            let (s0, c0) = half_adder(bvs[4].clone(), bvs[5].clone());
            let (s1, c1) = opt_full_adder(bvs[6].clone(), bvs[7].clone(), bvs[8].clone());
            let (s2, c2) = half_adder(bvs[9].clone(), bvs[10].clone());
            let a = IntExprNode::<isize, U6, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    bvs[0].index,
                    bvs[1].index,
                    bvs[3].index,
                    s1.index,
                    s2.index,
                    bvs[11].index,
                ]),
            };
            let b = IntExprNode::<isize, U6, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    0,
                    bvs[2].index,
                    s0.index,
                    c0.index,
                    c1.index,
                    c2.index,
                ]),
            };
            let exp = a + b;

            assert_eq!(exp.indexes.as_slice(), res.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let bvs = alloc_boolvars(ec.clone(), 4 * 3);
            let mut matrix = vec![
                vec![bvs[0].index],
                vec![bvs[1].index, bvs[2].index],
                vec![bvs[3].index, bvs[4].index, bvs[5].index],
                vec![bvs[6].index, bvs[7].index, bvs[8].index],
                vec![bvs[9].index, bvs[10].index],
                vec![bvs[11].index],
                vec![],
            ];
            let res = gen_dadda_mult(ec.clone(), &mut matrix);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 4 * 3);
            //       5  8
            //    2  4  7 10
            // 0  1  3  6  9 11
            let (s0, c0) = half_adder(bvs[4].clone(), bvs[5].clone());
            let (s1, c1) = opt_full_adder(bvs[6].clone(), bvs[7].clone(), bvs[8].clone());
            let (s2, c2) = half_adder(bvs[9].clone(), bvs[10].clone());
            let a = IntExprNode::<isize, U7, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    bvs[0].index,
                    bvs[1].index,
                    bvs[3].index,
                    s1.index,
                    s2.index,
                    bvs[11].index,
                    0,
                ]),
            };
            let b = IntExprNode::<isize, U7, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    0,
                    bvs[2].index,
                    s0.index,
                    c0.index,
                    c1.index,
                    c2.index,
                    0,
                ]),
            };
            let exp = a + b;

            assert_eq!(exp.indexes.as_slice(), res.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let bvs = alloc_boolvars(ec.clone(), 4 * 5);
            let mut matrix = vec![
                vec![bvs[0].index],
                vec![bvs[1].index, bvs[2].index],
                vec![bvs[3].index, bvs[4].index, bvs[5].index],
                vec![bvs[6].index, bvs[7].index, bvs[8].index, bvs[9].index],
                vec![bvs[10].index, bvs[11].index, bvs[12].index, bvs[13].index],
                vec![bvs[14].index, bvs[15].index, bvs[16].index],
                vec![bvs[17].index, bvs[18].index],
                vec![bvs[19].index],
            ];
            let res = gen_dadda_mult(ec.clone(), &mut matrix);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 4 * 5);
            //          9 13
            //       5  8 12 16
            //    2  4  7 11 15 18
            // 0  1  3  6 10 14 17 19
            let (s0, c0) = half_adder(bvs[8].clone(), bvs[9].clone());
            let (s1, c1) = opt_full_adder(bvs[11].clone(), bvs[12].clone(), bvs[13].clone());
            let (s2, c2) = half_adder(bvs[15].clone(), bvs[16].clone());
            //       5 s0 c0 c1 c2
            //    2  4  7 s1 s2 18
            // 0  1  3  6 10 14 17 19
            let (s0_2, c0_2) = half_adder(bvs[4].clone(), bvs[5].clone());
            let (s1_2, c1_2) = opt_full_adder(bvs[6].clone(), bvs[7].clone(), s0);
            let (s2_2, c2_2) = opt_full_adder(bvs[10].clone(), s1, c0);
            let (s3_2, c3_2) = opt_full_adder(bvs[14].clone(), s2, c1);
            let (s4_2, c4_2) = opt_full_adder(bvs[17].clone(), bvs[18].clone(), c2);
            //    2 s0 c0 c1 c2 c3 c4
            // 0  1  3 s1 s2 s3 s4 19
            let a = IntExprNode::<isize, U8, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    bvs[0].index,
                    bvs[1].index,
                    bvs[3].index,
                    s1_2.index,
                    s2_2.index,
                    s3_2.index,
                    s4_2.index,
                    bvs[19].index,
                ]),
            };
            let b = IntExprNode::<isize, U8, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    0,
                    bvs[2].index,
                    s0_2.index,
                    c0_2.index,
                    c1_2.index,
                    c2_2.index,
                    c3_2.index,
                    c4_2.index,
                ]),
            };
            let exp = a + b;

            assert_eq!(exp.indexes.as_slice(), res.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let bvs = alloc_boolvars(ec.clone(), 4 * 5 - 3);
            let mut matrix = vec![
                vec![bvs[0].index],
                vec![bvs[1].index, bvs[2].index],
                vec![bvs[3].index, bvs[4].index, bvs[5].index],
                vec![bvs[6].index, bvs[7].index, bvs[8].index, bvs[9].index],
                vec![bvs[10].index, bvs[11].index, bvs[12].index, bvs[13].index],
                vec![bvs[14].index, bvs[15].index, bvs[16].index],
            ];
            let res = gen_dadda_mult(ec.clone(), &mut matrix);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 4 * 5 - 3);
            //          9 13
            //       5  8 12 16
            //    2  4  7 11 15
            // 0  1  3  6 10 14
            let (s0, c0) = half_adder(bvs[8].clone(), bvs[9].clone());
            let (s1, c1) = opt_full_adder(bvs[11].clone(), bvs[12].clone(), bvs[13].clone());
            let s2 = bvs[15].clone() ^ bvs[16].clone();
            //       5 s0 c0 c1
            //    2  4  7 s1 s2
            // 0  1  3  6 10 14
            let (s0_2, c0_2) = half_adder(bvs[4].clone(), bvs[5].clone());
            let (s1_2, c1_2) = opt_full_adder(bvs[6].clone(), bvs[7].clone(), s0);
            let (s2_2, c2_2) = opt_full_adder(bvs[10].clone(), s1, c0);
            let s3_2 = bvs[14].clone() ^ s2 ^ c1;
            //    2 s0 c0 c1 c2
            // 0  1  3 s1 s2 s3
            let a = IntExprNode::<isize, U6, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    bvs[0].index,
                    bvs[1].index,
                    bvs[3].index,
                    s1_2.index,
                    s2_2.index,
                    s3_2.index,
                ]),
            };
            let b = IntExprNode::<isize, U6, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    0,
                    bvs[2].index,
                    s0_2.index,
                    c0_2.index,
                    c1_2.index,
                    c2_2.index,
                ]),
            };
            let exp = a + b;

            assert_eq!(exp.indexes.as_slice(), res.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
        {
            let ec = ExprCreator::new();
            let bvs = alloc_boolvars(ec.clone(), 5 * 7);
            let mut matrix = vec![
                vec![bvs[0].index],
                vec![bvs[1].index, bvs[2].index],
                vec![bvs[3].index, bvs[4].index, bvs[5].index],
                vec![bvs[6].index, bvs[7].index, bvs[8].index, bvs[9].index],
                vec![
                    bvs[10].index,
                    bvs[11].index,
                    bvs[12].index,
                    bvs[13].index,
                    bvs[14].index,
                ],
                vec![
                    bvs[15].index,
                    bvs[16].index,
                    bvs[17].index,
                    bvs[18].index,
                    bvs[19].index,
                ],
                vec![
                    bvs[20].index,
                    bvs[21].index,
                    bvs[22].index,
                    bvs[23].index,
                    bvs[24].index,
                ],
                vec![bvs[25].index, bvs[26].index, bvs[27].index, bvs[28].index],
                vec![bvs[29].index, bvs[30].index, bvs[31].index],
                vec![bvs[32].index, bvs[33].index],
                vec![bvs[34].index],
            ];
            let res = gen_dadda_mult(ec.clone(), &mut matrix);

            let exp_ec = ExprCreator::new();
            let bvs = alloc_boolvars(exp_ec.clone(), 5 * 7);
            //            14 19 24
            //          9 13 18 23 28
            //       5  8 12 17 22 27 31
            //    2  4  7 11 16 21 26 30 33
            // 0  1  3  6 10 15 20 25 29 32 34
            let (s0, c0) = half_adder(bvs[13].clone(), bvs[14].clone());
            let (s1, c1) = opt_full_adder(bvs[17].clone(), bvs[18].clone(), bvs[19].clone());
            let (s2, c2) = opt_full_adder(bvs[22].clone(), bvs[23].clone(), bvs[24].clone());
            let (s3, c3) = half_adder(bvs[27].clone(), bvs[28].clone());
            //          9 s0 c0 c1 c2 c3
            //       5  8 12 s1 s2 s3 31
            //    2  4  7 11 16 21 26 30 33
            // 0  1  3  6 10 15 20 25 29 32 34
            let (s0_2, c0_2) = half_adder(bvs[8].clone(), bvs[9].clone());
            let (s1_2, c1_2) = opt_full_adder(bvs[11].clone(), bvs[12].clone(), s0);
            let (s2_2, c2_2) = opt_full_adder(bvs[16].clone(), s1, c0);
            let (s3_2, c3_2) = opt_full_adder(bvs[21].clone(), s2, c1);
            let (s4_2, c4_2) = opt_full_adder(bvs[26].clone(), s3, c2);
            let (s5_2, c5_2) = opt_full_adder(bvs[30].clone(), bvs[31].clone(), c3);
            //       5 s0 c0 c1 c2 c3 c4 c5
            //    2  4  7 s1 s2 s3 s4 s5 33
            // 0  1  3  6 10 15 20 25 29 32 34
            let (s0_3, c0_3) = half_adder(bvs[4].clone(), bvs[5].clone());
            let (s1_3, c1_3) = opt_full_adder(bvs[6].clone(), bvs[7].clone(), s0_2);
            let (s2_3, c2_3) = opt_full_adder(bvs[10].clone(), s1_2, c0_2);
            let (s3_3, c3_3) = opt_full_adder(bvs[15].clone(), s2_2, c1_2);
            let (s4_3, c4_3) = opt_full_adder(bvs[20].clone(), s3_2, c2_2);
            let (s5_3, c5_3) = opt_full_adder(bvs[25].clone(), s4_2, c3_2);
            let (s6_3, c6_3) = opt_full_adder(bvs[29].clone(), s5_2, c4_2);
            let (s7_3, c7_3) = opt_full_adder(bvs[32].clone(), bvs[33].clone(), c5_2);
            //    2 s0 c0 c1 c2 c3 c4 c5 c6 c7
            // 0  1  3 s1 s2 s3 s4 s5 s6 s7 34
            let a = IntExprNode::<isize, U11, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    bvs[0].index,
                    bvs[1].index,
                    bvs[3].index,
                    s1_3.index,
                    s2_3.index,
                    s3_3.index,
                    s4_3.index,
                    s5_3.index,
                    s6_3.index,
                    s7_3.index,
                    bvs[34].index,
                ]),
            };
            let b = IntExprNode::<isize, U11, false> {
                creator: exp_ec.clone(),
                indexes: GenericArray::clone_from_slice(&[
                    0,
                    bvs[2].index,
                    s0_3.index,
                    c0_3.index,
                    c1_3.index,
                    c2_3.index,
                    c3_3.index,
                    c4_3.index,
                    c5_3.index,
                    c6_3.index,
                    c7_3.index,
                ]),
            };
            let exp = a + b;

            assert_eq!(exp.indexes.as_slice(), res.as_slice());
            assert_eq!(*exp_ec.borrow(), *ec.borrow());
        }
    }
}
