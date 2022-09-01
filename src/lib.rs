// lib.rs - main library
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

use std::collections::VecDeque;
use std::ops::{Index, IndexMut, Neg};

pub trait VarLit: Neg + PartialEq + Ord + Default + Copy {
    fn to(self) -> isize;
    fn is_empty(self) -> bool;
    fn empty() -> Self;
    fn positive(self) -> Self;
}

macro_rules! impl_variable {
    ($Ty:ident) => {
        impl VarLit for $Ty {
            #[inline]
            fn to(self) -> isize {
                self as isize
            }
            #[inline]
            fn is_empty(self) -> bool {
                self == 0
            }
            #[inline]
            fn empty() -> Self {
                0
            }
            #[inline]
            fn positive(self) -> Self {
                self.abs()
            }
        }
    };
}

impl_variable!(i8);
impl_variable!(i16);
impl_variable!(i32);
impl_variable!(i64);
impl_variable!(isize);

pub enum Literal<T: VarLit> {
    VarLit(T),
    Value(bool),
}

pub trait Clause<T = <Self as Index<usize>>::Output>: Index<usize> + IndexMut<usize>
where
    T: VarLit + Default,
    <Self as Index<usize>>::Output: Default + PartialEq<T> + Neg + Ord + Copy,
    <Self as Index<usize>>::Output: PartialEq<<<Self as Index<usize>>::Output as Neg>::Output>,
{
    fn clause_len(&self) -> usize;

    fn simplify_to<C: ResizableClause<T>>(&self, out: &mut C) -> usize
    where
        T: From<<Self as Index<usize>>::Output>,
        <C as Index<usize>>::Output: Default + PartialEq<T> + Neg + Ord + Copy,
        <C as Index<usize>>::Output: PartialEq<<<C as Index<usize>>::Output as Neg>::Output>,
    {
        out.assign(self);
        out.simplify()
    }

    fn is_empty(&self) -> bool {
        if self.clause_len() == 0 {
            true
        } else {
            for i in 0..self.clause_len() {
                if self[i] != T::empty() {
                    return false;
                }
            }
            true
        }
    }
}

impl<T> Clause<T> for [T]
where
    T: VarLit + Default + Neg + Copy + PartialEq<<T as Neg>::Output>,
{
    fn clause_len(&self) -> usize {
        self.len()
    }
}

impl<T> Clause<T> for Vec<T>
where
    T: VarLit + Default + Neg + Copy + PartialEq<<T as Neg>::Output>,
{
    fn clause_len(&self) -> usize {
        self.len()
    }
}

impl<T> Clause<T> for VecDeque<T>
where
    T: VarLit + Default + Neg + Copy + PartialEq<<T as Neg>::Output>,
{
    fn clause_len(&self) -> usize {
        self.len()
    }
}

impl<T, const N: usize> Clause<T> for [T; N]
where
    T: VarLit + Default + Neg + Copy + PartialEq<<T as Neg>::Output>,
{
    fn clause_len(&self) -> usize {
        N
    }
}

pub trait ResizableClause<T = <Self as Index<usize>>::Output>: Clause<T>
where
    T: VarLit + Default,
    <Self as Index<usize>>::Output: Default + PartialEq<T> + Neg + Ord + Copy,
    <Self as Index<usize>>::Output: PartialEq<<<Self as Index<usize>>::Output as Neg>::Output>,
{
    fn shrink(&mut self, i: usize);
    fn sort_abs(&mut self);
    fn assign<C: Clause<T> + ?Sized>(&mut self, src: &C)
    where
        T: From<<C as Index<usize>>::Output>,
        <C as Index<usize>>::Output: Default + PartialEq<T> + Neg + Ord + Copy,
        <C as Index<usize>>::Output: PartialEq<<<C as Index<usize>>::Output as Neg>::Output>;

    fn simplify(&mut self) -> usize {
        let mut j = 0;
        // sort clause
        self.sort_abs();
        // and remove zeroes and duplicates
        for i in 0..self.clause_len() {
            if (i <= 0 || self[i - 1] != self[i]) && self[i] != T::empty() {
                // if no zero and if no this same literal
                self[j] = self[i];
                j += 1;
            }
        }
        // check tautology - v or ~v
        for i in 0..j {
            if i >= j - 1 || self[i] != -self[i + 1] {
                // if tautology
                self.shrink(0);
                return 0;
            }
        }
        self.shrink(j);
        self.clause_len()
    }
}

impl<T> ResizableClause<T> for Vec<T>
where
    T: VarLit + Default + Neg + Copy + PartialEq<<T as Neg>::Output>,
{
    fn shrink(&mut self, l: usize) {
        self.resize(l, T::empty());
    }
    fn sort_abs(&mut self) {
        self.sort_by_key(|x| x.positive());
    }
    fn assign<C: Clause<T> + ?Sized>(&mut self, src: &C)
    where
        T: From<<C as Index<usize>>::Output>,
        <C as Index<usize>>::Output: Default + PartialEq<T> + Neg + Ord + Copy,
        <C as Index<usize>>::Output: PartialEq<<<C as Index<usize>>::Output as Neg>::Output>,
    {
        self.clear();
        self.resize(src.clause_len(), T::empty());
        for i in 0..src.clause_len() {
            self[i] = T::from(src[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
