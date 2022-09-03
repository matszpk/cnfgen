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

use std::collections::*;
use std::fmt::Debug;
use std::io::{self, Write};
use std::iter::Extend;
use std::ops::{Index, IndexMut, Neg};

pub trait VarLit: Neg + PartialEq + Ord + Copy + TryInto<isize> + TryInto<usize> {
    #[inline]
    fn to(self) -> isize
    where
        <Self as TryInto<isize>>::Error: Debug,
    {
        self.try_into().expect("VarLit is too big")
    }
    #[inline]
    fn to_usize(self) -> usize
    where
        <Self as TryInto<usize>>::Error: Debug,
    {
        self.try_into().expect("VarLit is too big")
    }
    fn is_empty(self) -> bool;
    fn empty() -> Self;
    fn positive(self) -> Option<Self>;
    fn write_to_vec(self, vec: &mut Vec<u8>);
}

macro_rules! impl_varlit {
    ($Ty:ident) => {
        impl VarLit for $Ty {
            #[inline]
            fn is_empty(self) -> bool {
                self == 0
            }
            #[inline]
            fn empty() -> Self {
                0
            }
            #[inline]
            fn positive(self) -> Option<Self> {
                self.checked_abs()
            }

            #[inline]
            fn write_to_vec(self, vec: &mut Vec<u8>) {
                itoap::write_to_vec(vec, self);
            }
        }
    };
}

impl_varlit!(i8);
impl_varlit!(i16);
impl_varlit!(i32);
impl_varlit!(i64);
impl_varlit!(isize);

#[derive(Clone, Copy)]
pub enum Literal<T: VarLit> {
    VarLit(T),
    Value(bool),
}

impl<T: VarLit> From<bool> for Literal<T> {
    fn from(t: bool) -> Self {
        Literal::Value(t)
    }
}

impl<T: VarLit> From<T> for Literal<T> {
    fn from(t: T) -> Self {
        Literal::VarLit(t)
    }
}

pub trait Clause<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize;
    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool;
    fn clause_for_each<F: FnMut(&T)>(&self, f: F);
    fn is_falsed(&self) -> bool;

    fn check(&self, var_num: usize) -> bool {
        self.clause_all(|x| {
            *x != T::empty()
                && if let Some(p) = x.positive() {
                    p.to_usize() <= var_num
                } else {
                    false
                }
        })
    }
}

macro_rules! impl_clause {
    ($Ty:ty) => {
        impl<T> Clause<T> for $Ty
        where
            T: VarLit + Neg<Output = T>,
            <T as TryInto<usize>>::Error: Debug,
        {
            fn clause_len(&self) -> usize {
                self.len()
            }

            fn is_falsed(&self) -> bool {
                false
            }

            fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
                self.iter().all(f)
            }

            fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
                self.iter().for_each(f);
            }
        }
    };
}

impl_clause!([T]);
impl_clause!(Vec<T>);
impl_clause!(VecDeque<T>);
impl_clause!(BTreeSet<T>);
impl_clause!(BinaryHeap<T>);
impl_clause!(HashSet<T>);
impl_clause!(LinkedList<T>);

impl<T, const N: usize> Clause<T> for [T; N]
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize {
        N
    }

    fn is_falsed(&self) -> bool {
        false
    }

    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
        self.iter().all(f)
    }

    fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
        self.iter().for_each(f);
    }
}

pub trait SimplifiableClause<T>:
    Clause<T> + Index<usize, Output = T> + IndexMut<usize, Output = T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn shrink(&mut self, l: usize);
    fn sort_abs(&mut self);
    fn assign<U, C>(&mut self, src: C)
    where
        U: VarLit + Neg<Output = U>,
        C: Clause<U>,
        <U as TryInto<usize>>::Error: Debug,
        T: TryFrom<U>,
        <T as TryFrom<U>>::Error: Debug;

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

impl<T> SimplifiableClause<T> for Vec<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn shrink(&mut self, l: usize) {
        self.resize(l, T::empty());
    }
    fn sort_abs(&mut self) {
        self.sort_by_key(|x| x.positive());
    }
    fn assign<U, C>(&mut self, src: C)
    where
        U: VarLit + Neg<Output = U>,
        C: Clause<U>,
        <U as TryInto<usize>>::Error: Debug,
        T: TryFrom<U>,
        <T as TryFrom<U>>::Error: Debug,
    {
        self.resize(src.clause_len(), T::empty());
        let mut i = 0;
        src.clause_for_each(|x| {
            self[i] = T::try_from(*x).unwrap();
            i += 1;
        });
    }
}

pub struct InputClause<T> {
    clause: Vec<T>,
    // if clause is tautology
    tautology: bool,
    falsed: bool,
}

impl<T: VarLit> InputClause<T> {
    pub fn new() -> Self {
        Self {
            clause: vec![],
            tautology: false,
            falsed: true,
        }
    }

    pub fn clause(&self) -> &Vec<T> {
        &self.clause
    }

    pub fn is_empty(&self) -> bool {
        self.clause.is_empty()
    }

    pub fn is_tautology(&self) -> bool {
        self.tautology
    }

    pub fn push(&mut self, lit: Literal<T>) {
        if !self.tautology {
            match lit {
                Literal::Value(t) => {
                    if t {
                        self.clause.clear();
                        self.tautology = true;
                        self.falsed = false;
                    }
                }
                Literal::VarLit(v) => {
                    self.clause.push(v);
                    self.falsed = false;
                }
            }
        }
    }
}

impl<'a, T: Copy + 'a> Extend<&'a T> for InputClause<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        if !self.tautology {
            <Vec<T> as Extend<&'a T>>::extend(&mut self.clause, iter);
            if !self.clause.is_empty() {
                self.falsed = false;
            }
        }
    }
}

impl<T> FromIterator<T> for InputClause<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut ret = Self {
            clause: Vec::from_iter(iter),
            tautology: false,
            falsed: true,
        };
        ret.falsed = ret.clause.is_empty();
        ret
    }
}

impl<T> Extend<T> for InputClause<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        if !self.tautology {
            self.clause.extend(iter);
            if !self.clause.is_empty() {
                self.falsed = false;
            }
        }
    }
}

impl<T> Extend<Literal<T>> for InputClause<T>
where
    T: VarLit,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = Literal<T>>,
    {
        if !self.tautology {
            iter.into_iter().for_each(|x| self.push(x));
        }
    }
}

impl<'a, T> FromIterator<&'a Literal<T>> for InputClause<T>
where
    T: VarLit,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = &'a Literal<T>>,
    {
        let mut ret = InputClause::new();
        iter.into_iter().for_each(|x| ret.push(*x));
        ret
    }
}

impl<'a, T> Extend<&'a Literal<T>> for InputClause<T>
where
    T: VarLit,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a Literal<T>>,
    {
        if !self.tautology {
            iter.into_iter().for_each(|x| self.push(*x));
        }
    }
}

impl<T> Clause<T> for InputClause<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize {
        self.clause.clause_len()
    }

    fn is_falsed(&self) -> bool {
        self.falsed
    }

    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
        self.clause.clause_all(f)
    }

    fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
        self.clause.clause_for_each(f);
    }
}

pub trait QuantSet<T>
where
    T: VarLit,
    <T as TryInto<usize>>::Error: Debug,
{
    fn quant_len(&self) -> usize;
    fn quant_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool;
    fn quant_for_each<F: FnMut(&T)>(&self, f: F);

    fn check(&self, var_num: usize) -> bool {
        self.quant_all(|x| *x > T::empty() && x.to_usize() <= var_num)
    }
}

macro_rules! impl_quant_set {
    ($Ty:ty) => {
        impl<T> QuantSet<T> for $Ty
        where
            T: VarLit,
            <T as TryInto<usize>>::Error: Debug,
        {
            fn quant_len(&self) -> usize {
                self.len()
            }

            fn quant_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
                self.iter().all(f)
            }

            fn quant_for_each<F: FnMut(&T)>(&self, f: F) {
                self.iter().for_each(f);
            }
        }
    };
}

impl_quant_set!([T]);
impl_quant_set!(Vec<T>);
impl_quant_set!(VecDeque<T>);
impl_quant_set!(BTreeSet<T>);
impl_quant_set!(BinaryHeap<T>);
impl_quant_set!(HashSet<T>);
impl_quant_set!(LinkedList<T>);

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    Exists,
    ForAll,
}

#[derive(Clone, Copy, Default, Debug)]
pub struct CNFHeader {
    pub var_num: usize,
    pub clause_num: usize,
}

pub struct CNFWriter<W: Write> {
    writer: W,
    buf: Vec<u8>,
    buf_clause: Vec<isize>,
    header: Option<CNFHeader>,
    need_cnf_false: bool,
    clause_count: usize,
    clause_real_count: usize,
}

const DEFAULT_BUF_CAPACITY: usize = 1024;
const DEFAULT_CLAUSE_CAPACITY: usize = 64;

impl<W: Write> CNFWriter<W> {
    pub fn new(w: W) -> Self {
        CNFWriter {
            writer: w,
            buf: Vec::with_capacity(DEFAULT_BUF_CAPACITY),
            header: None,
            buf_clause: Vec::<isize>::with_capacity(DEFAULT_CLAUSE_CAPACITY),
            clause_count: 0,
            clause_real_count: 0,
            need_cnf_false: false,
        }
    }

    pub fn write_header(&mut self, var_num: usize, clause_num: usize) -> io::Result<()> {
        self.header
            .as_ref()
            .expect("Header has already been written");
        self.buf.clear();
        self.buf.extend_from_slice(b"p cnf ");
        itoap::write_to_vec(&mut self.buf, var_num);
        self.buf.push(b' ');
        itoap::write_to_vec(&mut self.buf, clause_num);
        self.buf.push(b'\n');
        self.writer.write_all(&self.buf)?;
        self.header = Some(CNFHeader {
            var_num,
            clause_num,
        });
        Ok(())
    }

    pub fn write_quant<T: VarLit, Q: QuantSet<T>>(
        &mut self,
        q: Quantifier,
        qs: &Q,
    ) -> io::Result<()>
    where
        <T as TryInto<usize>>::Error: Debug,
    {
        if let Some(ref header) = self.header {
            if !qs.check(header.var_num) {
                panic!("Quantifier set with variable number over range");
            }
            self.buf.clear();
            self.buf.extend(if q == Quantifier::Exists {
                b"e "
            } else {
                b"a "
            });
            qs.quant_for_each(|x| {
                x.write_to_vec(&mut self.buf);
                self.buf.push(b' ');
            });
            self.buf.extend(b"0\n");
            self.writer.write_all(&self.buf)
        } else {
            panic!("Header has not been written");
        }
    }

    pub fn write_varlits<T, I>(&mut self, iter: I) -> io::Result<()>
    where
        T: VarLit + Neg<Output = T>,
        I: IntoIterator<Item = T>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug,
    {
        self.write_clause(InputClause::<T>::from_iter(iter))
    }

    pub fn write_literals<'a, T, I>(&mut self, iter: I) -> io::Result<()>
    where
        T: VarLit + Neg<Output = T> + 'a,
        I: IntoIterator<Item = &'a Literal<T>>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug,
    {
        self.write_clause(InputClause::<T>::from_iter(iter))
    }

    fn write_current_clause(&mut self) -> io::Result<()> {
        self.buf.clear();
        self.buf_clause.iter().for_each(|x| {
            x.write_to_vec(&mut self.buf);
            self.buf.push(b' ');
        });
        self.buf.extend(b"0\n");
        self.writer.write_all(&self.buf)
    }

    fn write_neg_prev_clause(&mut self) -> io::Result<()> {
        self.buf_clause.iter_mut().for_each(|x| *x = -*x);
        self.write_current_clause()
    }

    pub fn write_clause<T: VarLit, C: Clause<T>>(&mut self, clause: C) -> io::Result<()>
    where
        T: Neg<Output = T>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug,
    {
        if let Some(ref header) = self.header {
            if self.clause_count == header.clause_num {
                panic!("Too many clauses");
            }
            if !clause.is_falsed() {
                if !clause.check(header.var_num) {
                    panic!("Clause with variable number over range");
                }
                // simplify clause
                self.buf_clause.assign(clause);
                self.buf_clause.simplify();
                if self.buf_clause.clause_len() != 0 {
                    // if not empty then write
                    self.write_current_clause()?;
                    self.clause_real_count += 1;
                    if self.need_cnf_false {
                        self.write_neg_prev_clause()?;
                    }
                } else {
                    // if empty true clause then
                    if self.need_cnf_false {
                        // two falsified clauses
                        self.writer.write_all(b"1 0\n-1 0\n")?;
                    } else {
                        self.writer.write_all(b"0\n")?;
                    }
                }
                self.need_cnf_false = false;
            } else {
                // write falsification
                if self.need_cnf_false {
                    // write two clauses if next is falsed
                    self.writer.write_all(b"1 0\n-1 0\n")?;
                    self.need_cnf_false = false;
                } else if self.clause_real_count != 0 {
                    self.write_neg_prev_clause()?;
                } else {
                    // if first clause, then write while writing this first
                    self.need_cnf_false = true;
                }
            }
            self.clause_count += 1;
            Ok(())
        } else {
            panic!("Header has not been written");
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
