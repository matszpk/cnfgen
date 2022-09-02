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
        }
    };
}

impl_varlit!(i8);
impl_varlit!(i16);
impl_varlit!(i32);
impl_varlit!(i64);
impl_varlit!(isize);

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

    fn simplify_to<C: SimplifiableClause<T>>(&self, out: &mut C) -> usize {
        out.assign(self);
        out.simplify()
    }

    fn check(&self, var_num: usize) -> bool {
        self.clause_all(|x| {
            x.positive()
                .expect("Literal in clause is too big")
                .to_usize()
                > var_num
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
    fn assign<U, C>(&mut self, src: &C)
    where
        U: VarLit + Neg<Output = U>,
        C: Clause<U> + ?Sized,
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
    fn assign<U, C>(&mut self, src: &C)
    where
        U: VarLit + Neg<Output = U>,
        C: Clause<U> + ?Sized,
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

pub struct CNFWriter<W: Write> {
    writer: W,
    buf: Vec<u8>,
    header: Option<(usize, usize)>,
    clause_count: usize,
}

const DEFAULT_BUF_CAPACITY: usize = 1024;

impl<W: Write> CNFWriter<W> {
    pub fn new(w: W) -> Self {
        CNFWriter {
            writer: w,
            buf: Vec::with_capacity(DEFAULT_BUF_CAPACITY),
            header: None,
            clause_count: 0,
        }
    }

    pub fn write_header(&mut self, var_num: usize, clause_num: usize) -> io::Result<()> {
        self.header.expect("Header has already been written");
        self.buf.clear();
        self.buf.extend_from_slice(b"p cnf ");
        itoap::write_to_vec(&mut self.buf, var_num);
        self.buf.push(b' ');
        itoap::write_to_vec(&mut self.buf, clause_num);
        self.buf.push(b'\n');
        self.writer.write_all(&self.buf)?;
        self.header = Some((var_num, clause_num));
        Ok(())
    }

    pub fn write_clause<T: VarLit, C: Clause<T>>(&mut self, clause: &C) -> io::Result<()>
    where
        T: Neg<Output = T>,
        <T as TryInto<usize>>::Error: Debug,
    {
        if let Some(header) = self.header {
            if self.clause_count == header.1 {
                panic!("Too many clauses");
            }
            if !clause.check(header.0) {
                panic!("Clause with variable number over range");
            }

            self.clause_count += 1;
            Ok(())
        } else {
            panic!("Header has already been written");
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
