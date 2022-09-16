// writer.rs - writer module
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
//! The module to write CNF from clauses.

use std::collections::*;
use std::fmt::Debug;
use std::io::{self, Write};
use std::iter::Extend;
use std::ops::{Index, IndexMut, Neg, Not};

#[derive(thiserror::Error, Debug)]
/// An error type.
pub enum Error {
    /// It caused if header has already been written.
    #[error("Header has already been written")]
    HeaderAlreadyWritten,
    /// It caused if header has not been written.
    #[error("Header has not been written")]
    HeaderNotWritten,
    /// It caused if attempt to write quantifier after clauses.
    #[error("Quantifier after clauses")]
    QuantifierAfterClauses,
    /// It caused if attempt to write this same type of quantifier as previously.
    #[error("Quantifier's duplicate")]
    QuantifierDuplicate,
    /// It caused after write all clauses.
    #[error("Too many clauses to write")]
    TooManyClauses,
    /// It caused if clause have variable literal out of range.
    #[error("Variable literal is out of range")]
    VarLitOutOfRange,
    /// It caused if I/O error encountered.
    #[error("IO error: {0}")]
    IOError(#[from] io::Error),
}

/// A variable literal. It holds variable number if it is not negated,
/// or negated variable number if it is negated. Zero value is not allowed.
pub trait VarLit: Neg + PartialEq + Eq + Ord + Copy + TryInto<isize> + TryInto<usize> {
    /// Converts variable literal to isize.
    #[inline]
    fn to(self) -> isize
    where
        <Self as TryInto<isize>>::Error: Debug,
    {
        self.try_into().expect("VarLit is too big")
    }
    /// Converts variable literal to usize.
    #[inline]
    fn to_usize(self) -> usize
    where
        <Self as TryInto<usize>>::Error: Debug,
    {
        self.try_into().expect("VarLit is too big")
    }
    /// Returns true if literal is empty (zero value - not allowed).
    fn is_empty(self) -> bool;
    /// Returns empty literal - zero.
    fn empty() -> Self;
    /// Returns first variable - 1.
    fn first_value() -> Self;
    /// Returns some positive value (absolute value) if no overflow encountered.
    fn positive(self) -> Option<Self>;
    /// Write self value to vector of bytes.
    fn write_to_vec(self, vec: &mut Vec<u8>);
}

macro_rules! impl_varlit {
    ($Ty:ident) => {
        /// Implementation for an integer type.
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
            fn first_value() -> Self {
                1
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

/// A literal. It holds variable literal or value literal (false or true). It can be used
/// to construct clause from either variables or constants. T type must be a VarLit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Literal<T: VarLit> {
    /// It holds variable literal.
    VarLit(T),
    /// It holds boolean value.
    Value(bool),
}

impl<T: VarLit> Literal<T> {
    /// Returns true if self is variable literal.
    pub fn is_varlit(self) -> bool {
        matches!(self, Literal::VarLit(_))
    }

    /// Returns true if self is value.
    pub fn is_value(self) -> bool {
        matches!(self, Literal::Value(_))
    }
}

impl<T: VarLit + Neg<Output = T>> Not for Literal<T> {
    type Output = Literal<T>;

    fn not(self) -> Self::Output {
        match self {
            Literal::Value(t) => Literal::Value(!t),
            Literal::VarLit(t) => Literal::VarLit(-t),
        }
    }
}

/// Converts boolean value to Literal.
impl<T: VarLit> From<bool> for Literal<T> {
    fn from(t: bool) -> Self {
        Literal::Value(t)
    }
}

/// Converts variable literal to Literal.
impl<T: VarLit> From<T> for Literal<T> {
    fn from(t: T) -> Self {
        Literal::VarLit(t)
    }
}

/// Basic clause trait. It contains variable literals.
/// This clause is a disjuction of literals.
/// An empty clause is always false - formulaue contains that clause going
/// to be unsatisfied.
pub trait Clause<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    /// Mainly to internal use. Returns length of clause - number of literals.
    fn clause_len(&self) -> usize;
    /// Mainly to internal use. Returns true only if this function returns true for
    /// all items.
    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool;
    /// Mainly to internal use. It performs function for each item.
    fn clause_for_each<F: FnMut(&T)>(&self, f: F);

    /// Checks clause whether it have only allowed variable literals and variables
    /// used in this clause doesn't have number greater than var_num.
    fn check_clause(&self, var_num: usize) -> bool {
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
        /// An implementation for this type.
        impl<T> Clause<T> for $Ty
        where
            T: VarLit + Neg<Output = T>,
            <T as TryInto<usize>>::Error: Debug,
        {
            fn clause_len(&self) -> usize {
                self.len()
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

/// An implementation for a reference of slice.
impl<'a, T> Clause<T> for &'a [T]
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize {
        self.len()
    }

    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
        self.iter().all(f)
    }

    fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
        self.iter().for_each(f);
    }
}

impl_clause!([T]);
impl_clause!(Vec<T>);
impl_clause!(VecDeque<T>);
impl_clause!(BTreeSet<T>);
impl_clause!(BinaryHeap<T>);
impl_clause!(HashSet<T>);
impl_clause!(LinkedList<T>);

/// An implementation for an array.
impl<T, const N: usize> Clause<T> for [T; N]
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize {
        N
    }

    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
        self.iter().all(f)
    }

    fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
        self.iter().for_each(f);
    }
}

/// Trait of clause that can be simplified. This clause type is used during writing clause
/// by CNF writer to prepare clause to write.
pub trait SimplifiableClause<T>:
    Clause<T> + Index<usize, Output = T> + IndexMut<usize, Output = T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    /// Shrinks clause to specified length.
    fn shrink(&mut self, l: usize);
    /// Sorts literal by variable number (absolute value).
    fn sort_abs(&mut self);
    /// Assigns source clause to self.
    fn assign<U, C>(&mut self, src: C)
    where
        U: VarLit + Neg<Output = U>,
        C: Clause<U>,
        <U as TryInto<usize>>::Error: Debug,
        T: TryFrom<U>,
        <T as TryFrom<U>>::Error: Debug;

    /// Simplifies clause and returns its final length.
    fn simplify(&mut self) -> usize {
        let mut j = 0;
        // sort clause
        self.sort_abs();
        // and remove zeroes and duplicates
        for i in 0..self.clause_len() {
            if i <= 0 || self[i - 1] != self[i] {
                // if no this same literal
                self[j] = self[i];
                j += 1;
            }
        }
        self.shrink(j);
        // check tautology - v or ~v
        for i in 0..j {
            if i < j - 1 && self[i] == -self[i + 1] {
                // if tautology
                self.shrink(2);
                self[0] = T::first_value();
                self[1] = -T::first_value();
                return self.clause_len();
            }
        }
        self.clause_len()
    }
}

/// An implementation for vector.
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

/// A input clause that can be used to construct clauses. It can be easily constructed
/// by using `push` or `extend` methods. The push method accepts Literal.
pub struct InputClause<T> {
    clause: Vec<T>,
    tautology: bool,
}

impl<T: VarLit + Neg<Output = T>> InputClause<T> {
    /// Creates new an input clause.
    pub fn new() -> Self {
        Self {
            clause: vec![],
            tautology: false,
        }
    }

    /// Returns inner clause (container).
    pub fn clause(&self) -> &Vec<T> {
        &self.clause
    }

    /// Returns true if clause is empty.
    pub fn is_empty(&self) -> bool {
        self.clause.is_empty()
    }

    /// Returns true if clause is tautology after pushing true.
    pub fn is_tautology(&self) -> bool {
        self.tautology
    }

    /// Pushes a literal to clause. If literal is variable literal then it pushed to clause.
    /// If literal is false then nothing happens. If literal is true then clause
    /// going to be a tautology and any further literals going to be ignored.
    pub fn push(&mut self, lit: impl Into<Literal<T>>) {
        if !self.tautology {
            match lit.into() {
                Literal::Value(t) => {
                    if t {
                        self.clause.clear();
                        self.clause.extend([T::first_value(), -T::first_value()]);
                        self.tautology = true;
                    }
                }
                Literal::VarLit(v) => self.clause.push(v),
            }
        }
    }
}

/// An implementation Extend for InputClause for reference of VarLit items.
impl<'a, T: Copy + 'a> Extend<&'a T> for InputClause<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        if !self.tautology {
            <Vec<T> as Extend<&'a T>>::extend(&mut self.clause, iter);
        }
    }
}

/// An implementation FromIterator for InputClause for VarLit items.
impl<T> FromIterator<T> for InputClause<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self {
            clause: Vec::from_iter(iter),
            tautology: false,
        }
    }
}

/// An implementation Extend for InputClause for VarLit items.
impl<T> Extend<T> for InputClause<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        if !self.tautology {
            self.clause.extend(iter);
        }
    }
}

/// An implementation Extend for InputClause for Literal items.
impl<T> Extend<Literal<T>> for InputClause<T>
where
    T: VarLit + Neg<Output = T>,
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

/// An implementation FromIterator for InputClause for Literal items.
impl<T> FromIterator<Literal<T>> for InputClause<T>
where
    T: VarLit + Neg<Output = T>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Literal<T>>,
    {
        let mut ret = InputClause::new();
        iter.into_iter().for_each(|x| ret.push(x));
        ret
    }
}

/// An implementation FromIterator for InputClause for reference of Literal items.
impl<'a, T> Extend<&'a Literal<T>> for InputClause<T>
where
    T: VarLit + Neg<Output = T>,
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

/// An implementation Clause for InputCaluse.
impl<T> Clause<T> for InputClause<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize {
        self.clause.clause_len()
    }

    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
        self.clause.clause_all(f)
    }

    fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
        self.clause.clause_for_each(f);
    }
}

/// Quantified literal's set. It contains variables that will be used with quantifier.
pub trait QuantSet<T>
where
    T: VarLit,
    <T as TryInto<usize>>::Error: Debug,
{
    /// Mainly interal usage. Returns length of set.
    fn quant_len(&self) -> usize;
    /// Mainly to internal use. Returns true only if this function returns true for
    /// all items.
    fn quant_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool;
    /// Mainly to internal use. It performs function for each item.
    fn quant_for_each<F: FnMut(&T)>(&self, f: F);

    /// Checks set. Returns true if set contains only positive numbers of variables and
    /// only that is not greater than var_num.
    fn check_quantset(&self, var_num: usize) -> bool {
        self.quant_all(|x| *x > T::empty() && x.to_usize() <= var_num)
    }
}

macro_rules! impl_quant_set {
    ($Ty:ty) => {
        /// An implementation for this type.
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

/// An implementation for a reference of slice.
impl<'a, T> QuantSet<T> for &'a [T]
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

impl_quant_set!([T]);
impl_quant_set!(Vec<T>);
impl_quant_set!(VecDeque<T>);
impl_quant_set!(BTreeSet<T>);
impl_quant_set!(BinaryHeap<T>);
impl_quant_set!(HashSet<T>);
impl_quant_set!(LinkedList<T>);

/// An implementation for an array.
impl<T, const N: usize> QuantSet<T> for [T; N]
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

/// Quantifier type. It can be a existential and universal.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Quantifier {
    /// An existential quantifier type - exists.
    Exists,
    /// An universal quantifier type - for all.
    ForAll,
}

/// CNF file header. It contains a number of variables and a number of clauses.
#[derive(Clone, Copy, Default, Debug)]
pub struct CNFHeader {
    /// Number of variables in formulae. It can be zero.
    pub var_num: usize,
    /// Number of clauses in formulae. It can be zero.
    pub clause_num: usize,
}

/// A CNF formulae writer.
pub struct CNFWriter<W: Write> {
    writer: W,
    buf: Vec<u8>,
    buf_clause: Vec<isize>,
    header: Option<CNFHeader>,
    clause_count: usize,
    last_quant: Option<Quantifier>,
}

const DEFAULT_BUF_CAPACITY: usize = 1024;
const DEFAULT_CLAUSE_CAPACITY: usize = 64;

/// An implementation for Write.
impl<W: Write> CNFWriter<W> {
    /// Creates new CNF writer. Parameter is writer.
    pub fn new(w: W) -> Self {
        CNFWriter {
            writer: w,
            buf: Vec::with_capacity(DEFAULT_BUF_CAPACITY),
            header: None,
            buf_clause: Vec::<isize>::with_capacity(DEFAULT_CLAUSE_CAPACITY),
            clause_count: 0,
            last_quant: None,
        }
    }

    /// Returns an inner writer.
    pub fn inner(&self) -> &W {
        &self.writer
    }

    /// Writes a CNF header. It returns Ok if no error encountered.
    pub fn write_header(&mut self, var_num: usize, clause_num: usize) -> Result<(), Error> {
        if self.header.is_none() {
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
        } else {
            Err(Error::HeaderAlreadyWritten)
        }
    }

    /// Writes quantifier. It returns Ok if no error encountered.
    /// It must be called after header write and before any clause write.
    pub fn write_quant<T: VarLit, Q: QuantSet<T>>(
        &mut self,
        q: Quantifier,
        qs: Q,
    ) -> Result<(), Error>
    where
        <T as TryInto<usize>>::Error: Debug,
    {
        if let Some(ref header) = self.header {
            if self.clause_count != 0 {
                return Err(Error::QuantifierAfterClauses);
            }
            if !qs.check_quantset(header.var_num) {
                return Err(Error::VarLitOutOfRange);
            }
            if let Some(lastq) = self.last_quant {
                if lastq == q {
                    return Err(Error::QuantifierDuplicate);
                }
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
            self.writer.write_all(&self.buf)?;

            self.last_quant = Some(q);
            Ok(())
        } else {
            Err(Error::HeaderNotWritten)
        }
    }

    /// Writes Literals as clause. It returns Ok if no error encountered.
    /// It must be called after header write.
    /// It construct from literals clause and try to write this clause.
    pub fn write_literals<T, I>(&mut self, iter: I) -> Result<(), Error>
    where
        T: VarLit + Neg<Output = T>,
        I: IntoIterator<Item = Literal<T>>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug,
    {
        self.write_clause(InputClause::<T>::from_iter(iter))
    }

    /// Writes clause. It must be called after header write.
    pub fn write_clause<T: VarLit, C: Clause<T>>(&mut self, clause: C) -> Result<(), Error>
    where
        T: Neg<Output = T>,
        isize: TryFrom<T>,
        <isize as TryFrom<T>>::Error: Debug,
        <T as TryInto<usize>>::Error: Debug,
    {
        if let Some(ref header) = self.header {
            if self.clause_count == header.clause_num {
                return Err(Error::TooManyClauses);
            }
            if !clause.check_clause(header.var_num) {
                return Err(Error::VarLitOutOfRange);
            }
            // simplify clause
            self.buf_clause.assign(clause);
            self.buf_clause.simplify();
            self.buf.clear();
            self.buf_clause.iter().for_each(|x| {
                x.write_to_vec(&mut self.buf);
                self.buf.push(b' ');
            });
            self.buf.extend(b"0\n");
            self.writer.write_all(&mut self.buf)?;
            self.clause_count += 1;
            Ok(())
        } else {
            Err(Error::HeaderNotWritten)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_varlit() {
        for (exp, x) in [
            (Some(0), 0),
            (Some(1), -1),
            (Some(43), 43),
            (Some(113), -113),
            (Some(i16::MAX), i16::MAX),
            (None, i16::MIN),
        ] {
            assert_eq!(exp, x.positive());
        }
        for (exp, x) in [
            (Some(0), 0),
            (Some(1), -1),
            (Some(454), 454),
            (Some(113), -113),
            (Some(isize::MAX), isize::MAX),
            (None, isize::MIN),
        ] {
            assert_eq!(exp, x.positive());
        }
        assert_eq!(33, 33.to());
        assert_eq!(33, 33.to_usize());
        assert_eq!(0, i32::empty());
        assert!(!32.is_empty());
        assert!(0.is_empty());
    }

    #[test]
    fn test_varlit_write_to_vec() {
        for (exp, x) in [("xx23", 23i8), ("xx-45", -45i8), ("xx0", 0i8)] {
            let mut bytes = Vec::from(b"xx".as_slice());
            x.write_to_vec(&mut bytes);
            assert_eq!(exp.as_bytes(), &bytes);
        }
        for (exp, x) in [
            ("xx123323", 123323i32),
            ("xx-113145", -113145i32),
            ("xx0", 0i32),
        ] {
            let mut bytes = Vec::from(b"xx".as_slice());
            x.write_to_vec(&mut bytes);
            assert_eq!(exp.as_bytes(), &bytes);
        }
        for (exp, x) in [
            ("xx123323", 123323isize),
            ("xx-113145", -113145isize),
            ("xx0", 0isize),
        ] {
            let mut bytes = Vec::from(b"xx".as_slice());
            x.write_to_vec(&mut bytes);
            assert_eq!(exp.as_bytes(), &bytes);
        }
    }

    fn lit_func<T: VarLit>(t: impl Into<Literal<T>>) -> Literal<T> {
        t.into()
    }

    #[test]
    fn test_literal() {
        assert_eq!(Literal::<isize>::Value(false), lit_func(false));
        assert_eq!(Literal::<isize>::Value(true), lit_func(true));
        assert_eq!(Literal::<isize>::VarLit(2343), lit_func(2343));
        assert_eq!(Literal::<isize>::VarLit(-59521), lit_func(-59521));
        assert!(!Literal::<isize>::Value(false).is_varlit());
        assert!(Literal::<isize>::Value(false).is_value());
        assert!(Literal::<isize>::VarLit(3).is_varlit());
        assert!(!Literal::<isize>::VarLit(4).is_value());
    }

    fn clause_func<T, C>(t: C) -> C
    where
        T: VarLit + Neg<Output = T>,
        C: Clause<T>,
        <T as TryInto<usize>>::Error: Debug,
    {
        t
    }

    #[test]
    fn test_clause() {
        let clause = [1, 2, 4];
        clause_func(clause);
        clause_func([12isize]);
        clause_func(Vec::from(clause));
        clause_func(BTreeSet::from(clause));
        clause_func(clause.as_slice());

        let mut v = vec![];
        clause.clause_for_each(|x| v.push(*x));
        assert_eq!(Vec::from([1, 2, 4]), v);
        assert!(clause.clause_all(|x| *x <= 4));
        assert!(!clause.clause_all(|x| *x > 2));
        assert_eq!(clause.len(), clause.clause_len());
    }

    #[test]
    fn test_clause_check_clause() {
        for (vn, exp, c) in [
            (5, true, [1, 4, -3].as_slice()),
            (5, false, [1, 0, 4, -3].as_slice()),
            (4, true, [1, -4, 2].as_slice()),
            (4, false, [1, -5, 2].as_slice()),
            (4, false, [3, -4, 2, 5].as_slice()),
            ((1 << 15), false, [3, -4, 2, i16::MIN].as_slice()),
            ((1 << 7), true, [3, -4, 2, i8::MIN as i16].as_slice()),
        ] {
            assert_eq!(exp, c.check_clause(vn));
        }
    }

    #[test]
    fn test_simplifiable_clause() {
        let mut sclause = Vec::from([2, 5, 4]);
        sclause.assign([1, 6, 2]);
        assert_eq!([1, 6, 2].as_slice(), sclause.as_slice());
        sclause.assign([3, 1, 5]);
        assert_eq!([3, 1, 5].as_slice(), sclause.as_slice());
        sclause.assign([3, 1, -5, 7, -4]);
        sclause.sort_abs();
        assert_eq!([1, 3, -4, -5, 7].as_slice(), sclause.as_slice());
        sclause.assign([-1, 2, 3]);
        assert_eq!([-1, 2, 3].as_slice(), sclause.as_slice());
    }

    #[test]
    fn test_simplifiable_clause_simplify() {
        for (clause, exp, expres) in [
            ([1, 1, -4].as_slice(), [1, -4].as_slice(), 2),
            ([-3, -3, 1, 5, 5].as_slice(), [1, -3, 5].as_slice(), 3),
            ([5, -3, 1, 5, 1, 5, -3].as_slice(), [1, -3, 5].as_slice(), 3),
            ([-3, 3, 1, 5, 5].as_slice(), [1, -1].as_slice(), 2),
            ([1, 3, 3, 1, 5, -3, -3, 5].as_slice(), [1, -1].as_slice(), 2),
            ([1, 2, -4].as_slice(), [1, 2, -4].as_slice(), 3),
        ] {
            let mut sclause = Vec::from(clause);
            let resr = sclause.simplify();
            assert_eq!((exp, expres), (sclause.as_slice(), resr));
        }
    }

    macro_rules! input_clause_assert {
        ($cls:ident, $list:expr, $tau:expr) => {
            assert_eq!($list.as_slice(), $cls.clause().as_slice());
            assert_eq!($tau, $cls.is_tautology());
        };

        ($cls:ident, $tau:expr) => {
            assert!($cls.clause().is_empty());
            assert_eq!($tau, $cls.is_tautology());
        };
    }

    #[test]
    fn test_input_clause_push() {
        let mut iclause = InputClause::new();
        assert_eq!(0, iclause.clause().clause_len());
        input_clause_assert!(iclause, false);
        assert!(iclause.clause().is_empty());
        iclause.push(false);

        iclause.push(2);
        iclause.push(-3);
        iclause.push(Literal::VarLit(-4)); // literal
        iclause.push(false);
        assert_eq!([2, -3, -4].as_slice(), iclause.clause().as_slice());
        input_clause_assert!(iclause, [2, -3, -4], false);
        assert_eq!(3, iclause.clause_len());
        assert!(!iclause.clause().is_empty());

        iclause.push(Literal::Value(true));
        input_clause_assert!(iclause, [1, -1], true);
        iclause.push(-7);
        input_clause_assert!(iclause, [1, -1], true);
        assert_eq!(2, iclause.clause().clause_len());

        iclause.push(true);
        input_clause_assert!(iclause, [1, -1], true);
    }

    #[test]
    fn test_input_clause_extend() {
        let mut iclause = InputClause::new();
        iclause.push(2);
        iclause.extend([4, -1, 3]);
        input_clause_assert!(iclause, [2, 4, -1, 3], false);

        // with tautology
        let mut iclause = InputClause::new();
        iclause.push(2);
        iclause.push(true);
        iclause.extend([4, -1, 3]);
        input_clause_assert!(iclause, [1, -1], true);

        let mut iclause = InputClause::new();
        iclause.push(2);
        iclause.extend([4, -1, 3]);
        input_clause_assert!(iclause, [2, 4, -1, 3], false);

        let mut iclause = InputClause::new();
        iclause.extend(Vec::<i32>::new());
        input_clause_assert!(iclause, false);

        // literals
        let mut iclause = InputClause::new();
        iclause.push(2);
        iclause.extend([Literal::Value(false), 4.into(), (-1).into(), 3.into()]);
        input_clause_assert!(iclause, [2, 4, -1, 3], false);

        let mut iclause = InputClause::<i32>::new();
        iclause.extend([Literal::Value(false), 4.into(), (-1).into(), 3.into()]);
        input_clause_assert!(iclause, [4, -1, 3], false);

        // with tautology
        let mut iclause = InputClause::<i32>::new();
        iclause.extend([
            Literal::Value(false),
            4.into(),
            (-1).into(),
            true.into(),
            3.into(),
        ]);
        input_clause_assert!(iclause, [1, -1], true);

        let mut iclause = InputClause::<i32>::new();
        iclause.extend(Vec::<Literal<i32>>::new());
        input_clause_assert!(iclause, false);
    }

    #[test]
    fn test_input_clause_from_iter() {
        let iclause = InputClause::from_iter([4, -1, 3]);
        input_clause_assert!(iclause, [4, -1, 3], false);

        let iclause = InputClause::from_iter(Vec::<i32>::new());
        input_clause_assert!(iclause, false);

        let iclause =
            InputClause::from_iter([Literal::Value(false), 4.into(), (-1).into(), 3.into()]);
        input_clause_assert!(iclause, [4, -1, 3], false);

        // from literals iterator
        let iclause = InputClause::<i32>::from_iter([
            Literal::Value(false),
            4.into(),
            true.into(),
            (-1).into(),
            3.into(),
        ]);
        input_clause_assert!(iclause, [1, -1], true);

        let iclause = InputClause::<i32>::from_iter(Vec::<Literal<i32>>::new());
        input_clause_assert!(iclause, false);
    }

    fn quantset_func<T, Q>(t: Q) -> Q
    where
        T: VarLit,
        Q: QuantSet<T>,
        <T as TryInto<usize>>::Error: Debug,
    {
        t
    }

    #[test]
    fn test_quantset() {
        let quantset = [1, 2, 4];
        assert_eq!(3, quantset[..].quant_len());
        quantset_func(quantset);
        quantset_func(Vec::from(quantset));
        quantset_func(BTreeSet::from(quantset));
        quantset_func(quantset.as_slice());

        let mut v = vec![];
        quantset.quant_for_each(|x| v.push(*x));
        assert_eq!(Vec::from([1, 2, 4]), v);
        assert!(quantset.quant_all(|x| *x <= 4));
        assert!(!quantset.quant_all(|x| *x > 2));
        assert_eq!(quantset.len(), quantset.quant_len());
    }

    #[test]
    fn test_quantset_check_quantset() {
        for (vn, exp, q) in [
            (5, true, [1, 4, 3].as_slice()),
            (5, false, [1, 0, 4, 3].as_slice()),
            (4, true, [1, 4, 2].as_slice()),
            (4, false, [1, 5, 2].as_slice()),
            (5, false, [1, -4, 3].as_slice()),
        ] {
            assert_eq!(exp, q.check_quantset(vn));
        }
    }

    #[test]
    fn test_cnfwriter_write_header() {
        let mut cnf_writer = CNFWriter::new(vec![]);
        assert_eq!(
            Ok(()),
            cnf_writer.write_header(7, 4).map_err(|x| x.to_string())
        );
        assert_eq!("p cnf 7 4\n", String::from_utf8_lossy(cnf_writer.inner()));
        assert_eq!(
            Err("Header has already been written".to_string()),
            cnf_writer.write_header(7, 4).map_err(|x| x.to_string())
        );

        let mut cnf_writer = CNFWriter::new(vec![]);
        assert_eq!(
            Ok(()),
            cnf_writer.write_header(0, 0).map_err(|x| x.to_string())
        );
        assert_eq!("p cnf 0 0\n", String::from_utf8_lossy(cnf_writer.inner()));
    }

    #[test]
    fn test_cnfwriter_write_clause() {
        let mut cnf_writer = CNFWriter::new(vec![]);
        cnf_writer.write_header(3, 2).unwrap();
        assert_eq!(
            Ok(()),
            cnf_writer
                .write_clause([-1, 2, 3])
                .map_err(|x| x.to_string())
        );
        assert_eq!(
            Ok(()),
            cnf_writer.write_clause([1, -2]).map_err(|x| x.to_string())
        );
        assert_eq!(
            r##"p cnf 3 2
-1 2 3 0
1 -2 0
"##,
            String::from_utf8_lossy(cnf_writer.inner())
        );

        // check error handling
        let mut cnf_writer = CNFWriter::new(vec![]);
        assert_eq!(
            Err("Header has not been written".to_string()),
            cnf_writer
                .write_clause([-1, 2, 3])
                .map_err(|x| x.to_string())
        );

        let mut cnf_writer = CNFWriter::new(vec![]);
        cnf_writer.write_header(3, 2).unwrap();
        assert_eq!(
            Err("Variable literal is out of range".to_string()),
            cnf_writer
                .write_clause([-1, 4, 3])
                .map_err(|x| x.to_string())
        );
        assert_eq!(
            Ok(()),
            cnf_writer
                .write_clause([-1, -1, 2, 3, 3])
                .map_err(|x| x.to_string())
        );
        assert_eq!(
            Ok(()),
            cnf_writer
                .write_clause([-2, 1, -2])
                .map_err(|x| x.to_string())
        );
        // check written cnf
        assert_eq!(
            r##"p cnf 3 2
-1 2 3 0
1 -2 0
"##,
            String::from_utf8_lossy(cnf_writer.inner())
        );
        assert_eq!(
            Err("Too many clauses to write".to_string()),
            cnf_writer.write_clause([1, -3]).map_err(|x| x.to_string())
        );
    }

    #[test]
    fn test_cnfwriter_write_clauses_with_empty() {
        let mut cnf_writer = CNFWriter::new(vec![]);
        cnf_writer.write_header(3, 4).unwrap();
        for c in [
            [-2, 1, 3].as_slice(),
            [2, 1].as_slice(),
            [].as_slice(),
            [3, -1, 2].as_slice(),
        ] {
            cnf_writer.write_clause(c).unwrap();
        }
        assert_eq!(
            r##"p cnf 3 4
1 -2 3 0
1 2 0
0
-1 2 3 0
"##,
            String::from_utf8_lossy(cnf_writer.inner())
        );
    }

    #[test]
    fn test_cnfwriter_write_literals() {
        let mut cnf_writer = CNFWriter::new(vec![]);
        cnf_writer.write_header(3, 2).unwrap();
        cnf_writer
            .write_literals([
                Literal::from(-1),
                (-1).into(),
                false.into(),
                2.into(),
                3.into(),
                3.into(),
            ])
            .unwrap();
        cnf_writer
            .write_literals([Literal::from(2), false.into(), (1).into()])
            .unwrap();
        assert_eq!(
            r##"p cnf 3 2
-1 2 3 0
1 2 0
"##,
            String::from_utf8_lossy(cnf_writer.inner())
        );
    }

    #[test]
    fn test_cnfwriter_write_quantifiers() {
        let mut cnf_writer = CNFWriter::new(vec![]);
        cnf_writer.write_header(5, 4).unwrap();
        cnf_writer.write_quant(Quantifier::ForAll, [3, 1]).unwrap();
        cnf_writer.write_quant(Quantifier::Exists, [2]).unwrap();
        cnf_writer.write_quant(Quantifier::ForAll, [4, 5]).unwrap();
        for c in [
            [-2, 1, 3].as_slice(),
            [2, 4].as_slice(),
            [5, -1, 2].as_slice(),
            [-5, 3, -4].as_slice(),
        ] {
            cnf_writer.write_clause(c).unwrap();
        }
        assert_eq!(
            r##"p cnf 5 4
a 3 1 0
e 2 0
a 4 5 0
1 -2 3 0
2 4 0
-1 2 5 0
3 -4 -5 0
"##,
            String::from_utf8_lossy(cnf_writer.inner())
        );

        let mut cnf_writer = CNFWriter::new(vec![]);
        cnf_writer.write_header(5, 4).unwrap();
        cnf_writer.write_clause([1, 4]).unwrap();
        assert_eq!(
            Err("Quantifier after clauses".to_string()),
            cnf_writer
                .write_quant(Quantifier::ForAll, [3, 1])
                .map_err(|x| x.to_string())
        );

        let mut cnf_writer = CNFWriter::new(vec![]);
        cnf_writer.write_header(5, 4).unwrap();
        cnf_writer.write_quant(Quantifier::ForAll, [3, 1]).unwrap();
        cnf_writer.write_quant(Quantifier::Exists, [2]).unwrap();
        assert_eq!(
            Err("Quantifier's duplicate".to_string()),
            cnf_writer
                .write_quant(Quantifier::Exists, [4, 5])
                .map_err(|x| x.to_string())
        );
    }
}