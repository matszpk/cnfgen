// mod.rs - integer expression structures.

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module to generate CNF clauses from integer expressions.
//!
//! This module contains traits and main structure to operate on integer expressions:
//! `IntExprNode`. An IntExprNode just holds boolean expression for every bit of integer.
//! You can use defined type of IntExprNode or just define your integer by supplying
//! generic parameters.
//!
//! Three generic parameters determine type of IntExprNode.
//! The first T parameter is just variable literal type - it can be omitted.
//! The second parameter is typed integer (from typenum crate) that determine number of bits
//! of integer. The last parameter is sign - true if signed integer or false if unsigned integer.
//! Type of IntExprNode can be written in form: `IntExprNode<i32, U12, false>` -
//! IntExprNode for 12-bit unsigned integer with 32-bit variable literals.
//!
//! ## Operations on expression nodes.
//!
//! An IntExprNode provides many operations:
//!
//! * equality - returns true if two expressions are equal.
//! * inequalities - less, less or equal, greater, greater or equal.
//! * absolute value - `abs()` only for signed IntExprNode.
//! * bitwise arithmentic - bitwise AND, OR, XOR and NOT by using standard operators.
//! * modular arithmetic - addition, subtraction, negation, multiplication.
//! * conditional arithmentic - modular arithmentic that provides condition.
//! * shifts - left and right shifts.
//! * conditional shifts - left and right.
//! * full multiplication - full multiplication that returns full product.
//! * division and remainder (modulo) - returns quotient, remainder and required condition.
//! * counting bits.
//! * counting leading and trailing ones and zeroes.
//!
//! Many operations are defined through additional traits in this module.
//! These traits and basic operations are implemented for expression nodes and integers -
//! it possible to use integer as self or as an argument with expression node like:
//! `332.mod_mul(x1)`. The method `constant` provide simple way to convert integer
//! into an expression node (IntExprNode).
//!
//! The simple example of usage:
//! ```
//! use cnfgen::boolexpr::*;
//! use cnfgen::intexpr::*;
//! use cnfgen::writer::{CNFError, CNFWriter};
//! use std::io;
//! fn write_diophantine_equation() -> Result<(), CNFError> {
//!     // define ExprCreator.
//!     let creator = ExprCreator32::new();
//!     // define variables - signed 32-bit wide.
//!     let x = I32ExprNode::variable(creator.clone());
//!     let y = I32ExprNode::variable(creator.clone());
//!     let z = I32ExprNode::variable(creator.clone());
//!     // define equation: x^2 + y^2 - 77*z^2 = 0
//!     let powx = x.clone().fullmul(x);  // x^2
//!     let powy = y.clone().fullmul(y);  // y^2
//!     let powz = z.clone().fullmul(z);  // z^2
//!     // We use cond_mul to get product and required condition to avoid overflow.
//!     let (prod, cond0) = powz.cond_mul(77i64);
//!     // Similary, we use conditional addition and conditional subtraction.
//!     let (sum1, cond1) = powx.cond_add(powy);
//!     let (diff2, cond2) = sum1.cond_sub(prod);
//!     // define final formula with required conditions.
//!     let formula: BoolExprNode<_> = diff2.equal(0) & cond0 & cond1 & cond2;
//!     // write CNF to stdout.
//!     formula.write(&mut CNFWriter::new(io::stdout()))
//! }
//! ```
//!
//! ## Conditional operations.
//!
//! Conditional operations defined by `IntCondXXX` traits is specific type of operations that
//! provide additional condition as an boolean expression. This condition is satisfiable when
//! no overflow encountered while evaluating operation. It can supplied at root of final
//! expression to force evaluate an operation without unexpected overflow like in this
//! simple example that generates diophantic equation.
//!
//! The condition in conditional shifting
//! just will be satisfied when shift (right argument) value is lower than number of
//! bits of left argument.
//!
//! Division and remainder just returns additional condition that will be satisified if
//! right argument is not zero.
//!
//! ## Conversion between types.
//!
//! It is possible conversion between various IntExprNodes that have various sizes and signs.
//! Conversions are implemented by using standard `From` and `TryFrom` traits.
//! Conversion from lesser IntExprNode into greater IntExprNode if source are unsigned.
//!
//! ## Other operations.
//!
//! IntExprNode provides other operations like concatenation of bits, splitting into two
//! shorter IntExprNodes, casting to signed or unsigned and selection of bits of IntExprNodes.

use std::cell::RefCell;
use std::cmp;
use std::fmt::Debug;
use std::iter;
use std::ops::{Add, BitAnd, BitOr, Neg, Not, Sub};
use std::rc::Rc;

use generic_array::typenum::*;
use generic_array::*;

use crate::boolexpr::{bool_ite, bool_opt_ite, half_adder, BoolExprNode};
pub use crate::boolexpr_creator::{ExprCreator, ExprCreator32, ExprCreatorSys};
use crate::dynintexpr::DynIntExprNode;
use crate::int_utils::*;
use crate::writer::{Literal, VarLit};
use crate::{impl_int_bitop_assign, impl_int_ty1_lt_ty2};

/// Integer error.
#[derive(thiserror::Error, Debug)]
pub enum IntError {
    /// If bit overflow - too many bits required.
    #[error("Bit overflow")]
    BitOverflow,
    /// A value can be negative - it can be happened when convert signed value into unsigned.
    #[error("Value can be negative")]
    CanBeNegative,
    /// If bits number if mismatch for example: while conversion from DynIntExprNode.
    #[error("Bit number mismatch")]
    BitsMismatch,
}

pub mod traits;
pub use traits::*;
pub mod bin_arith;
pub use bin_arith::*;
pub mod int_arith;
pub use int_arith::*;
pub mod extra_arith;
pub use extra_arith::*;

/// The main structure that represents integer expression, subexpression or integer value.
///
/// It joined with the ExprCreator that holds all expressions.
/// Creation of new expression is naturally simple thanks operators. However, expression nodes
/// must be cloned before using in other expressions if they will be used more than once.
/// Simple examples:
///
/// * `(x1 << x2).mod_add(x3.clone()).equal(x3)`
/// * `x1.clone().fullmul(x1).mod_add(x2.clone().fullmul(x2))`
///
/// Integer expression nodes can be used with integer values or variables that will represents
/// constant integer value in an expression. Simple example: `4u8<<x1`.
/// Due to some limitations only some configurations of integer size and IntExprNode sizes
/// are possible.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntExprNode<T: VarLit + Debug, N: ArrayLength<usize>, const SIGN: bool> {
    pub(super) creator: Rc<RefCell<ExprCreator<T>>>,
    pub(super) indexes: GenericArray<usize, N>,
}

impl<T, N: ArrayLength<usize>, const SIGN: bool> IntExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Number of BITS.
    pub const BITS: usize = N::USIZE;
    /// SIGN of integer. It can be false - unsigned, or true - signed.
    pub const SIGN: bool = SIGN;
    /// Internally used logarithm of number of bits.
    pub const LOG_BITS: usize = calc_log_bits(Self::BITS);

    /// Creates new variable as expression node.
    pub fn variable(creator: Rc<RefCell<ExprCreator<T>>>) -> Self {
        let mut indexes = GenericArray::<usize, N>::default();
        {
            let mut creator = creator.borrow_mut();
            indexes.iter_mut().for_each(|x| {
                let l = creator.new_variable();
                *x = creator.single(l);
            });
        }
        IntExprNode { creator, indexes }
    }

    /// Creates integer from boolean expressions. An argument is object convertible into
    /// iterator of `BoolExprNode`.
    pub fn from_boolexprs(iter: impl IntoIterator<Item = BoolExprNode<T>>) -> Option<Self> {
        let mut creator = None;
        GenericArray::from_exact_iter(iter.into_iter().map(|x| {
            // check creator - whether this same
            if let Some(c) = creator.clone() {
                assert_eq!(Rc::as_ptr(&c), Rc::as_ptr(&x.creator));
            } else {
                creator = Some(x.creator.clone());
            }
            x.index
        }))
        .map(|indexes| IntExprNode {
            creator: creator.unwrap(),
            indexes,
        })
    }

    /// Creates filled integer from from Literal.
    pub fn filled(creator: Rc<RefCell<ExprCreator<T>>>, v: impl Into<Literal<T>>) -> Self {
        IntExprNode {
            creator: creator.clone(),
            indexes: GenericArray::from_exact_iter(
                iter::repeat(creator.borrow_mut().single(v)).take(N::USIZE),
            )
            .unwrap(),
        }
    }

    /// Creates filled integer from from a boolean value.
    pub fn filled_expr(v: BoolExprNode<T>) -> Self {
        IntExprNode {
            creator: v.creator.clone(),
            indexes: GenericArray::from_exact_iter(iter::repeat(v.index).take(N::USIZE)).unwrap(),
        }
    }

    /// Casts integer into unsigned integer.
    pub fn as_unsigned(self) -> IntExprNode<T, N, false> {
        IntExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }

    /// Casts integer into signed integer.
    pub fn as_signed(self) -> IntExprNode<T, N, true> {
        IntExprNode {
            creator: self.creator,
            indexes: self.indexes,
        }
    }
}

impl<T, N: ArrayLength<usize>> IntExprNode<T, N, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer that contains `N2` bits starting from `start`.
    pub fn subvalue<N2>(&self, start: usize) -> IntExprNode<T, N2, false>
    where
        N2: ArrayLength<usize>,
    {
        IntExprNode {
            creator: self.creator.clone(),
            indexes: GenericArray::clone_from_slice(&self.indexes[start..start + N2::USIZE]),
        }
    }

    /// Creates integer that contains `N2` selected bits. List of bits given in
    /// object that can be converted into iterator of indexes. It returns None if
    /// number of elements in iterator doesn't match.
    pub fn select_bits<N2, I>(&self, iter: I) -> Option<IntExprNode<T, N2, false>>
    where
        N2: ArrayLength<usize>,
        I: IntoIterator<Item = usize>,
    {
        GenericArray::from_exact_iter(iter.into_iter().map(|x| self.indexes[x])).map(|indexes| {
            IntExprNode {
                creator: self.creator.clone(),
                indexes,
            }
        })
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn concat<N2>(self, rest: IntExprNode<T, N2, false>) -> IntExprNode<T, Sum<N, N2>, false>
    where
        N: Add<N2>,
        N2: ArrayLength<usize>,
        Sum<N, N2>: ArrayLength<usize>,
    {
        use generic_array::sequence::*;
        assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rest.creator));
        IntExprNode {
            creator: self.creator,
            indexes: self.indexes.concat(rest.indexes),
        }
    }

    /// Splits integer into two parts: the first with `K` bits and second with rest of bits.
    pub fn split<K>(
        self,
    ) -> (
        IntExprNode<T, K, false>,
        IntExprNode<T, operator_aliases::Diff<N, K>, false>,
    )
    where
        N: Sub<K>,
        K: ArrayLength<usize>,
        operator_aliases::Diff<N, K>: ArrayLength<usize>,
    {
        use generic_array::sequence::*;
        let (indexes1, indexes2) = self.indexes.split();
        (
            IntExprNode {
                creator: self.creator.clone(),
                indexes: indexes1,
            },
            IntExprNode {
                creator: self.creator,
                indexes: indexes2,
            },
        )
    }
}

// TryFrom implementation
macro_rules! impl_int_try_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                TryFrom<IntExprNode<T, $ty2, SIGN2>> for IntExprNode<T, $ty1, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntExprNode<T, $ty2, SIGN2>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                // if all rest of bits are 0 - just false
                if !v.indexes.iter().skip(len1).all(|x| *x==0) {
                    return Err(IntError::BitOverflow);
                }
                Ok(IntExprNode::<T, $ty1, false>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntExprNode<T, $ty2, false>> for IntExprNode<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntExprNode<T, $ty2, false>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                // if all rest of bits are 0 - just false
                if !v.indexes.iter().skip(len1-1).all(|x| *x==0) {
                    return Err(IntError::BitOverflow);
                }
                Ok(IntExprNode::<T, $ty1, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntExprNode<T, $ty2, true>> for IntExprNode<T, $ty1, true>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntExprNode<T, $ty2, true>) -> Result<Self, Self::Error> {
                let len1 = <$ty1>::USIZE;
                let last_idx = v.indexes[len1-1];
                if !v.indexes.iter().skip(len1).all(|x| last_idx==*x) {
                    return Err(IntError::BitOverflow);
                }
                Ok(IntExprNode::<T, $ty1, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::clone_from_slice(&v.indexes[0..len1]) })
            }
        }

        // try from for rest
        impl<T: VarLit, $( $gparams ),* >
                TryFrom<IntExprNode<T, $ty1, true>> for IntExprNode<T, $ty2, false>
        where
            $ty1: ArrayLength<usize>,
            $ty2: ArrayLength<usize>,
        {
            type Error = IntError;

            fn try_from(v: IntExprNode<T, $ty1, true>) -> Result<Self, Self::Error> {
                if *v.indexes.last().unwrap() != 0 {
                    return Err(IntError::CanBeNegative); // if minus
                }
                // default is zero - then is false - zero bit value
                let mut new_v = IntExprNode::<T, $ty2, false>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                new_v.indexes[0..v.indexes.len()].copy_from_slice(v.indexes.as_slice());
                Ok(new_v)
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_try_from);

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<IntExprNode<T, N, false>>
    for IntExprNode<T, N, true>
{
    type Error = IntError;

    fn try_from(v: IntExprNode<T, N, false>) -> Result<Self, Self::Error> {
        if *v.indexes.last().unwrap() != 0 {
            // if input if higher than possible output
            return Err(IntError::BitOverflow);
        }
        Ok(IntExprNode {
            creator: v.creator,
            indexes: v.indexes,
        })
    }
}

impl<T: VarLit, N: ArrayLength<usize>> TryFrom<IntExprNode<T, N, true>>
    for IntExprNode<T, N, false>
{
    type Error = IntError;

    fn try_from(v: IntExprNode<T, N, true>) -> Result<Self, Self::Error> {
        if *v.indexes.last().unwrap() != 0 {
            // if input is lower than 0
            return Err(IntError::CanBeNegative);
        }
        Ok(IntExprNode {
            creator: v.creator,
            indexes: v.indexes,
        })
    }
}

impl<T: VarLit, N: ArrayLength<usize>, const SIGN: bool> TryFrom<DynIntExprNode<T, SIGN>>
    for IntExprNode<T, N, SIGN>
{
    type Error = IntError;

    fn try_from(v: DynIntExprNode<T, SIGN>) -> Result<Self, Self::Error> {
        if N::USIZE != v.indexes.len() {
            return Err(IntError::BitsMismatch);
        }
        Ok(IntExprNode {
            creator: v.creator,
            indexes: GenericArray::clone_from_slice(&v.indexes),
        })
    }
}

// From implementation
macro_rules! impl_int_from {
    ($ty1:ty, $ty2: ty, $($gparams:ident),*) => {
        impl<T: VarLit, const SIGN2: bool, $( $gparams ),* >
                From<IntExprNode<T, $ty1, false>> for IntExprNode<T, $ty2, SIGN2>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: IntExprNode<T, $ty1, false>) -> Self {
                // default is zero - then is false - zero bit value
                let mut new_v = IntExprNode::<T, $ty2, SIGN2>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                new_v.indexes[0..v.indexes.len()].copy_from_slice(v.indexes.as_slice());
                new_v
            }
        }

        impl<T: VarLit, $( $gparams ),* >
                From<IntExprNode<T, $ty1, true>> for IntExprNode<T, $ty2, true>
            where
                $ty1: ArrayLength<usize>,
                $ty2: ArrayLength<usize>, {
            fn from(v: IntExprNode<T, $ty1, true>) -> Self {
                // default is zero - then is false - zero bit value
                let len = <$ty1>::USIZE;
                let mut new_v = IntExprNode::<T, $ty2, true>{ creator: v.creator.clone(),
                    indexes: GenericArray::default() };
                new_v.indexes[0..len].copy_from_slice(v.indexes.as_slice());
                let last = *v.indexes.last().unwrap();
                // copy sign to rest
                new_v.indexes[len..].iter_mut().for_each(|x| *x = last);
                new_v
            }
        }
    }
}

impl_int_ty1_lt_ty2!(impl_int_from);

impl<T: VarLit, N, const SIGN: bool> From<BoolExprNode<T>> for IntExprNode<T, N, SIGN>
where
    N: ArrayLength<usize>,
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Put boolean as first bit of integer.
    fn from(v: BoolExprNode<T>) -> Self {
        assert_ne!(N::USIZE, 0);
        let ec = v.creator.clone();
        Self::from_boolexprs(
            std::iter::once(v)
                .chain((0..N::USIZE - 1).map(|_| BoolExprNode::single_value(ec.clone(), false))),
        )
        .unwrap()
    }
}

// types

/// IntExprNode for unsinged 8-bit integer.
pub type U8ExprNode<T> = IntExprNode<T, U8, false>;
/// IntExprNode for unsinged 16-bit integer.
pub type U16ExprNode<T> = IntExprNode<T, U16, false>;
/// IntExprNode for unsinged 32-bit integer.
pub type U32ExprNode<T> = IntExprNode<T, U32, false>;
/// IntExprNode for unsinged 64-bit integer.
pub type U64ExprNode<T> = IntExprNode<T, U64, false>;
/// IntExprNode for unsinged 128-bit integer.
pub type U128ExprNode<T> = IntExprNode<T, U128, false>;

/// IntExprNode for unsinged integer with various size.
pub type UExprNode<T, N> = IntExprNode<T, N, false>;
/// IntExprNode for singed integer with various size.
pub type IExprNode<T, N> = IntExprNode<T, N, true>;

/// IntExprNode for singed 8-bit integer.
pub type I8ExprNode<T> = IntExprNode<T, U8, true>;
/// IntExprNode for singed 16-bit integer.
pub type I16ExprNode<T> = IntExprNode<T, U16, true>;
/// IntExprNode for singed 32-bit integer.
pub type I32ExprNode<T> = IntExprNode<T, U32, true>;
/// IntExprNode for singed 64-bit integer.
pub type I64ExprNode<T> = IntExprNode<T, U64, true>;
/// IntExprNode for singed 128-bit integer.
pub type I128ExprNode<T> = IntExprNode<T, U128, true>;

/// Returns result of the If-Then-Else (ITE) - integer version.
pub fn int_ite<C, T, E>(
    c: C,
    t: T,
    e: E,
) -> <<T as BitAnd>::Output as BitOr<<E as BitAnd>::Output>>::Output
where
    C: Not + Clone,
    T: BitAnd + BitMask<C>,
    E: BitAnd + BitMask<<C as Not>::Output>,
    <T as BitAnd<T>>::Output: BitOr<<E as BitAnd<E>>::Output>,
{
    (<T as BitMask<C>>::bitmask(c.clone()) & t)
        | (<E as BitMask<<C as Not>::Output>>::bitmask(!c) & e)
}

/// Returns result of the If-Then-Else (ITE) - integer version - optimized version.
pub fn int_opt_ite<T, N, const SIGN: bool>(
    c: BoolExprNode<T>,
    t: IntExprNode<T, N, SIGN>,
    e: IntExprNode<T, N, SIGN>,
) -> IntExprNode<T, N, SIGN>
where
    N: ArrayLength<usize>,
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    IntExprNode::from_boolexprs(
        t.iter()
            .zip(e.iter())
            .map(|(tb, eb)| bool_opt_ite(c.clone(), tb, eb)),
    )
    .unwrap()
}

/// Returns minimal value from two.
pub fn int_min<T, E>(t: T, e: E) -> <<T as BitAnd>::Output as BitOr<<E as BitAnd>::Output>>::Output
where
    <T as traits::IntOrd<E>>::Output: Clone + Not,
    T: Clone + BitAnd + BitMask<<T as IntOrd<E>>::Output> + IntOrd<E>,
    E: Clone + BitAnd + BitMask<<<T as IntOrd<E>>::Output as Not>::Output>,
    <T as BitAnd<T>>::Output: BitOr<<E as BitAnd<E>>::Output>,
{
    int_ite(t.clone().less_than(e.clone()), t, e)
}

/// Returns maximal value from two.
pub fn int_max<T, E>(t: T, e: E) -> <<T as BitAnd>::Output as BitOr<<E as BitAnd>::Output>>::Output
where
    <T as traits::IntOrd<E>>::Output: Clone + Not,
    T: Clone + BitAnd + BitMask<<T as IntOrd<E>>::Output> + IntOrd<E>,
    E: Clone + BitAnd + BitMask<<<T as IntOrd<E>>::Output as Not>::Output>,
    <T as BitAnd<T>>::Output: BitOr<<E as BitAnd<E>>::Output>,
{
    int_ite(t.clone().greater_than(e.clone()), t, e)
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index.
pub fn int_table<T, N, K, I, const SIGN: bool>(
    index: IntExprNode<T, K, SIGN>,
    table_iter: I,
) -> IntExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = IntExprNode<T, N, SIGN>>,
{
    let mut ites = vec![];
    let mut iter = table_iter.into_iter();
    while let Some(v) = iter.next() {
        if let Some(v2) = iter.next() {
            ites.push(int_ite(index.bit(0), v2, v));
        } else {
            panic!("Odd number of elements");
        }
    }

    for step in 1..K::USIZE {
        if (ites.len() & 1) != 0 {
            panic!("Odd number of elements");
        }
        for i in 0..(ites.len() >> 1) {
            ites[i] = int_ite(
                index.bit(step),
                ites[(i << 1) + 1].clone(),
                ites[i << 1].clone(),
            );
        }
        ites.resize(
            ites.len() >> 1,
            IntExprNode::filled(index.creator.clone(), false),
        );
    }

    ites.pop().unwrap()
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index.
pub fn int_booltable<T, K, I, const SIGN: bool>(
    index: IntExprNode<T, K, SIGN>,
    table_iter: I,
) -> BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = BoolExprNode<T>>,
{
    let mut ites = vec![];
    let mut iter = table_iter.into_iter();
    while let Some(v) = iter.next() {
        if let Some(v2) = iter.next() {
            ites.push(bool_ite(index.bit(0), v2, v));
        } else {
            panic!("Odd number of elements");
        }
    }

    for step in 1..K::USIZE {
        if (ites.len() & 1) != 0 {
            panic!("Odd number of elements");
        }
        for i in 0..(ites.len() >> 1) {
            ites[i] = bool_ite(
                index.bit(step),
                ites[(i << 1) + 1].clone(),
                ites[i << 1].clone(),
            );
        }
        ites.resize(
            ites.len() >> 1,
            BoolExprNode::single_value(index.creator.clone(), false),
        );
    }

    ites.pop().unwrap()
}

/// Returns result of indexing of table with values. Optimized version.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index. This optimized version reduces duplicates and negations.
pub fn int_opt_table<T, N, K, I, const SIGN: bool>(
    index: IntExprNode<T, K, SIGN>,
    table_iter: I,
) -> IntExprNode<T, N, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = IntExprNode<T, N, SIGN>>,
{
    let tbl = Vec::from_iter(table_iter);
    IntExprNode::from_boolexprs(
        (0..N::USIZE).map(|bit| int_opt_booltable(index.clone(), tbl.iter().map(|t| t.bit(bit)))),
    )
    .unwrap()
}

/// Returns result of indexing of table with values. Optimized version.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index. This optimized version reduces duplicates and negations.
pub fn int_opt_booltable<T, K, I, const SIGN: bool>(
    index: IntExprNode<T, K, SIGN>,
    table_iter: I,
) -> BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
    I: IntoIterator<Item = BoolExprNode<T>>,
{
    use crate::boolexpr::{boolexpr_are_negated, boolexpr_are_same};
    let mut ites: Vec<BoolExprNode<T>> = vec![];
    let tbl = Vec::from_iter(table_iter);
    // detect any repetitions in any step before generation
    let mut iter = tbl.iter();
    while let Some(v) = iter.next() {
        if let Some(v2) = iter.next() {
            let count = ites.len() << 1;
            let mut already_added = false;
            for k in 1..K::USIZE {
                let kbit = 1 << k;
                // if odd in some bit level
                if (count & kbit) != 0 {
                    // check two pairs
                    if boolexpr_are_same(&tbl[count], &tbl[count - kbit])
                        && boolexpr_are_same(&tbl[count + 1], &tbl[count + 1 - kbit])
                    {
                        // if are same
                        ites.push(ites[(count - kbit) >> 1].clone());
                        already_added = true;
                        break;
                    } else if boolexpr_are_negated(&tbl[count], &tbl[count - kbit])
                        && boolexpr_are_negated(&tbl[count + 1], &tbl[count + 1 - kbit])
                    {
                        // if negated
                        ites.push(!ites[(count - kbit) >> 1].clone());
                        already_added = true;
                        break;
                    }
                }
            }
            if !already_added {
                ites.push(bool_opt_ite(index.bit(0), v2.clone(), v.clone()));
            }
        } else {
            panic!("Odd number of elements");
        }
    }

    for step in 1..K::USIZE {
        if (ites.len() & 1) != 0 {
            panic!("Odd number of elements");
        }
        for i in 0..(ites.len() >> 1) {
            let count = i << (step + 1);
            let mut already_added = false;
            for k in step + 1..K::USIZE {
                let kbit = 1 << k;
                // if odd in some bit level
                if (count & kbit) != 0 {
                    // check two pairs
                    if (0..(1 << (step + 1)))
                        .all(|x| boolexpr_are_same(&tbl[count + x], &tbl[count + x - kbit]))
                    {
                        // if are same
                        ites[i] = ites[(count - kbit) >> (step + 1)].clone();
                        already_added = true;
                        break;
                    } else if (0..(1 << (step + 1)))
                        .all(|x| boolexpr_are_negated(&tbl[count + x], &tbl[count + x - kbit]))
                    {
                        // if negated
                        ites[i] = !ites[(count - kbit) >> (step + 1)].clone();
                        already_added = true;
                        break;
                    }
                }
            }
            if !already_added {
                ites[i] = bool_opt_ite(
                    index.bit(step),
                    ites[(i << 1) + 1].clone(),
                    ites[i << 1].clone(),
                );
            }
        }
        ites.resize(
            ites.len() >> 1,
            BoolExprNode::single_value(index.creator.clone(), false),
        );
    }

    ites.pop().unwrap()
}

/// Demultiplexer - returns list of outputs of demultiplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn int_demux<T, N, K, const SIGN: bool>(
    index: IntExprNode<T, K, SIGN>,
    value: IntExprNode<T, N, SIGN>,
) -> Vec<IntExprNode<T, N, SIGN>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    N: ArrayLength<usize>,
    K: ArrayLength<usize>,
{
    assert_ne!(K::USIZE, 0);
    let mut chooser_table = vec![];
    chooser_table.push(!index.bit(K::USIZE - 1));
    chooser_table.push(index.bit(K::USIZE - 1));
    for l in 1..K::USIZE {
        let mut new_chooser_table = Vec::with_capacity(1 << l);
        for i in 0..1 << l {
            new_chooser_table.push(chooser_table[i].clone() & !index.bit(K::USIZE - l - 1));
            new_chooser_table.push(chooser_table[i].clone() & index.bit(K::USIZE - l - 1));
        }
        chooser_table = new_chooser_table;
    }
    (0..1 << K::USIZE)
        .map(|i| value.clone() & BitMask::bitmask(chooser_table[i].clone()))
        .collect::<Vec<_>>()
}

/// Demultiplexer - returns list of outputs of demultiplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn int_booldemux<T, K, const SIGN: bool>(
    index: IntExprNode<T, K, SIGN>,
    value: BoolExprNode<T>,
) -> Vec<BoolExprNode<T>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    K: ArrayLength<usize>,
{
    assert_ne!(K::USIZE, 0);
    let mut chooser_table = vec![];
    chooser_table.push(!index.bit(K::USIZE - 1));
    chooser_table.push(index.bit(K::USIZE - 1));
    for l in 1..K::USIZE {
        let mut new_chooser_table = Vec::with_capacity(1 << l);
        for i in 0..1 << l {
            new_chooser_table.push(chooser_table[i].clone() & !index.bit(K::USIZE - l - 1));
            new_chooser_table.push(chooser_table[i].clone() & index.bit(K::USIZE - l - 1));
        }
        chooser_table = new_chooser_table;
    }
    (0..1 << K::USIZE)
        .map(|i| value.clone() & chooser_table[i].clone())
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boolexpr::BoolExprNode;

    #[test]
    fn test_expr_node() {
        let ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U8, false>::variable(ec.clone());
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9], *x1.indexes);
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9], *(x1.clone().as_signed()).indexes);
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9], *(x1.as_unsigned()).indexes);
        let x2 = IntExprNode::<isize, U8, true>::variable(ec.clone());
        assert_eq!([10, 11, 12, 13, 14, 15, 16, 17], *x2.indexes);
        assert_eq!(
            [10, 11, 12, 13, 14, 15, 16, 17],
            *(x2.clone().as_unsigned()).indexes
        );
        assert_eq!([10, 11, 12, 13, 14, 15, 16, 17], *(x2.as_signed()).indexes);

        let b1 = BoolExprNode::variable(ec.clone());
        let x3 = IntExprNode::<isize, U4, false>::filled(ec.clone(), b1.varlit().unwrap());
        assert_eq!([18, 18, 18, 18], *x3.indexes);
        let b1 = BoolExprNode::variable(ec.clone());
        let b2 = BoolExprNode::variable(ec.clone());
        let bxp = b1.clone() ^ b2.clone();
        let x4 = IntExprNode::<isize, U4, false>::filled_expr(bxp.clone());
        assert_eq!(
            iter::repeat(bxp.index)
                .take(4)
                .collect::<Vec<_>>()
                .as_slice(),
            x4.indexes.as_slice()
        );

        //
        let b3 = BoolExprNode::variable(ec.clone());
        let b4 = BoolExprNode::variable(ec.clone());
        let bxps = [
            b1.clone() & b2.clone(),
            b1.clone() | b2.clone(),
            b1.clone() ^ b2.clone(),
            b1 | b2.clone() | b3.clone(),
            b3.clone() & b4.clone(),
            b3.clone() | b4.clone(),
            b3.clone() ^ b4.clone(),
            b2 | b3 | b4,
        ];

        let x5 = IntExprNode::<isize, U8, false>::from_boolexprs(bxps.clone()).unwrap();
        assert_eq!(
            bxps.iter().map(|x| x.index).collect::<Vec<_>>().as_slice(),
            x5.indexes.as_slice()
        );
    }

    #[test]
    fn test_expr_node_manip() {
        let ec = ExprCreator::new();
        let x1 = IntExprNode::<isize, U16, false>::variable(ec.clone());
        let x2 = x1.subvalue::<U6>(7);
        assert_eq!([9, 10, 11, 12, 13, 14], *x2.indexes);
        let x3 = x1
            .select_bits::<U9, _>([3, 8, 9, 0, 3, 4, 12, 14, 15])
            .unwrap();
        assert_eq!([5, 10, 11, 2, 5, 6, 14, 16, 17], *x3.indexes);
        assert_eq!(None, x1.select_bits::<U9, _>([3, 8, 9, 0, 3, 4, 12, 14]));
        assert_eq!(
            None,
            x1.select_bits::<U9, _>([3, 8, 9, 0, 3, 4, 12, 14, 15, 0])
        );

        let y1 = IntExprNode::<isize, U8, false>::variable(ec.clone());
        let z1 = x1.clone().concat(y1.clone());
        assert_eq!(
            (2..(2 + 24)).into_iter().collect::<Vec<usize>>().as_slice(),
            z1.indexes.as_slice()
        );
        let z1 = y1.concat(x1);
        assert_eq!(
            ((2 + 16)..(2 + 24))
                .into_iter()
                .chain((2..18).into_iter())
                .collect::<Vec<usize>>()
                .as_slice(),
            z1.indexes.as_slice()
        );
        let (xt1, xt2) = z1.split::<U5>();
        assert_eq!([18, 19, 20, 21, 22], *xt1.indexes);
        assert_eq!(
            ((2 + 16 + 5)..(2 + 24))
                .into_iter()
                .chain((2..18).into_iter())
                .collect::<Vec<usize>>()
                .as_slice(),
            xt2.indexes.as_slice()
        );
    }

    #[test]
    fn test_expr_node_from() {
        let ec = ExprCreator::new();
        // Unsigned N -> Unsigned N+X
        let x1 = IntExprNode::<isize, U8, false>::variable(ec.clone());
        let x2 = IntExprNode::<isize, U14, false>::from(x1.clone());
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0], *x2.indexes);
        // Unsigned N -> Signed N+X
        let ix2 = IntExprNode::<isize, U14, true>::from(x1.clone());
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 0, 0, 0], *ix2.indexes);
        let ix1 = IntExprNode::<isize, U8, true>::variable(ec.clone());
        // Signed N, where SIGN=var -> Signed N+X
        let ix2 = IntExprNode::<isize, U12, true>::from(ix1.clone());
        assert_eq!(
            [10, 11, 12, 13, 14, 15, 16, 17, 17, 17, 17, 17],
            *ix2.indexes
        );
    }

    #[test]
    fn test_expr_node_try_from_dynint_expr_node() {
        use crate::dynintexpr::DynIntExprNode;
        let ec = ExprCreator::new();
        let dix1 = DynIntExprNode::<isize, false>::variable(ec.clone(), 10);
        let ix1 = IntExprNode::<isize, U10, false>::try_from(dix1.clone()).unwrap();
        assert_eq!(ix1.indexes.as_slice(), dix1.indexes.as_slice());
    }

    #[test]
    fn test_expr_node_try_from() {
        let ec = ExprCreator::new();
        let ix1 = IntExprNode::<isize, U8, true>::from(IntExprNode::<isize, U7, false>::variable(
            ec.clone(),
        ));
        // Signed N, SIGN=0 -> Unsigned N
        let x1 = IntExprNode::<isize, U8, false>::try_from(ix1.clone()).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0], *x1.indexes);
        // Signed N, SIGN=0 -> Unsigned N+X
        let x2 = IntExprNode::<isize, U9, false>::try_from(ix1.clone()).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0, 0], *x2.indexes);
        let x2 = IntExprNode::<isize, U10, false>::try_from(ix1).unwrap();
        assert_eq!([2, 3, 4, 5, 6, 7, 8, 0, 0, 0], *x2.indexes);

        let ix1 = IntExprNode::<isize, U8, true>::from(IntExprNode::<isize, U7, true>::variable(
            ec.clone(),
        ));
        // Signed N, SIGN=var -> Unsigned N
        assert_eq!(
            Err("Value can be negative".to_string()),
            IntExprNode::<isize, U8, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        // Signed N, SIGN=var -> Unsigned N+X
        assert_eq!(
            Err("Value can be negative".to_string()),
            IntExprNode::<isize, U9, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Value can be negative".to_string()),
            IntExprNode::<isize, U10, false>::try_from(ix1).map_err(|x| x.to_string())
        );

        let x1 = IntExprNode::<isize, U8, false>::from(IntExprNode::<isize, U7, false>::variable(
            ec.clone(),
        ));
        // Unsigned N, LAST=0 -> Signed N
        let ix2 = IntExprNode::<isize, U8, true>::try_from(x1.clone()).unwrap();
        assert_eq!([16, 17, 18, 19, 20, 21, 22, 0], *ix2.indexes);
        // Unsigned N, LAST=0 -> Signed N+X
        let ix2 = IntExprNode::<isize, U9, true>::try_from(x1.clone()).unwrap();
        assert_eq!([16, 17, 18, 19, 20, 21, 22, 0, 0], *ix2.indexes);

        let x1 = IntExprNode::<isize, U8, false>::variable(ec.clone());
        // Unsinged N, LAST=var -> Signed N+X
        let ix2 = IntExprNode::<isize, U9, true>::try_from(x1.clone()).unwrap();
        assert_eq!([23, 24, 25, 26, 27, 28, 29, 30, 0], *ix2.indexes);
        // Unsinged N, LAST=var -> Signed N
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U8, true>::try_from(x1.clone()).map_err(|x| x.to_string())
        );

        //
        // V[N-X..] = 0, LASTS = 0
        let ux1 = IntExprNode::<isize, U8, false>::from(IntExprNode::<isize, U6, false>::variable(
            ec.clone(),
        ));
        // Unsigned N, LASTS=0 -> Unsigned N-X
        let x2 = IntExprNode::<isize, U6, false>::try_from(ux1.clone()).unwrap();
        assert_eq!([31, 32, 33, 34, 35, 36], *x2.indexes);
        // Unsigned N, LASTS=0, V[N-X-1]=var -> Unsigned N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, false>::try_from(ux1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U4, false>::try_from(ux1.clone()).map_err(|x| x.to_string())
        );
        let ix2 = IntExprNode::<isize, U7, true>::try_from(ux1.clone()).unwrap();
        // Unsigned N, LASTS=0 -> Signed N-X+1
        assert_eq!([31, 32, 33, 34, 35, 36, 0], *ix2.indexes);
        // Unsigned N, LASTS=0 -> Signed N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U6, true>::try_from(ux1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, true>::try_from(ux1.clone()).map_err(|x| x.to_string())
        );

        let ix1 = IntExprNode::<isize, U8, true>::from(IntExprNode::<isize, U6, false>::variable(
            ec.clone(),
        ));
        // Signed N, LASTS=0 -> Unsigned N-X
        let x2 = IntExprNode::<isize, U6, false>::try_from(ix1.clone()).unwrap();
        assert_eq!([37, 38, 39, 40, 41, 42], *x2.indexes);
        // Signed N, LASTS=0 -> Unsigned N-X-1
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        // Signed N, LASTS=0 -> Signed N-X+1
        let ix2 = IntExprNode::<isize, U7, true>::try_from(ix1.clone()).unwrap();
        assert_eq!([37, 38, 39, 40, 41, 42, 0], *ix2.indexes);
        // Signed N, LASTS=0 -> Signed N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U6, true>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, true>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );

        // constvar - this same var for all LASTS bits
        let ix1 = IntExprNode::<isize, U8, true>::from(IntExprNode::<isize, U6, true>::variable(
            ec.clone(),
        ));
        // Signed N, LASTS=constvar -> Unsigned N-X
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U6, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        // Signed N, LASTS=constvar -> Unsigned N-X+1
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U7, false>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        let ix2 = IntExprNode::<isize, U6, true>::try_from(ix1.clone()).unwrap();
        // Signed N, LASTS=constvar -> Signed N-X
        assert_eq!([43, 44, 45, 46, 47, 48], *ix2.indexes);
        // Signed N, LASTS=constvar -> Signed N-X-1
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U5, true>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
        assert_eq!(
            Err("Bit overflow".to_string()),
            IntExprNode::<isize, U4, true>::try_from(ix1.clone()).map_err(|x| x.to_string())
        );
    }

    #[test]
    fn test_int_ite() {
        let ec = ExprCreator::new();
        let c1 = BoolExprNode::<isize>::variable(ec.clone());
        let x1 = IntExprNode::<isize, U7, false>::variable(ec.clone());
        let x2 = IntExprNode::<isize, U7, false>::variable(ec.clone());
        let res = int_ite(c1, x1, x2);

        let exp_ec = ExprCreator::new();
        let c1 = BoolExprNode::<isize>::variable(exp_ec.clone());
        let x1 = IntExprNode::<isize, U7, false>::variable(exp_ec.clone());
        let x2 = IntExprNode::<isize, U7, false>::variable(exp_ec.clone());
        let exp =
            (IntExprNode::filled_expr(c1.clone()) & x1) | (IntExprNode::filled_expr(!c1) & x2);

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_int_table() {
        let ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U5, false>::variable(ec.clone());
        let values = (0..(1 << 5))
            .into_iter()
            .map(|_| IntExprNode::<isize, U10, false>::variable(ec.clone()))
            .collect::<Vec<_>>();
        let res = int_table(idx, values);

        let exp_ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U5, false>::variable(exp_ec.clone());
        let values = (0..(1 << 5))
            .into_iter()
            .map(|_| IntExprNode::<isize, U10, false>::variable(exp_ec.clone()))
            .collect::<Vec<_>>();

        let mut selects0 = vec![];
        for i in 0..16 {
            selects0.push(int_ite(
                idx.bit(0),
                values[(i << 1) + 1].clone(),
                values[i << 1].clone(),
            ));
        }
        let mut selects1 = vec![];
        for i in 0..8 {
            selects1.push(int_ite(
                idx.bit(1),
                selects0[(i << 1) + 1].clone(),
                selects0[i << 1].clone(),
            ));
        }
        let mut selects2 = vec![];
        for i in 0..4 {
            selects2.push(int_ite(
                idx.bit(2),
                selects1[(i << 1) + 1].clone(),
                selects1[i << 1].clone(),
            ));
        }
        let mut selects3 = vec![];
        for i in 0..2 {
            selects3.push(int_ite(
                idx.bit(3),
                selects2[(i << 1) + 1].clone(),
                selects2[i << 1].clone(),
            ));
        }
        let exp = int_ite(idx.bit(4), selects3[1].clone(), selects3[0].clone());

        assert_eq!(exp.indexes.as_slice(), res.indexes.as_slice());
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_int_booltable() {
        let ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U5, false>::variable(ec.clone());
        let values = (0..(1 << 5))
            .into_iter()
            .map(|_| BoolExprNode::<isize>::variable(ec.clone()))
            .collect::<Vec<_>>();
        let res = int_booltable(idx, values);

        let exp_ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U5, false>::variable(exp_ec.clone());
        let values = (0..(1 << 5))
            .into_iter()
            .map(|_| BoolExprNode::<isize>::variable(exp_ec.clone()))
            .collect::<Vec<_>>();

        let mut selects0 = vec![];
        for i in 0..16 {
            selects0.push(bool_ite(
                idx.bit(0),
                values[(i << 1) + 1].clone(),
                values[i << 1].clone(),
            ));
        }
        let mut selects1 = vec![];
        for i in 0..8 {
            selects1.push(bool_ite(
                idx.bit(1),
                selects0[(i << 1) + 1].clone(),
                selects0[i << 1].clone(),
            ));
        }
        let mut selects2 = vec![];
        for i in 0..4 {
            selects2.push(bool_ite(
                idx.bit(2),
                selects1[(i << 1) + 1].clone(),
                selects1[i << 1].clone(),
            ));
        }
        let mut selects3 = vec![];
        for i in 0..2 {
            selects3.push(bool_ite(
                idx.bit(3),
                selects2[(i << 1) + 1].clone(),
                selects2[i << 1].clone(),
            ));
        }
        let exp = bool_ite(idx.bit(4), selects3[1].clone(), selects3[0].clone());

        assert_eq!(exp.index, res.index);
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_int_demux() {
        let ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U1, false>::variable(ec.clone());
        let value = IntExprNode::<isize, U10, false>::variable(ec.clone());
        let res = int_demux(idx, value);

        let exp_ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U1, false>::variable(exp_ec.clone());
        let value = IntExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let exp = vec![
            value.clone() & IntExprNode::filled_expr(!idx.bit(0)),
            value.clone() & IntExprNode::filled_expr(idx.bit(0)),
        ];

        assert_eq!(
            exp.into_iter().map(|x| x.indexes).collect::<Vec<_>>(),
            res.into_iter().map(|x| x.indexes).collect::<Vec<_>>()
        );
        assert_eq!(*exp_ec.borrow(), *ec.borrow());

        let ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U4, false>::variable(ec.clone());
        let value = IntExprNode::<isize, U10, false>::variable(ec.clone());
        let res = int_demux(idx, value);

        let exp_ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U4, false>::variable(exp_ec.clone());
        let value = IntExprNode::<isize, U10, false>::variable(exp_ec.clone());
        let stage0 = vec![!idx.bit(3), idx.bit(3)];
        let stage1 = stage0
            .iter()
            .map(|x| [x.clone() & !idx.bit(2), x.clone() & idx.bit(2)])
            .flatten()
            .collect::<Vec<_>>();
        let stage2 = stage1
            .iter()
            .map(|x| [x.clone() & !idx.bit(1), x.clone() & idx.bit(1)])
            .flatten()
            .collect::<Vec<_>>();
        let stage3 = stage2
            .iter()
            .map(|x| [x.clone() & !idx.bit(0), x.clone() & idx.bit(0)])
            .flatten()
            .collect::<Vec<_>>();
        let exp = stage3
            .into_iter()
            .map(|x| value.clone() & IntExprNode::filled_expr(x.clone()))
            .collect::<Vec<_>>();

        assert_eq!(
            exp.into_iter().map(|x| x.indexes).collect::<Vec<_>>(),
            res.into_iter().map(|x| x.indexes).collect::<Vec<_>>()
        );
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }

    #[test]
    fn test_int_booldemux() {
        let ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U1, false>::variable(ec.clone());
        let value = BoolExprNode::<isize>::variable(ec.clone());
        let res = int_booldemux(idx, value);

        let exp_ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U1, false>::variable(exp_ec.clone());
        let value = BoolExprNode::<isize>::variable(exp_ec.clone());
        let exp = vec![value.clone() & !idx.bit(0), value.clone() & idx.bit(0)];

        assert_eq!(
            exp.into_iter().map(|x| x.index).collect::<Vec<_>>(),
            res.into_iter().map(|x| x.index).collect::<Vec<_>>()
        );
        assert_eq!(*exp_ec.borrow(), *ec.borrow());

        let ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U4, false>::variable(ec.clone());
        let value = BoolExprNode::<isize>::variable(ec.clone());
        let res = int_booldemux(idx, value);

        let exp_ec = ExprCreator::new();
        let idx = IntExprNode::<isize, U4, false>::variable(exp_ec.clone());
        let value = BoolExprNode::<isize>::variable(exp_ec.clone());
        let stage0 = vec![!idx.bit(3), idx.bit(3)];
        let stage1 = stage0
            .iter()
            .map(|x| [x.clone() & !idx.bit(2), x.clone() & idx.bit(2)])
            .flatten()
            .collect::<Vec<_>>();
        let stage2 = stage1
            .iter()
            .map(|x| [x.clone() & !idx.bit(1), x.clone() & idx.bit(1)])
            .flatten()
            .collect::<Vec<_>>();
        let stage3 = stage2
            .iter()
            .map(|x| [x.clone() & !idx.bit(0), x.clone() & idx.bit(0)])
            .flatten()
            .collect::<Vec<_>>();
        let exp = stage3
            .into_iter()
            .map(|x| value.clone() & x.clone())
            .collect::<Vec<_>>();

        assert_eq!(
            exp.into_iter().map(|x| x.index).collect::<Vec<_>>(),
            res.into_iter().map(|x| x.index).collect::<Vec<_>>()
        );
        assert_eq!(*exp_ec.borrow(), *ec.borrow());
    }
}
