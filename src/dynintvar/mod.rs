// dynintexpr.rs - dynamic integer expression structures.

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module to generate CNF clauses from dynamic integer expressions better than 'dynintexpr'.
//!
//! The module to generate CNF clauses from integer expressions better than `dynintexpr` module.
//! It offers same functionality as `intexpr`, reference support, immediates handling,
//! simpler conversion from integers, improved concatenation,
//! standard binary arithmetic operators overloading.
//! To write some formula `boolvar::call16`, `boolvar::call32` or `boolvar::callsys` should be
//! used to call routine that generates formula by using this module.
//!
//! Two generic parameters determines type of DynIntVar.
//! The first T parameter is just variable literal type - it can be omitted.
//! The second parameter is sign - true if signed integer or false if unsigned integer.
//! Type of DynIntExprNode can be written in form: `DynIntVar<i32, false>` -
//! DynIntVar for unsigned integer with 32-bit variable literals.
//!
//! You can use `IDynExprNode` or `UDynExprNode` to omit second parameter.
//! IMPORTANT: About overloading standard arithmetic operators. Any operations done in modular
//! arithmetic without checking carry, overflow and underflow. Therefore DynIntVar type should be
//! treat as modular arithmetic type.
//!
//! About usage of immediates with `DynIntVar`. it easier than in `DynIntExprNode`. Regardless
//! what is length of integer, any conversion from integer with same signess will be done
//! automatically. It just possible to write: `a + 12u8` and `a` can have any length.
//! If conversion fails then program panicked.
//!
//! The simple example of usage:
//! ```
//! use cnfgen::boolvar::*;
//! use cnfgen::dynintvar::*;
//! use cnfgen::writer::{CNFError, CNFWriter};
//! use std::io;
//! fn write_diophantine_equation() -> Result<(), CNFError> {
//!     let formula: BoolVar32 = call32(|| {
//!         // define variables - signed 32-bit wide.
//!         let x = IDynVar32::var(32);
//!         let y = IDynVar32::var(32);
//!         let z = IDynVar32::var(32);
//!         // define equation: x^2 + y^2 - 77*z^2 = 0
//!         let powx = (&x).fullmul(&x);  // x^2
//!         let powy = (&y).fullmul(&y);  // y^2
//!         let powz = (&z).fullmul(&z);  // z^2
//!         // We use cond_mul to get product and required condition to avoid overflow.
//!         let (prod, cond0) = powz.cond_mul(77i64);
//!         // Similary, we use conditional addition and conditional subtraction.
//!         let (sum1, cond1) = powx.cond_add(powy);
//!         let (diff2, cond2) = sum1.cond_sub(prod);
//!         // define final formula with required conditions.
//!         diff2.equal(0) & cond0 & cond1 & cond2
//!     });
//!     // write CNF to stdout.
//!     formula.write(&mut CNFWriter::new(io::stdout()))
//! }
//! ```

use std::cmp;
use std::collections::HashMap;
use std::fmt::Debug;
use std::ops::Neg;

use generic_array::*;

use crate::boolexpr::BoolExprNode;
use crate::boolvar::{BoolVar, EXPR_CREATOR_16, EXPR_CREATOR_32, EXPR_CREATOR_SYS};
pub use crate::dynintexpr::TryFromNSized;
use crate::dynintexpr::{DynIntExprNode, TryIntConstantN};
pub use crate::intexpr::{
    BitVal, DivMod, ExtraOps, FullMul, IntCondAdd, IntCondMul, IntCondNeg, IntCondShl, IntCondShr,
    IntCondSub, IntEqual, IntError, IntExprNode, IntModAdd, IntModAddAssign, IntModMul,
    IntModMulAssign, IntModNeg, IntModSub, IntModSubAssign, IntOrd, IntRol, IntRor,
};
use crate::intvar::IntVar;
use crate::writer::{Literal, VarLit};
use crate::{impl_int_ipty, impl_int_upty};

use crate::dynintexpr;

pub mod arith;
pub use arith::*;

/// The main structure that represents integer expression, subexpression or integer value.
///
/// It provides same operations as IntExprNode but they are easier to use
/// thanks simpler and easier to use interface that allow references and implements
/// standard arithmetic operators like addition, subtraction but with modular arithmetic rules.
/// Simple examples:
///
/// * `((x1 << x2) + x3).equal(x3)`
/// * `x1.fullmul(x1) + x2.fullmul(x2)`
///
/// The size of DynIntVar can be determined at runtime.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DynIntVar<T: VarLit + Debug, const SIGN: bool>(DynIntExprNode<T, SIGN>);

impl<T: VarLit + Debug, const SIGN: bool> From<DynIntVar<T, SIGN>> for DynIntExprNode<T, SIGN> {
    fn from(t: DynIntVar<T, SIGN>) -> Self {
        t.0
    }
}

impl<T, const SIGN: bool> From<DynIntExprNode<T, SIGN>> for DynIntVar<T, SIGN>
where
    T: VarLit + Debug,
{
    fn from(t: DynIntExprNode<T, SIGN>) -> Self {
        Self(t)
    }
}

impl<T, const SIGN: bool> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// SIGN of integer. It can be false - unsigned, or true - signed.
    pub const SIGN: bool = SIGN;
}

macro_rules! impl_create_var {
    ($t:ident, $creator:ident) => {
        impl<const SIGN: bool> DynIntVar<$t, SIGN> {
            pub fn var(n: usize) -> Self {
                $creator.with_borrow(|ec| {
                    Self(DynIntExprNode::<$t, SIGN>::variable(ec.clone().unwrap(), n))
                })
            }

            pub fn filled_lit(n: usize, v: impl Into<Literal<$t>>) -> Self {
                $creator.with_borrow(|ec| {
                    Self(DynIntExprNode::<$t, SIGN>::filled(
                        ec.clone().unwrap(),
                        n,
                        v,
                    ))
                })
            }
        }
    };
}

impl_create_var!(i16, EXPR_CREATOR_16);
impl_create_var!(i32, EXPR_CREATOR_32);
impl_create_var!(isize, EXPR_CREATOR_SYS);

impl<T, const SIGN: bool> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer from boolean expressions. An argument is object convertible into
    /// iterator of `BoolExprNode`.
    pub fn from_iter<ITP: Into<BoolVar<T>>>(iter: impl IntoIterator<Item = ITP>) -> Self {
        Self(DynIntExprNode::from_boolexprs(
            iter.into_iter().map(|x| BoolExprNode::from(x.into())),
        ))
    }

    pub fn filled(n: usize, v: impl Into<BoolVar<T>>) -> Self {
        Self(DynIntExprNode::filled_expr(n, BoolExprNode::from(v.into())))
    }

    /// Casts integer into unsigned integer.
    pub fn as_unsigned(self) -> DynIntVar<T, false> {
        DynIntVar::<T, false>::from(self.0.as_unsigned())
    }

    /// Casts integer into signed integer.
    pub fn as_signed(self) -> DynIntVar<T, true> {
        DynIntVar::<T, true>::from(self.0.as_signed())
    }

    /// Returns length - number of bits.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns true if length is zero - number of bits is zero.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<T> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    pub fn to_dynint1(self) -> DynIntVar<T, false> {
        DynIntVar::filled(1, self)
    }
}

impl<T> DynIntVar<T, false>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Creates integer that contains `n` bits starting from `start`.
    pub fn subvalue(&self, start: usize, n: usize) -> Self {
        Self(self.0.subvalue(start, n))
    }

    /// Creates integers that contains `n1`, `n2`, ... bits starting from `start`.
    pub fn subvalues(&self, start: usize, ns: impl IntoIterator<Item = usize>) -> Vec<Self> {
        let mut startx = start;
        let mut out = vec![];
        for n in ns.into_iter() {
            out.push(self.subvalue(startx, n));
            startx += n;
        }
        out
    }

    /// Creates integer that contains selected bits. List of bits given in
    /// object that can be converted into iterator of indexes.
    pub fn select_bits(&self, iter: impl IntoIterator<Item = usize>) -> Self {
        Self(self.0.select_bits(iter))
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn concat(self, rest: Self) -> Self {
        Self(self.0.concat(rest.into()))
    }

    /// Creates integer of concatenation of self and `rest`.
    pub fn cat(self, rest: Self) -> Self {
        Self(self.0.concat(rest.into()))
    }

    /// Creates integer of concatenation of iterator
    pub fn concat_iter(iter: impl IntoIterator<Item = Self>) -> Self {
        Self::from_iter(
            iter.into_iter()
                .map(|x| {
                    let v = x.iter().collect::<Vec<_>>();
                    v.into_iter()
                })
                .flatten(),
        )
    }

    /// Creates integer of concatenation of iterator
    pub fn cat_iter(iter: impl IntoIterator<Item = Self>) -> Self {
        Self::concat_iter(iter)
    }

    /// Splits integer into two parts: the first with `k` bits and second with rest of bits.
    pub fn split(self, k: usize) -> (Self, Self) {
        let (s1, s2) = self.0.split(k);
        (Self(s1), Self(s2))
    }
}

impl<T: VarLit> TryFromNSized<DynIntVar<T, false>> for DynIntVar<T, false> {
    type Error = IntError;

    fn try_from_n(input: DynIntVar<T, false>, n: usize) -> Result<Self, IntError> {
        TryFromNSized::try_from_n(input.0, n).map(|x| Self(x))
    }
}

impl<T: VarLit> TryFromNSized<DynIntVar<T, true>> for DynIntVar<T, false> {
    type Error = IntError;

    fn try_from_n(input: DynIntVar<T, true>, n: usize) -> Result<Self, IntError> {
        TryFromNSized::try_from_n(input.0, n).map(|x| Self(x))
    }
}

impl<T: VarLit> TryFromNSized<DynIntVar<T, false>> for DynIntVar<T, true> {
    type Error = IntError;

    fn try_from_n(input: DynIntVar<T, false>, n: usize) -> Result<Self, IntError> {
        TryFromNSized::try_from_n(input.0, n).map(|x| Self(x))
    }
}

impl<T: VarLit> TryFromNSized<DynIntVar<T, true>> for DynIntVar<T, true> {
    type Error = IntError;

    fn try_from_n(input: DynIntVar<T, true>, n: usize) -> Result<Self, IntError> {
        TryFromNSized::try_from_n(input.0, n).map(|x| Self(x))
    }
}

impl<T, N, const SIGN: bool> From<IntVar<T, N, SIGN>> for DynIntVar<T, SIGN>
where
    T: VarLit,
    N: ArrayLength<usize>,
{
    fn from(v: IntVar<T, N, SIGN>) -> Self {
        Self(DynIntExprNode::from(IntExprNode::from(v)))
    }
}

// integer conversion

pub trait FromNSized<T>: Sized {
    /// Convert from input. `n` is number of bits of destination.
    fn from_n(input: T, n: usize) -> Self;
}

macro_rules! impl_int_conv {
    ($t:ident, $creator:ident) => {
        macro_rules! impl_int_from_u_n {
            ($pty:ty) => {
                impl FromNSized<$pty> for DynIntVar<$t, false> {
                    fn from_n(v: $pty, n: usize) -> Self {
                        $creator.with_borrow(|ec| {
                            DynIntExprNode::<$t, false>::try_constant_n(ec.clone().unwrap(), n, v)
                                .map(|x| Self(x))
                                .unwrap()
                        })
                    }
                }
            };
        }

        impl_int_upty!(impl_int_from_u_n);

        macro_rules! impl_int_from_i_n {
            ($pty:ty) => {
                impl FromNSized<$pty> for DynIntVar<$t, true> {
                    fn from_n(v: $pty, n: usize) -> Self {
                        $creator.with_borrow(|ec| {
                            DynIntExprNode::<$t, true>::try_constant_n(ec.clone().unwrap(), n, v)
                                .map(|x| Self(x))
                                .unwrap()
                        })
                    }
                }
            };
        }

        impl_int_ipty!(impl_int_from_i_n);
    };
}

impl_int_conv!(i16, EXPR_CREATOR_16);
impl_int_conv!(i32, EXPR_CREATOR_32);
impl_int_conv!(isize, EXPR_CREATOR_SYS);

/// Allow to create constant sized from self
pub trait SelfConstant<T>: Sized {
    fn constant(&self, v: T) -> Self;
}

macro_rules! impl_int_conv_self {
    ($t:ident, $creator:ident) => {
        macro_rules! impl_int_uconstant_n {
            ($pty:ty) => {
                impl SelfConstant<$pty> for DynIntVar<$t, false> {
                    fn constant(&self, v: $pty) -> Self {
                        let n = self.bitnum();
                        $creator.with_borrow(|ec| {
                            DynIntExprNode::<$t, false>::try_constant_n(ec.clone().unwrap(), n, v)
                                .map(|x| Self(x))
                                .unwrap()
                        })
                    }
                }
            };
        }

        impl_int_upty!(impl_int_uconstant_n);

        macro_rules! impl_int_iconstant_n {
            ($pty:ty) => {
                impl SelfConstant<$pty> for DynIntVar<$t, true> {
                    fn constant(&self, v: $pty) -> Self {
                        let n = self.bitnum();
                        $creator.with_borrow(|ec| {
                            DynIntExprNode::<$t, true>::try_constant_n(ec.clone().unwrap(), n, v)
                                .map(|x| Self(x))
                                .unwrap()
                        })
                    }
                }
            };
        }

        impl_int_ipty!(impl_int_iconstant_n);
    };
}

impl_int_conv_self!(i16, EXPR_CREATOR_16);
impl_int_conv_self!(i32, EXPR_CREATOR_32);
impl_int_conv_self!(isize, EXPR_CREATOR_SYS);

impl<T: VarLit, const SIGN: bool> FromNSized<BoolVar<T>> for DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    /// Put boolean as first bit of integer.
    fn from_n(v: BoolVar<T>, n: usize) -> Self {
        Self(DynIntExprNode::<T, SIGN>::try_from_n(BoolExprNode::<T>::from(v), n).unwrap())
    }
}

impl<'a, T, const SIGN: bool> BitVal for &'a DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolVar<T>;

    fn bitnum(self) -> usize {
        self.0.bitnum()
    }

    fn bit(self, x: usize) -> Self::Output {
        BoolVar::from(self.0.bit(x))
    }
}

// IntEqual

impl<T, const SIGN: bool> IntEqual for DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.equal(rhs.0))
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.nequal(rhs.0))
    }
}

impl<T, const SIGN: bool> IntEqual<DynIntVar<T, SIGN>> for &DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: DynIntVar<T, SIGN>) -> Self::Output {
        BoolVar::from(self.0.clone().equal(rhs.0))
    }

    fn nequal(self, rhs: DynIntVar<T, SIGN>) -> Self::Output {
        BoolVar::from(self.0.clone().nequal(rhs.0))
    }
}

impl<T, const SIGN: bool> IntEqual<&DynIntVar<T, SIGN>> for DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: &DynIntVar<T, SIGN>) -> Self::Output {
        BoolVar::from(self.0.equal(rhs.0.clone()))
    }

    fn nequal(self, rhs: &DynIntVar<T, SIGN>) -> Self::Output {
        BoolVar::from(self.0.nequal(rhs.0.clone()))
    }
}

impl<T, const SIGN: bool> IntEqual for &DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolVar<T>;

    fn equal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.clone().equal(rhs.0.clone()))
    }

    fn nequal(self, rhs: Self) -> Self::Output {
        BoolVar::from(self.0.clone().nequal(rhs.0.clone()))
    }
}

macro_rules! int_equal_uint_x_sign {
    ($pty:ty, $sign:expr) => {
        impl<T> IntEqual<$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: $pty) -> Self::Output {
                let r = self.constant(rhs);
                self.equal(r)
            }

            fn nequal(self, rhs: $pty) -> Self::Output {
                let r = self.constant(rhs);
                self.nequal(r)
            }
        }
        impl<T> IntEqual<&$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: &$pty) -> Self::Output {
                let r = self.constant(*rhs);
                self.equal(r)
            }

            fn nequal(self, rhs: &$pty) -> Self::Output {
                let r = self.constant(*rhs);
                self.nequal(r)
            }
        }
        impl<T> IntEqual<$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: $pty) -> Self::Output {
                self.equal(self.constant(rhs))
            }

            fn nequal(self, rhs: $pty) -> Self::Output {
                self.nequal(self.constant(rhs))
            }
        }
        impl<T> IntEqual<&$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: &$pty) -> Self::Output {
                self.equal(self.constant(*rhs))
            }

            fn nequal(self, rhs: &$pty) -> Self::Output {
                self.nequal(self.constant(*rhs))
            }
        }

        impl<T> IntEqual<DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self).equal(rhs)
            }

            fn nequal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self).nequal(rhs)
            }
        }
        impl<T> IntEqual<&DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self.clone()).equal(rhs)
            }

            fn nequal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self.clone()).nequal(rhs)
            }
        }
        impl<T> IntEqual<DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).equal(rhs)
            }

            fn nequal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).nequal(rhs)
            }
        }
        impl<T> IntEqual<&DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn equal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).equal(rhs)
            }

            fn nequal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).nequal(rhs)
            }
        }
    };
}

macro_rules! int_equal_uint_x_unsigned {
    ($pty:ty) => {
        int_equal_uint_x_sign!($pty, false);
    };
}

impl_int_upty!(int_equal_uint_x_unsigned);

macro_rules! int_equal_uint_x_signed {
    ($pty:ty) => {
        int_equal_uint_x_sign!($pty, true);
    };
}

impl_int_ipty!(int_equal_uint_x_signed);

// IntOrd

macro_rules! impl_selfxint_ord {
    ($sign:expr) => {
        impl<T> IntOrd for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.less_than(rhs.0))
            }

            fn less_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.less_equal(rhs.0))
            }

            fn greater_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.greater_than(rhs.0))
            }

            fn greater_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.greater_equal(rhs.0))
            }
        }

        impl<T> IntOrd<DynIntVar<T, $sign>> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().less_than(rhs.0))
            }

            fn less_equal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().less_equal(rhs.0))
            }

            fn greater_than(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().greater_than(rhs.0))
            }

            fn greater_equal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                BoolVar::from(self.0.clone().greater_equal(rhs.0))
            }
        }

        impl<T> IntOrd<&DynIntVar<T, $sign>> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                BoolVar::from(self.0.less_than(rhs.0.clone()))
            }

            fn less_equal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                BoolVar::from(self.0.less_equal(rhs.0.clone()))
            }

            fn greater_than(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                BoolVar::from(self.0.greater_than(rhs.0.clone()))
            }

            fn greater_equal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                BoolVar::from(self.0.greater_equal(rhs.0.clone()))
            }
        }

        impl<T> IntOrd for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().less_than(rhs.0.clone()))
            }

            fn less_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().less_equal(rhs.0.clone()))
            }

            fn greater_than(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().greater_than(rhs.0.clone()))
            }

            fn greater_equal(self, rhs: Self) -> Self::Output {
                BoolVar::from(self.0.clone().greater_equal(rhs.0.clone()))
            }
        }
    };
}

impl_selfxint_ord!(false);
impl_selfxint_ord!(true);

macro_rules! int_ord_uint_x_sign {
    ($pty:ty, $sign:expr) => {
        impl<T> IntOrd<$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: $pty) -> Self::Output {
                let r = self.constant(rhs);
                self.less_than(r)
            }

            fn less_equal(self, rhs: $pty) -> Self::Output {
                let r = self.constant(rhs);
                self.less_equal(r)
            }

            fn greater_than(self, rhs: $pty) -> Self::Output {
                let r = self.constant(rhs);
                self.greater_than(r)
            }

            fn greater_equal(self, rhs: $pty) -> Self::Output {
                let r = self.constant(rhs);
                self.greater_equal(r)
            }
        }
        impl<T> IntOrd<&$pty> for DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &$pty) -> Self::Output {
                let r = self.constant(*rhs);
                self.less_than(r)
            }

            fn less_equal(self, rhs: &$pty) -> Self::Output {
                let r = self.constant(*rhs);
                self.less_equal(r)
            }

            fn greater_than(self, rhs: &$pty) -> Self::Output {
                let r = self.constant(*rhs);
                self.greater_than(r)
            }

            fn greater_equal(self, rhs: &$pty) -> Self::Output {
                let r = self.constant(*rhs);
                self.greater_equal(r)
            }
        }
        impl<T> IntOrd<$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: $pty) -> Self::Output {
                self.less_than(self.constant(rhs))
            }

            fn less_equal(self, rhs: $pty) -> Self::Output {
                self.less_equal(self.constant(rhs))
            }

            fn greater_than(self, rhs: $pty) -> Self::Output {
                self.greater_than(self.constant(rhs))
            }

            fn greater_equal(self, rhs: $pty) -> Self::Output {
                self.greater_equal(self.constant(rhs))
            }
        }
        impl<T> IntOrd<&$pty> for &DynIntVar<T, $sign>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &$pty) -> Self::Output {
                self.less_than(self.constant(*rhs))
            }

            fn less_equal(self, rhs: &$pty) -> Self::Output {
                self.less_equal(self.constant(*rhs))
            }

            fn greater_than(self, rhs: &$pty) -> Self::Output {
                self.greater_than(self.constant(*rhs))
            }

            fn greater_equal(self, rhs: &$pty) -> Self::Output {
                self.greater_equal(self.constant(*rhs))
            }
        }

        impl<T> IntOrd<DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self).less_than(rhs)
            }

            fn less_equal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self).less_equal(rhs)
            }

            fn greater_than(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self).greater_than(rhs)
            }

            fn greater_equal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self).greater_equal(rhs)
            }
        }
        impl<T> IntOrd<&DynIntVar<T, $sign>> for $pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self.clone()).less_than(rhs)
            }

            fn less_equal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self.clone()).less_equal(rhs)
            }

            fn greater_than(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self.clone()).greater_than(rhs)
            }

            fn greater_equal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(self.clone()).greater_equal(rhs)
            }
        }
        impl<T> IntOrd<DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).less_than(rhs)
            }

            fn less_equal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).less_equal(rhs)
            }

            fn greater_than(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).greater_than(rhs)
            }

            fn greater_equal(self, rhs: DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).greater_equal(rhs)
            }
        }
        impl<T> IntOrd<&DynIntVar<T, $sign>> for &$pty
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
            DynIntVar<T, $sign>: SelfConstant<$pty>,
        {
            type Output = BoolVar<T>;

            fn less_than(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).less_than(rhs)
            }

            fn less_equal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).less_equal(rhs)
            }

            fn greater_than(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).greater_than(rhs)
            }

            fn greater_equal(self, rhs: &DynIntVar<T, $sign>) -> Self::Output {
                rhs.constant(*self).greater_equal(rhs)
            }
        }
    };
}

macro_rules! int_ord_uint_x_unsigned {
    ($pty:ty) => {
        int_ord_uint_x_sign!($pty, false);
    };
}

impl_int_upty!(int_ord_uint_x_unsigned);

macro_rules! int_ord_uint_x_signed {
    ($pty:ty) => {
        int_ord_uint_x_sign!($pty, true);
    };
}

impl_int_ipty!(int_ord_uint_x_signed);

// int_ite, tables, demux

pub fn dynint_ite<T, const SIGN: bool>(
    c: BoolVar<T>,
    t: DynIntVar<T, SIGN>,
    e: DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    DynIntVar(dynintexpr::dynint_ite(BoolExprNode::from(c), t.0, e.0))
}

/// Returns result of the If-Then-Else (ITE) - dyninteger version - optimized version.
pub fn dynint_opt_ite<T, const SIGN: bool>(
    c: BoolVar<T>,
    t: DynIntVar<T, SIGN>,
    e: DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    DynIntVar(dynintexpr::dynint_opt_ite(c.into(), t.0, e.0))
}

pub fn dynint_ite_r<T, const SIGN: bool>(
    c: &BoolVar<T>,
    t: &DynIntVar<T, SIGN>,
    e: &DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    dynint_ite(c.clone(), t.clone(), e.clone())
}

pub fn dynint_opt_ite_r<T, const SIGN: bool>(
    c: &BoolVar<T>,
    t: &DynIntVar<T, SIGN>,
    e: &DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    dynint_opt_ite(c.clone(), t.clone(), e.clone())
}

/// Returns minimal value from two.
pub fn dynint_min<T, const SIGN: bool>(
    t: DynIntVar<T, SIGN>,
    e: DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    DynIntExprNode<T, SIGN>: IntOrd<Output = BoolExprNode<T>>,
{
    DynIntVar(dynintexpr::dynint_min(t.0, e.0))
}

/// Returns maximal value from two.
pub fn dynint_max<T, const SIGN: bool>(
    t: DynIntVar<T, SIGN>,
    e: DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    DynIntExprNode<T, SIGN>: IntOrd<Output = BoolExprNode<T>>,
{
    DynIntVar(dynintexpr::dynint_max(t.0, e.0))
}

pub fn dynint_min_r<T, const SIGN: bool>(
    t: &DynIntVar<T, SIGN>,
    e: &DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    DynIntExprNode<T, SIGN>: IntOrd<Output = BoolExprNode<T>>,
{
    dynint_min(t.clone(), e.clone())
}

pub fn dynint_max_r<T, const SIGN: bool>(
    t: &DynIntVar<T, SIGN>,
    e: &DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    DynIntExprNode<T, SIGN>: IntOrd<Output = BoolExprNode<T>>,
{
    dynint_max(t.clone(), e.clone())
}

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index.
pub fn dynint_table<T, I, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    table_iter: I,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntVar<T, SIGN>>,
{
    DynIntVar::<T, SIGN>(dynintexpr::dynint_table(
        index.into(),
        table_iter.into_iter().map(|x| x.into()),
    ))
}

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
pub fn dynint_table_partial<T, I, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    table_iter: I,
    fill: DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntVar<T, SIGN>>,
{
    let k = index.bitnum();
    let tbl = table_iter
        .into_iter()
        .take(1 << k)
        .map(|x| x.into())
        .collect::<Vec<_>>();
    let tbl_len = tbl.len();
    DynIntVar::<T, SIGN>(dynintexpr::dynint_table(
        index.into(),
        tbl.into_iter()
            .chain(std::iter::repeat(fill.into()).take((1 << k) - tbl_len)),
    ))
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index.
pub fn dynint_booltable<T, I, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    table_iter: I,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = BoolVar<T>>,
{
    BoolVar::<T>::from(dynintexpr::dynint_booltable(
        index.into(),
        table_iter.into_iter().map(|x| x.into()),
    ))
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
pub fn dynint_booltable_partial<T, I, BTP, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    table_iter: I,
    fill: BTP,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = BoolVar<T>>,
    BTP: Into<BoolVar<T>>,
{
    let k = index.bitnum();
    let tbl = table_iter
        .into_iter()
        .take(1 << k)
        .map(|x| x.into())
        .collect::<Vec<_>>();
    let tbl_len = tbl.len();
    BoolVar::<T>::from(dynintexpr::dynint_booltable(
        index.into(),
        tbl.into_iter()
            .chain(std::iter::repeat(fill.into().into()).take((1 << k) - tbl_len)),
    ))
}

/// Demultiplexer - returns list of outputs of demultiplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn dynint_demux<T, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    value: DynIntVar<T, SIGN>,
) -> Vec<DynIntVar<T, SIGN>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    dynintexpr::dynint_demux(index.into(), value.into())
        .into_iter()
        .map(|x| x.into())
        .collect::<Vec<_>>()
}

/// Demultiplexer - returns list of outputs of demultiplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn dynint_booldemux<T, BTP, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    value: BTP,
) -> Vec<BoolVar<T>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    BTP: Into<BoolVar<T>>,
{
    dynintexpr::dynint_booldemux(index.into(), value.into().into())
        .into_iter()
        .map(|x| x.into())
        .collect::<Vec<_>>()
}

// optimized version

/// Returns result of indexing of table with values. Optimized version.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index. This optimized version reduces duplicates and negations.
pub fn dynint_opt_table<T, I, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    table_iter: I,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntVar<T, SIGN>>,
{
    DynIntVar::<T, SIGN>(dynintexpr::dynint_opt_table(
        index.into(),
        table_iter.into_iter().map(|x| x.into()),
    ))
}

/// Returns result of indexing of table with values. Optimized version.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
/// This optimized version reduces duplicates and negations.
pub fn dynint_opt_table_partial<T, I, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    table_iter: I,
    fill: DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntVar<T, SIGN>>,
{
    let k = index.bitnum();
    let tbl = table_iter
        .into_iter()
        .take(1 << k)
        .map(|x| x.into())
        .collect::<Vec<_>>();
    let tbl_len = tbl.len();
    DynIntVar::<T, SIGN>(dynintexpr::dynint_opt_table(
        index.into(),
        tbl.into_iter()
            .chain(std::iter::repeat(fill.into()).take((1 << k) - tbl_len)),
    ))
}

/// Returns result of indexing of table with values. Optimized version.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index. This optimized version reduces duplicates and negations.
pub fn dynint_opt_booltable<T, I, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    table_iter: I,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = BoolVar<T>>,
{
    BoolVar::<T>::from(dynintexpr::dynint_opt_booltable(
        index.into(),
        table_iter.into_iter().map(|x| x.into()),
    ))
}

/// Returns result of indexing of table with values. Optimized version.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
/// This optimized version reduces duplicates and negations.
pub fn dynint_opt_booltable_partial<T, I, BTP, const SIGN: bool>(
    index: DynIntVar<T, SIGN>,
    table_iter: I,
    fill: BTP,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = BoolVar<T>>,
    BTP: Into<BoolVar<T>>,
{
    let k = index.bitnum();
    let tbl = table_iter
        .into_iter()
        .take(1 << k)
        .map(|x| x.into())
        .collect::<Vec<_>>();
    let tbl_len = tbl.len();
    BoolVar::<T>::from(dynintexpr::dynint_opt_booltable(
        index.into(),
        tbl.into_iter()
            .chain(std::iter::repeat(fill.into().into()).take((1 << k) - tbl_len)),
    ))
}

// version with references

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index.
pub fn dynint_table_r<T, I, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    table_iter: I,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntVar<T, SIGN>>,
{
    dynint_table(index.clone(), table_iter)
}

/// Returns result of indexing of table with values.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
pub fn dynint_table_partial_r<T, I, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    table_iter: I,
    fill: &DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntVar<T, SIGN>>,
{
    dynint_table_partial(index.clone(), table_iter, fill.clone())
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index.
pub fn dynint_booltable_r<T, I, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    table_iter: I,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = BoolVar<T>>,
{
    dynint_booltable::<T, I, SIGN>(index.clone(), table_iter)
}

/// Returns result of indexing of table with values.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
pub fn dynint_booltable_partial_r<T, I, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    table_iter: I,
    fill: &BoolVar<T>,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = BoolVar<T>>,
{
    dynint_booltable_partial::<T, I, BoolVar<T>, SIGN>(index.clone(), table_iter, fill.clone())
}

/// Demultiplexer - returns list of outputs of demultiplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn dynint_demux_r<T, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    value: &DynIntVar<T, SIGN>,
) -> Vec<DynIntVar<T, SIGN>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    dynint_demux(index.clone(), value.clone())
}

/// Demultiplexer - returns list of outputs of demultiplexer.
///
/// It performs operation: `[i==0 & v, i==1 & v, i==2 & v,....]`.
pub fn dynint_booldemux_r<T, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    value: &BoolVar<T>,
) -> Vec<BoolVar<T>>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    dynint_booldemux(index.clone(), value.clone())
}

// optimized version

/// Returns result of indexing of table with values. Optimized version.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index. This optimized version reduces duplicates and negations.
pub fn dynint_opt_table_r<T, I, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    table_iter: I,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntVar<T, SIGN>>,
{
    dynint_opt_table(index.clone(), table_iter)
}

/// Returns result of indexing of table with values. Optimized version.
///
/// It perform operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
/// This optimized version reduces duplicates and negations.
pub fn dynint_opt_table_partial_r<T, I, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    table_iter: I,
    fill: &DynIntVar<T, SIGN>,
) -> DynIntVar<T, SIGN>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = DynIntVar<T, SIGN>>,
{
    dynint_opt_table_partial(index.clone(), table_iter, fill.clone())
}

/// Returns result of indexing of table with values. Optimized version.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Length of table must be at least `1 << K` - where K is number of
/// bits of index. This optimized version reduces duplicates and negations.
pub fn dynint_opt_booltable_r<T, I, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    table_iter: I,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = BoolVar<T>>,
{
    dynint_opt_booltable::<T, I, SIGN>(index.clone(), table_iter)
}

/// Returns result of indexing of table with values. Optimized version.
///
/// It performs operation: `table[index]`, where table given as object convertible to
/// iterator of expressions. Table can have partial length. fill - is item to fill rest of
/// required space in table.
/// This optimized version reduces duplicates and negations.
pub fn dynint_opt_booltable_partial_r<T, I, const SIGN: bool>(
    index: &DynIntVar<T, SIGN>,
    table_iter: I,
    fill: &BoolVar<T>,
) -> BoolVar<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
    I: IntoIterator<Item = BoolVar<T>>,
{
    dynint_opt_booltable_partial::<T, I, BoolVar<T>, SIGN>(index.clone(), table_iter, fill.clone())
}

// types

pub type DynIntVar16<const SIGN: bool> = DynIntVar<i16, SIGN>;
pub type DynIntVar32<const SIGN: bool> = DynIntVar<i32, SIGN>;
pub type DynIntVarSys<const SIGN: bool> = DynIntVar<isize, SIGN>;

/// DynIntExprNode for unsinged integer.
pub type UDynVar16 = DynIntVar<i16, false>;
/// DynIntExprNode for singed integer.
pub type IDynVar16 = DynIntVar<i16, true>;
/// DynIntExprNode for unsinged integer.
pub type UDynVar32 = DynIntVar<i32, false>;
/// DynIntExprNode for singed integer.
pub type IDynVar32 = DynIntVar<i32, true>;
/// DynIntExprNode for unsinged integer.
pub type UDynVarSys = DynIntVar<isize, false>;
/// DynIntExprNode for singed integer.
pub type IDynVarSys = DynIntVar<isize, true>;
