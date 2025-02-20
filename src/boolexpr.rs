// boolexpr.rs - boolean expression structures.

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The module to generate CNF clauses from boolean expressions.
//!
//! This module contains traits and main structure to operate on boolean expressions:
//! `BoolExprNode`. The same `BoolExprNode` can be used in following way:
//!
//! ```
//! use cnfgen::boolexpr::*;
//! use cnfgen::writer::{CNFError, CNFWriter};
//! use std::io;
//! fn simple_expr_generator() -> Result<(), CNFError> {
//!     // define ExprCreator.
//!     let creator = ExprCreator32::new();
//!     // define variables.
//!     let x1 = BoolExprNode::variable(creator.clone());
//!     let x2 = BoolExprNode::variable(creator.clone());
//!     let x3 = BoolExprNode::variable(creator.clone());
//!     let x4 = BoolExprNode::variable(creator.clone());
//!     // define final expression: x1 => ((x2 xor x3) == (x3 and x4)).
//!     let expr = x1.clone().imp((x2 ^ x3.clone()).bequal(x3 & x4));
//!     // write CNF to stdout.
//!     expr.write(&mut CNFWriter::new(io::stdout()))
//! }
//! ```
//! Same BoolExprNode can be used to build boolean expressions by using operators.
//! Additional traits provide two extra operators: a material implication and a bolean equality.

use std::cell::RefCell;
use std::fmt::Debug;
use std::io::Write;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Neg, Not};
use std::rc::Rc;

use crate::boolexpr_creator::Node;
pub use crate::boolexpr_creator::{ExprCreator, ExprCreator32, ExprCreatorSys};

use crate::writer::{CNFError, CNFWriter, Literal, QuantSet, Quantifier, VarLit};

/// Equality operator for boolean expressions and boolean words.
///
/// It defined for BoolExprNode. Type `Rhs` can be various than Self.
/// This trait also defines `Output` that can be different than Self.
pub trait BoolEqual<Rhs = Self> {
    type Output;

    /// A method to make equality.
    fn bequal(self, rhs: Rhs) -> Self::Output;
}

/// Equality operator for bool.
impl BoolEqual for bool {
    type Output = bool;

    fn bequal(self, rhs: bool) -> Self::Output {
        self == rhs
    }
}

/// Material implication `(!self | rhs)` operator for boolean expressions and boolean words.
///
/// It defined for BoolExprNode (BoolExprNode). Type `Rhs` can be various than Self.
/// This trait also defines `Output` that can be different than Self.
pub trait BoolImpl<Rhs = Self> {
    type Output;

    fn imp(self, rhs: Rhs) -> Self::Output;
}

/// Material implication for bool.
impl BoolImpl for bool {
    type Output = bool;

    fn imp(self, rhs: bool) -> Self::Output {
        (!self) | rhs
    }
}

/// The main structure that represents expression, subexpression or literal.
///
/// It joined with the ExprCreator that holds all expressions.
/// Creation of new expression is naturally simple thanks operators. However, expression nodes
/// must be cloned before using in other expressions if they will be used more than once.
/// Simple examples:
///
/// * `(v1.clone() ^ v2) | v1`.
/// * `(v1.clone() ^ v2) | v1 & !v3`.
///
/// Expression nodes can be used with literals (Literal) or same values (boolean or integer).
/// If integer will be given then that integer will represents variable literal.
/// This implementation provides some simplification when an expression node will be joined with
/// literal or value or this same expression node (example: `v1 ^ true` => `!v1`).
///
/// The generic parameter T is variable literal type - it can be signed integer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoolExprNode<T: VarLit + Debug> {
    pub(super) creator: Rc<RefCell<ExprCreator<T>>>,
    pub(super) index: usize,
}

impl<T> BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    #[inline]
    pub(super) fn new(creator: Rc<RefCell<ExprCreator<T>>>, index: usize) -> Self {
        BoolExprNode { creator, index }
    }

    /// Creates single value as expression node.
    #[inline]
    pub fn single_value(creator: Rc<RefCell<ExprCreator<T>>>, v: bool) -> Self {
        BoolExprNode {
            creator,
            index: v.into(),
        }
    }

    /// Creates single literal as expression node.
    pub fn single(creator: Rc<RefCell<ExprCreator<T>>>, l: impl Into<Literal<T>>) -> Self {
        let index = creator.borrow_mut().single(l);
        BoolExprNode { creator, index }
    }

    // Creates new variable as expression node.
    pub fn variable(creator: Rc<RefCell<ExprCreator<T>>>) -> Self {
        let index = {
            let mut creator = creator.borrow_mut();
            let l = creator.new_variable();
            creator.single(l)
        };
        BoolExprNode { creator, index }
    }

    /// Returns literal value if exists
    pub fn value(&self) -> Option<bool> {
        if let Node::Single(Literal::Value(b)) = self.creator.borrow().nodes[self.index] {
            Some(b)
        } else {
            None
        }
    }

    /// Returns variable literal if exists
    pub fn varlit(&self) -> Option<T> {
        if let Node::Single(Literal::VarLit(l)) = self.creator.borrow().nodes[self.index] {
            Some(l)
        } else {
            None
        }
    }

    /// Writes expression to CNF.
    #[inline]
    pub fn write<W: Write>(&self, cnf: &mut CNFWriter<W>) -> Result<(), CNFError> {
        let empty: [(Quantifier, Vec<T>); 0] = [];
        self.creator.borrow().write(self.index, empty, cnf)
    }

    /// Writes quantified expression to QCNF.
    #[inline]
    pub fn write_quant<W, QL, Q>(&self, quants: QL, cnf: &mut CNFWriter<W>) -> Result<(), CNFError>
    where
        W: Write,
        QL: IntoIterator<Item = (Quantifier, Q)>,
        Q: QuantSet<T>,
    {
        self.creator.borrow().write(self.index, quants, cnf)
    }
}

/// If two expr nodes are same
pub fn boolexpr_are_same<T>(t1: &BoolExprNode<T>, t2: &BoolExprNode<T>) -> bool
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    t1.index == t2.index
}

/// If two expr nodes are negated (T2=!T1)
pub fn boolexpr_are_negated<T>(t1: &BoolExprNode<T>, t2: &BoolExprNode<T>) -> bool
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    assert_eq!(Rc::as_ptr(&t1.creator), Rc::as_ptr(&t2.creator));
    let (node1, node2) = {
        let creator = t1.creator.borrow();
        (creator.nodes[t1.index], creator.nodes[t2.index])
    };
    // optimization for v1 op -v1, or -v1 op v1.
    if node2 == Node::Negated(t1.index) || node1 == Node::Negated(t2.index) {
        return true;
    }
    if let Node::Single(lit1) = node1 {
        if let Node::Single(lit2) = node2 {
            if lit1 == !lit2 {
                return true;
            }
        }
    }
    false
}

/// An implementation Not for BoolExprNode.
impl<T> Not for BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = Self;

    fn not(self) -> Self::Output {
        let node1 = {
            let creator = self.creator.borrow();
            creator.nodes[self.index]
        };
        match node1 {
            Node::Single(l) => BoolExprNode::single(self.creator, !l),
            Node::Negated(index1) => BoolExprNode {
                creator: self.creator,
                index: index1,
            },
            _ => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    match creator.nodes[self.index] {
                        Node::Single(l) => creator.single(!l),
                        _ => creator.new_not(self.index),
                    }
                };
                BoolExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

macro_rules! new_op_impl {
    // for argeqres - if None then use self
    ($t:ident, $u:ident, $v:ident, $argeqres:expr, $argnegres:expr) => {
        /// An implementation operator for BoolExprNode.
        impl<T> $t for BoolExprNode<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = Self;

            fn $v(self, rhs: Self) -> Self::Output {
                assert_eq!(Rc::as_ptr(&self.creator), Rc::as_ptr(&rhs.creator));
                // optimization for v1 op v1.
                if self.index == rhs.index {
                    if let Some(t) = $argeqres {
                        return BoolExprNode::single_value(self.creator, t);
                    } else {
                        return self;
                    }
                }

                let (node1, node2) = {
                    let creator = self.creator.borrow();
                    (creator.nodes[self.index], creator.nodes[rhs.index])
                };
                // optimization for v1 op -v1, or -v1 op v1.
                if node2 == Node::Negated(self.index) || node1 == Node::Negated(rhs.index) {
                    if let Some(t) = $argnegres {
                        return BoolExprNode::single_value(self.creator, t);
                    } else {
                        return rhs; // for implication
                    }
                }

                if let Node::Single(lit1) = node1 {
                    if let Node::Single(lit2) = node2 {
                        self.$v(lit2)
                    } else {
                        // lit1 op node2
                        lit1.$v(rhs)
                    }
                } else {
                    if let Node::Single(lit2) = node2 {
                        self.$v(lit2)
                    } else {
                        // complicated
                        let index = self.creator.borrow_mut().$u(self.index, rhs.index);
                        BoolExprNode {
                            creator: self.creator,
                            index,
                        }
                    }
                }
            }
        }
    };
}

// for argeqres - if None then use self
new_op_impl!(BitAnd, new_and, bitand, None::<bool>, Some(false));
new_op_impl!(BitOr, new_or, bitor, None::<bool>, Some(true));
new_op_impl!(BitXor, new_xor, bitxor, Some(false), Some(true));
new_op_impl!(BoolEqual, new_equal, bequal, Some(true), Some(false));
new_op_impl!(BoolImpl, new_impl, imp, Some(true), None::<bool>);

/// An implementation BitAnd for BoolExprNode where rhs is Literal.
impl<T, U> BitAnd<U> for BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bitand(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return BoolExprNode::single(self.creator, v1 & v2);
                    } else {
                        return v1 & BoolExprNode::single(self.creator, lit2);
                    }
                } else if lit1 == lit2 {
                    return self;
                } else if lit1 == !lit2 {
                    return BoolExprNode::single_value(self.creator, false);
                }
            }
        }
        match lit2 {
            Literal::Value(false) => BoolExprNode {
                creator: self.creator,
                index: 0,
            },
            Literal::Value(true) => self,
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_and(self.index, index)
                };
                BoolExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

/// An implementation BitAnd for Literal where rhs is BoolExprNode.
impl<T> BitAnd<BoolExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bitand(self, rhs: BoolExprNode<T>) -> Self::Output {
        rhs.bitand(self)
    }
}

macro_rules! new_op_l_xn_impl {
    ($t:ty, $u: ident, $v: ident) => {
        /// An implementation operator for value where rhs is BoolExprNode.
        impl $u<BoolExprNode<$t>> for $t {
            type Output = BoolExprNode<$t>;

            fn $v(self, rhs: BoolExprNode<$t>) -> Self::Output {
                rhs.$v(Literal::from(self))
            }
        }
    };
}

macro_rules! new_all_op_l_xn_impls {
    ($u: ident, $v: ident) => {
        /// An implementation operator for boolean where rhs is BoolExprNode.
        impl<T> $u<BoolExprNode<T>> for bool
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            type Output = BoolExprNode<T>;

            fn $v(self, rhs: BoolExprNode<T>) -> Self::Output {
                rhs.$v(Literal::from(self))
            }
        }
        new_op_l_xn_impl!(i8, $u, $v);
        new_op_l_xn_impl!(i16, $u, $v);
        new_op_l_xn_impl!(i32, $u, $v);
        new_op_l_xn_impl!(i64, $u, $v);
        new_op_l_xn_impl!(isize, $u, $v);
    };
}

new_all_op_l_xn_impls!(BitAnd, bitand);

/// An implementation BitOr for BoolExprNode where rhs is Literal.
impl<T, U> BitOr<U> for BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bitor(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return BoolExprNode::single(self.creator, v1 | v2);
                    } else {
                        return v1 | BoolExprNode::single(self.creator, lit2);
                    }
                } else if lit1 == lit2 {
                    return self;
                } else if lit1 == !lit2 {
                    return BoolExprNode::single_value(self.creator, true);
                }
            }
        }
        match lit2 {
            Literal::Value(false) => self,
            Literal::Value(true) => BoolExprNode {
                creator: self.creator,
                index: 1,
            },
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_or(self.index, index)
                };
                BoolExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

/// An implementation BitOr for Literal where rhs is BoolExprNode.
impl<T: VarLit> BitOr<BoolExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bitor(self, rhs: BoolExprNode<T>) -> Self::Output {
        rhs.bitor(self)
    }
}

new_all_op_l_xn_impls!(BitOr, bitor);

/// An implementation BitXor for BoolExprNode where rhs is Literal.
impl<T, U> BitXor<U> for BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bitxor(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return BoolExprNode::single(self.creator, v1 ^ v2);
                    } else {
                        return v1 ^ BoolExprNode::single(self.creator, lit2);
                    }
                } else if lit1 == lit2 {
                    return BoolExprNode::single_value(self.creator, false);
                } else if lit1 == !lit2 {
                    return BoolExprNode::single_value(self.creator, true);
                }
            }
        }
        match lit2 {
            Literal::Value(false) => self,
            Literal::Value(true) => !self,
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_xor(self.index, index)
                };
                BoolExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

/// An implementation BitXor for Literal where rhs is BoolExprNode.
impl<T> BitXor<BoolExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bitxor(self, rhs: BoolExprNode<T>) -> Self::Output {
        rhs.bitxor(self)
    }
}

new_all_op_l_xn_impls!(BitXor, bitxor);

/// An implementation BoolEqual for BoolExprNode where rhs is Literal.
impl<T, U> BoolEqual<U> for BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bequal(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return BoolExprNode::single(self.creator, v1.bequal(v2));
                    } else {
                        return v1.bequal(BoolExprNode::single(self.creator, lit2));
                    }
                } else if lit1 == lit2 {
                    return BoolExprNode::single_value(self.creator, true);
                } else if lit1 == !lit2 {
                    return BoolExprNode::single_value(self.creator, false);
                }
            }
        }
        match lit2 {
            Literal::Value(false) => !self,
            Literal::Value(true) => self,
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_equal(self.index, index)
                };
                BoolExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

/// An implementation BoolEqual for Literal where rhs is BoolExprNode.
impl<T> BoolEqual<BoolExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn bequal(self, rhs: BoolExprNode<T>) -> Self::Output {
        rhs.bequal(self)
    }
}

new_all_op_l_xn_impls!(BoolEqual, bequal);

/// An implementation BoolImpl for BoolExprNode where rhs is Literal.
impl<T, U> BoolImpl<U> for BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    U: Into<Literal<T>>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn imp(self, rhs: U) -> Self::Output {
        let lit2 = rhs.into();
        {
            let node1 = self.creator.borrow().nodes[self.index];
            if let Node::Single(lit1) = node1 {
                if let Literal::Value(v1) = lit1 {
                    if let Literal::Value(v2) = lit2 {
                        return BoolExprNode::single(self.creator, v1.imp(v2));
                    } else {
                        return v1.imp(BoolExprNode::single(self.creator, lit2));
                    }
                } else if lit1 == lit2 {
                    return BoolExprNode::single_value(self.creator, true);
                } else if lit1 == !lit2 {
                    return BoolExprNode::single(self.creator, lit2);
                }
            }
        }
        match lit2 {
            Literal::Value(false) => !self,
            Literal::Value(true) => BoolExprNode {
                creator: self.creator,
                index: 1,
            },
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = self.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_impl(self.index, index)
                };
                BoolExprNode {
                    creator: self.creator,
                    index,
                }
            }
        }
    }
}

/// An implementation BoolImpl for Literal where rhs is BoolExprNode.
impl<T> BoolImpl<BoolExprNode<T>> for Literal<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    type Output = BoolExprNode<T>;

    fn imp(self, rhs: BoolExprNode<T>) -> Self::Output {
        let lit1 = self;
        {
            let node2 = rhs.creator.borrow().nodes[rhs.index];
            if let Node::Single(lit2) = node2 {
                if lit1 == lit2 {
                    return BoolExprNode::single_value(rhs.creator, true);
                } else if lit1 == !lit2 {
                    return BoolExprNode::single(rhs.creator, lit2);
                }
            }
        }
        match lit1 {
            Literal::Value(false) => BoolExprNode {
                creator: rhs.creator,
                index: 1,
            },
            Literal::Value(true) => rhs,
            Literal::VarLit(l) => {
                let index = {
                    let mut creator = rhs.creator.borrow_mut();
                    let index = creator.single(l);
                    creator.new_impl(index, rhs.index)
                };
                BoolExprNode {
                    creator: rhs.creator,
                    index,
                }
            }
        }
    }
}

/// An implementation BoolImpl for bool where rhs is BoolExprNode.
impl<T: VarLit + Debug> BoolImpl<BoolExprNode<T>> for bool {
    type Output = BoolExprNode<T>;

    fn imp(self, rhs: BoolExprNode<T>) -> Self::Output {
        if self {
            rhs
        } else {
            BoolExprNode {
                creator: rhs.creator,
                index: 1,
            }
        }
    }
}

macro_rules! new_impl_imp_impls {
    ($ty: ty) => {
        /// An implementation BoolImpl for value where rhs is BoolExprNode.
        impl BoolImpl<BoolExprNode<$ty>> for $ty {
            type Output = BoolExprNode<$ty>;

            fn imp(self, rhs: BoolExprNode<$ty>) -> Self::Output {
                let lit1 = Literal::from(self);
                {
                    let node2 = rhs.creator.borrow().nodes[rhs.index];
                    if let Node::Single(lit2) = node2 {
                        if lit1 == lit2 {
                            return BoolExprNode::single_value(rhs.creator, true);
                        } else if lit1 == !lit2 {
                            return BoolExprNode::single(rhs.creator, lit2);
                        }
                    }
                }
                let index = {
                    let mut creator = rhs.creator.borrow_mut();
                    let index = creator.single(self);
                    creator.new_impl(index, rhs.index)
                };
                BoolExprNode {
                    creator: rhs.creator,
                    index,
                }
            }
        }
    };
}

new_impl_imp_impls!(i8);
new_impl_imp_impls!(i16);
new_impl_imp_impls!(i32);
new_impl_imp_impls!(i64);
new_impl_imp_impls!(isize);

macro_rules! impl_op_assign {
    ($trait:ident, $op_assign:ident, $op:ident) => {
        impl<T> $trait for BoolExprNode<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $op_assign(&mut self, rhs: BoolExprNode<T>) {
                *self = self.clone().$op(rhs);
            }
        }

        impl<T, U> $trait<U> for BoolExprNode<T>
        where
            T: VarLit + Neg<Output = T> + Debug,
            U: Into<Literal<T>>,
            isize: TryFrom<T>,
            <T as TryInto<usize>>::Error: Debug,
            <T as TryFrom<usize>>::Error: Debug,
            <isize as TryFrom<T>>::Error: Debug,
        {
            fn $op_assign(&mut self, rhs: U) {
                *self = self.clone().$op(rhs);
            }
        }
    };
}

impl_op_assign!(BitAndAssign, bitand_assign, bitand);
impl_op_assign!(BitOrAssign, bitor_assign, bitor);
impl_op_assign!(BitXorAssign, bitxor_assign, bitxor);

/// Returns result of the If-Then-Else (ITE) - bitwise version.
pub fn bool_ite<C, T, E>(
    c: C,
    t: T,
    e: E,
) -> <<C as BitAnd<T>>::Output as BitOr<<<C as Not>::Output as BitAnd<E>>::Output>>::Output
where
    C: BitAnd<T> + Not + Clone,
    <C as Not>::Output: BitAnd<E>,
    <C as BitAnd<T>>::Output: BitOr<<<C as Not>::Output as BitAnd<E>>::Output>,
{
    (c.clone() & t) | ((!c) & e)
}

/// Returns result of the If-Then-Else (ITE) - bitwise version. Optimized version.
pub fn bool_opt_ite<T>(
    c: BoolExprNode<T>,
    t: BoolExprNode<T>,
    e: BoolExprNode<T>,
) -> BoolExprNode<T>
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    assert_eq!(Rc::as_ptr(&t.creator), Rc::as_ptr(&e.creator));
    // optimization for v1 op v1.
    if t.index == e.index {
        return t;
    }
    let (node1, node2) = {
        let creator = t.creator.borrow();
        (creator.nodes[t.index], creator.nodes[e.index])
    };
    // optimization for v1 op -v1, or -v1 op v1.
    if node2 == Node::Negated(t.index) || node1 == Node::Negated(e.index) {
        return e ^ c;
    }
    if let Node::Single(lit1) = node1 {
        if let Node::Single(lit2) = node2 {
            if lit1 == !lit2 {
                return e ^ c;
            }
        }
    }
    bool_ite(c, t, e)
}

/// Returns result of half adder: sum and carry.
pub fn half_adder<A, B>(a: A, b: B) -> (<A as BitXor<B>>::Output, <A as BitAnd<B>>::Output)
where
    A: BitAnd<B> + BitXor<B> + Clone,
    B: Clone,
{
    (a.clone() ^ b.clone(), a & b)
}

/// The full adder output.
pub type FullAdderOutput<A, B, C> = (
    <<A as BitXor<B>>::Output as BitXor<C>>::Output,
    <<<A as BitXor<B>>::Output as BitAnd<C>>::Output as BitOr<<A as BitAnd<B>>::Output>>::Output,
);

/// Returns result of full adder (with three arguments): sum and carry.
pub fn full_adder<A, B, C>(a: A, b: B, c: C) -> FullAdderOutput<A, B, C>
where
    A: BitAnd<B> + BitXor<B> + Clone,
    <A as BitXor<B>>::Output: BitAnd<C> + BitXor<C> + Clone,
    <<A as BitXor<B>>::Output as BitAnd<C>>::Output: BitOr<<A as BitAnd<B>>::Output>,
    B: Clone,
    C: Clone,
{
    let s0 = a.clone() ^ b.clone();
    (s0.clone() ^ c.clone(), (s0 & c) | (a & b))
}

/// Optimized full adder. Optimize boolean expression if any input is constant boolean value.
pub fn opt_full_adder<T>(
    a: BoolExprNode<T>,
    b: BoolExprNode<T>,
    c: BoolExprNode<T>,
) -> (BoolExprNode<T>, BoolExprNode<T>)
where
    T: VarLit + Neg<Output = T> + Debug,
    isize: TryFrom<T>,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
    <isize as TryFrom<T>>::Error: Debug,
{
    if a.value().is_some() {
        full_adder(b, c, a)
    } else if b.value().is_some() {
        full_adder(a, c, b)
    } else {
        full_adder(a, b, c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_node_varlit() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let xp1 = !v1.clone() & v2.clone();
        assert_eq!(v1.varlit(), Some(1));
        assert_eq!(v2.varlit(), Some(2));
        assert_eq!(xp1.varlit(), None);
    }

    #[test]
    fn test_expr_nodes() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let xp1 = !v1.clone() & v2.clone();
        let _ = xp1.clone() | !v3.clone() ^ (v1.clone() | v2.clone());
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::And(5, 3),
                    Node::Single(Literal::VarLit(-3)),
                    Node::Or(2, 3),
                    Node::Xor(8, 7),
                    Node::Or(6, 9),
                ],
                lit_to_index: vec![2, 5, 3, 0, 4, 7],
            },
            *ec.borrow()
        );
        let _ = v1.clone() ^ v2.clone().bequal(v3) | !xp1;
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::And(5, 3),
                    Node::Single(Literal::VarLit(-3)),
                    Node::Or(2, 3),
                    Node::Xor(8, 7),
                    Node::Or(6, 9),
                    Node::Equal(3, 4),
                    Node::Xor(11, 2),
                    Node::Negated(6),
                    Node::Or(12, 13),
                ],
                lit_to_index: vec![2, 5, 3, 0, 4, 7],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_1() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let v4x = ec.borrow_mut().new_variable();
        let v5x = ec.borrow_mut().new_variable();
        let _ = Literal::from(v5x)
            | (v1.clone() ^ Literal::from(true))
            | (Literal::from(true) ^ v2)
            | (v3 & Literal::from(true))
            | (Literal::from(v4x) & v1)
            | Literal::from(false);
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::Single(Literal::VarLit(5)),
                    Node::Or(5, 6),
                    Node::Single(Literal::VarLit(-2)),
                    Node::Or(7, 8),
                    Node::Or(9, 4),
                    Node::Single(Literal::VarLit(4)),
                    Node::And(2, 11),
                    Node::Or(10, 12),
                ],
                lit_to_index: vec![2, 5, 3, 8, 4, 0, 11, 0, 6, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_2() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let v4x = ec.borrow_mut().new_variable().varlit().unwrap();
        let v5x = ec.borrow_mut().new_variable().varlit().unwrap();
        let _ = v5x | (v1.clone() ^ true) | (true ^ v2) | (v3 & true) | (v4x & v1) | false;
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::Single(Literal::VarLit(5)),
                    Node::Or(5, 6),
                    Node::Single(Literal::VarLit(-2)),
                    Node::Or(7, 8),
                    Node::Or(9, 4),
                    Node::Single(Literal::VarLit(4)),
                    Node::And(2, 11),
                    Node::Or(10, 12),
                ],
                lit_to_index: vec![2, 5, 3, 8, 4, 0, 11, 0, 6, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_3() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = ec.borrow_mut().new_variable().varlit().unwrap();
        let v3 = BoolExprNode::variable(ec.clone());
        let _ = v2.bequal((!v1).bequal(Literal::from(v2).bequal(v3)));
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(-1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Equal(3, 5),
                    Node::Equal(6, 4),
                    Node::Equal(7, 5),
                ],
                lit_to_index: vec![2, 4, 5, 0, 3, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_imp_equal() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let _ = v3.clone().bequal(v1.imp(v2.bequal(v3)));
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Equal(3, 4),
                    Node::Impl(2, 5),
                    Node::Equal(6, 4),
                ],
                lit_to_index: vec![2, 0, 3, 0, 4, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_lits_imp_equal_2() {
        let ec = ExprCreator::<isize>::new();
        let _ = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let _ = v3.clone().bequal(1.imp(v2.bequal(v3)));
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Equal(3, 4),
                    Node::Impl(2, 5),
                    Node::Equal(6, 4),
                ],
                lit_to_index: vec![2, 0, 3, 0, 4, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_nodes_not_simpls() {
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let v2 = BoolExprNode::variable(ec.clone());
            let xp1 = v1.imp(v2.clone());
            let xp2 = !xp1.clone();
            let _ = xp2.clone() & v2 & !xp2.clone();
            assert_eq!(!xp2.clone(), xp1.clone());
            assert_eq!(
                ExprCreator {
                    nodes: vec![
                        Node::Single(Literal::Value(false)),
                        Node::Single(Literal::Value(true)),
                        Node::Single(Literal::VarLit(1)),
                        Node::Single(Literal::VarLit(2)),
                        Node::Impl(2, 3),
                        Node::Negated(4),
                        Node::And(5, 3),
                        Node::And(6, 4),
                    ],
                    lit_to_index: vec![2, 0, 3, 0],
                },
                *ec.borrow()
            );
        }
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let v2 = BoolExprNode::variable(ec.clone());
            let np1 = !v1.clone();
            let _ = np1.clone() & v2 & !np1.clone();
            assert_eq!(!np1.clone(), v1);
            assert_eq!(!!np1.clone(), np1);
            assert_eq!(
                ExprCreator {
                    nodes: vec![
                        Node::Single(Literal::Value(false)),
                        Node::Single(Literal::Value(true)),
                        Node::Single(Literal::VarLit(1)),
                        Node::Single(Literal::VarLit(2)),
                        Node::Single(Literal::VarLit(-1)),
                        Node::And(4, 3),
                        Node::And(5, 2),
                    ],
                    lit_to_index: vec![2, 4, 3, 0],
                },
                *ec.borrow()
            );
        }
        {
            let ec = ExprCreator::<isize>::new();
            let np1 = BoolExprNode::single(ec.clone(), true);
            let np2 = !np1.clone();
            let np3 = !np2.clone();
            assert_eq!(np2, BoolExprNode::single(ec.clone(), false));
            assert_eq!(np3, np1);
            assert_eq!(
                ExprCreator {
                    nodes: vec![
                        Node::Single(Literal::Value(false)),
                        Node::Single(Literal::Value(true)),
                    ],
                    lit_to_index: vec![],
                },
                *ec.borrow()
            );
        }
    }

    enum ExpOpResult {
        XPTrue,
        XPFalse,
        XPVar1,
        XPNotVar1,
        XPExpr,
        XPNotExpr,
    }

    use ExpOpResult::*;

    macro_rules! test_op_simpls {
        ($op:ident, $tt:expr, $v1f:expr, $fv1:expr, $v1t:expr, $tv1:expr, $nv1v1:expr, $v1nv1:expr,
         $v1v1: expr, $xpxp: expr, $nxpxp: expr, $xpnxp: expr) => {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let nv1 = !v1.clone();
            let xpfalse = BoolExprNode::single(ec.clone(), false);
            let xptrue = BoolExprNode::single(ec.clone(), true);
            let v2 = BoolExprNode::variable(ec.clone());
            let xp = v1.clone() & v2.clone();
            let nxp = !(xp.clone());

            macro_rules! select {
                ($r:tt) => {
                    match $r {
                        XPTrue => xptrue.clone(),
                        XPFalse => xpfalse.clone(),
                        XPVar1 => v1.clone(),
                        XPNotVar1 => nv1.clone(),
                        XPExpr => xp.clone(),
                        XPNotExpr => nxp.clone(),
                    }
                };
            }

            assert_eq!(xptrue.clone().$op(true), select!($tt));
            assert_eq!(true.$op(xptrue.clone()), select!($tt));
            assert_eq!(xptrue.clone().$op(Literal::from(true)), select!($tt));
            assert_eq!(Literal::from(true).$op(xptrue.clone()), select!($tt));
            assert_eq!(xptrue.clone().$op(xptrue.clone()), select!($tt));

            assert_eq!(v1.clone().$op(false), select!($v1f));
            assert_eq!(false.$op(v1.clone()), select!($fv1));
            assert_eq!(v1.clone().$op(Literal::from(false)), select!($v1f));
            assert_eq!(Literal::from(false).$op(v1.clone()), select!($fv1));
            assert_eq!(v1.clone().$op(xpfalse.clone()), select!($v1f));
            assert_eq!(xpfalse.clone().$op(v1.clone()), select!($fv1));

            assert_eq!(v1.clone().$op(true), select!($v1t));
            assert_eq!(true.$op(v1.clone()), select!($tv1));
            assert_eq!(v1.clone().$op(Literal::from(true)), select!($v1t));
            assert_eq!(Literal::from(true).$op(v1.clone()), select!($tv1));
            assert_eq!(v1.clone().$op(xptrue.clone()), select!($v1t));
            assert_eq!(xptrue.clone().$op(v1.clone()), select!($tv1));

            assert_eq!((-1).$op(v1.clone()), select!($nv1v1));
            assert_eq!(v1.clone().$op(-1), select!($v1nv1));
            assert_eq!(Literal::from(-1).$op(v1.clone()), select!($nv1v1));
            assert_eq!(v1.clone().$op(Literal::from(-1)), select!($v1nv1));
            assert_eq!(nv1.clone().$op(v1.clone()), select!($nv1v1));
            assert_eq!(v1.clone().$op(nv1.clone()), select!($v1nv1));

            assert_eq!((1).$op(v1.clone()), select!($v1v1));
            assert_eq!(v1.clone().$op(1), select!($v1v1));
            assert_eq!(Literal::from(1).$op(v1.clone()), select!($v1v1));
            assert_eq!(v1.clone().$op(Literal::from(1)), select!($v1v1));
            assert_eq!(v1.clone().$op(v1.clone()), select!($v1v1));

            assert_eq!(xp.clone().$op(xp.clone()), select!($xpxp));
            assert_eq!(nxp.clone().$op(xp.clone()), select!($nxpxp));
            assert_eq!(xp.clone().$op(nxp.clone()), select!($xpnxp));
        };
    }

    #[test]
    fn test_expr_nodes_and_simpls() {
        test_op_simpls!(
            bitand, XPTrue, XPFalse, XPFalse, XPVar1, XPVar1, XPFalse, XPFalse, XPVar1, XPExpr,
            XPFalse, XPFalse
        );
    }

    #[test]
    fn test_expr_nodes_or_simpls() {
        test_op_simpls!(
            bitor, XPTrue, XPVar1, XPVar1, XPTrue, XPTrue, XPTrue, XPTrue, XPVar1, XPExpr, XPTrue,
            XPTrue
        );
    }

    #[test]
    fn test_expr_nodes_xor_simpls() {
        test_op_simpls!(
            bitxor, XPFalse, XPVar1, XPVar1, XPNotVar1, XPNotVar1, XPTrue, XPTrue, XPFalse,
            XPFalse, XPTrue, XPTrue
        );
    }

    #[test]
    fn test_expr_nodes_equal_simpls() {
        test_op_simpls!(
            bequal, XPTrue, XPNotVar1, XPNotVar1, XPVar1, XPVar1, XPFalse, XPFalse, XPTrue, XPTrue,
            XPFalse, XPFalse
        );
    }

    #[test]
    fn test_expr_nodes_impl_simpls() {
        test_op_simpls!(
            imp, XPTrue, XPNotVar1, XPTrue, XPTrue, XPVar1, XPVar1, XPNotVar1, XPTrue, XPTrue,
            XPExpr, XPNotExpr
        );
    }

    #[test]
    fn test_expr_op_assign() {
        let ec = ExprCreator::<isize>::new();
        let mut v1 = BoolExprNode::variable(ec.clone());
        let mut v2 = BoolExprNode::variable(ec.clone());
        let mut v3 = BoolExprNode::variable(ec.clone());
        let v4 = BoolExprNode::variable(ec.clone());
        v1 &= v4.clone();
        v2 |= v4.clone();
        v3 ^= v4;
        assert_eq!(6, v1.index);
        assert_eq!(7, v2.index);
        assert_eq!(8, v3.index);
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(4)),
                    Node::And(2, 5),
                    Node::Or(3, 5),
                    Node::Xor(4, 5),
                ],
                lit_to_index: vec![2, 0, 3, 0, 4, 0, 5, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_op_assign_lit() {
        let ec = ExprCreator::<isize>::new();
        let mut v1 = BoolExprNode::variable(ec.clone());
        let mut v2 = BoolExprNode::variable(ec.clone());
        let mut v3 = BoolExprNode::variable(ec.clone());
        let v4 = BoolExprNode::variable(ec.clone()).varlit().unwrap();
        v1 &= Literal::from(v4);
        v2 |= Literal::from(v4);
        v3 ^= Literal::from(v4);
        assert_eq!(6, v1.index);
        assert_eq!(7, v2.index);
        assert_eq!(8, v3.index);
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Single(Literal::VarLit(4)),
                    Node::And(2, 5),
                    Node::Or(3, 5),
                    Node::Xor(4, 5),
                ],
                lit_to_index: vec![2, 0, 3, 0, 4, 0, 5, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_bool_ite() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let _ = bool_ite(v1, v2, v3);
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::And(2, 3),
                    Node::Single(Literal::VarLit(-1)),
                    Node::And(6, 4),
                    Node::Or(5, 7)
                ],
                lit_to_index: vec![2, 6, 3, 0, 4, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_bool_opt_ite() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let _ = bool_opt_ite(v1, v2, v3);
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::And(2, 3),
                    Node::Single(Literal::VarLit(-1)),
                    Node::And(6, 4),
                    Node::Or(5, 7)
                ],
                lit_to_index: vec![2, 6, 3, 0, 4, 0],
            },
            *ec.borrow()
        );
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        // this same T and E.
        let _ = bool_opt_ite(v1.clone(), v2.clone(), v2.clone());
        // T and negated T as E.
        let _ = bool_opt_ite(v1.clone(), v2.clone(), !v2.clone());
        // E and negated E as T.
        let _ = bool_opt_ite(v1.clone(), !v2.clone(), v2.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let xp = v2.clone() & v3.clone();
        // T and negated T as E.
        let _ = bool_opt_ite(v1.clone(), xp.clone(), !xp.clone());
        // E and negated E as T.
        let _ = bool_opt_ite(v1, !xp.clone(), xp);
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(-2)),
                    Node::Xor(4, 2),
                    Node::Xor(3, 2),
                    Node::Single(Literal::VarLit(3)),
                    Node::And(3, 7),
                    Node::Negated(8),
                    Node::Xor(9, 2),
                    Node::Negated(8),
                    Node::Xor(8, 2),
                ],
                lit_to_index: vec![2, 0, 3, 4, 7, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_half_adder() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let (s, c) = half_adder(v1, v2);
        assert_eq!(4, s.index);
        assert_eq!(5, c.index);
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Xor(2, 3),
                    Node::And(2, 3),
                ],
                lit_to_index: vec![2, 0, 3, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_full_adder() {
        let ec = ExprCreator::<isize>::new();
        let v1 = BoolExprNode::variable(ec.clone());
        let v2 = BoolExprNode::variable(ec.clone());
        let v3 = BoolExprNode::variable(ec.clone());
        let (s, c) = full_adder(v1, v2, v3);
        assert_eq!(6, s.index);
        assert_eq!(9, c.index);
        assert_eq!(
            ExprCreator {
                nodes: vec![
                    Node::Single(Literal::Value(false)),
                    Node::Single(Literal::Value(true)),
                    Node::Single(Literal::VarLit(1)),
                    Node::Single(Literal::VarLit(2)),
                    Node::Single(Literal::VarLit(3)),
                    Node::Xor(2, 3),
                    Node::Xor(5, 4),
                    Node::And(5, 4),
                    Node::And(2, 3),
                    Node::Or(7, 8),
                ],
                lit_to_index: vec![2, 0, 3, 0, 4, 0],
            },
            *ec.borrow()
        );
    }

    #[test]
    fn test_expr_opt_full_adder() {
        let exp_ec = ExprCreator {
            nodes: vec![
                Node::Single(Literal::Value(false)),
                Node::Single(Literal::Value(true)),
                Node::Single(Literal::VarLit(1)),
                Node::Single(Literal::VarLit(2)),
                Node::Xor(2, 3),
                Node::And(2, 3),
            ],
            lit_to_index: vec![2, 0, 3, 0],
        };
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let v2 = BoolExprNode::variable(ec.clone());
            let (s, c) = opt_full_adder(v1, v2, BoolExprNode::single_value(ec.clone(), false));
            assert_eq!(4, s.index);
            assert_eq!(5, c.index);
            assert_eq!(exp_ec, *ec.borrow());
        }
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let v2 = BoolExprNode::variable(ec.clone());
            let (s, c) = opt_full_adder(v1, BoolExprNode::single_value(ec.clone(), false), v2);
            assert_eq!(4, s.index);
            assert_eq!(5, c.index);
            assert_eq!(exp_ec, *ec.borrow());
        }
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let v2 = BoolExprNode::variable(ec.clone());
            let (s, c) = opt_full_adder(BoolExprNode::single_value(ec.clone(), false), v1, v2);
            assert_eq!(4, s.index);
            assert_eq!(5, c.index);
            assert_eq!(exp_ec, *ec.borrow());
        }
        let exp_ec = ExprCreator {
            nodes: vec![
                Node::Single(Literal::Value(false)),
                Node::Single(Literal::Value(true)),
                Node::Single(Literal::VarLit(1)),
                Node::Single(Literal::VarLit(2)),
                Node::Xor(2, 3),
                Node::Negated(4),
                Node::And(2, 3),
                Node::Or(4, 6),
            ],
            lit_to_index: vec![2, 0, 3, 0],
        };
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let v2 = BoolExprNode::variable(ec.clone());
            let (s, c) = opt_full_adder(v1, v2, BoolExprNode::single_value(ec.clone(), true));
            assert_eq!(5, s.index);
            assert_eq!(7, c.index);
            assert_eq!(exp_ec, *ec.borrow());
        }
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let v2 = BoolExprNode::variable(ec.clone());
            let (s, c) = opt_full_adder(v1, BoolExprNode::single_value(ec.clone(), true), v2);
            assert_eq!(5, s.index);
            assert_eq!(7, c.index);
            assert_eq!(exp_ec, *ec.borrow());
        }
        {
            let ec = ExprCreator::<isize>::new();
            let v1 = BoolExprNode::variable(ec.clone());
            let v2 = BoolExprNode::variable(ec.clone());
            let (s, c) = opt_full_adder(BoolExprNode::single_value(ec.clone(), true), v1, v2);
            assert_eq!(5, s.index);
            assert_eq!(7, c.index);
            assert_eq!(exp_ec, *ec.borrow());
        }
    }

    #[test]
    fn test_expr_node_write() {
        let ec = ExprCreator::<isize>::new();
        let mut v = vec![];
        v.push(BoolExprNode::single(ec.clone(), false));
        for _ in 0..2 {
            v.push(BoolExprNode::variable(ec.clone()));
        }
        let xp = v[1].clone() & v[2].clone();
        let mut cnf_writer = CNFWriter::new(vec![]);
        xp.write(&mut cnf_writer).unwrap();
        assert_eq!(
            "p cnf 2 2\n1 0\n2 0\n",
            String::from_utf8_lossy(cnf_writer.inner())
        );

        let mut cnf_writer = CNFWriter::new(vec![]);
        xp.write_quant(
            [(Quantifier::Exists, [1]), (Quantifier::ForAll, [2])],
            &mut cnf_writer,
        )
        .unwrap();
        assert_eq!(
            "p cnf 2 2\ne 1 0\na 2 0\n1 0\n2 0\n",
            String::from_utf8_lossy(cnf_writer.inner())
        );
    }
}

#[cfg(test)]
pub(crate) mod test_utils {
    use super::*;

    pub(crate) fn alloc_boolvars(
        ec: Rc<RefCell<ExprCreator<isize>>>,
        var_count: isize,
    ) -> Vec<BoolExprNode<isize>> {
        (0..var_count)
            .into_iter()
            .map(|_| BoolExprNode::variable(ec.clone()))
            .collect::<Vec<_>>()
    }
}
