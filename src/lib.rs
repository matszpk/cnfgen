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

#![cfg_attr(docsrs, feature(doc_cfg))]
//! The library to generate CNF (Conjuctive Normal Form) formulaes.

pub mod prelude {
    pub use crate::BitMask;
    pub use crate::BitVal;
    pub use crate::BoolEqual;
    pub use crate::BoolExprNode;
    pub use crate::BoolImpl;
    pub use crate::CNFError;
    pub use crate::CNFWriter;
    pub use crate::Clause;
    pub use crate::DivMod;
    pub use crate::DynIntExprNode;
    pub use crate::ExprCreator;
    pub use crate::FullMul;
    pub use crate::InputClause;
    pub use crate::IntCondAdd;
    pub use crate::IntCondMul;
    pub use crate::IntCondNeg;
    pub use crate::IntCondShl;
    pub use crate::IntCondShr;
    pub use crate::IntCondSub;
    pub use crate::IntConstant;
    pub use crate::IntEqual;
    pub use crate::IntError;
    pub use crate::IntExprNode;
    pub use crate::IntModAdd;
    pub use crate::IntModAddAssign;
    pub use crate::IntModMul;
    pub use crate::IntModMulAssign;
    pub use crate::IntModNeg;
    pub use crate::IntModSub;
    pub use crate::IntModSubAssign;
    pub use crate::IntOrd;
    pub use crate::Literal;
    pub use crate::QuantSet;
    pub use crate::Quantifier;
    pub use crate::SimplifiableClause;
    pub use crate::TryFromNSized;
    pub use crate::TryIntConstant;
    pub use crate::TryIntConstantN;
    pub use crate::VarLit;
}

pub mod writer;
pub use writer::{
    CNFError, CNFWriter, Clause, InputClause, Literal, QuantSet, Quantifier, SimplifiableClause,
    VarLit,
};

pub mod boolexpr;
pub use boolexpr::{bool_ite, BoolEqual, BoolImpl, ExprNode as BoolExprNode};
pub mod boolexpr_creator;
pub use boolexpr_creator::{ExprCreator, ExprCreator32, ExprCreatorSys};
mod int_utils;
pub mod intexpr;
pub use intexpr::{
    int_ite, int_table, BitMask, BitVal, DivMod, ExprNode as IntExprNode, FullMul, I128ExprNode,
    I16ExprNode, I32ExprNode, I64ExprNode, I8ExprNode, IExprNode, IntCondAdd, IntCondMul,
    IntCondNeg, IntCondShl, IntCondShr, IntCondSub, IntConstant, IntEqual, IntError, IntModAdd,
    IntModAddAssign, IntModMul, IntModMulAssign, IntModNeg, IntModSub, IntModSubAssign, IntOrd,
    TryIntConstant, U128ExprNode, U16ExprNode, U32ExprNode, U64ExprNode, U8ExprNode, UExprNode,
};
pub mod dynintexpr;
mod intmacros;
pub use dynintexpr::{
    dynint_ite, dynint_table, ExprNode as DynIntExprNode, IDynExprNode, TryFromNSized,
    TryIntConstantN, UDynExprNode,
};

pub use generic_array;
