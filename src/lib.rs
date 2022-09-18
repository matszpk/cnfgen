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
    pub use crate::CNFWriter;
    pub use crate::Clause;
    pub use crate::InputClause;
    pub use crate::Literal;
    pub use crate::QuantSet;
    pub use crate::Quantifier;
    pub use crate::SimplifiableClause;
    pub use crate::VarLit;
}

pub mod writer;
pub use writer::{
    CNFWriter, Clause, InputClause, Literal, QuantSet, Quantifier, SimplifiableClause, VarLit,
};

pub mod boolexpr;
