# CNFGEN

The library to generate CNF (Conjunctive Normal Form) formulas.

This library provides simple CNF writer, structures to create boolean formula from
boolean expressions and integer expressions. The module `writer` provides
basic types, traits to handle clauses and literals, simple the CNF writer to write
same CNF formulas. The `boolexpr` module provides structure to construct boolean
expressions. The `intexpr` and `dynintexpr` modules provide structure and traits to
construct integer expressions.

Same construction of expressions can be done in natural way by using operators or
methods. The object called `ExprCreator` holds all expressions. The main structures
that allow construct expressions are expression nodes: `BoolExprNode`, `IntExprNode`
and `DynIntExprNode`. BoolExprNode allows to construct boolean expressions.
`IntExprNode` and `DynIntExprNode` allows to construct integer expressions or multiple
bit expressions.

The version 0.4.0 offers new interface to operate on expressions.
This interface in `boolvar`, `intvar` and `dynintvar` modules. New interface offers
few simplifications that facility writing complex expressions.
New `boolvar` module provides simpler interface to construct boolean expressions.
New `intvar` module provides simpler interface to construct integer expressions.
New `dynintvar` module provides simpler interface to construct dynamic integer expressions.
The routine that creates new expression must be called inside `call16`, `call32` or `callsys`.
That routine can returns formula to generate. The `BoolVar` allows to operate on boolean
expressions, `IntVar` allows to operate on integer expressions and `DynIntVar` allows to
operate on dynamic integer expressions. These types can be used as references and
constants be converted into one of that type by using From trait.

The version 0.5.0 adds `min` and `max` helpers, new an optimized tables and If-Then-Else and
and additional `subvalues` method to dynamic integers.

Samples of usage of these modules can be found in documentation of these modules.

Typical usage of this library is: construction boolean expression and write it by using
method `write` from an expression object. The `writer` module can be used to write
'raw' CNF formulas that can be generated by other software.

Sample usage:

```
use cnfgen::boolvar::*;
use cnfgen::intvar::*;
use cnfgen::writer::{CNFError, CNFWriter};
use std::io;
fn write_diophantine_equation() -> Result<(), CNFError> {
    let formula: BoolVar32 = call32(|| {
        // define variables - signed 32-bit wide.
        let x = I32Var32::var();
        let y = I32Var32::var();
        let z = I32Var32::var();
        // define equation: x^2 + y^2 - 77*z^2 = 0
        let powx = (&x).fullmul(&x);  // x^2
        let powy = (&y).fullmul(&y);  // y^2
        let powz = (&z).fullmul(&z);  // z^2
        // We use cond_mul to get product and required condition to avoid overflow.
        let (prod, cond0) = powz.cond_mul(77i64);
        // Similary, we use conditional addition and conditional subtraction.
        let (sum1, cond1) = powx.cond_add(powy);
        let (diff2, cond2) = sum1.cond_sub(prod);
        // define final formula with required conditions.
        diff2.equal(0) & cond0 & cond1 & cond2
    });
    // write CNF to stdout.
    formula.write(&mut CNFWriter::new(io::stdout()))
}
```

Sample usage (older):

```
use cnfgen::boolexpr::*;
use cnfgen::intexpr::*;
use cnfgen::writer::{CNFError, CNFWriter};
use std::io;

fn write_diophantine_equation() -> Result<(), CNFError> {
    // define ExprCreator.
    let creator = ExprCreator32::new();
    // define variables - signed 32-bit wide.
    let x = I32ExprNode::variable(creator.clone());
    let y = I32ExprNode::variable(creator.clone());
    let z = I32ExprNode::variable(creator.clone());
    // define equation: x^2 + y^2 - 77*z^2 = 0
    let powx = x.clone().fullmul(x);  // x^2
    let powy = y.clone().fullmul(y);  // y^2
    let powz = z.clone().fullmul(z);  // z^2
    // We use cond_mul to get product and required condition to avoid overflow.
    let (prod, cond0) = powz.cond_mul(77i64);
    // Similary, we use conditional addition and conditional subtraction.
    let (sum1, cond1) = powx.cond_add(powy);
    let (diff2, cond2) = sum1.cond_sub(prod);
    // define final formula with required conditions.
    let formula: BoolExprNode<_> = diff2.equal(0) & cond0 & cond1 & cond2;
    // write CNF to stdout.
    formula.write(&mut CNFWriter::new(io::stdout()))
}
```
