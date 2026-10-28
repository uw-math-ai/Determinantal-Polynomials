# Computing with determinantal polynomials

Keep theorems in Mathlib's `MvPolynomial`. Construct executable inputs directly in
`CMvPolynomial`, and use `cMvPolynomialEquiv` only in correctness proofs. Converting a
symbolic Mathlib polynomial back through the equivalence is noncomputable.

For example, in a Lean file:

```lean
module

import DetPoly.CMVPolynomial.Matrix
meta import DetPoly.CMVPolynomial

open CMvPolynomial

def A : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 4]
def B : Matrix (Fin 2) (Fin 2) ℚ := !![1, 4; 3 / 2, 4]

#eval sameFiber A B -- true
#eval detPoly A
#eval pderiv 0 (detPoly A)
#eval adjPoly A
```

Use `ℚ`, `ℤ`, or computable finite fields for coefficients. Abstract `Field` instances
need not be executable. The native examples in `DetPoly/CMVPolynomial/Examples.lean`
include a 4×4 cut transpose. Check them with:

```sh
lake build DetPoly.CMVPolynomial.Examples
```

The core provides constants, variables, arithmetic, decidable equality (with decidable
coefficient equality), substitution, partial differentiation, setting a variable to zero,
Rayleigh differences, and the paper's degree-one resultant. Coefficients are accessed by
function application to a `DFinsupp` exponent vector. `normalize` rebuilds the outer support
bound, discarding zero terms; it is provably the identity on polynomial values. It does not
normalize the support bounds inside exponent vectors. Printing uses unsafe quotient
extraction only for display, with unspecified term order.

The matrix API computes `diag(X) + A`, its determinant and adjugate, and compares two
determinantal polynomials. Its correctness lemmas connect these to the existing project
definitions, with no new `sorry`s. The Boolean `sameFiber` is certified equivalent to equality
of `Matrix.detPoly`. The project's separate theorem connecting this equality to all principal
minors, `Matrix.detPoly_eq_iff`, still has its original `sorry`; the new correctness proofs
do not use it.

## Backend choice: CompPoly

[CompPoly](https://github.com/Verified-zkEVM/CompPoly) is a promising backend for sustained
computation. Inspected revision: `9be21b026e43ff9b032113dc9b766d2b17fd6c3c`.

* Its Lean and Mathlib versions match this project's `v4.35.0`.
* `CPoly.CMvPolynomial n R` uses vector exponents and tree maps, keeping stored coefficients
  nonzero. This avoids the direct-sum model's accumulating support bounds.
* It supplies ring instances, a Mathlib ring equivalence, substitution, evaluation, variable
  renaming, degree queries, and leading-term operations.
* Algorithms use `Fin n` variables and lawful Boolean coefficient equality. General-index
  theorems can remain in `MvPolynomial`; executable matrices can use `Fin n`.
* No multivariate polynomial differentiation or factorization API was found in the inspected
  multivariate subtree. Those need implementation or a separate backend.

Recommendation: use the current direct-sum implementation as a small reference model and
correctness baseline. Before expanding it into a large algebra system, evaluate a pinned
CompPoly backend on the same matrix examples. Port the project-specific operations and
correctness lemmas to that backend if it performs well. No CompPoly dependency is added yet,
and compatibility here means matching pins and source inspection, not a successful downstream
build or a performance benchmark.

## Remaining algorithmic work

These primitives compute and check candidates; they do not implement the full fiber search.
That needs constructive rank-one block decomposition, polynomial exact division/factorization
(or externally proposed factors with verified product identities), and reconstruction of
constant matrix entries from the proposed adjugate. Over infinite fields, searching the whole
fiber by enumeration is not a terminating general algorithm.

For larger matrices, benchmark determinant and adjugate expansion separately from the
polynomial backend. The initial implementation uses Mathlib's permutation-based determinant;
a division-free determinant algorithm can be a more important improvement than changing the
polynomial representation. Factorization and matrix reconstruction require stronger coefficient
assumptions than the ring operations in this implementation.
