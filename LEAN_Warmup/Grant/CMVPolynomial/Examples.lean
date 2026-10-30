/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import LEAN_Warmup.Grant.CMVPolynomial.Matrix
public meta import LEAN_Warmup.Grant.CMVPolynomial
public meta import Mathlib.Algebra.DirectSum.Ring

/-!
# Executable checks for computable matrix polynomials

These checks use exact rational arithmetic and `#guard` checks.
-/
-- This module checks executable behavior rather than exporting computation proofs.
set_option linter.hashCommand false

@[expose] public section

namespace CMvPolynomial.Examples

/-- A two-by-two rational matrix. -/
def A : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 3, 4]
/-- A diagonal conjugate of `A`. -/
def B : Matrix (Fin 2) (Fin 2) ℚ := !![1, 4; 3 / 2, 4]
/-- A matrix with a different off-diagonal product from `A`. -/
def D : Matrix (Fin 2) (Fin 2) ℚ := !![1, 4; 3, 4]

-- Same diagonal and off-diagonal product, hence the same determinantal polynomial.
#guard sameFiber A B = true
#guard sameFiber A D = false
#guard detPoly A = X 0 * X 1 + 4 * X 0 + X 1 - 2

#guard pderiv 0 (detPoly A) = X 1 + 4
#guard setZero 0 (detPoly A) = X 1 - 2
#guard rayleighDiff 0 1 (detPoly A) = 6
#guard resultant 0 (X 0 + 2) (X 0 + 3 : CMvPolynomial (Fin 2) ℚ) = -1
#guard (adjPoly A) 0 1 = -2
#guard normalize (X 0 - X 0 : CMvPolynomial (Fin 2) ℚ) = 0

-- A cut transpose: exchange the right factors of the rank-one off-diagonal blocks
-- and transpose the lower diagonal block.
/-- A four-by-four matrix with rank-one off-diagonal blocks. -/
def cutA : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 2, 3, 4; 3, 4, 6, 8; 35, 40, 5, 6; 42, 48, 7, 8]
/-- The cut transpose of `cutA` along its first two indices. -/
def cutB : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, 2, 5, 6; 3, 4, 10, 12; 21, 24, 5, 7; 28, 32, 6, 8]

#guard sameFiber cutA cutB = true

-- The empty determinant and a one-variable derivative also compute.
#guard detPoly (0 : Matrix (Fin 0) (Fin 0) ℚ) = 1
#guard pderiv 0 (X 0 ^ 3 : CMvPolynomial (Fin 1) ℚ) = 3 * X 0 ^ 2

end CMvPolynomial.Examples

end
