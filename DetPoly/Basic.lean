/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaoda Ji, Joe Rogge, Nhi Bach, David Javnozon, Anders Lewis, Liron Shani, Grant Yang
-/

module

public import Mathlib

/-!
# Determinantal Polynomials

Lean 4 formalization of Theorem 4.1 from
[arXiv:2309.00806](https://arxiv.org/abs/2309.00806) (Al Ahmadieh '23),
characterizing the fiber of a point in the image of the principal minor map.
-/
@[expose] public noncomputable section
open MvPolynomial Matrix

variable {n R : Type*} [CommRing R] [DecidableEq n] [Fintype n]

/-- The Rayleigh difference `Δᵢⱼ(f) = ∂ᵢf ∂ⱼf - f ∂ᵢ∂ⱼf`. -/
def rayleighDiff (i j : n) (f : MvPolynomial n R) : MvPolynomial n R :=
  pderiv i f * pderiv j f - f * pderiv i (pderiv j f)

/-- `diag(x₁,…,xₙ) + A`. -/
abbrev Matrix.mvCharmatrix (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  diagonal X + A.map C

/-- The determinantal polynomial `f_A = det(diag(x) + A)`. -/
abbrev Matrix.detpoly (A : Matrix n n R) : MvPolynomial n R :=
  A.mvCharmatrix.det

/-- The principal submatrix `A[S, S]`. -/
abbrev Matrix.principalSubmatrix (A : Matrix n n R) (S : Finset n) : Matrix S S R :=
  A.submatrix (↑) (↑)

end
