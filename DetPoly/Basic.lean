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

variable {n R : Type*}

/-- The submatrix of `A` with rows in `S` and columns in `T`. -/
abbrev Matrix.finsetSubmatrix {m : Type*} (A : Matrix n m R) (S : Finset n) (T : Finset m)
    : Matrix S T R :=
  A.submatrix (↑) (↑)

/-- The principal submatrix `A[S, S]`. -/
abbrev Matrix.principalSubmatrix (A : Matrix n n R) (S : Finset n) : Matrix S S R :=
  A.finsetSubmatrix S S

theorem Matrix.principalSubmatrix_eq_toSquareBlockProp (A : Matrix n n R) (S : Finset n) :
    A.principalSubmatrix S = A.toSquareBlockProp (· ∈ S) :=
  rfl

variable [CommRing R] [DecidableEq n] [Fintype n]

/-- hack to work around different instances getting picked up:
  `Subtype.fintype` vs. `Finset.Subtype.fintype` -/
theorem Matrix.det_principalSubmatrix (A : Matrix n n R) (S : Finset n) :
    (A.principalSubmatrix S).det =
      @det _ _ (Subtype.fintype (· ∈ S)) _ _ (A.toSquareBlockProp (· ∈ S)) := by
  convert rfl using 2
  exact (A.principalSubmatrix_eq_toSquareBlockProp S).symm

/-- The Rayleigh difference `Δᵢⱼ(f) = ∂ᵢf ∂ⱼf - f ∂ᵢ∂ⱼf`. -/
def rayleighDiff (i j : n) (f : MvPolynomial n R) : MvPolynomial n R :=
  pderiv i f * pderiv j f - f * pderiv i (pderiv j f)

/-- `diag(x₁,…,xₙ) + A`. -/
abbrev Matrix.mvCharmatrix (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  diagonal X + A.map C

/-- The determinantal polynomial `f_A = det(diag(x) + A)`. -/
abbrev Matrix.detpoly (A : Matrix n n R) : MvPolynomial n R :=
  A.mvCharmatrix.det

end
