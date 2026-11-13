/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaoda Ji, Joe Rogge, Nhi Bach, David Javnozon, Anders Lewis, Liron Shani, Grant Yang
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib

/-!
# Determinantal polynomials and cuts

Definitions used by Theorem 2.3 and Lemma 4.3 of Al Ahmadieh (2023).
-/
@[expose] public section
open MvPolynomial Matrix

variable {n R : Type*}

/-- The submatrix of `A` with rows in `S` and columns in `T`. -/
abbrev Matrix.setSubmatrix {m : Type*} (A : Matrix n m R) (S : Set n) (T : Set m)
    : Matrix S T R :=
  A.submatrix (↑) (↑)

variable [DecidableEq n] [Fintype n]

section CommRing
variable [CommRing R]

/-- The Rayleigh difference `Δᵢⱼ(f) = ∂ᵢf ∂ⱼf - f ∂ᵢ∂ⱼf`. -/
noncomputable
def rayleighDiff (i j : n) (f : MvPolynomial n R) : MvPolynomial n R :=
  pderiv i f * pderiv j f - f * pderiv i (pderiv j f)

/-- `diag(x₁,…,xₙ) + A`. -/
noncomputable
abbrev Matrix.mvCharmatrix (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  diagonal X + A.map C

/-- The determinantal polynomial `f_A = det(diag(x) + A)`. -/
noncomputable
abbrev Matrix.detpoly (A : Matrix n n R) : MvPolynomial n R :=
  A.mvCharmatrix.det

/-- The principal minor `A_S`. -/
abbrev Matrix.principalMinor (A : Matrix n n R) (S : Finset n) : R :=
  (A.setSubmatrix S S).det
end CommRing
end
