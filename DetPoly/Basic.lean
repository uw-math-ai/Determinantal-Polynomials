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
@[expose] public noncomputable section
open MvPolynomial Matrix

variable {n R : Type*}

/-- The submatrix of `A` with rows in `S` and columns in `T`. -/
abbrev Matrix.setSubmatrix {m : Type*} (A : Matrix n m R) (S : Set n) (T : Set m)
    : Matrix S T R :=
  A.submatrix (↑) (↑)

/-- Compatibility alias for `Matrix.setSubmatrix` -/
abbrev Matrix.finsetSubmatrix {m : Type*} (A : Matrix n m R) (S : Finset n) (T : Finset m) :=
  A.setSubmatrix S T

variable [DecidableEq n] [Fintype n]

section CommRing
variable [CommRing R]

/-- The Rayleigh difference `Δᵢⱼ(f) = ∂ᵢf ∂ⱼf - f ∂ᵢ∂ⱼf`. -/
def rayleighDiff (i j : n) (f : MvPolynomial n R) : MvPolynomial n R :=
  pderiv i f * pderiv j f - f * pderiv i (pderiv j f)

/-- `diag(x₁,…,xₙ) + A`. -/
abbrev Matrix.mvCharmatrix (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  diagonal X + A.map C

/-- The determinantal polynomial `f_A = det(diag(x) + A)`. -/
abbrev Matrix.detpoly (A : Matrix n n R) : MvPolynomial n R :=
  A.mvCharmatrix.det

end CommRing

section Field
variable {𝔽 : Type*} [Field 𝔽]

/-- `A` has a cut at `X`: `2 ≤ |X| ≤ n - 2`, `rk A[X,Xᶜ] ≤ 1` and `rk A[Xᶜ,X] ≤ 1`. Proofs
use the factorization form `rank_le_one_iff_eq_vecMulVec`. The definition is symmetric in
`X ↔ Xᶜ` (`HasCut.compl`). -/
def Matrix.HasCut (A : Matrix n n 𝔽) (X : Finset n) : Prop :=
  2 ≤ X.card ∧ 2 ≤ Xᶜ.card ∧
    (A.setSubmatrix X (Xᶜ : Finset n)).rank ≤ 1 ∧
    (A.setSubmatrix (Xᶜ : Finset n) X).rank ≤ 1

/-- The complement of a cut is a cut. -/
theorem Matrix.HasCut.compl {A : Matrix n n 𝔽} {X : Finset n} (h : A.HasCut X) :
    A.HasCut Xᶜ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨h₂, by rwa [compl_compl], by rwa [compl_compl], by rwa [compl_compl]⟩

end Field

end
