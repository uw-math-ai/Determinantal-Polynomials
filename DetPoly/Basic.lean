/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaoda Ji, Joe Rogge, Nhi Bach, David Javnozon, Anders Lewis, Liron Shani, Grant Yang
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Determinantal Polynomials

Lean 4 formalization of Theorem 4.1 from
[arXiv:2309.00806](https://arxiv.org/abs/2309.00806) (Al Ahmadieh '23),
characterizing the fiber of a point in the image of the principal minor map.
-/
@[expose] public noncomputable section
open MvPolynomial Matrix

variable {n R : Type*}

section
variable {m : Type*}

/-- The submatrix of `A` with rows in `S` and columns in `T`. -/
abbrev Matrix.setSubmatrix (A : Matrix n m R) (S : Set n) (T : Set m)
    : Matrix S T R :=
  A.submatrix (↑) (↑)

end

/-- The principal submatrix `A[S, S]`. -/
abbrev Matrix.principalSubmatrix (A : Matrix n n R) (S : Set n) : Matrix S S R :=
  A.setSubmatrix S S

theorem Matrix.principalSubmatrix_eq_toSquareBlockProp (A : Matrix n n R) (S : Set n) :
    A.principalSubmatrix S = A.toSquareBlockProp (· ∈ S) :=
  rfl

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
