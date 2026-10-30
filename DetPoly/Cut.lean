/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/

module

public import DetPoly.Basic

/-! # Cuts of matrices -/

@[expose] public section

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n]

/-- `A` has a cut at `X`: `2 ≤ |X| ≤ n - 2`, `rk A[X,Xᶜ] ≤ 1` and `rk A[Xᶜ,X] ≤ 1`. Proofs
use the factorization form `rank_le_one_iff_eq_vecMulVec`. The definition is symmetric in
`X ↔ Xᶜ` (`HasCut.compl`). -/
def Matrix.HasCut [Field 𝔽] (A : Matrix n n 𝔽) (X : Finset n) : Prop :=
  2 ≤ X.card ∧ 2 ≤ Xᶜ.card ∧
    (A.finsetSubmatrix X Xᶜ).rank ≤ 1 ∧
    (A.finsetSubmatrix Xᶜ X).rank ≤ 1

/-- The complement of a cut is a cut. -/
theorem Matrix.HasCut.compl [Field 𝔽] {A : Matrix n n 𝔽} {X : Finset n} (h : A.HasCut X) :
    A.HasCut Xᶜ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨h₂, by rwa [compl_compl], by rwa [compl_compl], by rwa [compl_compl]⟩

end
