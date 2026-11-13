/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang, Shaoda Ji
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Determinants of rank-one updates

Fraction-free determinant identities for matrices built from outer products `u vᵀ`
(`Matrix.vecMulVec u v`), over a commutative ring.

## Main results

* `Matrix.det_add_vecMulVec`: the matrix determinant lemma `det (A + u vᵀ) = det A + vᵀ adj(A) u`.
* `Matrix.adjugate_fromBlocks_vecMulVec_apply₁₂`: an entry of the adjugate of
  `[[A, u vᵀ], [C, D]]` in the upper right block factors as
  `-det (A with column i replaced by u) · det (D with row j replaced by v)`.
* `Matrix.det_fromBlocks_vecMulVec`:
  `det [[A, p qᵀ], [u vᵀ, D]] = det A det D - (vᵀ adj(A) p) (qᵀ adj(D) u)`.
* `Matrix.rank_le_one_iff_eq_vecMulVec`: over a field, a matrix has rank at most one iff it is an
  outer product.

## Implementation notes

Mathlib's versions (`Matrix.det_add_replicateCol_mul_replicateRow`, `Matrix.det_fromBlocks₁₁`)
assume an invertible block. The versions here use the adjugate instead, so they hold over any
commutative ring, e.g. for `diagonal X + A` over `MvPolynomial n R`.
-/

@[expose] public section

open Finset

namespace Matrix

variable {R m n : Type*}

section CommRing

variable [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The **matrix determinant lemma** over a commutative ring:
`det (A + u vᵀ) = det A + vᵀ adj(A) u`. Compare `Matrix.det_add_replicateCol_mul_replicateRow`,
which assumes `A` invertible. -/
theorem det_add_vecMulVec (A : Matrix n n R) (u v : n → R) :
    (A + vecMulVec u v).det = A.det + v ⬝ᵥ A.adjugate *ᵥ u := by
  -- Add `v j • u` to the columns `j ∈ S` one at a time.
  let B (S : Finset n) : Matrix n n R := of fun i j ↦ A i j + if j ∈ S then u i * v j else 0
  suffices h : ∀ S, (B S).det = A.det + ∑ j ∈ S, v j * (A.updateCol j u).det by
    have hB : A + vecMulVec u v = B univ := by ext; simp [B, vecMulVec_apply]
    rw [hB, h, ← cramer_eq_adjugate_mulVec, dotProduct]
    simp [cramer_apply]
  intro S
  induction S using Finset.induction_on with
  | empty =>
    have : B ∅ = A := by ext; simp [B]
    simp [this]
  | insert k S hk ih =>
    have hBk : B (insert k S) = (B S).updateCol k ((fun i ↦ B S i k) + v k • u) := by
      ext i j
      by_cases hj : j = k
      · subst hj; simp [B, hk, mul_comm]
      · simp [B, hj]
    -- Subtracting `v j •` column `k` from each column `j ∈ S` turns `B S` back into `A`.
    have hu : ((B S).updateCol k u).det = (A.updateCol k u).det := by
      rw [← det_transpose, ← det_transpose (A.updateCol k u)]
      refine det_eq_of_forall_row_eq_smul_add_const (fun j ↦ if j ∈ S then v j else 0) k
        (by simp [hk]) fun j i ↦ ?_
      by_cases hj : j = k
      · subst hj; simp [hk]
      · by_cases hjS : j ∈ S <;> simp [B, hj, hjS, mul_comm]
    rw [hBk, det_updateCol_add, updateCol_eq_self, det_updateCol_smul, ih, hu,
      sum_insert hk]
    ring

/-- An entry of the adjugate of `[[A, u vᵀ], [C, D]]` in the upper right block factors:
`adj(M)_{ij} = -det (A with column i replaced by u) · det (D with row j replaced by v)`. -/
theorem adjugate_fromBlocks_vecMulVec_apply₁₂ (A : Matrix m m R) (C : Matrix n m R)
    (D : Matrix n n R) (u : m → R) (v : n → R) (i : m) (j : n) :
    (fromBlocks A (vecMulVec u v) C D).adjugate (.inl i) (.inr j) =
      -((A.updateCol i u).det * (D.updateRow j v).det) := by
  -- `adj(M)_{ij} = det N`, where row `inr j` of `N` is the unit vector at `inl i`. Adding
  -- multiples of that row turns column `inl i` into `(u, e_j)`; then subtracting multiples of
  -- this column clears the upper right block.
  set N := (fromBlocks A (vecMulVec u v) C D).updateRow (.inr j) (Pi.single (.inl i) 1)
  set B := N.updateCol (.inl i) (Sum.elim u (Pi.single j 1))
  have hNB : N.det = B.det := by
    refine (det_eq_of_forall_row_eq_smul_add_const
      (Sum.elim (fun r ↦ u r - A r i) (fun r ↦ if r = j then 0 else -C r i)) (.inr j)
      (by simp) fun a b ↦ ?_).symm
    rcases a with a | a <;> rcases b with b | b <;>
      simp [N, B, updateRow_apply, updateCol_apply, Pi.single_apply] <;> split_ifs <;> simp_all
  have hB : B.det = (fromBlocks (A.updateCol i u) 0 B.toBlocks₂₁ (D.updateRow j (-v))).det := by
    rw [← det_transpose, eq_comm, ← det_transpose]
    refine det_eq_of_forall_row_eq_smul_add_const (Sum.elim 0 (-v)) (.inl i) (by simp)
      fun a b ↦ ?_
    rcases a with a | a <;> rcases b with b | b <;>
      simp [N, B, toBlocks₂₁, updateRow_apply, updateCol_apply, Pi.single_apply,
        vecMulVec_apply, mul_comm]
    split_ifs <;> simp
  rw [adjugate_apply, hNB, hB, det_fromBlocks_zero₁₂, ← neg_one_smul R v, det_updateRow_smul]
  ring

/-- The determinant of `[[A, p qᵀ], [u vᵀ, D]]`. This is the rank-one Schur complement formula
`det A · det (D - u vᵀ A⁻¹ p qᵀ)`, without assuming `A` invertible. -/
theorem det_fromBlocks_vecMulVec (A : Matrix m m R) (D : Matrix n n R) (p v : m → R)
    (q u : n → R) :
    (fromBlocks A (vecMulVec p q) (vecMulVec u v) D).det =
      A.det * D.det - (v ⬝ᵥ A.adjugate *ᵥ p) * (q ⬝ᵥ D.adjugate *ᵥ u) := by
  have hsplit : fromBlocks A (vecMulVec p q) (vecMulVec u v) D =
      fromBlocks A (vecMulVec p q) 0 D + vecMulVec (Sum.elim 0 u) (Sum.elim v 0) := by
    ext (i | i) (j | j) <;> simp [vecMulVec_apply]
  have hA : ∑ i, v i * (A.updateCol i p).det = v ⬝ᵥ A.adjugate *ᵥ p := by
    simp [← cramer_eq_adjugate_mulVec, cramer_apply, dotProduct]
  have hD : ∑ j, (D.updateRow j q).det * u j = q ⬝ᵥ D.adjugate *ᵥ u := by
    rw [dotProduct_mulVec, dotProduct, ← mulVec_transpose, adjugate_transpose,
      ← cramer_eq_adjugate_mulVec]
    simp [cramer_transpose_apply]
  have key : Sum.elim v 0 ⬝ᵥ (fromBlocks A (vecMulVec p q) 0 D).adjugate *ᵥ Sum.elim 0 u =
      -((∑ i, v i * (A.updateCol i p).det) * ∑ j, (D.updateRow j q).det * u j) := by
    simp only [dotProduct, mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, zero_mul, mul_zero, sum_const_zero, add_zero, zero_add,
      adjugate_fromBlocks_vecMulVec_apply₁₂]
    rw [sum_mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_neg_distrib, mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [hsplit, det_add_vecMulVec, det_fromBlocks_zero₂₁, key, hA, hD]
  ring

end CommRing

section Field

variable {K : Type*} [Field K]

/-- A matrix has rank `≤ 1` iff it is an outer product `u vᵀ`. Mathlib has the `←` direction
(`Matrix.rank_vecMulVec_le`) and the module version
(`Submodule.finrank_le_one_iff_isPrincipal`). -/
theorem rank_le_one_iff_eq_vecMulVec [Fintype n] (M : Matrix m n K) :
    M.rank ≤ 1 ↔ ∃ u v, M = vecMulVec u v := by
  refine ⟨fun h ↦ ?_, fun ⟨u, v, h⟩ ↦ h ▸ rank_vecMulVec_le u v⟩
  have := FiniteDimensional.span_of_finite K (Set.finite_range M.col)
  rw [rank_eq_finrank_span_cols, Submodule.finrank_le_one_iff_isPrincipal,
    Submodule.isPrincipal_iff] at h
  obtain ⟨u, hu⟩ := h
  have : ∀ j, ∃ c : K, c • u = M.col j := fun j ↦
    Submodule.mem_span_singleton.mp (hu ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using this
  refine ⟨u, c, ?_⟩
  ext i j
  rw [vecMulVec_apply, ← col_apply M j i, ← hc j, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- A matrix with a nonzero entry has rank at least one. -/
theorem one_le_rank_of_apply_ne_zero [Fintype n] {M : Matrix m n K} {i : m} {j : n}
    (h : M i j ≠ 0) : 1 ≤ M.rank := by
  have := FiniteDimensional.span_of_finite K (Set.finite_range M.col)
  rw [rank_eq_finrank_span_cols]
  refine Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨_, Submodule.subset_span ⟨j, rfl⟩⟩, fun hc ↦ h ?_⟩
  simpa using congrArg (fun w : Submodule.span K (Set.range M.col) ↦ (w : m → K) i) hc

end Field

end Matrix

end
