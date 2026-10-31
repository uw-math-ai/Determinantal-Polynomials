/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Cofactors and Laplace expansion over an arbitrary index type

Mathlib's Laplace expansion over an arbitrary `Fintype` is `Matrix.det_eq_sum_mul_adjugate_row`,
which keeps the cofactor as `adjugate A j i = det (A.updateRow i (Pi.single j 1))`. The forms
with an explicit minor (`Matrix.det_succ_row`, `Matrix.adjugate_fin_succ_eq_det_submatrix`) are
stated for `Fin (n + 1)`, where `Fin.succAbove` matches the rows `{k // k ≠ i}` with the columns
`{k // k ≠ j}` monotonically, giving the sign `(-1) ^ (i + j)`.

Over an arbitrary index type we match them by `Equiv.swap i j` instead, whose sign
`Equiv.Perm.sign (Equiv.swap i j)` is `1` if `i = j` and `-1` otherwise.

## Main results

* `Matrix.det_updateRow_single_self`, `Matrix.det_updateCol_single_self`:
  `det (A.updateRow i (Pi.single i 1))` is the principal minor on `{k // k ≠ i}`.
* `Matrix.det_updateRow_single`, `Matrix.det_updateCol_single`: the general case.
* `Matrix.adjugate_apply_self`, `Matrix.adjugate_apply_eq_det_submatrix`: entries of the adjugate
  as minors.
* `Matrix.adjugate_submatrix_apply_self`: deleting two indices one at a time.
* `Matrix.det_eq_sum_mul_det_submatrix_row`, `Matrix.det_eq_sum_mul_det_submatrix_col`: Laplace
  expansion along a row or a column.
-/

public section

open Equiv (Perm)

variable {n R : Type*} [CommRing R] [DecidableEq n] [Fintype n]

namespace Matrix

/-- Replacing row `i` by `Pi.single i 1` leaves the principal minor on `{k // k ≠ i}`. -/
theorem det_updateRow_single_self (A : Matrix n n R) (i : n) :
    (A.updateRow i (Pi.single i 1)).det =
      (A.submatrix (↑) ((↑) : {k // k ≠ i} → n)).det := by
  rw [twoBlockTriangular_det _ (· ≠ i)]
  · have h : (A.updateRow i (Pi.single i 1)).toSquareBlockProp (¬· ≠ i) = 1 := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp only [ne_eq, not_not] at ha hb
      subst ha hb
      simp [toSquareBlockProp_def]
    rw [h, det_one, mul_one]
    congr 1
    ext ⟨a, ha⟩ ⟨b, hb⟩
    simp [toSquareBlockProp_def, ha]
  · simp_all

/-- Replacing column `j` by `Pi.single j 1` leaves the principal minor on `{k // k ≠ j}`. -/
theorem det_updateCol_single_self (A : Matrix n n R) (j : n) :
    (A.updateCol j (Pi.single j 1)).det =
      (A.submatrix (↑) ((↑) : {k // k ≠ j} → n)).det := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_single_self, ← transpose_submatrix,
    det_transpose]

/-- Replacing row `i` by `Pi.single j 1` leaves the minor on rows `{k // k ≠ i}` and columns
`{k // k ≠ j}`, matched by `Equiv.swap i j`. This generalizes
`Matrix.adjugate_fin_succ_eq_det_submatrix` to an arbitrary index type. -/
theorem det_updateRow_single (A : Matrix n n R) (i j : n) :
    (A.updateRow i (Pi.single j 1)).det =
      Perm.sign (Equiv.swap i j) *
        (A.submatrix (↑) fun k : {k // k ≠ i} ↦ Equiv.swap i j k).det := by
  obtain rfl | hij := eq_or_ne i j
  · simpa using det_updateRow_single_self A i
  -- swapping columns `i` and `j` turns row `i` into `Pi.single i 1`
  have h := det_permute' (Equiv.swap i j) (A.updateRow i (Pi.single j 1))
  have hr : Pi.single j (1 : R) ∘ Equiv.swap i j = Pi.single i 1 :=
    (Pi.single_comp_equiv _ _ _).trans (by simp)
  rw [← Equiv.coe_refl, submatrix_updateRow_equiv, Equiv.refl_symm, Equiv.refl_apply,
    ← Function.comp_def, hr, det_updateRow_single_self, Perm.sign_swap hij] at h
  rw [Perm.sign_swap hij]
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h ⊢
  exact (neg_eq_iff_eq_neg.1 h.symm).trans rfl

/-- Replacing column `j` by `Pi.single i 1` leaves the minor on rows `{k // k ≠ i}` and columns
`{k // k ≠ j}`, matched by `Equiv.swap j i`. -/
theorem det_updateCol_single (A : Matrix n n R) (i j : n) :
    (A.updateCol j (Pi.single i 1)).det =
      Perm.sign (Equiv.swap j i) *
        (A.submatrix (fun k : {k // k ≠ j} ↦ Equiv.swap j i k) (↑)).det := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_single, ← transpose_submatrix,
    det_transpose]

/-- A diagonal entry of the adjugate is the principal minor on `{k // k ≠ i}`. -/
theorem adjugate_apply_self (A : Matrix n n R) (i : n) :
    A.adjugate i i = (A.submatrix (↑) ((↑) : {k // k ≠ i} → n)).det := by
  rw [adjugate_apply, det_updateRow_single_self]

/-- The diagonal entry at `i` of the adjugate of the principal submatrix on `{k // k ≠ j}` is the
principal minor on `{k // k ≠ i ∧ k ≠ j}`. -/
theorem adjugate_submatrix_apply_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (A.submatrix (↑) ((↑) : {k // k ≠ j} → n)).adjugate ⟨i, hij⟩ ⟨i, hij⟩ =
      (A.submatrix (↑) ((↑) : {k // k ≠ i ∧ k ≠ j} → n)).det := by
  rw [adjugate_apply_self]
  let e : {l : {k // k ≠ j} // l ≠ ⟨i, hij⟩} ≃ {k // k ≠ i ∧ k ≠ j} :=
    (Equiv.subtypeEquivRight (by simp)).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter (· ≠ j) (· ≠ i)).trans <|
        Equiv.subtypeEquivRight (by tauto)
  rw [← det_submatrix_equiv_self e.symm]
  simp [e, Function.comp_def]

/-- An entry of the adjugate as a signed minor. This generalizes
`Matrix.adjugate_fin_succ_eq_det_submatrix` to an arbitrary index type. -/
theorem adjugate_apply_eq_det_submatrix (A : Matrix n n R) (i j : n) :
    A.adjugate i j =
      Perm.sign (Equiv.swap j i) *
        (A.submatrix (↑) fun k : {k // k ≠ j} ↦ Equiv.swap j i k).det := by
  rw [adjugate_apply, det_updateRow_single]

/-- **Laplace expansion** along row `i`. This generalizes `Matrix.det_succ_row` to an arbitrary
index type. -/
theorem det_eq_sum_mul_det_submatrix_row (A : Matrix n n R) (i : n) :
    A.det = ∑ j, Perm.sign (Equiv.swap i j) * A i j *
      (A.submatrix (↑) fun k : {k // k ≠ i} ↦ Equiv.swap i j k).det := by
  rw [det_eq_sum_mul_adjugate_row A i]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [adjugate_apply_eq_det_submatrix]
  ring

/-- **Laplace expansion** along column `j`. This generalizes `Matrix.det_succ_column` to an
arbitrary index type. -/
theorem det_eq_sum_mul_det_submatrix_col (A : Matrix n n R) (j : n) :
    A.det = ∑ i, Perm.sign (Equiv.swap j i) * A i j *
      (A.submatrix (fun k : {k // k ≠ j} ↦ Equiv.swap j i k) (↑)).det := by
  rw [← det_transpose, det_eq_sum_mul_det_submatrix_row _ j]
  simp_rw [transpose_apply, ← transpose_submatrix, det_transpose]

end Matrix

end
