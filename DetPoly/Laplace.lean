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

Over an arbitrary index type there is no canonical matching, so we index the kept rows and the
kept columns by a common type `m` through equivalences `er ec : Option m ≃ n`: the deleted row is
`er none`, the deleted column is `ec none`, the minor is `A.submatrix (er ∘ some) (ec ∘ some)`,
and the sign is `Equiv.Perm.sign (er.symm.trans ec)`. For instance `Equiv.optionSubtypeNe i`
indexes `{k // k ≠ i}`, and `(finSuccEquiv' i).symm` recovers the `Fin.succAbove` matching.
For a set of rows the same pattern uses `m ⊕ m' ≃ n` instead of `Option m ≃ n`.

## Main results

* `Matrix.det_updateRow_single_self`, `Matrix.det_updateCol_single_self`:
  `det (A.updateRow i (Pi.single i 1))` is the principal minor on `{k // k ≠ i}`.
* `Matrix.det_updateRow_single`, `Matrix.det_updateCol_single`: the general case.
* `Matrix.adjugate_apply_self`, `Matrix.adjugate_apply_eq_det_submatrix`: entries of the adjugate
  as minors.
* `Matrix.adjugate_submatrix_apply_self`: deleting two indices one at a time.
* `Matrix.det_eq_sum_mul_det_submatrix_row`, `Matrix.det_eq_sum_mul_det_submatrix_col`: Laplace
  expansion along a row or a column.
* `Matrix.adjugate_apply_eq_det_submatrix_swap`, `Matrix.det_eq_sum_mul_det_submatrix_row_swap`,
  `Matrix.det_eq_sum_mul_det_submatrix_col_swap`: the special case `m = {k // k ≠ i}`, with
  `{k // k ≠ i}` matched to `{k // k ≠ j}` by `Equiv.swap i j`.
-/

public section

open Equiv (Perm)

variable {m n R : Type*} [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

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

/-- Replacing row `er none` by `Pi.single (ec none) 1` leaves the minor on the rows `er ∘ some`
and the columns `ec ∘ some`, with the sign of the matching `er.symm.trans ec`. This generalizes
`Matrix.adjugate_fin_succ_eq_det_submatrix` to an arbitrary index type. -/
theorem det_updateRow_single (A : Matrix n n R) (er ec : Option m ≃ n) :
    (A.updateRow (er none) (Pi.single (ec none) 1)).det =
      Perm.sign (er.symm.trans ec) * (A.submatrix (er ∘ some) (ec ∘ some)).det := by
  set M := A.updateRow (er none) (Pi.single (ec none) 1)
  -- reindexing rows by `er` and columns by `ec` moves the replaced entry to `(none, none)`
  have hM : (M.submatrix id (er.symm.trans ec)).submatrix er er =
      (A.submatrix er ec).updateRow none (Pi.single none 1) := by
    ext (_ | a) b <;> simp [M, updateRow_apply, Pi.single_apply, ec.injective.eq_iff]
  let e : m ≃ {k : Option m // k ≠ none} :=
    ((Equiv.subtypeEquivRight fun _ ↦ Option.ne_none_iff_isSome).trans
      (Equiv.optionIsSomeEquiv m)).symm
  have h := det_permute' (er.symm.trans ec) M
  rw [← det_submatrix_equiv_self er, hM, det_updateRow_single_self,
    ← det_submatrix_equiv_self e] at h
  change (A.submatrix (er ∘ some) (ec ∘ some)).det = Perm.sign (er.symm.trans ec) * M.det at h
  rw [h, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
    Int.cast_one, one_mul]

/-- Replacing column `ec none` by `Pi.single (er none) 1` leaves the minor on the rows `er ∘ some`
and the columns `ec ∘ some`, with the sign of the matching `er.symm.trans ec`. -/
theorem det_updateCol_single (A : Matrix n n R) (er ec : Option m ≃ n) :
    (A.updateCol (ec none) (Pi.single (er none) 1)).det =
      Perm.sign (er.symm.trans ec) * (A.submatrix (er ∘ some) (ec ∘ some)).det := by
  rw [← det_transpose, ← updateRow_transpose, det_updateRow_single, ← transpose_submatrix,
    det_transpose, ← Perm.sign_symm, Equiv.symm_trans, Equiv.symm_symm]

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

/-- The entry of the adjugate at `(ec none, er none)` is the minor on the rows `er ∘ some` and
the columns `ec ∘ some`, with the sign of the matching `er.symm.trans ec`. This generalizes
`Matrix.adjugate_fin_succ_eq_det_submatrix` to an arbitrary index type. -/
theorem adjugate_apply_eq_det_submatrix (A : Matrix n n R) (er ec : Option m ≃ n) :
    A.adjugate (ec none) (er none) =
      Perm.sign (er.symm.trans ec) * (A.submatrix (er ∘ some) (ec ∘ some)).det := by
  rw [adjugate_apply, det_updateRow_single]

/-- **Laplace expansion** along the row `er none`, where `ec j` deletes the column `j`. This
generalizes `Matrix.det_succ_row` to an arbitrary index type. -/
theorem det_eq_sum_mul_det_submatrix_row (A : Matrix n n R) (er : Option m ≃ n)
    (ec : n → Option m ≃ n) (hec : ∀ j, ec j none = j) :
    A.det = ∑ j, Perm.sign (er.symm.trans (ec j)) * A (er none) j *
      (A.submatrix (er ∘ some) (ec j ∘ some)).det := by
  rw [det_eq_sum_mul_adjugate_row A (er none)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  conv_lhs => rw [← hec j, adjugate_apply_eq_det_submatrix, hec j]
  ring

/-- **Laplace expansion** along the column `ec none`, where `er i` deletes the row `i`. This
generalizes `Matrix.det_succ_column` to an arbitrary index type. -/
theorem det_eq_sum_mul_det_submatrix_col (A : Matrix n n R) (er : n → Option m ≃ n)
    (ec : Option m ≃ n) (her : ∀ i, er i none = i) :
    A.det = ∑ i, Perm.sign ((er i).symm.trans ec) * A i (ec none) *
      (A.submatrix (er i ∘ some) (ec ∘ some)).det := by
  rw [← det_transpose, det_eq_sum_mul_det_submatrix_row _ ec er her]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [transpose_apply, ← transpose_submatrix, det_transpose, ← Perm.sign_symm,
    Equiv.symm_trans, Equiv.symm_symm]

/-! ### Matching `{k // k ≠ i}` with `{k // k ≠ j}` by `Equiv.swap i j` -/

/-- `Matrix.adjugate_apply_eq_det_submatrix` with the rows `{k // k ≠ j}` matched to the columns
`{k // k ≠ i}` by `Equiv.swap j i`. -/
theorem adjugate_apply_eq_det_submatrix_swap (A : Matrix n n R) (i j : n) :
    A.adjugate i j =
      Perm.sign (Equiv.swap j i) *
        (A.submatrix (↑) fun k : {k // k ≠ j} ↦ Equiv.swap j i k).det := by
  have h := adjugate_apply_eq_det_submatrix A (Equiv.optionSubtypeNe j)
    ((Equiv.optionSubtypeNe j).trans (Equiv.swap j i))
  simp only [Equiv.optionSubtypeNe_none, Equiv.trans_apply, Equiv.swap_apply_left] at h
  rw [h, ← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
  rfl

/-- **Laplace expansion** along row `i`, with the minors matched by `Equiv.swap i j`. -/
theorem det_eq_sum_mul_det_submatrix_row_swap (A : Matrix n n R) (i : n) :
    A.det = ∑ j, Perm.sign (Equiv.swap i j) * A i j *
      (A.submatrix (↑) fun k : {k // k ≠ i} ↦ Equiv.swap i j k).det := by
  rw [det_eq_sum_mul_adjugate_row A i]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [adjugate_apply_eq_det_submatrix_swap]
  ring

/-- **Laplace expansion** along column `j`, with the minors matched by `Equiv.swap j i`. -/
theorem det_eq_sum_mul_det_submatrix_col_swap (A : Matrix n n R) (j : n) :
    A.det = ∑ i, Perm.sign (Equiv.swap j i) * A i j *
      (A.submatrix (fun k : {k // k ≠ j} ↦ Equiv.swap j i k) (↑)).det := by
  rw [← det_transpose, det_eq_sum_mul_det_submatrix_row_swap _ j]
  simp_rw [transpose_apply, ← transpose_submatrix, det_transpose]

end Matrix

end
