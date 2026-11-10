/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.PrincipalCofactors

/-!
# Cofactors and Laplace expansion over an arbitrary index type

General row and column deletion formulas use equivalences `er ec : Option m ≃ n`;
the sign is `Equiv.Perm.sign (er.symm.trans ec)`. The swap versions match the
remaining rows and columns by `Equiv.swap`. The principal-minor identities used by
Theorem 2.3 remain in `DetPoly.Laplace`.
-/

public section

open Equiv (Perm)

variable {m n R : Type*} [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

namespace Matrix

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
