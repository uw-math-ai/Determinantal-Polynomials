/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Cofactors and Laplace expansion over an arbitrary index type

Mathlib's Laplace expansion over an arbitrary `Fintype` is `Matrix.det_eq_sum_mul_adjugate_row`,
which keeps the cofactor as the sign-free `adjugate A j i = det (A.updateRow i (Pi.single j 1))`.
The submatrix forms (`Matrix.det_succ_row`, `Matrix.adjugate_fin_succ_eq_det_submatrix`) need
`Fin (n + 1)`, because deleting row `i` and column `j` needs a bijection `{i}ᶜ ≃ {j}ᶜ`, and the
sign `(-1) ^ (i + j)` belongs to the order-preserving one.

Over an arbitrary index type we use the bijection `Equiv.swap i j : {i}ᶜ → {j}ᶜ` instead. Its
sign is `Equiv.Perm.sign (Equiv.swap i j)`, which is `1` if `i = j` and `-1` otherwise.

## Main results

* `Matrix.det_updateRow_single_self`: `det (A.updateRow i (Pi.single i 1)) = det A[{i}ᶜ]`.
* `Matrix.det_updateRow_single`: the general case, with columns reindexed by `Equiv.swap i j`.
* `Matrix.adjugate_apply_self`, `Matrix.adjugate_apply_eq_det_submatrix`: the corresponding
  statements for the adjugate.
* `Matrix.det_eq_sum_mul_det_submatrix_row`: Laplace expansion along a row.
-/

public section

open Equiv (Perm)

variable {n R : Type*} [CommRing R] [DecidableEq n]

namespace Matrix

variable [Fintype n]

/-- Replacing row `i` by `eᵢ` leaves the complementary principal minor. -/
theorem det_updateRow_single_self (A : Matrix n n R) (i : n) :
    (A.updateRow i (Pi.single i 1)).det = (A.principalSubmatrix {i}ᶜ).det := by
  rw [twoBlockTriangular_det _ (· ∈ ({i}ᶜ : Set n))]
  · have h1 : (A.updateRow i (Pi.single i 1)).toSquareBlockProp (· ∉ ({i}ᶜ : Set n)) = 1 := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_not] at ha hb
      subst ha hb
      simp [toSquareBlockProp_def]
    rw [h1, det_one, mul_one]
    congr 1
    ext ⟨a, ha⟩ ⟨b, hb⟩
    simp [toSquareBlockProp_def, updateRow_ne (show a ≠ i from ha)]
  · simp_all [updateRow_apply]

/-- Replacing row `i` by `eⱼ` leaves the minor deleting row `i` and column `j`, with the columns
`{i}ᶜ → {j}ᶜ` matched by `Equiv.swap i j`. This is the analogue of
`Matrix.adjugate_fin_succ_eq_det_submatrix` for an arbitrary index type. -/
theorem det_updateRow_single (A : Matrix n n R) (i j : n) :
    (A.updateRow i (Pi.single j 1)).det =
      Perm.sign (Equiv.swap i j) *
        (A.submatrix (↑) fun k : ({i}ᶜ : Set n) ↦ Equiv.swap i j k).det := by
  have h : (A.updateRow i (Pi.single j 1)).submatrix id (Equiv.swap i j) =
      (A.submatrix id (Equiv.swap i j)).updateRow i (Pi.single i 1) := by
    ext a b
    by_cases ha : a = i
    · subst ha; simp [Pi.single_apply, Equiv.swap_apply_eq_iff]
    · simp [ha]
  have hσ := det_permute' (Equiv.swap i j) (A.updateRow i (Pi.single j 1))
  rw [h, det_updateRow_single_self] at hσ
  have hs : (Perm.sign (Equiv.swap i j) : R) * Perm.sign (Equiv.swap i j) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  calc _ = (Perm.sign (Equiv.swap i j) : R) * Perm.sign (Equiv.swap i j) *
        (A.updateRow i (Pi.single j 1)).det := by rw [hs, one_mul]
    _ = _ := by rw [mul_assoc, ← hσ]; rfl

/-- A diagonal entry of the adjugate is the complementary principal minor. -/
theorem adjugate_apply_self (A : Matrix n n R) (i : n) :
    A.adjugate i i = (A.principalSubmatrix {i}ᶜ).det := by
  rw [adjugate_apply, det_updateRow_single_self]

/-- An entry of the adjugate as a signed minor, for an arbitrary index type. -/
theorem adjugate_apply_eq_det_submatrix (A : Matrix n n R) (i j : n) :
    A.adjugate i j =
      Perm.sign (Equiv.swap j i) *
        (A.submatrix (↑) fun k : ({j}ᶜ : Set n) ↦ Equiv.swap j i k).det := by
  rw [adjugate_apply, det_updateRow_single]

/-- **Laplace expansion** along row `i`, for an arbitrary index type. -/
theorem det_eq_sum_mul_det_submatrix_row (A : Matrix n n R) (i : n) :
    A.det = ∑ j, Perm.sign (Equiv.swap i j) * A i j *
      (A.submatrix (↑) fun k : ({i}ᶜ : Set n) ↦ Equiv.swap i j k).det := by
  rw [det_eq_sum_mul_adjugate_row A i]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [adjugate_apply_eq_det_submatrix]
  ring

end Matrix

end
