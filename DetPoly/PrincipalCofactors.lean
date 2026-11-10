/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Principal cofactors

The principal-minor identities needed to differentiate determinantal polynomials in
`DetPoly.Theorem2_3`. General cofactors and row and column expansions are in
`LEAN_Warmup.Grant.Laplace`.
-/

public section

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

end Matrix

end
