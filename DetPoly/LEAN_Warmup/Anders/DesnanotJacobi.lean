/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anders Lewis
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The Desnanot–Jacobi identity

`adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ = det M · det M({i,j}ᶜ, {i,j}ᶜ)` for `i ≠ j`.

## Proof outline

Let `C` be the identity with columns `i`, `j` replaced by those of `adjugate M`, and let
`S = {i, j}ᶜ`. Both `C` and `M * C` are block triangular with respect to `S`, so
* `det C = adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ`, and
* `det (M * C) = (det M)² · det M[S]`.

Hence `det M · LHS = det M · (det M · det M[S])` over any commutative ring. To cancel `det M`,
prove the identity for the generic matrix `mvPolynomialX n n ℤ` (whose determinant is nonzero in
an integral domain) and specialize.
-/

@[expose] public section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

namespace Matrix

/-- The identity matrix with columns `i` and `j` replaced by those of `adjugate M`. -/
def adjugateCols (M : Matrix n n R) (i j : n) : Matrix n n R :=
  ((1 : Matrix n n R).updateCol i fun k ↦ M.adjugate k i).updateCol j fun k ↦ M.adjugate k j

/-- The determinant of the `{i, j}` block of `N`, computed by reindexing the block to `Fin 2`. -/
theorem det_toSquareBlockProp_pair (N : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (N.toSquareBlockProp fun k ↦ k = i ∨ k = j).det = N i i * N j j - N i j * N j i := by
  let e : Fin 2 ≃ {k // k = i ∨ k = j} :=
    { toFun := ![⟨i, .inl rfl⟩, ⟨j, .inr rfl⟩]
      invFun := fun k ↦ if k.1 = i then 0 else 1
      left_inv := by intro a; fin_cases a <;> simp [hij.symm]
      right_inv := by rintro ⟨k, rfl | rfl⟩ <;> simp [hij.symm] }
  rw [← det_submatrix_equiv_self e, det_fin_two]
  rfl

/-- The columns of `adjugateCols M i j` indexed by `{i, j}ᶜ` are standard basis vectors, so it
is block triangular and its determinant is the `{i, j}` block. -/
theorem det_adjugateCols (M : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (M.adjugateCols i j).det =
      M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i := by
  rw [twoBlockTriangular_det' _ fun k ↦ k = i ∨ k = j, det_toSquareBlockProp_pair _ hij]
  · -- the `{i, j}ᶜ` block is the identity, and the entries of `adjugateCols` at `i`, `j`
    have h1 : (M.adjugateCols i j).toSquareBlockProp (fun k ↦ ¬(k = i ∨ k = j)) = 1 := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw [not_or] at hb
      simp [adjugateCols, toSquareBlockProp_def, updateCol_apply, hb.1, hb.2, one_apply]
    simp only [h1, det_one, mul_one]
    simp [adjugateCols, hij]
  · -- block triangularity
    intro k hk l hl
    have hkl : k ≠ l := by rintro rfl; exact hl hk
    rw [not_or] at hl
    simp [adjugateCols, hl.1, hl.2, hkl]

/-- Columns `i`, `j` of `M * adjugateCols M i j` are `det M • eᵢ`, `det M • eⱼ` (by
`mul_adjugate`), and the other columns are those of `M`. -/
theorem mul_adjugateCols_apply (M : Matrix n n R) (i j k l : n) :
    (M * M.adjugateCols i j) k l =
      if l = i ∨ l = j then (M.det • (1 : Matrix n n R)) k l else M k l := by
  have hv (c : n) : (M *ᵥ fun k ↦ M.adjugate k c) k = (M.det • (1 : Matrix n n R)) k c := by
    rw [← mul_adjugate]; rfl
  simp only [adjugateCols, mul_updateCol, mul_one, updateCol_apply, hv]
  split_ifs <;> subst_vars <;> tauto

/-- `M * adjugateCols M i j` is block triangular, with blocks `det M • 1` and `M[{i, j}ᶜ]`. -/
theorem det_mul_adjugateCols (M : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (M * M.adjugateCols i j).det =
      M.det ^ 2 * (M.toSquareBlockProp fun k ↦ ¬(k = i ∨ k = j)).det := by
  rw [twoBlockTriangular_det _ fun k ↦ k = i ∨ k = j, det_toSquareBlockProp_pair _ hij]
  · -- the `{i, j}` block is `det M • 1`, and the `{i, j}ᶜ` block is `M[{i, j}ᶜ]`
    have h1 : (M * M.adjugateCols i j).toSquareBlockProp (fun k ↦ ¬(k = i ∨ k = j)) =
        M.toSquareBlockProp fun k ↦ ¬(k = i ∨ k = j) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      rw [not_or] at hb
      simp [toSquareBlockProp_def, mul_adjugateCols_apply, hb.1, hb.2]
    simp only [h1, mul_adjugateCols_apply, true_or, or_true, ↓reduceIte, smul_apply,
      one_apply_eq, one_apply_ne hij, one_apply_ne hij.symm, smul_eq_mul, mul_one, mul_zero,
      sub_zero, pow_two]
  · -- block triangularity
    intro k hk l hl
    have hkl : k ≠ l := by rintro rfl; exact hk hl
    simp [mul_adjugateCols_apply, hl, hkl]

/-- The Desnanot–Jacobi identity multiplied through by `det M`. Holds over any commutative ring. -/
theorem det_mul_adjugate_mul_adjugate_sub_adjugate_mul_adjugate (M : Matrix n n R) {i j : n}
    (hij : i ≠ j) :
    M.det * (M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i) =
      M.det * (M.det * (M.toSquareBlockProp fun k ↦ ¬(k = i ∨ k = j)).det) := by
  rw [← det_adjugateCols M hij, ← det_mul, det_mul_adjugateCols M hij, pow_two, mul_assoc]

/-- The Desnanot–Jacobi (Dodgson condensation) identity, written in terms of the adjugate so
no signs appear. -/
-- This is a mouthful but it seems like Lean standards are for descriptive names on the LHS,
-- with proper names in the docstring.
theorem adjugate_mul_adjugate_sub_adjugate_mul_adjugate (M : Matrix n n R) {i j : n}
    (hij : i ≠ j) :
    M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i =
      M.det * (M.toSquareBlockProp fun k ↦ ¬(k = i ∨ k = j)).det := by
  let A := mvPolynomialX n n ℤ
  suffices A.adjugate i i * A.adjugate j j - A.adjugate i j * A.adjugate j i =
      A.det * (A.toSquareBlockProp fun k ↦ ¬(k = i ∨ k = j)).det by
    let f := MvPolynomial.aeval (R := ℤ) fun p : n × n ↦ M p.1 p.2
    have hA : f.mapMatrix A = M := mvPolynomialX_mapMatrix_aeval ℤ M
    have h := congrArg f this
    simp only [map_sub, map_mul, AlgHom.map_det] at h
    -- what remains differs from the goal only by unfolding `f.mapMatrix`
    rw [← hA, ← AlgHom.map_adjugate]
    exact h
  exact mul_left_cancel₀ (det_mvPolynomialX_ne_zero n ℤ)
    (det_mul_adjugate_mul_adjugate_sub_adjugate_mul_adjugate A hij)

end Matrix

end
