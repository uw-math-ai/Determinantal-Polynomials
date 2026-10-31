/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anders Lewis
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The Desnanot–Jacobi identity

For `i ≠ j`, `adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ = det M · det M[{i,j}ᶜ, {i,j}ᶜ]`, where the
minor is `M.submatrix (↑) (↑)` on `{k // k ≠ i ∧ k ≠ j}`
(`Matrix.adjugate_mul_adjugate_sub_adjugate_mul_adjugate`). Stating it with the adjugate avoids
signs. This is the Dodgson condensation step and the key identity behind Theorem 2.3.

## Proof outline

Let `C` be the identity with columns `i`, `j` replaced by those of `adjugate M`, and let
`S = {k // k ≠ i ∧ k ≠ j}`. Both `C` and `M * C` are block triangular with respect to `S`, so
* `det C = adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ`, and
* `det (M * C) = (det M)² · det M[S]`.

Hence `det M · LHS = det M · (det M · det M[S])` over any commutative ring. To cancel `det M`,
prove the identity for the generic matrix `mvPolynomialX n n ℤ` (whose determinant is nonzero in
an integral domain) and specialize.

## Implementation notes

The block-triangular steps use Mathlib's `Matrix.twoBlockTriangular_det`, which splits the index
type by a predicate (here `fun k ↦ k ≠ i ∧ k ≠ j`) without reindexing to a sum type. Its blocks
are `toSquareBlockProp`s, definitionally equal to `submatrix (↑) (↑)`.
-/

public section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

namespace Matrix

/-- The determinant of the block of `N` on a two-element set `{i, j}`. -/
theorem det_toSquareBlockProp_pair (N : Matrix n n R) {i j : n}
    (hij : i ≠ j) {p : n → Prop} [DecidablePred p] (hp : ∀ x, p x ↔ x = i ∨ x = j) :
    (N.toSquareBlockProp p).det = N i i * N j j - N i j * N j i := by
  have hl : [i, j].Nodup := by simpa
  let e := (hl.getEquiv [i, j]).trans (Equiv.subtypeEquivRight (q := p) fun x ↦ by simp [hp])
  rw [← det_submatrix_equiv_self e]
  exact det_fin_two _

/-- The identity matrix with columns `i` and `j` replaced by those of `adjugate M`. -/
private def adjugateCols (M : Matrix n n R) (i j : n) : Matrix n n R :=
  ((1 : Matrix n n R).updateCol i fun k ↦ M.adjugate k i).updateCol j fun k ↦ M.adjugate k j

/-- The complementary block of `adjugateCols` is the identity. -/
private theorem adjugateCols_toSquareBlockProp_compl (M : Matrix n n R) (i j : n) :
    (adjugateCols M i j).toSquareBlockProp (fun k ↦ k ≠ i ∧ k ≠ j) = 1 := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp [adjugateCols, toSquareBlockProp_def, updateCol_apply, hb.1, hb.2, one_apply]

/-- The columns of `adjugateCols M i j` outside `{i, j}` are standard basis vectors, so its
determinant is that of the `{i, j}` block. -/
private theorem det_adjugateCols (M : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (adjugateCols M i j).det =
      M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i := by
  rw [twoBlockTriangular_det _ (fun k ↦ k ≠ i ∧ k ≠ j),
    det_toSquareBlockProp_pair _ hij (p := fun k ↦ ¬(k ≠ i ∧ k ≠ j)) fun _ ↦ by tauto]
  · -- the complementary block is the identity
    simp only [adjugateCols_toSquareBlockProp_compl, det_one, one_mul]
    simp [adjugateCols, hij]
  · -- block triangularity
    intro k hk l hl
    have hkl : k ≠ l := by rintro rfl; exact hk hl
    simp [adjugateCols, hl.1, hl.2, hkl]

/-- Columns `i`, `j` of `M * adjugateCols M i j` are `det M • eᵢ`, `det M • eⱼ` (by
`mul_adjugate`), and the other columns are those of `M`. -/
private theorem mul_adjugateCols_apply (M : Matrix n n R) (i j k l : n) :
    (M * adjugateCols M i j) k l =
      if l = i ∨ l = j then (M.det • (1 : Matrix n n R)) k l else M k l := by
  have hv (c : n) : (M *ᵥ fun k ↦ M.adjugate k c) k = (M.det • (1 : Matrix n n R)) k c := by
    rw [← mul_adjugate]; rfl
  simp only [adjugateCols, mul_updateCol, mul_one, updateCol_apply, hv]
  split_ifs <;> subst_vars <;> tauto

/-- `M * adjugateCols M i j` is block triangular, with blocks `M` on `{k // k ≠ i ∧ k ≠ j}` and
`det M • 1` on `{i, j}`. -/
private theorem det_mul_adjugateCols (M : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (M * adjugateCols M i j).det =
      M.det ^ 2 * (M.submatrix ((↑) : {k // k ≠ i ∧ k ≠ j} → n) (↑)).det := by
  rw [twoBlockTriangular_det' _ (fun k ↦ k ≠ i ∧ k ≠ j),
    det_toSquareBlockProp_pair _ hij (p := fun k ↦ ¬(k ≠ i ∧ k ≠ j)) fun _ ↦ by tauto]
  · have h : (M * adjugateCols M i j).toSquareBlockProp (fun k ↦ k ≠ i ∧ k ≠ j) =
        M.submatrix (↑) (↑) := by
      ext ⟨a, ha⟩ ⟨b, hb⟩
      simp [toSquareBlockProp_def, mul_adjugateCols_apply, hb.1, hb.2]
    simp [h, mul_adjugateCols_apply, hij, hij.symm, pow_two, mul_comm]
  · -- block triangularity
    intro k hk l hl
    have hkl : k ≠ l := by rintro rfl; exact hl hk
    simp only [ne_eq, not_and_or, not_not] at hl
    simp [mul_adjugateCols_apply, hl, hkl]

/-- The Desnanot–Jacobi identity multiplied through by `det M`. -/
private theorem det_mul_adjugate_mul_adjugate_sub_adjugate_mul_adjugate (M : Matrix n n R)
    {i j : n} (hij : i ≠ j) :
    M.det * (M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i) =
      M.det * (M.det * (M.submatrix ((↑) : {k // k ≠ i ∧ k ≠ j} → n) (↑)).det) := by
  rw [← det_adjugateCols M hij, ← det_mul, det_mul_adjugateCols M hij, pow_two, mul_assoc]

/-- The **Desnanot–Jacobi identity** (Dodgson condensation), in adjugate form:
`adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ = det M · det M[{i,j}ᶜ, {i,j}ᶜ]`. This is a two-index
analogue of `Matrix.det_eq_sum_mul_adjugate_row`. -/
theorem adjugate_mul_adjugate_sub_adjugate_mul_adjugate (M : Matrix n n R) {i j : n}
    (hij : i ≠ j) :
    M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i =
      M.det * (M.submatrix ((↑) : {k // k ≠ i ∧ k ≠ j} → n) (↑)).det := by
  let A := mvPolynomialX n n ℤ
  suffices A.adjugate i i * A.adjugate j j - A.adjugate i j * A.adjugate j i =
      A.det * (A.submatrix ((↑) : {k // k ≠ i ∧ k ≠ j} → n) (↑)).det by
    let f := MvPolynomial.aeval (R := ℤ) fun p : n × n ↦ M p.1 p.2
    have hA : f.mapMatrix A = M := mvPolynomialX_mapMatrix_aeval ℤ M
    have h := congrArg f this
    simp only [map_sub, map_mul, AlgHom.map_det] at h
    -- what remains differs from the goal only by unfolding `f.mapMatrix`
    rwa [← hA, ← AlgHom.map_adjugate]
  exact mul_left_cancel₀ (det_mvPolynomialX_ne_zero n ℤ)
    (det_mul_adjugate_mul_adjugate_sub_adjugate_mul_adjugate A hij)

end Matrix

end
