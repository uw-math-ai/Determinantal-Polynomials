/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anders Lewis
-/
module

public import DetPoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The Desnanot–Jacobi identity

For `i ≠ j`, `adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ = det M · det M[{i,j}ᶜ, {i,j}ᶜ]`
(`Matrix.adjugate_mul_adjugate_sub_adjugate_mul_adjugate`). Stating it with the adjugate avoids
signs. This is the Dodgson condensation step and the key identity behind Theorem 2.3.

## Proof outline

Let `C` be the identity with columns `i`, `j` replaced by those of `adjugate M`, and let
`S = {i, j}ᶜ`. Both `C` and `M * C` are block triangular with respect to `S`, so
* `det C = adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ`, and
* `det (M * C) = (det M)² · det M[S]`.

Hence `det M · LHS = det M · (det M · det M[S])` over any commutative ring. To cancel `det M`,
prove the identity for the generic matrix `mvPolynomialX n n ℤ` (whose determinant is nonzero in
an integral domain) and specialize.

## Implementation notes

The block-triangular steps use Mathlib's `Matrix.twoBlockTriangular_det`, which splits the index
type by a predicate (here `· ∈ {i, j}ᶜ`) without reindexing to a sum type. Its blocks are
`toSquareBlockProp`s, definitionally equal to `principalSubmatrix` for a set predicate.
-/

public section

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

namespace Matrix

/-- The determinant of the block of `N` on a two-element set `{i, j}`. -/
theorem det_toSquareBlockProp_pair (N : Matrix n n R) {i j : n}
    (hij : i ≠ j) {p : n → Prop} [DecidablePred p]
    (hp : ∀ x, x ∈ ({i, j} : Set n) ↔ p x) :
    (N.toSquareBlockProp p).det = N i i * N j j - N i j * N j i := by
  have hl : [i, j].Nodup := by simpa
  let e := (hl.getEquiv [i, j]).trans (Equiv.subtypeEquivRight (by simpa using hp))
  rw [← det_submatrix_equiv_self e]
  exact det_fin_two _

/-- The identity matrix with columns `i` and `j` replaced by those of `adjugate M`. -/
private def adjugateCols (M : Matrix n n R) (i j : n) : Matrix n n R :=
  ((1 : Matrix n n R).updateCol i fun k ↦ M.adjugate k i).updateCol j fun k ↦ M.adjugate k j

/-- The complementary block of `adjugateCols` is the identity. -/
private theorem adjugateCols_toSquareBlockProp_compl (M : Matrix n n R) (i j : n) :
    (adjugateCols M i j).toSquareBlockProp (· ∈ ({i, j}ᶜ : Set n)) = 1 := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
  simp [adjugateCols, toSquareBlockProp_def, updateCol_apply, hb.1, hb.2, one_apply]

/-- The columns of `adjugateCols M i j` indexed by `{i, j}ᶜ` are standard basis vectors, so its
determinant is that of the `{i, j}` block. -/
private theorem det_adjugateCols (M : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (adjugateCols M i j).det =
      M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i := by
  rw [twoBlockTriangular_det _ (· ∈ ({i, j}ᶜ : Set n)),
    det_toSquareBlockProp_pair _ hij (p := (· ∉ ({i, j}ᶜ : Set n)))
      (by simp [or_iff_not_imp_left])]
  · -- the `{i, j}ᶜ` block is the identity
    simp only [adjugateCols_toSquareBlockProp_compl, det_one, one_mul]
    simp [adjugateCols, hij]
  · -- block triangularity
    intro k hk l hl
    have hkl : k ≠ l := by rintro rfl; exact hk hl
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hl
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

/-- Multiplying by `adjugateCols` preserves the complementary principal block. -/
private theorem mul_adjugateCols_toSquareBlockProp_compl (M : Matrix n n R) (i j : n) :
    (M * adjugateCols M i j).toSquareBlockProp (· ∈ ({i, j}ᶜ : Set n)) =
      M.toSquareBlockProp (· ∈ ({i, j}ᶜ : Set n)) := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
  simp [toSquareBlockProp_def, mul_adjugateCols_apply, hb.1, hb.2]

/-- `M * adjugateCols M i j` is block triangular, with blocks `M[{i, j}ᶜ]` and `det M • 1`. -/
private theorem det_mul_adjugateCols (M : Matrix n n R) {i j : n} (hij : i ≠ j) :
    (M * adjugateCols M i j).det = M.det ^ 2 * (M.principalSubmatrix ({i, j}ᶜ : Set n)).det := by
  rw [twoBlockTriangular_det' _ (· ∈ ({i, j}ᶜ : Set n)),
    det_toSquareBlockProp_pair _ hij (p := fun x ↦ x ∉ ({i, j}ᶜ : Set n))
      (by simp [or_iff_not_imp_left])]
  · -- the `{i, j}ᶜ` block is `M[{i, j}ᶜ]`, and the `{i, j}` block is `det M • 1`
    simp [mul_adjugateCols_toSquareBlockProp_compl, mul_adjugateCols_apply, hij, hij.symm,
      pow_two, mul_comm, principalSubmatrix_eq_toSquareBlockProp]
  · -- block triangularity
    intro k hk l hl
    have hkl : k ≠ l := by rintro rfl; exact hl hk
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_not] at hl
    simp [mul_adjugateCols_apply, hl, hkl]

/-- The Desnanot–Jacobi identity multiplied through by `det M`. -/
private theorem det_mul_adjugate_mul_adjugate_sub_adjugate_mul_adjugate (M : Matrix n n R)
    {i j : n} (hij : i ≠ j) :
    M.det * (M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i) =
      M.det * (M.det * (M.principalSubmatrix ({i, j}ᶜ : Set n)).det) := by
  rw [← det_adjugateCols M hij, ← det_mul, det_mul_adjugateCols M hij, pow_two, mul_assoc]

/-- The **Desnanot–Jacobi identity** (Dodgson condensation), in adjugate form:
`adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ = det M · det M[{i,j}ᶜ, {i,j}ᶜ]`. -/
theorem adjugate_mul_adjugate_sub_adjugate_mul_adjugate (M : Matrix n n R) {i j : n}
    (hij : i ≠ j) :
    M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i =
      M.det * (M.principalSubmatrix ({i, j}ᶜ : Set n)).det := by
  let A := mvPolynomialX n n ℤ
  suffices A.adjugate i i * A.adjugate j j - A.adjugate i j * A.adjugate j i =
      A.det * (A.principalSubmatrix ({i, j}ᶜ : Set n)).det by
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
