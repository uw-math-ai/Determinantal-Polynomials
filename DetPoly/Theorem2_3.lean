/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.Basic
public import DetPoly.DesnanotJacobi
public import DetPoly.JacobiFormula
public import DetPoly.PrincipalCofactors

/-!
# Theorem 2.3: Rayleigh differences of determinantal polynomials

`Δᵢⱼ(f_A) = G_ij G_ji`, where `f_A = det(diag(x) + A)` and `G = adj(diag(x) + A)`
([arXiv:2309.00806], Thm 2.3). The proof combines `∂ᵢ f_A = G_ii`,
`∂ᵢ∂ⱼ f_A = det (diag(x) + A)[{i,j}ᶜ]` with the Desnanot–Jacobi identity
`Matrix.adjugate_mul_adjugate_sub_adjugate_mul_adjugate`. No non-principal minors are needed:
off-diagonal cofactors only appear as adjugate entries.

## Implementation notes

The partial derivatives are computed for `diag(x ∘ v) + B` with `v : m → n`, so that principal
submatrices of `diag(x) + A` (indexed by subtypes) are covered by the same lemma. By Jacobi's
formula (`Derivation.leibniz_det`), only rows `l` with `v l = i` contribute to `∂ᵢ`, and such a
row differentiates to `eₗ`, leaving `adj(diag(x ∘ v) + B)_ll`.
-/

public noncomputable section
open MvPolynomial Matrix

variable {m n R : Type*} [CommRing R] [DecidableEq n]

section pderiv
variable [DecidableEq m] [Fintype m]

omit [Fintype m] in
/-- Entries of `diag(x ∘ v) + B` are affine: `∂ᵢ` of row `l` is `eₗ` if `v l = i`, else `0`. -/
theorem pderiv_diagonal_X_add_apply (v : m → n) (B : Matrix m m R) (i : n) (l c : m) :
    pderiv i ((diagonal (fun l ↦ X (v l)) + B.map C : Matrix m m (MvPolynomial n R)) l c) =
      if v l = i then (Pi.single l 1 : m → MvPolynomial n R) c else 0 := by
  by_cases hlc : l = c <;> by_cases hl : v l = i <;> simp_all [pderiv_X, Ne.symm]

/-- `∂ᵢ det(diag(x ∘ v) + B)` is the sum of the diagonal adjugate entries at `l` with
`v l = i`. -/
theorem pderiv_det_diagonal_X_add (v : m → n) (B : Matrix m m R) (i : n) :
    pderiv i (diagonal (fun l ↦ X (v l)) + B.map C).det =
      ∑ l with v l = i, (diagonal (fun l ↦ X (v l)) + B.map C).adjugate l l := by
  rw [(pderiv i).leibniz_det, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro l _
  simp_rw [pderiv_diagonal_X_add_apply]
  by_cases hl : v l = i
  · simp only [hl, ite_true, adjugate_apply]
  · simp only [hl, ite_false]
    exact det_eq_zero_of_row_eq_zero l fun c ↦ by simp

omit [DecidableEq n] in
/-- `∂_{v k} det(diag(x ∘ v) + B) = adj(diag(x ∘ v) + B)_kk` for injective `v`. -/
theorem pderiv_det_diagonal_X_add_of_injective {v : m → n} (hv : v.Injective)
    (B : Matrix m m R) (k : m) :
    pderiv (v k) (diagonal (fun l ↦ X (v l)) + B.map C).det =
      (diagonal (fun l ↦ X (v l)) + B.map C).adjugate k k := by
  classical
  rw [pderiv_det_diagonal_X_add, Finset.sum_eq_single_of_mem k (by simp) _]
  intro l hl hlk
  exact absurd (hv (Finset.mem_filter.1 hl).2) hlk

omit [DecidableEq n] in
/-- `∂ᵢ det(diag(x ∘ v) + B) = 0` if `i` is not in the range of `v`. -/
theorem pderiv_det_diagonal_X_add_of_notMem (v : m → n) (B : Matrix m m R) {i : n}
    (hi : i ∉ Set.range v) : pderiv i (diagonal (fun l ↦ X (v l)) + B.map C).det = 0 := by
  classical
  rw [pderiv_det_diagonal_X_add, Finset.sum_eq_zero fun l hl ↦
    absurd ⟨l, (Finset.mem_filter.1 hl).2⟩ hi]

end pderiv

variable [Fintype n]

/-- `∂ᵢ f_A = G_ii`. -/
theorem pderiv_detpoly (A : Matrix n n R) (i : n) :
    pderiv i A.detpoly = A.mvCharmatrix.adjugate i i :=
  pderiv_det_diagonal_X_add_of_injective (v := id) Function.injective_id A i

/-- `∂ᵢ∂ⱼ f_A` is the principal minor of `diag(x) + A` on `{k // k ≠ i ∧ k ≠ j}`, for `i ≠ j`. -/
theorem pderiv_pderiv_detpoly (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    pderiv i (pderiv j A.detpoly) =
      (A.mvCharmatrix.submatrix ((↑) : {k // k ≠ i ∧ k ≠ j} → n) (↑)).det := by
  rw [pderiv_detpoly, adjugate_apply_self, mvCharmatrix_submatrix _ Subtype.val_injective]
  refine (pderiv_det_diagonal_X_add_of_injective Subtype.val_injective _
    (⟨i, hij⟩ : {k // k ≠ j})).trans ?_
  rw [← mvCharmatrix_submatrix _ Subtype.val_injective, adjugate_submatrix_apply_self]

/-- `∂ᵢ∂ᵢ f_A = 0`: `f_A` is multiaffine. -/
theorem pderiv_pderiv_detpoly_self (A : Matrix n n R) (i : n) :
    pderiv i (pderiv i A.detpoly) = 0 := by
  rw [pderiv_detpoly, adjugate_apply_self, mvCharmatrix_submatrix _ Subtype.val_injective]
  exact pderiv_det_diagonal_X_add_of_notMem _ _ (by simp)

/-- **Theorem 2.3**: `Δᵢⱼ(f_A) = G_ij G_ji` where `G = adj(diag(x) + A)`. -/
theorem rayleighDiff_detpoly (A : Matrix n n R) (i j : n) :
    rayleighDiff i j A.detpoly = A.mvCharmatrix.adjugate i j * A.mvCharmatrix.adjugate j i := by
  rw [rayleighDiff]
  obtain rfl | hij := eq_or_ne i j
  · rw [pderiv_pderiv_detpoly_self, pderiv_detpoly, mul_zero, sub_zero]
  · rw [pderiv_pderiv_detpoly A hij, pderiv_detpoly, pderiv_detpoly, detpoly,
      ← adjugate_mul_adjugate_sub_adjugate_mul_adjugate _ hij]
    ring

end
