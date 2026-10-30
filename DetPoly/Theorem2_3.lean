/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.DesnanotJacobi

/-!
# Theorem 2.3: Rayleigh differences of determinantal polynomials

`Δᵢⱼ(f_A) = G_ij G_ji`, where `f_A = det(diag(x) + A)` and `G = adj(diag(x) + A)`
([arXiv:2309.00806], Thm 2.3). The proof combines `∂ᵢ∂ⱼ f_A = det (diag(x) + A)[{i,j}ᶜ]` with
the Desnanot–Jacobi identity `Matrix.adjugate_mul_adjugate_sub_adjugate_mul_adjugate`.
-/
public noncomputable section
open MvPolynomial Matrix

variable {n R : Type*} [CommRing R] [DecidableEq n] [Fintype n]

theorem pderiv_detPoly_eq (A : Matrix n n R) (i : n) :
    (pderiv i A.detpoly) = (A.mvCharmatrix.principalSubmatrix ({i}ᶜ : Finset n)).det := by
  sorry

theorem pderiv_pderiv_detPoly_eq (A : Matrix n n R) {i j : n} (hneq : i ≠ j) :
    (pderiv i (pderiv j A.detpoly)) = (A.mvCharmatrix.principalSubmatrix ({i, j}ᶜ : Finset n)).det := by
  sorry

#check adjugate_mul_adjugate_sub_adjugate_mul_adjugate
/-- Theorem 2.3 -/
theorem theorem2_3 (A : Matrix n n R) (i j : n) :
    rayleighDiff i j A.detpoly = A.mvCharmatrix.adjugate i j * A.mvCharmatrix.adjugate j i := by
  sorry

end
