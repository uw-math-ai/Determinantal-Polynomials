/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib
public import DetPoly.DesnanotJacobi

/-!
# Theorem 2.3: Rayleigh differences of determinantal polynomials

`Δᵢⱼ(f_A) = G_ij G_ji`, where `f_A = det(diag(x) + A)` and `G = adj(diag(x) + A)`
([arXiv:2309.00806], Thm 2.3). The proof combines `∂ᵢ∂ⱼ f_A = det (diag(x) + A)[{i,j}ᶜ]` with
the Desnanot–Jacobi identity `Matrix.adjugate_mul_adjugate_sub_adjugate_mul_adjugate`.
-/
public noncomputable section

namespace Theorem23

open MvPolynomial Matrix

variable {n R : Type*} [CommRing R] [DecidableEq n] [Fintype n]

/-- The Rayleigh difference `Δᵢⱼ(f) = ∂ᵢf ∂ⱼf - f ∂ᵢ∂ⱼf`. -/
def rayleighDiff (i j : n) (f : MvPolynomial n R) : MvPolynomial n R :=
  pderiv i f * pderiv j f - f * pderiv i (pderiv j f)

/-- `diag(x₁,…,xₙ) + A`. -/
abbrev _root_.Matrix.mvCharmatrix (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  diagonal X + A.map C

/-- The determinantal polynomial `f_A = det(diag(x) + A)`. -/
abbrev _root_.Matrix.detPoly (A : Matrix n n R) : MvPolynomial n R :=
  A.mvCharmatrix.det

/-- The principal submatrix `A[S, S]`. -/
abbrev _root_.Matrix.principalSubmatrix (A : Matrix n n R) (S : Finset n) : Matrix S S R :=
  A.submatrix (↑) (↑)

theorem pderiv_eq (A : Matrix n n R) (i : n) :
    (pderiv i A.detPoly) = (A.mvCharmatrix.principalSubmatrix {i}ᶜ).det := by
  sorry

theorem iterate_pderiv_eq (A : Matrix n n R) {i j : n} (hneq : i ≠ j) :
    (pderiv i (pderiv j A.detPoly)) = (A.mvCharmatrix.principalSubmatrix {i, j}ᶜ).det := by
  sorry

#check adjugate_mul_adjugate_sub_adjugate_mul_adjugate
/-- Theorem 2.3 -/
theorem rayleighDiff_detPoly (A : Matrix n n R) (i j : n) :
    rayleighDiff i j A.detPoly = A.mvCharmatrix.adjugate i j * A.mvCharmatrix.adjugate j i := by
  sorry


end Theorem23

end
