module

public import Mathlib
public import DetPoly.LEAN_Warmup.Anders.DesnanotJacobi

/-!
-/
public noncomputable section

namespace Theorem23

open MvPolynomial Matrix

variable {n R : Type*} [CommRing R] [DecidableEq n] [Fintype n]

def rayleighDiff (i j : n) (f : MvPolynomial n R) : MvPolynomial n R :=
  pderiv i f * pderiv j f - f * pderiv i (pderiv j f)

abbrev _root_.Matrix.mvCharmatrix (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  diagonal X + A.map C

abbrev _root_.Matrix.detPoly (A : Matrix n n R) : MvPolynomial n R :=
  A.mvCharmatrix.det

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
