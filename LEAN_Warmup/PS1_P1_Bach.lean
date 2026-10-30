/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nhi Bach
-/

module

public import Mathlib

/-!
# Warmup: a matrix with a repeated row has determinant zero

Let `A` be a square matrix over a commutative ring `R`, and let `A^(i,j)` be
the matrix obtained from `A` by replacing row `j` with row `i` (where `i ≠ j`).
Then `det A^(i,j) = 0`.
-/
-- PS1

public section

namespace BachWarmup

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Problem 1(a): replacing row `j` of `A` with row `i` (for `i ≠ j`) gives a
matrix whose rows `i` and `j` are equal, so its determinant is zero. -/
theorem det_updateRow_eq_zero (A : Matrix ι ι R) {i j : ι} (hij : i ≠ j) :
    (A.updateRow j (A i)).det = 0 := by
  -- A matrix with two equal rows has determinant zero,
  -- so it suffices to show rows `i` and `j` agree.
  apply Matrix.det_zero_of_row_eq hij
  -- Row `j` is now row `i` of `A`, and row `i` is unchanged.
  rw [Matrix.updateRow_self, Matrix.updateRow_ne hij]
/-! ## Part (b) -/
/-- The adjugate, defined by cofactors exactly as in the problem:
entry `(i, j)` is `(-1)^(i+j)` times the determinant of `A` with
row `j` and column `i` removed. -/
def adj {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun i j =>
    (-1 : R) ^ (i + j : ℕ) * (A.submatrix j.succAbove i.succAbove).det

/-- Our cofactor definition agrees with Mathlib's `Matrix.adjugate`. -/
theorem adj_eq_adjugate {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    adj A = A.adjugate := by
  ext i j
  -- Mathlib's formula for the adjugate in terms of cofactors:
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  -- Unfold our definition; the two sides differ only by `i + j` vs `j + i`.
  simp only [adj, Matrix.of_apply]
  ring

/-- Problem 1(b): `A * adj A = det(A) • I`. -/
theorem mul_adj {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A * adj A = A.det • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
  rw [adj_eq_adjugate]
  exact Matrix.mul_adjugate A
/-! ## Part (c) -/
/-- Problem 1(c): `A` has a two-sided inverse with entries in `R`
if and only if `det A` is a unit in `R`. -/
theorem exists_inverse_iff_isUnit_det (A : Matrix ι ι R) :
    (∃ B : Matrix ι ι R, A * B = 1 ∧ B * A = 1) ↔ IsUnit A.det := by
  constructor
  · -- (⇒) If `A * B = 1`, then `det A * det B = det (A * B) = det 1 = 1`,
    -- so `det A` has an inverse in `R`.
    rintro ⟨B, hAB, -⟩
    exact isUnit_iff_exists_inv.mpr ⟨B.det, by rw [← Matrix.det_mul, hAB, Matrix.det_one]⟩
  · -- (⇐) If `det A` is a unit, take `B = A⁻¹`. Mathlib defines it as
    -- `(det A)⁻¹ • adjugate A`, so by part (b) it is a two-sided inverse.
    intro h
    exact ⟨A⁻¹, Matrix.mul_nonsing_inv A h, Matrix.nonsing_inv_mul A h⟩
end BachWarmup

end
