/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaoda Ji, Joe Rogge, Nhi Bach, David Javnozon, Anders Lewis, Liron Shani, Grant Yang
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib

/-!
# Determinantal polynomials and cuts

Definitions used by Theorem 2.3 and Lemma 4.3 of Al Ahmadieh (2023).
-/
@[expose] public section
open MvPolynomial Matrix

variable {n R : Type*}

/-- The submatrix of `A` with rows in `S` and columns in `T`. -/
abbrev Matrix.setSubmatrix {m : Type*} (A : Matrix n m R) (S : Set n) (T : Set m)
    : Matrix S T R :=
  A.submatrix (↑) (↑)

variable [DecidableEq n] [Fintype n]

section CommRing
variable [CommRing R]

/-- The Rayleigh difference `Δᵢⱼ(f) = ∂ᵢf ∂ⱼf - f ∂ᵢ∂ⱼf`. -/
noncomputable
def rayleighDiff (i j : n) (f : MvPolynomial n R) : MvPolynomial n R :=
  pderiv i f * pderiv j f - f * pderiv i (pderiv j f)

/-- `diag(x₁,…,xₙ) + A`. -/
noncomputable
abbrev Matrix.mvCharmatrix (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  diagonal X + A.map C

/-- The determinantal polynomial `f_A = det(diag(x) + A)`. -/
noncomputable
abbrev Matrix.detpoly (A : Matrix n n R) : MvPolynomial n R :=
  A.mvCharmatrix.det

/-- The principal minor `A_S`. -/
abbrev Matrix.principalMinor (A : Matrix n n R) (S : Finset n) : R :=
  (A.setSubmatrix S S).det


omit [Fintype n] in
/-- Principal submatrices of `diag(x) + A` along an injective `e` are `diag(x ∘ e) + A[e, e]`. -/
theorem Matrix.mvCharmatrix_submatrix {m : Type*} [DecidableEq m] (A : Matrix n n R)
    {e : m → n} (he : e.Injective) :
    A.mvCharmatrix.submatrix e e = diagonal (fun l ↦ X (e l)) + (A.submatrix e e).map C := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, he.ne hab]

/-- Expansion of `det(diag(x) + A)` by multilinearity in the rows: choose the row `xᵢ eᵢ` for
`i ∈ S` and the row of `A` otherwise. Compare `Matrix.coeff_det_one_add_X_smul_eq_sum_minors`. -/
theorem Matrix.det_diagonal_add (x : n → R) (A : Matrix n n R) :
    (diagonal x + A).det = ∑ S : Finset n, (∏ i ∈ S, x i) * A.principalMinor Sᶜ := by
  let D := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap
  change D ((diagonal x).row + A.row) = _
  rw [D.map_add_univ]
  refine Finset.sum_congr rfl (fun S _ ↦ ?_)
  have h : S.piecewise (diagonal x).row A.row =
      S.piecewise (fun i ↦ x i • S.piecewise (1 : Matrix n n R).row A.row i)
        (S.piecewise (1 : Matrix n n R).row A.row) := by
    ext i j
    by_cases hi : i ∈ S <;> simp [hi, diagonal_apply, one_apply]
  rw [h, D.map_piecewise_smul, smul_eq_mul, ← Finset.piecewise_compl]
  exact congrArg _ (det_piecewise_one_eq_submatrix_det A Sᶜ)

/-- `f_A = ∑_S A_{Sᶜ} ∏_{i ∈ S} xᵢ`. -/
theorem Matrix.detpoly_eq_sum (A : Matrix n n R) :
    A.detpoly =
      ∑ S : Finset n, monomial (∑ i ∈ S, Finsupp.single i 1) (A.principalMinor Sᶜ) := by
  rw [detpoly, mvCharmatrix, det_diagonal_add]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [monomial_sum_index, mul_comm]
  exact congrArg₂ _ (RingHom.map_det C _).symm rfl

/-- `f_A` is multiaffine: it has degree at most `1` in each variable. -/
theorem Matrix.detpoly_mem_restrictDegree (A : Matrix n n R) :
    A.detpoly ∈ restrictDegree n R 1 :=
  detpoly_eq_sum A ▸ Submodule.sum_mem _ fun S _ ↦ (mem_restrictDegree _ _ _).2 fun s hs i ↦ by
    rw [Finset.mem_singleton.1 (support_monomial_subset hs)]
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]; split_ifs <;> simp

omit [DecidableEq n] [Fintype n] in
theorem Finset.sum_single_one_injective :
    Function.Injective fun S : Finset n ↦ ∑ i ∈ S, Finsupp.single i (1 : ℕ) := by
  classical
  intro S T h
  ext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq'] at this
  split_ifs at this <;> simp_all

/-- The coefficient of `∏_{i ∈ S} xᵢ` in `f_A` is the complementary principal minor `A_{Sᶜ}`. -/
theorem Matrix.coeff_detpoly (A : Matrix n n R) (S : Finset n) :
    A.detpoly.coeff (∑ i ∈ S, Finsupp.single i 1) = A.principalMinor Sᶜ := by
  rw [detpoly_eq_sum, coeff_sum, Finset.sum_eq_single S]
  · simp
  · intro T _ hT
    rw [coeff_monomial, ite_eq_right_iff]
    exact fun h ↦ absurd (Finset.sum_single_one_injective h) hT
  · simp

/-- Two matrices have the same determinantal polynomial iff they have the same principal
minors. -/
theorem detpoly_eq_iff_principalMinor_eq (A B : Matrix n n R) :
    A.detpoly = B.detpoly ↔ A.principalMinor = B.principalMinor := by
  refine ⟨fun h ↦ funext fun S ↦ ?_, fun h ↦ by rw [detpoly_eq_sum, detpoly_eq_sum, h]⟩
  simpa [coeff_detpoly] using congrArg (fun p ↦ p.coeff (∑ i ∈ Sᶜ, Finsupp.single i 1)) h

end CommRing

end
