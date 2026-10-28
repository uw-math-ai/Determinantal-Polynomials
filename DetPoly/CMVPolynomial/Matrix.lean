/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.CMVPolynomial
public import DetPoly.LEAN_Warmup.ClaudeMathlib

/-!
# Correctness of computable matrix polynomials

The executable definitions live in `CMvPolynomial`; the equivalence transports their
outputs to the project's mathematical definitions.
-/
public section

namespace CMvPolynomial

variable {σ R : Type*} [DecidableEq σ] [CommRing R]

@[simp] theorem equiv_setZero (i : σ) (p : CMvPolynomial σ R) :
    cMvPolynomialEquiv (setZero i p) = _root_.setZero i (cMvPolynomialEquiv p) := by
  simp only [setZero, equiv_bind, _root_.setZero]
  congr 2
  funext j
  by_cases h : j = i <;> simp [h, MvPolynomial.X]

@[simp] theorem equiv_rayleighDiff (i j : σ) (p : CMvPolynomial σ R) :
    cMvPolynomialEquiv (rayleighDiff i j p) =
      _root_.rayleighDiff i j (cMvPolynomialEquiv p) := by
  simp [rayleighDiff, _root_.rayleighDiff]

@[simp] theorem equiv_charmatrix (A : Matrix σ σ R) :
    (charmatrix A).map cMvPolynomialEquiv = A.mvCharmatrix := by
  ext i j : 2
  by_cases h : i = j <;> simp [charmatrix, Matrix.mvCharmatrix, MvPolynomial.X, h]

@[simp] theorem equiv_resultant (i : σ) (p q : CMvPolynomial σ R) :
    cMvPolynomialEquiv (resultant i p q) =
      _root_.res i (cMvPolynomialEquiv p) (cMvPolynomialEquiv q) := by
  simp [resultant, _root_.res]

variable [Fintype σ]

@[simp] theorem equiv_detPoly (A : Matrix σ σ R) :
    cMvPolynomialEquiv (detPoly A) = A.detPoly := by
  change cMvPolynomialEquiv.toRingHom (charmatrix A).det = A.mvCharmatrix.det
  rw [RingHom.map_det]
  exact congrArg Matrix.det (equiv_charmatrix A)

@[simp] theorem equiv_adjPoly (A : Matrix σ σ R) :
    (adjPoly A).map cMvPolynomialEquiv = A.adjPoly := by
  have h := cMvPolynomialEquiv.toRingHom.map_adjugate (charmatrix A)
  change (adjPoly A).map cMvPolynomialEquiv =
    ((charmatrix A).map cMvPolynomialEquiv).adjugate at h
  rw [equiv_charmatrix] at h
  exact h

/-- This certificate uses only the algebra equivalence, not the project's unfinished
principal-minor coefficient theorem. -/
theorem sameFiber_eq_true_iff_detPoly_eq [DecidableEq R] (A B : Matrix σ σ R) :
    sameFiber A B = true ↔ A.detPoly = B.detPoly := by
  simp only [sameFiber, decide_eq_true_eq]
  rw [← equiv_detPoly, ← equiv_detPoly]
  exact cMvPolynomialEquiv.injective.eq_iff.symm

end CMvPolynomial

end
