/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib
public meta import Mathlib.Algebra.DirectSum.Ring

/-!
# Computable multivariate polynomials

A direct-sum computation model, following Mathlib's wiki on computation models for
polynomials. Exponents and coefficients use `DFinsupp`; the noncomputable algebra
equivalence transfers proofs to `MvPolynomial` without entering executable code.

Use exact computable coefficients such as `ℚ` or `ZMod p`. Arithmetic accumulates support
bounds: `normalize` discards zero terms and rebuilds the outer bound when needed. The `Repr`
instance uses unsafe quotient extraction only for display; the algorithms and proofs do not.

Substitution and differentiation have correctness lemmas. Matrix operations initially use
Mathlib's determinant and adjugate algorithms, suitable for small examples. This model does
not yet provide polynomial division or factorization.
-/
@[expose] public section

open scoped DirectSum

variable (σ R : Type*) [DecidableEq σ] [CommSemiring R]

/-- Direct sums with computable exponent vectors and coefficients. -/
abbrev CMvPolynomial := ⨁ _ : (Π₀ _ : σ, ℕ), R

variable {σ R}

/-- A polynomial variable. -/
abbrev CMvPolynomial.X (i : σ) : CMvPolynomial σ R
  := .single (.single i 1) 1

/-- Display only nonzero terms. Term order is unspecified. -/
unsafe instance [DecidableEq R] [Repr σ] [Repr R] : Repr (CMvPolynomial σ R) where
  reprPrec p _ := repr ((p.support'.unquot.1.unquot.dedup.filter (fun s => p s ≠ 0)).map fun s =>
    ((s.support'.unquot.1.unquot.dedup.filter (fun i => s i ≠ 0)).map (fun i => (i, s i)), p s))

/-- The bridge to Mathlib polynomials; algorithms should stay in `CMvPolynomial`. -/
noncomputable def cMvPolynomialEquiv : (CMvPolynomial σ R) ≃ₐ[R] (MvPolynomial σ R) := by
  classical
  exact addMonoidAlgebraAlgEquivDirectSum.symm.trans
    (AddMonoidAlgebra.domCongr R R finsuppAddEquivDFinsupp.symm)

namespace CMvPolynomial

/-- A constant polynomial. -/
abbrev C (r : R) : CMvPolynomial σ R := .single 0 r

@[simp] theorem equiv_single (s : Π₀ _ : σ, ℕ) (r : R) :
    cMvPolynomialEquiv (.single s r) = MvPolynomial.monomial s.toFinsupp r := by
  classical
  simp [cMvPolynomialEquiv, DirectSum.toAddMonoidAlgebra,
    AddMonoidAlgebra.domCongr, AddMonoidAlgebra.mapDomainRingEquiv,
    MvPolynomial.monomial]

theorem equiv_C (r : R) :
    cMvPolynomialEquiv (C (σ := σ) r) = MvPolynomial.C r := by
  simp [C]

theorem equiv_X (i : σ) :
    cMvPolynomialEquiv (X (R := R) i) = MvPolynomial.X i := by
  simp [X, MvPolynomial.X]

/-- Rebuild the outer support bound after arithmetic, discarding zero coefficients. -/
def normalize [DecidableEq R] (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  p.support.sum fun s => .single s (p s)

@[simp] theorem normalize_eq [DecidableEq R] (p : CMvPolynomial σ R) : normalize p = p := by
  exact DFinsupp.sum_single

/-- Substitute polynomials for variables. -/
def bind (x : σ → CMvPolynomial σ R) : CMvPolynomial σ R →+ CMvPolynomial σ R :=
  DirectSum.toAddMonoid (fun s =>
    { toFun := fun r => C r * s.prod (fun i n => x i ^ n)
      map_zero' := by simp [C]
      map_add' := by intro a b; simp [C, add_mul, DFinsupp.single_add] })

@[simp] theorem bind_single (x : σ → CMvPolynomial σ R) (s : Π₀ _ : σ, ℕ) (r : R) :
    bind x (.single s r) = C r * s.prod (fun i n => x i ^ n) := by
  unfold bind DirectSum.toAddMonoid
  rw [DFinsupp.liftAddHom_apply_single]
  rfl

@[simp] theorem equiv_bind (x : σ → CMvPolynomial σ R) (p : CMvPolynomial σ R) :
    cMvPolynomialEquiv (bind x p) =
      MvPolynomial.aeval (fun i => cMvPolynomialEquiv (x i)) (cMvPolynomialEquiv p) := by
  classical
  induction p using DirectSum.induction_on with
  | zero => simp [bind]
  | of s r =>
    change cMvPolynomialEquiv (bind x (.single s r)) =
      MvPolynomial.aeval _ (cMvPolynomialEquiv (.single s r))
    rw [bind_single, map_mul, equiv_C, equiv_single, MvPolynomial.aeval_monomial]
    simp only [map_dfinsuppProd, map_pow, MvPolynomial.algebraMap_eq]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Set one variable to zero. -/
def setZero (i : σ) (p : CMvPolynomial σ R) : CMvPolynomial σ R :=
  bind (fun j => if j = i then 0 else X j) p

/-- Formal partial derivative, computed term by term. -/
def pderiv (i : σ) : CMvPolynomial σ R →+ CMvPolynomial σ R :=
  DirectSum.toAddMonoid fun s =>
    { toFun := fun r => .single (s - .single i 1) (r * (s i : R))
      map_zero' := by simp
      map_add' := by intro a b; simp [add_mul, DFinsupp.single_add] }

@[simp] theorem pderiv_single (i : σ) (s : Π₀ _ : σ, ℕ) (r : R) :
    pderiv i (.single s r) = .single (s - .single i 1) (r * ↑(s i)) := by
  unfold pderiv DirectSum.toAddMonoid
  rw [DFinsupp.liftAddHom_apply_single]
  rfl

@[simp] theorem equiv_pderiv (i : σ) (p : CMvPolynomial σ R) :
    cMvPolynomialEquiv (pderiv i p) = MvPolynomial.pderiv i (cMvPolynomialEquiv p) := by
  classical
  induction p using DirectSum.induction_on with
  | zero => simp [pderiv]
  | of s r =>
    change cMvPolynomialEquiv (pderiv i (.single s r)) =
      MvPolynomial.pderiv i (cMvPolynomialEquiv (.single s r))
    rw [pderiv_single, equiv_single, equiv_single, MvPolynomial.pderiv_monomial]
    congr 2
    ext j
    simp [Finsupp.single_apply]
  | add p q hp hq => simp [hp, hq]

section Ring
variable {S : Type*} [CommRing S]

/-- Rayleigh difference. -/
def rayleighDiff (i j : σ) (p : CMvPolynomial σ S) : CMvPolynomial σ S :=
  pderiv i p * pderiv j p - p * pderiv i (pderiv j p)

/-- The degree-one resultant used in the fiber construction. -/
def resultant (i : σ) (p q : CMvPolynomial σ S) : CMvPolynomial σ S :=
  setZero i p * pderiv i q - setZero i q * pderiv i p

variable [Fintype σ]

/-- The computable matrix `diag(X) + A`. -/
def charmatrix (A : Matrix σ σ S) : Matrix σ σ (CMvPolynomial σ S) :=
  Matrix.diagonal X + A.map C

/-- A computable determinantal polynomial. -/
def detPoly (A : Matrix σ σ S) : CMvPolynomial σ S := (charmatrix A).det

/-- A computable polynomial adjugate. -/
def adjPoly (A : Matrix σ σ S) : Matrix σ σ (CMvPolynomial σ S) :=
  (charmatrix A).adjugate

/-- Executable comparison of determinantal polynomials. -/
def sameFiber [DecidableEq S] (A B : Matrix σ σ S) : Bool :=
  decide (detPoly A = detPoly B)

end Ring
end CMvPolynomial

end
