/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import LEAN_Warmup.ClaudeMathlib

/-!
# Polynomials as differential operators

A polynomial `p` acts on `MvPolynomial σ R` by substituting `xᵢ ↦ ∂ᵢ`. We call the result
`p(∂)`. The higher derivatives of the paper are `∂_S f = (∏_{i ∈ S} xᵢ)(∂) f`. In general,
`∂^s f = (x^s)(∂) f`.

## Main definitions

* `MvPolynomial.aevalOfCommute x hx`: evaluates at pairwise commuting elements `x i` of a
  possibly noncommutative `R`-algebra. **MISSING** from Mathlib, which only has the
  univariate `Polynomial.aeval` for noncommutative targets.
* `MvPolynomial.pderivOp : MvPolynomial σ R →ₐ[R] Module.End R (MvPolynomial σ R)` sends
  `p ↦ p(∂)`, with `X i ↦ pderiv i`.

## Main results

* `coeff_pderiv_iterate`, `coeff_pderivOp_monomial`: `[x^t] ∂^s f = ∏ᵢ (tᵢ+sᵢ)^{\underline{sᵢ}}
  [x^{t+s}] f`, which uses falling factorials (`Nat.descFactorial`). Compare the univariate
  `Polynomial.coeff_iterate_derivative`.
* `coeff_pderivOp_prod_X`: `[x^t] ∂_S f = ∏_{i ∈ S} (tᵢ+1) · [x^{t+S}] f`.
* `constantCoeff_pderivOp_prod_X`: `(∂_S f)|_{x=0} = [x^S] f`. This holds for any `f` and gives
  the coefficient-extraction step behind "same fiber ⟺ `f_A = f_B`".
* `constantCoeff_pderivOp_apply_monomial`: `(p(∂) x^s)|_{x=0} = s! · [x^s] p` (apolarity).
* `pderivOp_injective`: `p ↦ p(∂)` is injective when `R` is a domain of characteristic `0`.
* `pderivOp_prod_X_mem_supported`, `IsMultiaffine.pderivOp_prod_X`: for multiaffine `f`,
  `∂_S f` is multiaffine and free of the variables in `S`.
* `Matrix.pderivOp_detPoly` (**TODO**): `∂_S f_A = det (diag(x) + A)[Sᶜ, Sᶜ]`. It implies
  `Matrix.coeff_detPoly` (see `Matrix.coeff_detPoly_of_pderivOp`).

## What Mathlib has

* `MvPolynomial.pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)`
  (`Mathlib/Algebra/MvPolynomial/PDeriv.lean`). Related lemmas are `coeff_pderiv`,
  `pderiv_monomial`, `pderiv_comm`, `commute_pderiv` (a `Function.Commute`), `pderiv_map`,
  and `pderiv_rename`.
* `MvPolynomial.mkDerivation`/`mkDerivationEquiv` (`.../MvPolynomial/Derivation.lean`)
  identify derivations with `σ → A`. Together with the `Module` structure on `Derivation`,
  these give first-order operators `∑ aᵢ ∂ᵢ`. `Derivation`s are closed under the Lie
  bracket (the `LieRing` instance in `Mathlib/RingTheory/Derivation/Lie.lean`) but not under
  composition. A composite of derivations is only a linear map, so higher-order operators live
  in `Module.End R (MvPolynomial σ R)`.
* Univariate: `Polynomial.derivative` (a `LinearMap`), `Polynomial.coeff_iterate_derivative`,
  `Polynomial.hasseDeriv` with `factorial_smul_hasseDeriv`, `hasseDeriv_comp`, and
  `hasseDeriv_mul` (Leibniz), plus `Polynomial.taylor`.
* `MvPowerSeries.pderiv` and Euler's identity (`Mathlib/RingTheory/MvPolynomial/EulerIdentity`).
* Mathlib has **no** multivariate iterated or Hasse derivatives. It also has no Weyl algebra or
  ring of differential operators, and no `MvPolynomial` evaluation at commuting elements of a
  noncommutative algebra. The last one is easy to build from `Algebra.isMulCommutative_adjoin`
  together with the scoped instance `IsMulCommutative → CommSemiring` (see note
  [commutative subobjects]). That is how `aevalOfCommute` is defined.
* The project's computable `CMvPolynomial.pderiv` matches `MvPolynomial.pderiv` via
  `CMvPolynomial.equiv_pderiv`.

## Design notes

* **Why an `AlgHom`.** `pderivOp` gets linearity in `p`, `(pq)(∂) = p(∂) ∘ q(∂)` (`map_mul`),
  `map_pow`, and `AlgHom.commutes` for free. Do not phrase `∂_S` as a product of `pderiv i`'s.
  Neither `Finset.prod` nor `Finsupp.prod` works in the noncommutative `Module.End`. The
  alternative `Finset.noncommProd` makes every statement carry commutativity proofs, and
  iterating along a `List` makes statements depend on the order.
* **No `AlgEquiv`.** The target `Module.End` is far bigger than the image. In characteristic
  `0`, `pderivOp_injective` and `AlgEquiv.ofInjective` identify `MvPolynomial σ R` with the
  constant-coefficient differential operators (`pderivOp.range`). In characteristic `p`,
  `pderivOp (X i ^ p) = 0`, so it is not injective.
* **Hasse derivatives** `D^{(s)} = ∂^s / s!` are the characteristic-free alternative
  (`Polynomial.hasseDeriv`). They satisfy `D^{(s)} D^{(t)} = C(s+t, s) D^{(s+t)}`, so they form a
  divided-power algebra rather than the image of an `AlgHom` from `MvPolynomial`. The paper
  only differentiates multiaffine polynomials along squarefree monomials `x^S`, where
  `∂_S = D^{(S)}`. In that case the factor `∏ (tᵢ + 1)` in `coeff_pderivOp_prod_X` is `1` on
  the relevant coefficients, so no Hasse derivatives are needed here. A Mathlib version could
  define `MvPolynomial.hasseDeriv s` coefficientwise, as `Polynomial.hasseDeriv` is, with
  `s.prod (fun _ k ↦ k !) • hasseDeriv s = pderivOp (monomial s 1)`.
* Possible further API: `pderivOp_monomial_apply_monomial`, `pderivOp_map`, `pderivOp_rename`,
  the Leibniz rule `∂_S (fg) = ∑_{T ⊆ S} ∂_T f · ∂_{S∖T} g`, and the multiaffine Taylor
  expansion `f = ∑_S x^S (∂_S f)|_{x=0}` (stated with `setZero`).

## Dictionary

| paper | Lean |
|---|---|
| `∂_S f`, `∂^{|S|} f / ∏_{i∈S} ∂xᵢ` | `pderivOp (∏ i ∈ S, X i) f` |
| `∂^s f` (multi-index) | `pderivOp (monomial s 1) f` |
| `∂ᵢ^k f` | `pderivOp (X i ^ k) f`, or `(pderiv i)^[k] f` (`pderivOp_X_pow`) |
| `p(∂) f` | `pderivOp p f` |
-/

@[expose] public noncomputable section

open MvPolynomial

section Exponent

variable {σ : Type*}

@[simp]
theorem Finset.exponent_empty : (∅ : Finset σ).exponent = 0 := by
  simp [Finset.exponent]

theorem Finset.exponent_insert [DecidableEq σ] {a : σ} {S : Finset σ} (ha : a ∉ S) :
    (insert a S).exponent = Finsupp.single a 1 + S.exponent :=
  Finset.sum_insert ha

theorem Finset.exponent_apply [DecidableEq σ] (S : Finset σ) (i : σ) :
    S.exponent i = if i ∈ S then 1 else 0 := by
  simp [Finset.exponent, Finsupp.finsetSum_apply, Finsupp.single_apply]

end Exponent

namespace MvPolynomial

variable {R σ A : Type*} [CommSemiring R]

section AevalOfCommute

variable [Semiring A] [Algebra R A]

open scoped IsMulCommutative in
/-- Evaluate at a family of pairwise commuting elements of a possibly noncommutative algebra. -/
def aevalOfCommute (x : σ → A) (hx : Pairwise fun i j ↦ Commute (x i) (x j)) :
    MvPolynomial σ R →ₐ[R] A :=
  have : IsMulCommutative (Algebra.adjoin R (Set.range x)) :=
    Algebra.isMulCommutative_adjoin R <| by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
      exact hx fun hij ↦ h (hij ▸ rfl)
  (Algebra.adjoin R (Set.range x)).val.comp
    (aeval fun i ↦ ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩)

variable {x : σ → A} {hx : Pairwise fun i j ↦ Commute (x i) (x j)}

@[simp]
theorem aevalOfCommute_X (i : σ) : aevalOfCommute (R := R) x hx (X i) = x i := by
  simp [aevalOfCommute]

end AevalOfCommute

/-- `p ↦ p(∂)`: the differential operator obtained by substituting `xᵢ ↦ ∂ᵢ`. -/
def pderivOp : MvPolynomial σ R →ₐ[R] Module.End R (MvPolynomial σ R) :=
  aevalOfCommute (fun i ↦ (pderiv i).toLinearMap) fun i j _ ↦
    LinearMap.ext fun p ↦ pderiv_comm i j p

@[simp]
theorem pderivOp_X (i : σ) : pderivOp (X i : MvPolynomial σ R) = (pderiv i).toLinearMap :=
  aevalOfCommute_X i

theorem pderivOp_mul_apply (p q f : MvPolynomial σ R) :
    pderivOp (p * q) f = pderivOp p (pderivOp q f) := by
  rw [map_mul, Module.End.mul_apply]

theorem pderivOp_X_pow (i : σ) (k : ℕ) :
    ⇑(pderivOp (X i ^ k : MvPolynomial σ R)) = (pderiv i)^[k] := by
  rw [map_pow, pderivOp_X, Module.End.coe_pow]
  rfl

theorem coeff_pderiv_iterate (i : σ) (k : ℕ) (f : MvPolynomial σ R) (t : σ →₀ ℕ) :
    ((pderiv i)^[k] f).coeff t =
      (t i + k).descFactorial k * f.coeff (t + Finsupp.single i k) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', coeff_pderiv, ih, add_assoc, ← Finsupp.single_add,
      Finsupp.add_apply, Finsupp.single_eq_same, Nat.descFactorial_succ, add_comm 1 k,
      show t i + (k + 1) - k = t i + 1 by omega, show t i + 1 + k = t i + (k + 1) by omega]
    push_cast
    ring

theorem coeff_pderivOp_monomial (s : σ →₀ ℕ) (f : MvPolynomial σ R) (t : σ →₀ ℕ) :
    (pderivOp (monomial s 1) f).coeff t =
      (s.prod fun i k ↦ (t i + k).descFactorial k : ℕ) * f.coeff (t + s) := by
  classical
  induction s using Finsupp.induction generalizing t with
  | zero => simp
  | single_add a b s ha hb ih =>
    rw [monomial_single_add, pderivOp_mul_apply, pderivOp_X_pow, coeff_pderiv_iterate, ih,
      Finsupp.prod_add_index_of_disjoint (by
        rw [Finsupp.support_single _ hb]; exact Finset.disjoint_singleton_left.mpr ha),
      Finsupp.prod_single_index (by simp), add_assoc]
    have : (s.prod fun i k ↦ ((t + Finsupp.single a b) i + k).descFactorial k) =
        s.prod fun i k ↦ (t i + k).descFactorial k :=
      Finsupp.prod_congr fun i hi ↦ by
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (ne_of_mem_of_not_mem hi ha), add_zero]
    rw [this]
    push_cast
    ring

theorem constantCoeff_pderivOp_monomial (s : σ →₀ ℕ) (f : MvPolynomial σ R) :
    constantCoeff (pderivOp (monomial s 1) f) = (s.prod fun _ k ↦ k.factorial : ℕ) * f.coeff s := by
  simp [constantCoeff_eq, coeff_pderivOp_monomial, Nat.descFactorial_self]

theorem coeff_pderivOp_prod_X (S : Finset σ) (f : MvPolynomial σ R) (t : σ →₀ ℕ) :
    (pderivOp (∏ i ∈ S, X i) f).coeff t = (∏ i ∈ S, (t i + 1 : R)) * f.coeff (t + S.exponent) := by
  classical
  induction S using Finset.induction_on generalizing t with
  | empty => simp [Finset.exponent]
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, pderivOp_mul_apply, pderivOp_X, Derivation.coeFn_coe,
      coeff_pderiv, ih, Finset.prod_insert ha, Finset.exponent_insert ha, add_assoc]
    have : ∏ i ∈ S, (((t + Finsupp.single a 1 : σ →₀ ℕ) i : R) + 1) = ∏ i ∈ S, (t i + 1 : R) :=
      Finset.prod_congr rfl fun i hi ↦ by
        rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (ne_of_mem_of_not_mem hi ha), add_zero]
    rw [this]
    ring

theorem constantCoeff_pderivOp_prod_X (S : Finset σ) (f : MvPolynomial σ R) :
    constantCoeff (pderivOp (∏ i ∈ S, X i) f) = f.coeff S.exponent := by
  simp [constantCoeff_eq, coeff_pderivOp_prod_X]

theorem constantCoeff_pderivOp_apply_monomial (p : MvPolynomial σ R) (s : σ →₀ ℕ) :
    constantCoeff (pderivOp p (monomial s 1)) = (s.prod fun _ k ↦ k.factorial : ℕ) * p.coeff s := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_monomial, map_smul, LinearMap.smul_apply,
      smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_pderivOp_monomial, coeff_smul,
      coeff_monomial, coeff_monomial]
    rcases eq_or_ne u s with rfl | h
    · simp [mul_comm]
    · simp [h, h.symm]
  | add p q hp hq => simp [hp, hq, mul_add]

theorem pderivOp_injective [IsDomain R] [CharZero R] :
    Function.Injective (pderivOp : MvPolynomial σ R →ₐ[R] _) := by
  intro p q h
  ext s
  have := constantCoeff_pderivOp_apply_monomial p s
  rw [h, constantCoeff_pderivOp_apply_monomial] at this
  refine (mul_left_cancel₀ ?_ this).symm
  exact Nat.cast_ne_zero.mpr (Finsupp.prod_ne_zero_iff.mpr fun _ _ ↦ Nat.factorial_ne_zero _)

end MvPolynomial

/-! ### Multiaffine polynomials and `f_A` -/

section Multiaffine

variable {R n : Type*} [CommRing R]

theorem coeff_add_exponent_ne_zero_of_coeff_pderivOp_ne_zero {S : Finset n}
    {f : MvPolynomial n R} {t : n →₀ ℕ} (ht : (pderivOp (∏ i ∈ S, X i) f).coeff t ≠ 0) :
    f.coeff (t + S.exponent) ≠ 0 := by
  rw [coeff_pderivOp_prod_X] at ht
  exact right_ne_zero_of_mul ht

/-- For multiaffine `f`, `∂_S f` does not involve the variables in `S`. -/
theorem pderivOp_prod_X_mem_supported {f : MvPolynomial n R} (hf : IsMultiaffine f)
    (S : Finset n) : pderivOp (∏ i ∈ S, X i) f ∈ supported R (↑S : Set n)ᶜ := by
  classical
  rw [mem_supported_iff_degreeOf_eq_zero]
  intro i hi
  rw [Set.notMem_compl_iff, Finset.mem_coe] at hi
  rw [← Nat.le_zero, degreeOf_le_iff]
  intro t ht
  have h := monomial_le_degreeOf i
    (mem_support_iff.mpr (coeff_add_exponent_ne_zero_of_coeff_pderivOp_ne_zero
      (mem_support_iff.mp ht)))
  simp only [Finsupp.add_apply, Finset.exponent_apply, hi, ite_true] at h
  have := hf i
  omega

theorem IsMultiaffine.pderivOp_prod_X {f : MvPolynomial n R} (hf : IsMultiaffine f)
    (S : Finset n) : IsMultiaffine (pderivOp (∏ i ∈ S, X i) f) := by
  intro i
  rw [degreeOf_le_iff]
  intro t ht
  have h := monomial_le_degreeOf i
    (mem_support_iff.mpr (coeff_add_exponent_ne_zero_of_coeff_pderivOp_ne_zero
      (mem_support_iff.mp ht)))
  rw [Finsupp.add_apply] at h
  have := hf i
  omega

/-- The coefficient of `∏_{i ∈ S} xᵢ` is `(∂_S f)|_{x = 0}`. -/
theorem coeff_exponent_eq_constantCoeff_pderivOp (f : MvPolynomial n R) (S : Finset n) :
    f.coeff S.exponent = constantCoeff (pderivOp (∏ i ∈ S, X i) f) :=
  (constantCoeff_pderivOp_prod_X S f).symm

variable [Fintype n] [DecidableEq n]

/-- **TODO** (generalized Jacobi formula): `∂_S f_A` is the principal minor of `diag(x) + A` on
`Sᶜ`. The case `S = {i}` is `Matrix.pderiv_detPoly`. Hint: induct on `S`; `xᵢ` appears only in
the `(i, i)` entry, so expanding along row `i` (`det_eq_sum_mul_adjugate_row`) gives
`∂ᵢ det M = det M[{i}ᶜ, {i}ᶜ]`. -/
theorem Matrix.pderivOp_detPoly (A : Matrix n n R) (S : Finset n) :
    pderivOp (∏ i ∈ S, X i) A.detpoly = A.mvCharmatrix.principalMinor Sᶜ := by
  induction S using Finset.induction with
  | empty => 
    simp only [Finset.prod_empty, map_one, Module.End.one_apply, Finset.compl_empty]
    ext m
    rw [Matrix.principalMinor, Matrix.principalSubmatrix]
    sorry
  | insert a S hS h => 
    sorry
    
#check Matrix.detRowAlternating
#check Finset.induction

omit [Fintype n] in
theorem Matrix.constantCoeff_principalMinor_mvCharmatrix (A : Matrix n n R) (S : Finset n) :
    constantCoeff (A.mvCharmatrix.principalMinor S) = A.principalMinor S := by
  rw [principalMinor, RingHom.map_det, principalMinor]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [mvCharmatrix, principalSubmatrix, h]

/-- `Matrix.coeff_detPoly` follows from `Matrix.pderivOp_detPoly`. -/
theorem Matrix.coeff_detPoly_of_pderivOp (A : Matrix n n R) (S : Finset n) :
    A.detpoly.coeff S.exponent = A.principalMinor Sᶜ := by
  rw [coeff_exponent_eq_constantCoeff_pderivOp, pderivOp_detPoly,
    constantCoeff_principalMinor_mvCharmatrix]

end Multiaffine

end
