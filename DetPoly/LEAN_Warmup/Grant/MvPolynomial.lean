/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.LEAN_Warmup.ClaudeMathlib

/-!
# `setZero` API and Lemma 2.2

API for `setZero k` (`p ↦ p |_{x_k = 0}`), and **Lemma 2.2** ([AV22, Prop. 2.2]): a
polynomial `f` affine in `xᵢ` and `xⱼ` has `Δᵢⱼ f = 0` iff `f = g * h` with `g` free of `xᵢ`
and `h` free of `xⱼ`.

## Main results

* `exists_eq_X_mul_X_add`: `f = a xᵢxⱼ + b xᵢ + c xⱼ + d` with `a b c d ∈ R[x_k : k ≠ i, j]`.
* `rayleighDiff_mul_eq_zero`: the "if" half of Lemma 2.2, over any `CommRing`.
* `rayleighDiff_eq_zero_iff`: Lemma 2.2, over any UFD.
-/

public noncomputable section

open MvPolynomial

variable {R n : Type*} [CommRing R]

/-! ### `setZero` -/

section SetZero

variable [DecidableEq n]

theorem setZero_X (k j : n) :
    setZero k (X j : MvPolynomial n R) = if j = k then 0 else X j := by
  simp [setZero, Function.update_apply]

@[simp]
theorem setZero_X_self (k : n) : setZero k (X k : MvPolynomial n R) = 0 := by
  simp [setZero_X]

@[simp]
theorem setZero_X_of_ne {j k : n} (h : j ≠ k) : setZero k (X j : MvPolynomial n R) = X j := by
  simp [setZero_X, h]

theorem setZero_C (k : n) (r : R) : setZero k (C r : MvPolynomial n R) = C r :=
  (setZero k).commutes r

theorem setZero_monomial (k : n) (s : n →₀ ℕ) (r : R) :
    setZero k (monomial s r) = if s k = 0 then monomial s r else 0 := by
  ext t
  rw [coeff_setZero, apply_ite (fun p : MvPolynomial n R ↦ p.coeff t), coeff_monomial]
  split_ifs <;> simp_all

theorem support_setZero_subset (k : n) (p : MvPolynomial n R) :
    (setZero k p).support ⊆ p.support := by
  intro t ht
  rw [mem_support_iff, coeff_setZero] at ht
  split_ifs at ht
  · exact mem_support_iff.mpr ht
  · exact absurd rfl ht

theorem degreeOf_setZero_le (j k : n) (p : MvPolynomial n R) :
    (setZero k p).degreeOf j ≤ p.degreeOf j :=
  degreeOf_le_iff.mpr fun _ ht ↦ monomial_le_degreeOf j (support_setZero_subset k p ht)

/-- `setZero k` does not introduce new variables. -/
theorem setZero_mem_supported_of_mem {s : Set n} {k : n} {p : MvPolynomial n R}
    (hp : p ∈ supported R s) : setZero k p ∈ supported R s :=
  mem_supported_of_degreeOf_le (degreeOf_setZero_le · k p) hp

theorem setZero_eq_self_iff {k : n} {p : MvPolynomial n R} :
    setZero k p = p ↔ p ∈ supported R ({k}ᶜ : Set n) :=
  ⟨fun h ↦ h ▸ setZero_mem_supported k p, setZero_of_mem_supported⟩

@[simp]
theorem setZero_setZero (k : n) (p : MvPolynomial n R) : setZero k (setZero k p) = setZero k p :=
  setZero_of_mem_supported (setZero_mem_supported k p)

theorem setZero_comm (i j : n) (p : MvPolynomial n R) :
    setZero i (setZero j p) = setZero j (setZero i p) := by
  ext t
  simp only [coeff_setZero]
  split_ifs <;> rfl

theorem setZero_commute (i j : n) :
    Function.Commute (setZero (R := R) i) (setZero j) :=
  setZero_comm i j

@[simp]
theorem pderiv_setZero_self (k : n) (p : MvPolynomial n R) : pderiv k (setZero k p) = 0 :=
  pderiv_eq_zero_of_mem_supported (setZero_mem_supported k p)

theorem pderiv_setZero_of_ne {i k : n} (h : i ≠ k) (p : MvPolynomial n R) :
    pderiv i (setZero k p) = setZero k (pderiv i p) := by
  ext t
  simp only [coeff_pderiv, coeff_setZero, Finsupp.add_apply, Finsupp.single_eq_of_ne h.symm,
    add_zero, ite_mul, zero_mul]

theorem setZero_map {S : Type*} [CommRing S] (φ : R →+* S) (k : n) (p : MvPolynomial n R) :
    setZero k (map φ p) = map φ (setZero k p) := by
  ext t
  simp only [coeff_setZero, coeff_map]
  split_ifs <;> simp

/-- `setZero k` really is "evaluate at `x_k = 0`". -/
theorem eval_setZero (x : n → R) (k : n) (p : MvPolynomial n R) :
    eval x (setZero k p) = eval (Function.update x k 0) p := by
  rw [setZero, aeval_eq_bind₁, eval, eval₂Hom_bind₁]
  congr 2
  funext j
  rcases eq_or_ne j k with rfl | h <;> simp [*]

end SetZero

/-! ### Lemma 2.2 -/

section Lemma22

/-- `f = a xᵢxⱼ + b xᵢ + c xⱼ + d` with `a b c d ∈ R[x_k : k ≠ i, j]`, namely `a = ∂ⱼ∂ᵢf`,
`b = (∂ᵢf)|_{xⱼ=0}`, `c = ∂ⱼ(f|_{xᵢ=0})` and `d = f|_{xᵢ=xⱼ=0}`. -/
theorem exists_eq_X_mul_X_add {f : MvPolynomial n R} {i j : n} (hi : f.degreeOf i ≤ 1)
    (hj : f.degreeOf j ≤ 1) :
    ∃ a ∈ supported R ({i, j}ᶜ : Set n), ∃ b ∈ supported R ({i, j}ᶜ : Set n),
    ∃ c ∈ supported R ({i, j}ᶜ : Set n), ∃ d ∈ supported R ({i, j}ᶜ : Set n),
      f = X i * X j * a + X i * b + X j * c + d := by
  classical
  have hPj := (degreeOf_setZero_le j i f).trans hj
  have hQj := (degreeOf_pderiv_le i j f).trans hj
  have hP := setZero_mem_supported i f
  have hQ := pderiv_mem_supported hi
  simp only [mem_supported_compl_pair_iff]
  refine ⟨_, ⟨pderiv_mem_supported_of_mem hQ, pderiv_mem_supported hQj⟩,
    _, ⟨setZero_mem_supported_of_mem hQ, setZero_mem_supported j _⟩,
    _, ⟨pderiv_mem_supported_of_mem hP, pderiv_mem_supported hPj⟩,
    _, ⟨setZero_mem_supported_of_mem hP, setZero_mem_supported j _⟩, ?_⟩
  linear_combination eq_setZero_add_X_mul_pderiv hi + eq_setZero_add_X_mul_pderiv hPj +
    X i * eq_setZero_add_X_mul_pderiv hQj

/-- In terms of the decomposition `exists_eq_X_mul_X_add`, `Δᵢⱼ f = bc - ad`. -/
theorem rayleighDiff_X_mul_X_add {i j : n} (hij : i ≠ j) {a b c d : MvPolynomial n R}
    (ha : a ∈ supported R ({i, j}ᶜ : Set n)) (hb : b ∈ supported R ({i, j}ᶜ : Set n))
    (hc : c ∈ supported R ({i, j}ᶜ : Set n)) (hd : d ∈ supported R ({i, j}ᶜ : Set n)) :
    rayleighDiff i j (X i * X j * a + X i * b + X j * c + d) = b * c - a * d := by
  rw [mem_supported_compl_pair_iff] at ha hb hc hd
  simp only [rayleighDiff, map_add, map_zero, Derivation.map_one_eq_zero, Derivation.leibniz,
    smul_eq_mul, pderiv_X_self, pderiv_X_of_ne hij, pderiv_X_of_ne hij.symm,
    pderiv_eq_zero_of_mem_supported, ha, hb, hc, hd]
  ring

/-- The "if" half of Lemma 2.2. It needs no degree hypotheses. -/
theorem rayleighDiff_mul_eq_zero {i j : n} {g h : MvPolynomial n R}
    (hg : g ∈ supported R ({i}ᶜ : Set n)) (hh : h ∈ supported R ({j}ᶜ : Set n)) :
    rayleighDiff i j (g * h) = 0 := by
  have hgij : pderiv i (pderiv j g) = 0 := by
    rw [pderiv_comm, pderiv_eq_zero_of_mem_supported hg, map_zero]
  simp only [rayleighDiff, Derivation.leibniz, smul_eq_mul, pderiv_eq_zero_of_mem_supported hg,
    pderiv_eq_zero_of_mem_supported hh, mul_zero, zero_add, add_zero, hgij]
  ring

/-- **Lemma 2.2** ([AV22, Prop. 2.2]). The paper assumes `i ≠ j` and works over a field. The
statement also holds for `i = j`, and the proof only needs `R` to be a UFD. Some such hypothesis
is necessary: over `ℤ[√-5]`, `f = 2xᵢxⱼ + (1+√-5)xᵢ + (1-√-5)xⱼ + 3` has `Δᵢⱼ f = 0` but does
not factor.

Proof: write `f = a xᵢxⱼ + b xᵢ + c xⱼ + d`, so `Δᵢⱼ f = bc - ad`. If `a ≠ 0`, split
`a = γα` with `γ ∣ b` and `α ∣ c`; then `f = (α xⱼ + β)(γ xᵢ + δ)`. If `a = 0`, then `b = 0`
or `c = 0`, and `f` itself is free of `xᵢ` or of `xⱼ`. -/
theorem rayleighDiff_eq_zero_iff [IsDomain R] [UniqueFactorizationMonoid R]
    {f : MvPolynomial n R} {i j : n} (hi : f.degreeOf i ≤ 1) (hj : f.degreeOf j ≤ 1) :
    rayleighDiff i j f = 0 ↔
      ∃ g ∈ supported R ({i}ᶜ : Set n), ∃ h ∈ supported R ({j}ᶜ : Set n), f = g * h := by
  classical
  refine ⟨fun hΔ ↦ ?_, fun ⟨g, hg, h, hh, hf⟩ ↦ hf ▸ rayleighDiff_mul_eq_zero hg hh⟩
  rcases eq_or_ne i j with rfl | hij
  · -- `Δᵢᵢ f = (∂ᵢf)²`, so `∂ᵢf = 0` and `f` is free of `xᵢ`.
    have h0 : pderiv i f = 0 := by
      simpa [rayleighDiff, pderiv_eq_zero_of_mem_supported (pderiv_mem_supported hi)] using hΔ
    refine ⟨f, ?_, 1, one_mem _, (mul_one f).symm⟩
    rw [eq_setZero_add_X_mul_pderiv hi, h0, mul_zero, add_zero]
    exact setZero_mem_supported i f
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := exists_eq_X_mul_X_add hi hj
  rw [rayleighDiff_X_mul_X_add hij ha hb hc hd, sub_eq_zero] at hΔ
  rw [mem_supported_compl_pair_iff] at ha hb hc hd
  have hXi : X i ∈ supported R ({j}ᶜ : Set n) := X_mem_supported.mpr hij
  have hXj : X j ∈ supported R ({i}ᶜ : Set n) := X_mem_supported.mpr hij.symm
  rcases eq_or_ne a 0 with rfl | ha0
  · rcases mul_eq_zero.mp (hΔ.trans (zero_mul d)) with rfl | rfl
    · exact ⟨X j * c + d, add_mem (mul_mem hXj hc.1) hd.1, 1, one_mem _, by ring⟩
    · exact ⟨1, one_mem _, X i * b + d, add_mem (mul_mem hXi hb.2) hd.2, by ring⟩
  obtain ⟨γ, α, ⟨β, rfl⟩, ⟨δ, rfl⟩, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul ⟨d, hΔ⟩
  have hd : d = β * δ := mul_left_cancel₀ ha0 (by linear_combination -hΔ)
  subst hd
  refine ⟨α * X j + β, add_mem (mul_mem ?_ hXj) ?_, γ * X i + δ, add_mem (mul_mem ?_ hXi) ?_,
    by ring⟩
  · exact mem_supported_of_mul_mem ha.1 (left_ne_zero_of_mul ha0)
  · exact mem_supported_of_mul_mem hb.1 (left_ne_zero_of_mul ha0)
  · exact mem_supported_of_mul_mem (mul_comm γ α ▸ ha.2) (right_ne_zero_of_mul ha0)
  · exact mem_supported_of_mul_mem hc.2 (right_ne_zero_of_mul ha0)

end Lemma22

end
