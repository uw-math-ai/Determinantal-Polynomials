/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.LEAN_Warmup.ClaudeMathlib

/-! -/
public noncomputable section

open MvPolynomial


variable {R 𝔽 n : Type*} [DecidableEq n] [Field 𝔽] [CommRing R]

#check eq_setZero_add_X_mul_pderiv

#check pderiv
#check modMonomial

theorem setZero_X {k : n} : (setZero k) (X k : MvPolynomial n R) = 0 := by
  rw [setZero_eq_modMonomial]
  simp

-- what is the correct way to phrase this? there's the nontriviality tactic right how does that work
-- also is this theorem in mathlib?
omit [DecidableEq n] in
theorem triviality [h : Subsingleton R] {f g : MvPolynomial n R} : f = g := by
  ext m
  exact h.allEq (f.coeff m) (g.coeff m)

theorem setZero_X_diff {p q : n}
    (h : p ≠ q) : (setZero p) (X q : MvPolynomial n R) = X q := by
  by_cases htriv : Subsingleton R
  · exact triviality
  push Not at htriv
  rw [setZero_eq_modMonomial]
  rw [← eq_modMonomial_single (p := X q) (q := 0) (r := X q) (by simp) ?_]
  rw [support_X]
  simp only [Finset.mem_singleton, forall_eq]
  rw [Finsupp.single_apply, ite_eq_right h.symm]

-- this proof seems like the wrong way to do this.
theorem setZero_comm {i j : n} {f : MvPolynomial n R} :
    setZero i (setZero j f) = setZero j (setZero i f) := by
  apply MvPolynomial.induction_on f
  · intro a; simp
  · intro p q h₁ h₂
    repeat rw [map_add]
    rw [h₁, h₂]
  · intro p q h
    rw [map_mul, map_mul (setZero i), h]
    rw [map_mul (setZero i), map_mul (setZero j)]
    by_cases hi : q = i
    · by_cases hj : i = j
      · rw [hj]
      · change i ≠ j at hj
        rw [hi, setZero_X_diff hj.symm, setZero_X]
        simp
    · change q ≠ i at hi
      rw [setZero_X_diff hi.symm]
      by_cases hj : q = j
      · rw [hj, setZero_X]; simp
      · change q ≠ j at hj
        rw [setZero_X_diff hj.symm, setZero_X_diff hi.symm]

-- idk, i also probably want that setZero commutes with pderiv for not equal.
theorem setZero_map {S} [CommRing S] {φ : R →+* S} {f : MvPolynomial n R} {i : n} :
    setZero i (map φ f) = map φ (setZero i f) := by
  sorry

theorem setZero_commute {i j : n} :
    Function.Commute (setZero (R := R) i) (setZero j) :=
  @setZero_comm _ _ _ _ i j


omit [DecidableEq n] in
/-- **Lemma 2.2** ([AV22, Prop. 2.2]). How we phrase it:
* "degree one in `xᵢ` and `xⱼ`" ↦ `f.degreeOf i ≤ 1`, `f.degreeOf j ≤ 1`;
* "`g ∈ 𝔽[x_k : k ≠ i]`" ↦ `g ∈ supported 𝔽 {i}ᶜ`;
* the factorization is an *equation in `MvPolynomial n 𝔽`*, `f = g * h`.

Proof sketch in Lean terms: apply `eq_setZero_add_X_mul_pderiv` twice to get
`f = a xᵢxⱼ + b xᵢ + c xⱼ + d` with `a b c d ∈ supported 𝔽 {i, j}ᶜ`. Then `Δᵢⱼ f = bc - ad`.
The step "`bc = ad` ⟹ common factorization" is a gcd argument in the UFD `MvPolynomial n 𝔽`
(Mathlib has the `UniqueFactorizationMonoid` instance; see also `gcd_mul_lcm`,
`exists_dvd_and_dvd_of_dvd_mul`). `mem_supported_of_dvd` keeps the `gcd`s in
`supported 𝔽 {i, j}ᶜ`. -/
theorem rayleighDiff_eq_zero_iff {f : MvPolynomial n 𝔽} {i j : n} (hij : i ≠ j)
    (hi : f.degreeOf i ≤ 1) (hj : f.degreeOf j ≤ 1) :
    rayleighDiff i j f = 0 ↔
      ∃ g ∈ supported 𝔽 ({i}ᶜ : Set n), ∃ h ∈ supported 𝔽 ({j}ᶜ : Set n), f = g * h := by
  classical
  constructor
  · intro h
    sorry
  · intro ⟨g, hg, h, ⟨hh, hf⟩⟩
    rw [eq_setZero_add_X_mul_pderiv hi, eq_setZero_add_X_mul_pderiv hj, hf, rayleighDiff]
    sorry




end
