/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/

module

public import DetPoly.Basic
public import DetPoly.IrreducibleMatrix
public import DetPoly.DiagSimilar
public import Mathlib

/-!
# Definitions and statements for "The fiber of the principal minor map"

Definitions for [Al Ahmadieh, arXiv:2309.00806] and statements of its results leading to
Theorem 4.1. Tags used in docstrings:

* **TODO**: our proof, still `sorry`.
* **EXTERNAL**: a result cited from another paper, `sorry` for now.
* **MISSING**: Mathlib has nothing like it.
* **NAME ONLY**: Mathlib has the content in another form; the docstring says where.

## Conventions

* The index type is `n` with `[Fintype n] [DecidableEq n]`, not `Fin n`, and subsets are
  `Finset n`. The paper's signs like `(-1)^i` are absorbed into other factors (Lemma 4.3).
* Ring identities are stated over a `CommRing R`. Results using rank, division or unique
  factorization are stated over a field `𝔽`.
* All polynomials live in `MvPolynomial n R`. "Multiaffine" and "`g ∈ R[x_k : k ∈ s]`" are
  predicates (`IsMultiaffine`, `MvPolynomial.supported`), not separate types, so factors can be
  multiplied without `rename`.
* Families indexed by a subset (like `aᵢ` for `i ∈ X`) are total functions `n → _`, with
  hypotheses guarded by `i ∈ X`.

## Dictionary

| paper | Lean |
|---|---|
| `A = DBD⁻¹` or `A = DBᵀD⁻¹` | `DiagEquivalent A B` |
| `A_S` | `A.principalMinor S` |
| fiber of `A` under the principal minor map | `A.pmFiber` |
| `𝒟(n)` | `{A | A.HasTrivialFiber}` |
| `A` reducible / irreducible | `A.IsReducible` / `A.IsIrred` |
| `A` has a cut `X` | `A.HasCut X` |
| `diag(x₁,…,xₙ) + A` | `A.mvCharmatrix` |
| `f_A` | `A.detpoly` |
| `G = (diag(x) + A)^adj` | `A.adjPoly` |
| `f` multiaffine | `IsMultiaffine f` |
| `f` has degree `≤ 1` in `xᵢ` | `f.degreeOf i ≤ 1` |
| `g ∈ 𝔽[x_k : k ≠ i]` | `g ∈ supported 𝔽 {i}ᶜ` |
| `g ∈ 𝔽[x_k : k ≠ i, j]` | `g ∈ supported 𝔽 {i, j}ᶜ` |
| `g ∈ 𝔽[x_k : k ∈ X \ {i}]` | `g ∈ supported 𝔽 ↑(X.erase i)` |
| `g |_{x_k = 0}` | `setZero k g` |
| `∂f/∂xᵢ`, `∂²f/∂xᵢ∂xⱼ` | `pderiv i f`, `pderiv i (pderiv j f)` |
| `Δᵢⱼ(f)` | `rayleighDiff i j f` |
| `res_{x_k}(g, h)` | `res k g h` (**not** `Polynomial.resultant`) |

 Results **MISSING** form Mathlib:

 * the Desnanot–Jacobi identity (and Jacobi's complementary-minor theorem in general);
 * the generalized Laplace expansion along a *set* of rows (Theorem 3.1);
 * Jacobi's formula `∂ᵢ det = adj_ii` for a multivariate matrix;
 * symmetrizable matrices (`IsSymmetrizable`).

 ## Two places where the paper should be double-checked

 1. **Theorem 4.1(a), "diagonally equivalent to a symmetric matrix", needs square roots.**
    The proof of Lemma 4.4 sets `D_jj = √α_jk`. Over `ℚ` this can fail, and we believe the
    theorem is then false as literally stated. Take a rational, irreducible `A` with a cut such
    that `DAD⁻¹` is symmetric only for some `D` over `ℚ(√2)`. Its fiber over `ℚ` is still
    trivial (descend `D` to `ℚ` using irreducibility), yet `A` is not `ℚ`-diagonally equivalent
    to a symmetric matrix. The field-independent notion is **symmetrizable**:
    `∃ μ` invertible diagonal with `μA` symmetric (`Matrix.IsSymmetrizable` below). Over a
    field where every element is a square, the two notions agree. We state Theorem 4.1 with
    `IsSymmetrizable`. Discuss this with the mentors.
 2. **Lemma 4.5 vs. Example 4.6.** The lemma transposes the `Q` block, but the example
    transposes the `P` block. Both are fine (one is the transpose of the other, and
    `adj(Bᵀ) = adj(B)ᵀ`). We checked the example in sympy: `f_A = f_B`, `G_B[X,X] = G_A[X,X]ᵀ`,
    and `G_B[Xᶜ,Xᶜ] = G_A[Xᶜ,Xᶜ]`. Pick one convention; we follow the lemma.

## Deviations from the paper

* Theorem 4.1(a), "diagonally equivalent to a symmetric matrix", needs square roots in `𝔽`
  (Lemma 4.4 sets `D_jj = √α_jk`). We use `IsSymmetrizable` instead: `μA` is symmetric for
  some invertible diagonal `μ`. The two agree when every element of `𝔽` is a square. This is
  still to be confirmed with the mentors.
* Lemma 4.5 transposes the block `Q`, while Example 4.6 transposes `P`. Both work; we follow
  the lemma.
-/

@[expose] public section

open Matrix MvPolynomial

/-! ## Diagonal equivalence -/

section DiagEquivalent

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [CommSemiring R]

/-- Conjugating by diagonals rescales entries. -/
theorem diagonal_mul_mul_diagonal_apply (a b : n → R) (N : Matrix n n R) (i j : n) :
    (diagonal a * N * diagonal b) i j = a i * N i j * b j := by
  rw [mul_diagonal, diagonal_mul]

end DiagEquivalent

/-! ## Principal minors, the principal minor map, and its fibers -/

section Minors

variable {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

omit [Fintype n] [DecidableEq n] [CommRing R] in
@[simp]
theorem Matrix.principalSubmatrix_apply (A : Matrix n n R) (S : Finset n) (i j : S) :
    A.principalSubmatrix S i j = A i j := rfl

/-- The principal minor `A_S`. **NAME ONLY**: Mathlib has no name for it. -/
def Matrix.principalMinor (A : Matrix n n R) (S : Finset n) : R :=
  (A.principalSubmatrix S).det

omit [Fintype n] in
/-- `A_∅ = 1`, since the empty determinant is `1`. -/
@[simp]
theorem Matrix.principalMinor_empty (A : Matrix n n R) : A.principalMinor ∅ = 1 := by
  simp [principalMinor]

/-- The principal minor map `φ : A ↦ (A_S)_{S ⊆ [n]}`. -/
def Matrix.principalMinors (A : Matrix n n R) : Finset n → R := A.principalMinor

/-- The fiber of `A` under the principal minor map. -/
def Matrix.pmFiber (A : Matrix n n R) : Set (Matrix n n R) :=
  {B | B.principalMinors = A.principalMinors}

/-- `A ∈ 𝒟(n)`: the fiber of `A` is a single point up to diagonal equivalence. -/
def Matrix.HasTrivialFiber (A : Matrix n n R) : Prop :=
  ∀ B ∈ A.pmFiber, DiagEquivalent B A

/-- Diagonally equivalent matrices have the same principal minors. -/
theorem Matrix.DiagEquivalent.mem_pmFiber {A B : Matrix n n R}
    (h : DiagEquivalent B A) : B ∈ A.pmFiber := by
  rcases h with ⟨d, rfl⟩ | ⟨d, rfl⟩ <;> ext S <;>
    simp only [principalMinors, principalMinor]
  · have : (diagonal (fun i ↦ (d i).val) * A * diagonal (fun i ↦ (d i)⁻¹.val)).principalSubmatrix S
        = diagonal (fun i : S ↦ (d i).val) * A.principalSubmatrix S *
          diagonal (fun i : S ↦ (d i)⁻¹.val) := by
      ext i j; simp
    rw [this, det_mul, det_mul, det_diagonal, det_diagonal, mul_right_comm,
      ← Finset.prod_mul_distrib]
    simp
  · have : (diagonal (fun i ↦ (d i).val) * Aᵀ * diagonal (fun i ↦ (d i)⁻¹.val)).principalSubmatrix S
        = diagonal (fun i : S ↦ (d i).val) * (A.principalSubmatrix S)ᵀ *
          diagonal (fun i : S ↦ (d i)⁻¹.val) := by
      ext i j; simp
    rw [this, det_mul, det_mul, det_diagonal, det_diagonal, det_transpose, mul_right_comm,
      ← Finset.prod_mul_distrib]
    simp

/-- Diagonally similar matrices have the same principal minors. -/
theorem Matrix.DiagSimilar.mem_pmFiber {A B : Matrix n n R} (h : DiagSimilar B A) :
    B ∈ A.pmFiber :=
  DiagEquivalent.mem_pmFiber h.diagEquivalent

end Minors

/-! ## Cuts and symmetrizability

Reducibility is in `DetPoly.IrreducibleMatrix`. -/

section Combinatorial

variable {R 𝔽 n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- A matrix has rank `≤ 1` iff it is an outer product `u vᵀ`. **NAME ONLY**: Mathlib has the
`←` direction (`Matrix.rank_vecMulVec_le`) and the module version
(`Submodule.finrank_le_one_iff_isPrincipal`). -/
theorem Matrix.rank_le_one_iff_eq_vecMulVec [Field 𝔽] {m p : Type*} [Fintype p]
    (M : Matrix m p 𝔽) : M.rank ≤ 1 ↔ ∃ u v, M = vecMulVec u v := by
  refine ⟨fun h ↦ ?_, fun ⟨u, v, h⟩ ↦ h ▸ rank_vecMulVec_le u v⟩
  have := FiniteDimensional.span_of_finite 𝔽 (Set.finite_range M.col)
  rw [rank_eq_finrank_span_cols, Submodule.finrank_le_one_iff_isPrincipal,
    Submodule.isPrincipal_iff] at h
  obtain ⟨u, hu⟩ := h
  have : ∀ j, ∃ c : 𝔽, c • u = M.col j := fun j ↦
    Submodule.mem_span_singleton.mp (hu ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using this
  refine ⟨u, c, ?_⟩
  ext i j
  rw [vecMulVec_apply, ← col_apply M j i, ← hc j, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Diagonal similarity to a symmetric matrix. For a symmetric target, allowing
transpose gives the same relation, so this also expresses the paper's terminology. -/
def Matrix.IsDiagSimilarSymm [CommRing R] (A : Matrix n n R) : Prop :=
  ∃ S : Matrix n n R, S.IsSymm ∧ DiagSimilar A S

/-- `A` is *symmetrizable*: `μA` is symmetric for some invertible diagonal `μ`, i.e.
`μᵢ aᵢⱼ = μⱼ aⱼᵢ`. **MISSING** from Mathlib. -/
def Matrix.IsSymmetrizable [CommRing R] (A : Matrix n n R) : Prop :=
  ∃ μ : n → Rˣ, (diagonal (fun i ↦ (μ i).val) * A).IsSymm

/-- If `A = D S D⁻¹` with `S` symmetric, then `μ = D⁻²` symmetrizes `A`. -/
theorem Matrix.IsDiagSimilarSymm.isSymmetrizable [CommRing R] {A : Matrix n n R}
    (h : A.IsDiagSimilarSymm) : A.IsSymmetrizable := by
  obtain ⟨S, hS, d, rfl⟩ := h
  · refine ⟨d⁻¹ ^ 2, IsSymm.ext fun i j ↦ ?_⟩
    have hi := (d i).inv_mul
    have hj := (d j).inv_mul
    have hs : S i j = S j i := hS.apply j i
    simp only [diagonal_mul, mul_diagonal, Pi.pow_apply, Pi.inv_apply,
      Units.val_pow_eq_pow_val, hs]
    linear_combination (↑(d j)⁻¹ * S j i * ↑(d i)⁻¹) * hj -
      (↑(d i)⁻¹ * S j i * ↑(d j)⁻¹) * hi

/-- **TODO**. The converse needs square roots; this is the gap in Lemma 4.4. -/
theorem Matrix.IsSymmetrizable.isDiagSimilarSymm [Field 𝔽] [IsAlgClosed 𝔽] {A : Matrix n n 𝔽}
    (h : A.IsSymmetrizable) : A.IsDiagSimilarSymm := by
  sorry

end Combinatorial

/-! ## Polynomials in some of the variables; multiaffine polynomials

`R[x_k : k ∈ s]` is the subalgebra `MvPolynomial.supported R s`. For example,
`R[x_k : k ≠ i, j]` is `supported R {i, j}ᶜ` and `R[x_k : k ∈ X \ {i}]` is
`supported R ↑(X.erase i)`. Membership is usually easiest to prove through `degreeOf`
(`mem_supported_iff_degreeOf_eq_zero`). -/

section Polys

variable {R n : Type*} [CommRing R]

theorem mem_supported_iff_degreeOf_eq_zero {p : MvPolynomial n R} {s : Set n} :
    p ∈ supported R s ↔ ∀ i ∉ s, p.degreeOf i = 0 := by
  rw [mem_supported, Set.subset_def]
  refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩
  · by_contra h'
    exact hi (h i (by rwa [Finset.mem_coe, mem_vars_iff_degreeOf_ne_zero]))
  · by_contra h'
    exact mem_vars_iff_degreeOf_ne_zero.mp hi (h i h')

theorem mem_supported_compl_singleton_iff {p : MvPolynomial n R} {i : n} :
    p ∈ supported R ({i}ᶜ : Set n) ↔ p.degreeOf i = 0 := by
  simp [mem_supported_iff_degreeOf_eq_zero]

theorem mem_supported_compl_pair_iff {p : MvPolynomial n R} {i j : n} :
    p ∈ supported R ({i, j}ᶜ : Set n) ↔
      p ∈ supported R ({i}ᶜ : Set n) ∧ p ∈ supported R ({j}ᶜ : Set n) := by
  rw [mem_supported_iff_degreeOf_eq_zero, mem_supported_compl_singleton_iff,
    mem_supported_compl_singleton_iff]
  simp only [Set.mem_compl_iff, not_not, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]

/-- An operation that does not raise any `degreeOf` preserves `supported R s`. -/
theorem mem_supported_of_degreeOf_le {s : Set n} {p q : MvPolynomial n R}
    (hqp : ∀ i, q.degreeOf i ≤ p.degreeOf i) (hp : p ∈ supported R s) : q ∈ supported R s := by
  rw [mem_supported_iff_degreeOf_eq_zero] at hp ⊢
  exact fun i hi ↦ Nat.le_zero.mp ((hqp i).trans (hp i hi).le)

/-- Divisors of a nonzero polynomial in `supported R s` are in `supported R s`. -/
theorem mem_supported_of_dvd [IsDomain R] {s : Set n} {p q : MvPolynomial n R}
    (hpq : p ∣ q) (hq : q ∈ supported R s) (hq0 : q ≠ 0) : p ∈ supported R s := by
  obtain ⟨r, rfl⟩ := hpq
  rw [mem_supported_iff_degreeOf_eq_zero] at hq ⊢
  intro i hi
  have := hq i hi
  rw [degreeOf_mul_eq (left_ne_zero_of_mul hq0) (right_ne_zero_of_mul hq0)] at this
  omega

theorem mem_supported_of_mul_mem [IsDomain R] {s : Set n} {p q : MvPolynomial n R}
    (hpq : p * q ∈ supported R s) (hp : p ≠ 0) : q ∈ supported R s := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact zero_mem _
  · exact mem_supported_of_dvd (dvd_mul_left q p) hpq (mul_ne_zero hp hq)

/-- `p` is multiaffine: degree at most 1 in each variable. **NAME ONLY**: Mathlib's form is
`p ∈ restrictDegree n R 1` (`isMultiaffine_iff_mem_restrictDegree`). -/
def IsMultiaffine (p : MvPolynomial n R) : Prop := ∀ i, p.degreeOf i ≤ 1

theorem isMultiaffine_iff_mem_restrictDegree (p : MvPolynomial n R) :
    IsMultiaffine p ↔ p ∈ restrictDegree n R 1 := by
  simp only [IsMultiaffine, mem_restrictDegree, degreeOf_le_iff]
  exact ⟨fun h s hs i ↦ h i s hs, fun h i s hs ↦ h s hs i⟩

/-- The exponent vector of `∏_{i ∈ S} xᵢ`. **NAME ONLY**: equal to
`Multiset.toFinsupp S.val`. -/
noncomputable def Finset.exponent (S : Finset n) : n →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

/-- If `p` is affine in `x_k`, dividing by `x_k` (`divMonomial`) is `∂ₖ`. -/
theorem divMonomial_single_eq_pderiv {k : n} {p : MvPolynomial n R} (hp : p.degreeOf k ≤ 1) :
    p.divMonomial (Finsupp.single k 1) = pderiv k p := by
  ext t
  rw [coeff_divMonomial, coeff_pderiv, add_comm]
  by_cases ht : t k = 0
  · simp [ht]
  · have : p.coeff (t + Finsupp.single k 1) = 0 := by
      by_contra h
      have := monomial_le_degreeOf k (mem_support_iff.mpr h)
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      omega
    simp [this]

/-- If `p` is affine in `x_k`, then `∂ₖp` is free of `x_k`. -/
theorem pderiv_mem_supported {k : n} {p : MvPolynomial n R} (hp : p.degreeOf k ≤ 1) :
    pderiv k p ∈ supported R ({k}ᶜ : Set n) := by
  rw [← divMonomial_single_eq_pderiv hp, mem_supported_compl_singleton_iff, ← Nat.le_zero,
    degreeOf_le_iff]
  intro t ht
  rw [mem_support_iff, coeff_divMonomial] at ht
  have := monomial_le_degreeOf k (mem_support_iff.mpr ht)
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
  omega

theorem pderiv_eq_zero_of_mem_supported {k : n} {p : MvPolynomial n R}
    (hp : p ∈ supported R ({k}ᶜ : Set n)) : pderiv k p = 0 :=
  pderiv_eq_zero_of_notMem_vars <| by
    rwa [mem_vars_iff_degreeOf_ne_zero, not_not, ← mem_supported_compl_singleton_iff]

theorem degreeOf_pderiv_le (i j : n) (p : MvPolynomial n R) :
    (pderiv i p).degreeOf j ≤ p.degreeOf j := by
  rw [degreeOf_le_iff]
  intro t ht
  rw [mem_support_iff, coeff_pderiv] at ht
  have := monomial_le_degreeOf j (mem_support_iff.mpr (left_ne_zero_of_mul ht))
  simp only [Finsupp.add_apply] at this
  omega

theorem pderiv_mem_supported_of_mem {s : Set n} {i : n} {p : MvPolynomial n R}
    (hp : p ∈ supported R s) : pderiv i p ∈ supported R s :=
  mem_supported_of_degreeOf_le (degreeOf_pderiv_le i · p) hp

private theorem single_one_le_iff {k : n} {t : n →₀ ℕ} :
    Finsupp.single k 1 ≤ t ↔ t k ≠ 0 := by
  rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

variable [DecidableEq n]

/-
#check killCompl
#check optionEquivLeft
#check finSuccEquiv -/

/-- `p |_{x_k = 0}`, defined with `aeval` so that it is an `AlgHom`. **NAME ONLY**: Mathlib's
form is `p.modMonomial (single k 1)` (`setZero_eq_modMonomial`), whose partner `divMonomial`
divides by `x_k`. -/
noncomputable def setZero (k : n) : MvPolynomial n R →ₐ[R] MvPolynomial n R :=
  aeval (Function.update X k 0)

theorem setZero_eq_modMonomial (k : n) (p : MvPolynomial n R) :
    setZero k p = p.modMonomial (Finsupp.single k 1) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s r =>
    ext t
    rw [setZero, aeval_monomial, Finsupp.prod]
    by_cases hs : s k = 0
    · have : ∏ i ∈ s.support, (Function.update X k 0 i : MvPolynomial n R) ^ s i
          = monomial s 1 := by
        rw [monomial_eq, C_1, one_mul, Finsupp.prod]
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        rw [Function.update_of_ne (by rintro rfl; simp_all)]
      rw [this, algebraMap_eq, C_mul_monomial, mul_one]
      by_cases ht : Finsupp.single k 1 ≤ t
      · rw [coeff_modMonomial_of_le _ ht, coeff_monomial, ite_eq_right]
        rintro rfl; exact single_one_le_iff.mp ht hs
      · rw [coeff_modMonomial_of_not_le _ ht]
    · rw [Finset.prod_eq_zero (i := k) (by simpa using hs) (by simp [hs]), mul_zero]
      by_cases ht : Finsupp.single k 1 ≤ t
      · rw [coeff_modMonomial_of_le _ ht]; rfl
      · rw [coeff_modMonomial_of_not_le _ ht, coeff_monomial, ite_eq_right_iff.mpr]
        · rfl
        rintro rfl; exact absurd (single_one_le_iff.mpr hs) ht
  | add p q hp hq =>
    rw [map_add, hp, hq]; ext t
    by_cases ht : Finsupp.single k 1 ≤ t
    · simp [coeff_modMonomial_of_le _ ht]
    · simp [coeff_modMonomial_of_not_le _ ht]

/-- `setZero k` keeps exactly the monomials without `x_k`. -/
theorem coeff_setZero (k : n) (p : MvPolynomial n R) (t : n →₀ ℕ) :
    (setZero k p).coeff t = if t k = 0 then p.coeff t else 0 := by
  rw [setZero_eq_modMonomial]
  split_ifs with ht
  · exact coeff_modMonomial_of_not_le _ (by rwa [single_one_le_iff, not_not])
  · exact coeff_modMonomial_of_le _ (single_one_le_iff.mpr ht)

theorem setZero_mem_supported (k : n) (p : MvPolynomial n R) :
    setZero k p ∈ supported R ({k}ᶜ : Set n) := by
  rw [mem_supported_compl_singleton_iff, ← Nat.le_zero, degreeOf_le_iff]
  intro t ht
  rw [mem_support_iff, coeff_setZero] at ht
  by_contra h
  exact ht (by simp [show t k ≠ 0 by omega])

theorem setZero_of_mem_supported {k : n} {p : MvPolynomial n R}
    (hp : p ∈ supported R ({k}ᶜ : Set n)) : setZero k p = p := by
  rw [mem_supported_compl_singleton_iff] at hp
  ext t
  rw [coeff_setZero, ite_eq_left_iff]
  intro ht
  by_contra h
  have := monomial_le_degreeOf k (mem_support_iff.mpr (Ne.symm h))
  omega

/-- `p = p|_{x_k=0} + x_k ∂ₖp` for `p` affine in `x_k`. With `setZero_mem_supported` and
`pderiv_mem_supported`, this replaces writing `f = a xᵢxⱼ + b xᵢ + c xⱼ + d` by hand. -/
theorem eq_setZero_add_X_mul_pderiv {k : n} {p : MvPolynomial n R} (hp : p.degreeOf k ≤ 1) :
    p = setZero k p + X k * pderiv k p := by
  rw [setZero_eq_modMonomial, ← divMonomial_single_eq_pderiv hp,
    modMonomial_add_divMonomial_single]

end Polys

/-! ## The determinantal polynomial and the adjugate -/

section DetPoly

variable {R 𝔽 n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- `G = (diag(x) + A)^adj`. -/
noncomputable def Matrix.adjPoly (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  A.mvCharmatrix.adjugate

/-- **TODO**: the coefficient of `∏_{i ∈ S} xᵢ` in `f_A` is the complementary minor `A_{Sᶜ}`.
The expansion is `det_add_diagonal_formula` (`DetPoly/PS2_#1c_Shaoda.lean`). Mathlib's
univariate analogue is `Matrix.coeff_det_one_add_X_smul_eq_sum_minors`. -/
theorem Matrix.coeff_detpoly (A : Matrix n n R) (S : Finset n) :
    A.detpoly.coeff S.exponent = A.principalMinor Sᶜ := by
  sorry

/-- **TODO** -/
theorem Matrix.detpoly_isMultiaffine (A : Matrix n n R) : IsMultiaffine A.detpoly := by
  sorry

/-- The leading coefficient is `1`, the normalization in Theorem 2.1. -/
theorem Matrix.coeff_univ_detpoly (A : Matrix n n R) :
    A.detpoly.coeff Finset.univ.exponent = 1 := by
  rw [coeff_detpoly, Finset.compl_univ, principalMinor_empty]

/-- **TODO**: same fiber iff same determinantal polynomial. -/
theorem Matrix.detpoly_eq_iff {A B : Matrix n n R} :
    B.detpoly = A.detpoly ↔ B ∈ A.pmFiber := by
  sorry

/-- **TODO**, **MISSING** (Jacobi's formula): `∂ᵢ f_A = G_ii`. Mathlib only has univariate
versions (`Matrix.derivative_det_one_add_X_smul`). Hint: expand along row `i`
(`det_eq_sum_mul_adjugate_row`); the cofactors along row `i` are free of `xᵢ`. -/
theorem Matrix.pderiv_detpoly (A : Matrix n n R) (i : n) :
    pderiv i A.detpoly = A.adjPoly i i := by
  sorry

/-- **TODO**: `G_ij ∈ R[x_k : k ≠ i, j]` for `i ≠ j`. -/
theorem Matrix.adjPoly_mem_supported (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    A.adjPoly i j ∈ supported R ({i, j}ᶜ : Set n) := by
  sorry

/-- **TODO** -/
theorem Matrix.adjPoly_isMultiaffine (A : Matrix n n R) (i j : n) :
    IsMultiaffine (A.adjPoly i j) := by
  sorry

/-- **TODO**: `G_{DAD⁻¹} = D G_A D⁻¹`. Hint: `adjugate_mul_distrib`, since `diag(x)` commutes
with `D`. -/
theorem Matrix.adjPoly_diag_conj (A : Matrix n n R) (d : n → Rˣ) (i j : n) :
    (diagonal (fun i ↦ (d i).val) * A * diagonal (fun i ↦ (d i)⁻¹.val)).adjPoly i j =
      C (d i).val * A.adjPoly i j * C (d j)⁻¹.val := by
  sorry

end DetPoly

/-! ## Rayleigh differences and resultants -/

section Rayleigh

variable {R 𝔽 n : Type*} [CommRing R]

variable [DecidableEq n]

/-- The paper's resultant `res_{x_k}(g, h) = g|_{x_k=0} ∂ₖh - h|_{x_k=0} ∂ₖg`. This is **not**
Mathlib's `Polynomial.resultant`, though for `g, h` affine in `x_k` it is the Sylvester
resultant with formal degrees `(1, 1)`. -/
noncomputable def res (k : n) (g h : MvPolynomial n R) : MvPolynomial n R :=
  setZero k g * pderiv k h - setZero k h * pderiv k g

/-- `res` is linear over polynomials free of `x_k`. -/
theorem res_mul_left {k : n} {c : MvPolynomial n R} (hc : c ∈ supported R ({k}ᶜ : Set n))
    (g h : MvPolynomial n R) : res k (c * g) h = c * res k g h := by
  simp only [res, map_mul, setZero_of_mem_supported hc, Derivation.leibniz,
    pderiv_eq_zero_of_mem_supported hc, smul_eq_mul]
  ring

-- Lemma 2.2 (`rayleighDiff_eq_zero_iff`) and the rest of the `setZero` API are in
-- `LEAN_Warmup.Grant.MvPolynomial`.

variable [Fintype n]

/-- **TODO**, **MISSING**: the Desnanot–Jacobi identity, in adjugate form (no signs). Nearby
Mathlib API: `adjugate_adjugate`, `det_adjugate`, and Schur complements
(`LinearAlgebra/Matrix/SchurComplement.lean`). -/
theorem Matrix.adjugate_mul_adjugate_sub {M : Matrix n n R} {i j : n} (hij : i ≠ j) :
    M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i =
      M.det * (M.principalSubmatrix ({i, j}ᶜ : Finset n)).det := by
  sorry

/-- **Theorem 2.3**. It also holds for `i = j`, where both sides are `G_ii²`. -/
theorem Matrix.rayleighDiff_detpoly (A : Matrix n n R) (i j : n) :
    rayleighDiff i j A.detpoly = A.adjPoly i j * A.adjPoly j i := by
  sorry

/-- **TODO**: condition (b) of Theorem 2.1 for the adjugate ("only if" direction). -/
theorem Matrix.res_adjPoly (A : Matrix n n R) {i j k : n} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) : res k (A.adjPoly i j) A.detpoly = A.adjPoly i k * A.adjPoly k j := by
  sorry

end Rayleigh

/-! ## External results

These are `sorry` theorems rather than axioms, so they show up in `#print axioms`. -/

section External

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **EXTERNAL**, **Lemma 4.2** ([Hartfiel–Loewy 1984, Thm 1]): for irreducible `A`, every
entry of `G` is nonzero. -/
theorem Matrix.adjPoly_ne_zero {A : Matrix n n 𝔽} (hA : A.IsIrred) (i j : n) :
    A.adjPoly i j ≠ 0 := by
  sorry

/-- **EXTERNAL**, **Theorem 2.1**, "if" direction ([AV22, Thm 3.1 and Rem 3.4]), in the strong
form that Lemma 4.5 uses: the off-diagonal entries of `G_B` are the `gᵢⱼ`. -/
theorem exists_detpoly_eq_of_rayleigh {f : MvPolynomial n 𝔽} (hf : IsMultiaffine f)
    (hlead : f.coeff Finset.univ.exponent = 1) (g : n → n → MvPolynomial n 𝔽)
    (hΔ : ∀ i j, i ≠ j → rayleighDiff i j f = g i j * g j i)
    (hsupp : ∀ i j, i ≠ j → g i j ∈ supported 𝔽 ({i, j}ᶜ : Set n))
    (haff : ∀ i j, IsMultiaffine (g i j))
    (hres : ∀ i j k, i ≠ j → k ≠ i → k ≠ j → res k (g i j) f = g i k * g k j) :
    ∃ B : Matrix n n 𝔽, B.detpoly = f ∧ ∀ i j, i ≠ j → B.adjPoly i j = g i j := by
  sorry

/-- **EXTERNAL** ([Loewy 1986, Thm 1]): irreducible with no cut implies trivial fiber. -/
theorem Matrix.hasTrivialFiber_of_noCut (hn : 4 ≤ Fintype.card n) {A : Matrix n n 𝔽}
    (hA : A.IsIrred) (hcut : ∀ X, ¬ A.HasCut X) : A.HasTrivialFiber := by
  sorry

end External

/-! ## Results of the paper -/

section Paper

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **Lemma 4.3**, with the paper's sign `(-1)^i` absorbed into `aᵢ`. For the block
`G[Xᶜ, X]`, apply this to `Xᶜ` (`HasCut.compl`).

The paper's proof uses the generalized Laplace expansion (Theorem 3.1), which is **MISSING**
from Mathlib and used only here. An alternative is to write `A[X, Xᶜ] = u vᵀ`
(`rank_le_one_iff_eq_vecMulVec`) and expand the cofactor by multilinearity in the rows of `X`. -/
theorem Matrix.adjPoly_eq_mul_of_hasCut (hn : 4 ≤ Fintype.card n) {A : Matrix n n 𝔽}
    (hA : A.IsIrred) {X : Finset n} (hX : A.HasCut X) :
    ∃ a b : n → MvPolynomial n 𝔽,
      (∀ i ∈ X, a i ∈ supported 𝔽 ↑(X.erase i) ∧ a i ≠ 0) ∧
      (∀ j ∉ X, b j ∈ supported 𝔽 ↑(Xᶜ.erase j) ∧ b j ≠ 0) ∧
      ∀ i ∈ X, ∀ j ∉ X, A.adjPoly i j = a i * b j := by
  sorry

/-- **Lemma 4.4**, with the conclusion `IsSymmetrizable`, which needs no square roots. -/
theorem Matrix.isSymmetrizable_of_adjPoly_proportional (hn : 4 ≤ Fintype.card n)
    {A : Matrix n n 𝔽} (hA : A.IsIrred) {X : Finset n} (hX : A.HasCut X)
    (hα : ∀ i ∈ X, ∀ j ∉ X, ∃ α : 𝔽, A.adjPoly i j = C α * A.adjPoly j i) :
    A.IsSymmetrizable := by
  sorry

/-- The matrix `H` of Lemma 4.5: keep `P = G[X,X]`, transpose `Q = G[Xᶜ,Xᶜ]`, and swap
factors in the off-diagonal blocks (`Uᵢⱼ = aᵢcⱼ`, `Vᵢⱼ = bᵢdⱼ`). -/
noncomputable def cutSwap {R : Type*} (X : Finset n) (G : Matrix n n R) [Mul R]
    (a b c d : n → R) : Matrix n n R :=
  Matrix.of fun i j ↦
    if i ∈ X then (if j ∈ X then G i j else a i * c j)
    else (if j ∈ X then b i * d j else G j i)

/-- **Lemma 4.5**, in the strong form that Theorem 4.1 needs: `H` is `G_B` off the diagonal. -/
theorem Matrix.exists_adjPoly_eq_cutSwap (hn : 4 ≤ Fintype.card n) {A : Matrix n n 𝔽}
    (hA : A.IsIrred) {X : Finset n} (hX : A.HasCut X) (a b c d : n → MvPolynomial n 𝔽)
    (ha : ∀ i ∈ X, a i ∈ supported 𝔽 ↑(X.erase i))
    (hb : ∀ j ∉ X, b j ∈ supported 𝔽 ↑(Xᶜ.erase j))
    (hc : ∀ i ∉ X, c i ∈ supported 𝔽 ↑(Xᶜ.erase i))
    (hd : ∀ j ∈ X, d j ∈ supported 𝔽 ↑(X.erase j))
    (hR : ∀ i ∈ X, ∀ j ∉ X, A.adjPoly i j = a i * b j)
    (hT : ∀ i ∉ X, ∀ j ∈ X, A.adjPoly i j = c i * d j) :
    ∃ B : Matrix n n 𝔽, B.detpoly = A.detpoly ∧
      ∀ i j, i ≠ j → B.adjPoly i j = cutSwap X A.adjPoly a b c d i j := by
  sorry

/-- **Theorem 4.1** (`⇒`), reducible case: reducible matrices have nontrivial fibers. This
needs no `n ≥ 4`. -/
theorem Matrix.IsReducible.not_hasTrivialFiber {A : Matrix n n 𝔽} (hA : A.IsReducible) :
    ¬ A.HasTrivialFiber := by
  sorry

/-- **Lemma 5.1**. `[Nonempty n]` excludes the `0 × 0` matrix, which is irreducible while
`f = 1` is not. -/
theorem Matrix.isIrred_iff_irreducible_detpoly [Nonempty n] (A : Matrix n n 𝔽) :
    A.IsIrred ↔ Irreducible A.detpoly := by
  sorry

/-- **Lemma 6.1**, generalized from symmetric to symmetrizable `A`. The same proof works,
since `G_ij ∝ G_ji`. -/
theorem Matrix.IsSymmetrizable.hasTrivialFiber_iff (hn : 4 ≤ Fintype.card n)
    {A : Matrix n n 𝔽} (hA : A.IsSymmetrizable) : A.HasTrivialFiber ↔ A.IsIrred := by
  sorry

/-- **Theorem 4.1**, with (a) phrased as `IsSymmetrizable`. Condition (b) is
`∀ X, ¬ A.HasCut X`. -/
theorem Matrix.hasTrivialFiber_iff (hn : 4 ≤ Fintype.card n) (A : Matrix n n 𝔽) :
    A.HasTrivialFiber ↔ A.IsIrred ∧ (A.IsSymmetrizable ∨ ∀ X, ¬ A.HasCut X) := by
  sorry

end Paper

/-! ## Example 4.6

`A` has a cut at `X = {1, 2}` and `B` is in its fiber. Matrices over `ℚ` and their principal
minors are computable, so this is checked by `#guard`. -/

/-- Example 4.6, matrix `A`. -/
def ex46A : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2, -1, 1, -2; 1, 1, -3, 6; 1, 2, 1, 1; -1, -2, 2, -1]

/-- Example 4.6, matrix `B`. -/
def ex46B : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2, 1, 1, -2; -1, 1, 2, -4; 1, -3, 1, 1; -1, 3, 2, -1]

set_option linter.hashCommand false in
#guard (Finset.univ.filter fun S ↦ ex46A.principalMinor S ≠ ex46B.principalMinor S).card = 0

end
