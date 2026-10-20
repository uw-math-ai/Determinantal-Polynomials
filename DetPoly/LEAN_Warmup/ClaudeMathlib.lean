/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/

module

public import Mathlib

/-!
# Notation for "The fiber of the principal minor map" (Al Ahmadieh, arXiv:2309.00806)

This file sets up every notion the paper uses and states its results in the form we think we
should formalize. Comments explain *why* each phrasing was chosen and which Mathlib
declarations it builds on. Tags:

* **MISSING**: Mathlib has no version of this, so we have to build it.
* **NAME ONLY**: Mathlib has the content, just not under a name we'd want to use.
* **TODO**: a statement whose proof is ours and still `sorry`.
* **EXTERNAL**: a result the paper cites from another paper (also `sorry`).

## Global conventions (opinionated)

* **Field `𝔽`, index type `n`.** We use an arbitrary `[Fintype n] [DecidableEq n]` rather than
  `Fin n`. Nothing in the paper needs the order on `[n]` except signs like `(-1)^i` and
  `(-1)^(∑S + ∑T)`, and those are bookkeeping that we design away (see Lemma 4.3 below).
  Subsets of `[n]` are `Finset n`; complements are `Xᶜ`.
* **Generality.** Purely algebraic identities (Dodgson, the coefficients of `f_A`, the
  resultant identities) hold over any `CommRing R`, so we state them that way. Results that
  use division, rank, or unique factorization are stated over `𝔽`.
* **Polynomials** are `MvPolynomial n R`, with variables `X i` playing the role of `xᵢ`.
  "Multiaffine" and "lies in `𝔽[x_k : k ∈ s]`" are *predicates* on `MvPolynomial n R`, not new
  types. That way `f`, its factors, its derivatives, and the entries of the adjugate all live
  in one ring and can be multiplied without coercions.
* **Junk values.** Families indexed by part of `[n]` (like `aᵢ` for `i ∈ X`) are total
  functions `n → _`. Hypotheses are guarded by `i ∈ X`, and values outside `X` are ignored.
  This is much easier to use than functions on subtypes.

## Dictionary

| paper | Lean |
|---|---|
| `A = DBD⁻¹` or `A = DBᵀD⁻¹` | `DiagEquiv A B` |
| `A_S` | `A.principalMinor S` |
| fiber of `A` under the principal minor map | `A.pmFiber` |
| `𝒟(n)` | `{A | A.HasTrivialFiber}` |
| `A` reducible / irreducible | `A.IsReducible` / `A.IsIrred` |
| `A` has a cut `X` | `A.HasCut X` |
| `diag(x₁,…,xₙ) + A` | `A.mvCharmatrix` |
| `f_A` | `A.detPoly` |
| `G = (diag(x) + A)^adj` | `A.adjPoly` |
| `f` multiaffine | `IsMultiaffine f` |
| `f` has degree `≤ 1` in `xᵢ` | `f.degreeOf i ≤ 1` |
| `g ∈ 𝔽[x_k : k ≠ i]` | `g ∈ supported 𝔽 {i}ᶜ` |
| `g ∈ 𝔽[x_k : k ≠ i, j]` | `g ∈ supported 𝔽 {i, j}ᶜ` |
| `g ∈ 𝔽[x_k : k ∈ X \ {i}]` | `g ∈ supported 𝔽 ↑(X.erase i)` |
| `g |_{x_k = 0}` | `setZero k g` (equal to Mathlib's `g.modMonomial (single k 1)`) |
| `∂f/∂xᵢ`, `∂²f/∂xᵢ∂xⱼ` | `pderiv i f`, `pderiv i (pderiv j f)` |
| `Δᵢⱼ(f)` | `rayleighDiff i j f` |
| `res_{x_k}(g, h)` | `res k g h` (**not** `Polynomial.resultant`, see §6) |

## What Mathlib already has

Most notions the paper needs are in Mathlib in *some* form. Often there is a univariate
version, a general version, or the main proof technique, but not the exact multivariate
statement. Only these are truly **MISSING**:

* the Desnanot–Jacobi identity (and Jacobi's complementary-minor theorem in general);
* the generalized Laplace expansion along a *set* of rows (Theorem 3.1);
* Jacobi's formula `∂ᵢ det = adj_ii` for a multivariate matrix;
* symmetrizable matrices (`IsSymmetrizable`).

Everything else is **NAME ONLY** or a short bridge lemma. The details are next to each
definition below. Paths are relative to `.lake/packages/mathlib/`.

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

Things sympy confirmed on random 4×4 matrices:
`Δᵢⱼ(f_A) = G_ij G_ji` for **all** `i, j` (including `i = j`);
`res_{x_k}(G_ij, f_A) = +G_ik G_kj`; and `∂ᵢ f_A = G_ii`.
-/

@[expose] public section

open Matrix MvPolynomial

/-! ## 1. Diagonal equivalence -/

section DiagEquiv

variable {R n : Type*} [Fintype n] [DecidableEq n]

variable [CommSemiring R]

/-- `M` and `N` are *diagonally equivalent*: `M = D N D⁻¹` or `M = D Nᵀ D⁻¹` for an invertible
diagonal `D`.

Design notes:
* Quantify over units `d : n → Rˣ`, never `d : n → R` with `(diagonal d)⁻¹`. The latter makes
  every matrix equivalent to `0` via `d = 0`.
* A plain `def ... : Prop` (Mathlib style), not a `structure` or `abbrev`.
* The paper includes the transpose in "diagonally equivalent", so we do too. -/
def DiagEquiv (M N : Matrix n n R) : Prop :=
  ∃ d : n → Rˣ,
    M = diagonal (fun i ↦ (d i).val) * N * diagonal (fun i ↦ (d i)⁻¹.val) ∨
    M = diagonal (fun i ↦ (d i).val) * Nᵀ * diagonal (fun i ↦ (d i)⁻¹.val)

/-- Conjugating by diagonals rescales entries. Working entrywise is the easy way to prove
anything about `DiagEquiv`. -/
theorem diagonal_mul_mul_diagonal_apply (a b : n → R) (N : Matrix n n R) (i j : n) :
    (diagonal a * N * diagonal b) i j = a i * N i j * b j := by
  rw [mul_diagonal, diagonal_mul]

theorem DiagEquiv.equivalence : Equivalence (DiagEquiv (R := R) (n := n)) where
  refl M := by use 1; simp
  symm := by
    rintro M N ⟨d, h | h⟩
    · use d⁻¹
      left; ext i j
      simp [h, mul_assoc]
    · use d
      right; ext i j
      simp [h, mul_assoc]
  trans := by
    rintro M N O ⟨d₁, hl₁ | hr₁⟩ ⟨d₂, hl₂ | hr₂⟩
    · use d₁ * d₂
      left; ext i j
      simp [hl₁, hl₂, mul_assoc]
    · use d₁ * d₂
      right; ext i j
      simp [hl₁, hr₂, mul_assoc]
    · use d₁ * d₂⁻¹
      right; ext i j
      simp [hr₁, hl₂, mul_assoc]
    · use d₁ * d₂⁻¹
      left; ext i j
      simp [hr₁, hr₂, mul_assoc]

/-- So `Quotient DiagEquiv.setoid` is "matrices up to diagonal equivalence". -/
def DiagEquiv.setoid : Setoid (Matrix n n R) := ⟨DiagEquiv, DiagEquiv.equivalence⟩

end DiagEquiv

/-! ## 2. Principal minors, the principal minor map, and its fibers -/

section Minors

variable {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- `A[S, S]`, the principal submatrix on `S`. It is indexed by the subtype `↥S`.

**NAME ONLY.** Mathlib writes this inline as `(A.submatrix (↑) (↑) : Matrix S S R)`, e.g. in
`Matrix.det_piecewise_one_eq_submatrix_det` (`LinearAlgebra/Matrix/Charpoly/Coeff.lean`).
Our definition unfolds to exactly that, so `rw [principalSubmatrix]` turns our statements into
the form Mathlib's lemmas expect. For non-principal submatrices like `A[X, Xᶜ]`, use
`A.submatrix (↑) (↑)` directly. -/
def Matrix.principalSubmatrix (A : Matrix n n R) (S : Finset n) : Matrix S S R :=
  A.submatrix (↑) (↑)

omit [Fintype n] [DecidableEq n] [CommRing R] in
@[simp]
theorem Matrix.principalSubmatrix_apply (A : Matrix n n R) (S : Finset n) (i j : S) :
    A.principalSubmatrix S i j = A i j := rfl

/-- The principal minor `A_S`.

**NAME ONLY.** Mathlib never names "the determinant of a principal submatrix". The only named
version is `BirdDet.pminor` (`LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean`), which
takes words `Fin p → Fin n` and is internal to Bird's algorithm, so don't use it. -/
def Matrix.principalMinor (A : Matrix n n R) (S : Finset n) : R :=
  (A.principalSubmatrix S).det

omit [Fintype n] in
/-- `A_∅ = 1` for free, because the determinant of an empty matrix is `1`. So we don't need
the paper's convention "we set `A_∅ = 1`". -/
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
  ∀ B ∈ A.pmFiber, DiagEquiv B A

/-- "It is easy to see that if two matrices are diagonally equivalent, then their principal
minors are equal." -/
theorem DiagEquiv.mem_pmFiber {A B : Matrix n n R} (h : DiagEquiv B A) : B ∈ A.pmFiber := by
  obtain ⟨d, rfl | rfl⟩ := h <;> ext S <;>
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

end Minors

/-! ## 3. Reducibility, symmetry, cuts -/

section Combinatorial

variable {R 𝔽 n : Type*} [Fintype n] [DecidableEq n]

/-
**Do not use Mathlib's `Matrix.IsIrreducible`** (`LinearAlgebra/Matrix/Irreducible/Defs.lean`).
It needs `[Ring R] [LinearOrder R]` and means "entrywise nonnegative, and the graph of
*positive* entries is strongly connected". That is the Perron–Frobenius notion, and it
doesn't apply over a general field.

The paper says "reducible = block upper triangular after a simultaneous permutation". We avoid
permutations entirely. A permutation into block form *is* a choice of subset `S` (the first
block). So reducibility is "some nonempty proper `S` receives no edges from outside". Mathlib's
`Matrix.BlockTriangular M b` (with block labels `b : n → α`) is the matching
permutation-free notion for many blocks (Theorem 5.2), and
`Matrix.blockTriangular_reindex_iff` converts if you ever need an actual permutation.
-/

/-- `A` is reducible: after putting `S` first, `A = [[A_SS, *], [0, A_S'S']]`. -/
def Matrix.IsReducible [Zero R] (A : Matrix n n R) : Prop :=
  ∃ S : Finset n, S.Nonempty ∧ S ≠ Finset.univ ∧ ∀ i ∉ S, ∀ j ∈ S, A i j = 0

/-- Irreducible in the paper's sense. Note: if `n` is empty, every matrix is `IsIrred`, but
`f_A = 1` is not an irreducible polynomial. So Lemma 5.1 needs `[Nonempty n]`. -/
def Matrix.IsIrred [Zero R] (A : Matrix n n R) : Prop := ¬ A.IsReducible

omit [Fintype n] [DecidableEq n] in
theorem Matrix.blockTriangular_of_subset [Zero R] (A : Matrix n n R) (S : Finset n)
    (hS : ∀ i ∉ S, ∀ j ∈ S, A i j = 0) : A.BlockTriangular (fun i ↦ i ∉ S) := by
  intro i j hij
  obtain ⟨-, h⟩ := lt_iff_le_not_ge.mp hij
  simp only [le_Prop_eq, not_imp, not_not] at h
  exact hS i h.1 j h.2

/-- `A` has a cut at `X`: `2 ≤ |X| ≤ n - 2` and `rk A[X,Xᶜ] ≤ 1`, `rk A[Xᶜ,X] ≤ 1`.

We use `Matrix.rank` to stay faithful to the paper. The proofs, however, use the
rank-one *factorization*, so the first lemma we need is `rank_le_one_iff_eq_vecMulVec`.
Note that the definition is symmetric in `X ↔ Xᶜ` (`HasCut.compl`), which is how we get the
"`T`" block of Lemma 4.3 for free. -/
def Matrix.HasCut [Field 𝔽] (A : Matrix n n 𝔽) (X : Finset n) : Prop :=
  2 ≤ X.card ∧ 2 ≤ Xᶜ.card ∧
    (A.submatrix ((↑) : X → n) ((↑) : ↥Xᶜ → n)).rank ≤ 1 ∧
    (A.submatrix ((↑) : ↥Xᶜ → n) ((↑) : X → n)).rank ≤ 1

omit [Fintype n] [DecidableEq n] in
/-- A matrix has rank `≤ 1` iff it is an outer product `u vᵀ`.

**NAME ONLY.** Mathlib has the `←` direction (`Matrix.rank_vecMulVec_le`,
`LinearAlgebra/Matrix/Rank.lean`) and the module version `rank_le_one_iff` /
`Submodule.finrank_le_one_iff_isPrincipal` (`LinearAlgebra/Dimension/
FreeAndStrongRankCondition.lean`). The proof glues these together through the column space
(`Matrix.rank_eq_finrank_span_cols`): the span of the columns is `𝔽 ∙ u`, so column `j` is
`c j • u`. -/
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

/-- Cuts are symmetric. -/
theorem Matrix.HasCut.compl [Field 𝔽] {A : Matrix n n 𝔽} {X : Finset n} (h : A.HasCut X) :
    A.HasCut Xᶜ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨h₂, by rwa [compl_compl], by rwa [compl_compl], by rwa [compl_compl]⟩

/-- The paper's "diagonally equivalent to a symmetric matrix". Uses `Matrix.IsSymm`. -/
def Matrix.IsDiagEquivSymm [CommRing R] (A : Matrix n n R) : Prop :=
  ∃ S : Matrix n n R, S.IsSymm ∧ DiagEquiv A S

/-- `A` is *symmetrizable*: `μA` is symmetric for some invertible diagonal `μ`, i.e.
`μᵢ aᵢⱼ = μⱼ aⱼᵢ`. This is the notion we believe Theorem 4.1(a) really needs (see the module
docstring).

**MISSING.** In Mathlib the word only appears in a docstring about symmetrizable Kac–Moody
algebras (`LinearAlgebra/RootSystem/RootPositive.lean`). -/
def Matrix.IsSymmetrizable [CommRing R] (A : Matrix n n R) : Prop :=
  ∃ μ : n → Rˣ, (diagonal (fun i ↦ (μ i).val) * A).IsSymm

/-- If `A = D S D⁻¹` with `S` symmetric, take `μ = D⁻²`: then `μA = D⁻¹ S D⁻¹` is symmetric.
(The earlier hint `μ = D²` was wrong.) -/
theorem Matrix.IsDiagEquivSymm.isSymmetrizable [CommRing R] {A : Matrix n n R}
    (h : A.IsDiagEquivSymm) : A.IsSymmetrizable := by
  obtain ⟨S, hS, d, rfl | rfl⟩ := h <;>
  · refine ⟨d⁻¹ ^ 2, IsSymm.ext fun i j ↦ ?_⟩
    have hi := (d i).inv_mul
    have hj := (d j).inv_mul
    have hs : S i j = S j i := hS.apply j i
    simp only [diagonal_mul, mul_diagonal, transpose_apply, Pi.pow_apply, Pi.inv_apply,
      Units.val_pow_eq_pow_val, hs]
    linear_combination (↑(d j)⁻¹ * S j i * ↑(d i)⁻¹) * hj -
      (↑(d i)⁻¹ * S j i * ↑(d j)⁻¹) * hi

/-- **TODO**: the converse needs square roots. That is exactly the gap in Lemma 4.4. -/
theorem Matrix.IsSymmetrizable.isDiagEquivSymm [Field 𝔽] [IsAlgClosed 𝔽] {A : Matrix n n 𝔽}
    (h : A.IsSymmetrizable) : A.IsDiagEquivSymm := by
  sorry

end Combinatorial

/-! ## 4. Polynomials in some of the variables; multiaffine polynomials -/

section Polys

variable {R n : Type*} [CommRing R]

/-
**How to phrase `g ∈ 𝔽[x_k : k ≠ i]`.** Use `MvPolynomial.supported 𝔽 s`
(`Algebra/MvPolynomial/Supported.lean`), the subalgebra of polynomials whose variables lie in
`s : Set n`:
* `𝔽[x_k : k ≠ i]`     ↦ `supported 𝔽 {i}ᶜ`
* `𝔽[x_k : k ≠ i, j]`  ↦ `supported 𝔽 {i, j}ᶜ`
* `𝔽[x_k : k ∈ X \ i]` ↦ `supported 𝔽 ↑(X.erase i)`   (coerce the `Finset` to a `Set`)

Why this and not the alternatives:
* `MvPolynomial {k // k ≠ i} 𝔽` is a *different type*, so `f = g * h` would need `rename`
  coercions on every factor. With `supported`, `g`, `h`, and `f` all live in
  `MvPolynomial n 𝔽`.
* `i ∉ g.vars` is equivalent (`mem_supported`), but `supported` is a `Subalgebra`. So
  closure under `+`, `*`, `C`, and `X k` (for `k ∈ s`) comes for free (`Subalgebra.mul_mem`,
  `X_mem_supported`, ...), as does monotonicity (`supported_mono`).
* Useful API: `mem_supported`, `supported_eq_range_rename`, `supportedEquivMvPolynomial`,
  `mem_vars_iff_degreeOf_ne_zero`. In practice, membership is easiest to prove through
  `degreeOf`, via `mem_supported_iff_degreeOf_eq_zero` below.
-/

/-- The bridge between `supported` and `degreeOf`: `p` avoids the variables outside `s`. -/
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

/-- Divisors of a nonzero polynomial in `supported R s` are in `supported R s`. This is the
fact Lemma 2.2 needs to keep its `gcd`s in the right subalgebra. It is not in Mathlib under
this name, but it follows directly from `MvPolynomial.degreeOf_mul_eq`
(`Algebra/MvPolynomial/NoZeroDivisors.lean`), since degrees add in a domain. -/
theorem mem_supported_of_dvd [IsDomain R] {s : Set n} {p q : MvPolynomial n R}
    (hpq : p ∣ q) (hq : q ∈ supported R s) (hq0 : q ≠ 0) : p ∈ supported R s := by
  obtain ⟨r, rfl⟩ := hpq
  rw [mem_supported_iff_degreeOf_eq_zero] at hq ⊢
  intro i hi
  have := hq i hi
  rw [degreeOf_mul_eq (left_ne_zero_of_mul hq0) (right_ne_zero_of_mul hq0)] at this
  omega

/-
**How to phrase "degree at most 1 in `xᵢ`".** Use `p.degreeOf i ≤ 1`. Lemma 2.2 says "degree
one", but its proof only uses "at most one". The weaker hypothesis is more general and is what
we can supply in applications (`hf i` for multiaffine `f`).
-/

/-- `p` is multiaffine: degree at most 1 in each variable. We define it with `degreeOf`
because that is how it's *used* (one variable at a time).

**NAME ONLY.** Mathlib's form is the submodule `restrictDegree n R 1`
(`RingTheory/MvPolynomial/Basic.lean`); see `isMultiaffine_iff_mem_restrictDegree`. -/
def IsMultiaffine (p : MvPolynomial n R) : Prop := ∀ i, p.degreeOf i ≤ 1

theorem isMultiaffine_iff_mem_restrictDegree (p : MvPolynomial n R) :
    IsMultiaffine p ↔ p ∈ restrictDegree n R 1 := by
  simp only [IsMultiaffine, mem_restrictDegree, degreeOf_le_iff]
  exact ⟨fun h s hs i ↦ h i s hs, fun h i s hs ↦ h s hs i⟩

/-- The exponent vector of `∏_{i ∈ S} xᵢ`. A multiaffine polynomial is determined by its
coefficients at these. The coefficient of `x₁⋯xₙ` is `p.coeff Finset.univ.exponent`.

**NAME ONLY.** Equivalent Mathlib forms are `Multiset.toFinsupp S.val` and
`Finsupp.indicator`; the sum of `single`s is the easiest to compute with. -/
noncomputable def Finset.exponent (S : Finset n) : n →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

/-- If `p` is affine in `x_k`, dividing by `x_k` (`divMonomial`) is the same as `∂ₖ`. This
connects `pderiv` to Mathlib's `Algebra/MvPolynomial/Division.lean`. -/
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

/-- If `p` is affine in `x_k`, then `∂ₖp` doesn't involve `x_k`. -/
theorem pderiv_mem_supported {k : n} {p : MvPolynomial n R} (hp : p.degreeOf k ≤ 1) :
    pderiv k p ∈ supported R ({k}ᶜ : Set n) := by
  rw [← divMonomial_single_eq_pderiv hp, mem_supported_compl_singleton_iff, ← Nat.le_zero,
    degreeOf_le_iff]
  intro t ht
  rw [mem_support_iff, coeff_divMonomial] at ht
  have := monomial_le_degreeOf k (mem_support_iff.mpr ht)
  simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
  omega

private theorem single_one_le_iff {k : n} {t : n →₀ ℕ} :
    Finsupp.single k 1 ≤ t ↔ t k ≠ 0 := by
  rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

variable [DecidableEq n]

/-
**Setting a variable to zero.** Mathlib has this operation three times, but never under this
name and never as `aeval (Function.update X k 0)`:
* `p.modMonomial (Finsupp.single k 1)` (notation `p %ᵐᵒⁿᵒᵐⁱᵃˡ single k 1`, scoped in
  `MvPolynomial`; `Algebra/MvPolynomial/Division.lean`) keeps the terms not divisible by
  `x_k`. Its partner `divMonomial` divides by `x_k`. `modMonomial_add_divMonomial_single` is
  the decomposition `p = p|_{x_k=0} + x_k · (p / x_k)`.
* `killCompl` (`Algebra/MvPolynomial/Rename.lean`) sends variables outside the range of an
  injective map to `0`, landing in `MvPolynomial {i // i ≠ k} R`. That changes the type,
  which our "one ring" convention avoids.
* `optionEquivLeft` / `finSuccEquiv` turn `p` into a polynomial in one variable, and then
  `Polynomial.coeff 0`. This needs `Option n` or `Fin (n + 1)`.

We define `setZero` as `aeval` so that it is an `AlgHom` (giving `map_mul`, `map_add`, ...
for free; Mathlib has no such lemmas for `modMonomial`). We then *prove*
`setZero_eq_modMonomial` once, and get the rest of the API from `Division.lean`. The working
lemma is `coeff_setZero`.
-/

/-- `p |_{x_k = 0}`, as an algebra map so `map_mul`, `map_add`, ... apply. -/
noncomputable def setZero (k : n) : MvPolynomial n R →ₐ[R] MvPolynomial n R :=
  aeval (Function.update X k 0)

/-- The bridge from `setZero` to Mathlib's `modMonomial`. -/
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

/-- The workhorse decomposition `p = p|_{x_k=0} + x_k ∂ₖp` for `p` affine in `x_k`. Together
with `setZero_mem_supported` and `pderiv_mem_supported`, this replaces "write
`f = a xᵢxⱼ + b xᵢ + c xⱼ + d`". There is no need to isolate variables via `optionEquivLeft`.
It is Mathlib's `modMonomial_add_divMonomial_single` plus `divMonomial_single_eq_pderiv`. -/
theorem eq_setZero_add_X_mul_pderiv {k : n} {p : MvPolynomial n R} (hp : p.degreeOf k ≤ 1) :
    p = setZero k p + X k * pderiv k p := by
  rw [setZero_eq_modMonomial, ← divMonomial_single_eq_pderiv hp,
    modMonomial_add_divMonomial_single]

end Polys

/-! ## 5. The determinantal polynomial and the adjugate -/

section DetPoly

variable {R 𝔽 n : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- `diag(x₁,…,xₙ) + A`. The name mirrors Mathlib's univariate `Matrix.charmatrix` (which is
`X • 1 - A`); note our sign is `+ A`, as in the paper. Mathlib has no multivariate version. -/
noncomputable def Matrix.mvCharmatrix (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  diagonal X + A.map C

/-- The determinantal polynomial `f_A = det(diag(x) + A)`. -/
noncomputable def Matrix.detPoly (A : Matrix n n R) : MvPolynomial n R :=
  A.mvCharmatrix.det

/-- `G = (diag(x) + A)^adj`, with entries `G_ij`. Use Mathlib's `Matrix.adjugate`
(`LinearAlgebra/Matrix/Adjugate.lean`). Its basic API is `adjugate_apply`,
`mul_adjugate`/`adjugate_mul`, `det_eq_sum_mul_adjugate_row`/`_col` (cofactor expansion),
`adjugate_transpose`, and `adjugate_mul_distrib`. -/
noncomputable def Matrix.adjPoly (A : Matrix n n R) : Matrix n n (MvPolynomial n R) :=
  A.mvCharmatrix.adjugate

/-- **TODO**: "the coefficients of `f_A` are the principal minors of `A`", made precise. The
coefficient of `∏_{i ∈ S} xᵢ` is the *complementary* minor `A_{Sᶜ}`.

Mathlib only has the univariate version, `Matrix.coeff_det_one_add_X_smul_eq_sum_minors`
(`LinearAlgebra/Matrix/Charpoly/Coeff.lean`), which is our statement after `xᵢ ↦ X`. Copy its
proof: view `det` as `detRowAlternating`, expand the sum of rows with
`MultilinearMap.map_add_univ`, pull out the scalars with `map_smul_univ`, and finish with
`det_piecewise_one_eq_submatrix_det`. The multivariate case is *easier*, because each `S`
gives a different monomial, so there is no `powersetCard` regrouping. -/
theorem Matrix.coeff_detPoly (A : Matrix n n R) (S : Finset n) :
    A.detPoly.coeff S.exponent = A.principalMinor Sᶜ := by
  sorry

/-- **TODO** -/
theorem Matrix.detPoly_isMultiaffine (A : Matrix n n R) : IsMultiaffine A.detPoly := by
  sorry

/-- The leading coefficient is `1`. This is the normalization hypothesis of Theorem 2.1. -/
theorem Matrix.coeff_univ_detPoly (A : Matrix n n R) :
    A.detPoly.coeff Finset.univ.exponent = 1 := by
  rw [coeff_detPoly, Finset.compl_univ, principalMinor_empty]

/-- **TODO**: the fiber can be described by `f_A`. Every proof in the paper uses this
direction: "`B` in the fiber of `A`" is replaced by "`f_B = f_A`". -/
theorem Matrix.detPoly_eq_iff {A B : Matrix n n R} :
    B.detPoly = A.detPoly ↔ B ∈ A.pmFiber := by
  sorry

/-- **TODO** (Jacobi's formula, the special case used in Thm 2.3): `∂ᵢ f_A = G_ii`. More
generally, `∏_{i ∈ S} ∂ᵢ f_A = det M(S,S)`; we only need `|S| ≤ 2`.

**MISSING.** Mathlib only has univariate forms: `Matrix.derivative_det_one_add_X_smul` and
`coeff_det_one_add_X_smul_one` (`Charpoly/Coeff.lean`). Suggested route: expand along row `i`
with `det_eq_sum_mul_adjugate_row`. Row `i` is the only row containing `xᵢ`, and the cofactors
along row `i` don't use row `i`, so they are killed by `pderiv i`. -/
theorem Matrix.pderiv_detPoly (A : Matrix n n R) (i : n) :
    pderiv i A.detPoly = A.adjPoly i i := by
  sorry

/-- **TODO**: `G_ij ∈ 𝔽[x_k : k ≠ i, j]` for `i ≠ j` (Theorem 2.1(a)). -/
theorem Matrix.adjPoly_mem_supported (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    A.adjPoly i j ∈ supported R ({i, j}ᶜ : Set n) := by
  sorry

/-- **TODO** -/
theorem Matrix.adjPoly_isMultiaffine (A : Matrix n n R) (i j : n) :
    IsMultiaffine (A.adjPoly i j) := by
  sorry

/-- **TODO**: if `B = DAD⁻¹`, then `G_B = D G_A D⁻¹`, i.e. `(G_B)ᵢⱼ = dᵢ (G_A)ᵢⱼ dⱼ⁻¹`. This
is used at the end of the proof of Theorem 4.1. Prove it via `adjugate_mul_distrib`, since
`diag(x)` commutes with `D`. -/
theorem Matrix.adjPoly_diag_conj (A : Matrix n n R) (d : n → Rˣ) (i j : n) :
    (diagonal (fun i ↦ (d i).val) * A * diagonal (fun i ↦ (d i)⁻¹.val)).adjPoly i j =
      C (d i).val * A.adjPoly i j * C (d j)⁻¹.val := by
  sorry

end DetPoly

/-! ## 6. Rayleigh differences and resultants (Section 2) -/

section Rayleigh

variable {R 𝔽 n : Type*} [CommRing R]

/-
Derivatives: `MvPolynomial.pderiv i` is a bundled `Derivation`, so linearity and the Leibniz
rule (`Derivation.leibniz`) are automatic. Key lemmas (`Algebra/MvPolynomial/PDeriv.lean`):
`pderiv_X`, `pderiv_C`, `pderiv_comm`, `coeff_pderiv`, `pderiv_eq_zero_of_notMem_vars`.
-/

/-- The Rayleigh difference `Δᵢⱼ(f) = ∂ᵢf ∂ⱼf - f ∂ᵢ∂ⱼf`. -/
noncomputable def rayleighDiff (i j : n) (f : MvPolynomial n R) : MvPolynomial n R :=
  pderiv i f * pderiv j f - f * pderiv i (pderiv j f)

/-
**The paper's resultant is NOT Mathlib's `Polynomial.resultant`.** Mathlib's
(`RingTheory/Polynomial/Resultant/Basic.lean`) is the Sylvester determinant of two univariate
polynomials, with optional formal degrees `m n`. The paper instead *defines*

  `res_{x_k}(g, h) = g|_{x_k=0} · ∂ₖh − h|_{x_k=0} · ∂ₖg`.

For `g, h` affine in `x_k`, this equals the Sylvester resultant with formal degrees `(1, 1)`.
But the definition is simpler, needs no variable isolation (`optionEquivLeft`), and makes
sense for any `g, h`. So we define it directly.
-/

variable [DecidableEq n]

/-- The paper's resultant `res_{x_k}(g, h)`. -/
noncomputable def res (k : n) (g h : MvPolynomial n R) : MvPolynomial n R :=
  setZero k g * pderiv k h - setZero k h * pderiv k g

/-- `res` is linear over constants in `x_k`. The paper uses this repeatedly, e.g.
`res_{x_k}((-1)^i aᵢ bⱼ, f) = (-1)^i bⱼ res_{x_k}(aᵢ, f)`. -/
theorem res_mul_left {k : n} {c : MvPolynomial n R} (hc : c ∈ supported R ({k}ᶜ : Set n))
    (g h : MvPolynomial n R) : res k (c * g) h = c * res k g h := by
  have hc' : pderiv k c = 0 := pderiv_eq_zero_of_notMem_vars <| by
    rw [mem_vars_iff_degreeOf_ne_zero, not_not, ← mem_supported_compl_singleton_iff]
    exact hc
  simp only [res, map_mul, setZero_of_mem_supported hc, Derivation.leibniz, hc', smul_eq_mul]
  ring

-- Lemma 2.2 can be found in DetPoly.LEAN_Warmup.Grant.MvPolynomial.

variable [Fintype n]

/-- **TODO**, **MISSING** in Mathlib: the Desnanot–Jacobi (Dodgson condensation) identity,
written in terms of the adjugate so no signs appear:
`adj(M)ᵢᵢ adj(M)ⱼⱼ - adj(M)ᵢⱼ adj(M)ⱼᵢ = det M · det M({i,j}ᶜ, {i,j}ᶜ)`.

Mathlib has neither this nor Jacobi's general theorem on minors of the adjugate. Nearby API:
`adjugate_adjugate`, `det_adjugate`, `det_smul_adjugate_adjugate`, `adjugate_fin_two`
(`LinearAlgebra/Matrix/Adjugate.lean`), and Schur complements
(`LinearAlgebra/Matrix/SchurComplement.lean`). -/
theorem Matrix.adjugate_mul_adjugate_sub {M : Matrix n n R} {i j : n} (hij : i ≠ j) :
    M.adjugate i i * M.adjugate j j - M.adjugate i j * M.adjugate j i =
      M.det * (M.principalSubmatrix ({i, j}ᶜ : Finset n)).det := by
  sorry

/-- **Theorem 2.3**. Holds for *all* `i, j` (for `i = j` both sides are `G_ii²`, since
`∂ᵢ²f = 0`). Not needing `i ≠ j` saves case splits later. -/
theorem Matrix.rayleighDiff_detPoly (A : Matrix n n R) (i j : n) :
    rayleighDiff i j A.detPoly = A.adjPoly i j * A.adjPoly j i := by
  sorry

/-- The "only if" half of Theorem 2.1 (condition (b) for the adjugate). It is pure algebra, so
it is **TODO** (ours), not external. We confirmed the sign with sympy. -/
theorem Matrix.res_adjPoly (A : Matrix n n R) {i j k : n} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) : res k (A.adjPoly i j) A.detPoly = A.adjPoly i k * A.adjPoly k j := by
  sorry

end Rayleigh

/-! ## 7. External results the paper cites

Opinion: state these as `theorem ... := by sorry` with a citation, and **never** as `axiom`.
That keeps them visible in `#print axioms` (as `sorryAx`) and in the blueprint dependency
graph, and we can replace them with proofs later.

Suggested scope: the new content of the paper is the `⇒` direction of Theorem 4.1 (building a
second point in the fiber). The `⇐` direction is mostly Loewy's 1986 paper (40 pages), so
take that as an external input first.
-/

section External

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **EXTERNAL**, **Lemma 4.2** ([Hartfiel–Loewy 1984, Thm 1]): for irreducible `A`, every
entry of `G` is nonzero. -/
theorem Matrix.adjPoly_ne_zero {A : Matrix n n 𝔽} (hA : A.IsIrred) (i j : n) :
    A.adjPoly i j ≠ 0 := by
  sorry

/-- **EXTERNAL**, **Theorem 2.1**, "if" direction ([AV22, Thm 3.1]), in the *strong* form that
Lemma 4.5 actually uses. The conclusion also pins down the adjugate (`G_B = g` off the
diagonal), not just `f = f_B`. Check that AV22's proof gives this (it constructs `A` from the
`gᵢⱼ`, so it should). -/
theorem exists_detPoly_eq_of_rayleigh {f : MvPolynomial n 𝔽} (hf : IsMultiaffine f)
    (hlead : f.coeff Finset.univ.exponent = 1) (g : n → n → MvPolynomial n 𝔽)
    (hΔ : ∀ i j, i ≠ j → rayleighDiff i j f = g i j * g j i)
    (hsupp : ∀ i j, i ≠ j → g i j ∈ supported 𝔽 ({i, j}ᶜ : Set n))
    (haff : ∀ i j, IsMultiaffine (g i j))
    (hres : ∀ i j k, i ≠ j → k ≠ i → k ≠ j → res k (g i j) f = g i k * g k j) :
    ∃ B : Matrix n n 𝔽, B.detPoly = f ∧ ∀ i j, i ≠ j → B.adjPoly i j = g i j := by
  sorry

/-- **EXTERNAL** ([Loewy 1986, Thm 1]): irreducible with no cut ⟹ trivial fiber. -/
theorem Matrix.hasTrivialFiber_of_noCut (hn : 4 ≤ Fintype.card n) {A : Matrix n n 𝔽}
    (hA : A.IsIrred) (hcut : ∀ X, ¬ A.HasCut X) : A.HasTrivialFiber := by
  sorry

end External

/-! ## 8. The statements of the paper -/

section Paper

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **Lemma 4.3**, phrased sign-free. The paper writes `G_ij = (-1)^i aᵢ bⱼ`. The `(-1)^i` is
an artifact of the generalized Laplace expansion and would force `n = Fin n`. Instead, absorb
the sign into `aᵢ`; nothing downstream needs it. Families are total functions guarded by
`i ∈ X`. For the other off-diagonal block (`T` in the paper), apply this to `Xᶜ` using
`HasCut.compl`.

On Theorem 3.1 (generalized Laplace expansion): it is **MISSING** from Mathlib, which only
expands along a single row or column (`det_succ_row`, `det_succ_column`,
`det_eq_sum_mul_adjugate_row`). Its sign-heavy form is painful, and the paper uses it *only*
here. Before formalizing it, try a direct argument: write `A[X, Xᶜ] = u vᵀ`
(`rank_le_one_iff_eq_vecMulVec`) and expand the cofactor by multilinearity in the rows of `X`
(`detRowAlternating` with `MultilinearMap.map_add_univ`, as in `coeff_detPoly`). -/
theorem Matrix.adjPoly_eq_mul_of_hasCut (hn : 4 ≤ Fintype.card n) {A : Matrix n n 𝔽}
    (hA : A.IsIrred) {X : Finset n} (hX : A.HasCut X) :
    ∃ a b : n → MvPolynomial n 𝔽,
      (∀ i ∈ X, a i ∈ supported 𝔽 ↑(X.erase i) ∧ a i ≠ 0) ∧
      (∀ j ∉ X, b j ∈ supported 𝔽 ↑(Xᶜ.erase j) ∧ b j ≠ 0) ∧
      ∀ i ∈ X, ∀ j ∉ X, A.adjPoly i j = a i * b j := by
  sorry

/-- **Lemma 4.4**, with the conclusion weakened to `IsSymmetrizable`. That is exactly what the
`αᵢⱼ` give *without* taking square roots. -/
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

/-- **Lemma 4.5**. The conclusion is phrased as "`H` *is* an adjugate", because the proof of
Theorem 4.1 needs `H = G_B` (off the diagonal), not merely `f_B = f_A`. -/
theorem Matrix.exists_adjPoly_eq_cutSwap (hn : 4 ≤ Fintype.card n) {A : Matrix n n 𝔽}
    (hA : A.IsIrred) {X : Finset n} (hX : A.HasCut X) (a b c d : n → MvPolynomial n 𝔽)
    (ha : ∀ i ∈ X, a i ∈ supported 𝔽 ↑(X.erase i))
    (hb : ∀ j ∉ X, b j ∈ supported 𝔽 ↑(Xᶜ.erase j))
    (hc : ∀ i ∉ X, c i ∈ supported 𝔽 ↑(Xᶜ.erase i))
    (hd : ∀ j ∈ X, d j ∈ supported 𝔽 ↑(X.erase j))
    (hR : ∀ i ∈ X, ∀ j ∉ X, A.adjPoly i j = a i * b j)
    (hT : ∀ i ∉ X, ∀ j ∈ X, A.adjPoly i j = c i * d j) :
    ∃ B : Matrix n n 𝔽, B.detPoly = A.detPoly ∧
      ∀ i j, i ≠ j → B.adjPoly i j = cutSwap X A.adjPoly a b c d i j := by
  sorry

/-- First step of the proof of **Theorem 4.1** (`⇒`): reducible matrices have nontrivial fibers.
No `n ≥ 4` is needed here. -/
theorem Matrix.IsReducible.not_hasTrivialFiber {A : Matrix n n 𝔽} (hA : A.IsReducible) :
    ¬ A.HasTrivialFiber := by
  sorry

/-- **Lemma 5.1**. `[Nonempty n]` is needed because the `0 × 0` matrix is irreducible but
`f = 1` is not an irreducible polynomial. `Irreducible` is Mathlib's notion for monoids. -/
theorem Matrix.isIrred_iff_irreducible_detPoly [Nonempty n] (A : Matrix n n 𝔽) :
    A.IsIrred ↔ Irreducible A.detPoly := by
  sorry

/-- **Lemma 6.1**, generalized from symmetric to symmetrizable matrices. The same proof works,
because `μA` symmetric gives `G_ij ∝ G_ji`, so `Δᵢⱼ(f) = (const) · G_ij²`. It is used in the
`⇐` direction of Theorem 4.1. -/
theorem Matrix.IsSymmetrizable.hasTrivialFiber_iff (hn : 4 ≤ Fintype.card n)
    {A : Matrix n n 𝔽} (hA : A.IsSymmetrizable) : A.HasTrivialFiber ↔ A.IsIrred := by
  sorry

/-- **Theorem 4.1** (main theorem), with (a) phrased as `IsSymmetrizable`; see the module
docstring for why. Condition (b) "`rk A[X,Xᶜ] ≥ 2` or `rk A[Xᶜ,X] ≥ 2` for all `X` with
`2 ≤ |X| ≤ n-2`" is literally `∀ X, ¬ A.HasCut X`. -/
theorem Matrix.hasTrivialFiber_iff (hn : 4 ≤ Fintype.card n) (A : Matrix n n 𝔽) :
    A.HasTrivialFiber ↔ A.IsIrred ∧ (A.IsSymmetrizable ∨ ∀ X, ¬ A.HasCut X) := by
  sorry

/-
**Theorem 5.2** (structure theorem), if we get to it: phrase the block form with
`Matrix.BlockTriangular A b` for a labelling `b : n → Fin s` (no permutations). Phrase the
blocks with `A.toSquareBlock b k`, and the factorization as
`A.detPoly = ∏ k, (A.toSquareBlock b k).detPoly'`. Here `detPoly'` must rename the block's
variables into `n` (`rename Subtype.val`), and each factor lies in `supported 𝔽 {i | b i = k}`.
`Matrix.BlockTriangular.det` already gives the determinant factorization.
-/

end Paper

/-! ## 9. Computation

Mathlib polynomials are noncomputable by design. Matrices over `ℚ`, `det`, and hence
`principalMinor` *are* computable. So the paper's examples can be checked by `#eval`, and any
algorithm we write can output matrices directly.

Example 4.6: `A` has a cut at `X = {1, 2}`, and `B` has the same principal minors. We expect
`0` mismatched subsets. -/

/-- Example 4.6, matrix `A`. -/
def ex46A : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2, -1, 1, -2; 1, 1, -3, 6; 1, 2, 1, 1; -1, -2, 2, -1]

/-- Example 4.6, matrix `B`. -/
def ex46B : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2, 1, 1, -2; -1, 1, 2, -4; 1, -3, 1, 1; -1, 3, 2, -1]

#eval (Finset.univ.filter fun S ↦ ex46A.principalMinor S ≠ ex46B.principalMinor S).card

end
