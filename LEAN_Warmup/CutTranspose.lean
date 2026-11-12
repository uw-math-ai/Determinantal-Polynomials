/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/

module

public import LEAN_Warmup.ClaudeMathlib

/-!
# Definitions and statements for "Characterizing and Testing Principal Minor Equivalence"

Definitions for [Chatterjee–Ghosh–Gurjar–Raj, STOC 2025] (CGGR; full version arXiv:2410.01961)
and statements of its results leading to Theorem 1.1, together with the alternate form of
[Al Ahmadieh, arXiv:2309.00806, Theorem 4.1] that follows from it. Tags used in docstrings:

* **TODO**: our proof, still `sorry`.
* **EXTERNAL**: a result cited from another paper, `sorry` for now.

## Conventions

* As in `LEAN_Warmup.ClaudeMathlib`: index type `n` with `[Fintype n] [DecidableEq n]`, subsets
  are `Finset n`, and families indexed by a subset are total functions `n → _`.
* CGGR define `ct(A, X)` through one fixed rank-one factorization of the cross blocks (the first
  nonzero row and column). We use the definitions of `DetPoly.CutTranspose` instead:
  `f : A.R1CutFactorization` (a cut `f.X` with `A[X,Xᶜ] = p qᵀ`, `A[Xᶜ,X] = u vᵀ`; it extends
  `A.R1Factorization`, which has no size condition), `A.cutTranspose f`,
  and `IsCutTranspose A X B` (`B = ct(A, X)` for *some* factorization). For
  irreducible `A` all cut-transposes at `X` are diagonally similar (`IsCutTranspose.diagSimilar`,
  CGGR Remark 2.11).
* Statements about `ct(A, X)` are phrased as `∀ B, IsCutTranspose A X B → …`.
* A sequence of cut-transposes from `A` to `C` is `p : CutTransposePath A C` (in
  `DetPoly.CutTranspose`), with `p.length` and the list of cuts `p.cuts`.
* CGGR's "`A + D` is nonsingular" for a diagonal `D` is `IsUnit (A + diagonal d).det`.
* CGGR's Lemmas 2.1, 2.9 and 2.15 compare `(A + D)^adj` and `(B + D)^adj`. These lose the scalar
  `det(A + D)` (`adj(-M) = adj M` for odd `n`), so we add the hypothesis
  `(A + diagonal d).det = (B + diagonal d).det`, which PME matrices satisfy
  (`PMEquiv.det_add_diagonal_eq`).

## Dictionary

| CGGR | Lean |
|---|---|
| `A` and `B` are PME | `PMEquiv A B` (`pmEquiv_iff_mem_pmFiber`) |
| `A` is DS / DE to `B` | `DiagSimilar A B` / `DiagEquivalent A B` |
| `X` is a cut of `A` | `A.HasCut X` |
| `X` is a minimal cut of `A` | `A.IsMinimalCut X` |
| all off-diagonal entries of `A` are nonzero | `A.OffDiagNeZero` |
| `ct(A, X)` | any `B` with `IsCutTranspose A X B` |
| cut-transpose equivalent w.r.t. `𝒳` | `CutTransposeEquivWrt A Xs B` |
| `A[S]` | `A.principalSubmatrix ↑S` |
| `A[S + t]` | `A.principalSubmatrix ↑(insert t S)` |
| `(A + D)^adj` | `(A + diagonal d).adjugate` |

## Not stated here

* Lemma 2.4 (PME of reducible matrices reduces to the irreducible diagonal blocks; this is
  Al Ahmadieh's Corollary 5.4).
* Observation 3.7 and Claim 3.8 (lifting a cut sequence from `A[Sᶜ + s]` to `A`): bookkeeping
  for the induction in Theorem 1.1, best stated once the proof is being formalized.
* The first part of Lemma 3.3 (only its "in particular" is stated).
* Sections 4–5 (the algorithm and the PIT application), beyond Claim 4.1.
-/

@[expose] public section

open Matrix

namespace Matrix

/-! ## Principal minor equivalence (Section 2.1) -/

section PME

variable {R n : Type*} [DecidableEq n] [CommRing R]

/-- `A` and `B` are *principal minor equivalent*: all corresponding principal minors agree. -/
def PMEquiv (A B : Matrix n n R) : Prop :=
  ∀ S : Finset n, A.principalMinor S = B.principalMinor S

theorem pmEquiv_iff_mem_pmFiber {A B : Matrix n n R} : PMEquiv A B ↔ B ∈ A.pmFiber :=
  ⟨fun h ↦ funext fun S ↦ (h S).symm, fun h S ↦ (congrFun h S).symm⟩

@[refl]
theorem PMEquiv.refl (A : Matrix n n R) : PMEquiv A A := fun _ ↦ rfl

@[symm]
theorem PMEquiv.symm {A B : Matrix n n R} (h : PMEquiv A B) : PMEquiv B A := fun S ↦ (h S).symm

@[trans]
theorem PMEquiv.trans {A B C : Matrix n n R} (h₁ : PMEquiv A B) (h₂ : PMEquiv B C) :
    PMEquiv A C := fun S ↦ (h₁ S).trans (h₂ S)

/-- A matrix is PME to its transpose. -/
theorem pmEquiv_transpose (A : Matrix n n R) : PMEquiv A Aᵀ :=
  fun S ↦ (det_transpose (A.principalSubmatrix (S : Set n))).symm

theorem PMEquiv.transpose {A B : Matrix n n R} (h : PMEquiv A B) : PMEquiv Aᵀ Bᵀ :=
  (pmEquiv_transpose A).symm.trans (h.trans (pmEquiv_transpose B))

/-- **TODO**. Principal submatrices of PME matrices are PME (used throughout Section 3). Hint:
a principal minor of `A[T]` at `S : Finset T` is the principal minor of `A` at the image of `S`
(`Matrix.det_reindex_self` / `det_submatrix_equiv_self`). -/
theorem PMEquiv.principalSubmatrix {A B : Matrix n n R} (h : PMEquiv A B) (T : Finset n) :
    PMEquiv (A.principalSubmatrix (T : Set n)) (B.principalSubmatrix (T : Set n)) := by
  sorry

variable [Fintype n]

/-- Diagonally equivalent matrices are PME. -/
theorem DiagEquivalent.pmEquiv {A B : Matrix n n R} (h : DiagEquivalent A B) : PMEquiv A B :=
  congrFun h.principalMinor_eq

/-- Diagonally similar matrices are PME. -/
theorem DiagSimilar.pmEquiv {A B : Matrix n n R} (h : DiagSimilar A B) : PMEquiv A B :=
  h.diagEquivalent.pmEquiv

/-- PME matrices have the same determinant after any diagonal shift (`f_A(d) = f_B(d)`). -/
theorem PMEquiv.det_add_diagonal_eq {A B : Matrix n n R} (h : PMEquiv A B) (d : n → R) :
    (A + diagonal d).det = (B + diagonal d).det := by
  rw [add_comm, det_diagonal_add, add_comm, det_diagonal_add]
  exact Finset.sum_congr rfl fun S _ ↦ by rw [h Sᶜ]

/-- PME is equality of determinantal polynomials. -/
theorem pmEquiv_iff_detpoly_eq {A B : Matrix n n R} : PMEquiv A B ↔ A.detpoly = B.detpoly := by
  rw [detpoly_eq_iff_principalMinor_eq, funext_iff, PMEquiv]

/-- `A ∈ 𝒟(n)` iff everything PME to `A` is diagonally equivalent to `A`. -/
theorem hasTrivialFiber_iff_forall_pmEquiv {A : Matrix n n R} :
    A.HasTrivialFiber ↔ ∀ B, PMEquiv A B → DiagEquivalent B A :=
  ⟨fun h B hB ↦ h B (pmEquiv_iff_mem_pmFiber.mp hB),
    fun h B hB ↦ h B (pmEquiv_iff_mem_pmFiber.mpr hB)⟩

end PME

/-! ## Irreducibility and cuts (Sections 2.2–2.3) -/

section OffDiag

variable {𝔽 n : Type*} [Field 𝔽]

/-- All off-diagonal entries of `A` are nonzero. CGGR reduce Theorem 1.1 to this case. -/
def OffDiagNeZero (A : Matrix n n 𝔽) : Prop := ∀ i j, i ≠ j → A i j ≠ 0

/-- A matrix with nonzero off-diagonal entries is irreducible (remark after Definition 2.2). -/
theorem OffDiagNeZero.isIrred [Finite n] {A : Matrix n n 𝔽} (hA : A.OffDiagNeZero) :
    A.IsIrred := by
  classical
  have := Fintype.ofFinite n
  by_contra h
  obtain ⟨S, ⟨j, hj⟩, hne, hS⟩ := isReducible_iff_exists_finset.mp h
  obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by simpa [Finset.eq_univ_iff_forall] using hne
  exact hA i j (by rintro rfl; exact hi hj) (hS i hi j hj)

theorem OffDiagNeZero.transpose {A : Matrix n n 𝔽} (hA : A.OffDiagNeZero) :
    Aᵀ.OffDiagNeZero := fun i j hij ↦ hA j i hij.symm

/-- PME preserves irreducibility, by Lemma 5.1 (`isIrred_iff_irreducible_detpoly`). -/
theorem PMEquiv.isIrred [DecidableEq n] [Finite n] [Nonempty n] {A B : Matrix n n 𝔽}
    (h : PMEquiv A B) (hA : A.IsIrred) : B.IsIrred := by
  have := Fintype.ofFinite n
  rw [isIrred_iff_irreducible_detpoly] at hA ⊢
  rwa [← pmEquiv_iff_detpoly_eq.mp h]

end OffDiag

section Cuts

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- `X` is a *minimal cut* of `A`: no cut of `A` is properly contained in `X`. -/
def IsMinimalCut (A : Matrix n n 𝔽) (X : Finset n) : Prop :=
  A.HasCut X ∧ ∀ Y ⊆ X, A.HasCut Y → Y = X

/-- A cut of size two is minimal. -/
theorem HasCut.isMinimalCut_of_card_eq_two {A : Matrix n n 𝔽} {X : Finset n} (h : A.HasCut X)
    (hX : X.card = 2) : A.IsMinimalCut X :=
  ⟨h, fun _ hYX hY ↦ Finset.eq_of_subset_of_card_le hYX (hX ▸ hY.two_le_card)⟩

/-- **TODO**. Every matrix with a cut has a minimal cut (well-founded induction on `⊂`). -/
theorem HasCut.exists_isMinimalCut {A : Matrix n n 𝔽} {X : Finset n} (h : A.HasCut X) :
    ∃ Y ⊆ X, A.IsMinimalCut Y := by
  sorry

end Cuts

/-! ## The cut-transpose operation (Section 2.5)

The definitions and the basic API (involution, transpose, complement, Lemma 2.12) are in
`DetPoly.CutTranspose`. -/

theorem cutTranspose_eq_cutSwap {R n : Type*} [DecidableEq n] [Mul R]
    {A : Matrix n n R} (f : A.R1Factorization) :
    A.cutTranspose f = cutSwap f.X A f.p f.q f.u f.v := rfl

section CutTransposeField

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **TODO**, **Remark 2.11**: for irreducible `A`, the cut-transpose at `X` is unique up to
diagonal similarity. Hint: the cross blocks have rank exactly one
(`Matrix.HasCut.rank_eq_one`), so two factorizations differ by `(λp, λ⁻¹q, μu, μ⁻¹v)` on the
relevant indices; conjugate by `diag(λμ on X, 1 on Xᶜ)`. -/
theorem IsCutTranspose.diagSimilar {A B C : Matrix n n 𝔽} {X : Finset n} (hA : A.IsIrred)
    (hB : IsCutTranspose A X B) (hC : IsCutTranspose A X C) :
    DiagSimilar B C := by
  sorry

/-- **Lemma 2.12** (Al Ahmadieh, Lemma 4.5): cut-transpose preserves all principal minors.
This is `Matrix.IsCutTranspose.principalMinor_eq`. -/
theorem IsCutTranspose.pmEquiv {A B : Matrix n n 𝔽} {X : Finset n} (h : IsCutTranspose A X B) :
    PMEquiv A B :=
  congrFun h.principalMinor_eq

/-- **TODO**. Cut-transpose is compatible with diagonal equivalence: if `A' ~DE A` then every
cut-transpose of `A'` at `X` is diagonally equivalent to some cut-transpose of `A` at `X`.
Hint: `ct(A, X)ᵀ = ct(Aᵀ, X)` (`transpose_cutTranspose`), and for `A' = DAD⁻¹` with the
induced factorization, `ct(A', X) = D̃ ct(A, X) D̃⁻¹` where `D̃ = diag(D_X, D_{Xᶜ}⁻¹)`. For a
factorization of `A'` that is not induced from one of `A`, pull it back along `D` instead. -/
theorem DiagEquivalent.exists_isCutTranspose {A A' B' : Matrix n n 𝔽} {X : Finset n}
    (h : DiagEquivalent A' A) (hB' : IsCutTranspose A' X B') :
    ∃ B, IsCutTranspose A X B ∧ DiagEquivalent B' B := by
  sorry

/-- **TODO**. Diagonally equivalent matrices have the same cuts. Hint: `HasCut.transpose`, and
rescale a cut factorization along the diagonal similarity. -/
theorem DiagEquivalent.hasCut {A B : Matrix n n 𝔽} {X : Finset n} (h : DiagEquivalent A B)
    (hX : A.HasCut X) : B.HasCut X := by
  sorry

end CutTransposeField

/-! ## Cut-transpose equivalence (Definition 2.14) -/

section Chain

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- `A` and `B` are *cut-transpose equivalent with respect to* the cut sequence `Xs`: a path
of cut-transposes along `Xs` ends at a matrix diagonally equivalent to `B`. -/
def CutTransposeEquivWrt (A : Matrix n n 𝔽) (Xs : List (Finset n)) (B : Matrix n n 𝔽) : Prop :=
  ∃ (C : Matrix n n 𝔽) (p : CutTransposePath A C), p.cuts = Xs ∧ DiagEquivalent C B

/-- `A` and `B` are *cut-transpose equivalent*: `A` is connected by cut-transposes to a matrix
diagonally equivalent to `B`. -/
def CutTransposeEquiv (A B : Matrix n n 𝔽) : Prop :=
  ∃ C, CutTransposeConnected A C ∧ DiagEquivalent C B

theorem cutTransposeEquiv_iff_exists_cutTransposeEquivWrt {A B : Matrix n n 𝔽} :
    CutTransposeEquiv A B ↔ ∃ Xs, CutTransposeEquivWrt A Xs B :=
  ⟨fun ⟨C, ⟨p⟩, hC⟩ ↦ ⟨p.cuts, C, p, rfl, hC⟩, fun ⟨_, C, p, _, hC⟩ ↦ ⟨C, ⟨p⟩, hC⟩⟩

theorem CutTransposePath.pmEquiv {A C : Matrix n n 𝔽} (p : CutTransposePath A C) :
    PMEquiv A C :=
  congrFun p.principalMinor_eq

/-- The easy direction of Theorem 1.1. -/
theorem CutTransposeEquiv.pmEquiv {A B : Matrix n n 𝔽} (h : CutTransposeEquiv A B) :
    PMEquiv A B :=
  let ⟨_, ⟨p⟩, hCB⟩ := h
  p.pmEquiv.trans hCB.pmEquiv

theorem CutTransposeEquivWrt.pmEquiv {A B : Matrix n n 𝔽} {Xs : List (Finset n)}
    (h : CutTransposeEquivWrt A Xs B) : PMEquiv A B :=
  (cutTransposeEquiv_iff_exists_cutTransposeEquivWrt.mpr ⟨Xs, h⟩).pmEquiv

theorem DiagEquivalent.cutTransposeEquiv {A B : Matrix n n 𝔽} (h : DiagEquivalent A B) :
    CutTransposeEquiv A B :=
  ⟨A, ⟨.nil A⟩, h⟩

/-- If every cut-transpose of `A` stays in the diagonal-equivalence class of `A`, then so does
the end of every path starting in that class. -/
theorem CutTransposePath.diagEquivalent {A A' C : Matrix n n 𝔽}
    (hA : ∀ X B, IsCutTranspose A X B → DiagEquivalent B A)
    (p : CutTransposePath A' C) (hA' : DiagEquivalent A' A) : DiagEquivalent C A := by
  induction p with
  | nil => exact hA'
  | cons f hB _ ih =>
    obtain ⟨B, hB', hBB⟩ := hA'.exists_isCutTranspose (isCutTranspose_of_cons f hB)
    exact ih (hBB.trans (hA _ B hB'))

end Chain

/-! ## Passing to the adjugate (Lemmas 2.1, 2.6, 2.9, 2.13, 2.15, Claim 4.1)

These reduce Theorem 1.1 to matrices with nonzero off-diagonal entries. -/

section Adjugate

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **EXTERNAL**, **Lemma 2.1** (from [Hartfiel–Loewy 1984, Lemma 4]).
We also assume `det(A + D) = det(B + D)`, which holds when `A` and `B` are PME. Hint:
`adj M = det M • M⁻¹` and the principal minors of `M⁻¹` are those of `M` on complements divided
by `det M` (Jacobi's complementary minor formula). -/
theorem pmEquiv_adjugate_add_diagonal_iff {A B : Matrix n n 𝔽} {d : n → 𝔽}
    (hA : IsUnit (A + diagonal d).det) (hdet : (A + diagonal d).det = (B + diagonal d).det) :
    PMEquiv (A + diagonal d).adjugate (B + diagonal d).adjugate ↔ PMEquiv A B := by
  sorry

/-- **TODO**, **Lemma 2.6**: `A` and `(A + D)^adj` have the same cuts. Compare Lemma 4.3 of
Al Ahmadieh's paper (`Matrix.hasCut_adjPoly_of_hasCut`), which is the same statement before
specializing `x ↦ d`. -/
theorem hasCut_adjugate_add_diagonal_iff {A : Matrix n n 𝔽} {d : n → 𝔽}
    (hA : IsUnit (A + diagonal d).det) {X : Finset n} :
    (A + diagonal d).adjugate.HasCut X ↔ A.HasCut X := by
  sorry

/-- **EXTERNAL**, **Lemma 2.9** (from [Hartfiel–Loewy 1984, Lemma 4]). As in Lemma 2.1, we add
`det(A + D) = det(B + D)` to CGGR's hypotheses. Hint: `adj M = det M • M⁻¹`, and
`D (A + diag d) D⁻¹ = D A D⁻¹ + diag d` for diagonal `D`. -/
theorem diagSimilar_adjugate_add_diagonal_iff {A B : Matrix n n 𝔽} {d : n → 𝔽}
    (hA : IsUnit (A + diagonal d).det) (hdet : (A + diagonal d).det = (B + diagonal d).det) :
    DiagSimilar (A + diagonal d).adjugate (B + diagonal d).adjugate ↔ DiagSimilar A B := by
  sorry

/-- **TODO**, **Lemma 2.13**: cut-transpose and adjugate commute up to diagonal similarity.
(That `X` is a cut of `A^adj` is part of the lemma.)
Note `A` must benonsingular: a cut-transpose can change the rank, so `A^adj = 0` while
`ct(A, X)^adj ≠ 0`. CGGR only apply it to nonsingular `A + D`. Hint: by the nullity theorem,
`rank A⁻¹[X, Xᶜ] = rank A[X, Xᶜ]`. -/
theorem IsCutTranspose.adjugate {A B : Matrix n n 𝔽} {X : Finset n} (hA : A.IsIrred)
    (hdet : IsUnit A.det) (h : IsCutTranspose A X B) :
    A.adjugate.HasCut X ∧ ∃ B', IsCutTranspose A.adjugate X B' ∧ DiagSimilar B.adjugate B' := by
  sorry

/-- **TODO**, **Lemma 2.15**. As in Lemma 2.1, we add `det(A + D) = det(B + D)` to CGGR's
hypotheses: for odd `n` and irreducible nonsingular `A` with zero diagonal, `B = -A` and `d = 0`
violate the statement without it. -/
theorem cutTransposeEquivWrt_adjugate_add_diagonal_iff {A B : Matrix n n 𝔽} (hA : A.IsIrred)
    (hB : B.IsIrred) {d : n → 𝔽} (hAd : IsUnit (A + diagonal d).det)
    (hdet : (A + diagonal d).det = (B + diagonal d).det) (Xs : List (Finset n)) :
    CutTransposeEquivWrt (A + diagonal d).adjugate Xs (B + diagonal d).adjugate ↔
      CutTransposeEquivWrt A Xs B := by
  sorry

/-- **TODO**, **Claim 4.1**, existence part only. CGGR need `|𝔽| > 10 n⁵`; we assume `𝔽`
infinite. Hint: every entry of `(diag(x) + A)^adj` is a nonzero polynomial (Lemma 4.2,
`Matrix.adjPoly_ne_zero`) and so is `f_A`; a finite product of nonzero polynomials over an
infinite field has a non-root (`MvPolynomial.funext`). -/
theorem exists_diagonal_offDiagNeZero_adjugate [Infinite 𝔽] {A B : Matrix n n 𝔽}
    (hA : A.IsIrred) (hB : B.IsIrred) :
    ∃ d : n → 𝔽, IsUnit (A + diagonal d).det ∧ IsUnit (B + diagonal d).det ∧
      (∀ i j, (A + diagonal d).adjugate i j ≠ 0) ∧ ∀ i j, (B + diagonal d).adjugate i j ≠ 0 := by
  sorry

end Adjugate

/-! ## The characterization (Section 3) -/

section Characterization

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **EXTERNAL**, **Lemma 2.8 (1)** ([Hartfiel–Loewy 1984, Thm 3] for `n = 2, 3`; `n ≤ 1` is
trivial). Part (2) is `Matrix.hasTrivialFiber_of_noCut`. -/
theorem hasTrivialFiber_of_card_le_three (hn : Fintype.card n ≤ 3) {A : Matrix n n 𝔽}
    (hA : A.IsIrred) : A.HasTrivialFiber := by
  sorry

/-- **TODO**, **Lemma 3.1**: the base case `n = 4`. -/
theorem diagEquivalent_or_cutTranspose_of_card_eq_four (hn : Fintype.card n = 4)
    {A B : Matrix n n 𝔽} (hA : A.OffDiagNeZero) (h : PMEquiv A B) :
    DiagEquivalent A B ∨ ((∃ X, A.HasCut X ∧ B.HasCut X) ∧
      ∀ X, B.HasCut X → ∀ C, IsCutTranspose A X C → DiagEquivalent C B) := by
  sorry

/-- **TODO**, **Lemma 3.2 (1)**: if `T` or `Tᶜ` is contained in `S` or `Sᶜ`, then `T` is a cut
of `A` iff it is a cut of `ct(A, S)`. -/
theorem IsCutTranspose.hasCut_iff_of_nested {A C : Matrix n n 𝔽} {S T : Finset n}
    (hA : A.OffDiagNeZero) (hC : IsCutTranspose A S C)
    (hT : T ⊆ S ∨ T ⊆ Sᶜ ∨ Tᶜ ⊆ S ∨ Tᶜ ⊆ Sᶜ) : C.HasCut T ↔ A.HasCut T := by
  sorry

/-- **TODO**, **Lemma 3.2 (2)**: otherwise, `T` is a cut of `A` iff `T Δ S` is a cut of
`ct(A, S)`. -/
theorem IsCutTranspose.hasCut_symmDiff_iff {A C : Matrix n n 𝔽} {S T : Finset n}
    (hA : A.OffDiagNeZero) (hC : IsCutTranspose A S C)
    (hT : ¬ (T ⊆ S ∨ T ⊆ Sᶜ ∨ Tᶜ ⊆ S ∨ Tᶜ ⊆ Sᶜ)) : C.HasCut (symmDiff T S) ↔ A.HasCut T := by
  sorry

/-- **TODO**, **Lemma 3.3**, "in particular": if `S` is a minimal cut with `|S| > 2` and
`t ∉ S`, then `A[S + t]` has no cut. -/
theorem IsMinimalCut.not_hasCut_principalSubmatrix_insert {A : Matrix n n 𝔽} {S : Finset n}
    (hA : A.OffDiagNeZero) (hS : A.IsMinimalCut S) (hS2 : 2 < S.card) {t : n} (ht : t ∉ S)
    (Y : Finset ((insert t S : Finset n) : Set n)) :
    ¬ (A.principalSubmatrix ((insert t S : Finset n) : Set n)).HasCut Y := by
  sorry

/-- **TODO**, **Lemma 3.4**: if `S` is a cut of `A`, `t ∈ S`, and `Y ⊆ Sᶜ` is a cut of
`A[Sᶜ + t]`, then `Y` is a cut of `A`. -/
theorem HasCut.of_principalSubmatrix_insert_compl {A : Matrix n n 𝔽} {S : Finset n}
    (hA : A.OffDiagNeZero) (hS : A.HasCut S) {t : n} (ht : t ∈ S)
    {Y : Finset ((insert t Sᶜ : Finset n) : Set n)}
    (hY : (A.principalSubmatrix ((insert t Sᶜ : Finset n) : Set n)).HasCut Y)
    (hYt : ∀ y ∈ Y, (y : n) ≠ t) :
    A.HasCut (Y.map (Function.Embedding.subtype _)) := by
  sorry

/-- **TODO**, **Lemma 3.5**, in the form used in the proof of Theorem 1.1: a size-two cut of
`A` is a cut of `B`, or of a cut-transpose of `B`. (CGGR give the cut of `B` explicitly:
`{t ∈ Sᶜ | A[S + t] ~DS B[S + t]} ∪ {sᵢ}` for either `sᵢ ∈ S`.) -/
theorem PMEquiv.hasCut_or_of_card_eq_two {A B : Matrix n n 𝔽} (hA : A.OffDiagNeZero)
    (hB : B.OffDiagNeZero) (h : PMEquiv A B) {S : Finset n} (hS : A.HasCut S)
    (hS2 : S.card = 2) :
    B.HasCut S ∨ ∃ X, B.HasCut X ∧ ∀ C, IsCutTranspose B X C → C.HasCut S := by
  sorry

/-- **TODO**, **Lemma 3.6**: a minimal cut of `A` of size greater than two is a cut of `B`. -/
theorem PMEquiv.hasCut_of_isMinimalCut {A B : Matrix n n 𝔽} (hA : A.OffDiagNeZero)
    (hB : B.OffDiagNeZero) (h : PMEquiv A B) {S : Finset n} (hS : A.IsMinimalCut S)
    (hS2 : 2 < S.card) : B.HasCut S := by
  sorry

/-- **TODO**, **Lemma 3.9**: if `S` is a minimal cut of `A` and a cut of `B`, `s ∈ S`, and
`A[Sᶜ + s] ~DS B[Sᶜ + s]`, then `A ~DS B` or `ct(A, Sᶜ) ~DS B`. We write `ct(A, Sᶜ)` as `Cᵀ` for
a cut-transpose `C` of `A` at `S` (`cutTranspose_compl`, `transpose_cutTranspose`). -/
theorem PMEquiv.diagSimilar_or_cutTranspose {A B : Matrix n n 𝔽} (hA : A.OffDiagNeZero)
    (hB : B.OffDiagNeZero) (h : PMEquiv A B) {S : Finset n} (hS : A.IsMinimalCut S)
    (hSB : B.HasCut S) {s : n} (hs : s ∈ S)
    (hDS : DiagSimilar (A.principalSubmatrix ((insert s Sᶜ : Finset n) : Set n))
      (B.principalSubmatrix ((insert s Sᶜ : Finset n) : Set n))) :
    DiagSimilar A B ∨ ∀ C, IsCutTranspose A S C → DiagSimilar Cᵀ B := by
  sorry

/-- **EXTERNAL**, **Theorem 1.1**, hard direction: irreducible PME matrices are cut-transpose
equivalent, through a cut sequence of length at most `2n`. (CGGR state `k < 2n`; `≤` also
covers the empty matrix.) -/
theorem PMEquiv.exists_cutTransposeEquivWrt {A B : Matrix n n 𝔽} (hA : A.IsIrred)
    (hB : B.IsIrred) (h : PMEquiv A B) :
    ∃ Xs : List (Finset n), Xs.length ≤ 2 * Fintype.card n ∧ CutTransposeEquivWrt A Xs B := by
  sorry

/-- **Theorem 1.1**: irreducible matrices are PME iff they are cut-transpose equivalent. -/
theorem pmEquiv_iff_cutTransposeEquivWrt {A B : Matrix n n 𝔽} (hA : A.IsIrred)
    (hB : B.IsIrred) :
    PMEquiv A B ↔
      ∃ Xs : List (Finset n), Xs.length ≤ 2 * Fintype.card n ∧ CutTransposeEquivWrt A Xs B :=
  ⟨fun h ↦ h.exists_cutTransposeEquivWrt hA hB, fun ⟨_, _, h⟩ ↦ h.pmEquiv⟩

theorem pmEquiv_iff_cutTransposeEquiv {A B : Matrix n n 𝔽} (hA : A.IsIrred) (hB : B.IsIrred) :
    PMEquiv A B ↔ CutTransposeEquiv A B :=
  ⟨fun h ↦ let ⟨Xs, _, hXs⟩ := h.exists_cutTransposeEquivWrt hA hB
    cutTransposeEquiv_iff_exists_cutTransposeEquivWrt.mpr ⟨Xs, hXs⟩,
    CutTransposeEquiv.pmEquiv⟩

end Characterization

/-! ## Alternate Theorem 4.1 of Al Ahmadieh's paper -/

section

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- A cut whose cut-transpose leaves the diagonal-equivalence class gives a nontrivial
fiber. -/
theorem not_hasTrivialFiber_of_isCutTranspose {A B : Matrix n n 𝔽} {X : Finset n}
    (hB : IsCutTranspose A X B) (hBA : ¬ DiagEquivalent B A) : ¬ A.HasTrivialFiber :=
  fun h ↦ hBA (hasTrivialFiber_iff_forall_pmEquiv.mp h B hB.pmEquiv)

/-- **Theorem 4.1**: `A ∈ 𝒟(n)` iff `A` is irreducible and every cut-transpose of
`A` is diagonally equivalent to `A`. `→` needs `IsReducible.not_hasTrivialFiber` and Lemma 2.12;
`←` needs Theorem 1.1, Lemma 5.1, and
compatibility of cut-transpose with diagonal equivalence. -/
theorem hasTrivialFiber_iff_forall_isCutTranspose [Nonempty n] (A : Matrix n n 𝔽) :
    A.HasTrivialFiber ↔
      A.IsIrred ∧ ∀ X B, IsCutTranspose A X B → DiagEquivalent B A := by
  constructor
  · intro h
    exact ⟨by_contra fun hA ↦ IsReducible.not_hasTrivialFiber hA h,
      fun X B hB ↦ hasTrivialFiber_iff_forall_pmEquiv.mp h B hB.pmEquiv⟩
  · rintro ⟨hA, hct⟩
    rw [hasTrivialFiber_iff_forall_pmEquiv]
    intro B hAB
    obtain ⟨Xs, -, C, p, -, hCB⟩ := hAB.exists_cutTransposeEquivWrt hA (hAB.isIrred hA)
    exact hCB.symm.trans (p.diagEquivalent hct (DiagEquivalent.refl A))

/-- The no-cut case (Loewy's theorem) as a special case of the theorem. -/
theorem hasTrivialFiber_of_noCut' [Nonempty n] {A : Matrix n n 𝔽} (hA : A.IsIrred)
    (hcut : ∀ X, ¬ A.HasCut X) : A.HasTrivialFiber :=
  (hasTrivialFiber_iff_forall_isCutTranspose A).mpr 
    ⟨hA, fun X _ hX ↦ absurd hX.hasCut_left (hcut X)⟩

end

end Matrix

/-! ## Examples

All of these are computable over `ℚ`. Indices are `0, 1, 2, 3` and the cut is `X = {0, 1}`,
with both cross blocks all ones, so `p = q = u = v = 1`. -/

/-- Shaoda's example matrix -/
def exMat : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 2, 1, 1;
     3, 0, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 0]

/-- A matrix whose cut-transpose at `{0, 1}` is not diagonally equivalent to it. -/
def exActive : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 2, 1, 1;
     3, 0, 1, 1;
     1, 1, 0, 2;
     1, 1, 3, 0]

/-- The cut-transpose of `exActive` at `{0, 1}`. -/
def exActiveCT : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 2, 1, 1;
     3, 0, 1, 1;
     1, 1, 0, 3;
     1, 1, 2, 0]

/-- The all-ones factorization at `{0, 1}` of `exMat`. -/
def exMatFact : exMat.R1CutFactorization :=
  ⟨⟨{0, 1}, 1, 1, 1, 1,
    by intro i hi j hj; fin_cases i <;> fin_cases j <;> simp_all [exMat],
    by intro i hi j hj; fin_cases i <;> fin_cases j <;> simp_all [exMat]⟩, by decide, by decide⟩

/-- The all-ones factorization at `{0, 1}` of `exActive`. -/
def exActiveFact : exActive.R1CutFactorization :=
  ⟨⟨{0, 1}, 1, 1, 1, 1,
    by intro i hi j hj; fin_cases i <;> fin_cases j <;> simp_all [exActive],
    by intro i hi j hj; fin_cases i <;> fin_cases j <;> simp_all [exActive]⟩, by decide, by decide⟩

example : exMat.cutTranspose exMatFact = exMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cutTranspose_apply, exMatFact, exMat]

example : exActive.cutTranspose exActiveFact = exActiveCT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cutTranspose_apply, exActiveFact, exActive, exActiveCT]

set_option linter.hashCommand false in
#guard (Finset.univ.filter fun S : Finset (Fin 4) ↦
  (exActive.submatrix (fun i : S ↦ (i : Fin 4)) (fun i : S ↦ (i : Fin 4))).det ≠
    (exActiveCT.submatrix (fun i : S ↦ (i : Fin 4)) (fun i : S ↦ (i : Fin 4))).det).card = 0

/-- Example 4.6 of Al Ahmadieh's paper transposes the `X` block, so `ex46B` is the transpose
of a cut-transpose of `ex46A` at `{0, 1}` (`cutTranspose_compl`). -/
example : ex46A.cutTranspose
    ⟨{0, 1}, ![1, -3, 0, 0], ![0, 0, 1, -2], ![0, 0, 1, -1], ![1, 2, 0, 0],
      by intro i hi j hj; fin_cases i <;> fin_cases j <;> norm_num [ex46A] at *,
      by intro i hi j hj; fin_cases i <;> fin_cases j <;> simp_all [ex46A]⟩ = ex46Bᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [cutTranspose_apply, ex46A, ex46B]

end
