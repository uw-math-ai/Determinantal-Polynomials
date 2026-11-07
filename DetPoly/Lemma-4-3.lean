/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Rogge
-/

module

public import DetPoly.Cut
public import DetPoly.IrreducibleMatrix

/-!
# A cut of `A` is a cut of `(diag(x) + A)^adj` (Lemma 4.3)

The paper's Lemma 4.3 states that if an irreducible `A` has a cut `X`, then
`G = (diag(x₁,…,xₙ) + A)^adj` factors as `G_ij = (-1)^i aᵢ bⱼ` for `i ∈ X`, `j ∈ Xᶜ`. Applying
this to `X` and `Xᶜ` gives `rk G[X,Xᶜ] ≤ 1` and `rk G[Xᶜ,X] ≤ 1`, i.e. `X` is a cut of `G`.

`Matrix.HasCut` is stated over a field, so we view `G` over the fraction field of
`MvPolynomial n 𝔽`. The factorization form is `Matrix.adjPoly_eq_mul_of_hasCut`.
-/

@[expose] public section

open MvPolynomial

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **Lemma 4.3**, rank form: a cut `X` of an irreducible `A` is also a cut of
`G = (diag(x) + A)^adj`, with ranks taken over the fraction field of `𝔽[x]`.

Proof hint: by `rank_le_one_iff_eq_vecMulVec` it suffices to factor `G[X,Xᶜ]` and `G[Xᶜ,X]`
as outer products, which is `Matrix.adjPoly_eq_mul_of_hasCut` applied to `X` and to `Xᶜ`
(`HasCut.compl`). -/
lemma Matrix.hasCut_adjPoly_of_hasCut {A : Matrix n n 𝔽} (hA : A.IsIrred) {X : Finset n}
    (hX : A.HasCut X) :
    (A.mvCharmatrix.adjugate.map
      (algebraMap (MvPolynomial n 𝔽) (FractionRing (MvPolynomial n 𝔽)))).HasCut X := by
  sorry

-- lemma rank_eq_zero_entry {m k : Type*} [Fintype m] [Fintype k]
--     (M : Matrix m k 𝔽) (h : M.rank = 0) (i : m) (j : k) : M i j = 0 := by
--   by_contra hij
--   have hpos : 0 < M.rank := by
--     rw [Matrix.rank_eq_finrank_span_cols]
--     apply Module.finrank_pos_iff_exists_ne_zero.mpr
--     refine ⟨⟨M.col j, Submodule.subset_span ⟨j, rfl⟩⟩, ?_⟩
--     intro hc
--     apply hij
--     have := congrArg (fun v : Submodule.span 𝔽 (Set.range M.col) => (v : m → 𝔽) i) hc
--     simpa using this
--   omega

/-- If `A` is irreducible and `X` is a rank-one cut, then the ranks of
`M[X, Xᶜ]` and `M[Xᶜ, X]` are both exactly `1`
-/
lemma Matrix.isIrred_hasCut_rk1 {A : Matrix n n 𝔽} (hA : A.IsIrred)
    {X : Finset n} (hX : A.HasCut X) :
    ((A.finsetSubmatrix X Xᶜ).rank = 1) ∧
    ((A.finsetSubmatrix Xᶜ X).rank = 1) := by
  -- SLOP (anders) Haven't fully understood this tactic chain yet.
  -- The two statements are swapped by `X ↔ Xᶜ`, so it suffices to prove the first for any cut.
  suffices key : ∀ Y : Finset n, A.HasCut Y → (A.finsetSubmatrix Y Yᶜ).rank = 1 from
    ⟨key X hX, by have h := key Xᶜ hX.compl; rwa [compl_compl] at h⟩
  rintro Y ⟨hYcard, hYcCard, hUpperBd, -⟩
  refine le_antisymm hUpperBd ?_
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ Y, ∃ j ∈ Yᶜ, A i j ≠ 0 := by
    by_contra hall
    push Not at hall
    have hne : Yᶜ.Nonempty := Finset.card_pos.mp (by omega)
    have hnu : Yᶜ ≠ Finset.univ := by
      intro h
      rw [Finset.compl_eq_univ_iff] at h
      simp [h] at hYcard
    exact (Matrix.isReducible_iff_exists_finset.mpr
      ⟨Yᶜ, hne, hnu, fun i hi j hj => hall i (by simpa using hi) j hj⟩) hA
  rw [Matrix.rank_eq_finrank_span_cols]
  refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩⟩, ?_⟩
  intro hc
  apply hij
  have := congrArg (fun v : Submodule.span 𝔽 (Set.range _) => (v : Y → 𝔽) ⟨i, hi⟩) hc
  simpa using this

/-- second statement of lemma 4.3: If `rk M[X, Xᶜ] = 1`, then for all
`i ∈ X`, there exists `a_i ∈ 𝔽[x_k : k ∈ X ∖ {i}]` such that for all `j in Xᶜ`,
`M_{X, X_i ∪ j} = c_j a_i`, where the constants `c_j ∈ 𝔽` do not depend on `i`.

The minor `M_{X, X_i ∪ j}` is taken with columns indexed by `X` via the bijection
`X ≃ X_i ∪ j` sending `i ↦ j` (`Function.update`). This differs from the paper's
increasing-order minor by a sign, which is absorbed into `a_i`. -/
lemma Matrix.hasCut_minors_multiples {A : Matrix n n 𝔽} (hA : A.IsIrred)
    {X : Finset n} (hX : A.HasCut X) :
    ∃ (a : n → MvPolynomial n 𝔽) (c : n → 𝔽), ∀ i (hi : i ∈ X),
      a i ∈ supported 𝔽 ↑(X.erase i) ∧ ∀ j ∉ X,
        (A.mvCharmatrix.submatrix ((↑) : X → n)
          (Function.update ((↑) : X → n) ⟨i, hi⟩ j)).det = C (c j) * a i := sorry
end
