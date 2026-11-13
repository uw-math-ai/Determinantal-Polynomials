/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Rogge
-/

module

public import DetPoly.CutTranspose

/-!
# A cut of `A` is a cut of `(diag(x) + A)^adj` (Lemma 4.3)

The paper's Lemma 4.3 states that if an irreducible `A` has a cut `X`, then
`G = (diag(x₁,…,xₙ) + A)^adj` factors as `G_ij = (-1)^i aᵢ bⱼ` for `i ∈ X`, `j ∈ Xᶜ`. Applying
this to `X` and `Xᶜ` factors both cross blocks of `G`, i.e. `X` is a cut of `G` over
`MvPolynomial n 𝔽` (`Matrix.HasCut` asks for a factorization, so no fraction field is needed).
The factorization form with support conditions is `Matrix.adjPoly_eq_mul_of_hasCut`.
-/

@[expose] public section

open MvPolynomial

variable {𝔽 n : Type*} [Fintype n] [DecidableEq n] [Field 𝔽]

/-- **Lemma 4.3**, cut form: a cut `X` of an irreducible `A` is also a cut of
`G = (diag(x) + A)^adj` over `𝔽[x]`.

Proof hint: an `R1CutFactorization` of `G` at `X` is `Matrix.adjPoly_eq_mul_of_hasCut` applied
to `X` and to `Xᶜ` (`HasCut.compl`); its key step is
`Matrix.adjugate_fromBlocks_vecMulVec_apply₁₂`. -/
lemma Matrix.hasCut_adjPoly_of_hasCut {A : Matrix n n 𝔽} (hA : A.IsIrred) {X : Finset n}
    (hX : A.HasCut X) : A.mvCharmatrix.adjugate.HasCut X := by
  sorry

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
