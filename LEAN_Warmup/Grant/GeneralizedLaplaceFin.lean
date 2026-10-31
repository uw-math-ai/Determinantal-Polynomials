/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.GeneralizedLaplace

/-!
# Generalized Laplace expansion over `Fin N`, as in the paper

The paper's form of the generalized Laplace expansion ([arXiv:2309.00806], Thm 3.1) for
`Fin N`, with minors indexed increasingly and the sign `(-1) ^ (ΣS + ΣT)`. This is the
`LinearOrder` version `Matrix.det_eq_sum_neg_one_pow_mul_det_mul_det`, where the position
`#{b | b < a}` of `a : Fin N` is `a` itself.
-/

public section

open Finset

variable {R : Type*} [CommRing R] {N : ℕ}

namespace Matrix

theorem card_compl_fin {S : Finset (Fin N)} {k : ℕ} (hS : #S = k) : #Sᶜ = N - k := by
  rw [card_compl, Fintype.card_fin, hS]

/-- **Generalized Laplace expansion** along the set of rows `S` ([arXiv:2309.00806], Thm 3.1),
with minors indexed increasingly and the sign `(-1) ^ (ΣS + ΣT)`. -/
theorem det_eq_sum_neg_one_pow_mul_det_mul_det_fin (A : Matrix (Fin N) (Fin N) R)
    {k : ℕ} (S : Finset (Fin N)) (hS : #S = k) :
    A.det = ∑ T : {T : Finset (Fin N) // #T = k},
      (-1) ^ (∑ i ∈ S, (i : ℕ) + ∑ j ∈ T.1, (j : ℕ)) *
        (A.submatrix (S.orderEmbOfFin hS) (T.1.orderEmbOfFin T.2)).det *
        (A.submatrix (Sᶜ.orderEmbOfFin (card_compl_fin hS))
          (T.1ᶜ.orderEmbOfFin (card_compl_fin T.2))).det := by
  have hpos (a : Fin N) : #{b | b < a} = (a : ℕ) := by
    rw [← Fin.card_Iio]
    congr 1
    ext
    simp
  simpa only [hpos] using det_eq_sum_neg_one_pow_mul_det_mul_det A S hS (card_compl_fin hS)

end Matrix

end
