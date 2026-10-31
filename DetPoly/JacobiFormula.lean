/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Jacobi's formula for derivations

For a derivation `D` of a commutative ring `A` and `M : Matrix n n A`,
`D (det M) = ∑ i, det (M with row i replaced by D (M i ·))`
(`Derivation.leibniz_det`). Applied to `MvPolynomial.pderiv`, this is the multivariate Jacobi
formula. Mathlib has Jacobi's formula only for `Polynomial.derivative` of `det (1 + X • M)`.

The proof expands `det` as a sum over permutations and uses the Leibniz rule for finite
products (`Derivation.leibniz_prod`).
-/

public section

open Finset Matrix

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A]
  [Module A M] [Module R M] (D : Derivation R A M)

/-- The **Leibniz rule** for a finite product. -/
theorem leibniz_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) • D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, leibniz, ih, sum_insert ha, erase_insert ha, smul_sum, add_comm]
    congr 1
    refine sum_congr rfl ?_
    intro _ hi
    rw [erase_insert_of_ne (ne_of_mem_of_not_mem hi ha).symm,
      prod_insert fun h ↦ ha (mem_of_mem_erase h), mul_smul]

end Derivation

namespace Derivation

variable {R A n : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq n] [Fintype n]

/-- **Jacobi's formula** for a derivation: `D (det M)` is the sum over rows `i` of the
determinant of `M` with row `i` differentiated. -/
theorem leibniz_det (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j ↦ D (M i j)).det := by
  simp_rw [det_apply, map_sum]
  rw [sum_comm]
  refine sum_congr rfl ?_
  intro σ _
  simp_rw [Units.smul_def]
  rw [map_zsmul, leibniz_prod, ← smul_sum]
  conv_rhs => rw [← Equiv.sum_comp σ]
  congr 1
  refine sum_congr rfl ?_
  intro j _
  rw [← mul_prod_erase univ _ (mem_univ j), updateRow_self, smul_eq_mul, mul_comm]
  congr 1
  refine prod_congr rfl ?_
  intro _ hk
  rw [updateRow_ne (σ.injective.ne (ne_of_mem_erase hk))]

end Derivation

end
