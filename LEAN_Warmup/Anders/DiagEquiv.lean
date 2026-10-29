/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anders Lewis
-/
module

public import Mathlib

/-!
# Diagonal equivalence of matrices

`M ~ N` iff `M = L N R` for invertible diagonal `L`, `R`. This is two-sided scaling, not the
paper's diagonal similarity `B = D A D⁻¹`.
-/

@[expose] public section

variable {R m n : Type*} [CommRing R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

namespace Matrix

/-- `M = diag(l) * N * diag(r)` for some vectors of units `l`, `r`. -/
def DiagEquiv (M N : Matrix m n R) : Prop :=
  ∃ (l : m → Rˣ) (r : n → Rˣ), -- Vectors in Lean are just functions from
                               -- finite sets to their data type.
    M = diagonal (fun i ↦ (l i).val) * N * diagonal (fun j ↦ (r j).val)

theorem DiagEquiv.equivalence : Equivalence (DiagEquiv (R := R) (m := m) (n := n)) where
  refl := by
    intro M
    -- The identity matrix takes us from M to M
    use 1, 1
    simp
  symm := by
    rintro M N ⟨l, r, rfl⟩
    -- Use the elementwise inverse of l and r to get from M to N
    use l⁻¹, r⁻¹
    -- Not taking i and j forces you to do matrix multiplications, which gets ugly.
    ext i j
    simp [mul_assoc]
  trans := by
    rintro X Y Z ⟨l1, r1, rfl⟩ ⟨l2, r2, rfl⟩
    -- Just compose the transforms to get from L to R
    use l1 * l2, r2 * r1
    ext i j
    simp [mul_assoc]

end Matrix

end
