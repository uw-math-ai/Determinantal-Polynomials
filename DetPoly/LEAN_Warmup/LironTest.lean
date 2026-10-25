import Mathlib

/-! # Lean Warmup PS1 2(a): conjugating by a diagonal matrix -/

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

/-- The (i, j) entry of D A D⁻¹ where D = diag(d), is dᵢ aᵢⱼ dⱼ⁻¹ -/
theorem diag_conj_apply (d : n → F) (A : Matrix n n F) (i j : n) :
    (diagonal d * A * diagonal (fun k => (d k)⁻¹)) i j = d i * A i j * (d j)⁻¹ := by
  rw [mul_diagonal, diagonal_mul]
