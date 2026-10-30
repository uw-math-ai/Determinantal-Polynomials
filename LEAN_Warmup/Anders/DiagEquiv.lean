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

variable {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

namespace Matrix

/-- `M = diag(l) * N * diag(r)` for some vectors of units `l`, `r`. -/
def TwoSidedDiagEquiv (M N : Matrix m n R) : Prop :=
  ∃ (l : m → Rˣ) (r : n → Rˣ),
    M = diagonal (fun i ↦ (l i).val) * N * diagonal (fun j ↦ (r j).val)

theorem TwoSidedDiagEquiv.equivalence :
    Equivalence (TwoSidedDiagEquiv (R := R) (m := m) (n := n)) where
  refl := by
    intro M
    use 1, 1
    simp
  symm := by
    rintro M N ⟨l, r, rfl⟩
    use l⁻¹, r⁻¹
    ext i j
    simp [mul_assoc]
  trans := by
    rintro X Y Z ⟨l1, r1, rfl⟩ ⟨l2, r2, rfl⟩
    use l1 * l2, r2 * r1
    ext i j
    simp [mul_assoc]

@[refl, simp]
theorem TwoSidedDiagEquiv.refl (M : Matrix m n R) : TwoSidedDiagEquiv M M :=
  TwoSidedDiagEquiv.equivalence.refl M

@[symm]
theorem TwoSidedDiagEquiv.symm {M N : Matrix m n R} (h :
    TwoSidedDiagEquiv M N) :
    TwoSidedDiagEquiv N M :=
  TwoSidedDiagEquiv.equivalence.symm h

@[trans]
theorem TwoSidedDiagEquiv.trans {M N P : Matrix m n R}
    (hMN : TwoSidedDiagEquiv M N) (hNP : TwoSidedDiagEquiv N P) : TwoSidedDiagEquiv M P :=
  TwoSidedDiagEquiv.equivalence.trans hMN hNP

/-- The setoid of matrices under two-sided invertible diagonal scaling. -/
def twoSidedDiagEquivSetoid : Setoid (Matrix m n R) :=
  ⟨TwoSidedDiagEquiv, TwoSidedDiagEquiv.equivalence⟩

/-- Transposing both matrices preserves diagonal equivalence. -/
theorem TwoSidedDiagEquiv.transpose {M N : Matrix m n R} (h : TwoSidedDiagEquiv M N) :
    TwoSidedDiagEquiv Mᵀ Nᵀ := by
  rcases h with ⟨l, r, rfl⟩
  refine ⟨r, l, ?_⟩
  simp [transpose_mul, Matrix.mul_assoc]

/-- Two square matrices are diagonally equivalent, possibly after transposing the second. -/
def TwoSidedDiagEquivUpToTranspose (M N : Matrix n n R) : Prop :=
  TwoSidedDiagEquiv M N ∨ TwoSidedDiagEquiv M Nᵀ

theorem TwoSidedDiagEquivUpToTranspose.equivalence :
    Equivalence (TwoSidedDiagEquivUpToTranspose (R := R) (n := n)) where
  refl M := Or.inl (TwoSidedDiagEquiv.equivalence.refl M)
  symm h := by
    rcases h with hl | ⟨l, r, rfl⟩
    · exact Or.inl (TwoSidedDiagEquiv.equivalence.symm hl)
    · right
      use r⁻¹, l⁻¹
      ext i j
      simp [mul_assoc]
  trans h₁ h₂ := by
    rcases h₁, h₂ with ⟨hl₁ | hr₁, hl₂ | hr₂⟩
    · exact Or.inl (TwoSidedDiagEquiv.equivalence.trans hl₁ hl₂)
    · exact Or.inr (TwoSidedDiagEquiv.equivalence.trans hl₁ hr₂)
    · exact Or.inr (TwoSidedDiagEquiv.equivalence.trans hr₁ hl₂.transpose)
    · exact Or.inl (by simpa using TwoSidedDiagEquiv.equivalence.trans hr₁ hr₂.transpose)

@[refl, simp]
theorem TwoSidedDiagEquivUpToTranspose.refl (M : Matrix n n R) :
    TwoSidedDiagEquivUpToTranspose M M :=
  TwoSidedDiagEquivUpToTranspose.equivalence.refl M

@[symm]
theorem TwoSidedDiagEquivUpToTranspose.symm {M N : Matrix n n R}
    (h : TwoSidedDiagEquivUpToTranspose M N) : TwoSidedDiagEquivUpToTranspose N M :=
  TwoSidedDiagEquivUpToTranspose.equivalence.symm h

@[trans]
theorem TwoSidedDiagEquivUpToTranspose.trans {M N P : Matrix n n R}
    (hMN :
    TwoSidedDiagEquivUpToTranspose M N) (hNP :
    TwoSidedDiagEquivUpToTranspose N P) :
    TwoSidedDiagEquivUpToTranspose M P :=
  TwoSidedDiagEquivUpToTranspose.equivalence.trans hMN hNP

/-- Diagonal equivalence implies diagonal equivalence up to transpose. -/
theorem TwoSidedDiagEquiv.twoSidedDiagEquivUpToTranspose {M N : Matrix n n R}
    (h : TwoSidedDiagEquiv M N) : TwoSidedDiagEquivUpToTranspose M N :=
  Or.inl h

/-- The setoid of square matrices under diagonal scaling and transpose. -/
def twoSidedDiagEquivUpToTransposeSetoid : Setoid (Matrix n n R) :=
  ⟨TwoSidedDiagEquivUpToTranspose, TwoSidedDiagEquivUpToTranspose.equivalence⟩

end Matrix

end
