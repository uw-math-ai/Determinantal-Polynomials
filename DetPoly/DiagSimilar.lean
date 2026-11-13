/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anders Lewis, Grant Yang
-/

module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import DetPoly.Basic

/-! # Diagonal similarity and diagonal equivalence

`DiagSimilar` means diagonal conjugacy. `DiagEquivalent` also permits transpose,
following Al Ahmadieh, "The fiber of the principal minor map".
-/

@[expose] public section
namespace Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

section CommSemiring
variable [CommSemiring R]

/-- Conjugacy by an invertible diagonal matrix. -/
def DiagSimilar (M N : Matrix n n R) : Prop :=
  ∃ d : n → Rˣ,
    M = diagonal (fun i ↦ (d i).val) * N * diagonal (fun i ↦ (d i)⁻¹.val)

theorem DiagSimilar.equivalence : Equivalence (DiagSimilar (R := R) (n := n)) where
  refl M := by use 1; simp
  symm h := by
    obtain ⟨d, rfl⟩ := h
    use d⁻¹
    ext i j
    simp [mul_assoc]
  trans h₁ h₂ := by
    rcases h₁, h₂ with ⟨⟨d₁, rfl⟩, ⟨d₂, rfl⟩⟩
    use d₁ * d₂
    ext i j
    simp [mul_assoc]

/-- Diagonal similarity is preserved by transpose (using the inverse diagonal). -/
theorem DiagSimilar.transpose {M N : Matrix n n R} (h : DiagSimilar M N) :
    DiagSimilar Mᵀ Nᵀ := by
  rcases h with ⟨d, rfl⟩
  refine ⟨d⁻¹, ?_⟩
  simp [transpose_mul, Matrix.mul_assoc]

/-- Diagonal similarity preserves the zero pattern. -/
theorem DiagSimilar.apply_eq_zero_iff {M N : Matrix n n R} (h : DiagSimilar M N) (i j : n) :
    M i j = 0 ↔ N i j = 0 := by
  obtain ⟨d, rfl⟩ := h
  simp [diagonal_mul, mul_diagonal]

/-- Diagonal similarity, allowing a transpose, as in the principal minor paper. -/
def DiagEquivalent (M N : Matrix n n R) : Prop :=
  DiagSimilar M N ∨ DiagSimilar M Nᵀ

theorem DiagEquivalent.equivalence : Equivalence (DiagEquivalent (R := R) (n := n)) where
  refl M := Or.inl (DiagSimilar.equivalence.refl M)
  symm h := by
    rcases h with hl | ⟨d, rfl⟩
    · exact Or.inl (DiagSimilar.equivalence.symm hl)
    · right
      use d
      ext i j
      simp [mul_left_comm, mul_assoc]
  trans h₁ h₂ := by
    rcases h₁, h₂ with ⟨hl₁ | hr₁, hl₂ | hr₂⟩
    · exact Or.inl (DiagSimilar.equivalence.trans hl₁ hl₂)
    · exact Or.inr (DiagSimilar.equivalence.trans hl₁ hr₂)
    · exact Or.inr (DiagSimilar.equivalence.trans hr₁ hl₂.transpose)
    · exact Or.inl (by simpa using DiagSimilar.equivalence.trans hr₁ hr₂.transpose)

@[refl, simp]
theorem DiagSimilar.refl (M : Matrix n n R) : DiagSimilar M M :=
  DiagSimilar.equivalence.refl M

@[symm]
theorem DiagSimilar.symm {M N : Matrix n n R} (h : DiagSimilar M N) : DiagSimilar N M :=
  DiagSimilar.equivalence.symm h

@[trans]
theorem DiagSimilar.trans {M N P : Matrix n n R}
    (hMN : DiagSimilar M N) (hNP : DiagSimilar N P) : DiagSimilar M P :=
  DiagSimilar.equivalence.trans hMN hNP

/-- The setoid of matrices under diagonal conjugacy. -/
def diagSimilarSetoid : Setoid (Matrix n n R) :=
  ⟨DiagSimilar, DiagSimilar.equivalence⟩

@[refl, simp]
theorem DiagEquivalent.refl (M : Matrix n n R) : DiagEquivalent M M :=
  DiagEquivalent.equivalence.refl M

@[symm]
theorem DiagEquivalent.symm {M N : Matrix n n R} (h : DiagEquivalent M N) : DiagEquivalent N M :=
  DiagEquivalent.equivalence.symm h

@[trans]
theorem DiagEquivalent.trans {M N P : Matrix n n R}
    (hMN : DiagEquivalent M N) (hNP : DiagEquivalent N P) : DiagEquivalent M P :=
  DiagEquivalent.equivalence.trans hMN hNP

/-- The setoid of matrices under diagonal conjugacy and transpose. -/
def diagEquivalentSetoid : Setoid (Matrix n n R) :=
  ⟨DiagEquivalent, DiagEquivalent.equivalence⟩

/-- Diagonal similarity implies diagonal equivalence. -/
theorem DiagSimilar.diagEquivalent {M N : Matrix n n R}
    (h : DiagSimilar M N) : DiagEquivalent M N :=
  Or.inl h

/-- For a symmetric target, diagonal equivalence reduces to diagonal similarity. -/
theorem diagEquivalent_iff_diagSimilar_of_isSymm {M N : Matrix n n R} (hN : N.IsSymm) :
    DiagEquivalent M N ↔ DiagSimilar M N := by
  simp [DiagEquivalent, hN.eq]

end CommSemiring

variable [CommRing R]

omit [Fintype n] in
@[simp]
theorem principalMinor_transpose (M : Matrix n n R) : Mᵀ.principalMinor = M.principalMinor :=
  funext fun _ ↦ det_transpose _

/-- Diagonally similar matrices have the same principal minors. -/
theorem DiagSimilar.principalMinor_eq {M N : Matrix n n R} (h : DiagSimilar M N) :
    M.principalMinor = N.principalMinor := by
  obtain ⟨d, rfl⟩ := h
  ext S
  have : (diagonal (fun i ↦ (d i).val) * N * diagonal (fun i ↦ (d i)⁻¹.val)).setSubmatrix S S =
      diagonal (fun i : S ↦ (d i).val) * N.setSubmatrix S S *
        diagonal (fun i : S ↦ (d i)⁻¹.val) := by
    ext; simp
  rw [principalMinor, this, det_mul_comm, ← Matrix.mul_assoc, diagonal_mul_diagonal]
  simp

/-- Diagonally equivalent matrices have the same principal minors. -/
theorem DiagEquivalent.principalMinor_eq {M N : Matrix n n R} (h : DiagEquivalent M N) :
    M.principalMinor = N.principalMinor := by
  rcases h with h | h
  · exact h.principalMinor_eq
  · rw [h.principalMinor_eq, principalMinor_transpose]

end Matrix

end
