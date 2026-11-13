/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.LinearAlgebra.Matrix.Block
public import DetPoly.DiagSimilar

/-!
# Reducible and irreducible matrices

A square matrix `A` is *irreducible* if the digraph with an edge `i ⟶ j` whenever
`A i j ≠ 0` is strongly connected; equivalently, no simultaneous permutation of rows and
columns makes `A` block upper triangular with at least two diagonal blocks.

Mathlib's `Matrix.IsIrreducible` is the Perron–Frobenius notion for nonnegative matrices
(edges are *positive* entries), so it does not apply over a general field. We copy its design
with `0 < A i j` replaced by `A i j ≠ 0`.

## Main results

* `Matrix.isReducible_iff_exists_set`: `A` is reducible iff `A i j = 0` for all `i ∉ S`,
  `j ∈ S`, for some nonempty proper `S`.
* `Matrix.isReducible_iff_exists_finset`: the same, with a `Finset`.
* `Matrix.isReducible_iff_blockTriangular`: `A` is `Matrix.BlockTriangular` for a surjective
  labelling `n → Bool`. This is the form to use with `Matrix.BlockTriangular.det`.

## Implementation notes

We use `Quiver.IsStronglyConnected`, not `Quiver.IsSStronglyConnected` (positive-length paths)
as Mathlib's `Matrix.IsIrreducible` does. They differ only for `1 × 1` matrices: `!![0]` is
irreducible in the paper's sense, consistent with Lemma 5.1 (`x + a` is irreducible).

The `0 × 0` matrix is irreducible, but `f_A = 1` is not an irreducible polynomial.
-/

@[expose] public section

namespace Matrix

open Quiver

variable {R n : Type*}

section Zero

variable [Zero R]

/-- The directed graph (quiver) associated with a matrix `A`, with an edge `i ⟶ j` iff
`A i j ≠ 0`. This is `Matrix.toQuiver` with "positive" replaced by "nonzero". -/
@[instance_reducible]
def toQuiver' (A : Matrix n n R) : Quiver n :=
  ⟨fun i j => PLift (A i j ≠ 0)⟩

/-- `A` is irreducible, in the paper's sense: the digraph `A.toQuiver'` of nonzero entries is
strongly connected. Compare `Matrix.IsIrreducible`, the nonnegative version. -/
def IsIrred (A : Matrix n n R) : Prop :=
  @IsStronglyConnected n A.toQuiver'

/-- `A` is reducible: after a simultaneous permutation of rows and columns, `A` is block upper
triangular with at least two diagonal blocks. See `isReducible_iff_exists_set`. -/
def IsReducible (A : Matrix n n R) : Prop := ¬ A.IsIrred

/-- `A` is reducible iff, after putting `S` first, `A = [[A_SS, *], [0, A_S'S']]` for some
nonempty proper `S`. -/
theorem isReducible_iff_exists_set {A : Matrix n n R} : A.IsReducible ↔
    ∃ S : Set n, S.Nonempty ∧ Sᶜ.Nonempty ∧ ∀ i ∉ S, ∀ j ∈ S, A i j = 0 := by
  let := A.toQuiver'
  constructor
  · intro h
    simp only [IsReducible, IsIrred, isStronglyConnected_iff, not_forall] at h
    obtain ⟨i, j, hij⟩ := h
    -- `S` is the set of vertices that can reach `j`.
    refine ⟨{k | Nonempty (Path k j)}, ⟨j, ⟨Path.nil⟩⟩, ⟨i, hij⟩, fun k hk l ⟨p⟩ => ?_⟩
    by_contra hkl
    exact hk ⟨(Hom.toPath (⟨hkl⟩ : k ⟶ l)).comp p⟩
  · rintro ⟨S, ⟨j, hj⟩, ⟨i, hi⟩, hS⟩ hirr
    obtain ⟨p⟩ := hirr i j
    -- Every vertex that can reach a vertex of `S` lies in `S`.
    have key : ∀ {k} (q : Path i k), k ∈ S → i ∈ S := by
      intro k q
      induction q with
      | nil => exact id
      | @cons k l _ e ih => exact fun hl => ih (not_not.mp fun hk => e.down (hS k hk l hl))
    exact hi (key p hj)

/-- `isReducible_iff_exists_set` with a `Finset`. -/
theorem isReducible_iff_exists_finset [Fintype n] {A : Matrix n n R} : A.IsReducible ↔
    ∃ S : Finset n, S.Nonempty ∧ S ≠ Finset.univ ∧ ∀ i ∉ S, ∀ j ∈ S, A i j = 0 := by
  classical
  rw [isReducible_iff_exists_set]
  constructor
  · rintro ⟨S, hS, hSc, h⟩
    refine ⟨S.toFinset, by simpa using hS, ?_, by simpa using h⟩
    simpa [Finset.eq_univ_iff_forall, Set.nonempty_compl, Set.eq_univ_iff_forall] using hSc
  · rintro ⟨S, hS, hSc, h⟩
    refine ⟨S, hS, ?_, h⟩
    simpa [Finset.eq_univ_iff_forall, Set.nonempty_compl, Set.eq_univ_iff_forall] using hSc

/-- `A` is reducible iff it is block triangular (`Matrix.BlockTriangular`) with respect to a
labelling `b : n → Bool` that takes both values. The first block is `b ⁻¹' {false}`. -/
theorem isReducible_iff_blockTriangular {A : Matrix n n R} : A.IsReducible ↔
    ∃ b : n → Bool, Function.Surjective b ∧ A.BlockTriangular b := by
  rw [isReducible_iff_exists_set]
  constructor
  · rintro ⟨S, ⟨j, hj⟩, ⟨i, hi⟩, hS⟩
    classical
    refine ⟨fun k => decide (k ∉ S), ?_, fun k l hlk => ?_⟩
    · rintro (_ | _)
      exacts [⟨j, by simpa using hj⟩, ⟨i, by simpa using hi⟩]
    · simp only [Bool.lt_iff, decide_eq_false_iff_not, not_not, decide_eq_true_eq] at hlk
      exact hS k hlk.2 l hlk.1
  · rintro ⟨b, hb, hA⟩
    obtain ⟨j, hj⟩ := hb false
    obtain ⟨i, hi⟩ := hb true
    refine ⟨{k | b k = false}, ⟨j, hj⟩, ⟨i, by simp [hi]⟩, fun k hk l hl => hA ?_⟩
    simp_all


theorem blockTriangular_of_subset (A : Matrix n n R) (S : Finset n)
    (hS : ∀ i ∉ S, ∀ j ∈ S, A i j = 0) : A.BlockTriangular (fun i ↦ i ∉ S) := by
  intro i j hij
  obtain ⟨-, h⟩ := lt_iff_le_not_ge.mp hij
  simp only [le_Prop_eq, not_imp, not_not] at h
  exact hS i h.1 j h.2

end Zero

section DiagEquiv

variable [DecidableEq n] [Fintype n]

/-- Two block triangular matrices that agree on the diagonal blocks have the same
determinant. -/
theorem BlockTriangular.det_eq_det {R α : Type*} [CommRing R] [LinearOrder α] {m : Type*}
    [Fintype m] [DecidableEq m] {b : m → α} {M N : Matrix m m R} (hM : M.BlockTriangular b)
    (hN : N.BlockTriangular b) (h : ∀ i j, b i = b j → M i j = N i j) : M.det = N.det := by
  classical
  rw [hM.det, hN.det]
  refine Finset.prod_congr rfl fun a _ ↦ congrArg det ?_
  ext i j
  exact h _ _ (i.2.trans j.2.symm)

/-- **Al Ahmadieh, Theorem 4.1 (⇒), reducible case.** A reducible matrix has a matrix with the
same principal minors that is not diagonally equivalent to it. If `A = [[E, F], [0, G]]`,
change one entry of `F`: the principal minors only see `E` and `G`, while diagonal
equivalence preserves the zero pattern of `A` or of `Aᵀ`. -/
theorem IsReducible.exists_principalMinor_eq_not_diagEquivalent [CommRing R] [Nontrivial R]
    {A : Matrix n n R} (hA : A.IsReducible) :
    ∃ B : Matrix n n R, A.principalMinor = B.principalMinor ∧ ¬ A.DiagEquivalent B := by
  classical
  obtain ⟨b, hb, hAb⟩ := isReducible_iff_blockTriangular.mp hA
  obtain ⟨i, hi⟩ := hb false
  obtain ⟨j, hj⟩ := hb true
  have hji : A j i = 0 := hAb (by simp [hi, hj])
  have hij : i ≠ j := by rintro rfl; simp_all
  -- `B` is `A` with the entry `(i, j)` of the upper right block made zero iff it was nonzero.
  let B := A.updateRow i (Function.update (A i) j (if A i j = 0 then 1 else 0))
  have hB : ∀ k l, (k, l) ≠ (i, j) → B k l = A k l := by
    intro k l hkl
    by_cases hk : k = i
    · subst hk; simp_all [B]
    · simp [B, hk]
  have hBb : B.BlockTriangular b := fun k l hlk ↦ by
    rw [hB k l (by rintro ⟨⟩; rw [hi, hj] at hlk; exact absurd hlk (by decide))]
    exact hAb hlk
  refine ⟨B, funext fun T ↦ ?_, ?_⟩
  · refine (hAb.submatrix (f := Subtype.val (p := (· ∈ (T : Set n))))).det_eq_det
      hBb.submatrix fun k l hkl ↦ (hB _ _ ?_).symm
    rintro ⟨⟩
    simp_all
  · have hBij : B i j = if A i j = 0 then 1 else 0 := by simp [B]
    rintro (h | h)
    · have := h.apply_eq_zero_iff i j
      split_ifs at hBij <;> simp_all
    · have h₁ := h.apply_eq_zero_iff i j
      have h₂ := h.apply_eq_zero_iff j i
      rw [transpose_apply, hB j i (by simp [hij.symm])] at h₁
      rw [transpose_apply] at h₂
      split_ifs at hBij <;> simp_all

end DiagEquiv

end Matrix

end
