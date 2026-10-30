/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.LinearAlgebra.Matrix.Block

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

variable {R n : Type*} [Zero R]

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

end Matrix

end
