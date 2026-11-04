import Mathlib

/-!
# Lemma 3.2 — increasing-order shuffle permutations

This file formalizes the definitions and the reduction of Lemma 3.2
from two arbitrary subsets to the sign of a single shuffle.

The one remaining gap is explicitly marked `sorry`: proving the
single-shuffle sign by induction on the size of its subset.

All indices are zero-based (`Fin n`). `indexSum` adds one to each index
to match the paper's convention [n] = {1, ..., n}.
-/

open scoped BigOperators

namespace Lemma32

noncomputable section

/-! ## 1. Sums used in the parity formula -/

/-- Sum of the one-based positions of the elements of `S`. -/
def indexSum {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  Finset.sum S (fun i : Fin n => i.val + 1)

/-- The sum `1 + 2 + ... + k`. -/
def triangular (k : ℕ) : ℕ :=
  Finset.sum (Finset.range k) (fun j : ℕ => j + 1)

/-- The triangle sum gains exactly the new final term. -/
lemma triangular_succ (k : ℕ) :
    triangular (k + 1) = triangular k + (k + 1) := by
  change (Finset.range (k + 1)).sum (fun j : ℕ => j + 1) =
    (Finset.range k).sum (fun j : ℕ => j + 1) + (k + 1)
  exact Finset.sum_range_succ (fun j : ℕ => j + 1) k

/-- Removing an element separates its contribution to the index sum. -/
lemma indexSum_erase {n : ℕ}
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    indexSum S = (i.val + 1) + indexSum (S.erase i) := by
  change S.sum (fun j : Fin n => j.val + 1) =
    (i.val + 1) + (S.erase i).sum (fun j : Fin n => j.val + 1)
  exact (Finset.add_sum_erase S (fun j : Fin n => j.val + 1) hi).symm

/-- Removing a member decreases the cardinality by one. -/
lemma card_erase_step {n : ℕ}
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    (S.erase i).card + 1 = S.card := by
  exact Finset.card_erase_add_one hi

/-! ## 2. The actual increasing-order shuffle -/

/-!
`shuffle T` is the permutation whose output sequence consists of

1. the elements of `T` in increasing order;
2. the elements of `Tᶜ` in increasing order.

`finSumEquivOfFinset` supplies those two order-preserving enumerations.
The preceding equivalences merely identify `Fin n` with the pair of
blocks of sizes `T.card` and `Tᶜ.card`.
-/
noncomputable def shuffle {n : ℕ}
    (T : Finset (Fin n)) : Equiv.Perm (Fin n) := by
  classical
  have hcard : n = T.card + Tᶜ.card := by
    simp
  let e₁ : Fin n ≃ Fin (T.card + Tᶜ.card) :=
    (Fin.castOrderIso hcard).toEquiv
  let e₂ : Fin (T.card + Tᶜ.card) ≃
      (Fin T.card ⊕ Fin Tᶜ.card) :=
    (finSumFinEquiv (m := T.card) (n := Tᶜ.card)).symm
  let e₃ : (Fin T.card ⊕ Fin Tᶜ.card) ≃ Fin n :=
    finSumEquivOfFinset (s := T) rfl rfl
  exact (e₁.trans e₂).trans e₃

/-!
For equal-size subsets `S` and `T`, the two-line permutation is

    sigma = shuffle(T) ∘ shuffle(S)^{-1}.

It sends the increasing enumeration of `S` to that of `T`, and the
increasing enumeration of `Sᶜ` to that of `Tᶜ`.
-/
noncomputable def twoLine {n : ℕ}
    (S T : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  (shuffle S).symm.trans (shuffle T)

/-- Sign of the composition of the two ordered shuffles. -/
lemma sign_twoLine {n : ℕ} (S T : Finset (Fin n)) :
    Equiv.Perm.sign (twoLine S T) =
      Equiv.Perm.sign (shuffle T) *
        Equiv.Perm.sign (shuffle S) := by
  simp [twoLine]

/-! ## 3. The induction target — the only unfinished result -/

/-!
This is the mathematical induction from the paper.

For `T = ∅`, `shuffle T` is the identity.
For nonempty `T`, let `t` be its least element and apply induction to
`T.erase t`. To get the new shuffle, move `t` to the beginning through
`t.val + T.card - 1` adjacent swaps.

Each adjacent swap changes the permutation sign by `-1`.
Combining this with `indexSum_erase` and `triangular_succ` yields the
exponent on the right. This is the one lemma still to formalize.
-/
theorem shuffle_sign_induction {n : ℕ} (T : Finset (Fin n)) :
    Equiv.Perm.sign (shuffle T) =
      (-1 : ℤˣ) ^ (indexSum T + triangular T.card) := by
  sorry

/-! ## 4. Pure parity cancellation (no induction needed) -/

/-- The two copies of the triangular exponent cancel in parity. -/
lemma two_shuffle_parity (a b c : ℕ) :
    (-1 : ℤˣ) ^ (a + c) * (-1 : ℤˣ) ^ (b + c) =
      (-1 : ℤˣ) ^ (a + b) := by
  rw [← pow_add]
  have h : (a + c) + (b + c) = (a + b) + 2 * c := by
    omega
  rw [h, pow_add]
  have htwo : (-1 : ℤˣ) ^ (2 * c) = 1 := by
    rw [pow_mul]
    norm_num
  rw [htwo, mul_one]

/-! ## 5. The final lemma, deduced from the shuffle induction -/

/-- Lemma 3.2 for the two-line permutation of equally sized subsets. -/
theorem lemma_3_2 {n : ℕ}
    (S T : Finset (Fin n)) (hcard : S.card = T.card) :
    Equiv.Perm.sign (twoLine S T) =
      (-1 : ℤˣ) ^ (indexSum S + indexSum T) := by
  rw [sign_twoLine S T]
  rw [shuffle_sign_induction T, shuffle_sign_induction S]
  rw [hcard]
  calc
    (-1 : ℤˣ) ^ (indexSum T + triangular T.card) *
        (-1 : ℤˣ) ^ (indexSum S + triangular T.card) =
        (-1 : ℤˣ) ^ (indexSum T + indexSum S) :=
      two_shuffle_parity (indexSum T) (indexSum S) (triangular T.card)
    _ = (-1 : ℤˣ) ^ (indexSum S + indexSum T) := by
      rw [add_comm (indexSum T) (indexSum S)]

end

end Lemma32
