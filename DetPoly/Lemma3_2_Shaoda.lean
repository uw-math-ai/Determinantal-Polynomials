import Mathlib

/-!
# Lemma 3.2 — increasing-order shuffle permutations

This file formalizes the definitions and the reduction of Lemma 3.2
from two arbitrary subsets to the sign of a single shuffle.

Version v22 completes the shuffle-sign formula by exact inversion counting.
The triangular-number identity is proved by induction. No `sorry` or
additional axioms are used in the proof.
Mathlib's `Equiv.Perm.finPairsLT` uses dependent Sigma pairs, not
ordinary product pairs. Here we use a matching product-type set of
reverse-order pairs, leaving the conversion to Sigma pairs for later.

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

/-!
## 3. Arithmetic identity needed for the induction step

When `t ∈ T`, the exponent for `T` differs by exactly two
from the exponent obtained by deleting `t` and counting the
`t.val + T.card - 1` adjacent transpositions.
-/
lemma induction_exponent_step {n : ℕ}
    (T : Finset (Fin n)) (t : Fin n) (ht : t ∈ T) :
    (-1 : ℤˣ) ^ (indexSum T + triangular T.card) =
      (-1 : ℤˣ) ^ (t.val + T.card - 1) *
        (-1 : ℤˣ) ^
          (indexSum (T.erase t) + triangular (T.erase t).card) := by
  have hc := card_erase_step T t ht
  have hs := indexSum_erase T t ht
  have htri : triangular T.card =
      triangular (T.erase t).card + T.card := by
    calc
      triangular T.card = triangular ((T.erase t).card + 1) := by rw [hc]
      _ = triangular (T.erase t).card + ((T.erase t).card + 1) :=
        triangular_succ _
      _ = triangular (T.erase t).card + T.card := by rw [hc]
  have hexp :
      indexSum T + triangular T.card =
        ((t.val + T.card - 1) +
          (indexSum (T.erase t) + triangular (T.erase t).card)) + 2 := by
    omega
  rw [hexp, pow_add, pow_add]
  norm_num

/-!
## 4. Inversion formula for the concrete shuffle

Mathlib gives a fraction-free formula for the sign of *any* permutation
of `Fin n`: multiply `-1` for each inverted pair `i < j` and `1` for
each pair in the correct order. This theorem applies it to our concrete
`shuffle T`; no new hypothesis, axiom, or `sorry` is introduced.

The next combinatorial goal is to show that, because both halves of the
shuffle are increasing, the inverted pairs are precisely the pairs
`(t,c)` with `t ∈ T`, `c ∉ T`, and `c < t`.
-/

/-- The cross-block inverted pairs, written using the *values* in `T` and `Tᶜ`. -/
def crossingInversions {n : ℕ} (T : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (T.product Tᶜ).filter (fun p => p.2 < p.1)

/-- Membership in the cross-block inversion set is exactly the three expected conditions. -/
lemma mem_crossingInversions {n : ℕ} (T : Finset (Fin n))
    (t c : Fin n) :
    (t, c) ∈ crossingInversions T ↔
      t ∈ T ∧ c ∉ T ∧ c < t := by
  simp [crossingInversions, and_assoc]

/-- The concrete sign of `shuffle T` as the product over its inversions. -/
lemma shuffle_sign_inversion_product {n : ℕ} (T : Finset (Fin n)) :
    Equiv.Perm.sign (shuffle T) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (if shuffle T i < shuffle T j then (1 : ℤˣ) else -1) := by
  exact Equiv.Perm.sign_eq_prod_prod_Ioi (shuffle T)

/-!
Once we identify the inversion pairs with `crossingInversions T`,
we can convert this product into

    sign (shuffle T) = (-1) ^ (crossingInversions T).card.

Then induction on `T.card` reduces to counting how these pairs change
when an element is removed. This avoids needing to construct the
adjacent-swap permutation explicitly.
-/

/-!
## 5. Preparation for counting inversions

`Equiv.Perm.finPairsLT n` uses the dependent pair type
`Σ _ : Fin n, Fin n`, whereas `crossingInversions T` uses the
ordinary product `Fin n × Fin n`. They cannot be compared directly.

For this step we define reverse-order pairs using the *same product
representation* as `crossingInversions`. The conversion to the Sigma
pairs from Mathlib's sign theorem is a separate later task.

The strict internal-pair count is the other combinatorial ingredient:
inside a `k`-element subset there are exactly `k.choose 2`
ordered pairs `(a,b)` with `a < b`.
-/

/-- All reversed pairs, represented as ordinary product pairs. -/
def reverseOrderPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  ((Finset.univ : Finset (Fin n)).product Finset.univ).filter
    (fun p => p.2 < p.1)

/-- Every crossing inversion is a reverse-order product pair. -/
lemma crossingInversions_subset_reverseOrderPairs {n : ℕ}
    (T : Finset (Fin n)) :
    crossingInversions T ⊆ reverseOrderPairs n := by
  intro p hp
  have hlt : p.2 < p.1 := (Finset.mem_filter.mp hp).2
  simp [reverseOrderPairs, hlt]

/-- Crossing inversions are exactly the appropriate filtered reverse pairs. -/
lemma crossingInversions_eq_filter_reverseOrderPairs {n : ℕ}
    (T : Finset (Fin n)) :
    crossingInversions T =
      (reverseOrderPairs n).filter
        (fun p => p.1 ∈ T ∧ p.2 ∉ T) := by
  ext p
  simp [crossingInversions, reverseOrderPairs, and_comm]

/-- A universal-set description, convenient for filtering products in the sign formula. -/
lemma crossingInversions_eq_filter_univ {n : ℕ}
    (T : Finset (Fin n)) :
    crossingInversions T =
      (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => p.1 ∈ T ∧ p.2 ∉ T ∧ p.2 < p.1) := by
  ext p
  simp [crossingInversions, and_assoc]

/-- There are no crossing inversions when the first block is empty. -/
lemma crossingInversions_empty (n : ℕ) :
    crossingInversions (∅ : Finset (Fin n)) = ∅ := by
  simp [crossingInversions]

/-- There are no crossing inversions when the first block is the whole space. -/
lemma crossingInversions_univ (n : ℕ) :
    crossingInversions (Finset.univ : Finset (Fin n)) = ∅ := by
  simp [crossingInversions]

/-- Among k distinct elements, precisely k.choose 2 pairs are strictly ascending. -/
lemma internalStrictPairs_card {n : ℕ} (T : Finset (Fin n)) :
    ((T.product T).filter (fun p => p.1 < p.2)).card =
      T.card.choose 2 := by
  exact Finset.card_product_filter_lt (s := T)

/-!
## 5A. The two branches of the concrete shuffle

These indices are the positions in `Fin n` corresponding to an index
in the first or second part of the concatenated increasing enumeration.

The proofs are deliberately separate from the inversion-counting step:
we first establish what the actual permutation does on each block.
-/

/-- Position in `Fin n` belonging to the first (selected) block. -/
noncomputable def firstBlockIndex {n : ℕ}
    (T : Finset (Fin n)) (i : Fin T.card) : Fin n :=
  (Fin.castOrderIso (show n = T.card + Tᶜ.card by simp)).symm
    ((finSumFinEquiv (m := T.card) (n := Tᶜ.card)) (Sum.inl i))

/-- Position in `Fin n` belonging to the second (complement) block. -/
noncomputable def secondBlockIndex {n : ℕ}
    (T : Finset (Fin n)) (i : Fin Tᶜ.card) : Fin n :=
  (Fin.castOrderIso (show n = T.card + Tᶜ.card by simp)).symm
    ((finSumFinEquiv (m := T.card) (n := Tᶜ.card)) (Sum.inr i))

/-- On the first block, `shuffle T` gives the increasing enumeration of `T`. -/
lemma shuffle_firstBlockIndex {n : ℕ}
    (T : Finset (Fin n)) (i : Fin T.card) :
    shuffle T (firstBlockIndex T i) = (T.orderEmbOfFin rfl) i := by
  classical
  change
    (finSumEquivOfFinset (s := T) rfl rfl)
      ((finSumFinEquiv (m := T.card) (n := Tᶜ.card)).symm
        ((Fin.castOrderIso (show n = T.card + Tᶜ.card by simp))
          ((Fin.castOrderIso (show n = T.card + Tᶜ.card by simp)).symm
            ((finSumFinEquiv (m := T.card) (n := Tᶜ.card)) (Sum.inl i))))) =
      (T.orderEmbOfFin rfl) i
  simp

/-- On the second block, `shuffle T` gives the increasing enumeration of `Tᶜ`. -/
lemma shuffle_secondBlockIndex {n : ℕ}
    (T : Finset (Fin n)) (i : Fin Tᶜ.card) :
    shuffle T (secondBlockIndex T i) = (Tᶜ.orderEmbOfFin rfl) i := by
  classical
  change
    (finSumEquivOfFinset (s := T) rfl rfl)
      ((finSumFinEquiv (m := T.card) (n := Tᶜ.card)).symm
        ((Fin.castOrderIso (show n = T.card + Tᶜ.card by simp))
          ((Fin.castOrderIso (show n = T.card + Tᶜ.card by simp)).symm
            ((finSumFinEquiv (m := T.card) (n := Tᶜ.card)) (Sum.inr i))))) =
      (Tᶜ.orderEmbOfFin rfl) i
  simp

/-!
## 5B. Order and membership facts for the two blocks

These facts follow from the two previously proved block-action lemmas.
They show that there are no inversions *within* either block, and that
all positions from the first block precede those from the second block.
The remaining inversion-identification argument concerns only pairs
with one index in each block.
-/

/-- Every output from the first block is in `T`. -/
lemma shuffle_firstBlock_mem {n : ℕ}
    (T : Finset (Fin n)) (i : Fin T.card) :
    shuffle T (firstBlockIndex T i) ∈ T := by
  rw [shuffle_firstBlockIndex]
  exact Finset.orderEmbOfFin_mem T rfl i

/-- Every output from the second block is outside `T`. -/
lemma shuffle_secondBlock_not_mem {n : ℕ}
    (T : Finset (Fin n)) (i : Fin Tᶜ.card) :
    shuffle T (secondBlockIndex T i) ∉ T := by
  rw [shuffle_secondBlockIndex]
  have hm : ((Tᶜ).orderEmbOfFin rfl) i ∈ Tᶜ :=
    Finset.orderEmbOfFin_mem Tᶜ rfl i
  exact Finset.mem_compl.mp hm

/-- The positions of the first block retain their zero-based indices. -/
lemma firstBlockIndex_val {n : ℕ}
    (T : Finset (Fin n)) (i : Fin T.card) :
    (firstBlockIndex T i).val = i.val := by
  simp [firstBlockIndex]

/-- Positions in the second block are shifted by `T.card`. -/
lemma secondBlockIndex_val {n : ℕ}
    (T : Finset (Fin n)) (i : Fin Tᶜ.card) :
    (secondBlockIndex T i).val = T.card + i.val := by
  simp [secondBlockIndex]

/-- Every first-block position precedes every second-block position. -/
lemma firstBlockIndex_lt_secondBlockIndex {n : ℕ}
    (T : Finset (Fin n)) (i : Fin T.card) (j : Fin Tᶜ.card) :
    firstBlockIndex T i < secondBlockIndex T j := by
  change (firstBlockIndex T i).val < (secondBlockIndex T j).val
  rw [firstBlockIndex_val, secondBlockIndex_val]
  omega

/-- The shuffle is strictly increasing on its first block. -/
lemma shuffle_firstBlock_strictMono {n : ℕ}
    (T : Finset (Fin n)) :
    StrictMono (fun i : Fin T.card => shuffle T (firstBlockIndex T i)) := by
  intro i j hij
  simpa only [shuffle_firstBlockIndex] using
    (T.orderEmbOfFin rfl).strictMono hij

/-- The shuffle is strictly increasing on its second block. -/
lemma shuffle_secondBlock_strictMono {n : ℕ}
    (T : Finset (Fin n)) :
    StrictMono (fun i : Fin Tᶜ.card => shuffle T (secondBlockIndex T i)) := by
  intro i j hij
  simpa only [shuffle_secondBlockIndex] using
    ((Tᶜ).orderEmbOfFin rfl).strictMono hij

/-!
## 5C. All inversions cross from the first block to the second

The first important combinatorial step is to classify every position
in `Fin n` as belonging to one of the two blocks. We then show that,
for `p < q`, a strict inversion `shuffle T q < shuffle T p` can occur
only when `p` is in the first block and `q` in the second block.

This is an equivalence about the actual permutation, not an assumption
about its sign. The numerical inversion count will be handled next.
-/

/-- The position embedding of the first block preserves strict order. -/
lemma firstBlockIndex_lt_iff {n : ℕ}
    (T : Finset (Fin n)) (i j : Fin T.card) :
    firstBlockIndex T i < firstBlockIndex T j ↔ i < j := by
  change (firstBlockIndex T i).val < (firstBlockIndex T j).val ↔
    i.val < j.val
  simp only [firstBlockIndex_val]

/-- The position embedding of the second block preserves strict order. -/
lemma secondBlockIndex_lt_iff {n : ℕ}
    (T : Finset (Fin n)) (i j : Fin Tᶜ.card) :
    secondBlockIndex T i < secondBlockIndex T j ↔ i < j := by
  change (secondBlockIndex T i).val < (secondBlockIndex T j).val ↔
    i.val < j.val
  simp only [secondBlockIndex_val]
  omega

/-- Every position of the shuffled list belongs to exactly one of its blocks. -/
lemma index_from_either_block {n : ℕ}
    (T : Finset (Fin n)) (p : Fin n) :
    (∃ i : Fin T.card, p = firstBlockIndex T i) ∨
      (∃ j : Fin Tᶜ.card, p = secondBlockIndex T j) := by
  classical
  by_cases hp : p.val < T.card
  · left
    let i : Fin T.card := ⟨p.val, hp⟩
    refine ⟨i, ?_⟩
    apply Fin.ext
    rw [firstBlockIndex_val]
  · right
    have hsize : n = T.card + Tᶜ.card := by simp
    have hj : p.val - T.card < Tᶜ.card := by
      have hbound : p.val < n := p.isLt
      omega
    let j : Fin Tᶜ.card := ⟨p.val - T.card, hj⟩
    refine ⟨j, ?_⟩
    apply Fin.ext
    rw [secondBlockIndex_val]
    change p.val = T.card + (p.val - T.card)
    omega

/-- For ordered positions, a strict inversion has one value in each block. -/
lemma shuffle_inversion_iff_cross {n : ℕ}
    (T : Finset (Fin n)) (p q : Fin n) (hpq : p < q) :
    shuffle T q < shuffle T p ↔
      shuffle T p ∈ T ∧
      shuffle T q ∉ T ∧
      shuffle T q < shuffle T p := by
  constructor
  · intro hinv
    rcases index_from_either_block T p with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rcases index_from_either_block T q with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have hmono : shuffle T (firstBlockIndex T i) <
            shuffle T (firstBlockIndex T j) :=
          (shuffle_firstBlock_strictMono T)
            ((firstBlockIndex_lt_iff T i j).mp hpq)
        exact False.elim (lt_asymm hinv hmono)
      · exact ⟨shuffle_firstBlock_mem T i,
          shuffle_secondBlock_not_mem T j, hinv⟩
    · rcases index_from_either_block T q with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact False.elim (lt_asymm hpq
          (firstBlockIndex_lt_secondBlockIndex T j i))
      · have hmono : shuffle T (secondBlockIndex T i) <
            shuffle T (secondBlockIndex T j) :=
          (shuffle_secondBlock_strictMono T)
            ((secondBlockIndex_lt_iff T i j).mp hpq)
        exact False.elim (lt_asymm hinv hmono)
  · intro h
    exact h.2.2

/-- Ordered input positions form an inversion precisely when their
    output pair belongs to the finite set of crossing inversions. -/
lemma shuffle_inversion_iff_mem_crossing {n : ℕ}
    (T : Finset (Fin n)) (p q : Fin n) (hpq : p < q) :
    shuffle T q < shuffle T p ↔
      (shuffle T p, shuffle T q) ∈ crossingInversions T := by
  exact (shuffle_inversion_iff_cross T p q hpq).trans
    (mem_crossingInversions T (shuffle T p) (shuffle T q)).symm

/-!
## 5D. From crossing values back to inversion positions

The previous result started with two *input positions* `p < q` and
characterized when their output values form a crossing inversion.

We also need the converse viewpoint: given two *output values* `(a,b)`
with `a ∈ T`, `b ∉ T`, and `b < a`, their inverse images are in the
first and second input blocks respectively. This identifies precisely
which value pairs contribute factors of `-1` to the sign product.
-/

/-- An output lies in `T` exactly when its input position lies in the first block. -/
lemma shuffle_mem_iff_position_first {n : ℕ}
    (T : Finset (Fin n)) (p : Fin n) :
    shuffle T p ∈ T ↔ p.val < T.card := by
  rcases index_from_either_block T p with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · constructor
    · intro _
      rw [firstBlockIndex_val]
      exact i.isLt
    · intro _
      exact shuffle_firstBlock_mem T i
  · constructor
    · intro hmem
      exact False.elim ((shuffle_secondBlock_not_mem T j) hmem)
    · intro hp
      rw [secondBlockIndex_val] at hp
      omega

/-- Every element of `T` has an inverse position before every element of `Tᶜ`. -/
lemma shuffle_inverse_first_before_second {n : ℕ}
    (T : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ T) (hb : b ∉ T) :
    (shuffle T).symm a < (shuffle T).symm b := by
  have ha' : shuffle T ((shuffle T).symm a) ∈ T := by
    simpa using ha
  have hb' : shuffle T ((shuffle T).symm b) ∉ T := by
    simpa using hb
  have hpa : ((shuffle T).symm a).val < T.card :=
    (shuffle_mem_iff_position_first T _).mp ha'
  have hpb : ¬ (((shuffle T).symm b).val < T.card) := by
    intro hp
    exact hb' ((shuffle_mem_iff_position_first T _).mpr hp)
  change ((shuffle T).symm a).val < ((shuffle T).symm b).val
  omega

/-- A value pair is a crossing inversion iff its two inverse positions
    are ordered and the values themselves are in reverse order. -/
lemma mem_crossing_iff_inverse_position_inversion {n : ℕ}
    (T : Finset (Fin n)) (a b : Fin n) :
    (a, b) ∈ crossingInversions T ↔
      (shuffle T).symm a < (shuffle T).symm b ∧ b < a := by
  constructor
  · intro h
    rcases (mem_crossingInversions T a b).mp h with ⟨ha, hb, hlt⟩
    exact ⟨shuffle_inverse_first_before_second T a b ha hb, hlt⟩
  · rintro ⟨hpq, hba⟩
    have hinv : shuffle T ((shuffle T).symm b) <
        shuffle T ((shuffle T).symm a) := by
      simpa using hba
    have hmem :=
      (shuffle_inversion_iff_mem_crossing T
        ((shuffle T).symm a) ((shuffle T).symm b) hpq).mp hinv
    simpa using hmem

/-- Output-value pairs whose *inverse* positions form an inversion. -/
def inversePositionValuePairs {n : ℕ} (T : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => (shuffle T).symm p.1 < (shuffle T).symm p.2 ∧ p.2 < p.1)

/-- Exact equality of the value-pair inversion descriptions. -/
lemma crossingInversions_eq_inversePositionValuePairs {n : ℕ}
    (T : Finset (Fin n)) :
    crossingInversions T = inversePositionValuePairs T := by
  ext p
  rcases p with ⟨a, b⟩
  simpa [inversePositionValuePairs] using
    (mem_crossing_iff_inverse_position_inversion T a b)

/-!
## 5E. A bijection between input inversions and output crossing pairs

A pair of positions `(p,q)` with `p < q` is an inversion of the
permutation precisely when `shuffle T q < shuffle T p`.

The map `(p,q) ↦ (shuffle T p, shuffle T q)` takes this set onto the
previously defined `crossingInversions T`. Injectivity follows from
injectivity of the underlying permutation. Thus the cardinalities agree.

This eliminates the last *set-theoretic* part of the inversion argument;
the remaining work is to convert the sign product to a power of `-1`
and prove the arithmetic formula for the crossing-pair count.
-/

/-- Inversions indexed by their two *input positions*. -/
def inputInversions {n : ℕ} (T : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ shuffle T p.2 < shuffle T p.1)

/-- Applying the shuffle to both coordinates of a position pair. -/
def shufflePair {n : ℕ} (T : Finset (Fin n))
    (p : Fin n × Fin n) : Fin n × Fin n :=
  (shuffle T p.1, shuffle T p.2)

/-- The shuffle acts injectively on pairs, since it is a permutation. -/
lemma shufflePair_injective {n : ℕ} (T : Finset (Fin n)) :
    Function.Injective (shufflePair T) := by
  intro a b h
  change (shuffle T a.1, shuffle T a.2) =
    (shuffle T b.1, shuffle T b.2) at h
  apply Prod.ext
  · exact (shuffle T).injective (congrArg Prod.fst h)
  · exact (shuffle T).injective (congrArg Prod.snd h)

/-- The image of the input-position inversion set is precisely the
    output-value crossing-inversion set. -/
lemma inputInversions_image {n : ℕ} (T : Finset (Fin n)) :
    (inputInversions T).image (shufflePair T) = crossingInversions T := by
  classical
  ext ⟨a, b⟩
  constructor
  · intro h
    obtain ⟨⟨p, q⟩, hmem, heq⟩ := Finset.mem_image.mp h
    have hpq : p < q := by
      exact (Finset.mem_filter.mp hmem).2.1
    have hqp : shuffle T q < shuffle T p := by
      exact (Finset.mem_filter.mp hmem).2.2
    have hcross : (shuffle T p, shuffle T q) ∈ crossingInversions T :=
      (shuffle_inversion_iff_mem_crossing T p q hpq).mp hqp
    change (shuffle T p, shuffle T q) = (a, b) at heq
    rwa [heq] at hcross
  · intro hcross
    obtain ⟨hpq, hba⟩ :=
      (mem_crossing_iff_inverse_position_inversion T a b).mp hcross
    apply Finset.mem_image.mpr
    refine ⟨((shuffle T).symm a, (shuffle T).symm b), ?_, ?_⟩
    · change ((shuffle T).symm a, (shuffle T).symm b) ∈
        (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun p => p.1 < p.2 ∧ shuffle T p.2 < shuffle T p.1)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hpq, by simpa using hba⟩
    · simp [shufflePair]

/-- Counting input inversions equals counting crossing output pairs. -/
lemma inputInversions_card_eq_crossing {n : ℕ} (T : Finset (Fin n)) :
    (inputInversions T).card = (crossingInversions T).card := by
  calc
    (inputInversions T).card =
        ((inputInversions T).image (shufflePair T)).card := by
          symm
          exact Finset.card_image_of_injective
            (inputInversions T) (shufflePair_injective T)
    _ = (crossingInversions T).card := by
          rw [inputInversions_image]

/-!
## 5F. Convert the sign product into a power of `-1`

Mathlib's sign formula was established in Section 4. We now turn its
factor for a pair of increasing input positions into `-1` exactly when
those two positions form an inversion. We then combine all factors into
one power, with exponent equal to the sum of the inversion indicators.

There is **no hypothesis about the sign** in this new lemma.
-/

/-- A product of powers of one fixed unit is the unit to the sum of
    the exponents. We prove this directly by induction on the finset. -/
private lemma product_powers_eq_power_sum {α : Type*}
    (s : Finset α) (a : ℤˣ) (f : α → ℕ) :
    (∏ x ∈ s, a ^ f x) = a ^ (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert x t hxt ih =>
      simp [hxt, ih, pow_add]

/-- A factor of the sign product is `-1` precisely when this pair is
    inverted. The assumption `i < j` excludes equal permutation values. -/
private lemma shuffle_sign_factor {n : ℕ}
    (T : Finset (Fin n)) (i j : Fin n) (hij : i < j) :
    (if shuffle T i < shuffle T j then (1 : ℤˣ) else -1) =
      (-1 : ℤˣ) ^
        (if shuffle T j < shuffle T i then (1 : ℕ) else 0) := by
  rcases lt_trichotomy (shuffle T i) (shuffle T j) with hlt | heq | hgt
  · have hn : ¬ shuffle T j < shuffle T i :=
      not_lt_of_ge (le_of_lt hlt)
    simp [hlt, hn]
  · exact False.elim ((ne_of_lt hij) ((shuffle T).injective heq))
  · have hn : ¬ shuffle T i < shuffle T j :=
      not_lt_of_ge (le_of_lt hgt)
    simp [hgt, hn]

/-- The sign of the actual shuffle is `-1` raised to its number of
    inversions, written as a double sum over `i < j`.

    This is derived from Mathlib's sign formula, not postulated. -/
lemma shuffle_sign_eq_pow_inversion_sum {n : ℕ}
    (T : Finset (Fin n)) :
    Equiv.Perm.sign (shuffle T) =
      (-1 : ℤˣ) ^
        (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
          if shuffle T j < shuffle T i then (1 : ℕ) else 0) := by
  calc
    Equiv.Perm.sign (shuffle T) =
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          (if shuffle T i < shuffle T j then (1 : ℤˣ) else -1) :=
      shuffle_sign_inversion_product T
    _ = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
          (-1 : ℤˣ) ^
            (if shuffle T j < shuffle T i then (1 : ℕ) else 0) := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j hj
      exact shuffle_sign_factor T i j (Finset.mem_Ioi.mp hj)
    _ = ∏ i : Fin n,
          (-1 : ℤˣ) ^
            (∑ j ∈ Finset.Ioi i,
              if shuffle T j < shuffle T i then (1 : ℕ) else 0) := by
      apply Finset.prod_congr rfl
      intro i _
      exact product_powers_eq_power_sum (Finset.Ioi i) (-1 : ℤˣ)
        (fun j => if shuffle T j < shuffle T i then (1 : ℕ) else 0)
    _ = (-1 : ℤˣ) ^
          (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
            if shuffle T j < shuffle T i then (1 : ℕ) else 0) := by
      exact product_powers_eq_power_sum Finset.univ (-1 : ℤˣ)
        (fun i => ∑ j ∈ Finset.Ioi i,
          if shuffle T j < shuffle T i then (1 : ℕ) else 0)

/-!
Section 5G below converts the double sum to the actual inversion
count. The remaining mathematical problem is then entirely a counting
identity for `crossingInversions T`, preferably by induction on `T.card`.
-/

/-!
## 5G. The double inversion sum really counts inversion pairs

Each inner sum ranges over the positions `j > i` and contributes
one precisely when the ordered pair `(i,j)` is an inversion.
Expanding the sums over the product of two universal finsets
therefore gives the cardinality of `inputInversions T`.

By Section 5E, that cardinality equals the number of crossing
inversions in the two ordered output blocks. These proofs use no
new hypotheses and no `sorry`.
-/

/-- The double sum of inversion indicators is the cardinality of
    the explicitly defined input inversion finset. -/
lemma inversion_sum_eq_inputInversions_card {n : ℕ}
    (T : Finset (Fin n)) :
    (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
      if shuffle T j < shuffle T i then (1 : ℕ) else 0) =
      (inputInversions T).card := by
  classical
  have hIoi (i : Fin n) :
      Finset.Ioi i =
        (Finset.univ : Finset (Fin n)).filter (fun j => i < j) := by
    ext j
    simp
  have hinner (i : Fin n) :
      (Finset.Ioi i).sum
          (fun j => if shuffle T j < shuffle T i then (1 : ℕ) else 0) =
        (Finset.univ : Finset (Fin n)).sum
          (fun j => if i < j ∧ shuffle T j < shuffle T i then
            (1 : ℕ) else 0) := by
    rw [hIoi i, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j <;> simp [hij]
  have huniv :
      (Finset.univ : Finset (Fin n × Fin n)) =
        (Finset.univ : Finset (Fin n)).product Finset.univ := by
    ext p
    simp
  calc
    (∑ i : Fin n, ∑ j ∈ Finset.Ioi i,
      if shuffle T j < shuffle T i then (1 : ℕ) else 0) =
        ∑ i : Fin n, ∑ j : Fin n,
          if i < j ∧ shuffle T j < shuffle T i then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact hinner i
    _ = (Finset.univ : Finset (Fin n × Fin n)).sum
          (fun p => if p.1 < p.2 ∧ shuffle T p.2 < shuffle T p.1 then
            (1 : ℕ) else 0) := by
      rw [huniv]
      exact (Finset.sum_product
        (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin n))
        (fun p : Fin n × Fin n =>
          if p.1 < p.2 ∧ shuffle T p.2 < shuffle T p.1 then
            (1 : ℕ) else 0)).symm
    _ = (inputInversions T).card := by
      simp [inputInversions]

/-- The sign is `(-1)` to the exact number of crossing inversions.
    This joins the Mathlib sign product to the proven inversion bijection. -/
lemma shuffle_sign_eq_pow_crossingInversions_card {n : ℕ}
    (T : Finset (Fin n)) :
    Equiv.Perm.sign (shuffle T) =
      (-1 : ℤˣ) ^ (crossingInversions T).card := by
  rw [shuffle_sign_eq_pow_inversion_sum,
    inversion_sum_eq_inputInversions_card,
    inputInversions_card_eq_crossing]

/-!
## 5H. Count crossing inversions one selected element at a time

For each `t ∈ T`, the crossing inversions beginning with `t` are exactly
those `c ∈ Tᶜ` satisfying `c < t`. The total crossing count is the sum
of these fiber cardinalities. No additional hypothesis is needed.
-/

/-- The crossing-inversion count is the sum of the counts of omitted
    indices below each selected index. -/
lemma crossingInversions_card_eq_sum_before {n : ℕ}
    (T : Finset (Fin n)) :
    (crossingInversions T).card =
      ∑ t ∈ T, ((Tᶜ).filter (fun c => c < t)).card := by
  classical
  calc
    (crossingInversions T).card =
        ((T.product Tᶜ).filter (fun p => p.2 < p.1)).sum
          (fun _ => (1 : ℕ)) := by
      simp [crossingInversions]
    _ = (T.product Tᶜ).sum
          (fun p => if p.2 < p.1 then (1 : ℕ) else 0) := by
      exact Finset.sum_filter (s := T.product Tᶜ)
        (fun p => p.2 < p.1) (fun _ => (1 : ℕ))
    _ = ∑ t ∈ T, ∑ c ∈ Tᶜ,
          if c < t then (1 : ℕ) else 0 := by
      exact Finset.sum_product T Tᶜ
        (fun p : Fin n × Fin n =>
          if p.2 < p.1 then (1 : ℕ) else 0)
    _ = ∑ t ∈ T, ((Tᶜ).filter (fun c => c < t)).card := by
      apply Finset.sum_congr rfl
      intro t _
      calc
        (∑ c ∈ Tᶜ, if c < t then (1 : ℕ) else 0) =
            ∑ c ∈ (Tᶜ).filter (fun c => c < t), (1 : ℕ) := by
          exact (Finset.sum_filter (s := Tᶜ)
            (fun c => c < t) (fun _ => (1 : ℕ))).symm
        _ = ((Tᶜ).filter (fun c => c < t)).card := by
          simp

/-- The empty shuffle has positive sign, deduced from the actual
    inversion-count formula rather than an assumed permutation identity. -/
lemma shuffle_sign_empty (n : ℕ) :
    Equiv.Perm.sign (shuffle (∅ : Finset (Fin n))) = 1 := by
  rw [shuffle_sign_eq_pow_crossingInversions_card]
  simp [crossingInversions_empty]

/-!
## 5I. Counting all positions below a selected position

For `t : Fin n`, there are exactly `t.val` elements strictly below `t`.
These are partitioned into those in `T` and those in its complement.
This is the elementary counting identity needed to convert the
crossing-inversion count into a sum of indices.
-/

/-- There are exactly `t.val` indices `c : Fin n` with `c < t`.
    Use mathlib's finite-index counting theorem directly, instead of
    constructing a bijection and simplifying `Fin.lt_def`. -/
lemma card_all_below {n : ℕ} (t : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun c => c < t)).card =
      t.val := by
  classical
  change ((Finset.univ : Finset (Fin n)).filter
      (fun c : Fin n => (c : ℕ) < t.val)).card = t.val
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt t.isLt)

/-- Among the `t.val` smaller indices, every one is either in `T`
    or outside `T`, and the two groups are disjoint. -/
lemma card_below_partition {n : ℕ}
    (T : Finset (Fin n)) (t : Fin n) :
    ((Tᶜ).filter (fun c => c < t)).card +
      (T.filter (fun c => c < t)).card = t.val := by
  classical
  let U : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun c => c < t)
  let B : Finset (Fin n) := T.filter (fun c => c < t)
  have hsub : B ⊆ U := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hc).2⟩
  have hdiff : U \ B = (Tᶜ).filter (fun c => c < t) := by
    ext c
    simp only [U, B, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_compl]
    tauto
  calc
    ((Tᶜ).filter (fun c => c < t)).card +
        (T.filter (fun c => c < t)).card =
        (U \ B).card + B.card := by rw [hdiff]
    _ = U.card := Finset.card_sdiff_add_card_eq_card hsub
    _ = t.val := card_all_below t

/-!
## 5J. Count the internal ordered pairs

We have already counted crossing inversions by summing, for each
`t ∈ T`, the number of omitted elements smaller than `t`.
The analogous sum over *selected* smaller elements counts the pairs
`(c,t)` in `T × T` with `c < t`. There are exactly `T.card.choose 2`
of these pairs. This is the finite-set combinatorics behind the
induction on the size of `T`.
-/

/-- The sum over `t ∈ T` of the number of preceding members of `T`
    is the number of unordered two-element subsets of `T`. -/
lemma internal_below_sum_eq_choose {n : ℕ} (T : Finset (Fin n)) :
    (∑ t ∈ T, (T.filter (fun c => c < t)).card) = T.card.choose 2 := by
  classical
  calc
    (∑ t ∈ T, (T.filter (fun c => c < t)).card) =
        ∑ t ∈ T, ∑ c ∈ T, if c < t then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      calc
        (T.filter (fun c => c < t)).card =
            ∑ c ∈ (T.filter (fun c => c < t)), (1 : ℕ) := by
          simp
        _ = ∑ c ∈ T, if c < t then (1 : ℕ) else 0 := by
          exact Finset.sum_filter (s := T)
            (fun c => c < t) (fun _ => (1 : ℕ))
    _ = ∑ c ∈ T, ∑ t ∈ T, if c < t then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
    _ = ((T.product T).filter (fun p => p.1 < p.2)).card := by
      calc
        (∑ c ∈ T, ∑ t ∈ T, if c < t then (1 : ℕ) else 0) =
            (T.product T).sum
              (fun p => if p.1 < p.2 then (1 : ℕ) else 0) := by
          exact (Finset.sum_product T T
            (fun p : Fin n × Fin n =>
              if p.1 < p.2 then (1 : ℕ) else 0)).symm
        _ = ((T.product T).filter (fun p => p.1 < p.2)).sum
              (fun _ => (1 : ℕ)) := by
          exact (Finset.sum_filter (s := T.product T)
            (fun p => p.1 < p.2) (fun _ => (1 : ℕ))).symm
        _ = ((T.product T).filter (fun p => p.1 < p.2)).card := by
          simp
    _ = T.card.choose 2 := internalStrictPairs_card T

/-- Combining the two complementary types of elements below `t`
    gives a precise equality between the crossing-inversion count,
    internal pairs, and zero-based indices of selected elements. -/
lemma crossing_count_add_choose {n : ℕ} (T : Finset (Fin n)) :
    (crossingInversions T).card + T.card.choose 2 =
      ∑ t ∈ T, t.val := by
  calc
    (crossingInversions T).card + T.card.choose 2 =
        (∑ t ∈ T, ((Tᶜ).filter (fun c => c < t)).card) +
          (∑ t ∈ T, (T.filter (fun c => c < t)).card) := by
      rw [crossingInversions_card_eq_sum_before, internal_below_sum_eq_choose]
    _ = ∑ t ∈ T,
          (((Tᶜ).filter (fun c => c < t)).card +
            (T.filter (fun c => c < t)).card) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ t ∈ T, t.val := by
      apply Finset.sum_congr rfl
      intro t _
      exact card_below_partition T t

/-!
## 5K. Convert counting into the desired parity exponent

The sum `1 + ... + k` equals `k + choose(k,2)`.
Together with `crossing_count_add_choose`, this yields the
*exact*, not merely mod-two, identity

  crossing_count(T) + triangular(T.card) = indexSum(T).

The desired sign formula follows since adding twice an integer
does not alter a power of `-1`.
-/

/-- The triangular-number identity, established by induction on `k`. -/
lemma triangular_eq_add_choose (k : ℕ) :
    triangular k = k + k.choose 2 := by
  induction k with
  | zero =>
      simp [triangular]
  | succ k ih =>
      have hc : (k + 1).choose 2 = k + k.choose 2 := by
        simpa using (Nat.choose_succ_left k 2 (by norm_num))
      rw [triangular_succ, ih, hc]
      omega

/-- The one-based index sum is the zero-based index sum plus the size. -/
lemma indexSum_eq_sum_val_add_card {n : ℕ} (T : Finset (Fin n)) :
    indexSum T = (∑ t ∈ T, t.val) + T.card := by
  simp [indexSum, Finset.sum_add_distrib]

/-- The exact crossing-inversion count needed for the shuffle sign. -/
lemma crossing_count_add_triangular {n : ℕ} (T : Finset (Fin n)) :
    (crossingInversions T).card + triangular T.card = indexSum T := by
  rw [triangular_eq_add_choose, indexSum_eq_sum_val_add_card]
  have h := crossing_count_add_choose T
  omega

/-! ## 6. Formal induction, isolated from the permutation calculation -/

/-!
This lemma is the complete *induction mechanism*: it takes exactly
(1) the sign in the empty case and (2) the sign change on deleting
one element. No sign formula is assumed.

The proof is an ordinary induction on the finite set. In the insertion
step, `induction_exponent_step` (proved above) supplies all the
arithmetic; only the actual permutation-sign change is needed.

Below we instead use the exact inversion count to obtain the sign
formula directly, retaining this conditional induction as an auxiliary tool.
-/
theorem shuffle_sign_induction_of_step {n : ℕ}
    (h0 : Equiv.Perm.sign (shuffle (∅ : Finset (Fin n))) = 1)
    (hstep : ∀ (T : Finset (Fin n)) (t : Fin n), t ∈ T →
      Equiv.Perm.sign (shuffle T) =
        (-1 : ℤˣ) ^ (t.val + T.card - 1) *
          Equiv.Perm.sign (shuffle (T.erase t)))
    (T : Finset (Fin n)) :
    Equiv.Perm.sign (shuffle T) =
      (-1 : ℤˣ) ^ (indexSum T + triangular T.card) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simpa [indexSum, triangular] using h0
  | @insert t s hts ih =>
      have ht : t ∈ insert t s := by simp
      have herase : (insert t s).erase t = s := by
        simp [hts]
      calc
        Equiv.Perm.sign (shuffle (insert t s)) =
            (-1 : ℤˣ) ^ (t.val + (insert t s).card - 1) *
              Equiv.Perm.sign (shuffle ((insert t s).erase t)) :=
          hstep (insert t s) t ht
        _ = (-1 : ℤˣ) ^ (t.val + (insert t s).card - 1) *
              (-1 : ℤˣ) ^ (indexSum s + triangular s.card) := by
          rw [herase, ih]
        _ = (-1 : ℤˣ) ^
              (indexSum (insert t s) + triangular (insert t s).card) := by
          simpa only [herase] using
            (induction_exponent_step (insert t s) t ht).symm

/-!
The actual shuffle sign is now deduced directly from the proved
crossing-inversion correspondence and the exact count above. The
conditional insertion-induction theorem remains available, but the
final proof does not require a separate adjacent-swap construction.
-/
theorem shuffle_sign_induction {n : ℕ} (T : Finset (Fin n)) :
    Equiv.Perm.sign (shuffle T) =
      (-1 : ℤˣ) ^ (indexSum T + triangular T.card) := by
  rw [shuffle_sign_eq_pow_crossingInversions_card]
  have hcount := crossing_count_add_triangular T
  have hexp : indexSum T + triangular T.card =
      (crossingInversions T).card + 2 * triangular T.card := by
    omega
  rw [hexp, pow_add, pow_mul]
  norm_num

/-! ## 7. Pure parity cancellation (no induction needed) -/

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

/-! ## 8. The final lemma, deduced from the shuffle induction -/

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
