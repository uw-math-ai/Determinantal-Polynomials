import Mathlib

/-!
# Counterexample to the necessity direction of the principal-minor fiber criterion

This independent file is based on Theorem 4.1 in
`A Cut-Transpose Gap in a Claimed Characterization of Principal-Minor Fibers`
(6 November 2026), rather than on the *incorrect* theorem in the 2023 paper.

Status: an UNCOMPILED v29 development draft.  It is NOT a kernel-verified
formalization.  The intended complete proof, including the normalization
and the fiber theorem, is written below but requires Lean 4 compilation,
error correction, and a warning-free regression before it can be accepted
as a new verified baseline.  No proof holes or unproved assumptions are introduced.

We use zero-based indices, so the exceptional pair (1,2) in the paper is
(0,1) here.
-/

namespace DetPoly.Theorem41

open scoped BigOperators Matrix

noncomputable section

variable {F : Type*} [Field F]

/-! ## A. Small algebraic rigidity lemmas -/

/-- The two reciprocal-looking equations `xy = 1`, `x + y = 2`
force `x = y = 1` over a field, without a characteristic assumption.
The proof avoids dividing by 2, so it also works in characteristic 2. -/
theorem eq_one_of_add_eq_two_mul_eq_one
    {x y : F} (hsum : x + y = 2) (hprod : x * y = 1) :
    x = 1 ∧ y = 1 := by
  have hsq : (x - 1) * (x - 1) = 0 := by
    calc
      (x - 1) * (x - 1) = x * (x + y - 2) - (x * y - 1) := by ring
      _ = 0 := by rw [hsum, hprod]; ring
  have hx : x = 1 := by
    rcases mul_eq_zero.mp hsq with h | h
    · exact sub_eq_zero.mp h
    · exact sub_eq_zero.mp h
  constructor
  · exact hx
  · have hy : 1 * y = 1 := by simpa [hx] using hprod
    simpa using hy

/-- Equality of two units follows from their pairwise products and
one mixed third-order (three-cycle) equation.

This is the calculation behind (4.9) of the source.  The identity

`(x-u)^2 = xu(xv+uy-2) - x²(uv-1) - u²(xy-1)`

uses only ring operations and holds in every characteristic. -/
theorem same_of_pair_products_and_mixed_sum
    {x y u v : F}
    (hxy : x * y = 1) (huv : u * v = 1)
    (hmix : x * v + u * y = 2) :
    x = u ∧ y = v := by
  have hsq : (x - u) * (x - u) = 0 := by
    calc
      (x - u) * (x - u) =
          x * u * (x * v + u * y - 2)
          - x * x * (u * v - 1)
          - u * u * (x * y - 1) := by ring
      _ = 0 := by rw [hmix, huv, hxy]; ring
  have hxu : x = u := by
    rcases mul_eq_zero.mp hsq with h | h
    · exact sub_eq_zero.mp h
    · exact sub_eq_zero.mp h
  constructor
  · exact hxu
  · have h : u * y = u * v := by
      calc
        u * y = x * y := by rw [hxu]
        _ = 1 := hxy
        _ = u * v := huv.symm
    have hu : u ≠ 0 := by
      intro hzero
      simp [hzero] at huv
    exact mul_left_cancel₀ hu h

/-- The factorization used in (4.7): a third-order principal minor
forces the exceptional entry to be either `1` or `q / p`.
No square roots or order structure are needed. -/
theorem factor_switch_dichotomy
    {p q x y : F}
    (hxy : x * y = 1)
    (hcycle : p * x + q * y = p + q) :
    x = 1 ∨ p * x = q := by
  have hfactor : (x - 1) * (p * x - q) = 0 := by
    calc
      (x - 1) * (p * x - q) =
          x * (p * x + q * y - (p + q)) - q * (x * y - 1) := by ring
      _ = 0 := by rw [hcycle, hxy]; ring
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-! ## B. Matrices and the actual principal-minor map -/

/-- The family (4.1), with paper indices shifted by one:
`a₀₁ = p`, `a₁₀ = q`, all diagonal entries vanish, and all other
off-diagonal entries equal one. -/
def exampleMatrix {n : ℕ} (p q : F) : Matrix (Fin n) (Fin n) F :=
  fun i j =>
    if i = j then 0
    else if i.val = 0 ∧ j.val = 1 then p
    else if i.val = 1 ∧ j.val = 0 then q
    else 1

/-- The formal principal-minor relation.  An injective enumeration
`f : Fin k → Fin n` enumerates a `k`-element principal submatrix.
Every principal subset can be enumerated this way; allowing *all*
enumerations avoids choosing a sorting convention. -/
def SamePrincipalMinors {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ (k : ℕ) (f : Fin k → Fin n), Function.Injective f →
    (A.submatrix f f).det = (B.submatrix f f).det

/-- Diagonal similarity in entrywise form, with all diagonal
entries of the conjugating matrix required to be invertible. -/
def DiagonallySimilar {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) : Prop :=
  ∃ d : Fin n → F, (∀ i, d i ≠ 0) ∧
    ∀ i j, B i j = d i * A i j * (d j)⁻¹

/-- Diagonal equivalence permits both diagonal similarity and a
global transpose; it must not be mistaken for diagonal similarity. -/
def DiagonallyEquivalent {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) F) : Prop :=
  DiagonallySimilar A B ∨ DiagonallySimilar Aᵀ B

/-- The entries on the diagonal are zero. -/
theorem exampleMatrix_diag {n : ℕ} (p q : F) (i : Fin n) :
    exampleMatrix p q i i = 0 := by
  simp [exampleMatrix]

/-- Every off-diagonal entry is nonzero if `p`, `q` are nonzero.
This is the combinatorial reason for irreducibility. -/
theorem exampleMatrix_offdiag_ne_zero {n : ℕ}
    (p q : F) (hp : p ≠ 0) (hq : q ≠ 0)
    (i j : Fin n) (hij : i ≠ j) :
    exampleMatrix p q i j ≠ 0 := by
  simp only [exampleMatrix]
  split_ifs with h₀ h₁ h₂
  · exact (hij h₀).elim
  · exact hp
  · exact hq
  · exact one_ne_zero

/-- The matrix is genuinely nonsymmetric along the exceptional edge
when `p ≠ q`. -/
theorem exampleMatrix_exceptional_entries {n : ℕ}
    (hn : 2 ≤ n) (p q : F) :
    exampleMatrix p q (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) = p ∧
    exampleMatrix p q (⟨1, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n) = q := by
  constructor <;> simp [exampleMatrix]

/-! ## C. The first three principal-minor identities -/

/-- Extract diagonal entries from the singleton principal minors. -/
theorem diagonal_eq_of_samePrincipalMinors {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (h : SamePrincipalMinors A B) (i : Fin n) :
    A i i = B i i := by
  let f : Fin 1 → Fin n := fun _ => i
  have hf : Function.Injective f := fun a b _ => Subsingleton.elim a b
  have hdet := h 1 f hf
  simpa [Matrix.det_fin_one, f] using hdet

/-! ## C1. Explicit enumeration of principal 2×2 and 3×3 blocks -/

/-- A two-element ordered enumeration. -/
def pairIdx {n : ℕ} (i j : Fin n) (t : Fin 2) : Fin n :=
  if t.val = 0 then i else j

/-- A three-element ordered enumeration. -/
def tripleIdx {n : ℕ} (i j k : Fin n) (t : Fin 3) : Fin n :=
  if t.val = 0 then i else if t.val = 1 then j else k

private theorem pairIdx_injective {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Function.Injective (pairIdx i j) := by
  have hji : j ≠ i := hij.symm
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [pairIdx]

private theorem tripleIdx_injective {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (tripleIdx i j k) := by
  have hji : j ≠ i := hij.symm
  have hki : k ≠ i := hik.symm
  have hkj : k ≠ j := hjk.symm
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [tripleIdx]

/-- Equality of second-order principal minors yields equality of
off-diagonal pair products for *zero-diagonal* matrices. -/
theorem pair_product_of_samePrincipalMinors {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (h : SamePrincipalMinors A B) (hzero : ∀ i, A i i = 0)
    (i j : Fin n) (hij : i ≠ j) :
    A i j * A j i = B i j * B j i := by
  have hzB (t : Fin n) : B t t = 0 := by
    rw [← diagonal_eq_of_samePrincipalMinors h]
    exact hzero t
  have hdet := h 2 (pairIdx i j) (pairIdx_injective hij)
  have hh : -(A i j * A j i) = -(B i j * B j i) := by
    simpa [Matrix.det_fin_two, pairIdx,
      hzero i, hzero j, hzB i, hzB j] using hdet
  exact neg_inj.mp hh

/-- Equality of third-order principal minors yields equality of
the two directed-cycle sums when diagonal entries vanish. -/
theorem triple_cycle_sum_of_samePrincipalMinors {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (h : SamePrincipalMinors A B) (hzero : ∀ i, A i i = 0)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    A i j * A j k * A k i + A i k * A j i * A k j =
      B i j * B j k * B k i + B i k * B j i * B k j := by
  have hzB (t : Fin n) : B t t = 0 := by
    rw [← diagonal_eq_of_samePrincipalMinors h]
    exact hzero t
  have hdet := h 3 (tripleIdx i j k)
    (tripleIdx_injective hij hik hjk)
  simpa [Matrix.det_fin_three, tripleIdx,
    hzero i, hzero j, hzero k,
    hzB i, hzB j, hzB k] using hdet

/-! ## C2. Principal minors and diagonal conjugation -/

/-- An entrywise diagonal conjugation.  `d` is checked for
nonvanishing in each theorem that requires it. -/
def diagConj {n : ℕ} (d : Fin n → F)
    (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  fun i j => d i * A i j * (d j)⁻¹

/-- Determinants of arbitrary principal submatrices are invariant
under a diagonal change of basis.  The proof uses mathlib's
row/column scaling identities; the two products cancel pointwise. -/
theorem det_diagConj_submatrix {n k : ℕ}
    (d : Fin n → F) (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin n) (Fin n) F) (f : Fin k → Fin n) :
    ((diagConj d A).submatrix f f).det =
      (A.submatrix f f).det := by
  let M : Matrix (Fin k) (Fin k) F := A.submatrix f f
  let v : Fin k → F := fun i => d (f i)
  let N : Matrix (Fin k) (Fin k) F :=
    fun i j => (v j)⁻¹ * M i j
  have hv (i : Fin k) : v i ≠ 0 := hd (f i)
  have hN : N.det = (∏ i : Fin k, (v i)⁻¹) * M.det := by
    have hNeq : N = Matrix.of (fun i j => (v j)⁻¹ * M i j) := by
      ext i j
      rfl
    rw [hNeq]
    exact Matrix.det_mul_row (fun i => (v i)⁻¹) M
  have hprod :
      (∏ i : Fin k, v i) * (∏ i : Fin k, (v i)⁻¹) = (1 : F) := by
    rw [← Finset.prod_mul_distrib]
    simp [hv]
  calc
    ((diagConj d A).submatrix f f).det =
        (Matrix.of fun (i j : Fin k) => v i * N i j).det := by
      congr 1
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.of_apply]
      dsimp [diagConj, N, M, v]
      ring
    _ = (∏ i : Fin k, v i) * N.det := Matrix.det_mul_column v N
    _ = (∏ i : Fin k, v i) *
          ((∏ i : Fin k, (v i)⁻¹) * M.det) := by rw [hN]
    _ = M.det := by rw [← mul_assoc, hprod, one_mul]
    _ = (A.submatrix f f).det := rfl

/-- All principal minors survive diagonal conjugation. -/
theorem samePrincipalMinors_diagConj {n : ℕ}
    (d : Fin n → F) (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin n) (Fin n) F) :
    SamePrincipalMinors A (diagConj d A) := by
  intro k f _
  exact (det_diagConj_submatrix d hd A f).symm

/-- Transposition preserves principal minors. -/
theorem samePrincipalMinors_transpose {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    SamePrincipalMinors A Aᵀ := by
  intro k f _
  simpa only [← Matrix.transpose_submatrix] using
    (Matrix.det_transpose (A.submatrix f f)).symm

/-- Same principal minors is transitive. -/
theorem samePrincipalMinors_trans {n : ℕ}
    {A B C : Matrix (Fin n) (Fin n) F}
    (hAB : SamePrincipalMinors A B)
    (hBC : SamePrincipalMinors B C) :
    SamePrincipalMinors A C := by
  intro k f hf
  exact (hAB k f hf).trans (hBC k f hf)

/-- The normalized matrix remains in the original principal-minor
fiber: no hidden assumption about the fiber is introduced here. -/
theorem samePrincipalMinors_normalize {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (h : SamePrincipalMinors A B)
    (d : Fin n → F) (hd : ∀ i, d i ≠ 0) :
    SamePrincipalMinors A (diagConj d B) :=
  samePrincipalMinors_trans h (samePrincipalMinors_diagConj d hd B)

/-! ## C3. Algebra of diagonal conjugations -/

/-- Composition of two diagonal conjugations. -/
theorem diagConj_comp {n : ℕ}
    (d e : Fin n → F) (A : Matrix (Fin n) (Fin n) F) :
    diagConj d (diagConj e A) =
      diagConj (fun i => d i * e i) A := by
  funext i j
  simp only [diagConj, mul_inv_rev]
  ring

/-- The inverse diagonal conjugation undoes the original. -/
theorem diagConj_inverse {n : ℕ}
    (d : Fin n → F) (hd : ∀ i, d i ≠ 0)
    (A : Matrix (Fin n) (Fin n) F) :
    diagConj (fun i => (d i)⁻¹) (diagConj d A) = A := by
  funext i j
  simp only [diagConj, inv_inv]
  field_simp [hd i, hd j]

/-- Reflexivity of diagonal similarity. -/
theorem diagonalSimilar_refl {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    DiagonallySimilar A A := by
  refine ⟨fun _ => 1, (by simp), ?_⟩
  intro i j
  simp

/-- Symmetry of diagonal similarity. -/
theorem diagonalSimilar_symm {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (h : DiagonallySimilar A B) : DiagonallySimilar B A := by
  obtain ⟨d, hd, hB⟩ := h
  refine ⟨(fun i => (d i)⁻¹), (fun i => inv_ne_zero (hd i)), ?_⟩
  intro i j
  rw [hB]
  simp only [inv_inv]
  field_simp [hd i, hd j]

/-- Transitivity of diagonal similarity. -/
theorem diagonalSimilar_trans {n : ℕ}
    {A B C : Matrix (Fin n) (Fin n) F}
    (hAB : DiagonallySimilar A B) (hBC : DiagonallySimilar B C) :
    DiagonallySimilar A C := by
  obtain ⟨d, hd, hB⟩ := hAB
  obtain ⟨e, he, hC⟩ := hBC
  refine ⟨(fun i => e i * d i), (fun i => mul_ne_zero (he i) (hd i)), ?_⟩
  intro i j
  rw [hC, hB]
  simp only [mul_inv_rev]
  ring

/-- Diagonal similarity of a matrix is a literal change of basis,
so transposition is allowed as a *second*, distinct alternative. -/
theorem diagonallyEquivalent_of_diagonalSimilar {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (h : DiagonallySimilar A B) : DiagonallyEquivalent A B :=
  Or.inl h

/-! ## D. The three-cycle obstruction to symmetrization -/

/-- The product of entries around a directed triangle. -/
def directedCycle {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (i j k : Fin n) : F :=
  A i j * A j k * A k i

/-- A change of basis by an invertible diagonal matrix cancels
around each directed cycle. -/
theorem cycle_invariant_of_diagonal_similarity {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (h : DiagonallySimilar A B) (i j k : Fin n) :
    directedCycle A i j k = directedCycle B i j k := by
  obtain ⟨d, hd, hB⟩ := h
  simp only [directedCycle, hB]
  field_simp [hd i, hd j, hd k]

/-- If `B` is symmetric, its clockwise and counterclockwise
triangle products coincide. -/
theorem cycle_reverse_of_symmetric {n : ℕ}
    (B : Matrix (Fin n) (Fin n) F) (hB : B = Bᵀ)
    (i j k : Fin n) :
    directedCycle B i j k = directedCycle B i k j := by
  have hij : B i j = B j i := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) hB
    simpa using h
  have hjk : B j k = B k j := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M j k) hB
    simpa using h
  have hki : B k i = B i k := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M k i) hB
    simpa using h
  simp only [directedCycle]
  rw [hij, hjk, hki]
  ring

/-- For the exceptional triangle `(0,1,2)` the two oriented
products are exactly `p` and `q`. -/
theorem example_cycles {n : ℕ} (hn : 4 ≤ n) (p q : F) :
    directedCycle (exampleMatrix (n := n) p q)
      ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ = p ∧
    directedCycle (exampleMatrix (n := n) p q)
      ⟨0, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ = q := by
  constructor <;> simp [directedCycle, exampleMatrix]

/-- Assertion (ii) of Theorem 4.1 over the ground field.
The cycle obstruction survives under any extension in which the
images of `p` and `q` remain distinct. -/
theorem not_diagonally_symmetrizable {n : ℕ}
    (hn : 4 ≤ n) (p q : F) (hpq : p ≠ q) :
    ¬ ∃ S : Matrix (Fin n) (Fin n) F,
      DiagonallySimilar (exampleMatrix p q) S ∧ S = Sᵀ := by
  rintro ⟨S, hsim, hsym⟩
  have c₁ := cycle_invariant_of_diagonal_similarity hsim
    (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨2, by omega⟩
  have c₂ := cycle_invariant_of_diagonal_similarity hsim
    (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩ ⟨1, by omega⟩
  have cs := cycle_reverse_of_symmetric S hsym
    (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨2, by omega⟩
  have hc := example_cycles hn p q
  apply hpq
  calc
    p = directedCycle (exampleMatrix (n := n) p q)
        ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ := hc.1.symm
    _ = directedCycle S ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ := c₁
    _ = directedCycle S ⟨0, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ := cs
    _ = directedCycle (exampleMatrix (n := n) p q)
          ⟨0, by omega⟩ ⟨2, by omega⟩ ⟨1, by omega⟩ := c₂.symm
    _ = q := hc.2

/-- The cycle obstruction is unchanged by passing to any field
extension.  Field homomorphisms are injective, hence unequal
parameters cannot become equal after scalar extension. -/
theorem not_diagonally_symmetrizable_over_extension {n : ℕ}
    (hn : 4 ≤ n) (p q : F) (hpq : p ≠ q)
    {K : Type*} [Field K] [Algebra F K] :
    ¬ ∃ S : Matrix (Fin n) (Fin n) K,
      DiagonallySimilar
        (exampleMatrix ((algebraMap F K) p) ((algebraMap F K) q)) S ∧
      S = Sᵀ := by
  have hneq : (algebraMap F K) p ≠ (algebraMap F K) q :=
    (RingHom.injective (algebraMap F K)).ne hpq
  exact not_diagonally_symmetrizable hn _ _ hneq

/-- The original criterion uses diagonal *equivalence* (which
permits a global transpose).  If a matrix is diagonally equivalent
to a symmetric matrix, it is already diagonally *similar* to one:
transposing the second alternative and using symmetry replaces the
conjugating diagonal by its inverse. -/
theorem diagonalEquivalent_symmetric_implies_diagonalSimilar {n : ℕ}
    {A S : Matrix (Fin n) (Fin n) F}
    (h : DiagonallyEquivalent A S) (hsym : S = Sᵀ) :
    DiagonallySimilar A S := by
  rcases h with h | h
  · exact h
  · obtain ⟨d, hd, hS⟩ := h
    refine ⟨(fun i => (d i)⁻¹), (fun i => inv_ne_zero (hd i)), ?_⟩
    intro i j
    have hswap : S i j = S j i := by
      have hh := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) hsym
      simpa using hh
    calc
      S i j = S j i := hswap
      _ = d j * A i j * (d i)⁻¹ := by
        simpa only [Matrix.transpose_apply] using hS j i
      _ = (d i)⁻¹ * A i j * ((d j)⁻¹)⁻¹ := by
        rw [inv_inv]
        ring

/-- The example is not even diagonally *equivalent* to a symmetric
matrix.  This is the precise obstruction relevant to the incorrect
necessity direction in the 2023 theorem. -/
theorem not_diagonally_equivalent_to_symmetric {n : ℕ}
    (hn : 4 ≤ n) (p q : F) (hpq : p ≠ q) :
    ¬ ∃ S : Matrix (Fin n) (Fin n) F,
      DiagonallyEquivalent (exampleMatrix p q) S ∧ S = Sᵀ := by
  rintro ⟨S, hsim, hsym⟩
  exact not_diagonally_symmetrizable hn p q hpq
    ⟨S, diagonalEquivalent_symmetric_implies_diagonalSimilar hsim hsym, hsym⟩

/-! ## E. Rigidity of a normalized fiber representative -/

/-- Three distinguished indices; these are mathematical indices 1,2,3
in the paper and zero-based indices 0,1,2 in Lean. -/
private def iZero {n : ℕ} (hn : 4 ≤ n) : Fin n := ⟨0, by omega⟩
private def iOne {n : ℕ} (hn : 4 ≤ n) : Fin n := ⟨1, by omega⟩
private def iTwo {n : ℕ} (hn : 4 ≤ n) : Fin n := ⟨2, by omega⟩

private theorem zero_ne_one {n : ℕ} (hn : 4 ≤ n) :
    iZero hn ≠ iOne hn := by simp [iZero, iOne]
private theorem zero_ne_two {n : ℕ} (hn : 4 ≤ n) :
    iZero hn ≠ iTwo hn := by simp [iZero, iTwo]
private theorem one_ne_two {n : ℕ} (hn : 4 ≤ n) :
    iOne hn ≠ iTwo hn := by simp [iOne, iTwo]

private theorem tail_ne_zero {n : ℕ} (hn : 4 ≤ n)
    (i : Fin n) (hi : 2 ≤ i.val) : iZero hn ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp [iZero] at hv
  omega

private theorem tail_ne_one {n : ℕ} (hn : 4 ≤ n)
    (i : Fin n) (hi : 2 ≤ i.val) : iOne hn ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  simp [iOne] at hv
  omega

private theorem example_first_tail {n : ℕ} (hn : 4 ≤ n)
    (p q : F) (i : Fin n) (hi : 2 ≤ i.val) :
    exampleMatrix p q (iZero hn) i = 1 ∧
    exampleMatrix p q i (iZero hn) = 1 ∧
    exampleMatrix p q (iOne hn) i = 1 ∧
    exampleMatrix p q i (iOne hn) = 1 := by
  have h0 : i.val ≠ 0 := by omega
  have h1 : i.val ≠ 1 := by omega
  -- Matrix-element comparisons occur in both orientations: `i = 0`
  -- and `0 = i`.  Give the simplifier the appropriately oriented
  -- inequality in each case (rather than relying on `eq_comm`).
  have h0rev : 0 ≠ i.val := h0.symm
  have h1rev : 1 ≠ i.val := h1.symm
  constructor
  · simp [exampleMatrix, iZero, Fin.ext_iff, h0rev, h1]
  constructor
  · simp [exampleMatrix, iZero, Fin.ext_iff, h0, h1]
  constructor
  · simp [exampleMatrix, iOne, Fin.ext_iff, h1rev, h0]
  · simp [exampleMatrix, iOne, Fin.ext_iff, h0, h1]

private theorem example_tail_tail {n : ℕ} (p q : F)
    (i j : Fin n) (hi : 2 ≤ i.val) (_hj : 2 ≤ j.val)
    (hij : i ≠ j) :
    exampleMatrix p q i j = 1 := by
  have hi0 : i.val ≠ 0 := by omega
  have hi1 : i.val ≠ 1 := by omega
  simp [exampleMatrix, hij, hi0, hi1]

private theorem example_first_pair {n : ℕ} (hn : 4 ≤ n) (p q : F) :
    exampleMatrix p q (iZero hn) (iOne hn) = p ∧
    exampleMatrix p q (iOne hn) (iZero hn) = q := by
  simpa [iZero, iOne] using
    exampleMatrix_exceptional_entries (by omega : 2 ≤ n) p q

/-- Exactly the identities supplied by the principal minors of
orders 1, 2, 3 after conjugating so that the first row and column
agree with the witness matrix.  This structure does **not** assert
any form of the desired diagonal equivalence. -/
structure NormalizedMinorData {n : ℕ} (hn : 4 ≤ n)
    (p q : F) (B : Matrix (Fin n) (Fin n) F) : Prop where
  diag_zero : ∀ i, B i i = 0
  first_row : ∀ j, B (iZero hn) j = exampleMatrix p q (iZero hn) j
  first_col : ∀ i, B i (iZero hn) = exampleMatrix p q i (iZero hn)
  tail_pair : ∀ i j, 2 ≤ i.val → 2 ≤ j.val → i ≠ j →
    B i j * B j i = 1
  tail_sum : ∀ i j, 2 ≤ i.val → 2 ≤ j.val → i ≠ j →
    B i j + B j i = 2
  one_pair : ∀ i, 2 ≤ i.val →
    B (iOne hn) i * B i (iOne hn) = 1
  one_mixed : ∀ i j, 2 ≤ i.val → 2 ≤ j.val → i ≠ j →
    B (iOne hn) i * B j (iOne hn) +
    B (iOne hn) j * B i (iOne hn) = 2
  exceptional_cycle : ∀ i, 2 ≤ i.val →
    p * B (iOne hn) i + q * B i (iOne hn) = p + q

/-- The low-order principal minors supply all the normalized
identities.  The proof uses *actual* determinants, not formalized
cycle equations postulated as an alternative hypothesis. -/
theorem normalizedMinorData_of_samePrincipalMinors {n : ℕ}
    (hn : 4 ≤ n) (p q : F)
    (B : Matrix (Fin n) (Fin n) F)
    (hpm : SamePrincipalMinors (exampleMatrix p q) B)
    (hrow : ∀ j, B (iZero hn) j = exampleMatrix p q (iZero hn) j)
    (hcol : ∀ i, B i (iZero hn) = exampleMatrix p q i (iZero hn)) :
    NormalizedMinorData hn p q B := by
  let A : Matrix (Fin n) (Fin n) F := exampleMatrix p q
  have hzero : ∀ i, A i i = 0 := exampleMatrix_diag p q
  have hdiag : ∀ i, B i i = 0 := by
    intro i
    rw [← diagonal_eq_of_samePrincipalMinors hpm]
    exact hzero i
  have hpair (i j : Fin n) (hij : i ≠ j) :
      A i j * A j i = B i j * B j i :=
    pair_product_of_samePrincipalMinors hpm hzero i j hij
  have htrip (i j k : Fin n)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      A i j * A j k * A k i + A i k * A j i * A k j =
        B i j * B j k * B k i + B i k * B j i * B k j :=
    triple_cycle_sum_of_samePrincipalMinors hpm hzero i j k hij hik hjk
  have htailpair (i j : Fin n) (hi : 2 ≤ i.val)
      (hj : 2 ≤ j.val) (hij : i ≠ j) :
      B i j * B j i = 1 := by
    have h₁ : A i j = 1 := example_tail_tail p q i j hi hj hij
    have h₂ : A j i = 1 := example_tail_tail p q j i hj hi (Ne.symm hij)
    simpa only [h₁, h₂, one_mul] using (hpair i j hij).symm
  have htailsum (i j : Fin n) (hi : 2 ≤ i.val)
      (hj : 2 ≤ j.val) (hij : i ≠ j) :
      B i j + B j i = 2 := by
    rcases example_first_tail hn p q i hi with ⟨ha0i, hai0, _, _⟩
    rcases example_first_tail hn p q j hj with ⟨ha0j, haj0, _, _⟩
    -- Keep these equalities in their expanded `exampleMatrix` form:
    -- the subsequent `dsimp only [A]` unfolds the local abbreviation.
    -- Rewriting with `A i j = 1` after that unfolding cannot match.
    have haij : exampleMatrix p q i j = 1 :=
      example_tail_tail p q i j hi hj hij
    have haji : exampleMatrix p q j i = 1 :=
      example_tail_tail p q j i hj hi (Ne.symm hij)
    have hA : A (iZero hn) i * A i j * A j (iZero hn) +
        A (iZero hn) j * A i (iZero hn) * A j i = (2 : F) := by
      dsimp only [A]
      rw [ha0i, haij, haj0, ha0j, hai0, haji]
      ring
    have hB : B (iZero hn) i * B i j * B j (iZero hn) +
        B (iZero hn) j * B i (iZero hn) * B j i =
        B i j + B j i := by
      rw [hrow i, hcol j, hrow j, hcol i]
      simp [ha0i, hai0, ha0j, haj0]
    calc
      B i j + B j i = B (iZero hn) i * B i j * B j (iZero hn) +
          B (iZero hn) j * B i (iZero hn) * B j i := hB.symm
      _ = A (iZero hn) i * A i j * A j (iZero hn) +
          A (iZero hn) j * A i (iZero hn) * A j i :=
            (htrip (iZero hn) i j
              (tail_ne_zero hn i hi) (tail_ne_zero hn j hj) hij).symm
      _ = 2 := hA
  have htailone (i j : Fin n) (hi : 2 ≤ i.val)
      (hj : 2 ≤ j.val) (hij : i ≠ j) :
      B i j = 1 ∧ B j i = 1 :=
    eq_one_of_add_eq_two_mul_eq_one
      (htailsum i j hi hj hij) (htailpair i j hi hj hij)
  have honepair (i : Fin n) (hi : 2 ≤ i.val) :
      B (iOne hn) i * B i (iOne hn) = 1 := by
    rcases example_first_tail hn p q i hi with ⟨_, _, ha1i, hai1⟩
    calc
      B (iOne hn) i * B i (iOne hn) = A (iOne hn) i * A i (iOne hn) :=
        (hpair (iOne hn) i (tail_ne_one hn i hi)).symm
      _ = 1 := by
        dsimp only [A]
        rw [ha1i, hai1]
        ring
  have honemixed (i j : Fin n) (hi : 2 ≤ i.val)
      (hj : 2 ≤ j.val) (hij : i ≠ j) :
      B (iOne hn) i * B j (iOne hn) +
        B (iOne hn) j * B i (iOne hn) = 2 := by
    rcases example_first_tail hn p q i hi with ⟨_, _, ha1i, hai1⟩
    rcases example_first_tail hn p q j hj with ⟨_, _, ha1j, haj1⟩
    -- The exact concrete matrix must be visible to `rw` after unfolding `A`.
    have haij : exampleMatrix p q i j = 1 :=
      example_tail_tail p q i j hi hj hij
    have haji : exampleMatrix p q j i = 1 :=
      example_tail_tail p q j i hj hi (Ne.symm hij)
    have hA : A (iOne hn) i * A i j * A j (iOne hn) +
        A (iOne hn) j * A i (iOne hn) * A j i = (2 : F) := by
      dsimp only [A]
      rw [ha1i, haij, haj1, ha1j, hai1, haji]
      ring
    rcases htailone i j hi hj hij with ⟨hbij, hbji⟩
    have hB : B (iOne hn) i * B i j * B j (iOne hn) +
        B (iOne hn) j * B i (iOne hn) * B j i =
        B (iOne hn) i * B j (iOne hn) +
        B (iOne hn) j * B i (iOne hn) := by
      rw [hbij, hbji]
      ring
    calc
      B (iOne hn) i * B j (iOne hn) +
          B (iOne hn) j * B i (iOne hn) =
          B (iOne hn) i * B i j * B j (iOne hn) +
          B (iOne hn) j * B i (iOne hn) * B j i := hB.symm
      _ = A (iOne hn) i * A i j * A j (iOne hn) +
          A (iOne hn) j * A i (iOne hn) * A j i :=
            (htrip (iOne hn) i j
              (tail_ne_one hn i hi) (tail_ne_one hn j hj) hij).symm
      _ = 2 := hA
  have hexception (i : Fin n) (hi : 2 ≤ i.val) :
      p * B (iOne hn) i + q * B i (iOne hn) = p + q := by
    rcases example_first_tail hn p q i hi with ⟨ha0i, hai0, ha1i, hai1⟩
    rcases example_first_pair hn p q with ⟨ha01, ha10⟩
    have hA : A (iZero hn) (iOne hn) * A (iOne hn) i * A i (iZero hn) +
        A (iZero hn) i * A (iOne hn) (iZero hn) * A i (iOne hn) =
        p + q := by
      dsimp only [A]
      rw [ha01, ha10, ha0i, hai0, ha1i, hai1]
      ring
    have hB : B (iZero hn) (iOne hn) * B (iOne hn) i * B i (iZero hn) +
        B (iZero hn) i * B (iOne hn) (iZero hn) * B i (iOne hn) =
        p * B (iOne hn) i + q * B i (iOne hn) := by
      rw [hrow (iOne hn), hcol (iOne hn), hrow i, hcol i]
      simp [ha01, ha10, ha0i, hai0]
    calc
      p * B (iOne hn) i + q * B i (iOne hn) =
          B (iZero hn) (iOne hn) * B (iOne hn) i * B i (iZero hn) +
          B (iZero hn) i * B (iOne hn) (iZero hn) * B i (iOne hn) :=
            hB.symm
      _ = A (iZero hn) (iOne hn) * A (iOne hn) i * A i (iZero hn) +
          A (iZero hn) i * A (iOne hn) (iZero hn) * A i (iOne hn) :=
            (htrip (iZero hn) (iOne hn) i
              (zero_ne_one hn) (tail_ne_zero hn i hi)
              (tail_ne_one hn i hi)).symm
      _ = p + q := hA
  exact {
    diag_zero := hdiag
    first_row := hrow
    first_col := hcol
    tail_pair := htailpair
    tail_sum := htailsum
    one_pair := honepair
    one_mixed := honemixed
    exceptional_cycle := hexception
  }

/-- All off-diagonal entries in the tail block equal one. -/
theorem normalized_tail_entries {n : ℕ} {hn : 4 ≤ n}
    {p q : F} {B : Matrix (Fin n) (Fin n) F}
    (h : NormalizedMinorData hn p q B)
    (i j : Fin n) (hi : 2 ≤ i.val) (hj : 2 ≤ j.val)
    (hij : i ≠ j) :
    B i j = 1 ∧ B j i = 1 :=
  eq_one_of_add_eq_two_mul_eq_one
    (h.tail_sum i j hi hj hij) (h.tail_pair i j hi hj hij)

/-- The first row of the one/tail block is constant.
The proof uses the cross-multiplied form of (4.9) and never
inverts an entry prematurely. -/
theorem normalized_one_tail_constant {n : ℕ} {hn : 4 ≤ n}
    {p q : F} {B : Matrix (Fin n) (Fin n) F}
    (h : NormalizedMinorData hn p q B)
    (i : Fin n) (hi : 2 ≤ i.val) :
    B (iOne hn) i = B (iOne hn) (iTwo hn) ∧
    B i (iOne hn) = B (iTwo hn) (iOne hn) := by
  by_cases heq : i = iTwo hn
  · subst i
    exact ⟨rfl, rfl⟩
  have hpair₁ := h.one_pair i hi
  have hpair₂ := h.one_pair (iTwo hn) (by simp [iTwo])
  have hmix := h.one_mixed i (iTwo hn) hi
    (by simp [iTwo]) heq
  exact same_of_pair_products_and_mixed_sum hpair₁ hpair₂ hmix

/-- The common exceptional row parameter satisfies the factor
switching dichotomy. -/
theorem normalized_exceptional_dichotomy {n : ℕ} {hn : 4 ≤ n}
    {p q : F} {B : Matrix (Fin n) (Fin n) F}
    (h : NormalizedMinorData hn p q B) :
    B (iOne hn) (iTwo hn) = 1 ∨
      p * B (iOne hn) (iTwo hn) = q := by
  exact factor_switch_dichotomy
    (h.one_pair (iTwo hn) (by simp [iTwo]))
    (h.exceptional_cycle (iTwo hn) (by simp [iTwo]))

/-- The two possible normalized matrices from (4.10).
`representative p q 1 1` is the original witness.
`representative p q (q/p) (p/q)` is a diagonal conjugate
of the transpose when `p,q ≠ 0`. -/
def representative {n : ℕ} (p q r s : F) : Matrix (Fin n) (Fin n) F :=
  fun i j =>
    if i = j then 0
    else if i.val = 0 ∧ j.val = 1 then p
    else if i.val = 1 ∧ j.val = 0 then q
    else if i.val = 1 then r
    else if j.val = 1 then s
    else 1

/-- The normalized matrix is completely determined by the two
entries in its exceptional row/column.  This is the main
combinatorial classification step; no higher minors are used. -/
theorem normalized_eq_representative {n : ℕ} {hn : 4 ≤ n}
    {p q : F} {B : Matrix (Fin n) (Fin n) F}
    (h : NormalizedMinorData hn p q B) :
    B = representative p q
        (B (iOne hn) (iTwo hn)) (B (iTwo hn) (iOne hn)) := by
  funext i j
  by_cases hij : i = j
  · subst j
    simp [representative, h.diag_zero]
  by_cases hi0 : i.val = 0
  · have heq : i = iZero hn := Fin.ext (by simpa [iZero] using hi0)
    subst i
    have hj0 : j.val ≠ 0 := by
      intro hj0
      apply hij
      apply Fin.ext
      simpa [iZero] using hj0.symm
    by_cases hj1 : j.val = 1
    · simpa [representative, exampleMatrix, iZero, hj0, hj1] using h.first_row j
    · simpa [representative, exampleMatrix, iZero, hj0, hj1] using h.first_row j
  by_cases hj0 : j.val = 0
  · have heq : j = iZero hn := Fin.ext (by simpa [iZero] using hj0)
    subst j
    by_cases hi1 : i.val = 1
    · simpa [representative, exampleMatrix, iZero, hi0, hi1] using h.first_col i
    · simpa [representative, exampleMatrix, iZero, hi0, hi1] using h.first_col i
  by_cases hi1 : i.val = 1
  · have heq : i = iOne hn := Fin.ext (by simpa [iOne] using hi1)
    subst i
    have hj1 : j.val ≠ 1 := by
      intro hj1
      apply hij
      exact Fin.ext (by simpa [iOne] using hj1.symm)
    have hjtail : 2 ≤ j.val := by omega
    have hcommon := (normalized_one_tail_constant h j hjtail).1
    -- The diagonal condition in `representative` tests `1 = j.val`,
    -- whereas the case split gives `j.val ≠ 1`.  Supply that symmetry
    -- explicitly: otherwise `simp` leaves an artificial diagonal case.
    have hj1rev : 1 ≠ j.val := hj1.symm
    calc
      B (iOne hn) j = B (iOne hn) (iTwo hn) := hcommon
      _ = representative p q
            (B (iOne hn) (iTwo hn)) (B (iTwo hn) (iOne hn))
            (iOne hn) j := by
          simp [representative, iOne, Fin.ext_iff, hj0, hj1rev]
  by_cases hj1 : j.val = 1
  · have heq : j = iOne hn := Fin.ext (by simpa [iOne] using hj1)
    subst j
    have hitail : 2 ≤ i.val := by omega
    have hcommon := (normalized_one_tail_constant h i hitail).2
    calc
      B i (iOne hn) = B (iTwo hn) (iOne hn) := hcommon
      _ = representative p q
            (B (iOne hn) (iTwo hn)) (B (iTwo hn) (iOne hn))
            i (iOne hn) := by
          simp [representative, iOne, Fin.ext_iff, hi0, hi1]
  have hitail : 2 ≤ i.val := by omega
  have hjtail : 2 ≤ j.val := by omega
  have htail := (normalized_tail_entries h i j hitail hjtail hij).1
  simpa [representative, hij, hi0, hj0, hi1, hj1] using htail

/-- The branch with row parameter `1` is exactly the original
witness matrix. -/
theorem representative_one_one {n : ℕ} (p q : F) :
    representative (n := n) p q 1 1 = exampleMatrix p q := by
  funext i j
  simp only [representative, exampleMatrix]
  split_ifs <;> simp_all

/-- The diagonal scaling required in the second branch of (4.10). -/
def specialScale {n : ℕ} (r : F) (i : Fin n) : F :=
  if i.val = 1 then r else 1

private theorem specialScale_ne_zero {n : ℕ}
    {r : F} (hr : r ≠ 0) (i : Fin n) :
    specialScale r i ≠ 0 := by
  by_cases hi : i.val = 1 <;> simp [specialScale, hi, hr]

/-- The second normalized representative is a diagonal conjugate
of the transpose.  The hypotheses `pr=q` and `rs=1` are precisely
the two identities obtained from the low-order principal minors.
Thus no diagonal-equivalence hypothesis is smuggled in. -/
theorem representative_eq_transpose_conj {n : ℕ}
    (p q r s : F) (hr : p * r = q) (hrs : r * s = 1) :
    representative (n := n) p q r s =
      diagConj (specialScale r) (exampleMatrix p q)ᵀ := by
  have hrnz : r ≠ 0 := by
    intro hzero
    simp [hzero] at hrs
  have hsinv : s = r⁻¹ := by
    have hmul : r * s = r * r⁻¹ := by
      rw [hrs, mul_inv_cancel₀ hrnz]
    exact mul_left_cancel₀ hrnz hmul
  have hp : p = q * r⁻¹ := by
    calc
      p = (p * r) * r⁻¹ := by field_simp [hrnz]
      _ = q * r⁻¹ := by rw [hr]
  -- Separate the diagonal before expanding conditionals.  Otherwise
  -- `split_ifs` may leave a spurious case where `i ≠ j`, but both
  -- indices have value 1, and then incorrectly ask for `r = 1`.
  funext i j
  by_cases hij : i = j
  · subst j
    simp [representative, diagConj, exampleMatrix]
  have hval : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  have hji : j ≠ i := Ne.symm hij
  have hrp : r * p = q := by
    calc
      r * p = p * r := mul_comm r p
      _ = q := hr
  -- Avoid `split_ifs <;> simp_all` here: feeding the large collection of
  -- overlapping `if`-branch hypotheses back into `simp_all` can exhaust
  -- Lean's simplifier recursion depth.  The following cases correspond
  -- directly to the matrix blocks, and each branch simplifies only its goal.
  by_cases hi0 : i.val = 0
  · have hi1 : i.val ≠ 1 := by omega
    by_cases hj1 : j.val = 1
    · -- Exceptional entry (0,1): `p = q * r⁻¹`.
      have hj0 : j.val ≠ 0 := by omega
      simpa [representative, diagConj, specialScale, exampleMatrix,
        hij, hji, hi0, hi1, hj0, hj1] using hp
    · -- First row away from the exceptional column.
      simp [representative, diagConj, specialScale, exampleMatrix,
        hij, hji, hi0, hj1]
  · by_cases hi1 : i.val = 1
    · by_cases hj0 : j.val = 0
      · -- Exceptional entry (1,0): `q = r * p`.
        have hj1 : j.val ≠ 1 := by omega
        simpa [representative, diagConj, specialScale, exampleMatrix,
          hij, hji, hi0, hi1, hj0, hj1] using hrp.symm
      · -- Exceptional row, tail column.
        have hj1 : j.val ≠ 1 := by
          intro hj1
          exact hval (hi1.trans hj1.symm)
        simp [representative, diagConj, specialScale, exampleMatrix,
          hij, hji, hi1, hj0, hj1]
    · by_cases hj0 : j.val = 0
      · -- Tail row, first column.
        have hj1 : j.val ≠ 1 := by omega
        simp [representative, diagConj, specialScale, exampleMatrix,
          hij, hji, hi1, hj0]
      · by_cases hj1 : j.val = 1
        · -- Tail row, exceptional column: `s = r⁻¹`.
          simpa [representative, diagConj, specialScale, exampleMatrix,
            hij, hji, hi0, hi1, hj0, hj1] using hsinv
        · -- Both indices lie in the tail, but are distinct.
          simp [representative, diagConj, specialScale, exampleMatrix,
            hij, hji, hi1, hj1]

/-- From normalized minor identities we obtain *exactly* the two
matrix alternatives in equation (4.10). -/
theorem normalized_fiber_classification {n : ℕ} {hn : 4 ≤ n}
    {p q : F} {B : Matrix (Fin n) (Fin n) F}
    (h : NormalizedMinorData hn p q B) :
    B = exampleMatrix p q ∨
    DiagonallySimilar (exampleMatrix p q)ᵀ B := by
  let r := B (iOne hn) (iTwo hn)
  let s := B (iTwo hn) (iOne hn)
  have hrs : r * s = 1 := h.one_pair (iTwo hn) (by simp [iTwo])
  have hrepr : B = representative p q r s := normalized_eq_representative h
  rcases normalized_exceptional_dichotomy h with hr | hr
  · left
    have hr' : r = 1 := hr
    have hs : s = 1 := by
      have hs' : (1 : F) * s = 1 := by simpa [hr'] using hrs
      simpa using hs'
    calc
      B = representative p q r s := hrepr
      _ = representative p q 1 1 := by rw [hr', hs]
      _ = exampleMatrix p q := representative_one_one p q
  · right
    have hrnz : r ≠ 0 := by
      intro hz
      simp [hz] at hrs
    have hdiag := representative_eq_transpose_conj (n := n) p q r s hr hrs
    refine ⟨specialScale r, specialScale_ne_zero hrnz, ?_⟩
    intro i j
    have hentry := congrArg
      (fun M : Matrix (Fin n) (Fin n) F => M i j)
      (hrepr.trans hdiag)
    simpa only [diagConj] using hentry

/-! ## F. Canonical first-row normalization -/

/-- A convenient diagonal gauge: the zeroth coordinate is 1,
and all other entries normalize the first row.  The division is
legal because equal 2×2 principal minors imply all off-diagonal
entries of `B` are nonzero. -/
def firstRowGauge {n : ℕ} (hn : 4 ≤ n) (p q : F)
    (B : Matrix (Fin n) (Fin n) F) (i : Fin n) : F :=
  if i = iZero hn then 1
  else B (iZero hn) i / exampleMatrix p q (iZero hn) i

/-- Nonvanishing of the normalizing gauge is deduced from
second-order principal minors, not assumed. -/
theorem firstRowGauge_ne_zero {n : ℕ} (hn : 4 ≤ n)
    (p q : F) (hp : p ≠ 0) (hq : q ≠ 0)
    (B : Matrix (Fin n) (Fin n) F)
    (hpm : SamePrincipalMinors (exampleMatrix p q) B)
    (i : Fin n) : firstRowGauge hn p q B i ≠ 0 := by
  by_cases hi : i = iZero hn
  · simp [firstRowGauge, hi]
  have h0i : iZero hn ≠ i := Ne.symm hi
  have ha : exampleMatrix p q (iZero hn) i ≠ 0 :=
    exampleMatrix_offdiag_ne_zero p q hp hq _ _ h0i
  have ha' : exampleMatrix p q i (iZero hn) ≠ 0 :=
    exampleMatrix_offdiag_ne_zero p q hp hq _ _ hi
  have hpair := pair_product_of_samePrincipalMinors hpm
    (exampleMatrix_diag p q) (iZero hn) i h0i
  have hb : B (iZero hn) i ≠ 0 := by
    intro hz
    have hzero : exampleMatrix p q (iZero hn) i *
        exampleMatrix p q i (iZero hn) = 0 := by
      rw [hpair, hz]
      ring
    exact (mul_ne_zero ha ha') hzero
  simp [firstRowGauge, hi, div_ne_zero hb ha]

/-- The gauge normalizes the first row. -/
theorem firstRowGauge_first_row {n : ℕ} (hn : 4 ≤ n)
    (p q : F) (hp : p ≠ 0) (hq : q ≠ 0)
    (B : Matrix (Fin n) (Fin n) F)
    (hpm : SamePrincipalMinors (exampleMatrix p q) B)
    (j : Fin n) :
    diagConj (firstRowGauge hn p q B) B (iZero hn) j =
      exampleMatrix p q (iZero hn) j := by
  by_cases hj : j = iZero hn
  · subst j
    have hdiag : B (iZero hn) (iZero hn) = 0 := by
      rw [← diagonal_eq_of_samePrincipalMinors hpm]
      exact exampleMatrix_diag p q _
    simp [diagConj, firstRowGauge, exampleMatrix_diag, hdiag]
  have h0j : iZero hn ≠ j := Ne.symm hj
  have ha : exampleMatrix p q (iZero hn) j ≠ 0 :=
    exampleMatrix_offdiag_ne_zero p q hp hq _ _ h0j
  have hb : B (iZero hn) j ≠ 0 := by
    have hpair := pair_product_of_samePrincipalMinors hpm
      (exampleMatrix_diag p q) (iZero hn) j h0j
    have ha' : exampleMatrix p q j (iZero hn) ≠ 0 :=
      exampleMatrix_offdiag_ne_zero p q hp hq _ _ hj
    intro hz
    have hh : exampleMatrix p q (iZero hn) j *
        exampleMatrix p q j (iZero hn) = 0 := by
      rw [hpair, hz]
      ring
    exact (mul_ne_zero ha ha') hh
  simp only [diagConj]
  have hg0 : firstRowGauge hn p q B (iZero hn) = 1 := by
    simp [firstRowGauge]
  have hgj : firstRowGauge hn p q B j =
      B (iZero hn) j / exampleMatrix p q (iZero hn) j := by
    simp [firstRowGauge, hj]
  rw [hg0, hgj]
  field_simp [ha, hb]

/-- The same gauge also normalizes the first column; this is
forced by the order-two principal-minor identities. -/
theorem firstRowGauge_first_col {n : ℕ} (hn : 4 ≤ n)
    (p q : F) (hp : p ≠ 0) (hq : q ≠ 0)
    (B : Matrix (Fin n) (Fin n) F)
    (hpm : SamePrincipalMinors (exampleMatrix p q) B)
    (i : Fin n) :
    diagConj (firstRowGauge hn p q B) B i (iZero hn) =
      exampleMatrix p q i (iZero hn) := by
  by_cases hi : i = iZero hn
  · subst i
    exact firstRowGauge_first_row hn p q hp hq B hpm _
  have h0i : iZero hn ≠ i := Ne.symm hi
  have ha : exampleMatrix p q (iZero hn) i ≠ 0 :=
    exampleMatrix_offdiag_ne_zero p q hp hq _ _ h0i
  have hpairs := pair_product_of_samePrincipalMinors hpm
    (exampleMatrix_diag p q) (iZero hn) i h0i
  have hgi : firstRowGauge hn p q B i =
      B (iZero hn) i / exampleMatrix p q (iZero hn) i := by
    simp [firstRowGauge, hi]
  have hg0 : firstRowGauge hn p q B (iZero hn) = 1 := by
    simp [firstRowGauge]
  calc
    diagConj (firstRowGauge hn p q B) B i (iZero hn) =
        (B (iZero hn) i / exampleMatrix p q (iZero hn) i) *
          B i (iZero hn) := by
      simp [diagConj, hgi, hg0]
    _ = (B (iZero hn) i * B i (iZero hn)) /
          exampleMatrix p q (iZero hn) i := by ring
    _ = (exampleMatrix p q (iZero hn) i *
          exampleMatrix p q i (iZero hn)) /
          exampleMatrix p q (iZero hn) i := by rw [hpairs]
    _ = exampleMatrix p q i (iZero hn) := by field_simp [ha]

/-! ## G. Main fiber theorem (the difficult assertion (iii)) -/

/-- The complete principal-minor fiber of the family has a single
diagonal-equivalence class.  Although only minors of sizes ≤ 3
are needed in the proof, the statement quantifies over **every**
principal minor via `SamePrincipalMinors`.

This is the assertion whose failure to prove would invalidate the
proposed counterexample; the earlier triangle obstruction alone is
not enough. -/
theorem samePrincipalMinors_implies_diagonallyEquivalent {n : ℕ}
    (hn : 4 ≤ n) (p q : F) (hp : p ≠ 0) (hq : q ≠ 0)
    (B : Matrix (Fin n) (Fin n) F)
    (hpm : SamePrincipalMinors (exampleMatrix p q) B) :
    DiagonallyEquivalent (exampleMatrix p q) B := by
  let A : Matrix (Fin n) (Fin n) F := exampleMatrix p q
  let d : Fin n → F := firstRowGauge hn p q B
  let C : Matrix (Fin n) (Fin n) F := diagConj d B
  have hd : ∀ i, d i ≠ 0 :=
    firstRowGauge_ne_zero hn p q hp hq B hpm
  have hCpm : SamePrincipalMinors A C :=
    samePrincipalMinors_normalize hpm d hd
  have hdata : NormalizedMinorData hn p q C :=
    normalizedMinorData_of_samePrincipalMinors hn p q C hCpm
      (firstRowGauge_first_row hn p q hp hq B hpm)
      (firstRowGauge_first_col hn p q hp hq B hpm)
  have hrecover : B = diagConj (fun i => (d i)⁻¹) C := by
    exact (diagConj_inverse d hd B).symm
  rcases normalized_fiber_classification hdata with hA | hAtranspose
  · left
    refine ⟨(fun i => (d i)⁻¹), (fun i => inv_ne_zero (hd i)), ?_⟩
    intro i j
    have hform : B = diagConj (fun i => (d i)⁻¹) A := by
      simpa [hA] using hrecover
    have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) hform
    simpa only [diagConj] using hentry
  · right
    obtain ⟨e, he, hCform⟩ := hAtranspose
    have hCeq : C = diagConj e Aᵀ := by
      funext i j
      exact hCform i j
    let t : Fin n → F := fun i => (d i)⁻¹ * e i
    have ht : ∀ i, t i ≠ 0 := fun i =>
      mul_ne_zero (inv_ne_zero (hd i)) (he i)
    have hBeq : B = diagConj t Aᵀ := by
      calc
        B = diagConj (fun i => (d i)⁻¹) C := hrecover
        _ = diagConj (fun i => (d i)⁻¹) (diagConj e Aᵀ) := by rw [hCeq]
        _ = diagConj t Aᵀ := diagConj_comp (fun i => (d i)⁻¹) e Aᵀ
    refine ⟨t, ht, ?_⟩
    intro i j
    have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) hBeq
    simpa only [diagConj] using hentry

/-! ## H. The two remaining geometric properties -/

/-- We use mathlib's field-independent indecomposability, rather
than its `Matrix.IsIrreducible` predicate for nonnegative matrices.
The latter requires an ordered field and is unsuitable here. -/
theorem exampleMatrix_indecomposable {n : ℕ}
    (hn : 4 ≤ n) (p q : F) (hp : p ≠ 0) (hq : q ≠ 0) :
    (exampleMatrix (n := n) p q).IsIndecomposable := by
  let A : Matrix (Fin n) (Fin n) F := exampleMatrix p q
  apply (Matrix.isIndecomposable_iff_blockTriangular_const (α := ℕ) A).2
  intro b hb
  refine ⟨b (iZero hn), ?_⟩
  funext i
  change b i = b (iZero hn)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hi : iZero hn ≠ i := by
      intro heq
      subst i
      exact hne rfl
    have hzero : A (iZero hn) i = 0 := hb hlt
    exact (exampleMatrix_offdiag_ne_zero p q hp hq _ _ hi) hzero
  · have hi : i ≠ iZero hn := by
      intro heq
      subst i
      exact hne rfl
    have hzero : A i (iZero hn) = 0 := hb hgt
    exact (exampleMatrix_offdiag_ne_zero p q hp hq _ _ hi) hzero

/-- A cut expressed as two rank-one cross-block factorizations.
Over a field this is the algebraic form of the two rank bounds in
(1.4); the two middle conditions force both sides to have size ≥ 2.

The present definition records the factorization directly, rather
than attempting to infer the desired rank from a mere determinant
calculation. -/
def HasFactorizedCut {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (X : Finset (Fin n)) : Prop :=
  2 ≤ X.card ∧ 2 ≤ (Xᶜ).card ∧
  ∃ (u v w z : Fin n → F),
    (∀ i ∈ X, ∀ j ∉ X, A i j = u i * v j) ∧
    (∀ i ∉ X, ∀ j ∈ X, A i j = w i * z j)

/-- The set corresponding to the cut `{1,2}` in the article. -/
def exceptionalCut {n : ℕ} (hn : 4 ≤ n) : Finset (Fin n) :=
  {iZero hn, iOne hn}

/-- Assertion (i), cut existence: both cross-blocks contain only
ones and thus factor as the outer product of two all-ones vectors. -/
theorem exampleMatrix_has_cut {n : ℕ}
    (hn : 4 ≤ n) (p q : F) :
    HasFactorizedCut (exampleMatrix p q) (exceptionalCut hn) := by
  have hz : iZero hn ≠ iOne hn := zero_ne_one hn
  have hcard : (exceptionalCut hn).card = 2 := by
    simp [exceptionalCut, hz]
  have hcompl : ((exceptionalCut hn)ᶜ).card = n - 2 := by
    simp [Finset.card_compl, hcard]
  have hsize : 2 ≤ ((exceptionalCut hn)ᶜ).card := by
    rw [hcompl]
    omega
  refine ⟨by omega, hsize, (fun _ => 1), (fun _ => 1),
    (fun _ => 1), (fun _ => 1), ?_, ?_⟩
  · intro i hi j hj
    have hi' : i = iZero hn ∨ i = iOne hn := by
      simpa [exceptionalCut] using hi
    have hj0 : j.val ≠ 0 := by
      intro h0
      apply hj
      have he : j = iZero hn := Fin.ext (by simpa [iZero] using h0)
      simp [exceptionalCut, he]
    have hj1 : j.val ≠ 1 := by
      intro h1
      apply hj
      have he : j = iOne hn := Fin.ext (by simpa [iOne] using h1)
      simp [exceptionalCut, he]
    have hjtail : 2 ≤ j.val := by omega
    rcases hi' with h | h
    · subst i
      simpa using (example_first_tail hn p q j hjtail).1
    · subst i
      simpa using (example_first_tail hn p q j hjtail).2.2.1
  · intro i hi j hj
    have hj' : j = iZero hn ∨ j = iOne hn := by
      simpa [exceptionalCut] using hj
    have hi0 : i.val ≠ 0 := by
      intro h0
      apply hi
      have he : i = iZero hn := Fin.ext (by simpa [iZero] using h0)
      simp [exceptionalCut, he]
    have hi1 : i.val ≠ 1 := by
      intro h1
      apply hi
      have he : i = iOne hn := Fin.ext (by simpa [iOne] using h1)
      simp [exceptionalCut, he]
    have hitail : 2 ≤ i.val := by omega
    rcases hj' with h | h
    · subst j
      simpa using (example_first_tail hn p q i hitail).2.1
    · subst j
      simpa using (example_first_tail hn p q i hitail).2.2.2

/-- The paper's literal rank-bound definition of a cut.
The cross-blocks are indexed by the two subtype index sets. -/
def HasCutRanks {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (X : Finset (Fin n)) : Prop :=
  2 ≤ X.card ∧ 2 ≤ (Xᶜ).card ∧
  (A.submatrix
      (fun i : {i : Fin n // i ∈ X} => i.1)
      (fun j : {j : Fin n // j ∉ X} => j.1)).rank ≤ 1 ∧
  (A.submatrix
      (fun i : {i : Fin n // i ∉ X} => i.1)
      (fun j : {j : Fin n // j ∈ X} => j.1)).rank ≤ 1

/-- An explicit outer-product factorization proves the two rank
inequalities.  Here we use `Matrix.rank_vecMulVec_le`, which is valid
over any field and does not require a positivity hypothesis. -/
theorem hasCutRanks_of_factorizedCut {n : ℕ}
    {A : Matrix (Fin n) (Fin n) F} {X : Finset (Fin n)}
    (h : HasFactorizedCut A X) : HasCutRanks A X := by
  obtain ⟨hX, hY, u, v, w, z, hforward, hreverse⟩ := h
  refine ⟨hX, hY, ?_, ?_⟩
  · have hM :
        A.submatrix
          (fun i : {i : Fin n // i ∈ X} => i.1)
          (fun j : {j : Fin n // j ∉ X} => j.1) =
        Matrix.vecMulVec
          (fun i : {i : Fin n // i ∈ X} => u i.1)
          (fun j : {j : Fin n // j ∉ X} => v j.1) := by
      ext i j
      simpa [Matrix.vecMulVec_apply] using
        (hforward i.1 i.2 j.1 j.2)
    rw [hM]
    exact Matrix.rank_vecMulVec_le _ _
  · have hM :
        A.submatrix
          (fun i : {i : Fin n // i ∉ X} => i.1)
          (fun j : {j : Fin n // j ∈ X} => j.1) =
        Matrix.vecMulVec
          (fun i : {i : Fin n // i ∉ X} => w i.1)
          (fun j : {j : Fin n // j ∈ X} => z j.1) := by
      ext i j
      simpa [Matrix.vecMulVec_apply] using
        (hreverse i.1 i.2 j.1 j.2)
    rw [hM]
    exact Matrix.rank_vecMulVec_le _ _

/-- Assertion (i) with the **literal matrix-rank definition**
from equation (1.4), not just a factorizable-cut proxy. -/
theorem exampleMatrix_has_cut_ranks {n : ℕ}
    (hn : 4 ≤ n) (p q : F) :
    HasCutRanks (exampleMatrix p q) (exceptionalCut hn) :=
  hasCutRanks_of_factorizedCut (exampleMatrix_has_cut hn p q)

/-! ## I. Exact fiber equality and the counterexample theorem -/

/-- Diagonal equivalence is sufficient for principal-minor equality.
This includes transposition explicitly, as required by the article. -/
theorem samePrincipalMinors_of_diagonallyEquivalent {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F}
    (h : DiagonallyEquivalent A B) : SamePrincipalMinors A B := by
  rcases h with h | h
  · obtain ⟨d, hd, hB⟩ := h
    have heq : B = diagConj d A := by
      funext i j
      exact hB i j
    rw [heq]
    exact samePrincipalMinors_diagConj d hd A
  · obtain ⟨d, hd, hB⟩ := h
    have heq : B = diagConj d Aᵀ := by
      funext i j
      exact hB i j
    rw [heq]
    exact samePrincipalMinors_trans
      (samePrincipalMinors_transpose A)
      (samePrincipalMinors_diagConj d hd Aᵀ)

/-- The entire fiber is exactly the diagonal-equivalence class;
in particular, there are no hidden extra fiber points in order 4
or higher. -/
theorem theorem_4_1_full_fiber {n : ℕ} (hn : 4 ≤ n)
    (p q : F) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∀ B : Matrix (Fin n) (Fin n) F,
      SamePrincipalMinors (exampleMatrix p q) B ↔
        DiagonallyEquivalent (exampleMatrix p q) B := by
  intro B
  exact ⟨samePrincipalMinors_implies_diagonallyEquivalent hn p q hp hq B,
    samePrincipalMinors_of_diagonallyEquivalent⟩

/-- Theorem 4.1 of the correction note, as a field-independent
counterexample family.  The cut condition is expressed by the actual
two cross-block rank inequalities, proved through explicit factorizations. -/
theorem theorem_4_1_counterexample_family {n : ℕ}
    (hn : 4 ≤ n) (p q : F)
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p ≠ q) :
    (exampleMatrix (n := n) p q).IsIndecomposable ∧
    HasCutRanks (exampleMatrix p q) (exceptionalCut hn) ∧
    (¬ ∃ S : Matrix (Fin n) (Fin n) F,
      DiagonallySimilar (exampleMatrix p q) S ∧ S = Sᵀ) ∧
    (∀ B : Matrix (Fin n) (Fin n) F,
      SamePrincipalMinors (exampleMatrix p q) B ↔
        DiagonallyEquivalent (exampleMatrix p q) B) := by
  exact ⟨exampleMatrix_indecomposable hn p q hp hq,
    exampleMatrix_has_cut_ranks hn p q,
    not_diagonally_symmetrizable hn p q hpq,
    theorem_4_1_full_fiber hn p q hp hq⟩

/-- The explicit `4 × 4` rational counterexample of Example 4.2:

    [0 2 1 1]
    [3 0 1 1]
    [1 1 0 1]
    [1 1 1 0]

It has a cut, is indecomposable and not symmetrizable, and its
principal-minor fiber contains exactly one diagonal-equivalence class. -/
theorem rational_counterexample_4x4 :
    (exampleMatrix (n := 4) (2 : ℚ) 3).IsIndecomposable ∧
    HasCutRanks (exampleMatrix (n := 4) (2 : ℚ) 3)
      (exceptionalCut (by omega : 4 ≤ 4)) ∧
    (¬ ∃ S : Matrix (Fin 4) (Fin 4) ℚ,
      DiagonallySimilar (exampleMatrix (2 : ℚ) 3) S ∧ S = Sᵀ) ∧
    (∀ B : Matrix (Fin 4) (Fin 4) ℚ,
      SamePrincipalMinors (exampleMatrix (2 : ℚ) 3) B ↔
        DiagonallyEquivalent (exampleMatrix (2 : ℚ) 3) B) := by
  exact theorem_4_1_counterexample_family (n := 4)
    (by omega) (2 : ℚ) 3 (by norm_num) (by norm_num) (by norm_num)

/-!
## Verification boundary

Everything above is written as a concrete Lean proof term/tactic script.
No theorem is *assumed* merely because it is desired: the normalization
identities are obtained from 1×1, 2×2 and 3×3 determinant equalities,
and all principal-minor preservation is derived from determinant laws.

Nevertheless this file has not been compiled against Lean/mathlib in the
present environment.  In particular, `theorem_4_1_counterexample_family`
and `rational_counterexample_4x4` MUST NOT be represented as kernel-accepted
until a complete `lake env lean` run passes, and diagnostics are corrected.
-/

end
end DetPoly.Theorem41
