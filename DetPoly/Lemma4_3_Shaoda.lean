import Mathlib

/-!
# Lemma 4.3 — Shaoda Ji

Let A be an n × n irreducible matrix over a field F, with n ≥ 4.
Suppose X is a cut.

Put

    M = A + diag(x₁, ..., xₙ),
    G = adj(M).

For i ∈ X and j ∉ X, we prove that there are polynomials aᵢ and bⱼ such that

    Gᵢⱼ = (-1)^i aᵢ bⱼ,

with

    aᵢ ∈ F[xₖ : k ∈ X \ {i}],
    bⱼ ∈ F[xₖ : k ∈ Xᶜ \ {j}],

and both factors are nonzero.

----------------------------------------------------------------------
Formalization strategy
----------------------------------------------------------------------

The handwritten proof writes the upper-right cut block as

    u vᵀ

and then factors the corresponding block of the adjugate over the
fraction field.

For Lean it is cleaner to prove a stronger fraction-free identity.

For

             [ P     u vᵀ ]
    M =      [             ],
             [ L       Q   ]

we prove

    adj(M)_(i,j)
      =
    - det(P with column i replaced by u)
      * det(Q with row j replaced by v).

This is proved by determinant-preserving row and column shears.

Consequently:

* the polynomial factorization is constructed explicitly;
* no fraction field is required;
* no gcd/common-factor cancellation is required;
* replacing column i removes xᵢ from the first factor;
* replacing row j removes xⱼ from the second factor.

Irreducibility is used only at the final step through Lemma 4.2.
-/

open scoped BigOperators

namespace Lemma43Shaoda

noncomputable section

variable {F : Type*} [Field F]

/-!
## 1. Polynomial ring
-/

abbrev Poly
    (F : Type*)
    [CommSemiring F]
    (n : ℕ) :=
  MvPolynomial (Fin n) F

def polynomialMatrix
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (Poly F n) :=
  A.map MvPolynomial.C

def genericShift
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (Poly F n) :=
  polynomialMatrix A +
    Matrix.diagonal
      (fun i => MvPolynomial.X i)

def genericAdjugate
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (Poly F n) :=
  (genericShift A).adjugate

/-!
`UsesOnly p S` means that every variable occurring in p belongs to S.
-/

def UsesOnly
    {n : ℕ}
    (p : Poly F n)
    (S : Finset (Fin n)) : Prop :=
  p.vars ⊆ S

/-!
## 2. The two sides of a cut
-/

abbrev InCut
    {n : ℕ}
    (X : Finset (Fin n)) :=
  {i : Fin n // i ∈ X}

abbrev OutCut
    {n : ℕ}
    (X : Finset (Fin n)) :=
  {i : Fin n // i ∉ X}

def splitEquiv
    {n : ℕ}
    (X : Finset (Fin n)) :
    InCut X ⊕ OutCut X ≃ Fin n :=
  Equiv.sumCompl
    (fun i : Fin n => i ∈ X)

def cutBlock11
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) :
    Matrix (InCut X) (InCut X) F :=
  A.submatrix Subtype.val Subtype.val

def cutBlock12
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) :
    Matrix (InCut X) (OutCut X) F :=
  A.submatrix Subtype.val Subtype.val

def cutBlock21
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) :
    Matrix (OutCut X) (InCut X) F :=
  A.submatrix Subtype.val Subtype.val

def cutBlock22
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) :
    Matrix (OutCut X) (OutCut X) F :=
  A.submatrix Subtype.val Subtype.val

/-!
A cut has at least two indices on both sides and rank-one cross blocks.
-/

def IsCut
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) : Prop :=
  2 ≤ Fintype.card (InCut X) ∧
  2 ≤ Fintype.card (OutCut X) ∧
  (cutBlock12 A X).rank = 1 ∧
  (cutBlock21 A X).rank = 1

/-!
## 3. Irreducibility and Lemma 4.2
-/

def MatrixIrreducible
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ S : Finset (Fin n),
    S.Nonempty →
    S ≠ Finset.univ →
    ∃ i, i ∈ S ∧
      ∃ j, j ∉ S ∧
        A i j ≠ 0

def Lemma42Statement
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j : Fin n,
    genericAdjugate A i j ≠ 0

/-!
## 4. A rank-one matrix is an outer product

If B has rank one, then B = u vᵀ.

Let W be the span of the columns. Since finrank W = 1, W is nontrivial.
We obtain a nonzero vector u₀ explicitly from the `Nontrivial W`
instance without introducing a `FiniteDimensional` assumption.
-/

lemma exists_vecMulVec_of_rank_eq_one
    {m k : Type*}
    [Fintype k]
    (B : Matrix m k F)
    (hB : B.rank = 1) :
    ∃ u : m → F, ∃ v : k → F,
      B = Matrix.vecMulVec u v := by
  classical
  let W : Submodule F (m → F) :=
    Submodule.span F (Set.range B.col)
  have hW :
      Module.finrank F W = 1 := by
    change
      Module.finrank F
          ↥(Submodule.span F (Set.range B.col)) =
        1
    rw [← Matrix.rank_eq_finrank_span_cols]
    exact hB
  have hNontrivial :
      Nontrivial W :=
    Module.nontrivial_of_finrank_eq_succ hW
  obtain ⟨u₀, hu₀⟩ :
      ∃ u₀ : W, u₀ ≠ 0 :=
    @exists_ne W hNontrivial 0
  have hcol (j : k) :
      B.col j ∈ W := by
    apply Submodule.subset_span
    exact Set.mem_range_self j
  have hscalar (j : k) :
      ∃ c : F,
        c • u₀ =
          (⟨B.col j, hcol j⟩ : W) := by
    exact
      exists_smul_eq_of_finrank_eq_one
        hW
        hu₀
        (⟨B.col j, hcol j⟩ : W)
  choose v hv using hscalar
  let u : m → F :=
    fun i => (u₀ : m → F) i
  refine ⟨u, v, ?_⟩
  funext i j
  have hij :=
    congrArg
      (fun w : W => (w : m → F) i)
      (hv j)
  simpa [u, Matrix.vecMulVec_apply, mul_comm] using hij.symm

/-!
## 5. Determinant-preserving row and column shears
-/

def rowShear
    {ι R : Type*}
    [CommRing R]
    (M : Matrix ι ι R)
    (c : ι → R)
    (k : ι) :
    Matrix ι ι R :=
  fun i j =>
    M i j + c i * M k j

lemma det_rowShear
    {ι R : Type*}
    [Fintype ι]
    [DecidableEq ι]
    [CommRing R]
    (M : Matrix ι ι R)
    (c : ι → R)
    (k : ι)
    (hk : c k = 0) :
    (rowShear M c k).det =
      M.det := by
  exact
    Matrix.det_eq_of_forall_row_eq_smul_add_const
      (A := rowShear M c k)
      (B := M)
      c
      k
      hk
      (by
        intro i j
        rfl)

def colShear
    {ι R : Type*}
    [CommRing R]
    (M : Matrix ι ι R)
    (c : ι → R)
    (k : ι) :
    Matrix ι ι R :=
  fun i j =>
    M i j + c j * M i k

lemma det_colShear
    {ι R : Type*}
    [Fintype ι]
    [DecidableEq ι]
    [CommRing R]
    (M : Matrix ι ι R)
    (c : ι → R)
    (k : ι)
    (hk : c k = 0) :
    (colShear M c k).det =
      M.det := by
  have hT :
      (colShear M c k).transpose =
        rowShear M.transpose c k := by
    rfl
  calc
    (colShear M c k).det
        =
        (colShear M c k).transpose.det := by
      exact
        (Matrix.det_transpose
          (colShear M c k)).symm
    _ =
        (rowShear M.transpose c k).det := by
      rw [hT]
    _ =
        M.transpose.det := by
      exact
        det_rowShear
          M.transpose c k hk
    _ =
        M.det := by
      exact Matrix.det_transpose M

/-!
## 6. Fraction-free factorization of an off-diagonal adjugate entry

For

             [ P     u vᵀ ]
    M =      [             ],
             [ L       Q   ]

we prove

    adj(M)_(i,j)
      =
    -det(P[i ← u]) det(Q[j ← v]).
-/

lemma adjugate_fromBlocks_vecMulVec_apply₁₂
    {I J R : Type*}
    [Fintype I]
    [DecidableEq I]
    [Fintype J]
    [DecidableEq J]
    [CommRing R]
    (P : Matrix I I R)
    (u : I → R)
    (v : J → R)
    (L : Matrix J I R)
    (Q : Matrix J J R)
    (i : I)
    (j : J) :
    (Matrix.fromBlocks
        P
        (Matrix.vecMulVec u v)
        L
        Q).adjugate
        (Sum.inl i)
        (Sum.inr j)
      =
    - (P.updateCol i u).det *
        (Q.updateRow j v).det := by
  classical
  let M : Matrix (I ⊕ J) (I ⊕ J) R :=
    Matrix.fromBlocks
      P
      (Matrix.vecMulVec u v)
      L
      Q
  let pivotRow : I ⊕ J :=
    Sum.inr j
  let pivotCol : I ⊕ J :=
    Sum.inl i
  let e : I ⊕ J → R :=
    Pi.single pivotCol 1
  let N₀ : Matrix (I ⊕ J) (I ⊕ J) R :=
    M.updateRow pivotRow e
  /-
  Clear the pivot column below the upper-left block.
  -/
  let c₁ : I ⊕ J → R :=
    Sum.elim
      (fun _ => 0)
      (fun r =>
        if r = j then 0 else -L r i)
  let N₁ :=
    rowShear N₀ c₁ pivotRow
  have hc₁ :
      c₁ pivotRow = 0 := by
    simp [c₁, pivotRow]
  have hdet₁ :
      N₁.det = N₀.det := by
    exact
      det_rowShear
        N₀ c₁ pivotRow hc₁
  /-
  Replace column i of P by u.
  -/
  let c₂ : I ⊕ J → R :=
    Sum.elim
      (fun r => u r - P r i)
      (fun _ => 0)
  let N₂ :=
    rowShear N₁ c₂ pivotRow
  have hc₂ :
      c₂ pivotRow = 0 := by
    simp [c₂, pivotRow]
  have hdet₂ :
      N₂.det = N₁.det := by
    exact
      det_rowShear
        N₁ c₂ pivotRow hc₂
  /-
  Clear the upper-right rank-one block.
  -/
  let d : I ⊕ J → R :=
    Sum.elim
      (fun _ => 0)
      (fun s => -v s)
  let N₃ :=
    colShear N₂ d pivotCol
  have hd :
      d pivotCol = 0 := by
    simp [d, pivotCol]
  have hdet₃ :
      N₃.det = N₂.det := by
    exact
      det_colShear
        N₂ d pivotCol hd
  /-
  Identify the upper-left block.
  -/
  have h₁₁ :
      N₃.toBlocks₁₁ =
        P.updateCol i u := by
    funext a b
    change
      N₃ (Sum.inl a) (Sum.inl b) =
        (P.updateCol i u) a b
    by_cases hb : b = i
    · subst b
      simp [
        N₃, N₂, N₁, N₀, M,
        colShear, rowShear,
        c₁, c₂, d,
        pivotRow, pivotCol, e,
        Matrix.updateRow_apply
      ]
    · simp [
        N₃, N₂, N₁, N₀, M,
        colShear, rowShear,
        c₁, c₂, d,
        pivotRow, pivotCol, e,
        Matrix.updateRow_apply,
        hb
      ]
  /-
  Identify the zero upper-right block.
  -/
  have h₁₂ :
      N₃.toBlocks₁₂ = 0 := by
    funext a b
    change
      N₃ (Sum.inl a) (Sum.inr b) = 0
    simp [
      N₃, N₂, N₁, N₀, M,
      colShear, rowShear,
      c₁, c₂, d,
      pivotRow, pivotCol, e,
      Matrix.updateRow_apply,
      Matrix.vecMulVec_apply
    ]
    ring
  /-
  Identify the lower-right block.
  -/
  have h₂₂ :
      N₃.toBlocks₂₂ =
        Q.updateRow j (-v) := by
    funext a b
    change
      N₃ (Sum.inr a) (Sum.inr b) =
        (Q.updateRow j (-v)) a b
    by_cases ha : a = j
    · subst a
      simp [
        N₃, N₂, N₁, N₀, M,
        colShear, rowShear,
        c₁, c₂, d,
        pivotRow, pivotCol, e,
        Matrix.updateRow_apply
      ]
    · simp [
        N₃, N₂, N₁, N₀, M,
        colShear, rowShear,
        c₁, c₂, d,
        pivotRow, pivotCol, e,
        Matrix.updateRow_apply,
        ha
      ]
  /-
  The resulting matrix is block lower triangular.
  -/
  have hN₃ :
      N₃ =
        Matrix.fromBlocks
          (P.updateCol i u)
          0
          N₃.toBlocks₂₁
          (Q.updateRow j (-v)) := by
    apply (Matrix.ext_iff_blocks).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h₁₁
    · simpa using h₁₂
    · simp
    · simpa using h₂₂
  have hdetBlock :
      N₃.det =
        (P.updateCol i u).det *
          (Q.updateRow j (-v)).det := by
    rw [hN₃]
    simp
  /-
  Negating the replacement row changes the determinant sign.
  -/
  have hneg :
      (Q.updateRow j (-v)).det =
        -(Q.updateRow j v).det := by
    calc
      (Q.updateRow j (-v)).det
          =
          Q.transpose.cramer (-v) j := by
        symm
        exact
          Matrix.cramer_transpose_apply
            Q (-v) j
      _ =
          -(Q.transpose.cramer v j) := by
        simp
      _ =
          -(Q.updateRow j v).det := by
        rw [Matrix.cramer_transpose_apply]
  calc
    (Matrix.fromBlocks
        P
        (Matrix.vecMulVec u v)
        L
        Q).adjugate
        (Sum.inl i)
        (Sum.inr j)
        =
        N₀.det := by
      simpa [
        M, N₀,
        pivotRow, pivotCol, e
      ] using
        Matrix.adjugate_apply
          M
          pivotCol
          pivotRow
    _ =
        N₁.det := by
      exact hdet₁.symm
    _ =
        N₂.det := by
      exact hdet₂.symm
    _ =
        N₃.det := by
      exact hdet₃.symm
    _ =
        (P.updateCol i u).det *
          (Q.updateRow j (-v)).det :=
      hdetBlock
    _ =
        - (P.updateCol i u).det *
          (Q.updateRow j v).det := by
      rw [hneg]
      ring

/-!
## 7. Split the generic matrix according to X
-/

def splitGeneric
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) :
    Matrix
      (InCut X ⊕ OutCut X)
      (InCut X ⊕ OutCut X)
      (Poly F n) :=
  (genericShift A).submatrix
    (splitEquiv X)
    (splitEquiv X)

lemma splitGeneric_toBlocks₁₂
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) :
    (splitGeneric A X).toBlocks₁₂ =
      (cutBlock12 A X).map
        MvPolynomial.C := by
  classical
  funext i j
  have hij :
      (i.1 : Fin n) ≠ j.1 := by
    intro h
    apply j.property
    simpa [h] using i.property
  change
    genericShift A i.1 j.1 =
      MvPolynomial.C (A i.1 j.1)
  simp [
    genericShift,
    polynomialMatrix,
    hij
  ]

lemma splitGeneric₁₁_apply
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n))
    (i j : InCut X) :
    (splitGeneric A X).toBlocks₁₁ i j =
      MvPolynomial.C (A i.1 j.1) +
        if i = j
        then MvPolynomial.X i.1
        else 0 := by
  classical
  change
    genericShift A i.1 j.1 =
      MvPolynomial.C (A i.1 j.1) +
        if i = j
        then MvPolynomial.X i.1
        else 0
  by_cases h : i = j
  · subst j
    simp [
      genericShift,
      polynomialMatrix
    ]
  · have hval :
        (i.1 : Fin n) ≠ j.1 := by
      intro h'
      apply h
      exact Subtype.ext h'
    simp [
      genericShift,
      polynomialMatrix,
      h,
      hval
    ]

lemma vars_splitGeneric₁₁_subset
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n))
    (i j : InCut X) :
    ((splitGeneric A X).toBlocks₁₁ i j).vars
      ⊆ {j.1} := by
  rw [splitGeneric₁₁_apply A X i j]
  intro z hz
  have h :=
    MvPolynomial.vars_add_subset
      (MvPolynomial.C (A i.1 j.1))
      (if i = j
       then MvPolynomial.X i.1
       else 0)
      hz
  by_cases hij : i = j
  · subst j
    simpa using h
  · simp [hij] at h

lemma splitGeneric₂₂_apply
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n))
    (i j : OutCut X) :
    (splitGeneric A X).toBlocks₂₂ i j =
      MvPolynomial.C (A i.1 j.1) +
        if i = j
        then MvPolynomial.X i.1
        else 0 := by
  classical
  change
    genericShift A i.1 j.1 =
      MvPolynomial.C (A i.1 j.1) +
        if i = j
        then MvPolynomial.X i.1
        else 0
  by_cases h : i = j
  · subst j
    simp [
      genericShift,
      polynomialMatrix
    ]
  · have hval :
        (i.1 : Fin n) ≠ j.1 := by
      intro h'
      apply h
      exact Subtype.ext h'
    simp [
      genericShift,
      polynomialMatrix,
      h,
      hval
    ]

lemma vars_splitGeneric₂₂_subset
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n))
    (i j : OutCut X) :
    ((splitGeneric A X).toBlocks₂₂ i j).vars
      ⊆ {i.1} := by
  rw [splitGeneric₂₂_apply A X i j]
  intro z hz
  have h :=
    MvPolynomial.vars_add_subset
      (MvPolynomial.C (A i.1 j.1))
      (if i = j
       then MvPolynomial.X i.1
       else 0)
      hz
  by_cases hij : i = j
  · subst j
    simpa using h
  · simp [hij] at h

/-!
## 8. Variables in a determinant

If every matrix entry uses only variables in S, so does the determinant.
-/

lemma vars_det_subset
    {ι σ : Type*}
    [Fintype ι]
    [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ F))
    (S : Finset σ)
    (hM :
      ∀ i j,
        (M i j).vars ⊆ S) :
    M.det.vars ⊆ S := by
  classical
  let T :
      Subalgebra F (MvPolynomial σ F) :=
    MvPolynomial.supported
      F
      (↑S : Set σ)
  let N : Matrix ι ι T :=
    fun i j =>
      ⟨M i j,
        (MvPolynomial.mem_supported).2
          (by
            intro z hz
            exact hM i j hz)⟩
  have hmap :
      T.val.mapMatrix N = M := by
    funext i j
    rfl
  have hdet :
      T.val N.det = M.det := by
    rw [AlgHom.map_det]
    rw [hmap]
  have hmem :
      M.det ∈ T := by
    rw [← hdet]
    exact (N.det).property
  have hvars :
      ↑(M.det.vars) ⊆
        (↑S : Set σ) :=
    (MvPolynomial.mem_supported).1 hmem
  intro z hz
  exact hvars hz

/-!
## 9. The cofactor sign
-/

def cofactorSign
    {n : ℕ}
    (i : Fin n) :
    Poly F n :=
  MvPolynomial.C
    ((-1 : F) ^ (i.val + 1))

lemma cofactorSign_mul_self
    {n : ℕ}
    (i : Fin n) :
    cofactorSign (F := F) i *
        cofactorSign (F := F) i =
      1 := by
  change
    MvPolynomial.C
        ((-1 : F) ^ (i.val + 1)) *
      MvPolynomial.C
        ((-1 : F) ^ (i.val + 1))
      =
    1
  rw [← MvPolynomial.C_mul]
  rw [← pow_add]
  rw [
    show
      (i.val + 1) + (i.val + 1) =
        2 * (i.val + 1) by
      omega
  ]
  rw [pow_mul]
  simp

/-!
## 10. The polynomial factorization
-/

def CutFactorizationCore
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) : Prop :=
  ∃ a b : Fin n → Poly F n,
    (∀ i, i ∈ X →
      ∀ j, j ∉ X →
        genericAdjugate A i j =
          cofactorSign i *
            a i *
            b j) ∧
    (∀ i, i ∈ X →
      UsesOnly
        (a i)
        (X.erase i)) ∧
    (∀ j, j ∉ X →
      UsesOnly
        (b j)
        (Xᶜ.erase j))

/-!
## 11. Derive the factorization directly from `IsCut`
-/

theorem cutFactorization_of_isCut
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n))
    (hcut : IsCut A X) :
    CutFactorizationCore A X := by
  classical
  /-
  Rank one gives an outer-product decomposition.
  -/
  obtain ⟨uF, vF, huvF⟩ :=
    exists_vecMulVec_of_rank_eq_one
      (B := cutBlock12 A X)
      hcut.2.2.1
  /-
  Regard these as constant polynomial vectors.
  -/
  let u : InCut X → Poly F n :=
    fun i =>
      MvPolynomial.C (uF i)
  let v : OutCut X → Poly F n :=
    fun j =>
      MvPolynomial.C (vF j)
  /-
  Split the generic matrix.
  -/
  let M :=
    splitGeneric A X
  let P :=
    M.toBlocks₁₁
  let B :=
    M.toBlocks₁₂
  let L :=
    M.toBlocks₂₁
  let Q :=
    M.toBlocks₂₂
  /-
  The upper-right block is exactly u vᵀ.
  -/
  have hB :
      B =
        Matrix.vecMulVec u v := by
    rw [
      show
        B =
          (cutBlock12 A X).map
            MvPolynomial.C by
          simpa [B, M] using
            splitGeneric_toBlocks₁₂
              A X
    ]
    rw [huvF]
    funext i j
    simp [
      u,
      v,
      Matrix.vecMulVec_apply
    ]
  /-
  Reconstruct M from its blocks.
  -/
  have hM :
      M =
        Matrix.fromBlocks
          P
          (Matrix.vecMulVec u v)
          L
          Q := by
    have h :=
      (Matrix.fromBlocks_toBlocks M).symm
    change
      M =
        Matrix.fromBlocks
          P B L Q
      at h
    rw [hB] at h
    exact h
  /-
  Define the two determinant factors.
  -/
  let r : InCut X → Poly F n :=
    fun i =>
      (P.updateCol i u).det
  let s : OutCut X → Poly F n :=
    fun j =>
      (Q.updateRow j v).det
  /-
  Apply the fraction-free adjugate identity.
  -/
  have hlocal
      (i : InCut X)
      (j : OutCut X) :
      M.adjugate
          (Sum.inl i)
          (Sum.inr j)
        =
      -r i * s j := by
    rw [hM]
    simpa [r, s] using
      adjugate_fromBlocks_vecMulVec_apply₁₂
        P u v L Q i j
  /-
  Adjugation commutes with simultaneous reindexing.
  -/
  have hadj :
      M.adjugate =
        (genericAdjugate A).submatrix
          (splitEquiv X)
          (splitEquiv X) := by
    simp [
      M,
      splitGeneric,
      genericAdjugate
    ]
  /-
  Return to the original Fin n indices.
  -/
  have hG
      (i : Fin n)
      (hi : i ∈ X)
      (j : Fin n)
      (hj : j ∉ X) :
      genericAdjugate A i j =
        -r ⟨i, hi⟩ *
          s ⟨j, hj⟩ := by
    have h :=
      hlocal
        (⟨i, hi⟩ : InCut X)
        (⟨j, hj⟩ : OutCut X)
    rw [hadj] at h
    simpa [splitEquiv] using h
  /-
  The first determinant factor uses only variables in X \ {i}.
  -/
  have hrVars
      (i : InCut X) :
      UsesOnly
        (r i)
        (X.erase i.1) := by
    apply
      vars_det_subset
        (M := P.updateCol i u)
        (S := X.erase i.1)
    intro p q z hz
    by_cases hq : q = i
    · subst q
      simp [u] at hz
    · have hzP :
          z ∈ (P p q).vars := by
        simpa [
          Matrix.updateCol_apply,
          hq
        ] using hz
      have hzq :
          z ∈
            ({q.1} :
              Finset (Fin n)) :=
        vars_splitGeneric₁₁_subset
          A X p q hzP
      have hzEq :
          z = q.1 := by
        simpa using hzq
      subst z
      have hval :
          (q.1 : Fin n) ≠ i.1 := by
        intro hval
        apply hq
        exact Subtype.ext hval
      simp [
        hval,
        q.property
      ]
  /-
  The second determinant factor uses only variables in Xᶜ \ {j}.
  -/
  have hsVars
      (j : OutCut X) :
      UsesOnly
        (s j)
        (Xᶜ.erase j.1) := by
    apply
      vars_det_subset
        (M := Q.updateRow j v)
        (S := Xᶜ.erase j.1)
    intro p q z hz
    by_cases hp : p = j
    · subst p
      simp [
        Matrix.updateRow_apply,
        v
      ] at hz
    · have hzQ :
          z ∈ (Q p q).vars := by
        simpa [
          Matrix.updateRow_apply,
          hp
        ] using hz
      have hzp :
          z ∈
            ({p.1} :
              Finset (Fin n)) :=
        vars_splitGeneric₂₂_subset
          A X p q hzQ
      have hzEq :
          z = p.1 := by
        simpa using hzp
      subst z
      have hval :
          (p.1 : Fin n) ≠ j.1 := by
        intro hval
        apply hp
        exact Subtype.ext hval
      simp [
        hval,
        p.property
      ]
  /-
  Absorb the prescribed sign into the first factor.
  -/
  let a : Fin n → Poly F n :=
    fun i =>
      if hi : i ∈ X then
        -(cofactorSign i *
          r ⟨i, hi⟩)
      else
        0
  let b : Fin n → Poly F n :=
    fun j =>
      if hj : j ∉ X then
        s ⟨j, hj⟩
      else
        0
  refine
    ⟨a, b, ?_, ?_, ?_⟩
  /-
  Prove the factorization.
  -/
  · intro i hi j hj
    have hg :=
      hG i hi j hj
    have hsign :=
      cofactorSign_mul_self
        (F := F) i
    have ha :
        a i =
          -(cofactorSign i *
            r ⟨i, hi⟩) := by
      simp [a, hi]
    have hb :
        b j =
          s ⟨j, hj⟩ := by
      simp [b, hj]
    rw [ha, hb]
    calc
      genericAdjugate A i j
          =
          -r ⟨i, hi⟩ *
            s ⟨j, hj⟩ :=
        hg
      _ =
          -(1 : Poly F n) *
            r ⟨i, hi⟩ *
            s ⟨j, hj⟩ := by
        ring
      _ =
          -(cofactorSign i *
              cofactorSign i) *
            r ⟨i, hi⟩ *
            s ⟨j, hj⟩ := by
        rw [hsign]
      _ =
          cofactorSign i *
            (-(cofactorSign i *
              r ⟨i, hi⟩)) *
            s ⟨j, hj⟩ := by
        ring
  /-
  Prove the variable restriction for a_i.
  -/
  · intro i hi
    have hr :=
      hrVars
        (⟨i, hi⟩ : InCut X)
    intro z hz
    have hzProd :
        z ∈
          (cofactorSign i *
            r ⟨i, hi⟩).vars := by
      simpa [a, hi] using hz
    have hmul :=
      MvPolynomial.vars_mul
        (cofactorSign i)
        (r ⟨i, hi⟩)
        hzProd
    rcases
        Finset.mem_union.mp hmul
      with hs | hrz
    · have hsEmpty :
          z ∈
            (∅ : Finset (Fin n)) := by
        simpa only [
          cofactorSign,
          MvPolynomial.vars_C
        ] using hs
      exact
        False.elim
          ((Finset.notMem_empty z)
            hsEmpty)
    · exact hr hrz
  /-
  Prove the variable restriction for b_j.
  -/
  · intro j hj
    have hs :=
      hsVars
        (⟨j, hj⟩ : OutCut X)
    simpa [b, hj] using hs

/-!
## 12. Full statement of Lemma 4.3
-/

def Lemma43Statement
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) : Prop :=
  ∃ a b : Fin n → Poly F n,
    (∀ i, i ∈ X →
      ∀ j, j ∉ X →
        genericAdjugate A i j =
          cofactorSign i *
            a i *
            b j) ∧
    (∀ i, i ∈ X →
      UsesOnly
        (a i)
        (X.erase i)) ∧
    (∀ j, j ∉ X →
      UsesOnly
        (b j)
        (Xᶜ.erase j)) ∧
    (∀ i, i ∈ X →
      ∀ j, j ∉ X →
        a i ≠ 0 ∧
        b j ≠ 0)

/-!
## 13. Lemma 4.3

The factorization is derived from the cut hypothesis itself.

The only previous-lemma dependency is Lemma 4.2.
-/

theorem lemma_4_3
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n))
    (_hn : 4 ≤ n)
    (hA : MatrixIrreducible A)
    (hcut : IsCut A X)
    (lemma42 :
      MatrixIrreducible A →
        Lemma42Statement A) :
    Lemma43Statement A X := by
  /-
  Lemma 4.2 gives nonvanishing of every adjugate entry.
  -/
  have hG :
      Lemma42Statement A :=
    lemma42 hA
  /-
  Construct the factors from the cut.
  -/
  obtain
    ⟨a, b,
      hfactor,
      haVars,
      hbVars⟩ :=
    cutFactorization_of_isCut
      A X hcut
  refine
    ⟨a, b,
      hfactor,
      haVars,
      hbVars,
      ?_⟩
  /-
  Fix i ∈ X and j ∉ X.
  -/
  intro i hi j hj
  have hGij :
      genericAdjugate A i j ≠ 0 :=
    hG i j
  /-
  The factored product cannot vanish.
  -/
  have hprod :
      cofactorSign i *
          a i *
          b j ≠ 0 := by
    intro hzero
    apply hGij
    calc
      genericAdjugate A i j
          =
          cofactorSign i *
            a i *
            b j :=
        hfactor i hi j hj
      _ = 0 := hzero
  /-
  Therefore a_i is nonzero.
  -/
  have hai :
      a i ≠ 0 := by
    intro hai
    apply hprod
    simp [hai]
  /-
  Likewise b_j is nonzero.
  -/
  have hbj :
      b j ≠ 0 := by
    intro hbj
    apply hprod
    simp [hbj]
  exact ⟨hai, hbj⟩

end

end Lemma43Shaoda
