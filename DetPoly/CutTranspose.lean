/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grant Yang
-/
module

public import DetPoly.IrreducibleMatrix
public import DetPoly.Lemma4_3_Shaoda

/-!
# Cuts and cut-transposes

A *cut* of `A` (Al Ahmadieh, before Lemma 4.3; CGGR Def. 2.5) is a set `X` with `2 ≤ |X|`,
`2 ≤ |Xᶜ|` whose cross blocks have rank at most one, i.e. `A = [[E, p qᵀ], [u vᵀ, N]]` along
`X`, `Xᶜ`. The *cut-transpose* (CGGR Def. 2.10) is `ct(A, X) = [[E, p uᵀ], [q vᵀ, Nᵀ]]`.

## Main definitions

* `Matrix.R1Factorization A`: a set `X` with vectors `p q u v` such that `A[X,Xᶜ] = p qᵀ` and
  `A[Xᶜ,X] = u vᵀ`. No size condition.
* `Matrix.cutTranspose A f`: the matrix `[[E, p uᵀ], [q vᵀ, Nᵀ]]` for `f : A.R1Factorization`.
* `Matrix.R1CutFactorization A`: an `R1Factorization` with `2 ≤ |X|` and `2 ≤ |Xᶜ|`.
* `Matrix.HasCut A X`: `X` is a cut of `A`, i.e. `A` has a rank-one cut factorization at `X`.
* `Matrix.IsCutTranspose A X B`: `B = ct(A, X)` for some cut factorization at `X`.
* `Matrix.CutTransposePath A C`: a sequence of cut-transposes from `A` to `C`, as data, with
  `length` and `cuts`.
* `Matrix.CutTransposeConnected A C`: some `CutTransposePath A C` exists.

## Main results

* `Matrix.hasCut_iff_rank_le_one`: over a field, `HasCut` is Al Ahmadieh's rank condition.
* `Matrix.HasCut.rank_eq_one`: for irreducible `A`, both cross blocks of a cut have rank one.
* `Matrix.det_add_vecMulVec`: the matrix determinant lemma over a commutative ring.
* `Matrix.det_fromBlocks_vecMulVec`:
  `det [[E, p qᵀ], [u vᵀ, N]] = det E det N - (vᵀ adj(E) p) (qᵀ adj(N) u)`.
* `Matrix.principalMinor_cutTranspose` (CGGR Lemma 2.12, Al Ahmadieh Lemma 4.5): cut-transposes
  preserve principal minors, over any commutative ring.
* `Matrix.cutTransposeConnected_equivalence`: being connected by cut-transposes is an
  equivalence relation.

## Implementation notes

The cut-transpose and its determinant are developed for `R1Factorization`, without the size
conditions of a cut: restricting to a principal submatrix can leave fewer than two indices of `X`,
and the principal-minor statement needs the determinant statement for those restrictions.

`HasCut` asks for a factorization rather than `rank ≤ 1`, so it makes sense over any ring (for
instance for `(diag(x) + A)^adj` over `MvPolynomial n R`); `rank` over a ring that is not a field
does not mean "outer product". The `X` block comes first and the `Xᶜ` block is transposed, as in
CGGR.
-/

@[expose] public section

open Finset

namespace Matrix

variable {R n m : Type*}

section Mul

variable [Mul R] [Fintype n] [DecidableEq n]

/-! ### Rank-one factorizations of the cross blocks -/

variable (A : Matrix n n R) in
/-- A *rank-one factorization* of the cross blocks of `A`: a set `X` with vectors `p q u v`
such that `A[X,Xᶜ] = p qᵀ` and `A[Xᶜ,X] = u vᵀ`, i.e. `A = [[E, p qᵀ], [u vᵀ, N]]`. Only the
values of `p, v` on `X` and of `q, u` on `Xᶜ` matter. -/
structure R1Factorization where
  /-- The set along which `A` is split into blocks. -/
  X : Finset n
  /-- The column factor of `A[X,Xᶜ]`. -/
  p : n → R
  /-- The row factor of `A[X,Xᶜ]`. -/
  q : n → R
  /-- The column factor of `A[Xᶜ,X]`. -/
  u : n → R
  /-- The row factor of `A[Xᶜ,X]`. -/
  v : n → R
  apply_mem_notMem : ∀ i ∈ X, ∀ j ∉ X, A i j = p i * q j
  apply_notMem_mem : ∀ i ∉ X, ∀ j ∈ X, A i j = u i * v j

variable {A : Matrix n n R} {X : Finset n}

namespace R1Factorization

variable (f : A.R1Factorization)

/-- The same factorization, read along `Xᶜ`: the two cross blocks exchange roles. -/
@[simps]
def compl : A.R1Factorization where
  X := f.Xᶜ
  p := f.u
  q := f.v
  u := f.p
  v := f.q
  apply_mem_notMem i hi j hj := f.apply_notMem_mem i (by simpa using hi) j (by simpa using hj)
  apply_notMem_mem i hi j hj := f.apply_mem_notMem i (by simpa using hi) j (by simpa using hj)

/-- Restriction along `e : m → n`, in particular to a principal submatrix. -/
@[simps]
def submatrix [Fintype m] (e : m → n) : (A.submatrix e e).R1Factorization where
  X := {i | e i ∈ f.X}
  p := f.p ∘ e
  q := f.q ∘ e
  u := f.u ∘ e
  v := f.v ∘ e
  apply_mem_notMem i hi j hj := f.apply_mem_notMem _ (by simpa using hi) _ (by simpa using hj)
  apply_notMem_mem i hi j hj := f.apply_notMem_mem _ (by simpa using hi) _ (by simpa using hj)

end R1Factorization

/-! ### The cut-transpose -/

variable (A) in
/-- The cut-transpose `ct(A, X) = [[E, p uᵀ], [q vᵀ, Nᵀ]]` of `A = [[E, p qᵀ], [u vᵀ, N]]`
(CGGR Def. 2.10): swap `q ↔ u` and transpose the `Xᶜ` block. -/
def cutTranspose (f : A.R1Factorization) : Matrix n n R :=
  of fun i j ↦
    if i ∈ f.X then (if j ∈ f.X then A i j else f.p i * f.u j)
    else (if j ∈ f.X then f.q i * f.v j else A j i)

omit [Fintype n] in
theorem cutTranspose_apply (f : A.R1Factorization) (i j : n) :
    A.cutTranspose f i j =
      if i ∈ f.X then (if j ∈ f.X then A i j else f.p i * f.u j)
      else (if j ∈ f.X then f.q i * f.v j else A j i) :=
  rfl

/-- The cut-transpose is split along the same set, with the factors `q` and `u` swapped. -/
@[simps]
def R1Factorization.swap (f : A.R1Factorization) : (A.cutTranspose f).R1Factorization where
  X := f.X
  p := f.p
  q := f.u
  u := f.q
  v := f.v
  apply_mem_notMem i hi j hj := by simp [cutTranspose_apply, hi, hj]
  apply_notMem_mem i hi j hj := by simp [cutTranspose_apply, hi, hj]

omit [Fintype n] in
/-- `ct(ct(A, X), X) = A` (CGGR Remark 2.11), for the swapped factorization. -/
@[simp]
theorem cutTranspose_swap (f : A.R1Factorization) :
    (A.cutTranspose f).cutTranspose f.swap = A := by
  ext i j
  by_cases hi : i ∈ f.X <;> by_cases hj : j ∈ f.X
  · simp [cutTranspose_apply, hi, hj]
  · simpa [cutTranspose_apply, hi, hj] using (f.apply_mem_notMem i hi j hj).symm
  · simpa [cutTranspose_apply, hi, hj] using (f.apply_notMem_mem i hi j hj).symm
  · simp [cutTranspose_apply, hi, hj]

omit [Fintype n] in
/-- The cut-transpose commutes with reindexing, in particular with principal submatrices. -/
theorem submatrix_cutTranspose [Fintype m] [DecidableEq m] (f : A.R1Factorization)
    (e : m → n) : (A.cutTranspose f).submatrix e e = (A.submatrix e e).cutTranspose
      (f.submatrix e) := by
  ext i j
  simp [cutTranspose_apply]

/-! ### Cuts -/

variable (A) in
/-- A *rank-one cut factorization* of `A`: a rank-one factorization of the cross blocks along a
set `X` with `2 ≤ |X|` and `2 ≤ |Xᶜ|`. -/
structure R1CutFactorization extends A.R1Factorization where
  two_le_card : 2 ≤ #X
  two_le_card_compl : 2 ≤ #Xᶜ

instance : CoeOut A.R1CutFactorization A.R1Factorization :=
  ⟨R1CutFactorization.toR1Factorization⟩

/-- `X` is a *cut* of `A`: `A` has a rank-one cut factorization at `X`. Over a field this is
Al Ahmadieh's definition `2 ≤ |X|`, `2 ≤ |Xᶜ|`, `rk A[X,Xᶜ] ≤ 1`, `rk A[Xᶜ,X] ≤ 1`
(`hasCut_iff_rank_le_one`). -/
def HasCut (A : Matrix n n R) (X : Finset n) : Prop :=
  ∃ f : A.R1CutFactorization, f.X = X

namespace R1CutFactorization

variable (f : A.R1CutFactorization)

/-- The cut of a cut factorization is a cut. -/
theorem hasCut : A.HasCut f.X :=
  ⟨f, rfl⟩

/-- The same factorization, read at the complementary cut `Xᶜ`. -/
def compl : A.R1CutFactorization :=
  ⟨f.toR1Factorization.compl, f.two_le_card_compl, by simpa using f.two_le_card⟩

/-- The cut-transpose has the same cut, with the factors `q` and `u` swapped. -/
def swap : (A.cutTranspose f).R1CutFactorization :=
  ⟨f.toR1Factorization.swap, f.two_le_card, f.two_le_card_compl⟩

@[simp] theorem toR1Factorization_compl : f.compl.toR1Factorization = f.toR1Factorization.compl :=
  rfl

@[simp] theorem toR1Factorization_swap : f.swap.toR1Factorization = f.toR1Factorization.swap :=
  rfl

end R1CutFactorization

/-- `HasCut` in terms of the size conditions and a rank-one factorization. -/
theorem hasCut_iff_exists_r1Factorization :
    A.HasCut X ↔ 2 ≤ #X ∧ 2 ≤ #Xᶜ ∧ ∃ f : A.R1Factorization, f.X = X := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.two_le_card, f.two_le_card_compl, f, rfl⟩
  · rintro ⟨h₁, h₂, f, rfl⟩
    exact ⟨⟨f, h₁, h₂⟩, rfl⟩

theorem HasCut.two_le_card (h : A.HasCut X) : 2 ≤ #X :=
  (hasCut_iff_exists_r1Factorization.mp h).1

theorem HasCut.two_le_card_compl (h : A.HasCut X) : 2 ≤ #Xᶜ :=
  (hasCut_iff_exists_r1Factorization.mp h).2.1

/-- The complement of a cut is a cut. -/
theorem HasCut.compl (h : A.HasCut X) : A.HasCut Xᶜ := by
  obtain ⟨f, rfl⟩ := h
  exact f.compl.hasCut

@[simp]
theorem hasCut_compl_iff : A.HasCut Xᶜ ↔ A.HasCut X :=
  ⟨fun h ↦ by simpa using h.compl, HasCut.compl⟩

/-- `X` is still a cut of `ct(A, X)`. -/
theorem HasCut.cutTranspose (f : A.R1CutFactorization) : (A.cutTranspose f).HasCut f.X :=
  f.swap.hasCut

/-- `B` is a cut-transpose of `A` at the cut `X`: `B = ct(A, X)` for some factorization of
the cross blocks. Statements about CGGR's `ct(A, X)` are phrased for every such `B`. -/
def IsCutTranspose (A : Matrix n n R) (X : Finset n) (B : Matrix n n R) : Prop :=
  ∃ f : A.R1CutFactorization, f.X = X ∧ B = A.cutTranspose f

variable {B : Matrix n n R}

theorem isCutTranspose_cutTranspose (f : A.R1CutFactorization) :
    IsCutTranspose A f.X (A.cutTranspose f) :=
  ⟨f, rfl, rfl⟩

/-- Every cut has a cut-transpose. -/
theorem HasCut.exists_isCutTranspose (h : A.HasCut X) : ∃ B, IsCutTranspose A X B :=
  let ⟨f, hf⟩ := h
  ⟨_, f, hf, rfl⟩

theorem IsCutTranspose.hasCut_left (h : IsCutTranspose A X B) : A.HasCut X := by
  obtain ⟨f, rfl, -⟩ := h
  exact f.hasCut

theorem IsCutTranspose.hasCut_right (h : IsCutTranspose A X B) : B.HasCut X := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact HasCut.cutTranspose f

/-- Being a cut-transpose at `X` is symmetric. -/
theorem IsCutTranspose.symm (h : IsCutTranspose A X B) : IsCutTranspose B X A := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨f.swap, rfl, (cutTranspose_swap f.toR1Factorization).symm⟩

/-! ### Paths of cut-transposes -/

/-- A *cut-transpose path* from `A` to `C` (CGGR Def. 2.14 without the final diagonal
equivalence): matrices `A = A₀, A₁, …, A_k = C` with `Aᵢ = ct(Aᵢ₋₁, fᵢ)` for cut factorizations
`fᵢ` of `Aᵢ₋₁`. It is data: `CutTransposePath.length` is `k` and `CutTransposePath.cuts` is
the list of cuts used. -/
inductive CutTransposePath : Matrix n n R → Matrix n n R → Type _
  | nil (A : Matrix n n R) : CutTransposePath A A
  | cons {A B C : Matrix n n R} (f : A.R1CutFactorization) (hB : B = A.cutTranspose f)
      (p : CutTransposePath B C) : CutTransposePath A C

namespace CutTransposePath

variable {C D : Matrix n n R}

/-- The number of cut-transposes in the path. -/
def length : {A C : Matrix n n R} → CutTransposePath A C → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ _ p => p.length + 1

/-- The cuts used, in order. -/
def cuts : {A C : Matrix n n R} → CutTransposePath A C → List (Finset n)
  | _, _, nil _ => []
  | _, _, cons f _ p => f.X :: p.cuts

/-- The path with a single cut-transpose. -/
def single (f : A.R1CutFactorization) : CutTransposePath A (A.cutTranspose f) :=
  cons f rfl (nil _)

/-- Concatenation of paths. -/
def append :
    {A B C : Matrix n n R} → CutTransposePath A B → CutTransposePath B C → CutTransposePath A C
  | _, _, _, nil _, q => q
  | _, _, _, cons f hB p, q => cons f hB (p.append q)

/-- The reversed path, using `ct(ct(A, X), X) = A` at each step. -/
def reverse : {A C : Matrix n n R} → CutTransposePath A C → CutTransposePath C A
  | _, _, nil A => nil A
  | _, _, cons f rfl p =>
    p.reverse.append (cons f.swap (cutTranspose_swap f.toR1Factorization).symm (nil _))

@[simp] theorem length_nil : (nil A).length = 0 := rfl

@[simp] theorem length_cons (f : A.R1CutFactorization) (hB : B = A.cutTranspose f)
    (p : CutTransposePath B C) : (cons f hB p).length = p.length + 1 := rfl

@[simp] theorem cuts_nil : (nil A).cuts = [] := rfl

@[simp] theorem cuts_cons (f : A.R1CutFactorization) (hB : B = A.cutTranspose f)
    (p : CutTransposePath B C) : (cons f hB p).cuts = f.X :: p.cuts := rfl

@[simp] theorem length_single (f : A.R1CutFactorization) : (single f).length = 1 := rfl

@[simp] theorem cuts_single (f : A.R1CutFactorization) : (single f).cuts = [f.X] := rfl

@[simp]
theorem length_cuts (p : CutTransposePath A C) : p.cuts.length = p.length := by
  induction p with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

@[simp]
theorem cuts_append (p : CutTransposePath A B) (q : CutTransposePath B C) :
    (p.append q).cuts = p.cuts ++ q.cuts := by
  induction p with
  | nil => rfl
  | cons _ _ _ ih => simp [append, ih]

@[simp]
theorem length_append (p : CutTransposePath A B) (q : CutTransposePath B C) :
    (p.append q).length = p.length + q.length := by
  simp [← length_cuts]

@[simp]
theorem cuts_reverse (p : CutTransposePath A C) : p.reverse.cuts = p.cuts.reverse := by
  induction p with
  | nil => rfl
  | cons f hB p ih => subst hB; simp [reverse, ih, cuts, R1CutFactorization.swap]

@[simp]
theorem length_reverse (p : CutTransposePath A C) : p.reverse.length = p.length := by
  simp [← length_cuts]

/-- Each step of a path is a cut-transpose at the corresponding cut. -/
theorem isCutTranspose_of_cons (f : A.R1CutFactorization) (hB : B = A.cutTranspose f) :
    IsCutTranspose A f.X B :=
  ⟨f, rfl, hB⟩

end CutTransposePath

/-- `A` and `C` are connected by a sequence of cut-transposes. -/
def CutTransposeConnected (A C : Matrix n n R) : Prop :=
  Nonempty (CutTransposePath A C)

variable (R n) in
/-- Being connected by cut-transposes is an equivalence relation. -/
theorem cutTransposeConnected_equivalence :
    Equivalence (CutTransposeConnected : Matrix n n R → Matrix n n R → Prop) where
  refl A := ⟨.nil A⟩
  symm := fun ⟨p⟩ ↦ ⟨p.reverse⟩
  trans := fun ⟨p⟩ ⟨q⟩ ↦ ⟨p.append q⟩

/-- A cut-transpose at `X` gives a path of length one through `X`. -/
theorem IsCutTranspose.exists_path (h : IsCutTranspose A X B) :
    ∃ p : CutTransposePath A B, p.cuts = [X] := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨.single f, rfl⟩

end Mul

/-! ### Transposes and complements -/

section CommMagma

variable [CommMagma R] [Fintype n] [DecidableEq n] {A B : Matrix n n R} {X : Finset n}

/-- The induced factorization of `Aᵀ`, along the same set. -/
@[simps]
def R1Factorization.transpose (f : A.R1Factorization) : Aᵀ.R1Factorization where
  X := f.X
  p := f.v
  q := f.u
  u := f.q
  v := f.p
  apply_mem_notMem i hi j hj := by rw [transpose_apply, f.apply_notMem_mem j hj i hi, mul_comm]
  apply_notMem_mem i hi j hj := by rw [transpose_apply, f.apply_mem_notMem j hj i hi, mul_comm]

omit [Fintype n] in
/-- `ct(A, X)ᵀ = ct(Aᵀ, X)` for the induced factorization. -/
theorem transpose_cutTranspose (f : A.R1Factorization) :
    (A.cutTranspose f)ᵀ = Aᵀ.cutTranspose f.transpose := by
  ext i j
  by_cases hi : i ∈ f.X <;> by_cases hj : j ∈ f.X <;>
    simp [cutTranspose_apply, hi, hj, mul_comm]

/-- Transposing the `X` block instead of the `Xᶜ` block gives the transposed matrix:
`ct(A, Xᶜ) = ct(A, X)ᵀ`. This is why Lemma 4.5 and Example 4.6 of Al Ahmadieh's paper agree up
to diagonal equivalence. -/
theorem cutTranspose_compl (f : A.R1Factorization) :
    A.cutTranspose f.compl = (A.cutTranspose f)ᵀ := by
  ext i j
  by_cases hi : i ∈ f.X <;> by_cases hj : j ∈ f.X <;>
    simp [cutTranspose_apply, hi, hj, mul_comm]

/-- The induced cut factorization of `Aᵀ`, at the same cut. -/
def R1CutFactorization.transpose (f : A.R1CutFactorization) : Aᵀ.R1CutFactorization :=
  ⟨f.toR1Factorization.transpose, f.two_le_card, f.two_le_card_compl⟩

@[simp]
theorem R1CutFactorization.toR1Factorization_transpose (f : A.R1CutFactorization) :
    f.transpose.toR1Factorization = f.toR1Factorization.transpose :=
  rfl

theorem HasCut.transpose (h : A.HasCut X) : Aᵀ.HasCut X := by
  obtain ⟨f, rfl⟩ := h
  exact f.transpose.hasCut

@[simp]
theorem hasCut_transpose : Aᵀ.HasCut X ↔ A.HasCut X :=
  ⟨fun h ↦ by simpa using h.transpose, HasCut.transpose⟩

theorem IsCutTranspose.transpose (h : IsCutTranspose A X B) : IsCutTranspose Aᵀ X Bᵀ := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨f.transpose, rfl, transpose_cutTranspose f.toR1Factorization⟩

theorem IsCutTranspose.compl (h : IsCutTranspose A X B) : IsCutTranspose A Xᶜ Bᵀ := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨f.compl, rfl, (cutTranspose_compl f.toR1Factorization).symm⟩

end CommMagma

/-! ## Cut-transposes preserve principal minors (CGGR Lemma 2.12) -/

section CommRing

variable [CommRing R] [Fintype n] [DecidableEq n]

/-- The **matrix determinant lemma** over a commutative ring:
`det (A + u vᵀ) = det A + vᵀ adj(A) u`. Compare `Matrix.det_add_replicateCol_mul_replicateRow`,
which assumes `A` invertible. -/
theorem det_add_vecMulVec (A : Matrix n n R) (u v : n → R) :
    (A + vecMulVec u v).det = A.det + v ⬝ᵥ A.adjugate *ᵥ u := by
  -- Add `v j • u` to the columns `j ∈ S` one at a time.
  let B (S : Finset n) : Matrix n n R := of fun i j ↦ A i j + if j ∈ S then u i * v j else 0
  suffices h : ∀ S, (B S).det = A.det + ∑ j ∈ S, v j * (A.updateCol j u).det by
    have hB : A + vecMulVec u v = B univ := by ext; simp [B, vecMulVec_apply]
    rw [hB, h, ← cramer_eq_adjugate_mulVec, dotProduct]
    simp [cramer_apply]
  intro S
  induction S using Finset.induction_on with
  | empty =>
    have : B ∅ = A := by ext; simp [B]
    simp [this]
  | insert k S hk ih =>
    have hBk : B (insert k S) = (B S).updateCol k ((fun i ↦ B S i k) + v k • u) := by
      ext i j
      by_cases hj : j = k
      · subst hj; simp [B, hk, mul_comm]
      · simp [B, hj]
    -- Subtracting `v j •` column `k` from each column `j ∈ S` turns `B S` back into `A`.
    have hu : ((B S).updateCol k u).det = (A.updateCol k u).det := by
      rw [← det_transpose, ← det_transpose (A.updateCol k u)]
      refine det_eq_of_forall_row_eq_smul_add_const (fun j ↦ if j ∈ S then v j else 0) k
        (by simp [hk]) fun j i ↦ ?_
      by_cases hj : j = k
      · subst hj; simp [hk]
      · by_cases hjS : j ∈ S <;> simp [B, hj, hjS, mul_comm]
    rw [hBk, det_updateCol_add, updateCol_eq_self, det_updateCol_smul, ih, hu,
      sum_insert hk]
    ring

/-- The determinant of `[[E, p qᵀ], [u vᵀ, N]]`. This is the rank-one Schur complement formula
`det E · det (N - u vᵀ E⁻¹ p qᵀ)`, without assuming `E` invertible. -/
theorem det_fromBlocks_vecMulVec {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (E : Matrix X X R) (N : Matrix Y Y R) (p v : X → R) (q u : Y → R) :
    (fromBlocks E (vecMulVec p q) (vecMulVec u v) N).det =
      E.det * N.det - (v ⬝ᵥ E.adjugate *ᵥ p) * (q ⬝ᵥ N.adjugate *ᵥ u) := by
  have hsplit : fromBlocks E (vecMulVec p q) (vecMulVec u v) N =
      fromBlocks E (vecMulVec p q) 0 N + vecMulVec (Sum.elim 0 u) (Sum.elim v 0) := by
    ext (i | i) (j | j) <;> simp [vecMulVec_apply]
  have hE : ∑ i, v i * (E.updateCol i p).det = v ⬝ᵥ E.adjugate *ᵥ p := by
    simp [← cramer_eq_adjugate_mulVec, cramer_apply, dotProduct]
  have hN : ∑ j, (N.updateRow j q).det * u j = q ⬝ᵥ N.adjugate *ᵥ u := by
    rw [dotProduct_mulVec, dotProduct, ← mulVec_transpose, adjugate_transpose,
      ← cramer_eq_adjugate_mulVec]
    simp [cramer_transpose_apply]
  have key : Sum.elim v 0 ⬝ᵥ (fromBlocks E (vecMulVec p q) 0 N).adjugate *ᵥ Sum.elim 0 u =
      -((∑ i, v i * (E.updateCol i p).det) * ∑ j, (N.updateRow j q).det * u j) := by
    simp only [dotProduct, mulVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, zero_mul, mul_zero, sum_const_zero, add_zero, zero_add,
      Lemma43Shaoda.adjugate_fromBlocks_vecMulVec_apply₁₂]
    rw [sum_mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_neg_distrib, mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [hsplit, det_add_vecMulVec, det_fromBlocks_zero₂₁, key, hE, hN]
  ring

/-- A cut-transpose has the same determinant. No size condition on `X` is needed. -/
theorem det_cutTranspose {A : Matrix n n R} (f : A.R1Factorization) :
    (A.cutTranspose f).det = A.det := by
  let e := Equiv.sumCompl (· ∈ f.X)
  let E : Matrix {i // i ∈ f.X} {i // i ∈ f.X} R := A.submatrix Subtype.val Subtype.val
  let N : Matrix {i // i ∉ f.X} {i // i ∉ f.X} R := A.submatrix Subtype.val Subtype.val
  let p (i : {i // i ∈ f.X}) := f.p i
  let v (i : {i // i ∈ f.X}) := f.v i
  let q (i : {i // i ∉ f.X}) := f.q i
  let u (i : {i // i ∉ f.X}) := f.u i
  have hA : A.submatrix e e = fromBlocks E (vecMulVec p q) (vecMulVec u v) N := by
    ext (⟨i, hi⟩ | ⟨i, hi⟩) (⟨j, hj⟩ | ⟨j, hj⟩) <;>
      simp [e, E, N, p, q, u, v, vecMulVec_apply, f.apply_mem_notMem, f.apply_notMem_mem, hi, hj]
  have hB : (A.cutTranspose f).submatrix e e =
      fromBlocks E (vecMulVec p u) (vecMulVec q v) Nᵀ := by
    ext (⟨i, hi⟩ | ⟨i, hi⟩) (⟨j, hj⟩ | ⟨j, hj⟩) <;>
      simp [e, E, N, p, q, u, v, cutTranspose_apply, vecMulVec_apply, hi, hj]
  rw [← det_submatrix_equiv_self e, ← det_submatrix_equiv_self e A, hA, hB,
    det_fromBlocks_vecMulVec, det_fromBlocks_vecMulVec, det_transpose, ← adjugate_transpose,
    mulVec_transpose, dotProduct_comm u, ← dotProduct_mulVec]

omit [Fintype n] in
/-- **CGGR Lemma 2.12** (Al Ahmadieh Lemma 4.5): a cut-transpose has the same principal
minors. -/
@[simp]
theorem principalMinor_cutTranspose {A : Matrix n n R} (f : A.R1Factorization) :
    (A.cutTranspose f).principalMinor = A.principalMinor := by
  ext S
  rw [principalMinor, setSubmatrix, submatrix_cutTranspose, det_cutTranspose]

theorem IsCutTranspose.principalMinor_eq {A B : Matrix n n R} {X : Finset n}
    (h : IsCutTranspose A X B) : A.principalMinor = B.principalMinor := by
  obtain ⟨f, -, rfl⟩ := h
  exact (principalMinor_cutTranspose f.toR1Factorization).symm

theorem CutTransposePath.principalMinor_eq {A C : Matrix n n R} (p : CutTransposePath A C) :
    A.principalMinor = C.principalMinor := by
  induction p with
  | nil => rfl
  | cons f hB _ ih => exact (hB ▸ principalMinor_cutTranspose f.toR1Factorization).symm.trans ih

theorem CutTransposeConnected.principalMinor_eq {A C : Matrix n n R}
    (h : CutTransposeConnected A C) : A.principalMinor = C.principalMinor :=
  let ⟨p⟩ := h
  p.principalMinor_eq

end CommRing

/-! ## Cuts over a field -/

section Field

variable {𝔽 : Type*} [Field 𝔽]

/-- A matrix has rank `≤ 1` iff it is an outer product `u vᵀ`. Mathlib has the `←` direction
(`Matrix.rank_vecMulVec_le`) and the module version
(`Submodule.finrank_le_one_iff_isPrincipal`). -/
theorem rank_le_one_iff_eq_vecMulVec {p : Type*} [Fintype p] (M : Matrix m p 𝔽) :
    M.rank ≤ 1 ↔ ∃ u v, M = vecMulVec u v := by
  refine ⟨fun h ↦ ?_, fun ⟨u, v, h⟩ ↦ h ▸ rank_vecMulVec_le u v⟩
  have := FiniteDimensional.span_of_finite 𝔽 (Set.finite_range M.col)
  rw [rank_eq_finrank_span_cols, Submodule.finrank_le_one_iff_isPrincipal,
    Submodule.isPrincipal_iff] at h
  obtain ⟨u, hu⟩ := h
  have : ∀ j, ∃ c : 𝔽, c • u = M.col j := fun j ↦
    Submodule.mem_span_singleton.mp (hu ▸ Submodule.subset_span ⟨j, rfl⟩)
  choose c hc using this
  refine ⟨u, c, ?_⟩
  ext i j
  rw [vecMulVec_apply, ← col_apply M j i, ← hc j, Pi.smul_apply, smul_eq_mul, mul_comm]

variable [Fintype n] [DecidableEq n] {A : Matrix n n 𝔽} {X : Finset n}

/-- A rank-one factorization bounds the ranks of the cross blocks. -/
theorem R1Factorization.rank_le_one (f : A.R1Factorization) :
    (A.setSubmatrix f.X (f.Xᶜ : Finset n)).rank ≤ 1 ∧
      (A.setSubmatrix (f.Xᶜ : Finset n) f.X).rank ≤ 1 := by
  constructor
  · refine (rank_le_one_iff_eq_vecMulVec _).mpr ⟨fun i ↦ f.p i, fun j ↦ f.q j, ?_⟩
    ext ⟨i, hi⟩ ⟨j, hj⟩
    exact f.apply_mem_notMem i (by simpa using hi) j (by simpa using hj)
  · refine (rank_le_one_iff_eq_vecMulVec _).mpr ⟨fun i ↦ f.u i, fun j ↦ f.v j, ?_⟩
    ext ⟨i, hi⟩ ⟨j, hj⟩
    exact f.apply_notMem_mem i (by simpa using hi) j (by simpa using hj)

/-- Cross blocks of rank at most one have a rank-one factorization. -/
theorem exists_r1Factorization_of_rank_le_one
    (h₁ : (A.setSubmatrix X (Xᶜ : Finset n)).rank ≤ 1)
    (h₂ : (A.setSubmatrix (Xᶜ : Finset n) X).rank ≤ 1) :
    ∃ f : A.R1Factorization, f.X = X := by
  obtain ⟨p, q, hpq⟩ := (rank_le_one_iff_eq_vecMulVec _).mp h₁
  obtain ⟨u, v, huv⟩ := (rank_le_one_iff_eq_vecMulVec _).mp h₂
  refine ⟨⟨X, fun i ↦ if hi : i ∈ X then p ⟨i, by simpa using hi⟩ else 0,
    fun j ↦ if hj : j ∈ X then 0 else q ⟨j, by simpa using hj⟩,
    fun i ↦ if hi : i ∈ X then 0 else u ⟨i, by simpa using hi⟩,
    fun j ↦ if hj : j ∈ X then v ⟨j, by simpa using hj⟩ else 0, fun i hi j hj ↦ ?_,
    fun i hi j hj ↦ ?_⟩, rfl⟩
  · simpa [hi, hj, vecMulVec_apply] using
      congrFun (congrFun hpq ⟨i, by simpa using hi⟩) ⟨j, by simpa using hj⟩
  · simpa [hi, hj, vecMulVec_apply] using
      congrFun (congrFun huv ⟨i, by simpa using hi⟩) ⟨j, by simpa using hj⟩

/-- Over a field, `HasCut` is Al Ahmadieh's definition: `2 ≤ |X|`, `2 ≤ |Xᶜ|`, and both
cross blocks have rank at most one. -/
theorem hasCut_iff_rank_le_one :
    A.HasCut X ↔ 2 ≤ #X ∧ 2 ≤ #Xᶜ ∧ (A.setSubmatrix X (Xᶜ : Finset n)).rank ≤ 1 ∧
      (A.setSubmatrix (Xᶜ : Finset n) X).rank ≤ 1 := by
  rw [hasCut_iff_exists_r1Factorization]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨?_, fun ⟨h₃, h₄⟩ ↦
    exists_r1Factorization_of_rank_le_one h₃ h₄⟩
  rintro ⟨f, rfl⟩
  exact f.rank_le_one

/-- If `A` is irreducible and `X` is a cut, both cross blocks have rank exactly one. -/
theorem HasCut.rank_eq_one (hX : A.HasCut X) (hA : A.IsIrred) :
    (A.setSubmatrix X (Xᶜ : Finset n)).rank = 1 ∧
      (A.setSubmatrix (Xᶜ : Finset n) X).rank = 1 := by
  -- The two statements are swapped by `X ↔ Xᶜ`, so it suffices to prove the first for any cut.
  suffices key : ∀ Y : Finset n, A.HasCut Y → (A.setSubmatrix Y (Yᶜ : Finset n)).rank = 1 from
    ⟨key X hX, by have h := key Xᶜ hX.compl; rwa [compl_compl] at h⟩
  intro Y hY
  obtain ⟨hYcard, hYcCard, hUpperBd, -⟩ := hasCut_iff_rank_le_one.mp hY
  refine le_antisymm hUpperBd ?_
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ Y, ∃ j ∈ Yᶜ, A i j ≠ 0 := by
    by_contra hall
    push Not at hall
    have hne : Yᶜ.Nonempty := Finset.card_pos.mp (by omega)
    have hnu : Yᶜ ≠ Finset.univ := by
      intro h
      rw [Finset.compl_eq_univ_iff] at h
      simp [h] at hYcard
    exact (isReducible_iff_exists_finset.mpr
      ⟨Yᶜ, hne, hnu, fun i hi j hj ↦ hall i (by simpa using hi) j hj⟩) hA
  rw [rank_eq_finrank_span_cols]
  refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩⟩, ?_⟩
  intro hc
  apply hij
  have := congrArg (fun v : Submodule.span 𝔽 (Set.range _) ↦ (v : Y → 𝔽) ⟨i, hi⟩) hc
  simpa using this

/-- For irreducible `A`, the cross blocks of a cut factorization are nonzero. -/
theorem R1CutFactorization.rank_eq_one (f : A.R1CutFactorization) (hA : A.IsIrred) :
    (A.setSubmatrix f.X (f.Xᶜ : Finset n)).rank = 1 ∧
      (A.setSubmatrix (f.Xᶜ : Finset n) f.X).rank = 1 :=
  f.hasCut.rank_eq_one hA

end Field

end Matrix

end
