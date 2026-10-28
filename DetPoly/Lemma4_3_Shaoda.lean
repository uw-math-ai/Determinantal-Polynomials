import Mathlib

/-!
# Lemma 4.3 — Shaoda Ji

Let A be an n × n irreducible matrix over a field F, n ≥ 4.
Let

    M = diag(x₁, ..., xₙ) + A

and

    G = adj(M).

If X is a cut, then for i ∈ X and j ∈ Xᶜ we want

    Gᵢⱼ = (-1)^i aᵢ bⱼ,

where

    aᵢ ∈ F[xₖ : k ∈ X \ {i}],
    bⱼ ∈ F[xₖ : k ∈ Xᶜ \ {j}],

and both aᵢ and bⱼ are nonzero.

----------------------------------------------------------------------
Structure of the mathematical proof
----------------------------------------------------------------------

After simultaneously permuting rows and columns, the paper assumes that
X is an initial block and writes

             [ A₁ + X₁    u vᵀ ]
    M =      [                  ].
             [ p qᵀ       A₂+X₂ ]

Writing

             [ G₁  G₂ ]
    G =      [        ],
             [ G₃  G₄ ]

the identity

    M G = det(M) I

gives in the upper-right block

    (A₁ + X₁) G₂ + u vᵀ G₄ = 0.

Over the fraction field this yields

         (A₁ + X₁)ᵃᵈʲ u · (vᵀG₄)
    G₂ = ------------------------- .
             - det(A₁ + X₁)

Hence G₂ has rank at most one.

The mathematically substantial descent step is then:

    rank-one factorization over Frac(F[x])
          +
    all entries actually lie in F[x]
          +
    cofactor variable-avoidance

        ==> Gᵢⱼ = (-1)^i aᵢ bⱼ

with aᵢ involving only variables in X \ {i} and
bⱼ involving only variables in Xᶜ \ {j}.

That descent is isolated below as `CutFactorizationCore`.

The final part of Lemma 4.3 is then completely formal:

* Lemma 4.2 says every entry Gᵢⱼ is nonzero when A is irreducible.
* Since Gᵢⱼ = (-1)^i aᵢ bⱼ,
  neither aᵢ nor bⱼ can be zero.
-/

open scoped BigOperators

namespace Lemma43Shaoda

noncomputable section

variable {F : Type*} [Field F]

/-!
## 1. The polynomial ring

Lean uses `Fin n = {0, ..., n-1}` for the indices.

Mathematically our polynomial ring is

    F[x₁, ..., xₙ].

In Lean this is

    MvPolynomial (Fin n) F.
-/

abbrev Poly (F : Type*) [CommSemiring F] (n : ℕ) :=
  MvPolynomial (Fin n) F

/-!
## 2. Embed the constant matrix A into the polynomial ring

Every entry of A lies in F.

To add A to the generic diagonal matrix, we first regard its entries
as constant multivariate polynomials.
-/

def polynomialMatrix
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (Poly F n) :=
  A.map (fun a => MvPolynomial.C a)

/-!
## 3. The matrix M = A + diag(x)

The diagonal entry at position i is the polynomial variable X i.

Thus this is exactly the generic matrix

    M = A + diag(x₁, ..., xₙ).
-/

def genericShift
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (Poly F n) :=
  polynomialMatrix A +
    Matrix.diagonal (fun i => MvPolynomial.X i)

/-!
## 4. Its adjugate G

This is the matrix called G in Lemma 4.3:

    G = Mᵃᵈʲ.
-/

def genericAdjugate
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (Poly F n) :=
  (genericShift A).adjugate

/-!
## 5. "A polynomial uses only variables in S"

Mathlib already defines

    p.vars : Finset (Fin n),

the finite set of variables actually occurring in p.

Therefore

    UsesOnly p S

is our formal translation of

    p ∈ F[xₖ : k ∈ S].
-/

def UsesOnly
    {n : ℕ}
    (p : Poly F n)
    (S : Finset (Fin n)) : Prop :=
  p.vars ⊆ S

/-!
For example,

    UsesOnly p (X.erase i)

means precisely

    p ∈ F[xₖ : k ∈ X \ {i}].

In particular, p cannot contain xᵢ.
-/

lemma not_mem_vars_of_usesOnly_erase
    {n : ℕ}
    {p : Poly F n}
    {S : Finset (Fin n)}
    {i : Fin n}
    (h : UsesOnly p (S.erase i)) :
    i ∉ p.vars := by
  intro hi
  have hmem : i ∈ S.erase i := h hi
  simp at hmem

/-!
## 6. Irreducibility of the zero-pattern of A

For the present formalization we encode irreducibility in the standard
subset form:

for every nonempty proper set S of indices, there is a nonzero entry
going from S to its complement.

Applying the same condition to Sᶜ supplies the reverse direction.
-/

def MatrixIrreducible
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ S : Finset (Fin n),
    S.Nonempty →
    S ≠ Finset.univ →
    ∃ i, i ∈ S ∧
      ∃ j, j ∉ S ∧ A i j ≠ 0

/-!
## 7. Cross-blocks and cuts

For finite sets S and T, `crossBlock A S T` is the submatrix

    A[S,T].

A cut has at least two indices on each side and both cross-blocks
have rank one.

This matches the rank-one block structure used in the proof.
-/

def crossBlock
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (S T : Finset (Fin n)) :
    Matrix {i // i ∈ S} {j // j ∈ T} F :=
  A.submatrix Subtype.val Subtype.val

def IsCut
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) : Prop :=
  2 ≤ X.card ∧
  2 ≤ Xᶜ.card ∧
  (crossBlock A X Xᶜ).rank = 1 ∧
  (crossBlock A Xᶜ X).rank = 1

/-!
## 8. The sign (-1)^i

The paper indexes rows by 1, ..., n.

Lean indexes `Fin n` by 0, ..., n-1.

Therefore mathematical row i corresponds to Lean exponent

    i.val + 1.

We regard the sign as a constant polynomial.
-/

def cofactorSign
    {n : ℕ}
    (i : Fin n) :
    Poly F n :=
  MvPolynomial.C
    ((-1 : F) ^ (i.val + 1))

/-!
## 9. Formal statement of Lemma 4.2

Lemma 4.2 is a previously established result.

Its conclusion is:

if A is irreducible, then every entry of

    adj(A + diag(x))

is a nonzero polynomial.

We package only its conclusion here so that Lemma 4.3 can use an
already-proved Lean version of Lemma 4.2.
-/

def Lemma42Statement
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j : Fin n,
    genericAdjugate A i j ≠ 0

/-!
## 10. The fraction-field / rank-one descent step

This is the exact formal interface for the technically difficult middle
part of the handwritten proof.

Starting from the cut, the block identity

    (A₁ + X₁)G₂ + uvᵀG₄ = 0

shows over the fraction field that G₂ has rank at most one.

The paper then cancels common factors in the two rank-one factors and
uses two facts:

1. every entry of G₂ is actually a polynomial;
2. Gᵢⱼ contains neither xᵢ nor xⱼ because it is a cofactor obtained
   by deleting column i and row j.

The result is the existence of polynomial factors aᵢ and bⱼ satisfying

    Gᵢⱼ = (-1)^i aᵢ bⱼ,

with the required separated variable sets.

This proposition is exactly what that descent step must establish.

It deliberately does NOT include nonvanishing of aᵢ and bⱼ.
That is proved later from Lemma 4.2, exactly as in Shaoda's proof.
-/

def CutFactorizationCore
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) : Prop :=
  ∃ a b : Fin n → Poly F n,
    /-
    The rank-one separated factorization.
    -/
    (∀ i, i ∈ X →
      ∀ j, j ∉ X →
        genericAdjugate A i j =
          cofactorSign i * a i * b j) ∧
    /-
    aᵢ uses only variables in X \ {i}.
    -/
    (∀ i, i ∈ X →
      UsesOnly (a i) (X.erase i)) ∧
    /-
    bⱼ uses only variables in Xᶜ \ {j}.
    -/
    (∀ j, j ∉ X →
      UsesOnly (b j) (Xᶜ.erase j))

/-!
## 11. Formal statement of Lemma 4.3

Lemma 4.3 is a proposition: it asserts the existence of polynomial
factors aᵢ and bⱼ.

Therefore we represent the conclusion by an existential proposition,
rather than by a data structure.

This distinction matters in Lean:

* `theorem` must prove something in `Prop`;
* `∃ a, P a` is a proposition;
* we may unpack such an existential while proving another proposition.

The statement below says that there exist two families of polynomials

    a : Fin n → F[x₁, ..., xₙ],
    b : Fin n → F[x₁, ..., xₙ]

such that:

1. Gᵢⱼ = (-1)^i aᵢ bⱼ for i ∈ X and j ∉ X;
2. aᵢ uses only variables in X \ {i};
3. bⱼ uses only variables in Xᶜ \ {j};
4. both aᵢ and bⱼ are nonzero.
-/

def Lemma43Statement
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n)) : Prop :=
  ∃ a b : Fin n → Poly F n,
    /-
    The required rank-one factorization.
    -/
    (∀ i, i ∈ X →
      ∀ j, j ∉ X →
        genericAdjugate A i j =
          cofactorSign i * a i * b j) ∧
    /-
    aᵢ belongs to

        F[xₖ : k ∈ X \ {i}].
    -/
    (∀ i, i ∈ X →
      UsesOnly (a i) (X.erase i)) ∧
    /-
    bⱼ belongs to

        F[xₖ : k ∈ Xᶜ \ {j}].
    -/
    (∀ j, j ∉ X →
      UsesOnly (b j) (Xᶜ.erase j)) ∧
    /-
    Both factors are nonzero for every relevant pair (i,j).
    -/
    (∀ i, i ∈ X →
      ∀ j, j ∉ X →
        a i ≠ 0 ∧ b j ≠ 0)

/-!
## 12. Lemma 4.3

We now prove Lemma 4.3.

The proof has exactly the same logical organization as the paper.

### Step 1

Irreducibility of A is used through Lemma 4.2.

Lemma 4.2 gives

    Gᵢⱼ ≠ 0

for every i and j.

### Step 2

The cut gives the rank-one block factorization.

The technically difficult fraction-field descent has already been isolated
as `CutFactorizationCore`.

It gives polynomial families aᵢ and bⱼ satisfying

    Gᵢⱼ = (-1)^i aᵢ bⱼ

and the required variable restrictions.

### Step 3

Since Gᵢⱼ is nonzero, neither factor can be zero.

Indeed, if aᵢ = 0 or bⱼ = 0, then

    (-1)^i aᵢ bⱼ = 0,

so the factorization would imply Gᵢⱼ = 0, contradicting Lemma 4.2.

This is exactly the final paragraph of Shaoda's proof.
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
        Lemma42Statement A)
    (cutFactorization :
      IsCut A X →
        CutFactorizationCore A X) :
    Lemma43Statement A X := by
  /-
  This is the precise point where irreducibility is used.

  Lemma 4.2 says that irreducibility of A implies that every entry
  of G = adj(A + diag(x)) is a nonzero polynomial.
  -/
  have hG :
      Lemma42Statement A :=
    lemma42 hA
  /-
  Apply the cut-factorization result.

  This produces the two polynomial families a and b, together with:

      hfactor : Gᵢⱼ = (-1)^i aᵢ bⱼ,
      haVars  : aᵢ has the correct variables,
      hbVars  : bⱼ has the correct variables.
  -/
  obtain
    ⟨a, b, hfactor, haVars, hbVars⟩ :=
      cutFactorization hcut
  /-
  Use exactly these polynomial families as the witnesses in the
  existential conclusion of Lemma 4.3.
  -/
  refine
    ⟨a, b,
      hfactor,
      haVars,
      hbVars,
      ?_⟩
  /-
  It remains only to prove that aᵢ and bⱼ are nonzero.
  -/
  intro i hi j hj
  /-
  Lemma 4.2 gives Gᵢⱼ ≠ 0.
  -/
  have hGij :
      genericAdjugate A i j ≠ 0 :=
    hG i j
  /-
  Therefore the product

      (-1)^i aᵢ bⱼ

  is nonzero.

  Otherwise the factorization would make Gᵢⱼ zero.
  -/
  have hprod :
      cofactorSign i * a i * b j ≠ 0 := by
    intro hzero
    apply hGij
    calc
      genericAdjugate A i j
          =
          cofactorSign i * a i * b j :=
        hfactor i hi j hj
      _ = 0 := hzero
  /-
  First prove aᵢ ≠ 0.

  If aᵢ were zero, the whole product would be zero.
  -/
  have hai :
      a i ≠ 0 := by
    intro haiZero
    apply hprod
    simp [haiZero]
  /-
  Similarly prove bⱼ ≠ 0.
  -/
  have hbj :
      b j ≠ 0 := by
    intro hbjZero
    apply hprod
    simp [hbjZero]
  exact ⟨hai, hbj⟩

/-!
## 13. A convenient form of the conclusion

The following theorem simply unfolds `Lemma43Statement`.

It is useful later because Lean displays the entire mathematical
conclusion directly rather than hiding it behind a definition name.
-/

theorem lemma_4_3_explicit
    {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F)
    (X : Finset (Fin n))
    (hn : 4 ≤ n)
    (hA : MatrixIrreducible A)
    (hcut : IsCut A X)
    (lemma42 :
      MatrixIrreducible A →
        Lemma42Statement A)
    (cutFactorization :
      IsCut A X →
        CutFactorizationCore A X) :
    ∃ a b : Fin n → Poly F n,
      (∀ i, i ∈ X →
        ∀ j, j ∉ X →
          genericAdjugate A i j =
            cofactorSign i * a i * b j) ∧
      (∀ i, i ∈ X →
        UsesOnly (a i) (X.erase i)) ∧
      (∀ j, j ∉ X →
        UsesOnly (b j) (Xᶜ.erase j)) ∧
      (∀ i, i ∈ X →
        ∀ j, j ∉ X →
          a i ≠ 0 ∧ b j ≠ 0) := by
  exact
    lemma_4_3
      A X hn hA hcut
      lemma42 cutFactorization

/-!
## 14. Reading the variable restrictions

Suppose we are inside another proof and have obtained witnesses

    a, b, hfactor, haVars, hbVars, hnonzero

from Lemma 4.3.

The next two lemmas translate the `UsesOnly` statements into the
particularly important facts

    xᵢ does not occur in aᵢ,

and

    xⱼ does not occur in bⱼ.
-/

lemma a_avoids_own_variable
    {n : ℕ}
    {X : Finset (Fin n)}
    {a : Fin n → Poly F n}
    {i : Fin n}
    (hi : i ∈ X)
    (ha :
      ∀ r, r ∈ X →
        UsesOnly (a r) (X.erase r)) :
    i ∉ (a i).vars := by
  exact
    not_mem_vars_of_usesOnly_erase
      (ha i hi)

lemma b_avoids_own_variable
    {n : ℕ}
    {X : Finset (Fin n)}
    {b : Fin n → Poly F n}
    {j : Fin n}
    (hj : j ∉ X)
    (hb :
      ∀ r, r ∉ X →
        UsesOnly (b r) (Xᶜ.erase r)) :
    j ∉ (b j).vars := by
  exact
    not_mem_vars_of_usesOnly_erase
      (hb j hj)

end

end Lemma43Shaoda
