/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaoda Ji
-/

module

public import Mathlib


/-!
# Determinant after adding a diagonal matrix

We prove

    det (A + diagonal x)
      =
    ∑ S : Finset ι,
      principalMinor A Sᶜ * ∏ i ∈ S, x i.

Mathematically, this is an application of multilinearity of the determinant.

For each row i of

    A + diagonal x,

we choose either

    row_i(A)

or

    row_i(diagonal x) = x_i e_i.

Thus every finite subset S of the index set gives one summand:

* for i ∈ S, choose the diagonal row x_i e_i;
* for i ∉ S, choose the row of A.

The factors x_i come out of the determinant by multilinearity.

After those scalars are removed, the rows indexed by S are identity rows.
They force the corresponding columns, so the remaining determinant is the
principal minor of A indexed by Sᶜ.
-/

open scoped BigOperators

public section

namespace DetDiagonal

/-!
## Basic assumptions

The first few definitions do not require the whole index type to be finite.
We add `[Fintype ι]` only when the determinant expansion needs it.
-/

variable {ι R : Type*}
variable [DecidableEq ι] [CommRing R]

/--
## 1. Principal minor

`principalMinor A S` is

    det A[S,S].

The subtype `↥S` consists of the indices belonging to `S`.
-/
def principalMinor
    (A : Matrix ι ι R)
    (S : Finset ι) : R :=
  (A.submatrix
      (Subtype.val : (↥S) → ι)
      (Subtype.val : (↥S) → ι)).det

/--
## 2. Mixing rows of two matrices

`mixRows S M N` uses

    row_i(M),  if i ∈ S,
    row_i(N),  if i ∉ S.
-/
def mixRows
    (S : Finset ι)
    (M N : Matrix ι ι R) : Matrix ι ι R :=
  Matrix.of (S.piecewise M.row N.row)

/-!
## 3. A row of a diagonal matrix

The i-th row of `diagonal x` is

    x_i e_i,

where `e_i` is the i-th row of the identity matrix.
-/

lemma row_diagonal_eq_smul_row_one
    (x : ι → R)
    (i : ι) :
    (Matrix.diagonal x).row i =
      x i • (1 : Matrix ι ι R).row i := by
  ext j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-!
From here onward we need `ι` to be finite.
-/

variable [Fintype ι]

/-!
## 4. Determinant as a multilinear map of the rows

Mathlib represents the determinant as an alternating map

    Matrix.detRowAlternating.

Its associated multilinear map is used by general results about
multilinearity.

This lemma connects a family of rows with the ordinary matrix determinant.
-/

lemma det_of_rows
    (r : ι → ι → R) :
    (Matrix.of r).det =
      (Matrix.detRowAlternating
        (n := ι) (R := R)).toMultilinearMap r := by
  rfl

/-!
## 5. Identity rows leave a principal minor

Suppose the rows indexed by `S` are identity rows and all remaining rows
come from `A`.

Then

    det(mixed matrix) = det A[Sᶜ,Sᶜ].

The identity rows force the same columns, leaving precisely the complementary
principal submatrix.
-/

lemma det_mixRows_one
    (A : Matrix ι ι R)
    (S : Finset ι) :
    (mixRows S (1 : Matrix ι ι R) A).det =
      principalMinor A Sᶜ := by
  simpa [mixRows, principalMinor, Finset.piecewise_compl] using
    (Matrix.det_piecewise_one_eq_submatrix_det A (Sᶜ))

/-!
## 6. Contribution of one fixed subset

Fix `S`.

On every index `i ∈ S`, the chosen diagonal row is

    x_i e_i.

Multilinearity lets us pull out all the scalars:

    ∏ i ∈ S, x_i.

The remaining determinant has identity rows on `S`, and therefore equals
the principal minor on `Sᶜ`.
-/

lemma det_mixRows_diagonal
    (A : Matrix ι ι R)
    (x : ι → R)
    (S : Finset ι) :
    (mixRows S (Matrix.diagonal x) A).det =
      principalMinor A Sᶜ * ∏ i ∈ S, x i := by
  /-
  `f` is the determinant viewed as a multilinear map of its rows.
  Using this single object consistently avoids coercion issues between
  alternating maps and multilinear maps.
  -/
  let f : MultilinearMap R (fun _ : ι => ι → R) R :=
    (Matrix.detRowAlternating
      (n := ι) (R := R)).toMultilinearMap
  /-
  `m` has identity rows on `S` and rows of `A` outside `S`.
  -/
  let m : ι → (ι → R) :=
    S.piecewise (1 : Matrix ι ι R).row A.row
  /-
  Multiplying the identity row at index `i ∈ S` by `x i` gives exactly
  the corresponding row of the diagonal matrix.
  -/
  have hm :
      S.piecewise (fun i => x i • m i) m =
        S.piecewise (Matrix.diagonal x).row A.row := by
    funext i
    by_cases hi : i ∈ S
    · simp [m, hi,
        row_diagonal_eq_smul_row_one (x := x) (i := i)]
    · simp [m, hi]
  /-
  Multilinearity pulls all factors `x i` with `i ∈ S` outside the
  determinant.
  -/
  have hscale :
      f
          (S.piecewise
            (Matrix.diagonal x).row
            A.row)
        =
      (∏ i ∈ S, x i) • f m := by
    have h :=
      MultilinearMap.map_piecewise_smul
        f x m S
    rw [hm] at h
    exact h
  calc
    /-
    Interpret the determinant of the mixed matrix as `f` applied to
    its family of rows.
    -/
    (mixRows S (Matrix.diagonal x) A).det
        =
        f
          (S.piecewise
            (Matrix.diagonal x).row
            A.row) := by
      simpa [mixRows, f] using
        (det_of_rows
          (R := R)
          (r :=
            S.piecewise
              (Matrix.diagonal x).row
              A.row))
    /-
    Pull the scalars out by multilinearity.
    -/
    _ =
        (∏ i ∈ S, x i) * f m := by
      simpa using hscale
    /-
    Convert `m` back to the matrix with identity rows on `S`.
    -/
    _ =
        (∏ i ∈ S, x i) *
          (mixRows S (1 : Matrix ι ι R) A).det := by
      apply congrArg
        (fun y : R => (∏ i ∈ S, x i) * y)
      simpa [m, mixRows, f] using
        (det_of_rows
          (R := R)
          (r :=
            S.piecewise
              (1 : Matrix ι ι R).row
              A.row)).symm
    /-
    Identity rows leave the complementary principal minor.
    -/
    _ =
        (∏ i ∈ S, x i) *
          principalMinor A Sᶜ := by
      rw [det_mixRows_one (A := A) (S := S)]
    /-
    Commute the two scalar factors to match the desired statement.
    -/
    _ =
        principalMinor A Sᶜ *
          ∏ i ∈ S, x i := by
      ac_rfl

/-!
## 7. Main determinant identity

Each row of

    diagonal x + A

is the sum

    row_i(diagonal x) + row_i(A).

The determinant is multilinear in the rows. Therefore it expands into one
summand for every finite subset `S`:

    i ∈ S     -> choose the diagonal row,
    i ∉ S     -> choose the row of A.

`MultilinearMap.map_add_univ` performs exactly this expansion.

The preceding lemma computes each summand.
-/

theorem det_add_diagonal_formula
    (A : Matrix ι ι R)
    (x : ι → R) :
    (A + Matrix.diagonal x).det =
      ∑ S : Finset ι,
        principalMinor A Sᶜ *
          ∏ i ∈ S, x i := by
  /-
  Again, use one explicit multilinear map for the determinant.
  -/
  let f : MultilinearMap R (fun _ : ι => ι → R) R :=
    (Matrix.detRowAlternating
      (n := ι) (R := R)).toMultilinearMap
  /-
  Expand the determinant multilinearly over all subsets `S`.
  -/
  have hsum :
      f ((Matrix.diagonal x).row + A.row) =
        ∑ S : Finset ι,
          f
            (S.piecewise
              (Matrix.diagonal x).row
              A.row) := by
    exact
      MultilinearMap.map_add_univ
        f
        (Matrix.diagonal x).row
        A.row
  /-
  Adding the two row families gives exactly the rows of the matrix sum.
  -/
  have hmatrix :
      Matrix.of
          ((Matrix.diagonal x).row + A.row)
        =
      Matrix.diagonal x + A := by
    rfl
  /-
  The theorem is written as `A + diagonal x`, while our multilinear
  expansion is naturally written as `diagonal x + A`.
  -/
  rw [add_comm A (Matrix.diagonal x)]
  calc
    /-
    Replace matrix addition with addition of row families.
    -/
    (Matrix.diagonal x + A).det
        =
        (Matrix.of
          ((Matrix.diagonal x).row + A.row)).det := by
      rw [hmatrix]
    /-
    Regard the determinant as the multilinear map `f`.
    -/
    _ =
        f ((Matrix.diagonal x).row + A.row) := by
      simpa [f] using
        (det_of_rows
          (R := R)
          (r :=
            (Matrix.diagonal x).row + A.row))
    /-
    Expand over every subset `S`.
    -/
    _ =
        ∑ S : Finset ι,
          f
            (S.piecewise
              (Matrix.diagonal x).row
              A.row) := hsum
    /-
    Evaluate each summand by the fixed-subset calculation above.
    -/
    _ =
        ∑ S : Finset ι,
          principalMinor A Sᶜ *
            ∏ i ∈ S, x i := by
      refine Finset.sum_congr rfl ?_
      intro S _
      calc
        /-
        Convert the selected row family into `mixRows`.
        -/
        f
            (S.piecewise
              (Matrix.diagonal x).row
              A.row)
            =
            (mixRows
              S
              (Matrix.diagonal x)
              A).det := by
          simpa [f, mixRows] using
            (det_of_rows
              (R := R)
              (r :=
                S.piecewise
                  (Matrix.diagonal x).row
                  A.row)).symm
        /-
        Apply the fixed-subset formula.
        -/
        _ =
            principalMinor A Sᶜ *
              ∏ i ∈ S, x i := by
          exact
            det_mixRows_diagonal
              (A := A)
              (x := x)
              (S := S)

end DetDiagonal

end
