/-
Copyright (c) 2026 University of Washington Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaoda Ji, Joe Rogge, Nhi Bach, David Javnozon, Anders Lewis, Liron Shani, Grant Yang
-/

module

public import DetPoly.Basic

/-!
# Principal submatrices

Convenience API for the principal-minor-map drafts.
-/

public section

variable {n R : Type*}

/-- The principal submatrix `A[S, S]`. -/
abbrev Matrix.principalSubmatrix (A : Matrix n n R) (S : Set n) : Matrix S S R :=
  A.setSubmatrix S S

theorem Matrix.principalSubmatrix_eq_toSquareBlockProp (A : Matrix n n R) (S : Set n) :
    A.principalSubmatrix S = A.toSquareBlockProp (· ∈ S) :=
  rfl

end
