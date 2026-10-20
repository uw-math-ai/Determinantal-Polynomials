module

public import Mathlib

public section


open Matrix

variable {R n : Type*} [Fintype n] [Field R] [DecidableEq n]

#check Matrix.submatrix

#check MvPolynomial
#check Matrix.inv
#check Matrix.transpose
#check Matrix.diagonal

#check Matrix.det

-- should this be a struct or abbrev or something?
-- also, is this already in mathlib anywhere?
def diagEquiv (M N : Matrix n n R) : Prop :=
  ∃(d : n → R), M = (diagonal d) * N * (diagonal d)⁻¹ ∨ M = (diagonal d) * Nᵀ * (diagonal d)⁻¹

theorem diagInv {d : n → R} : (diagonal d)⁻¹ = (diagonal <| fun x ↦ (d x)⁻¹) := by
  -- this definitely feels like it should be in mathlib
  -- investigate how i should be using the mathlib diagonal matrix apis.
  sorry


theorem equiv : Equivalence (@diagEquiv R n _ _ _) where
  refl _ := by
    use fun _ ↦ 1
    simp
  symm := by
    intro M N h
    obtain ⟨d, hd⟩ := h
    use fun x ↦ (d x)⁻¹
    rcases hd with hl | hr
    · left
      rw [hl]
      sorry
    · sorry
  trans := by
    intro M N O hMN hNO
    sorry
  


#check Matrix.IsIrreducible

-- + Reducible implies permutes to upper triangular block matrix?
-- is that in mathlib and what is the best way to express that

section

variable {m : Type*} [Fintype m]

def Matrix.indexSubset (mat : Matrix m n R) (I : Finset m) (J : Finset n) :
    Matrix { x // x ∈ I} {x // x ∈ J} R :=
  mat.submatrix Subtype.val Subtype.val

end

end


section 

open Ring Polynomial Finset

#check Polynomial ℚ 
-- why are polynomials noncomputable in mathlib?
-- what is the recommended strategy for dealing with computation with polynomials,
-- as we would like to implement the algo for finding a second matrix in the fiber in a computable way.
noncomputable def test : ℚ[X] := X


variable {σ R : Type*} [CommSemiring R]

-- is there a clean way to work with affine polynomials?
-- if there are clean affine polynomials, use that instead of MvPolynomial i guess
-- otherwise, how do we define it cleanly?
-- Like would something like AddMonoidAlgebra R (Finset σ) be a good idea? Or (σ → Bool) or something? Better type than bool?
#check MvPolynomial
#check Polynomial
#check Finsupp

-- is there some way to do this in mathlib?
-- this feels awful and wrong.
-- or should i just not do this and express "x_k never appears" using a hypothesis on my shit
def isolate (var : σ) : MvPolynomial σ R →+* (MvPolynomial σ R)[X] where
  toFun p := ∑ f ∈ p.support, if (f var ≠ 0) then -- idk man something 
  map_one' := by
    sorry
  map_zero' := by
    sorry


-- is the definition of resultant wrt a single variable from the paper in mathlib? 
#check Polynomial.resultant


-- partial deriv of mvpolynomial or affine polynomial?
-- + formal second deriv.
#check MvPolynomial.deriv
#check Polynomial.deriv 


end
