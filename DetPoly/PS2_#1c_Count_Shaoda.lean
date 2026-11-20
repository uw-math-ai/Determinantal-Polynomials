import Mathlib

/-!
# Counting argument for the diagonal determinant expansion

This file formalizes the counting argument from the handwritten proof.

The determinant identity itself is proved separately.  Here we focus only on
the number of terms.

The handwritten proof introduces two numbers:

    Aₙ = number of terms in
         det(A + diag(x₁, ..., xₙ)),

and

    Bₙ = number of terms in
         det(A + diag(0, x₂, ..., xₙ)).

Expansion in the first column gives

    Aₙ = Aₙ₋₁ + Bₙ,

and a second expansion gives

    Bₙ = Aₙ₋₁ + (n - 1) Bₙ₋₁.

To avoid predecessor notation in Lean, we index these as

    A_{n+1} = A_n + B_{n+1},

    B_{n+1} = A_n + n B_n.

We start with

    A₀ = 1,
    B₀ = 0.

The value B₀ is only an auxiliary initial value; the first meaningful
identity is B₁ = 1.

From the two recurrences we derive the second-order recurrence

    A_n = (n + 1) A_{n-1} - (n - 1) A_{n-2}.

Since subtraction in ℕ is inconvenient, Lean first proves the equivalent
addition-only form

    A_{n+2} + (n + 1) A_n = (n + 3) A_{n+1}.

Finally we prove

    A_n = ∑_{k=0}^n n! / k!

and verify independently that this agrees with the direct RHS count

    ∑_{k=0}^n binom(n,k) (n-k)!.

Important boundary:

This file formalizes the counting recurrence and its closed form.
It does not yet identify `Acount n` with the support cardinality of a
literal multivariate determinant polynomial.  That support-cardinality
bridge can be added as a third file after the present counting theorem
and the separate determinant theorem are both stable.
-/

open scoped BigOperators

namespace DetCounting

/-!
## 1. The pair (Aₙ, Bₙ)

Because A_{n+1} depends on B_{n+1}, it is convenient to construct
the two sequences simultaneously.

If at stage n we know

    a = A_n,
    b = B_n,

then the handwritten recurrence first gives

    B_{n+1} = a + n b,

and then

    A_{n+1} = a + B_{n+1}.

So one recursion step sends

    (a,b)

to

    (a + b', b'),

where

    b' = a + n b.
-/

def countState : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 =>
      let a := (countState n).1
      let b := (countState n).2
      let b' := a + n * b
      (a + b', b')

/-!
`Acount n` and `Bcount n` are the two components of this state.
-/

def Acount (n : ℕ) : ℕ :=
  (countState n).1

def Bcount (n : ℕ) : ℕ :=
  (countState n).2

/-!
## 2. Initial values

These correspond to the beginning of the handwritten recurrence.
-/

@[simp]
lemma Acount_zero :
    Acount 0 = 1 := by
  rfl

@[simp]
lemma Bcount_zero :
    Bcount 0 = 0 := by
  rfl

@[simp]
lemma Acount_one :
    Acount 1 = 2 := by
  norm_num [Acount, countState]

@[simp]
lemma Bcount_one :
    Bcount 1 = 1 := by
  norm_num [Bcount, countState]

/-!
## 3. The two recurrences from the handwritten proof

The second recurrence, with indices shifted by one, is

    B_{n+1} = A_n + n B_n.
-/

lemma Bcount_succ (n : ℕ) :
    Bcount (n + 1) =
      Acount n + n * Bcount n := by
  simp [Bcount, Acount, countState]

/-!
The first recurrence is

    A_{n+1} = A_n + B_{n+1}.
-/

lemma Acount_succ (n : ℕ) :
    Acount (n + 1) =
      Acount n + Bcount (n + 1) := by
  simp [Acount, Bcount, countState]

/-!
Thus Lean has now recorded exactly the two equations

    A_n = A_{n-1} + B_n,

    B_n = A_{n-1} + (n-1) B_{n-1},

using successor indexing.
-/

/-!
## 4. Eliminate B and obtain the second-order recurrence

The handwritten calculation is

    A_n
      = 2 A_{n-1} + (n-1)(A_{n-1} - A_{n-2})
      = (n+1)A_{n-1} - (n-1)A_{n-2}.

Over natural numbers, subtraction is truncated, so the cleaner formal
statement is the equivalent identity

    A_{n+2} + (n+1) A_n
      = (n+3) A_{n+1}.

This contains exactly the same recurrence information.
-/

lemma Acount_second_order_additive (n : ℕ) :
    Acount (n + 2) + (n + 1) * Acount n =
      (n + 3) * Acount (n + 1) := by
  rw [Acount_succ (n + 1)]
  rw [Bcount_succ (n + 1)]
  rw [Acount_succ n]
  ring

/-!
For reference, after replacing `n + 2` by `m`, this says

    A_m + (m-1) A_{m-2}
      = (m+1) A_{m-1},

which is equivalent to the recurrence written on the page:

    A_m
      = (m+1) A_{m-1}
        - (m-1) A_{m-2}.
-/

/-!
## 5. A useful first-order consequence

The two recurrences imply the particularly simple identity

    B_{n+1} = n A_n + 1.

This is not essential to the handwritten presentation, but it makes the
closed-form proof much cleaner.
-/

lemma Bcount_closed_step (n : ℕ) :
    Bcount (n + 1) =
      n * Acount n + 1 := by
  induction n with
  | zero =>
      norm_num [Acount, Bcount, countState]
  | succ n ih =>
      rw [Bcount_succ (n + 1)]
      rw [Acount_succ n]
      rw [ih]
      ring

/-!
Consequently

    A_{n+1}
      = A_n + B_{n+1}
      = (n+1) A_n + 1.
-/

lemma Acount_first_order (n : ℕ) :
    Acount (n + 1) =
      (n + 1) * Acount n + 1 := by
  rw [Acount_succ n]
  rw [Bcount_closed_step n]
  ring

/-!
A quick consistency check:

    A₀ = 1
    A₁ = 2
    A₂ = 5
    A₃ = 16

exactly as predicted by

    A_{n+1} = (n+1) A_n + 1.
-/

example : Acount 2 = 5 := by
  norm_num [Acount, Bcount, countState]

example : Acount 3 = 16 := by
  norm_num [Acount, Bcount, countState]

/-!
## 6. The closed form from the handwritten proof

The page obtains

    A_n = ∑_{k=0}^n n! / k!.

Because `/` on natural numbers is truncated division, it is cleaner to
state this equality in ℚ.

The left side is still the natural-number count `Acount n`, simply coerced
to ℚ.
-/

def factorialQuotientCount (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.factorial n : ℚ) / (Nat.factorial k : ℚ)

/-!
The closed-form sum satisfies the same first-order recurrence:

    F_{n+1} = (n+1) F_n + 1.

Indeed, separate the final summand k = n+1.  It equals 1.

For all earlier summands,

    (n+1)! / k!
      = (n+1) (n! / k!).
-/

lemma factorialQuotientCount_succ (n : ℕ) :
    factorialQuotientCount (n + 1) =
      (n + 1 : ℚ) * factorialQuotientCount n + 1 := by
  unfold factorialQuotientCount
  rw [Finset.sum_range_succ]
  have hfac :
      (Nat.factorial (n + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  rw [div_self hfac]
  simp only [
    Nat.factorial_succ,
    Nat.cast_mul,
    Nat.cast_add,
    Nat.cast_one
  ]
  rw [Finset.mul_sum]
  apply congrArg (fun z : ℚ => z + 1)
  refine Finset.sum_congr rfl ?_
  intro k _
  simp only [div_eq_mul_inv]
  ring

/-!
Now both `Acount` and the factorial sum satisfy

    X_{n+1} = (n+1) X_n + 1

and both begin at 1.

Induction therefore proves the desired formula.
-/

theorem Acount_eq_factorialQuotientCount (n : ℕ) :
    (Acount n : ℚ) =
      factorialQuotientCount n := by
  induction n with
  | zero =>
      norm_num [Acount, countState, factorialQuotientCount]
  | succ n ih =>
      calc
        (Acount (n + 1) : ℚ)
            =
            (((n + 1) * Acount n + 1 : ℕ) : ℚ) := by
          rw [Acount_first_order n]
        _ =
            (n + 1 : ℚ) * (Acount n : ℚ) + 1 := by
          norm_num
        _ =
            (n + 1 : ℚ) * factorialQuotientCount n + 1 := by
          rw [ih]
        _ =
            factorialQuotientCount (n + 1) := by
          symm
          exact factorialQuotientCount_succ n

/-!
This is the explicit version matching the final line of the handwritten page:

    A_n = Σ_{k=0}^n n! / k!.
-/

theorem Acount_closed_form (n : ℕ) :
    (Acount n : ℚ) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.factorial n : ℚ) /
          (Nat.factorial k : ℚ) := by
  exact Acount_eq_factorialQuotientCount n

/-!
## 7. Count the terms on the proposed right-hand side

For every k:

* there are `choose n k` subsets I of size k;
* the complementary principal minor has size n-k;
* treating all matrix entries as independent indeterminates, its determinant
  expansion has `(n-k)!` permutation terms.

Thus the direct combinatorial count is

    Σ_{k=0}^n choose(n,k) (n-k)!.
-/

def rhsTermCount (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    n.choose k * Nat.factorial (n - k)

/-!
The key arithmetic identity is

    choose(n,k) (n-k)! = n! / k!.

Again we state the quotient in ℚ.

Mathlib already knows

    choose(n,k) k! (n-k)! = n!.

We divide this identity by k!.
-/

lemma choose_mul_complement_factorial
    (n k : ℕ)
    (hk : k ≤ n) :
    ((n.choose k * Nat.factorial (n - k) : ℕ) : ℚ) =
      (Nat.factorial n : ℚ) /
        (Nat.factorial k : ℚ) := by
  have h :=
    Nat.choose_mul_factorial_mul_factorial
      (n := n) (k := k) hk
  have hkfac :
      (Nat.factorial k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [eq_div_iff hkfac]
  exact_mod_cast
    (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h)

/-!
Summing the preceding identity over all `0 ≤ k ≤ n` proves that the direct
RHS count is exactly the factorial-quotient sum.
-/

theorem rhsTermCount_cast_eq_factorialQuotientCount
    (n : ℕ) :
    (rhsTermCount n : ℚ) =
      factorialQuotientCount n := by
  unfold rhsTermCount factorialQuotientCount
  push_cast
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hklt : k < n + 1 :=
    Finset.mem_range.mp hk
  have hkle : k ≤ n := by
    omega
  simpa using
    choose_mul_complement_factorial n k hkle

/-!
## 8. Final counting theorem

We have proved, independently,

    A_n = Σ n!/k!

and

    RHS term count = Σ n!/k!.

Therefore the recurrence count `A_n` agrees with the direct count of the
proposed right-hand side.
-/

theorem Acount_eq_rhsTermCount (n : ℕ) :
    Acount n = rhsTermCount n := by
  have hA :
      (Acount n : ℚ) =
        factorialQuotientCount n :=
    Acount_eq_factorialQuotientCount n
  have hR :
      (rhsTermCount n : ℚ) =
        factorialQuotientCount n :=
    rhsTermCount_cast_eq_factorialQuotientCount n
  have h :
      (Acount n : ℚ) =
        (rhsTermCount n : ℚ) :=
    hA.trans hR.symm
  exact_mod_cast h

/-!
So the formal counting result is

    A_n
      =
    Σ_{k=0}^n choose(n,k) (n-k)!
      =
    Σ_{k=0}^n n! / k!.

The first equality lives naturally in ℕ.

The second equality is displayed in ℚ so that the quotient notation means
ordinary exact division.
-/

theorem counting_argument_final_nat (n : ℕ) :
    Acount n =
      ∑ k ∈ Finset.range (n + 1),
        n.choose k * Nat.factorial (n - k) := by
  exact Acount_eq_rhsTermCount n

theorem counting_argument_final_factorial (n : ℕ) :
    (Acount n : ℚ) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.factorial n : ℚ) /
          (Nat.factorial k : ℚ) := by
  exact Acount_closed_form n

end DetCounting
