import Mathlib
/-!
# Examples of programs and in Lean

We see our first examples of programs and proofs in Lean. A major goal is to illustrate *functional programming*, where we use recursions for loops and avoid mutable variables.

We define recursively summing to `n` and prove a theorem about it.
-/

/--
The function `sumToN` computes the sum of the first `n` natural numbers.
-/
def sumToN (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | m + 1 =>
    (sumToN m) + (m + 1)

#eval sumToN 10 -- 55

namespace concise
def sumToN : Nat → Nat
| 0 => 0
| m + 1 => (sumToN m) + (m + 1)
end concise

/--
The theorem `sumToN_eq` states that the sum of the first `n` natural numbers is `n * (n + 1) / 2`.
-/
theorem sumToN_eq (n: Nat) : 2 * sumToN n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ m ih => grind [sumToN]

def sumToNcond (n: Nat) : Nat :=
  if n = 0 then 0 else (sumToNcond (n - 1)) + n

#eval sumToNcond 10 -- 55

#eval (0  - 1) + 1 -- 1

/--
error: fail to show termination for
  sumToNcondBad
with errors
failed to infer structural recursion:
Not considering parameter n of sumToNcondBad:
  it is unchanged in the recursive calls
no parameters suitable for structural recursion

well-founded recursion cannot be used, `sumToNcondBad` does not take any (non-fixed) arguments
-/
#guard_msgs in
def sumToNcondBad (n: Int) : Nat :=
  sumToNcondBad n

/--
error: fail to show termination for
  sumToNint
with errors
failed to infer structural recursion:
Cannot use parameter n:
  the type ℤ does not have a `.brecOn` recursor


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : ℤ
h✝ : ¬n = 0
⊢ sizeOf (n - 1) < sizeOf n
-/
#guard_msgs in
def sumToNint (n: Int) : Int :=
  if n = 0 then 0 else (sumToNint (n - 1)) + n

partial def sumToNintLoopy (n: Int) : Int :=
  if n = 0 then 0 else (sumToNintLoopy (n - 1)) + n

/-!
Lean allows imperative programming, but it is not recommended. Here is an example of a program that uses a mutable variable.
-/
def sumToNImperative (n: Nat) : Nat :=
  Id.run do
    let mut sum := 0
    for i in [1:n+1] do
      sum := sum + i
    return sum

/--
error: fail to show termination for
  sumToN''
with errors
failed to infer structural recursion:
Cannot use parameter n:
  the type ℤ does not have a `.brecOn` recursor


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : ℤ
h✝ : ¬n = 0
⊢ sizeOf (n - 1) < sizeOf n
-/
#guard_msgs in
def sumToN'' (n: Int) : Int :=
  if n = 0 then 0 else (sumToN'' (n - 1)) + n

open Nat
theorem exists_infinite_primes' (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (n ! + 1)
  use p
  constructor
  · apply le_of_not_ge
    intro h
    apply Nat.Prime.not_dvd_one
    · have f1 : n ! + 1 ≠ 1 := by
        simp [Nat.ne_of_gt, factorial_pos]
      apply minFac_prime f1
    · have h₁ : p ∣ n ! := by
        apply dvd_factorial
        apply minFac_pos
        exact h
      rw [Nat.dvd_add_iff_right h₁]
      apply minFac_dvd
  · apply minFac_prime
    simp [Nat.ne_of_gt, factorial_pos]

theorem exists_infinite_primes'' (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p :=
  let p := minFac (n ! + 1)
  have f1 : n ! + 1 ≠ 1 := Nat.ne_of_gt (succ_lt_succ ( factorial_pos (n)))
  have pp : Nat.Prime p := minFac_prime (f1)
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ n ! := dvd_factorial (minFac_pos (n ! + 1)) (h)
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd (n ! + 1))
      pp.not_dvd_one (h₂)
  ⟨p, np, pp⟩
