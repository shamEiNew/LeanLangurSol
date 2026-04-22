import Mathlib

/-!
# Even Natural Numbers

This module defines the property of being an even natural number using an inductive predicate
and provides several proofs about even numbers.
-/

/--
Inductive predicate for even natural numbers.
* `0` is even.
* If `n` is even, then `n + 2` is even.
-/
@[grind cases]
inductive IsEven : Nat → Prop
  | zeroEven : IsEven 0
  | addTwoEven (h : IsEven n) : IsEven (n + 2)

open IsEven

/--
Zero is even.
-/
@[grind .]
theorem zero_even : IsEven 0 := by
  apply zeroEven

/--
If `n` is even, then `n + 2` is even.
-/
@[grind .]
theorem addTwo_even (n: Nat) (h: IsEven n) :
  IsEven (n + 2) := by
    apply addTwoEven
    assumption

/--
Twice any natural number is even.
-/
theorem IsEven_two_mul (n : Nat) : IsEven (2 * n) := by
  induction n <;> grind

/--
The successor of an even number is not even (i.e., it is odd).
-/
theorem succ_odd_of_isEven {n : Nat}
  (h : IsEven n) :
    ¬ IsEven (n + 1) := by
  induction h <;> grind

/--
For any natural number `n`, either `n` is even or `n + 1` is even.
-/
theorem nOrSuccNeven (n : Nat) : IsEven n ∨ IsEven (n + 1)
  := by
  induction n <;> grind
