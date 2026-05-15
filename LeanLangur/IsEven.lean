import Mathlib -- imports definitions and theorems used below

/-!
# Even Natural Numbers

This module defines the property of being an even natural number using an inductive predicate
and provides several proofs about even numbers.
-/

namespace langur -- starts a namespace to group the tutorial definitions

/--
Inductive predicate for even natural numbers.
* `0` is even.
* If `n` is even, then `n + 2` is even.
-/
@[grind cases] -- annotation controlling elaboration, simplification, or automation
inductive IsEven : Nat → Prop -- declares the inductive type or proposition `IsEven`
  | zeroEven : IsEven 0 -- declares another constructor or syntax alternative
  | addTwoEven (h : IsEven n) : IsEven (n + 2) -- declares another constructor or syntax alternative

open IsEven -- opens names so constructors or helpers can be written unqualified

/--
Zero is even.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem zero_even : IsEven 0 := by -- states and proves theorem `zero_even`
  apply zeroEven -- reduces the goal using this theorem or constructor

/--
If `n` is even, then `n + 2` is even.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem addTwo_even (n: Nat) (h: IsEven n) : -- states and proves theorem `addTwo_even`
  IsEven (n + 2) := by -- gives the value or proof for this declaration
    apply addTwoEven -- reduces the goal using this theorem or constructor
    assumption -- solves the goal from an existing hypothesis

/--
Twice any natural number is even.
-/
theorem IsEven_two_mul (n : Nat) : IsEven (2 * n) := by -- states and proves theorem `IsEven_two_mul`
  induction n <;> grind

/--
The successor of an even number is not even (i.e., it is odd).
-/
theorem succ_odd_of_isEven {n : Nat} -- states and proves theorem `succ_odd_of_isEven`
  (h : IsEven n) :
    ¬ IsEven (n + 1) := by -- gives the value or proof for this declaration
  induction h <;> grind

/--
For any natural number `n`, either `n` is even or `n + 1` is even.
-/
theorem nOrSuccNeven (n : Nat) : IsEven n ∨ IsEven (n + 1) -- states and proves theorem `nOrSuccNeven`
  := by -- gives the value or proof for this declaration
  induction n <;> grind

/-!
## Exercise: Odd numbers

Define an inductive predicate `IsOdd : Nat → Prop` for odd natural numbers, and prove that any natural number is either even or odd, but not both (As two separate propositions).
-/
end langur -- closes the current namespace or section
