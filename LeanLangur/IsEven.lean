import Mathlib -- imports definitions and theorems used below

/-!
## Prerequisite files

* `People.lean` - structures and named fields.
* `BinTree.lean` - inductive types, recursive functions on trees, and membership proofs.

## Main concepts introduced

* inductive propositions.
-/

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

#check IsEven.rec
#check Nat.rec
/--
Zero is even.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem zero_even : IsEven 0 := by -- starts tactic mode for theorem `zero_even`; the following tactics prove the stated goal
  apply zeroEven -- applies `zeroEven` backwards, replacing the current goal by its premises

/--
If `n` is even, then `n + 2` is even.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem addTwo_even (n: Nat) (h: IsEven n) : -- states and proves theorem `addTwo_even`
  IsEven (n + 2) := by -- starts tactic mode; the following tactics prove the proposition just stated
    apply addTwoEven -- applies `addTwoEven` backwards, replacing the current goal by its premises
    assumption -- solves the goal from an existing hypothesis

/--
Twice any natural number is even.
-/

--In this case our `motive` becomes the hypothesis of the theorem.
-- induction on on second part `succ n ih` is simply
-- that `motive n` holds and we need to prove that `motive (succ n)` holds.
theorem IsEven_two_mul (n : Nat) : IsEven (2 * n) := by -- starts tactic mode for theorem `IsEven_two_mul`; the following tactics prove the stated goal
  induction n with
  | zero => apply zeroEven
  | succ n ih => apply addTwoEven ; assumption

/--
The successor of an even number is not even (i.e., it is odd).
-/
theorem succ_odd_of_isEven {n : Nat} -- states and proves theorem `succ_odd_of_isEven`
  (h : IsEven n) :
    ¬ IsEven (n + 1) := by -- starts tactic mode; the following tactics prove the proposition just stated
  induction h with
  | zeroEven => intro h1;contradiction
  | addTwoEven h ih =>
    intro h2
    cases h2 with
    | addTwoEven h3 => exact (ih h3)




/--
For any natural number `n`, either `n` is even or `n + 1` is even.
-/
theorem nOrSuccNeven (n : Nat) : IsEven n ∨ IsEven (n + 1) -- states and proves theorem `nOrSuccNeven`
  := by -- starts tactic mode; the following tactics prove the proposition just stated
  induction n with
  | zero => left; apply zeroEven
  | succ n ih =>
    cases ih with
    | inl h => right; apply addTwoEven; assumption
    | inr h => left; assumption

/-!
## Exercise: Odd numbers

Define an inductive predicate `IsOdd : Nat → Prop` for odd natural numbers,
and prove that any natural number is either even or odd, but not both (As two separate propositions).
-/

inductive IsOdd : Nat → Prop
  | oneOdd : IsOdd 1
  | addTwoOdd (h : IsOdd n) : IsOdd (n + 2)


end langur -- closes the current namespace or section
/-!
## Next files

* `Adder.lean` - typeclasses; instances of typeclasses; typeclass inference. (recommended next file).
-/
