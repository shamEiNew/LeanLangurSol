import Mathlib
/-!
# Smallest element in a list

* We begin with our simplest examples of programs and proofs.
* We show how to add notation.
* We return to this file to see typeclasses in action to generalize from `Nat` to any type with a linear order.

This module is a good starting point for learning how to write simple programs and proofs in Lean 4. The only background required is basic Lean proving as in *A glimpse of Lean*.
-/

namespace langur

namespace nat

/--
A simple, incomplete implementation of the smallest element in a list of natural numbers.
Returns `default` (0) for an empty list.
-/
def smallestI (l: List Nat) : Nat :=
  match l with
  | [x] => x
  | x :: y :: zs =>
    min x (smallestI (y :: zs))
  | [] => default  -- placeholder for empty list

#eval smallestI [3, 1, 4, 1, 5, 9, 2, 6, 5]  -- evaluates to 1

/--
Implementation of the smallest element in a non-empty list of natural numbers.
The non-emptiness is guaranteed by the hypothesis `h`.
-/
def smallest (l: List Nat) (h: l ≠ []) : Nat :=
  match l with
  | x :: [] => x
  | x :: y :: zs =>
    min x (smallest (y :: zs) (by simp))

/--
The element returned by `smallest` is indeed a member of the list.
-/
theorem smallest_mem (l: List Nat) (h: l ≠ []) :
    smallest l h ∈ l := by
  fun_induction smallest <;> grind

/--
The element returned by `smallest` is less than or equal to all elements in the list.
-/
theorem smallest_le_all (l: List Nat) (h: l ≠ []) (x: Nat) :
    x ∈ l → smallest l h ≤ x := by
  fun_induction smallest <;> grind

#eval smallest [3, 1, 4, 1, 5, 9, 2, 6, 5] (by simp) -- evaluates to 1

/--
A macro to call `smallest` and automatically discharge the non-emptiness proof for literals.
-/
macro "smallest%" l:term : term => do
  `(smallest $l (by simp))

#eval smallest% [3, 1, 4, 1, 5, 9, 2, 6, 5] -- evaluates to 1

#print smallest_mem

#print smallest_mem._proof_1_2
#print smallest_mem._proof_1_3
#print smallest.induct_unfolding


/-!
## Exercise: Show that the properties characterizing the smallest element uniquely determine it.

Fill in the `sorry` below with a proof that if `y` is an element of the list `l` and is less than or equal to all elements of `l`, then `y` must be equal to `smallest l h`.

The tactic `fun_induction` is not enough here. You will need to do a more manual induction on the structure of the list, and further case analysis on the structure of the list in the inductive step. You can use `cases` or `match` for this.
-/
abbrev IsSmallest (l: List Nat) (x: Nat) : Prop :=
  x ∈ l ∧ ∀ y, y ∈ l → x ≤ y

theorem smallest_unique (l: List Nat) (h: l ≠ []) (y: Nat) :
    IsSmallest l y → y = smallest l h := by
    sorry

end nat
/-!
Continue to the file `ListOps.lean`.
-/

end langur
