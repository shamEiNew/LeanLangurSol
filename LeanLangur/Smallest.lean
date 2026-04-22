import Mathlib
/-!
# Smallest element in a list

* We begin with our simplest examples of programs and proofs.
* We show how to add notation.
* We return to this file to see typeclasses in action to generalize from `Nat` to any type with a linear order.
-/

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
end nat

namespace general

variable {α : Type} [LinearOrder α]

/--
Implementation of the smallest element in a non-empty list for any type with a linear order.
-/
def smallest  (l: List α) (h: l ≠ []) : α :=
  match l with
  | x :: [] => x
  | x :: y :: zs =>
    min x (smallest (y :: zs) (by simp))

/--
The element returned by `smallest` is indeed a member of the list.
-/
theorem smallest_mem (l: List α) (h: l ≠ []) :
    smallest l h ∈ l := by
  fun_induction smallest <;> grind

/--
The element returned by `smallest` is less than or equal to all elements in the list.
-/
theorem smallest_le_all (l: List α) (h: l ≠ []) (x: α) :
    x ∈ l → smallest l h ≤ x := by
  fun_induction smallest <;> grind

end general
