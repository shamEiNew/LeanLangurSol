import Mathlib
/-!
# Smallest element in a list

* We begin with our simplest examples of programs and proofs.
* We show how to add notation.
* We return to this file to see typeclasses in action to generalize from `Nat` to any type with a linear order.
-/

namespace langur

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

end langur
