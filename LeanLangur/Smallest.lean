import Mathlib
/-!
# Smallest element in a list

* We begin with our simplest examples of programs and proofs.
* We show how to add notation.
* We return to this file to see typeclasses in action to generalize from `Nat` to any type with a linear order.
-/

namespace nat
def smallestI (l: List Nat) : Nat :=
  match l with
  | [x] => x
  | x :: y :: zs =>
    min x (smallestI (y :: zs))
  | [] => default  -- placeholder for empty list

#eval smallestI [3, 1, 4, 1, 5, 9, 2, 6, 5]  -- evaluates to 1

def smallest (l: List Nat) (h: l ≠ []) : Nat :=
  match l with
  | x :: [] => x
  | x :: y :: zs =>
    min x (smallest (y :: zs) (by simp))

theorem smallest_mem (l: List Nat) (h: l ≠ []) :
    smallest l h ∈ l := by
  fun_induction smallest <;> grind

theorem smallest_le_all (l: List Nat) (h: l ≠ []) (x: Nat) :
    x ∈ l → smallest l h ≤ x := by
  fun_induction smallest <;> grind

#eval smallest [3, 1, 4, 1, 5, 9, 2, 6, 5] (by simp) -- evaluates to 1

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

def smallest  (l: List α) (h: l ≠ []) : α :=
  match l with
  | x :: [] => x
  | x :: y :: zs =>
    min x (smallest (y :: zs) (by simp))

theorem smallest_mem (l: List α) (h: l ≠ []) :
    smallest l h ∈ l := by
  fun_induction smallest <;> grind

theorem smallest_le_all (l: List α) (h: l ≠ []) (x: α) :
    x ∈ l → smallest l h ≤ x := by
  fun_induction smallest <;> grind

end general
