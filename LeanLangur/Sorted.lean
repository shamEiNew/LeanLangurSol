import Mathlib -- imports definitions and theorems used below

/-!
# Sorted Lists

This module defines the property of a list being sorted and provides various
theorems and alternative characterizations, such as monotonicity.
-/

namespace langur -- starts a namespace to group the tutorial definitions
variable {α : Type}[LinearOrder α]

/--
Inductive predicate for a sorted list.
* The empty list is sorted.
* A single-element list is sorted.
* A list starting with `x` and `y` is sorted if `x ≤ y` and the tail starting with `y` is sorted.
-/
@[grind cases] -- annotation controlling elaboration, simplification, or automation
inductive Sorted : List α → Prop -- declares the inductive type or proposition `Sorted`
  | nil : Sorted [] -- declares another constructor or syntax alternative
  | singleton (x : α) : Sorted [x] -- declares another constructor or syntax alternative
  | step (x y : α) (l : List α) (hxy: x ≤ y) -- declares another constructor or syntax alternative
      (tail_sorted: Sorted (y :: l)) : Sorted (x :: y :: l)

/--
If a list is sorted, its head is less than or equal to all other elements in the list.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem head_le_of_sorted  (a: α) (l : List α) : -- states and proves theorem `head_le_of_sorted`
  Sorted (a :: l) → ∀ x ∈ l, a ≤ x := by -- gives the value or proof for this declaration
  intro h -- introduces hypotheses or variables into the proof context
  match h with -- splits computation into cases by pattern matching
  | Sorted.singleton .. => simp -- matches a sorted singleton list proof and simplifies this proof case
  | Sorted.step .(a) y l hxy tail_sorted => -- matches a sorted list built from a head and sorted tail and proves this case using the following proof steps
    have ih := head_le_of_sorted y l tail_sorted -- records an intermediate fact for the proof
    grind -- asks the `grind` automation to finish the proof

/--
A list is sorted if its tail is sorted and the new head is less than or equal to all elements in the tail.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem cons_sorted (l : List α) :  Sorted l → (a : α) → -- states and proves theorem `cons_sorted`
  (∀ y ∈ l, a ≤ y) → Sorted (a :: l)  := by
  intro h₁ a h₀ -- introduces hypotheses or variables into the proof context
  match l with -- splits computation into cases by pattern matching
  | [] => -- matches the empty list and proves this case with the tactic steps below
    apply Sorted.singleton -- reduces the goal using this theorem or constructor
  | x :: l' => -- matches a nonempty list and proves this case with the tactic steps below
    grind [Sorted.step] -- asks the `grind` automation to finish the proof

/-!
## Sorted lists and monotone lists

We in some sense axiomatized the property of being sorted by saying that the head is less than or equal to the next element, and so on. We can also give an alternative characterization of sorted lists by saying that a list is sorted if it is monotone (i.e., non-decreasing). We show that these two characterizations are equivalent.

Such results are useful in making sure that our definitions are robust and capture the intended concept. They also allow us to use whichever characterization is more convenient in a given proof.
-/
/--
Predicate for checking if a list is monotone (non-decreasing).
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
def monotone (l : List α) : Prop := ∀ i j, -- defines `monotone`
  (h₁: i < j) → (h₂ : j < l.length) →
    l[i]' (by grind) ≤ l[j]' (by grind)

/--
Every sorted list is monotone.
-/
theorem monotone_of_sorted (l : List α) -- states and proves theorem `monotone_of_sorted`
  (h : Sorted l) : monotone l := by
  induction h with
  | nil => grind -- matches the empty list and asks `grind` to solve this case
  | singleton x => -- matches a sorted singleton list proof and proves this case with the tactic steps below
    grind -- asks the `grind` automation to finish the proof
  | step x y l hxy tail_sorted ih => -- matches a sorted list built from a head and sorted tail and returns `intro i j h₁ h₂`
    intro i j h₁ h₂ -- introduces hypotheses or variables into the proof context
    cases i with -- splits the proof by cases on this value or proof
    | zero => -- matches zero and returns `cases j with`
      cases j with -- splits the proof by cases on this value or proof
      | zero => contradiction -- matches zero and closes the impossible case by contradiction
      | succ j' => -- matches a successor natural number and returns `trans y <;> grind`
        trans y <;> grind
    | succ i' => -- matches a successor natural number and returns `cases j with`
      cases j with -- splits the proof by cases on this value or proof
      | zero => contradiction -- matches zero and closes the impossible case by contradiction
      | succ j' => grind -- matches a successor natural number and asks `grind` to solve this case

/--
If a list is monotone, its tail is also monotone.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem tail_monotone_of_monotone {y: α} -- states and proves theorem `tail_monotone_of_monotone`
  {ys : List α} (h : monotone (y :: ys)) :
  monotone ys := by -- gives the value or proof for this declaration
  intro i j h₁ h₂ -- introduces hypotheses or variables into the proof context
  have h₁' : i + 1 < j + 1 := by -- records an intermediate fact for the proof
    grind -- asks the `grind` automation to finish the proof
  have h₂' : j + 1 < (ys.length + 1) := by -- records an intermediate fact for the proof
    grind -- asks the `grind` automation to finish the proof
  specialize h (i + 1) (j + 1) h₁' h₂'
  grind -- asks the `grind` automation to finish the proof

/--
Every monotone list is sorted.
-/
theorem sorted_of_monotone (l : List α) -- states and proves theorem `sorted_of_monotone`
  (h : monotone l) : Sorted l := by
  induction l with
  | nil => apply Sorted.nil -- matches the empty list and applies Sorted.nil
  | cons x xs ih => -- matches a nonempty list and returns `cases xs with`
    cases xs with -- splits the proof by cases on this value or proof
    | nil => apply Sorted.singleton -- matches the empty list and applies Sorted.singleton
    | cons y ys => -- matches a nonempty list and proves this case with the tactic steps below
      apply Sorted.step -- reduces the goal using this theorem or constructor
      · apply h 0 1 (by simp) (by simp) -- focuses the next proof branch
      · grind -- focuses the next proof branch

/-!
## Exercise: Sorted lists with equal counts

Suppose we have two lists `l₁` and `l₂` such that:

* Both lists are sorted.
* Both lists contain the same elements with the same multiplicities (i.e., for every element `x`, the count of `x` in `l₁` is the same as the count of `x` in `l₂`).

Show that `l₁ = l₂`. You may find it useful to first show that the head of both lists must be the same, and then use induction on the tail of the lists.
-/

end langur -- closes the current namespace or section
