import Mathlib -- imports definitions and theorems used below

/-!
# Sorted Lists

This module defines the property of a list being sorted and provides various
theorems and alternative characterizations, such as monotonicity.
-/

namespace langur -- starts a namespace to group the tutorial definitions
variable {α : Type}[LinearOrder α] -- continues the Lean declaration above

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
      (tail_sorted: Sorted (y :: l)) : Sorted (x :: y :: l) -- continues the surrounding Lean expression

/--
If a list is sorted, its head is less than or equal to all other elements in the list.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem head_le_of_sorted  (a: α) (l : List α) : -- states and proves theorem `head_le_of_sorted`
  Sorted (a :: l) → ∀ x ∈ l, a ≤ x := by -- gives the value or proof for this declaration
  intro h -- introduces hypotheses or variables into the proof context
  match h with -- splits computation into cases by pattern matching
  | Sorted.singleton .. => simp -- handles this pattern-matching case
  | Sorted.step .(a) y l hxy tail_sorted => -- handles this pattern-matching case
    have ih := head_le_of_sorted y l tail_sorted -- records an intermediate fact for the proof
    grind -- asks the `grind` automation to finish the proof

/--
A list is sorted if its tail is sorted and the new head is less than or equal to all elements in the tail.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem cons_sorted (l : List α) :  Sorted l → (a : α) → -- states and proves theorem `cons_sorted`
  (∀ y ∈ l, a ≤ y) → Sorted (a :: l)  := by -- continues the surrounding Lean expression
  intro h₁ a h₀ -- introduces hypotheses or variables into the proof context
  match l with -- splits computation into cases by pattern matching
  | [] => -- handles this pattern-matching case
    apply Sorted.singleton -- reduces the goal using this theorem or constructor
  | x :: l' => -- handles this pattern-matching case
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
  (h₁: i < j) → (h₂ : j < l.length) → -- continues the surrounding Lean expression
    l[i]' (by grind) ≤ l[j]' (by grind) -- continues the Lean declaration above

/--
Every sorted list is monotone.
-/
theorem monotone_of_sorted (l : List α) -- states and proves theorem `monotone_of_sorted`
  (h : Sorted l) : monotone l := by -- continues the surrounding Lean expression
  induction h with -- continues the Lean declaration above
  | nil => grind -- handles this pattern-matching case
  | singleton x => -- handles this pattern-matching case
    grind -- asks the `grind` automation to finish the proof
  | step x y l hxy tail_sorted ih => -- handles this pattern-matching case
    intro i j h₁ h₂ -- introduces hypotheses or variables into the proof context
    cases i with -- splits the proof by cases on this value or proof
    | zero => -- handles this pattern-matching case
      cases j with -- splits the proof by cases on this value or proof
      | zero => contradiction -- handles this pattern-matching case
      | succ j' => -- handles this pattern-matching case
        trans y <;> grind -- continues the Lean declaration above
    | succ i' => -- handles this pattern-matching case
      cases j with -- splits the proof by cases on this value or proof
      | zero => contradiction -- handles this pattern-matching case
      | succ j' => grind -- handles this pattern-matching case

/--
If a list is monotone, its tail is also monotone.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem tail_monotone_of_monotone {y: α} -- states and proves theorem `tail_monotone_of_monotone`
  {ys : List α} (h : monotone (y :: ys)) : -- continues the surrounding Lean expression
  monotone ys := by -- gives the value or proof for this declaration
  intro i j h₁ h₂ -- introduces hypotheses or variables into the proof context
  have h₁' : i + 1 < j + 1 := by -- records an intermediate fact for the proof
    grind -- asks the `grind` automation to finish the proof
  have h₂' : j + 1 < (ys.length + 1) := by -- records an intermediate fact for the proof
    grind -- asks the `grind` automation to finish the proof
  specialize h (i + 1) (j + 1) h₁' h₂' -- continues the Lean declaration above
  grind -- asks the `grind` automation to finish the proof

/--
Every monotone list is sorted.
-/
theorem sorted_of_monotone (l : List α) -- states and proves theorem `sorted_of_monotone`
  (h : monotone l) : Sorted l := by -- continues the surrounding Lean expression
  induction l with -- continues the Lean declaration above
  | nil => apply Sorted.nil -- handles this pattern-matching case
  | cons x xs ih => -- handles this pattern-matching case
    cases xs with -- splits the proof by cases on this value or proof
    | nil => apply Sorted.singleton -- handles this pattern-matching case
    | cons y ys => -- handles this pattern-matching case
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
