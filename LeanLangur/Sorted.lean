import Mathlib

/-!
# Sorted Lists

This module defines the property of a list being sorted and provides various
theorems and alternative characterizations, such as monotonicity.
-/

namespace langur
variable {α : Type}[LinearOrder α]

/--
Inductive predicate for a sorted list.
* The empty list is sorted.
* A single-element list is sorted.
* A list starting with `x` and `y` is sorted if `x ≤ y` and the tail starting with `y` is sorted.
-/
@[grind cases]
inductive Sorted : List α → Prop
  | nil : Sorted []
  | singleton (x : α) : Sorted [x]
  | step (x y : α) (l : List α) (hxy: x ≤ y)
      (tail_sorted: Sorted (y :: l)) : Sorted (x :: y :: l)

/--
If a list is sorted, its head is less than or equal to all other elements in the list.
-/
@[grind .]
theorem head_le_of_sorted  (a: α) (l : List α) :
  Sorted (a :: l) → ∀ x ∈ l, a ≤ x := by
  intro h
  match h with
  | Sorted.singleton .. => simp
  | Sorted.step .(a) y l hxy tail_sorted =>
    have ih := head_le_of_sorted y l tail_sorted
    grind

/--
A list is sorted if its tail is sorted and the new head is less than or equal to all elements in the tail.
-/
@[grind .]
theorem cons_sorted (l : List α) :  Sorted l → (a : α) →
  (∀ y ∈ l, a ≤ y) → Sorted (a :: l)  := by
  intro h₁ a h₀
  match l with
  | [] =>
    apply Sorted.singleton
  | x :: l' =>
    grind [Sorted.step]

/-!
## Sorted lists and monotone lists

We in some sense axiomatized the property of being sorted by saying that the head is less than or equal to the next element, and so on. We can also give an alternative characterization of sorted lists by saying that a list is sorted if it is monotone (i.e., non-decreasing). We show that these two characterizations are equivalent.

Such results are useful in making sure that our definitions are robust and capture the intended concept. They also allow us to use whichever characterization is more convenient in a given proof.
-/
/--
Predicate for checking if a list is monotone (non-decreasing).
-/
@[grind .]
def monotone (l : List α) : Prop := ∀ i j,
  (h₁: i < j) → (h₂ : j < l.length) →
    l[i]' (by grind) ≤ l[j]' (by grind)

/--
Every sorted list is monotone.
-/
theorem monotone_of_sorted (l : List α)
  (h : Sorted l) : monotone l := by
  induction h with
  | nil => grind
  | singleton x =>
    grind
  | step x y l hxy tail_sorted ih =>
    intro i j h₁ h₂
    cases i with
    | zero =>
      cases j with
      | zero => contradiction
      | succ j' =>
        trans y <;> grind
    | succ i' =>
      cases j with
      | zero => contradiction
      | succ j' => grind

/--
If a list is monotone, its tail is also monotone.
-/
@[grind .]
theorem tail_monotone_of_monotone {y: α}
  {ys : List α} (h : monotone (y :: ys)) :
  monotone ys := by
  intro i j h₁ h₂
  have h₁' : i + 1 < j + 1 := by
    grind
  have h₂' : j + 1 < (ys.length + 1) := by
    grind
  specialize h (i + 1) (j + 1) h₁' h₂'
  grind

/--
Every monotone list is sorted.
-/
theorem sorted_of_monotone (l : List α)
  (h : monotone l) : Sorted l := by
  induction l with
  | nil => apply Sorted.nil
  | cons x xs ih =>
    cases xs with
    | nil => apply Sorted.singleton
    | cons y ys =>
      apply Sorted.step
      · apply h 0 1 (by simp) (by simp)
      · grind

/-!
## Exercise: Sorted lists with equal counts

Suppose we have two lists `l₁` and `l₂` such that:

* Both lists are sorted.
* Both lists contain the same elements with the same multiplicities (i.e., for every element `x`, the count of `x` in `l₁` is the same as the count of `x` in `l₂`).

Show that `l₁ = l₂`. You may find it useful to first show that the head of both lists must be the same, and then use induction on the tail of the lists.
-/

end langur
