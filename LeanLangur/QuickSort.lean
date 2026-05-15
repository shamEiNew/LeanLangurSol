import Mathlib.Data.List.Basic -- imports definitions and theorems used below
import Mathlib.Tactic -- imports definitions and theorems used below
import LeanLangur.Basic -- imports definitions and theorems used below
import LeanLangur.Sorted -- imports definitions and theorems used below
/-!
## Quicksort Algorithm (Pivot from Head)

Quicksort is a divide-and-conquer sorting algorithm known for its efficiency. It works by recursively partitioning the list around a chosen element (pivot) and then sorting the sub-lists.

Our implementation of quicksort for lists follows the following steps:

* If the list is empty, return the empty list.
* Otherwise, let `pivot` be the first element (`head`) of the list.
* Let `smaller` be the list of elements smaller (`≤`) than `pivot` and `larger` be the list of elements larger (`>`) than `pivot`.
* Recursively sort `smaller` and `larger` lists and concatenate them with `pivot` in between.

We begin by defining `smaller` and `larger` lists. We define them as abbreviations so that they are automatically unfolded by Lean.
-/
namespace langur -- starts a namespace to group the tutorial definitions
variable {α : Type}[LinearOrder α] -- continues the Lean declaration above

/--
Returns a sublist of elements from `l` that are less than or equal to the `pivot`.
-/
@[grind, simp] -- annotation controlling elaboration, simplification, or automation
def smaller (pivot : α) (l : List α) : List α := -- defines `smaller`
  l.filter (fun x => x ≤  pivot) -- maps this case or syntax pattern to its result

/--
Returns a sublist of elements from `l` that are strictly greater than the `pivot`.
-/
@[grind, simp] -- annotation controlling elaboration, simplification, or automation
def larger (pivot : α) (l : List α) : List α := -- defines `larger`
  l.filter (fun x => pivot < x) -- maps this case or syntax pattern to its result

/--
A partial (non-terminating) implementation of Quicksort.
-/
partial def naiveQuickSort : List α → List α -- defines the partial function `naiveQuickSort`
  | [] => [] -- handles this pattern-matching case
  | pivot :: l => -- handles this pattern-matching case
    (naiveQuickSort (smaller pivot l)) ++ -- continues the surrounding Lean expression
    pivot :: (naiveQuickSort (larger pivot l)) -- continues the Lean declaration above

/--
The verified implementation of Quicksort for lists.
Terminates because the filtered sublists are strictly smaller than the original list.
-/
def quickSort : List α → List α -- defines `quickSort`
  | [] => [] -- handles this pattern-matching case
  | pivot :: l => -- handles this pattern-matching case
    (quickSort (smaller pivot l)) ++ pivot :: (quickSort (larger pivot l)) -- continues the surrounding Lean expression
termination_by l => l.length -- tells Lean which expression decreases for termination


/--
Quicksort of an empty list is an empty list.
-/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem quickSort_nil : quickSort ([] : List α) = [] := by -- states and proves theorem `quickSort_nil`
  simp [quickSort] -- simplifies the current goal or hypotheses

/--
Recursive step of the Quicksort implementation.
-/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem quickSort_cons (pivot : α) (l : List α) : -- states and proves theorem `quickSort_cons`
    quickSort (pivot :: l) = (quickSort (smaller pivot l)) ++ -- continues the Lean declaration above
    pivot :: (quickSort (larger pivot l)) := by -- gives the value or proof for this declaration
  simp [quickSort] -- simplifies the current goal or hypotheses

/--
An element is in the original list if and only if it is in the `smaller` or `larger` sublists
(when partitioning around a pivot).
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem mem_iff_below_or_above_pivot (pivot : α) -- states and proves theorem `mem_iff_below_or_above_pivot`
  (l : List α)(x : α) : -- continues the surrounding Lean expression
    x ∈ l ↔ x ∈ smaller pivot l ∨ x ∈ larger pivot l := by grind -- gives the value or proof for this declaration

/--
The `quickSort` function preserves the elements of the list.
-/
@[grind =_] -- annotation controlling elaboration, simplification, or automation
theorem mem_iff_mem_quickSort (l: List α)(x : α) : -- states and proves theorem `mem_iff_mem_quickSort`
    x ∈ l ↔ x ∈ quickSort l := by -- gives the value or proof for this declaration
  fun_induction quickSort <;> grind -- continues the Lean declaration above

section Count -- continues the Lean declaration above
/-!
## Exercises

Prove that quickSort preserves the count of each element. A useful lemma was not annotated with `grind` so this is done below.
-/
attribute [grind .] List.count_eq_zero_of_not_mem -- continues the Lean declaration above


/--
The count of an element in a list is the sum of its counts in the partitioned sublists.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem count_sum_above_below_pivot (pivot : α) -- states and proves theorem `count_sum_above_below_pivot`
  (l : List α)(x : α) : -- continues the surrounding Lean expression
    (l.count x) = (smaller pivot l).count x + -- continues the surrounding Lean expression
      (larger pivot l).count x  := by -- continues the surrounding Lean expression
  sorry -- marks this tutorial exercise proof as unfinished

/--
The `quickSort` function preserves the count of each element in the list.
-/
theorem count_eq_count_quickSort (l : List α) -- states and proves theorem `count_eq_count_quickSort`
  (x : α) : -- continues the surrounding Lean expression
    l.count x = (quickSort l).count x := by -- gives the value or proof for this declaration
  sorry -- marks this tutorial exercise proof as unfinished
end Count -- closes the current namespace or section


/--
Concatenating two sorted lists with a pivot in between results in a sorted list,
provided the pivot respects the bounds of both lists.
-/
theorem sorted_sandwitch (l₁ : List α) (h₁ : Sorted l₁) -- states and proves theorem `sorted_sandwitch`
    (l₂ : List α) (h₂ : Sorted l₂) -- continues the surrounding Lean expression
    (bound : α) -- continues the surrounding Lean expression
    (h_bound₁ : ∀ x ∈ l₁, x ≤ bound) -- continues the surrounding Lean expression
    (h_bound₂ : ∀ x ∈ l₂, bound ≤ x) : -- continues the surrounding Lean expression
    Sorted (l₁ ++ bound :: l₂) := by -- gives the value or proof for this declaration
    induction h₁ with -- continues the Lean declaration above
    | nil => grind -- handles this pattern-matching case
    | singleton x => -- handles this pattern-matching case
      grind [Sorted.step] -- asks the `grind` automation to finish the proof
    | step x y l hxy tail_sorted ih => -- handles this pattern-matching case
      grind [Sorted.step] -- asks the `grind` automation to finish the proof

/--
The `quickSort` function correctly sorts any input list.
-/
theorem quickSort_sorted (l : List α) : Sorted (quickSort l) := by -- states and proves theorem `quickSort_sorted`
  cases l with -- splits the proof by cases on this value or proof
  | nil => -- handles this pattern-matching case
    simp [quickSort_nil] -- simplifies the current goal or hypotheses
    apply Sorted.nil -- reduces the goal using this theorem or constructor
  | cons pivot l => -- handles this pattern-matching case
    rw [quickSort_cons] -- continues the Lean declaration above
    have h_small := -- records an intermediate fact for the proof
      quickSort_sorted (smaller pivot l) -- continues the Lean declaration above
    have h_large := -- records an intermediate fact for the proof
      quickSort_sorted (larger pivot l) -- continues the Lean declaration above
    apply sorted_sandwitch <;> grind -- reduces the goal using this theorem or constructor
termination_by l.length -- tells Lean which expression decreases for termination
