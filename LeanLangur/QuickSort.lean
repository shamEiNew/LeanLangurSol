import Mathlib.Data.List.Basic
import Mathlib.Tactic
import LeanLangur.Basic
import LeanLangur.Sorted
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
namespace langur
variable {α : Type}[LinearOrder α]

/--
Returns a sublist of elements from `l` that are less than or equal to the `pivot`.
-/
@[grind, simp]
def smaller (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x ≤  pivot)

/--
Returns a sublist of elements from `l` that are strictly greater than the `pivot`.
-/
@[grind, simp]
def larger (pivot : α) (l : List α) : List α :=
  l.filter (fun x => pivot < x)

/--
A partial (non-terminating) implementation of Quicksort.
-/
partial def naiveQuickSort : List α → List α
  | [] => []
  | pivot :: l =>
    (naiveQuickSort (smaller pivot l)) ++
    pivot :: (naiveQuickSort (larger pivot l))

/--
The verified implementation of Quicksort for lists.
Terminates because the filtered sublists are strictly smaller than the original list.
-/
def quickSort : List α → List α
  | [] => []
  | pivot :: l =>
    (quickSort (smaller pivot l)) ++ pivot :: (quickSort (larger pivot l))
termination_by l => l.length


/--
Quicksort of an empty list is an empty list.
-/
@[simp, grind .]
theorem quickSort_nil : quickSort ([] : List α) = [] := by
  simp [quickSort]

/--
Recursive step of the Quicksort implementation.
-/
@[simp, grind .]
theorem quickSort_cons (pivot : α) (l : List α) :
    quickSort (pivot :: l) = (quickSort (smaller pivot l)) ++
    pivot :: (quickSort (larger pivot l)) := by
  simp [quickSort]

/--
An element is in the original list if and only if it is in the `smaller` or `larger` sublists
(when partitioning around a pivot).
-/
@[grind .]
theorem mem_iff_below_or_above_pivot (pivot : α)
  (l : List α)(x : α) :
    x ∈ l ↔ x ∈ smaller pivot l ∨ x ∈ larger pivot l := by grind

/--
The `quickSort` function preserves the elements of the list.
-/
@[grind =_]
theorem mem_iff_mem_quickSort (l: List α)(x : α) :
    x ∈ l ↔ x ∈ quickSort l := by
  fun_induction quickSort <;> grind

section Count
/-!
## Exercises

Prove that quickSort preserves the count of each element. A useful lemma was not annotated with `grind` so this is done below.
-/
attribute [grind .] List.count_eq_zero_of_not_mem


/--
The count of an element in a list is the sum of its counts in the partitioned sublists.
-/
@[grind .]
theorem count_sum_above_below_pivot (pivot : α)
  (l : List α)(x : α) :
    (l.count x) = (smaller pivot l).count x +
      (larger pivot l).count x  := by
  sorry

/--
The `quickSort` function preserves the count of each element in the list.
-/
theorem count_eq_count_quickSort (l : List α)
  (x : α) :
    l.count x = (quickSort l).count x := by
  sorry
end Count


/--
Concatenating two sorted lists with a pivot in between results in a sorted list,
provided the pivot respects the bounds of both lists.
-/
theorem sorted_sandwitch (l₁ : List α) (h₁ : Sorted l₁)
    (l₂ : List α) (h₂ : Sorted l₂)
    (bound : α)
    (h_bound₁ : ∀ x ∈ l₁, x ≤ bound)
    (h_bound₂ : ∀ x ∈ l₂, bound ≤ x) :
    Sorted (l₁ ++ bound :: l₂) := by
    induction h₁ with
    | nil => grind
    | singleton x =>
      grind [Sorted.step]
    | step x y l hxy tail_sorted ih =>
      grind [Sorted.step]

/--
The `quickSort` function correctly sorts any input list.
-/
theorem quickSort_sorted (l : List α) : Sorted (quickSort l) := by
  cases l with
  | nil =>
    simp [quickSort_nil]
    apply Sorted.nil
  | cons pivot l =>
    rw [quickSort_cons]
    have h_small :=
      quickSort_sorted (smaller pivot l)
    have h_large :=
      quickSort_sorted (larger pivot l)
    apply sorted_sandwitch <;> grind
termination_by l.length
