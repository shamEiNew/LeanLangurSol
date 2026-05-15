import Mathlib -- imports definitions and theorems used below

/-!
# Binary Search Trees

This module provides a basic implementation of Binary Search Trees (BSTs) in Lean 4.
It includes definitions for the tree structure, membership, order properties,
and basic operations like adding labels and searching.
-/

namespace langur -- starts a namespace to group the tutorial definitions

variable {α : Type}[LinearOrder α] -- continues the Lean declaration above

namespace binary_search_tree -- starts a namespace to group the tutorial definitions

/--
A binary search tree structure.
Each node contains a value and two children (left and right).
A leaf contains a single value.
-/
inductive BinarySearchTree (α : Type) where -- declares the inductive type or proposition `BinarySearchTree`
  | leaf : α → BinarySearchTree α -- declares another constructor or syntax alternative
  | node : α → BinarySearchTree α → BinarySearchTree α → BinarySearchTree α -- declares another constructor or syntax alternative
deriving Repr, Inhabited -- asks Lean to generate standard instances automatically

open BinarySearchTree -- opens names so constructors or helpers can be written unqualified

/--
Membership relation for Binary Search Trees.
-/
@[grind ., simp] -- annotation controlling elaboration, simplification, or automation
def BinarySearchTree.mem {α : Type} : BinarySearchTree α → α → Prop -- defines `BinarySearchTree.mem`
  | leaf x, y => x = y -- handles this pattern-matching case
  | node _ l r, y => BinarySearchTree.mem l y ∨ BinarySearchTree.mem r y -- handles this pattern-matching case

/--
Instance for using the `∈` notation with `BinarySearchTree`.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
instance {α : Type} : Membership α (BinarySearchTree α) where -- provides an instance for typeclass search
  mem := BinarySearchTree.mem -- gives the value or proof for this declaration

/--
A leaf contains an element `y` if and only if `y` is equal to the element in the leaf.
-/
@[grind ., simp] -- annotation controlling elaboration, simplification, or automation
theorem mem_leaf {α : Type} (x y : α) : -- states and proves theorem `mem_leaf`
    y ∈ leaf x ↔ x = y := by -- gives the value or proof for this declaration
    simp [Membership.mem] -- simplifies the current goal or hypotheses

/--
A node contains an element `y` if and only if `y` is in the left or right subtree.
-/
@[grind ., simp] -- annotation controlling elaboration, simplification, or automation
theorem mem_node {α : Type} (x: α) (l r : BinarySearchTree α) (y : α) : -- states and proves theorem `mem_node`
    y ∈ node x l r ↔ y ∈ l ∨ y ∈ r := by -- gives the value or proof for this declaration
    simp [BinarySearchTree.mem, Membership.mem] -- simplifies the current goal or hypotheses

/--
Predicate for checking if a binary tree satisfies the Binary Search Tree property:
for any node with value `v`, all elements in the left subtree are `≤ v` and
all elements in the right subtree are `≥ v`.
Also requires the value `v` to be present in one of the subtrees (for nodes).
-/
@[grind ., simp] -- annotation controlling elaboration, simplification, or automation
def IsOrdered : BinarySearchTree α → Prop -- defines `IsOrdered`
  | leaf _ => True -- handles this pattern-matching case
  | node v l r => -- handles this pattern-matching case
    (∀ x ∈ l, x ≤ v) ∧ (∀ x ∈ r, v ≤ x) ∧ IsOrdered l ∧ IsOrdered r ∧ (v ∈ l ∨ v ∈ r) -- continues the surrounding Lean expression

/--
A leaf is always ordered.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem IsOrdered_leaf (x: α) : -- states and proves theorem `IsOrdered_leaf`
  IsOrdered (leaf x) := by -- gives the value or proof for this declaration
  simp [IsOrdered] -- simplifies the current goal or hypotheses

/--
If a node is ordered, all elements in its left subtree are less than or equal to the node's value.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem IsOrdered_left_below (v: α) (l r: BinarySearchTree α) (h: IsOrdered (node v l r)) : -- states and proves theorem `IsOrdered_left_below`
  ∀ x ∈ l, x ≤ v := by -- gives the value or proof for this declaration
  grind -- asks the `grind` automation to finish the proof

/--
If a node is ordered, all elements in its right subtree are greater than or equal to the node's value.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem IsOrdered_right_above (v: α) (l r: BinarySearchTree α) (h: IsOrdered (node v l r)) : -- states and proves theorem `IsOrdered_right_above`
  ∀ x ∈ r, v ≤ x := by grind -- gives the value or proof for this declaration

/--
If a node is ordered, its left subtree must also be ordered.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem IsOrdered_left_subtree (v: α) (l r: BinarySearchTree α) (h: IsOrdered (node v l r)) : -- states and proves theorem `IsOrdered_left_subtree`
  IsOrdered l := by -- gives the value or proof for this declaration
  grind -- asks the `grind` automation to finish the proof

/--
If a node is ordered, its right subtree must also be ordered.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem IsOrdered_right_subtree (v: α) (l r: BinarySearchTree α) (h: IsOrdered (node v l r)) : -- states and proves theorem `IsOrdered_right_subtree`
  IsOrdered r := by -- gives the value or proof for this declaration
  grind -- asks the `grind` automation to finish the proof

/--
Adds a label to the binary search tree while maintaining the tree structure.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
def BinarySearchTree.addLabel (t: BinarySearchTree α) (label: α) : BinarySearchTree α := -- defines `BinarySearchTree.addLabel`
  match t with -- splits computation into cases by pattern matching
  | leaf x => -- handles this pattern-matching case
    if label = x then -- branches on this decidable condition
      leaf x -- continues the Lean declaration above
    else -- handles the alternative branch
    if label < x then -- branches on this decidable condition
      node label (leaf label) (leaf x) -- continues the Lean declaration above
    else -- handles the alternative branch
      node label (leaf x) (leaf label) -- continues the Lean declaration above
  | node v l r => -- handles this pattern-matching case
    if label ≤ v then -- branches on this decidable condition
      node v (BinarySearchTree.addLabel l label) r -- continues the Lean declaration above
    else -- handles the alternative branch
      node v l (BinarySearchTree.addLabel r label) -- continues the Lean declaration above

/--
An element is in the tree after adding a label if and only if it was already there or it is the new label.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem mem_addLabel (t: BinarySearchTree α) (label: α) (x : α) : -- states and proves theorem `mem_addLabel`
    x ∈ BinarySearchTree.addLabel t label ↔ x = label ∨ x ∈ t := by -- gives the value or proof for this declaration
  induction t with -- continues the Lean declaration above
  | leaf v => -- handles this pattern-matching case
    by_cases label ≤ v <;> grind -- starts tactic-mode proof construction
  | node v l r ihl ihr => -- handles this pattern-matching case
    by_cases label ≤ v <;> grind -- starts tactic-mode proof construction

/--
Adding a label to an ordered tree results in an ordered tree.
-/
theorem ordered_addLabel (t: BinarySearchTree α) (label: α) -- states and proves theorem `ordered_addLabel`
  (h: IsOrdered t) : -- continues the surrounding Lean expression
    IsOrdered (BinarySearchTree.addLabel t label) := by -- gives the value or proof for this declaration
  induction t with -- continues the Lean declaration above
  | leaf x => -- handles this pattern-matching case
    by_cases label ≤ x <;> grind -- starts tactic-mode proof construction
  | node v l r ihl ihr => -- handles this pattern-matching case
    by_cases label ≤ v <;> grind -- starts tactic-mode proof construction

/--
Returns the value at the root of a node, or the value in a leaf.
-/
def pivot : BinarySearchTree α → α -- defines `pivot`
| node l .. => l -- handles this pattern-matching case
| leaf l => l -- handles this pattern-matching case

/--
The pivot of an ordered tree is always a member of the tree.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem pivot_member (l: BinarySearchTree α) (h₀ : IsOrdered l) : -- states and proves theorem `pivot_member`
  pivot l ∈ l := by -- gives the value or proof for this declaration
  induction l with -- continues the Lean declaration above
  | leaf l => grind [pivot] -- handles this pattern-matching case
  | node label left right ihl ihr => -- handles this pattern-matching case
    grind [pivot] -- asks the `grind` automation to finish the proof

/--
Efficiently checks if a label is in an ordered binary search tree.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
def fastCheckMem (label : α)(l: BinarySearchTree α) : Bool := match l with -- defines `fastCheckMem`
  | leaf l => l == label -- handles this pattern-matching case
  | node l left right => -- handles this pattern-matching case
    if l == label then true -- branches on this decidable condition
    else if label < l then fastCheckMem label left -- handles the alternative branch
    else fastCheckMem label right -- handles the alternative branch

/--
`fastCheckMem` correctly determines membership in an ordered tree.
-/
theorem fastCheckMem_correct (label : α)(l: BinarySearchTree α)(h : IsOrdered l): -- states and proves theorem `fastCheckMem_correct`
  fastCheckMem label l = true ↔ label ∈ l := by -- gives the value or proof for this declaration
  induction l with -- continues the Lean declaration above
  | leaf label' => -- handles this pattern-matching case
    grind -- asks the `grind` automation to finish the proof
  | node label' left right ihl ihr => -- handles this pattern-matching case
    if p:label' = label -- branches on this decidable condition
      then -- continues the Lean declaration above
        grind -- asks the `grind` automation to finish the proof
    else -- handles the alternative branch
      if p':label < label' -- branches on this decidable condition
      then -- continues the Lean declaration above
        grind -- asks the `grind` automation to finish the proof
      else -- handles the alternative branch
        grind -- asks the `grind` automation to finish the proof

/-!
## Exercise: Deletion

Define a function `deleteLabel` that removes a label from an ordered binary search tree while maintaining the tree structure and order properties. Prove that after deletion, the label is no longer in the tree, and that all other labels are still present.
-/

end binary_search_tree -- closes the current namespace or section

end langur -- closes the current namespace or section
