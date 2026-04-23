import Mathlib
/-!
## Binary Trees

We consider an example of a data structure: binary trees. We define a binary tree datatype, a function to convert a binary tree to a list, and prove that membership in the tree corresponds to membership in the list.

This is our first example of defining an *inductive type*.

When you reach this, we expect that you have already worked through:
* `SmallestNat.lean`
* `ListOps.lean`
-/

namespace langur

variable {α : Type}

/--
A simple binary tree where each leaf carries a value of type `α`,
and nodes represent branches with two subtrees.
-/
inductive BinTree (α : Type) where
  | leaf : α → BinTree α
  | node : BinTree α → BinTree α → BinTree α
deriving Repr, Inhabited

open BinTree

/--
Converts a binary tree to a list by performing an in-order traversal.
-/
@[grind .]
def BinTree.toList {α : Type} : BinTree α → List α
  | leaf x => [x]
  | node l r =>
    BinTree.toList l ++ BinTree.toList r

/-- An example binary tree containing natural numbers. -/
def exampleTree : BinTree Nat :=
  node (node (leaf 1) (leaf 2)) (leaf 3)

#eval exampleTree.toList  -- Output: [1, 2, 3]

/--
Inductive predicate for membership in a binary tree.
-/
@[grind .]
def Bintree.mem {α : Type} : BinTree α → α → Prop
  | leaf x, y => x = y
  | node l r, y => Bintree.mem l y ∨ Bintree.mem r y

/--
Instance for using the `∈` notation with `BinTree`.
-/
@[grind ., simp]
instance {α : Type} : Membership α (BinTree α) where
  mem := Bintree.mem

/--
An element `y` is in a leaf carrying `x` if and only if `x = y`.
-/
@[grind ., simp]
theorem mem_leaf {α : Type} (x y : α) :
    y ∈ leaf x ↔ x = y := by
    simp [Bintree.mem, Membership.mem]

/--
An element `y` is in a node if and only if it is in either the left or the right subtree.
-/
@[grind ., simp]
theorem mem_node {α : Type} (l r : BinTree α) (y : α) :
    y ∈ node l r ↔ y ∈ l ∨ y ∈ r := by
    simp [Bintree.mem, Membership.mem]

/--
Theorem stating that an element is in the tree if and only if it is in the list
produced by `toList`.
-/
theorem mem_iff_mem_toList {α : Type} (t : BinTree α) (x : α) :
    x ∈ t ↔ x ∈ BinTree.toList t := by
    apply Iff.intro
    · induction t with
    | leaf a => grind
    | node l r ihl ihr => grind
    · induction t with
    | leaf a => grind
    | node l r ihl ihr => grind

/-!
## Exercise: List to BinTree

Define a function `listToBinTree : List α → BinTree α` that converts a list to a binary tree (this is not unique). Then, prove that for any list `l` and element `x`, `x ∈ listToBinTree l` if and only if `x ∈ l`.
-/
end langur
