import Mathlib
/-!
# List operations

We illustrate:

* Explicit and Implicit parameters.
* `do` notation for lists.
* Why we need typeclasses.
-/
def doubleList (α : Type) (l: List α) : List α :=
  l ++ l

#eval doubleList Nat [1, 3 ,5]

#eval doubleList String ["hello", "world"]

#eval doubleList _ ["a", "b", "c"]

/--
error: don't know how to synthesize placeholder for argument `l`
context:
⊢ List ℕ
-/
#guard_msgs in
#eval doubleList Nat _

def dblList {α : Type} (l: List α) : List α :=
  l ++ l

#eval dblList [1, 3 ,5]

#eval @dblList Int [1, 3 ,5]

#eval @dblList _ [1, 3 ,5]

/-!
List of pairs using `do` notation.
-/
def pairs {α β : Type} (l₁: List α) (l₂: List β) : List (α × β) := do
  let x ← l₁
  let y ← l₂
  return (x, y)

#eval pairs [1, 2] ["a", "b"]

/-!
List of sums using `do` notation.
-/
def sums {α : Type}[Add α] (l₁: List α) (l₂: List α ) : List α := do
  let x ← l₁
  let y ← l₂
  return x + y
