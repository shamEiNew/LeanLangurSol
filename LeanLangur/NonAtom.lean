/-!
# NonAtom Typeclass

This module defines the `NonAtom` typeclass, which identifies types that have at least
two distinct elements. It provides instances for several common types like `Nat`, `Bool`,
`List`, `Option`, and products.
-/

namespace langur

/--
A typeclass for types that have at least two distinct elements.
-/
class NonAtom (α : Type) where
    /-- The first distinct element. -/
    firstAtom : α
    /-- The second distinct element. -/
    secondAtom : α
    /-- Proof that the two elements are distinct. -/
    firstNeqSecond : firstAtom ≠ secondAtom

/--
Helper function to get the first atom of a `NonAtom` type.
-/
def firstAtom (α : Type) [c: NonAtom α] : α := c.firstAtom

/--
Helper function to get the second atom of a `NonAtom` type.
-/
def secondAtom (α : Type) [c: NonAtom α] : α := c.secondAtom

/--
Theorem stating that the two atoms of a `NonAtom` type are distinct.
-/
theorem firstAtomNeqSecond (α : Type) [c: NonAtom α] : firstAtom α  ≠ secondAtom α := c.firstNeqSecond

/-- `Nat` is a `NonAtom` type with 0 and 1. -/
instance : NonAtom Nat where
    firstAtom := 0
    secondAtom := 1
    firstNeqSecond := by decide

/-- `Bool` is a `NonAtom` type with false and true. -/
instance: NonAtom Bool where
    firstAtom := false
    secondAtom := true
    firstNeqSecond := by decide

/-- If `α` is `NonAtom`, then `List α` is also `NonAtom` (empty list vs single-element list). -/
instance [NonAtom α] : NonAtom (List α) where
    firstAtom := []
    secondAtom := [firstAtom α]
    firstNeqSecond := by simp

/-- If `α` is `Inhabited`, then `Option α` is `NonAtom` (none vs some). -/
instance [Inhabited α] : NonAtom (Option α) where
    firstAtom := none
    secondAtom := some (default : α)
    firstNeqSecond := by simp

/-- If `α` is `NonAtom`, then `α × α` is also `NonAtom`. -/
instance [NonAtom α] : NonAtom (α × α) where
    firstAtom := (firstAtom α, firstAtom α)
    secondAtom := (secondAtom α, secondAtom α)
    firstNeqSecond := by simp [firstAtomNeqSecond α]

/-- A `NonAtom` type is always `Inhabited` (using `firstAtom`). -/
instance [NonAtom α] : Inhabited α where
    default := firstAtom α

/-- If `α` is `NonAtom` and `β` is `Inhabited`, then `α × β` is `NonAtom`. -/
instance [NonAtom α] [Inhabited β] : NonAtom (α × β) where
    firstAtom := (firstAtom α, (default : β))
    secondAtom := (secondAtom α, (default : β))
    firstNeqSecond := by simp [firstAtomNeqSecond α]

/-- If `α` is `Inhabited` and `β` is `NonAtom`, then `α × β` is `NonAtom`. -/
instance [Inhabited α] [NonAtom β] : NonAtom (α × β) where
    firstAtom := ((default : α), firstAtom β)
    secondAtom := ((default : α), secondAtom β)
    firstNeqSecond := by simp [firstAtomNeqSecond β]

#eval firstAtom (Nat × Unit)

#eval secondAtom <| Nat × Nat

end langur
