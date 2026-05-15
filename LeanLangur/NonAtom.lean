/-!
# NonAtom Typeclass

This module defines the `NonAtom` typeclass, which identifies types that have at least
two distinct elements. It provides instances for several common types like `Nat`, `Bool`,
`List`, `Option`, and products.
-/

namespace langur -- starts a namespace to group the tutorial definitions

/--
A typeclass for types that have at least two distinct elements.
-/
class NonAtom (α : Type) where -- declares the typeclass `NonAtom`
    /-- The first distinct element. -/
    firstAtom : α -- continues the Lean declaration above
    /-- The second distinct element. -/
    secondAtom : α -- continues the Lean declaration above
    /-- Proof that the two elements are distinct. -/
    firstNeqSecond : firstAtom ≠ secondAtom -- continues the Lean declaration above

/--
Helper function to get the first atom of a `NonAtom` type.
-/
def firstAtom (α : Type) [c: NonAtom α] : α := c.firstAtom -- defines `firstAtom`

/--
Helper function to get the second atom of a `NonAtom` type.
-/
def secondAtom (α : Type) [c: NonAtom α] : α := c.secondAtom -- defines `secondAtom`

/--
Theorem stating that the two atoms of a `NonAtom` type are distinct.
-/
theorem firstAtomNeqSecond (α : Type) [c: NonAtom α] : firstAtom α  ≠ secondAtom α := c.firstNeqSecond -- states and proves theorem `firstAtomNeqSecond`

/-- `Nat` is a `NonAtom` type with 0 and 1. -/
instance : NonAtom Nat where -- provides an instance for typeclass search
    firstAtom := 0 -- gives the value or proof for this declaration
    secondAtom := 1 -- gives the value or proof for this declaration
    firstNeqSecond := by decide -- gives the value or proof for this declaration

/-- `Bool` is a `NonAtom` type with false and true. -/
instance: NonAtom Bool where -- provides an instance for typeclass search
    firstAtom := false -- gives the value or proof for this declaration
    secondAtom := true -- gives the value or proof for this declaration
    firstNeqSecond := by decide -- gives the value or proof for this declaration

/-- If `α` is `NonAtom`, then `List α` is also `NonAtom` (empty list vs single-element list). -/
instance [NonAtom α] : NonAtom (List α) where -- provides an instance for typeclass search
    firstAtom := [] -- gives the value or proof for this declaration
    secondAtom := [firstAtom α] -- gives the value or proof for this declaration
    firstNeqSecond := by simp -- gives the value or proof for this declaration

/-- If `α` is `Inhabited`, then `Option α` is `NonAtom` (none vs some). -/
instance [Inhabited α] : NonAtom (Option α) where -- provides an instance for typeclass search
    firstAtom := none -- gives the value or proof for this declaration
    secondAtom := some (default : α) -- gives the value or proof for this declaration
    firstNeqSecond := by simp -- gives the value or proof for this declaration

/-- If `α` is `NonAtom`, then `α × α` is also `NonAtom`. -/
instance [NonAtom α] : NonAtom (α × α) where -- provides an instance for typeclass search
    firstAtom := (firstAtom α, firstAtom α) -- gives the value or proof for this declaration
    secondAtom := (secondAtom α, secondAtom α) -- gives the value or proof for this declaration
    firstNeqSecond := by simp [firstAtomNeqSecond α] -- gives the value or proof for this declaration

/-- A `NonAtom` type is always `Inhabited` (using `firstAtom`). -/
instance [NonAtom α] : Inhabited α where -- provides an instance for typeclass search
    default := firstAtom α -- gives the value or proof for this declaration

/-- If `α` is `NonAtom` and `β` is `Inhabited`, then `α × β` is `NonAtom`. -/
instance [NonAtom α] [Inhabited β] : NonAtom (α × β) where -- provides an instance for typeclass search
    firstAtom := (firstAtom α, (default : β)) -- gives the value or proof for this declaration
    secondAtom := (secondAtom α, (default : β)) -- gives the value or proof for this declaration
    firstNeqSecond := by simp [firstAtomNeqSecond α] -- gives the value or proof for this declaration

/-- If `α` is `Inhabited` and `β` is `NonAtom`, then `α × β` is `NonAtom`. -/
instance [Inhabited α] [NonAtom β] : NonAtom (α × β) where -- provides an instance for typeclass search
    firstAtom := ((default : α), firstAtom β) -- gives the value or proof for this declaration
    secondAtom := ((default : α), secondAtom β) -- gives the value or proof for this declaration
    firstNeqSecond := by simp [firstAtomNeqSecond β] -- gives the value or proof for this declaration

#eval firstAtom (Nat × Unit) -- runs this expression as a tutorial check

#eval secondAtom <| Nat × Nat -- runs this expression as a tutorial check

end langur -- closes the current namespace or section
