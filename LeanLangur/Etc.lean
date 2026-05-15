import Mathlib -- imports definitions and theorems used below

/-!
# Miscellaneous Examples

A collection of various examples in Lean 4, including:
* Custom empty and false types.
* Simple proofs and exercises.

This is stuff added while livecoding as answers to questions, and is not meant to be a cohesive module. It is just a scratchpad for various examples.
-/

namespace langur -- starts a namespace to group the tutorial definitions

/--
A custom empty type.
-/
inductive MyEmpty where -- declares the inductive type or proposition `MyEmpty`
  deriving Repr -- asks Lean to generate standard instances automatically

/--
A custom false proposition.
-/
inductive MyFalse : Prop where -- declares the inductive type or proposition `MyFalse`

/--
Principle of explosion for the custom empty type.
-/
def ofEmpty{α : Type} : MyEmpty → α -- defines `ofEmpty`
  | e => by cases e -- handles this pattern-matching case

/--
Principle of explosion for the custom false proposition.
-/
theorem myFalse_elim (f : MyFalse) : ∀ {P : Prop}, P := by -- states and proves theorem `myFalse_elim`
  intro P -- introduces hypotheses or variables into the proof context
  cases f -- splits the proof by cases on this value or proof

/--
A very simple proof that `1 ≤ 5`.
-/
theorem easy : 1 ≤ 5 := by -- states and proves theorem `easy`
  apply Nat.le_succ_of_le -- reduces the goal using this theorem or constructor
  apply Nat.le_succ_of_le -- reduces the goal using this theorem or constructor
  apply Nat.le_succ_of_le -- reduces the goal using this theorem or constructor
  apply Nat.le_succ_of_le -- reduces the goal using this theorem or constructor
  apply Nat.le_refl -- reduces the goal using this theorem or constructor

#print easy -- prints Lean's generated declaration for inspection

/--
Predicate for checking if a real number is rational.
-/
def IsRational (x : ℝ) : Prop := -- defines `IsRational`
  ∃ (α  : ℚ), x = α -- continues the Lean declaration above

set_option pp.all true in -- sets an elaborator or diagnostic option for this example
#print IsRational -- prints Lean's generated declaration for inspection

/-- A subtype representing natural numbers that are even. -/
abbrev EvenNat := { n : Nat // n % 2 = 0} -- introduces `EvenNat` as a reducible abbreviation


end langur -- closes the current namespace or section
