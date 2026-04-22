import Mathlib

/-!
# Miscellaneous Examples

A collection of various examples in Lean 4, including:
* Custom empty and false types.
* Simple proofs and exercises.

This is stuff added while livecoding as answers to questions, and is not meant to be a cohesive module. It is just a scratchpad for various examples.
-/

namespace langur

/--
A custom empty type.
-/
inductive MyEmpty where
  deriving Repr

/--
A custom false proposition.
-/
inductive MyFalse : Prop where

/--
Principle of explosion for the custom empty type.
-/
def ofEmpty{α : Type} : MyEmpty → α
  | e => by cases e

/--
Principle of explosion for the custom false proposition.
-/
theorem myFalse_elim (f : MyFalse) : ∀ {P : Prop}, P := by
  intro P
  cases f

/--
A very simple proof that `1 ≤ 5`.
-/
theorem easy : 1 ≤ 5 := by
  apply Nat.le_succ_of_le
  apply Nat.le_succ_of_le
  apply Nat.le_succ_of_le
  apply Nat.le_succ_of_le
  apply Nat.le_refl

#print easy

/--
Predicate for checking if a real number is rational.
-/
def IsRational (x : ℝ) : Prop :=
  ∃ (α  : ℚ), x = α

set_option pp.all true in
#print IsRational

/-- A subtype representing natural numbers that are even. -/
abbrev EvenNat := { n : Nat // n % 2 = 0}


end langur
