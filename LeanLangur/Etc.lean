import Mathlib

/-!
# Miscellaneous Examples

A collection of various examples in Lean 4, including:
* Custom empty and false types.
* Real numbers and irrationality.
* Simple proofs and exercises.
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
The square root of `2` (an abbreviation).
-/
noncomputable abbrev sqrt2 : ℝ := Real.sqrt 2

/--
The equation `(sqrt2^sqrt2)^sqrt2 = 2`.
-/
theorem sq_sq_sq_sqrt2_rational :
  (sqrt2^sqrt2)^sqrt2 = 2 := by
  rw [← Real.rpow_mul, Real.mul_self_sqrt]
  · simp
  · simp
  · simp

example :
  (sqrt2^sqrt2)^sqrt2 = 2 := by
  rw [← Real.rpow_mul, Real.mul_self_sqrt] <;> simp

/--
There exists an irrational numbers `a` and `b` such that `a^b` is rational.
-/
theorem irrational_power_irrational_rational :
  ∃ (a b : ℝ), Irrational (a) ∧ Irrational b ∧
    ¬ Irrational (a^b)  := by
  by_cases h : Irrational (sqrt2^sqrt2)
  case pos =>
    use sqrt2 ^ sqrt2, sqrt2
    simp [h, sq_sq_sq_sqrt2_rational, irrational_sqrt_two]
  case neg =>
    use sqrt2, sqrt2
    simp [irrational_sqrt_two]
    assumption

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

end langur
