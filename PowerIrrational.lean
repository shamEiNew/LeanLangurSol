import Mathlib

/-!
## Non-computable existence proof

One of the most famous examples of a non-computable existence proof is the following: there exist irrational numbers `a` and `b` such that `a^b` is rational. The proof is as follows: consider `sqrt(2)^sqrt(2)`. If this number is irrational, then we can take `a = sqrt(2)` and `b = sqrt(2)`, and we are done. If this number is rational, then we can take `a = sqrt(2)^sqrt(2)` and `b = sqrt(2)`, and we are also done. In either case, we have found irrational numbers `a` and `b` such that `a^b` is rational.

However, this proof does not give us any explicit examples of such numbers, and it relies on the law of excluded middle, which is not constructive. Indeed, solving this problem explicitly amounts to answering the non-trivial question of whether `sqrt(2)^sqrt(2)` is rational or irrational.
-/

namespace langur

/--
The square root of `2` (an abbreviation).
-/
noncomputable abbrev sqrt2 : ℝ := Real.sqrt 2

/--
The equation `(sqrt2^sqrt2)^sqrt2 = 2`.
-/
theorem sq_sq_sq_sqrt2_rational :
  (sqrt2^sqrt2)^sqrt2 = 2 := by
  rw [← Real.rpow_mul, Real.mul_self_sqrt] <;> simp

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
The same result as `irrational_power_irrational_rational`, but with an explicit witness. This has to be noncomputable, since the original proof is nonconstructive. Concretely, `Classical.choice` is used to extract a witness from the existential statement and this is noncomputable.
-/
noncomputable def explicit_irrational_power_irrational_rational :
  {(a, b) : ℝ × ℝ | Irrational (a) ∧ Irrational b ∧
    ¬ Irrational (a^b) } := by
    apply Classical.choice
    let ⟨a, b, ha, hb, hab⟩ := irrational_power_irrational_rational
    exact ⟨(a, b), ⟨ha, hb, hab⟩⟩


end langur
