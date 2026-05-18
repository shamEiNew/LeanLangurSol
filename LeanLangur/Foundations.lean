/-!
# Foundations of Lean

* Terms in Lean include numbers, functions, data, theorems, proofs, types, ...
* Every term has a type.
* The command `#check` displays the type of a term.
* The command `#eval` evaluates a term to a value if this makes sense.
-/
#check 3 -- checks the type of `3`
#check Nat -- checks the type of `Nat`
#check Nat.add -- checks the type of `Nat.add`
#eval 3 + 4 -- evaluates `3 + 4` to `7`
#check Type
#check fun n ↦ n + 2

/--
error: could not synthesize a `Repr` or `ToString` instance for type
  Nat → Nat
-/
#guard_msgs in -- checks that the following command produces the expected message
#eval fun n ↦ n + 2 -- evaluates the function to a lambda expression

#eval (fun n ↦ n + 2) 5 -- evaluates the function at `5` to `7`

#check 1 = 2

#check Prop

#check Nat.le_refl

#check Nat.le_refl 3

theorem three_le_three : 3 ≤ 3 := Nat.le_refl 3 -- defines a theorem `three_le_three` and proves it using `Nat.le_refl`

#check three_le_three

example {p: Prop} (pf₁ pf₂ : p) : pf₁ = pf₂ := by -- starts a proof in tactic mode; the goal is to prove `p` from two proofs of `p`
  rfl -- solves the goal from an existing hypothesis
