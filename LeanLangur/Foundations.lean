/-!
# Foundations of Lean

* "Everything" in Lean is a term. Terms have types.
* Terms include:
  * numbers, strings
  * functions
  * lists
  * propositions (logical statements)
  * proofs
  * types
* We can form expressions for terms and types.
* We make two kinds of *judgements*:
  * term `a` has type `α`.
  * terms `a` and `b` are equal by definition.
* The context has terms with names.
* The command `#eval` evaluates a term to a value if this makes sense.
-/
#eval 2 + 3 -- 5

#check 2 + 3 -- Nat

#check "Hello, Lean!" -- String

#check Nat -- Type

#check Int -- Type

#check Type -- Type 1

def two : Nat := 2

def five := two + 3

#check two -- Nat

#check five -- Nat

#eval five -- 5


#check 3 -- checks the type of `3`
#check Nat -- checks the type of `Nat`
#check Nat.add -- checks the type of `Nat.add`
#eval 3 + 4 -- evaluates `3 + 4` to `7`
#check Type -- Type 1
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
