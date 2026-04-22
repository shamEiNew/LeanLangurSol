namespace langur

example {α : Prop} (pf₁ pf₂ : α) : pf₁ = pf₂ := by
  rfl

#print Decidable

/--
Instance to provide decidable equality for functions from `Bool` to `Nat`.
Two such functions are equal if they agree on both `true` and `false`.
-/
instance : DecidableEq (Bool → Nat) := by
  intro f g
  if c₁ : f true = g true then
    if c₂ : f false = g false then
      apply isTrue
      funext b
      cases b <;> simp [c₁, c₂]
    else
      apply isFalse
      grind
  else
    apply isFalse
    grind

/--
A more complex structure to illustrate derived decidable equality.
Contains a function field which relies on our `DecidableEq (Bool → Nat)` instance.
-/
structure Complicated where
  n : Nat
  f : Bool → Nat
deriving DecidableEq

example (f g : Nat → Nat): f = g → f 0 = g 0 := by
  intro h
  rw [h]

end langur
