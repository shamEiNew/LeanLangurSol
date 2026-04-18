/-!
## Structures

A simple datatype in Lean is a `Structure`. This is a special case of an *inductive type* with some additional conveniences for working with named fields. We consider some examples.
-/
structure Person where
  name : String
  age  : Nat
  deriving Repr, DecidableEq

#check Person.mk

def alice : Person :=
  { name := "Alice", age := 30 }

#eval alice.name  -- evaluates to "Alice"
#eval alice.age   -- evaluates to 30
#eval alice        -- { name := "Alice", age := 30 }

structure Voter extends Person where
  voterId : Nat
  is_voting_eligible : 18 ≤ age := by grind
  deriving Repr, DecidableEq

def bob : Voter :=
  { name := "Bob", age := 25, voterId := 12345}

abbrev EvenNat := { n : Nat // n % 2 = 0}

example {α : Prop} (pf₁ pf₂ : α) : pf₁ = pf₂ := by
  rfl

#print Decidable

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

structure Complicated where
  n : Nat
  f : Bool → Nat
deriving DecidableEq

example (f g : Nat → Nat): ∀ h:f = g,
  f 0 = g 0 := by
  intro h
  rw [h]
