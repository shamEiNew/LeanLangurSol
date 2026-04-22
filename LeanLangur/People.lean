/-!
## Structures

A simple datatype in Lean is a `Structure`. This is a special case of an *inductive type* with some additional conveniences for working with named fields. We consider some examples.
-/

namespace langur

/--
A structure representing a person with a name and an age.
Uses `deriving Repr` for printable output and `DecidableEq` for equality checking.
-/
structure Person where
  name : String
  age  : Nat
  deriving Repr, DecidableEq

#check Person.mk

/-- An example instance of the `Person` structure. -/
def alice : Person :=
  { name := "Alice", age := 30 }

#eval alice.name  -- evaluates to "Alice"
#eval alice.age   -- evaluates to 30
#eval alice        -- { name := "Alice", age := 30 }

/--
A structure representing a voter, extending the `Person` structure.
Includes a `voterId` and a proof of voting eligibility based on age.
-/
structure Voter extends Person where
  voterId : Nat
  /-- Proof that the voter is at least 18 years old. -/
  is_voting_eligible : 18 ≤ age := by grind
  deriving Repr, DecidableEq

/-- An example instance of the `Voter` structure. -/
def bob : Voter :=
  { name := "Bob", age := 25, voterId := 12345}


end langur
