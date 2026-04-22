/-!
## Structures

A simple datatype in Lean is a `Structure`. This is a special case of an *inductive type* with some additional conveniences for working with named fields. We consider some examples.

When you reach this, we expect that you have already worked through:

* `SmallestNat.lean`
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


/-!
## Exercise: Even numbers

Define a structure `EvenNumber` that represents an even natural number. It should have a field `value : Nat` and a proof that `value` is even (i.e., there exists some `k : Nat` such that `value = 2 * k`). Then, create an instance of `EvenNumber` for the number 10. Also define a function ``double: Nat → EvenNumber`` that takes a natural number `n` and returns an `EvenNumber` representing `2 * n`.
-/

end langur
