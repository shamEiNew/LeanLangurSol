namespace langur

/-!
## Function Equality, Decidability, and Proof irrelevance

This file introduces a few more concepts related to equality and decidability in Lean, including:

* Proof irrelevance: all proofs of the same proposition are considered equal, which allows us to conclude that any two proofs of the same proposition are equal without needing to inspect their structure.
* Function extensionality: two functions are equal if they give the same outputs for all inputs.
* The obvious converse: if two functions are equal, then they give the same outputs for all inputs.
* The `Decidable` typeclass, which allows us to express whether a proposition is decidable (i.e., we can algorithmically determine whether it is true or false).
* Decidable equality for function types, which relies on function extensionality.

We begin with *proof irrelevance*, which states that all proofs of the same proposition are equal. This allows us to conclude that any two proofs of the same proposition are equal without needing to inspect their structure.
-/
example {α : Prop} (pf₁ pf₂ : α) : pf₁ = pf₂ := by
  rfl

/-!
## Equality of functions

Two functions are equal if and only if they give the same outputs for all inputs. This is known as *function extensionality*. One direction is straightforward: if two functions are equal, then they give the same outputs for all inputs. The other direction requires the `funext` tactic, which allows us to conclude that two functions are equal if they give the same outputs for all inputs.
-/
example (f g : Nat → Nat): f = g → f 0 = g 0 := by
  grind

example (f g : Nat → Nat): (∀ x, f x = g x) → f = g := by
  intro h
  funext x
  apply h

#eval decide (1 = 1)
#eval decide (1 = 2)

def minNat (a b : Nat) : Nat := if a ≤ b then a else b

/--
error: failed to synthesize instance of type class
  Decidable (a ≤ b)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def minBad {α : Type}[LE α] (a b : α) : α := if a ≤ b then a else b

open Classical in
noncomputable def minExist {α : Type}[LE α]
  (a b : α) : α :=
  if a ≤ b then a else b

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'minExist', which is 'noncomputable'
-/
#guard_msgs in
#eval minExist 3 5

/--
error: failed to synthesize instance of type class
  Decidable (∀ (n : Nat), n + 1 = 1 + n)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval decide (∀ n : Nat, n + 1 = 1 +n)

/--
error: failed to synthesize
  Decidable ((fun x ↦ x + 1) = fun x ↦ 1 + x)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#eval (fun x => x + 1) = (fun x => 1 + x)

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


end langur
