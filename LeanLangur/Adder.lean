/-!
# `Add` typeclass

We illustrate:

* How to use addition in the presence of the typeclass `Add`.
* How to create new instances of `Add` for custom types.
* Typeclass inference.
-/
#eval 3 + 4

#eval "hello " ++ "world"

open Add
#eval add 1 3

#check add

/--
error: failed to synthesize instance of type class
  Add String

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#eval add "Hello" "world"

instance : Add String where
  add s t := s ++ " " ++ t

#eval add "Hello" "world"

#eval "Hello" + "world"

instance {α β : Type}[Add α][Add β] :
  Add (α × β) where
  add := fun (a₁, b₁) (a₂, b₂) ↦
      (a₁ + a₂, b₁ + b₂)

#eval (1, 2, "Hello") +(3, 4, "world")


#check 1
#check Nat
#check Type 3
#check (0 = 1)
