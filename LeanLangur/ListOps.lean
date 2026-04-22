import Mathlib
/-!
# List operations

We illustrate:

* Explicit and Implicit parameters.
* `do` notation for lists.
* Why we need typeclasses.

When you reach this, we expect that you have already worked through:

* `SmallestNat.lean`
-/

namespace langur

/--
Doubles a list by concatenating it with itself.
This version takes the type `α` as an explicit parameter.
-/
def doubleList (α : Type) (l: List α) : List α :=
  l ++ l

#eval doubleList Nat [1, 3 ,5]

#eval doubleList String ["hello", "world"]

#eval doubleList _ ["a", "b", "c"]

/--
error: don't know how to synthesize placeholder for argument `l`
context:
⊢ List ℕ
-/
#guard_msgs in
#eval doubleList Nat _

/--
Doubles a list by concatenating it with itself.
This version uses an implicit type parameter `{α : Type}`.
-/
def dblList {α : Type} (l: List α) : List α :=
  l ++ l

#eval dblList [1, 3 ,5]

#eval @dblList Int [1, 3 ,5]

#eval @dblList _ [1, 3 ,5]

/-!
List of pairs using `do` notation. The `do` notation is a convenient way to compose operations that involve iterating over lists. It allows us to write code that looks more like a traditional imperative style, while still being purely functional. The same notation and behaviour holds for so-called **Monads** in general. We will encounter other monads later, in particular `State` monads and `Option`.
-/

/--
Computes the Cartesian product of two lists using `do` notation.
Returns a list of all possible pairs `(x, y)` where `x ∈ l₁` and `y ∈ l₂`.
-/
def pairs {α β : Type} (l₁: List α) (l₂: List β) : List (α × β) := do
  let x ← l₁
  let y ← l₂
  return (x, y)

#eval pairs [1, 2] ["a", "b"]

/-!
## Exercise

Using the `do` notation, implement a function `innerPairs` that in a special case corresponds to the following Python list comprehension:

```python
[(x, y) for l in [[1, 2], [3, 4]] for x in l for y in l]`
```
More generally, we are given `ll: List (List α)` and we want `innerPairs` to return a list of all pairs `(x, y)` such that `x` and `y` are both elements of the same inner list in `ll`. In the above example, the answer would be `[(1, 1), (1, 2), (2, 1), (2, 2), (3, 3), (3, 4), (4, 3), (4, 4)]`.
-/

/-!
List of sums using `do` notation. Requires the type `α` to have an instance of the `Add` typeclass to tell Lean how to add elements of type `α`. Continue to the file `Adder.lean` to see how typeclasses work. This example is just a preview of using typeclasses.
-/

/--
Computes all possible sums of elements from two lists using `do` notation.
-/
def sums {α : Type}[Add α] (l₁: List α) (l₂: List α ) : List α := do
  let x ← l₁
  let y ← l₂
  return x + y

end langur
