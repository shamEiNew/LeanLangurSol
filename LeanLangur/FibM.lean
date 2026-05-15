import Std -- imports definitions and theorems used below
/-!
# Fibonacci Numbers with Memoization

The Fibonacci numbers are a classic sequence defined by the recurrence relation:
* `F(0) = 1`
* `F(1) = 1`
* `F(n) = F(n-1) + F(n-2)` for `n ≥ 2`
We can naively implement this recurrence relation in Lean, but it will be inefficient for large `n` due to repeated calculations. We show how to use memoization to optimize the computation of Fibonacci numbers using `State` Monad.

In the specific case of Fibonacci numbers, we can instead just use pairs. But this example illustrates the general technique of memoization using the State monad.
-/

namespace langur -- starts a namespace to group the tutorial definitions

namespace FibM -- starts a namespace to group the tutorial definitions

def slowFib : Nat → Nat -- defines `slowFib`
  | 0 => 1 -- handles this pattern-matching case
  | 1 => 1 -- handles this pattern-matching case
  | n + 2 => slowFib (n + 1) + slowFib n -- handles this pattern-matching case

#eval slowFib 33 -- runs this expression as a tutorial check

open Std -- opens names so constructors or helpers can be written unqualified

abbrev FibM := StateM (HashMap Nat  Nat) -- introduces `FibM` as a reducible abbreviation

def fibM (n : Nat) : FibM Nat := do -- defines `fibM`
  let cache ← get -- binds an intermediate value for the following expression
  match cache.get? n with -- splits computation into cases by pattern matching
  | some value => return value -- handles this pattern-matching case
  | none => -- handles this pattern-matching case
    match n with -- splits computation into cases by pattern matching
    | 0 => -- handles this pattern-matching case
      modify (fun m => m.insert 0 1) -- maps this case or syntax pattern to its result
      return 1 -- returns this value from the monadic block
    | 1 => -- handles this pattern-matching case
      modify (fun m => m.insert 1 1) -- maps this case or syntax pattern to its result
      return 1 -- returns this value from the monadic block
    | n + 2 => -- handles this pattern-matching case
      let fn1 ← fibM (n + 1) -- binds an intermediate value for the following expression
      let fn2 ← fibM n -- binds an intermediate value for the following expression
      let result := fn1 + fn2 -- binds an intermediate value for the following expression
      modify (fun m => m.insert (n + 2) result) -- maps this case or syntax pattern to its result
      return result -- returns this value from the monadic block
#eval fibM 1001 |>.run' ∅ -- This will be fast due to memoization

#check fibM -- asks Lean to display the inferred type


end FibM -- closes the current namespace or section

/-!
As mentioned earlier, we can also implement Fibonacci numbers using pairs to achieve a linear time complexity without needing memoization. A more realistic example is the computation of Catalan numbers in `CatalanM.lean`.

The exercise for this file and `CatalanM.lean` is the last exercise in `Combinations.lean`.
-/

end langur -- closes the current namespace or section
