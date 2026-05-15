import Std -- imports definitions and theorems used below
import Mathlib -- imports definitions and theorems used below

namespace langur -- starts a namespace to group the tutorial definitions

open Std -- opens names so constructors or helpers can be written unqualified

/-!
# Catalan Numbers and Memoization

The Catalan numbers are a sequence of natural numbers that have many combinatorial interpretations.

These satisfy the recurrence relation:
* `C(0) = 1`
* `C(n+1) = Σ (C(i) * C(n-i)) for i = 0 to n`

We can naively implement this recurrence relation in Lean, but it will be inefficient for large `n` due to repeated calculations. We show how to use memoization to optimize the computation of Catalan numbers using `State` Monad.
-/
namespace Catalan -- starts a namespace to group the tutorial definitions

abbrev CatalanM := StateM (HashMap Nat Nat) -- introduces `CatalanM` as a reducible abbreviation

#check List.range -- asks Lean to display the inferred type

/-- Naive recursive computation of Catalan numbers -/
partial def catalanNaive : Nat → Nat -- defines the partial function `catalanNaive`
  | 0 => 1 -- handles this pattern-matching case
  | n + 1 => -- handles this pattern-matching case
    let terms := -- binds an intermediate value for the following expression
      List.range (n + 1) |>.map (fun i => catalanNaive i * catalanNaive (n - i)) -- maps this case or syntax pattern to its result
    terms.sum -- continues the Lean declaration above

/-- Memoized computation of Catalan numbers using State Monad -/
partial def catalanMemo (n : Nat) : CatalanM Nat := do -- defines the partial function `catalanMemo`
  let cache ← get -- binds an intermediate value for the following expression
  match cache.get? n with -- splits computation into cases by pattern matching
  | some value => return value -- handles this pattern-matching case
  | none => -- handles this pattern-matching case
    match n with -- splits computation into cases by pattern matching
    | 0 => -- handles this pattern-matching case
      modify (fun m => m.insert 0 1) -- maps this case or syntax pattern to its result
      return 1 -- returns this value from the monadic block
    | n + 1 => -- handles this pattern-matching case
      let mut sum := 0 -- binds an intermediate value for the following expression
      for i in [0:n + 1] do -- iterates through these values in the monadic block
        let ci ← catalanMemo i -- binds an intermediate value for the following expression
        let cni ← catalanMemo (n - i) -- binds an intermediate value for the following expression
        sum := sum + (ci * cni) -- gives the value or proof for this declaration
      modify (fun m => m.insert (n + 1) sum) -- maps this case or syntax pattern to its result
      return sum -- returns this value from the monadic block

#eval catalanMemo 23 |>.run' {} -- runs this expression as a tutorial check
end Catalan -- closes the current namespace or section

/-!
The exercise for this file and `FibM.lean` is the last exercise in `Combinations.lean`.
-/

end langur -- closes the current namespace or section
