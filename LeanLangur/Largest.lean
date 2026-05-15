import Mathlib.Order.Lattice -- imports definitions and theorems used below
/-!
## Largest Element in a List: Programs with Proofs

We illustrate how to write programs with proofs in Lean by implementing a function to find the largest element in a (non-empty) list, along with proofs that the element is indeed in the list and is larger than or equal to all other elements.

* We first implement `largestNat` for lists of natural numbers, along with proofs `largestNat_mem` and `largestNat_ge_all`.

* We then generalize this to lists of any type with a linear order, implementing `largest` for *non-empty* lists along with proofs `largest_mem` and `largest_ge_all`.
-/

namespace langur -- starts a namespace to group the tutorial definitions

def largestNat : List Nat → Nat -- defines `largestNat`
| []       => 0  -- placeholder for empty list
| [x]      => x -- handles this pattern-matching case
| x :: y :: xs => -- handles this pattern-matching case
    max x (largestNat (y :: xs)) -- continues the Lean declaration above

#check largestNat.induct -- asks Lean to display the inferred type

#eval largestNat [3, 1, 4, 1, 5, 9, 2, 6, 5]  -- evaluates to 9

theorem largestNat_mem : ∀ (l : List Nat), l ≠ [] → largestNat l ∈ l := by -- states and proves theorem `largestNat_mem`
  intro l -- introduces hypotheses or variables into the proof context
  fun_induction largestNat <;> grind -- continues the Lean declaration above


theorem largestNat_ge_all (l: List Nat) (x: Nat) : -- states and proves theorem `largestNat_ge_all`
  x ∈ l → x ≤ largestNat l := by -- gives the value or proof for this declaration
  fun_induction largestNat <;> grind -- continues the Lean declaration above

variable {α : Type}[LinearOrder α] -- continues the Lean declaration above

def largest₀ [Inhabited α] (l: List α) : α := -- defines `largest`
  match l with -- splits computation into cases by pattern matching
  | [] => default -- handles this pattern-matching case
  | [x] => x -- handles this pattern-matching case
  | x :: y :: xs => -- handles this pattern-matching case
    max x (largest₀ (y :: xs)) -- continues the Lean declaration above

example [Inhabited α] : α × α := -- checks an unnamed example or proof
  default -- continues the Lean declaration above

@[grind .] -- annotation controlling elaboration, simplification, or automation
def largest (l: List α) (h: l ≠ []) : α := -- defines `largest`
  match l with -- splits computation into cases by pattern matching
  | [x] => x -- handles this pattern-matching case
  | x :: y :: xs => -- handles this pattern-matching case
    max x (largest (y :: xs) (by simp)) -- continues the Lean declaration above

#eval largest [1, 3, 2] (by simp)  -- evaluates to 3

theorem largest_mem (l: List α) (h: l ≠ []) : -- states and proves theorem `largest_mem`
  largest l h ∈ l := by -- gives the value or proof for this declaration
  match l with -- splits computation into cases by pattern matching
  | [x] => grind -- handles this pattern-matching case
  | x :: y :: xs => -- handles this pattern-matching case
    have ih := largest_mem (y :: xs) (by simp) -- records an intermediate fact for the proof
    grind -- asks the `grind` automation to finish the proof

theorem largest_ge_all (l: List α) (h: l ≠ []) (x: α) : -- states and proves theorem `largest_ge_all`
  x ∈ l → x ≤ largest l h := by -- gives the value or proof for this declaration
  match l with -- splits computation into cases by pattern matching
  | [y] => -- handles this pattern-matching case
    grind -- asks the `grind` automation to finish the proof
  | y :: z :: xs => -- handles this pattern-matching case
    have ih := -- records an intermediate fact for the proof
      largest_ge_all (z :: xs) (by simp) x -- continues the Lean declaration above
    grind -- asks the `grind` automation to finish the proof

def largest? (l: List α) : Option α := -- defines `largest?`
  match l with -- splits computation into cases by pattern matching
  | [] => none -- handles this pattern-matching case
  | x :: ys   => -- handles this pattern-matching case
    match largest? ys  with -- splits computation into cases by pattern matching
    | none => some x -- handles this pattern-matching case
    | some m => some (max x m) -- handles this pattern-matching case

#eval largest? [1, 3, 2]  -- evaluates to some 3
#eval largest? ([] : List Nat)  -- evaluates to none

def doubleLargest?₀ (l: List Nat) : Option Nat  := -- defines `doubleLargest?`
  match largest? l with -- splits computation into cases by pattern matching
  | none => none -- handles this pattern-matching case
  | some m => some (2 * m) -- handles this pattern-matching case

def doubleLargest?₁ (l: List Nat) : Option Nat  := -- defines `doubleLargest?`
  (largest? l).map (fun m => 2 * m) -- continues the surrounding Lean expression

def doubleLargest?₂ (l: List Nat) : Option Nat  := -- defines `doubleLargest?`
  do -- starts a `do` block for monadic sequencing
    let m ← largest? l -- binds an intermediate value for the following expression
    return 2 * m -- returns this value from the monadic block

def sumLargest? (l1 l2: List Nat) : Option Nat := -- defines `sumLargest?`
  do -- starts a `do` block for monadic sequencing
    let m1 ← largest? l1 -- binds an intermediate value for the following expression
    let m2 ← largest? l2 -- binds an intermediate value for the following expression
    return m1 + m2 -- returns this value from the monadic block

#eval sumLargest? [1, 3, 2] [4, 5, 6]  -- evaluates to some 9

#eval sumLargest? [] [4, 5, 6]  -- evaluates to none

def largestImp (l: List Nat): Nat := Id.run do -- defines `largestImp`
  let mut maxSoFar := 0 -- binds an intermediate value for the following expression
  for x in l do -- iterates through these values in the monadic block
    if x > maxSoFar then -- branches on this decidable condition
      maxSoFar := x -- gives the value or proof for this declaration
  return maxSoFar -- returns this value from the monadic block

end langur -- closes the current namespace or section
