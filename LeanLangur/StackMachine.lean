import LeanLangur.Basic -- imports definitions and theorems used below

/-!
# Stack Machine

This module defines a simple stack-based machine with instructions for pushing values,
popping values, and performing addition. It includes both unsafe and safe (option-returning)
execution engines, as well as a verified evaluator that uses a `ValidProgram` predicate.
-/

namespace langur -- starts a namespace to group the tutorial definitions

namespace stack_machine -- starts a namespace to group the tutorial definitions

/--
Instructions for the stack machine.
-/
inductive Instr -- declares the inductive type or proposition `Instr`
  | push (n : Nat) -- declares another constructor or syntax alternative
  | pop -- declares another constructor or syntax alternative
  | add -- declares another constructor or syntax alternative
  deriving Repr -- asks Lean to generate standard instances automatically

open Instr -- opens names so constructors or helpers can be written unqualified

/-- A stack is represented as a list of natural numbers. -/
abbrev Stack := List Nat -- introduces `Stack` as a reducible abbreviation

/-- A program is a list of instructions. -/
abbrev Program := List Instr -- introduces `Program` as a reducible abbreviation

/--
Unsafe evaluation of a program.
Assumes the stack has enough elements for `pop` and `add` operations.
-/
def eval! (p: Program) (s: Stack) : Stack := -- defines `eval!`
  match p with -- splits computation into cases by pattern matching
  | [] => s -- handles this pattern-matching case
  | push n :: p' => eval! p' (n :: s) -- handles this pattern-matching case
  | pop :: p' => -- handles this pattern-matching case
      eval! p' s.tail! -- continues the Lean declaration above
  | add :: p' => -- handles this pattern-matching case
      let x := s.head! -- binds an intermediate value for the following expression
      let y := s.tail!.head! -- binds an intermediate value for the following expression
      eval! p' ((x + y) :: s.tail!.tail!) -- continues the Lean declaration above

/--
Safe evaluation of a program using `Option`.
Returns `none` if an instruction is executed on an insufficient stack.
-/
def eval? (p: Program) (s: Stack) : Option Stack := -- defines `eval?`
  match p with -- splits computation into cases by pattern matching
  | [] => some s -- handles this pattern-matching case
  | push n :: p' => eval? p' (n :: s) -- handles this pattern-matching case
  | add :: p' => -- handles this pattern-matching case
      match s with -- splits computation into cases by pattern matching
      | x :: y :: zs => eval? p' ((x + y) :: zs) -- handles this pattern-matching case
      | _ => none -- handles this pattern-matching case
  | pop :: p' => -- handles this pattern-matching case
      match s with -- splits computation into cases by pattern matching
      | _ :: ys => eval? p' ys -- handles this pattern-matching case
      | _ => none -- handles this pattern-matching case

/--
Inductive predicate for a valid program given an initial stack size.
Ensures that the stack will never underflow during execution.
-/
@[grind cases] -- annotation controlling elaboration, simplification, or automation
inductive ValidProgram : (initStackSize : Nat) → (p : Program) → Prop -- declares the inductive type or proposition `ValidProgram`
  /-- The empty program is valid with any initial stack -/
  | nil : ValidProgram n [] -- declares another constructor or syntax alternative
  /-- If the first instruction is a push and the rest of the program is valid  with initial stack size `s + 1` then the program is valid with initial stack size `s` -/
  | push  {p : Program} : -- declares another constructor or syntax alternative
      ValidProgram (n + 1) p → -- continues the Lean declaration above
      ValidProgram n (push k :: p) -- continues the Lean declaration above
  /-- If the first instruction is a pop and the rest of the program is valid with initial stack size `s` then the program is valid with initial stack size `s + 1` -/
  | pop  {p : Program} : -- declares another constructor or syntax alternative
      ValidProgram n p → -- continues the Lean declaration above
      ValidProgram (n + 1) (pop :: p) -- continues the Lean declaration above
  /-- If the first instruction is an add and the rest of the program is valid with initial stack size `s + 2` then the program is valid with initial stack size `s + 1` -/
  | add {p : Program} : -- declares another constructor or syntax alternative
      ValidProgram (n + 1) p → -- continues the Lean declaration above
      ValidProgram (n + 2) (add :: p) -- continues the Lean declaration above

/-- The empty program is always valid. -/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_nil : ValidProgram n [] := ValidProgram.nil -- states and proves theorem `valid_program_nil`

/-- Pushing a value to a stack of size `n` results in a valid program if the rest is valid for `n+1`. -/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_push (n: Nat) (h : ValidProgram (n + 1) p') : -- states and proves theorem `valid_program_push`
    ValidProgram n (push k :: p') :=    ValidProgram.push h -- gives the value or proof for this declaration

/-- Adding values on a stack of size `k+2` is valid if the rest is valid for `k+1`. -/
@[simp, grind .] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_add (k: Nat) (h : ValidProgram (k + 1) p') : -- states and proves theorem `valid_program_add`
  ValidProgram (k + 2) (add :: p') := -- gives the value or proof for this declaration
  ValidProgram.add h -- continues the Lean declaration above

/-- Popping from a stack of size `n+1` is valid if the rest is valid for `n`. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_pop (h : ValidProgram n p') : -- states and proves theorem `valid_program_pop`
  ValidProgram (n + 1) (pop :: p') := -- gives the value or proof for this declaration
  ValidProgram.pop h -- continues the Lean declaration above

example (a b: Nat) : ValidProgram n [push a, push b, add] := by -- checks an unnamed example or proof
  grind -- asks the `grind` automation to finish the proof

example (a b c : Nat) : ValidProgram 0 [push a, push b, add, push c, add] := by -- checks an unnamed example or proof
  grind (ematch := 7) -- asks the `grind` automation to finish the proof

/-- If a program starting with `push` is valid, then the rest of the program is valid for a larger stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_of_push {k: Nat} (h : ValidProgram k (push a :: p')) : ValidProgram (k + 1) p' := by -- states and proves theorem `valid_program_of_push`
  cases h -- splits the proof by cases on this value or proof
  assumption -- solves the goal from an existing hypothesis

/-- An `add` instruction is never valid on an empty stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem invalid_program_add_zero: ¬ ValidProgram 0 (add :: p')  := by -- states and proves theorem `invalid_program_add_zero`
  intro h -- introduces hypotheses or variables into the proof context
  cases h -- splits the proof by cases on this value or proof

/-- An `add` instruction is never valid on a stack with only one element. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem invalid_program_add_one: ¬ ValidProgram 1 (add :: p')  := by -- states and proves theorem `invalid_program_add_one`
  grind -- asks the `grind` automation to finish the proof
  -- intro h
  -- cases h

/-- If a program starting with `add` is valid, then the rest is valid for a smaller stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_of_add {k: Nat} (h : ValidProgram (k + 2) (add :: p')) : ValidProgram (k + 1) p' := by -- states and proves theorem `valid_program_of_add`
  grind -- asks the `grind` automation to finish the proof

/-- A `pop` instruction is never valid on an empty stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem invalid_program_pop_zero: ¬ ValidProgram 0 (pop :: p')  := by -- states and proves theorem `invalid_program_pop_zero`
  grind -- asks the `grind` automation to finish the proof

/-- If a program starting with `pop` is valid, then the rest is valid for a smaller stack. -/
@[simp] -- annotation controlling elaboration, simplification, or automation
theorem valid_program_of_pop {k: Nat} (h : ValidProgram (k +1) (pop :: p')) : ValidProgram k p' := by -- states and proves theorem `valid_program_of_pop`
  grind -- asks the `grind` automation to finish the proof

/--
Evaluates a program that is guaranteed to be valid for the initial stack size.
This function is total and does not need to return `Option`.
-/
def evaluate (p: Program) (initStack: Stack) (h: ValidProgram initStack.length p) : Stack := -- defines `evaluate`
  match p with -- splits computation into cases by pattern matching
  | [] => initStack -- handles this pattern-matching case
  | push n :: p' => -- handles this pattern-matching case
      evaluate p' (n :: initStack) (valid_program_of_push h) -- continues the Lean declaration above
  | add :: p' => -- handles this pattern-matching case
      match initStack with -- splits computation into cases by pattern matching
      | x :: y :: zs => -- handles this pattern-matching case
        evaluate p' ((x + y) :: zs) (valid_program_of_add h) -- continues the Lean declaration above
      | [x] => by -- handles this pattern-matching case
        simp at h -- simplifies the current goal or hypotheses
  | pop :: p' => -- handles this pattern-matching case
      match initStack with -- splits computation into cases by pattern matching
      | [] => by -- handles this pattern-matching case
        simp at h -- simplifies the current goal or hypotheses
      | x :: ys => evaluate p' ys (valid_program_of_pop h) -- handles this pattern-matching case

#eval evaluate [push 2, push 3, add] [] (by grind) -- runs this expression as a tutorial check

#eval evaluate [push 2, add] [3] (by grind) -- runs this expression as a tutorial check

/--
error: `grind` failed
case grind
h : ¬ValidProgram [].length [push 2, add]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] ¬ValidProgram [].length [push 2, add]
    [prop] [].length = 0
    [prop] ValidProgram ([].length + 1) [add] → ValidProgram [].length [push 2, add]
  [eqc] True propositions
    [prop] [].length = 0
    [prop] ValidProgram ([].length + 1) [add] → ValidProgram [].length [push 2, add]
  [eqc] False propositions
    [prop] ValidProgram [].length [push 2, add]
    [prop] ValidProgram ([].length + 1) [add]
  [eqc] Equivalence classes
    [eqc] {[].length, 0}
    [eqc] others
      [eqc] {↑[].length, ↑0}
  [ematch] E-matching patterns
    [thm] List.eq_nil_of_length_eq_zero: [@List.length #2 #1]
    [thm] List.length_nil: [@List.length #0 (@List.nil _)]
    [thm] List.length_cons: [@List.length #2 (@List.cons _ #1 #0)]
    [thm] valid_program_nil: [ValidProgram #0 `[[]]]
    [thm] valid_program_push: [ValidProgram #1 (@List.cons `[Instr] (push #2) #3)]
    [thm] valid_program_add: [ValidProgram (#1 + 2) (@List.cons `[Instr] `[add] #2)]
  [cutsat] Assignment satisfying linear constraints
    [assign] [].length := 0
  [ring] Rings
    [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
      [basis] Basis
        [_] ↑[].length = 0
    [ring] Ring `Int`
      [basis] Basis
        [_] ↑[].length = 0
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] List.eq_nil_of_length_eq_zero ↦ 1
    [thm] List.length_nil ↦ 1
    [thm] valid_program_push ↦ 1
-/
#guard_msgs in -- checks that the following command produces the expected message
#eval evaluate [push 2, add] [] (by grind) -- runs this expression as a tutorial check

macro "evaluate%" p:term  : term => -- declares a custom macro form
  `(evaluate $p [] (by grind)) -- continues the Lean declaration above

#eval evaluate% [push 2, push 3, add] -- runs this expression as a tutorial check

/--
A program is valid for a given stack size if and only if its safe evaluation
on a stack of that size succeeds (returns `some`).
-/
theorem valid_iff_eval?_some (p: Program) (s: Stack) : ValidProgram s.length p ↔ (eval? p s) ≠ none := by -- states and proves theorem `valid_iff_eval?_some`
  constructor -- builds the required constructor or pair of goals
  · intro h -- focuses the next proof branch
    match p with -- splits computation into cases by pattern matching
    | [] => grind [eval?] -- handles this pattern-matching case
    | push n :: p' => -- handles this pattern-matching case
        have h' : ValidProgram (s.length + 1) p' := valid_program_of_push h -- records an intermediate fact for the proof
        have ih := (valid_iff_eval?_some p' (n ::s)) -- records an intermediate fact for the proof
        grind [eval?] -- asks the `grind` automation to finish the proof
    | add :: p' => -- handles this pattern-matching case
        match s with -- splits computation into cases by pattern matching
        | x :: y :: zs => -- handles this pattern-matching case
           have h' := valid_program_of_add h -- records an intermediate fact for the proof
           have ih := (valid_iff_eval?_some p' ((x + y) :: zs)) -- records an intermediate fact for the proof
           grind [eval?] -- asks the `grind` automation to finish the proof
    | pop :: p' => -- handles this pattern-matching case
        match s with -- splits computation into cases by pattern matching
        | x :: ys => -- handles this pattern-matching case
            have h' : ValidProgram ys.length p' := valid_program_of_pop h -- records an intermediate fact for the proof
            have ih := (valid_iff_eval?_some p' ys) -- records an intermediate fact for the proof
            grind [eval?] -- asks the `grind` automation to finish the proof
  · intro h -- focuses the next proof branch
    match p with -- splits computation into cases by pattern matching
    | [] => grind [eval?] -- handles this pattern-matching case
    | push n :: p' => -- handles this pattern-matching case
        have ih := (valid_iff_eval?_some p' (n ::s)) -- records an intermediate fact for the proof
        grind [eval?] -- asks the `grind` automation to finish the proof
    | add :: p' => -- handles this pattern-matching case
        match s with -- splits computation into cases by pattern matching
        | x :: y :: zs => -- handles this pattern-matching case
           have ih := (valid_iff_eval?_some p' ((x + y) :: zs)) -- records an intermediate fact for the proof
           grind [eval?] -- asks the `grind` automation to finish the proof
    | pop :: p' => -- handles this pattern-matching case
        match s with -- splits computation into cases by pattern matching
        | x :: ys => -- handles this pattern-matching case
            have ih := (valid_iff_eval?_some p' ys) -- records an intermediate fact for the proof
            simp -- simplifies the current goal or hypotheses
            apply valid_program_pop -- reduces the goal using this theorem or constructor
            simp [eval?] at h -- simplifies the current goal or hypotheses
            grind -- asks the `grind` automation to finish the proof

end stack_machine -- closes the current namespace or section

end langur -- closes the current namespace or section
