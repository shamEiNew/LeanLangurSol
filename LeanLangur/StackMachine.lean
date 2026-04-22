import LeanLangur.Basic

/-!
# Stack Machine

This module defines a simple stack-based machine with instructions for pushing values,
popping values, and performing addition. It includes both unsafe and safe (option-returning)
execution engines, as well as a verified evaluator that uses a `ValidProgram` predicate.
-/

namespace langur

namespace stack_machine

/--
Instructions for the stack machine.
-/
inductive Instr
  | push (n : Nat)
  | pop
  | add
  deriving Repr

open Instr

/-- A stack is represented as a list of natural numbers. -/
abbrev Stack := List Nat

/-- A program is a list of instructions. -/
abbrev Program := List Instr

/--
Unsafe evaluation of a program.
Assumes the stack has enough elements for `pop` and `add` operations.
-/
def eval! (p: Program) (s: Stack) : Stack :=
  match p with
  | [] => s
  | push n :: p' => eval! p' (n :: s)
  | pop :: p' =>
      eval! p' s.tail!
  | add :: p' =>
      let x := s.head!
      let y := s.tail!.head!
      eval! p' ((x + y) :: s.tail!.tail!)

/--
Safe evaluation of a program using `Option`.
Returns `none` if an instruction is executed on an insufficient stack.
-/
def eval? (p: Program) (s: Stack) : Option Stack :=
  match p with
  | [] => some s
  | push n :: p' => eval? p' (n :: s)
  | add :: p' =>
      match s with
      | x :: y :: zs => eval? p' ((x + y) :: zs)
      | _ => none
  | pop :: p' =>
      match s with
      | _ :: ys => eval? p' ys
      | _ => none

/--
Inductive predicate for a valid program given an initial stack size.
Ensures that the stack will never underflow during execution.
-/
@[grind cases]
inductive ValidProgram : (initStackSize : Nat) → (p : Program) → Prop
  /-- The empty program is valid with any initial stack -/
  | nil : ValidProgram n []
  /-- If the first instruction is a push and the rest of the program is valid  with initial stack size `s + 1` then the program is valid with initial stack size `s` -/
  | push  {p : Program} :
      ValidProgram (n + 1) p →
      ValidProgram n (push k :: p)
  /-- If the first instruction is a pop and the rest of the program is valid with initial stack size `s` then the program is valid with initial stack size `s + 1` -/
  | pop  {p : Program} :
      ValidProgram n p →
      ValidProgram (n + 1) (pop :: p)
  /-- If the first instruction is an add and the rest of the program is valid with initial stack size `s + 2` then the program is valid with initial stack size `s + 1` -/
  | add {p : Program} :
      ValidProgram (n + 1) p →
      ValidProgram (n + 2) (add :: p)

/-- The empty program is always valid. -/
@[simp, grind .]
theorem valid_program_nil : ValidProgram n [] := ValidProgram.nil

/-- Pushing a value to a stack of size `n` results in a valid program if the rest is valid for `n+1`. -/
@[simp, grind .]
theorem valid_program_push (n: Nat) (h : ValidProgram (n + 1) p') :
    ValidProgram n (push k :: p') :=    ValidProgram.push h

/-- Adding values on a stack of size `k+2` is valid if the rest is valid for `k+1`. -/
@[simp, grind .]
theorem valid_program_add (k: Nat) (h : ValidProgram (k + 1) p') :
  ValidProgram (k + 2) (add :: p') :=
  ValidProgram.add h

/-- Popping from a stack of size `n+1` is valid if the rest is valid for `n`. -/
@[simp]
theorem valid_program_pop (h : ValidProgram n p') :
  ValidProgram (n + 1) (pop :: p') :=
  ValidProgram.pop h

example (a b: Nat) : ValidProgram n [push a, push b, add] := by
  grind

example (a b c : Nat) : ValidProgram 0 [push a, push b, add, push c, add] := by
  grind (ematch := 7)

/-- If a program starting with `push` is valid, then the rest of the program is valid for a larger stack. -/
@[simp]
theorem valid_program_of_push {k: Nat} (h : ValidProgram k (push a :: p')) : ValidProgram (k + 1) p' := by
  cases h
  assumption

/-- An `add` instruction is never valid on an empty stack. -/
@[simp]
theorem invalid_program_add_zero: ¬ ValidProgram 0 (add :: p')  := by
  intro h
  cases h

/-- An `add` instruction is never valid on a stack with only one element. -/
@[simp]
theorem invalid_program_add_one: ¬ ValidProgram 1 (add :: p')  := by
  grind
  -- intro h
  -- cases h

/-- If a program starting with `add` is valid, then the rest is valid for a smaller stack. -/
@[simp]
theorem valid_program_of_add {k: Nat} (h : ValidProgram (k + 2) (add :: p')) : ValidProgram (k + 1) p' := by
  grind

/-- A `pop` instruction is never valid on an empty stack. -/
@[simp]
theorem invalid_program_pop_zero: ¬ ValidProgram 0 (pop :: p')  := by
  grind

/-- If a program starting with `pop` is valid, then the rest is valid for a smaller stack. -/
@[simp]
theorem valid_program_of_pop {k: Nat} (h : ValidProgram (k +1) (pop :: p')) : ValidProgram k p' := by
  grind

/--
Evaluates a program that is guaranteed to be valid for the initial stack size.
This function is total and does not need to return `Option`.
-/
def evaluate (p: Program) (initStack: Stack) (h: ValidProgram initStack.length p) : Stack :=
  match p with
  | [] => initStack
  | push n :: p' =>
      evaluate p' (n :: initStack) (valid_program_of_push h)
  | add :: p' =>
      match initStack with
      | x :: y :: zs =>
        evaluate p' ((x + y) :: zs) (valid_program_of_add h)
      | [x] => by
        simp at h
  | pop :: p' =>
      match initStack with
      | [] => by
        simp at h
      | x :: ys => evaluate p' ys (valid_program_of_pop h)

#eval evaluate [push 2, push 3, add] [] (by grind)

#eval evaluate [push 2, add] [3] (by grind)

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
#guard_msgs in
#eval evaluate [push 2, add] [] (by grind)

/--
A program is valid for a given stack size if and only if its safe evaluation
on a stack of that size succeeds (returns `some`).
-/
theorem valid_iff_eval?_some (p: Program) (s: Stack) : ValidProgram s.length p ↔ (eval? p s) ≠ none := by
  constructor
  · intro h
    match p with
    | [] => grind [eval?]
    | push n :: p' =>
        have h' : ValidProgram (s.length + 1) p' := valid_program_of_push h
        have ih := (valid_iff_eval?_some p' (n ::s))
        grind [eval?]
    | add :: p' =>
        match s with
        | x :: y :: zs =>
           have h' := valid_program_of_add h
           have ih := (valid_iff_eval?_some p' ((x + y) :: zs))
           grind [eval?]
    | pop :: p' =>
        match s with
        | x :: ys =>
            have h' : ValidProgram ys.length p' := valid_program_of_pop h
            have ih := (valid_iff_eval?_some p' ys)
            grind [eval?]
  · intro h
    match p with
    | [] => grind [eval?]
    | push n :: p' =>
        have ih := (valid_iff_eval?_some p' (n ::s))
        grind [eval?]
    | add :: p' =>
        match s with
        | x :: y :: zs =>
           have ih := (valid_iff_eval?_some p' ((x + y) :: zs))
           grind [eval?]
    | pop :: p' =>
        match s with
        | x :: ys =>
            have ih := (valid_iff_eval?_some p' ys)
            simp
            apply valid_program_pop
            simp [eval?] at h
            grind

end stack_machine

end langur
