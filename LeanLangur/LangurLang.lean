import Lean -- imports definitions and theorems used below
import Std -- imports definitions and theorems used below

namespace langur -- starts a namespace to group the tutorial definitions

open Lean Meta Elab Term -- opens names so constructors or helpers can be written unqualified

/-!
# LangurLang: A tiny imperative language

Inspired by the IMP language in Software Foundations. We have only natural number variables, and the following statements:
* Assignment: `x := expr`
* Conditional: `if (cond) { ... } else { ... }`
* While loops: `while (cond) { ... }`
* Print statements: `print expr`

We use a *shallow embedding*, so natural numbers are represented using Lean's `Nat` type and Booleans using Lean's `Bool` type.

We skip at first extracting natural numbers from expressions, and directly evaluate expressions to `Nat`, `Bool` or `String` in a context of variable bindings.
-/
def exprRelVars (vars: List (Name × Nat)) (stx: Syntax.Term) : MetaM Syntax.Term := -- defines `exprRelVars`
  match vars with -- splits computation into cases by pattern matching
  | [] => return stx -- handles this pattern-matching case
  | (n, val) :: tail => do -- handles this pattern-matching case
    let nId := mkIdent n -- binds an intermediate value for the following expression
    let nat := mkIdent ``Nat -- binds an intermediate value for the following expression
    let inner ← -- binds an intermediate value for the following expression
      exprRelVars tail stx -- continues the Lean declaration above
    let arg := Syntax.mkNumLit <| toString val -- binds an intermediate value for the following expression
    `((fun ($nId : $nat) => $inner) $arg) -- maps this case or syntax pattern to its result


def getNatRelVarsM (vars: List (Name × Nat)) -- defines `getNatRelVarsM`
  (t: Syntax.Term) : TermElabM Nat := do -- continues the surrounding Lean expression
  let stx ← exprRelVars vars t -- binds an intermediate value for the following expression
  let e ← withoutErrToSorry do -- binds an intermediate value for the following expression
    elabTermEnsuringType stx (mkConst ``Nat) -- continues the Lean declaration above
  Term.synthesizeSyntheticMVarsNoPostponing -- continues the Lean declaration above
  unsafe evalExpr Nat (mkConst ``Nat) e -- continues the Lean declaration above

def getBoolRelVarsM (vars: List (Name × Nat)) -- defines `getBoolRelVarsM`
  (t: Syntax.Term) : TermElabM Bool := do -- continues the surrounding Lean expression
  let stx ← exprRelVars vars t -- binds an intermediate value for the following expression
  let e ← elabTermEnsuringType stx (mkConst ``Bool) -- binds an intermediate value for the following expression
  Term.synthesizeSyntheticMVarsNoPostponing -- continues the Lean declaration above
  unsafe evalExpr Bool (mkConst ``Bool) e -- continues the Lean declaration above

def getStrRelVarsM (vars: List (Name × Nat)) -- defines `getStrRelVarsM`
  (t: Syntax.Term) : TermElabM String := do -- continues the surrounding Lean expression
  let stx ← exprRelVars vars t -- binds an intermediate value for the following expression
  let e ← withoutErrToSorry do -- binds an intermediate value for the following expression
    elabTermEnsuringType stx (mkConst ``String) -- continues the Lean declaration above
  Term.synthesizeSyntheticMVarsNoPostponing -- continues the Lean declaration above
  unsafe evalExpr String (mkConst ``String) e -- continues the Lean declaration above

namespace LangurLang -- starts a namespace to group the tutorial definitions

-- variables with name
abbrev State := Std.HashMap Name Nat -- introduces `State` as a reducible abbreviation

abbrev LangurLangM := -- introduces `LangurLangM` as a reducible abbreviation
  StateT State TermElabM -- continues the Lean declaration above

def getVar (name: Name) : LangurLangM Nat := do -- defines `getVar`
  let m ← get -- binds an intermediate value for the following expression
  return m.get! name -- returns this value from the monadic block

def setVar (name : Name) (value : Nat) : -- defines `setVar`
  LangurLangM Unit := do -- gives the value or proof for this declaration
  modify (fun m => m.insert name value) -- maps this case or syntax pattern to its result

def getNatInCtxM (stx: Syntax.Term) : LangurLangM Nat := do -- defines `getNatInCtxM`
  let m ← get -- binds an intermediate value for the following expression
  getNatRelVarsM m.toList stx -- continues the Lean declaration above

def getBoolInCtxM (stx: Syntax.Term) : LangurLangM Bool := do -- defines `getBoolInCtxM`
  let m ← get -- binds an intermediate value for the following expression
  getBoolRelVarsM m.toList stx -- continues the Lean declaration above

def getStrInCtxM (stx: Syntax.Term) : LangurLangM String := do -- defines `getStrInCtxM`
  let m ← get -- binds an intermediate value for the following expression
  getStrRelVarsM m.toList stx -- continues the Lean declaration above

declare_syntax_cat langur_statement -- continues the Lean declaration above

syntax langur_block := "{" sepBy(langur_statement, ";", ";", allowTrailingSep) "}" -- declares new parser syntax

syntax langur_program := sepBy(langur_statement, ";", ";", allowTrailingSep) -- declares new parser syntax

syntax langur_block : langur_statement -- declares new parser syntax

syntax ident ":=" term : langur_statement -- declares new parser syntax

syntax "if" ppSpace "(" term ")" ppSpace langur_block "else" langur_block : langur_statement -- declares new parser syntax

syntax "while" "(" term ")" ppSpace langur_block : langur_statement -- declares new parser syntax

syntax "print" term  : langur_statement -- declares new parser syntax

partial def interpretM : -- defines the partial function `interpretM`
  TSyntax `langur_statement → LangurLangM Unit -- continues the Lean declaration above
| `(langur_statement| {$s;*}) => do -- handles this pattern-matching case
    let stmts := s.getElems -- binds an intermediate value for the following expression
    for stmt in stmts do -- iterates through these values in the monadic block
      interpretM stmt -- continues the Lean declaration above
| `(langur_statement| $name:ident := $val) => do -- handles this pattern-matching case
  let value ← getNatInCtxM val -- binds an intermediate value for the following expression
  let n := name.getId -- binds an intermediate value for the following expression
  setVar n value -- continues the Lean declaration above
| `(langur_statement| if ($p) $t else $e) => do -- handles this pattern-matching case
  let c ← getBoolInCtxM p -- binds an intermediate value for the following expression
  if c -- branches on this decidable condition
    then runBlockM t -- continues the Lean declaration above
    else runBlockM e -- handles the alternative branch
| `(langur_statement| while ($p) $b) => do -- handles this pattern-matching case
  let rec loop : LangurLangM Unit := do -- binds an intermediate value for the following expression
    let c ← getBoolInCtxM p -- binds an intermediate value for the following expression
    if c then -- branches on this decidable condition
      runBlockM b -- continues the Lean declaration above
      loop -- continues the Lean declaration above
  loop -- continues the Lean declaration above
| stat@`(langur_statement| print $s) => do -- handles this pattern-matching case
  let str ← getStrInCtxM s -- binds an intermediate value for the following expression
  logInfoAt stat str -- continues the Lean declaration above
| _ => throwUnsupportedSyntax -- handles this pattern-matching case
where runBlockM (bs : TSyntax ``langur_block): LangurLangM Unit := -- begins the local implementation block for this declaration
  match bs with -- splits computation into cases by pattern matching
  | `(langur_block| {$s;*}) => -- handles this pattern-matching case
    let stmts := s.getElems -- binds an intermediate value for the following expression
    for stmt in stmts do -- iterates through these values in the monadic block
      interpretM stmt -- continues the Lean declaration above
  | _ => throwUnsupportedSyntax -- handles this pattern-matching case

def interpretProgramM (pgm: TSyntax ``langur_program) : LangurLangM Unit := do -- defines `interpretProgramM`
  match pgm with -- splits computation into cases by pattern matching
  | `(langur_program| $s;*) => -- handles this pattern-matching case
    let stmts := s.getElems -- binds an intermediate value for the following expression
    for stmt in stmts do -- iterates through these values in the monadic block
      interpretM stmt -- continues the Lean declaration above
  | _ => throwUnsupportedSyntax -- handles this pattern-matching case

def climbProgramM -- defines `climbProgramM`
  (pgm: TSyntax ``langur_program) (init: State) : TermElabM (State) := do -- continues the surrounding Lean expression
  let (_, m) ← interpretProgramM pgm |>.run init -- binds an intermediate value for the following expression
  return m -- returns this value from the monadic block

elab "#leap" ss:langur_program r:"return" : command  => -- declares an elaborator for custom syntax
  Command.liftTermElabM do -- continues the Lean declaration above
  let (_, m) ← interpretProgramM ss |>.run {} -- binds an intermediate value for the following expression
  logInfoAt r m!"Final variable state: {m.toList}" -- continues the Lean declaration above

elab "climb%" ss:langur_program -- declares an elaborator for custom syntax
    "return" v:term : term  => do -- maps this case or syntax pattern to its result
    let (_, m) ← interpretProgramM ss |>.run {} -- binds an intermediate value for the following expression
    let t ← exprRelVars m.toList v -- binds an intermediate value for the following expression
    elabTerm t none -- continues the Lean declaration above

macro "climb%" ss:langur_program "from%" init:langur_program -- declares a custom macro form
    "return" v:term : term  => do -- maps this case or syntax pattern to its result
    match init, ss with -- splits computation into cases by pattern matching
    | `(langur_program| $s;*), `(langur_program| $t;*) => do -- handles this pattern-matching case
      let lines := s.getElems ++ t.getElems -- binds an intermediate value for the following expression
      let prog ← `(langur_program| $lines;*) -- binds an intermediate value for the following expression
      `(climb% $prog return $v) -- continues the Lean declaration above
    | _, _ => Macro.throwError "Invalid syntax in climb% from% ... return ..." -- handles this pattern-matching case

end LangurLang -- closes the current namespace or section

end langur -- closes the current namespace or section
