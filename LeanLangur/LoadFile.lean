import Lean -- imports definitions and theorems used below

/-!
# Loading Files into Lean

This module provides tools for loading and parsing external files (like Markdown and JSON)
directly into Lean 4 environments, both as terms and via commands.
-/

namespace langur -- starts a namespace to group the tutorial definitions

open IO FS System Lean -- opens names so constructors or helpers can be written unqualified

/--
Reads the content of `README.md`.
-/
def readme : IO String := readFile "README.md" -- defines `readme`

#eval readme -- runs this expression as a tutorial check

/--
Reads the content of `lake-manifest.json`.
-/
def lakeManifest : IO String := readFile "lake-manifest.json" -- defines `lakeManifest`

#eval lakeManifest -- runs this expression as a tutorial check

/--
Parses the `lake-manifest.json` file into a `Json` object.
-/
def lakeManifestJson : IO Json := do -- defines `lakeManifestJson`
  let content ← lakeManifest -- binds an intermediate value for the following expression
  match Json.parse content with -- splits computation into cases by pattern matching
  | .ok json => return json -- handles this pattern-matching case
  | .error err => IO.throwServerError s!"Failed to parse JSON: {err}" -- handles this pattern-matching case

#eval lakeManifestJson -- runs this expression as a tutorial check

/--
An example of using the `json%` macro.
-/
def jsonEg := json% {"name": "LeanLangur", "version": "0.1.0", "dependencies": {"lean": "4.0.0"}} -- defines `jsonEg`

#eval jsonEg -- runs this expression as a tutorial check

open Lean Meta Elab Term PrettyPrinter Tactic Command Parser -- opens names so constructors or helpers can be written unqualified

declare_syntax_cat filepath -- continues the Lean declaration above
syntax str : filepath -- declares new parser syntax
syntax filepath " / " str : filepath -- declares new parser syntax

/--
Helper function to convert `filepath` syntax into a `System.FilePath`.
-/
partial def filePath : TSyntax `filepath → System.FilePath -- defines the partial function `filePath`
  | `(filepath| $s:str) => s.getString -- handles this pattern-matching case
  | `(filepath| $fs:filepath / $s) => (filePath fs / s.getString) -- handles this pattern-matching case
  | _ => System.FilePath.mk "" -- handles this pattern-matching case

/--
A term-level macro to load the contents of a file as a string.
Usage: `load_file% "path/to/file" ;`
-/
syntax (name:= loadFileTerm) "load_file%" (ppSpace filepath)? " ; " : term -- declares new parser syntax
@[term_elab loadFileTerm] def loadFileTermImpl : TermElab := fun stx _ => do -- annotation controlling elaboration, simplification, or automation
  match stx with -- splits computation into cases by pattern matching
  | `(load_file% $file:filepath ; ) => -- handles this pattern-matching case
    let filePath : System.FilePath := filePath file -- binds an intermediate value for the following expression
    let content ← IO.FS.readFile filePath -- binds an intermediate value for the following expression
    let stx' := Syntax.mkStrLit content -- binds an intermediate value for the following expression
    TryThis.addSuggestion stx stx' -- continues the Lean declaration above
    return mkStrLit content -- returns this value from the monadic block
  | _ => throwUnsupportedSyntax -- handles this pattern-matching case

/--
Example of loading `README.md` as a string.
-/
def egFile := load_file% "README.md" ; -- defines `egFile`

#eval egFile -- runs this expression as a tutorial check

/--
A term-level macro to load and parse a JSON file.
Usage: `load_json% "path/to/file" ;`
-/
syntax (name:= loadJsonTerm) "load_json%" (ppSpace filepath)? " ; " : term -- declares new parser syntax
@[term_elab loadJsonTerm] def loadJsonTermImpl : TermElab := fun stx _ => do -- annotation controlling elaboration, simplification, or automation
  match stx with -- splits computation into cases by pattern matching
  | `(load_json% $file:filepath ; ) => -- handles this pattern-matching case
    let filePath : System.FilePath := filePath file -- binds an intermediate value for the following expression
    let content ← IO.FS.readFile filePath -- binds an intermediate value for the following expression
    let .ok json := Json.parse content | throwError "Failed to parse JSON: {content}" -- binds an intermediate value for the following expression
    let rhs := "json% " ++ json.pretty -- binds an intermediate value for the following expression
    TryThis.addSuggestion stx rhs -- continues the Lean declaration above
    let .ok termStx := runParserCategory (← getEnv) `term rhs | throwError "Failed to parse JSON syntax: {rhs}" -- binds an intermediate value for the following expression
    elabTerm termStx (mkConst ``Json) -- continues the Lean declaration above
  | _ => throwUnsupportedSyntax -- handles this pattern-matching case

-- def egJson := load_json% "lake-manifest.json" ;

-- #eval egJson

/--
A command-level macro to load a file and define it as a constant.
Usage: `#load_file identifier "path/to/file"`
-/
syntax (name:= loadFile) "#load_file" (ppSpace ident)? (ppSpace filepath)? : command -- declares new parser syntax
@[command_elab loadFile] def loadFileImpl : CommandElab := fun stx  => -- annotation controlling elaboration, simplification, or automation
 Command.liftTermElabM  do -- continues the Lean declaration above
  match stx with -- splits computation into cases by pattern matching
  | `(command| #load_file $id:ident $file) => -- handles this pattern-matching case
    let filePath : System.FilePath := filePath file -- binds an intermediate value for the following expression
    let content ← try -- binds an intermediate value for the following expression
        IO.FS.readFile filePath -- continues the Lean declaration above
      catch _ => -- maps this case or syntax pattern to its result
        if ← filePath.isDir then -- branches on this decidable condition
          let files ← filePath.readDir -- binds an intermediate value for the following expression
          let files := files.map (·.fileName) -- binds an intermediate value for the following expression
          for f in files do -- iterates through these values in the monadic block
            let name := Syntax.mkStrLit f -- binds an intermediate value for the following expression
            let newPath ← `(filepath| $file / $name) -- binds an intermediate value for the following expression
            let newCommand ← `(command| #load_file $id $newPath) -- binds an intermediate value for the following expression
            TryThis.addSuggestion stx newCommand -- continues the Lean declaration above
        else -- handles the alternative branch
          logWarning s!"Failed to read file: {filePath}" -- continues the Lean declaration above
        return -- continues the Lean declaration above
    let name := id.getId -- binds an intermediate value for the following expression
    let contentLit := Syntax.mkStrLit content -- binds an intermediate value for the following expression
    let nameIdent := mkIdent name -- binds an intermediate value for the following expression
    let textCmd ← `(command| def $nameIdent := $contentLit:str) -- binds an intermediate value for the following expression
    TryThis.addSuggestion (header := "Load source:\n") stx textCmd -- gives the value or proof for this declaration
  | `(command| #load_file $file:filepath) => -- handles this pattern-matching case
    let filePath : System.FilePath := filePath file -- binds an intermediate value for the following expression
    let content ← try -- binds an intermediate value for the following expression
        IO.FS.readFile filePath -- continues the Lean declaration above

      catch _ => -- maps this case or syntax pattern to its result
        if ← filePath.isDir then -- branches on this decidable condition
          let files ← filePath.readDir -- binds an intermediate value for the following expression
          let files := files.map (·.fileName) -- binds an intermediate value for the following expression
          for f in files do -- iterates through these values in the monadic block
            let name := Syntax.mkStrLit f -- binds an intermediate value for the following expression
            let newPath ← `(filepath| $file / $name) -- binds an intermediate value for the following expression
            let newCommand ← `(command| #load_file $newPath:filepath) -- binds an intermediate value for the following expression
            TryThis.addSuggestion stx newCommand -- continues the Lean declaration above
        else -- handles the alternative branch
          logWarning s!"Failed to read file: {filePath}" -- continues the Lean declaration above
        return -- continues the Lean declaration above
    let name := filePath.fileName.getD "source" -- binds an intermediate value for the following expression
    let contentLit := Syntax.mkStrLit content -- binds an intermediate value for the following expression
    let nameIdent := mkIdent name.toName -- binds an intermediate value for the following expression
    let textCmd ← `(command| def $nameIdent := $contentLit:str) -- binds an intermediate value for the following expression
    TryThis.addSuggestion (header := "Load source:\n") stx textCmd -- gives the value or proof for this declaration
  | `(command| #load_file $id:ident) => -- handles this pattern-matching case
    let filePath : System.FilePath := "." -- binds an intermediate value for the following expression
    let files ← filePath.readDir -- binds an intermediate value for the following expression
    let files := files.map (·.fileName) -- binds an intermediate value for the following expression
    for f in files do -- iterates through these values in the monadic block
      let name := Syntax.mkStrLit f -- binds an intermediate value for the following expression
      let newPath ← `(filepath| $name:str) -- binds an intermediate value for the following expression
      let newCommand ← `(command| #load_file $id $newPath:filepath) -- binds an intermediate value for the following expression
      TryThis.addSuggestion stx newCommand -- continues the Lean declaration above
  | `(command| #load_file) => -- handles this pattern-matching case
    let filePath : System.FilePath := "." -- binds an intermediate value for the following expression
    let files ← filePath.readDir -- binds an intermediate value for the following expression
    let files := files.map (·.fileName) -- binds an intermediate value for the following expression
    for f in files do -- iterates through these values in the monadic block
      let name := Syntax.mkStrLit f -- binds an intermediate value for the following expression
      let newPath ← `(filepath| $name:str) -- binds an intermediate value for the following expression
      let newCommand ← `(command| #load_file $newPath:filepath) -- binds an intermediate value for the following expression
      TryThis.addSuggestion stx newCommand -- continues the Lean declaration above
  | _ => throwUnsupportedSyntax -- handles this pattern-matching case

-- #consider "Hello there."

declare_syntax_cat json_wrap -- continues the Lean declaration above
syntax json : json_wrap -- declares new parser syntax

/--
Converts a `Json` object into a `json` syntax object.
-/
def getJsonSyntax (js : Json) : MetaM <| TSyntax `json := do -- defines `getJsonSyntax`
  let .ok stx := -- binds an intermediate value for the following expression
    runParserCategory (← getEnv) `json_wrap js.pretty | throwError "Failed to parse JSON: {js}" -- continues the Lean declaration above
  match stx with -- splits computation into cases by pattern matching
  | `(json_wrap| $j:json) => -- handles this pattern-matching case
    return j -- returns this value from the monadic block
  | _ => throwError "Unexpected syntax: {stx}" -- handles this pattern-matching case

/--
A command to parse and display a JSON snippet.
-/
syntax (name:= rt_json) "#rt_json" ppSpace json : command -- declares new parser syntax

@[command_elab rt_json] def elabRtJsonImpl : CommandElab -- annotation controlling elaboration, simplification, or automation
| stx_cmd@`(command| #rt_json $js:json) => -- handles this pattern-matching case
  Command.liftTermElabM do -- continues the Lean declaration above
  let tExp ← elabTerm (← `(json% $js)) (mkConst ``Json) -- binds an intermediate value for the following expression
  Term.synthesizeSyntheticMVarsNoPostponing -- continues the Lean declaration above
  let term ← unsafe evalExpr Json (mkConst ``Json) tExp -- binds an intermediate value for the following expression
  let stx ← getJsonSyntax term -- extract syntax from JSON
  logInfo m!"JSON Syntax: {stx}" -- continues the Lean declaration above
  let n := mkIdent `json_example -- binds an intermediate value for the following expression
  let cmd ← `(command| def $n := json% $stx:json) -- binds an intermediate value for the following expression
  logInfo m!"Command: {cmd}" -- continues the Lean declaration above
  TryThis.addSuggestion stx_cmd cmd -- continues the Lean declaration above
  logInfo m!"Done" -- continues the Lean declaration above
| _ => throwUnsupportedSyntax -- handles this pattern-matching case

-- #rt_json {"c": {"d": -3.4}, "b": [true, false, null], "a": 1}

end langur -- closes the current namespace or section
