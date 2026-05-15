import Lean -- imports definitions and theorems used below

namespace langur -- starts a namespace to group the tutorial definitions

open IO FS System -- opens names so constructors or helpers can be written unqualified

/-!
# File Monad and Security

This module defines a custom monad `FileM` for file operations and a security framework
to verify that file programs only access safe paths and write safe values.
-/

namespace file_access -- starts a namespace to group the tutorial definitions

/--
Basic file commands.
-/
inductive FileCmd : Type → Type where -- declares the inductive type or proposition `FileCmd`
| read  : FilePath → FileCmd String -- declares another constructor or syntax alternative
| write : FilePath → String → FileCmd Unit -- declares another constructor or syntax alternative

/--
A free monad for file operations.
-/
inductive FileM : Type → Type _ where -- declares the inductive type or proposition `FileM`
| pure {α : Type} : α → FileM α -- declares another constructor or syntax alternative
| cons : FileCmd β → (k: β → FileM α) → FileM α -- declares another constructor or syntax alternative

/--
FlatMap operation for the `FileM` monad.
-/
def FileM.flatMap {α β : Type} (f : α → FileM β) : FileM α → FileM β -- defines `FileM.flatMap`
  | .pure a => f a -- matches a completed `FileM` value and returns `f a`
  | .cons cmd k => .cons cmd (fun b => (k b).flatMap f) -- matches a pending `FileM` command and returns `.cons cmd (fun b => (k b).flatMap f)`

instance : Monad FileM where -- provides an instance for typeclass search
  pure := FileM.pure -- gives the value or proof for this declaration
  bind x f := FileM.flatMap f x -- gives the value or proof for this declaration

/--
Reads the contents of a file.
-/
def FileM.read (path : FilePath) : FileM String := -- defines `FileM.read`
    .cons (FileCmd.read path) FileM.pure

/--
Writes contents to a file.
-/
def FileM.write (path : FilePath) (contents : String) : FileM Unit := -- defines `FileM.write`
    .cons (FileCmd.write path contents) FileM.pure

/--
Runs a `FileM` program in the `IO` monad.
-/
def FileM.run : FileM α → IO α -- defines `FileM.run`
    | FileM.pure a => return a -- matches a completed `FileM` value and returns a
    | FileM.cons cmd k => -- matches a pending `FileM` command and inspects `cmd` in a nested match to decide the result
        match cmd with -- splits computation into cases by pattern matching
        | FileCmd.read path => do -- matches a file-read command and computes intermediate values and returns `FileM.run (k contents)`
            let contents ← IO.FS.readFile path -- binds an intermediate value for the following expression
            FileM.run (k contents)
        | FileCmd.write path contents => do -- matches a file-write command and writes the requested file before resuming the computation
            IO.FS.writeFile path contents
            FileM.run (k ())

/--
Map operation for the `FileM` monad.
-/
abbrev FileM.map {α β : Type} (f : α → β) : FileM α → FileM β := fun x => do -- introduces `FileM.map` as a reducible abbreviation
    let a ← x -- binds an intermediate value for the following expression
    return f a -- returns this value from the monadic block

/--
Predicate for safe values that can be written to files.
-/
inductive SafeVal : {α : Type} → α → Prop where -- declares the inductive type or proposition `SafeVal`
| nat(n) : SafeVal (n : Nat) -- declares another constructor or syntax alternative
| strAppend (s t : String) : SafeVal s → SafeVal t → SafeVal (s ++ t) -- declares another constructor or syntax alternative
| space : SafeVal " " -- declares another constructor or syntax alternative
| newline : SafeVal "\n" -- declares another constructor or syntax alternative
| semicolon : SafeVal ";" -- declares another constructor or syntax alternative

/--
Appending two safe values with a newline in between is also a safe value.
-/
theorem blocks (s t : String) (h1 : SafeVal s) (h2 : SafeVal t) : SafeVal (s ++ "\n" ++ t) := by -- states and proves theorem `blocks`
    apply SafeVal.strAppend (s ++ "\n") -- reduces the goal using this theorem or constructor
    apply SafeVal.strAppend s -- reduces the goal using this theorem or constructor
    assumption -- solves the goal from an existing hypothesis
    apply SafeVal.newline -- reduces the goal using this theorem or constructor
    assumption -- solves the goal from an existing hypothesis

/--
Predicate for safe file paths.
Only paths starting with "public/" or "data/" are considered safe.
-/
inductive SafePath : FilePath → Prop where -- declares the inductive type or proposition `SafePath`
| pub (p : FilePath) : SafePath ("public" / p) -- declares another constructor or syntax alternative
| data (p : FilePath) : SafePath ("data" / p) -- declares another constructor or syntax alternative

/--
A path in the "public" directory is safe.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem pubSafe (p : FilePath) : SafePath ("public" / p) := by -- states and proves theorem `pubSafe`
    apply SafePath.pub -- reduces the goal using this theorem or constructor

/--
A path in the "data" directory is safe.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem dataSafe (p : FilePath) : SafePath ("data" / p) := by -- states and proves theorem `dataSafe`
    apply SafePath.data -- reduces the goal using this theorem or constructor

/--
Predicate for safe `FileM` programs.
A program is safe if it only reads/writes to safe paths and only writes safe values.
-/
inductive SafeProg  : {α : Type} →  FileM α → Prop where -- declares the inductive type or proposition `SafeProg`
| pureSafe (a : α) (h : SafeVal a) : SafeProg (FileM.pure a) -- declares another constructor or syntax alternative
| readSafe (p : FilePath) (h : SafePath p) : SafeProg  (FileM.read p) -- declares another constructor or syntax alternative
| writeSafe (p : FilePath) (h : SafePath p) (s : String) (h2 : SafeVal s) : SafeProg (FileM.write p s) -- declares another constructor or syntax alternative
| flatMapSafe -- declares another constructor or syntax alternative
    (x : FileM α)
    (h : SafeProg x)
    (f : α → FileM β)
    (h2 : ∀a, SafeVal a → SafeProg  (f a)) : SafeProg  (.flatMap f x)

/--
A program that just returns a safe value is safe.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem pureSafe (a : α) (h : SafeVal a) : SafeProg (FileM.pure a) := by -- states and proves theorem `pureSafe`
    apply SafeProg.pureSafe -- reduces the goal using this theorem or constructor
    assumption -- solves the goal from an existing hypothesis

/--
Reading from a safe path is a safe operation.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem readSafe (p : FilePath) (h : SafePath p) : SafeProg  (FileM.read p) := by -- states and proves theorem `readSafe`
    apply SafeProg.readSafe -- reduces the goal using this theorem or constructor
    assumption -- solves the goal from an existing hypothesis

/--
Writing a safe value to a safe path is a safe operation.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem writeSafe (p : FilePath) (h : SafePath p) (s : String) (h2 : SafeVal s) : SafeProg (FileM.write p s) := by -- states and proves theorem `writeSafe`
    apply SafeProg.writeSafe <;> assumption -- reduces the goal using this theorem or constructor

/--
The composition of two safe programs is safe.
-/
@[grind .] -- annotation controlling elaboration, simplification, or automation
theorem flatMapSafe -- states and proves theorem `flatMapSafe`
    (x : FileM α)
    (h : SafeProg x)
    (f : α → FileM β)
    (h2 : ∀a, SafeVal a → SafeProg  (f a)) : SafeProg  (.flatMap f x) := by
    apply SafeProg.flatMapSafe <;> assumption -- reduces the goal using this theorem or constructor

/--
Copies content from a public path to a data path.
-/
def pubToData (p : FilePath) : FileM Unit := do -- defines `pubToData`
    let contents ← FileM.read ("public" / p) -- binds an intermediate value for the following expression
    FileM.write ("data" / p) contents

/--
Proof that `pubToData` is a safe program.
-/
theorem safe_pubToData (p : FilePath) : SafeProg (pubToData p) := by -- states and proves theorem `safe_pubToData`
    apply SafeProg.flatMapSafe <;> grind -- reduces the goal using this theorem or constructor

/--
Merges two public files and writes the result to a data file.
-/
def mergePubs (p1 p2 out : FilePath) : FileM Unit := do -- defines `mergePubs`
    let c1 ← FileM.read ("public" / p1) -- binds an intermediate value for the following expression
    let c2 ← FileM.read ("public" / p2) -- binds an intermediate value for the following expression
    let merged := c1 ++ "\n" ++ c2 -- binds an intermediate value for the following expression
    FileM.write ("data" / out) merged

/--
Proof that `mergePubs` is a safe program.
-/
theorem safe_mergePubs (p1 p2 out : FilePath) : SafeProg (mergePubs p1 p2 out) := by -- states and proves theorem `safe_mergePubs`
    apply SafeProg.flatMapSafe -- reduces the goal using this theorem or constructor
    . apply SafeProg.readSafe
      grind -- asks the `grind` automation to finish the proof
    . intro c1 hC1
      apply SafeProg.flatMapSafe -- reduces the goal using this theorem or constructor
      . grind
      . intro c2 hC2
        let merged := c1 ++ "\n" ++ c2 -- binds an intermediate value for the following expression
        have hMerged : SafeVal merged := blocks c1 c2 hC1 hC2 -- records an intermediate fact for the proof
        grind -- asks the `grind` automation to finish the proof

end file_access -- closes the current namespace or section

end langur -- closes the current namespace or section
