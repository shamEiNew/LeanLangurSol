import Lean
open IO FS System

/-!
# File Monad and Security

This module defines a custom monad `FileM` for file operations and a security framework
to verify that file programs only access safe paths and write safe values.
-/

namespace file_access

/--
Basic file commands.
-/
inductive FileCmd : Type → Type where
| read  : FilePath → FileCmd String
| write : FilePath → String → FileCmd Unit

/--
A free monad for file operations.
-/
inductive FileM : Type → Type _ where
| pure {α : Type} : α → FileM α
| cons : FileCmd β → (k: β → FileM α) → FileM α

/--
FlatMap operation for the `FileM` monad.
-/
def FileM.flatMap {α β : Type} (f : α → FileM β) : FileM α → FileM β
  | .pure a => f a
  | .cons cmd k => .cons cmd (fun b => (k b).flatMap f)

instance : Monad FileM where
  pure := FileM.pure
  bind x f := FileM.flatMap f x

/--
Reads the contents of a file.
-/
def FileM.read (path : FilePath) : FileM String :=
    .cons (FileCmd.read path) FileM.pure

/--
Writes contents to a file.
-/
def FileM.write (path : FilePath) (contents : String) : FileM Unit :=
    .cons (FileCmd.write path contents) FileM.pure

/--
Runs a `FileM` program in the `IO` monad.
-/
def FileM.run : FileM α → IO α
    | FileM.pure a => return a
    | FileM.cons cmd k =>
        match cmd with
        | FileCmd.read path => do
            let contents ← IO.FS.readFile path
            FileM.run (k contents)
        | FileCmd.write path contents => do
            IO.FS.writeFile path contents
            FileM.run (k ())

/--
Map operation for the `FileM` monad.
-/
abbrev FileM.map {α β : Type} (f : α → β) : FileM α → FileM β := fun x => do
    let a ← x
    return f a

/--
Predicate for safe values that can be written to files.
-/
inductive SafeVal : {α : Type} → α → Prop where
| nat(n) : SafeVal (n : Nat)
| strAppend (s t : String) : SafeVal s → SafeVal t → SafeVal (s ++ t)
| space : SafeVal " "
| newline : SafeVal "\n"
| semicolon : SafeVal ";"

/--
Appending two safe values with a newline in between is also a safe value.
-/
theorem blocks (s t : String) (h1 : SafeVal s) (h2 : SafeVal t) : SafeVal (s ++ "\n" ++ t) := by
    apply SafeVal.strAppend (s ++ "\n")
    apply SafeVal.strAppend s
    assumption
    apply SafeVal.newline
    assumption

/--
Predicate for safe file paths.
Only paths starting with "public/" or "data/" are considered safe.
-/
inductive SafePath : FilePath → Prop where
| pub (p : FilePath) : SafePath ("public" / p)
| data (p : FilePath) : SafePath ("data" / p)

/--
A path in the "public" directory is safe.
-/
@[grind .]
theorem pubSafe (p : FilePath) : SafePath ("public" / p) := by
    apply SafePath.pub

/--
A path in the "data" directory is safe.
-/
@[grind .]
theorem dataSafe (p : FilePath) : SafePath ("data" / p) := by
    apply SafePath.data

/--
Predicate for safe `FileM` programs.
A program is safe if it only reads/writes to safe paths and only writes safe values.
-/
inductive SafeProg  : {α : Type} →  FileM α → Prop where
| pureSafe (a : α) (h : SafeVal a) : SafeProg (FileM.pure a)
| readSafe (p : FilePath) (h : SafePath p) : SafeProg  (FileM.read p)
| writeSafe (p : FilePath) (h : SafePath p) (s : String) (h2 : SafeVal s) : SafeProg (FileM.write p s)
| flatMapSafe
    (x : FileM α)
    (h : SafeProg x)
    (f : α → FileM β)
    (h2 : ∀a, SafeVal a → SafeProg  (f a)) : SafeProg  (.flatMap f x)

/--
A program that just returns a safe value is safe.
-/
@[grind .]
theorem pureSafe (a : α) (h : SafeVal a) : SafeProg (FileM.pure a) := by
    apply SafeProg.pureSafe
    assumption

/--
Reading from a safe path is a safe operation.
-/
@[grind .]
theorem readSafe (p : FilePath) (h : SafePath p) : SafeProg  (FileM.read p) := by
    apply SafeProg.readSafe
    assumption

/--
Writing a safe value to a safe path is a safe operation.
-/
@[grind .]
theorem writeSafe (p : FilePath) (h : SafePath p) (s : String) (h2 : SafeVal s) : SafeProg (FileM.write p s) := by
    apply SafeProg.writeSafe <;> assumption

/--
The composition of two safe programs is safe.
-/
@[grind .]
theorem flatMapSafe
    (x : FileM α)
    (h : SafeProg x)
    (f : α → FileM β)
    (h2 : ∀a, SafeVal a → SafeProg  (f a)) : SafeProg  (.flatMap f x) := by
    apply SafeProg.flatMapSafe <;> assumption

/--
Copies content from a public path to a data path.
-/
def pubToData (p : FilePath) : FileM Unit := do
    let contents ← FileM.read ("public" / p)
    FileM.write ("data" / p) contents

/--
Proof that `pubToData` is a safe program.
-/
theorem safe_pubToData (p : FilePath) : SafeProg (pubToData p) := by
    apply SafeProg.flatMapSafe <;> grind

/--
Merges two public files and writes the result to a data file.
-/
def mergePubs (p1 p2 out : FilePath) : FileM Unit := do
    let c1 ← FileM.read ("public" / p1)
    let c2 ← FileM.read ("public" / p2)
    let merged := c1 ++ "\n" ++ c2
    FileM.write ("data" / out) merged

/--
Proof that `mergePubs` is a safe program.
-/
theorem safe_mergePubs (p1 p2 out : FilePath) : SafeProg (mergePubs p1 p2 out) := by
    apply SafeProg.flatMapSafe
    . apply SafeProg.readSafe
      grind
    . intro c1 hC1
      apply SafeProg.flatMapSafe
      . grind
      . intro c2 hC2
        let merged := c1 ++ "\n" ++ c2
        have hMerged : SafeVal merged := blocks c1 c2 hC1 hC2
        grind

end file_access
