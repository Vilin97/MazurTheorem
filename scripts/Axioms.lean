/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Lean

/-!
# Kernel axiom audit for the integrated libraries

This executable imports the compiled `MazurTorsion` and `EllipticCurves`
libraries, enumerates every declaration defined in those module trees, and
checks its transitive axiom dependencies. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed.

Unlike a source-text check, this catches an indirect dependency on `sorryAx`,
`Lean.ofReduceBool`, or a custom axiom. Run it with `lake exe axioms` after
building the library.
-/

open Lean

/-- The compiled library roots whose declarations are audited. -/
def auditedRoots : Array Name := #[`MazurTorsion, `EllipticCurves]

/-- Axioms permitted in completed Mazur formalizations. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Import modules and run a core action against the resulting environment. -/
def withImportedEnvironment {α} (modules : Array Name) (action : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  unsafe Lean.enableInitializersExecution
  let environment ← Lean.importModules
    (modules.map fun moduleName => { module := moduleName })
    {}
    (trustLevel := 1024)
    (leakEnv := true)
    (loadExts := true)
    (level := .private)
  Prod.fst <$> Core.CoreM.toIO action
    (ctx := { fileName := "<axioms>", fileMap := default })
    (s := { env := environment })

/-- Whether a module is one of the audited roots or one of their descendants. -/
def isAuditedModule (moduleName : Name) : Bool :=
  auditedRoots.any fun root => moduleName == root || root.isPrefixOf moduleName

/-- Turn a Lean source path into its module name. -/
def pathToModule (path : System.FilePath) : Name :=
  (path.withExtension "").components.foldl
    (fun moduleName component => Name.mkStr moduleName component)
    Name.anonymous

/-- Recursively enumerate every Lean module below a source directory. -/
partial def collectLeanModules (directory : System.FilePath) : IO (Array Name) := do
  let mut modules := #[]
  for entry in (← directory.readDir) do
    if (← entry.path.isDir) then
      modules := modules ++ (← collectLeanModules entry.path)
    else if entry.path.extension == some "lean" then
      modules := modules.push (pathToModule entry.path)
  return modules

/-- Import both integrated library roots and every source module below them. -/
def auditedModules : IO (Array Name) := do
  return #[`MazurTorsion, `EllipticCurves] ++
    (← collectLeanModules ("MazurTorsion" : System.FilePath)) ++
    (← collectLeanModules ("EllipticCurves" : System.FilePath))

/-- Audit declarations whose defining modules lie under either audited root. -/
def audit : CoreM (Nat × Array String) := do
  let environment ← getEnv
  let importedModules := environment.allImportedModuleNames
  let candidates : Array Name :=
    environment.constants.fold (init := #[]) fun declarations declarationName _ =>
      match environment.getModuleIdxFor? declarationName with
      | some moduleIndex =>
          match importedModules[moduleIndex.toNat]? with
          | some moduleName =>
              if isAuditedModule moduleName then
                declarations.push declarationName
              else
                declarations
          | none => declarations
      | none => declarations
  let mut messages : Array String := #[]
  for declarationName in candidates do
    let axioms ← collectAxioms declarationName
    let disallowed := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
    if !disallowed.isEmpty then
      messages := messages.push s!"  {declarationName} -> {disallowed.toList}"
  return (candidates.size, messages)

/-- Run the audit and return a process exit code. -/
def main : IO UInt32 := do
  let modules ← auditedModules
  let (audited, messages) ← withImportedEnvironment modules audit
  if audited == 0 then
    IO.eprintln "axioms: audited zero integrated declarations; the audit is miswired"
    return 1
  if messages.isEmpty then
    IO.println s!"axioms: audited {audited} declaration(s) in MazurTorsion and \
      EllipticCurves; all dependencies are within {allowedAxioms}"
    return 0
  IO.eprintln s!"axioms: {messages.size} declaration(s) in MazurTorsion or \
    EllipticCurves use disallowed axioms:"
  for message in messages do
    IO.eprintln message
  IO.eprintln s!"allowed: {allowedAxioms}"
  return 1
