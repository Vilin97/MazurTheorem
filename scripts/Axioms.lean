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
  unsafe Lean.withImportModules
    (modules.map fun moduleName => { module := moduleName })
    {}
    (trustLevel := 1024)
    fun environment =>
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

/-- A shared memo table for axiom reachability across the whole library. -/
abbrev AxiomCacheM := ReaderT Environment (StateM (Lean.NameMap Bool))

/-- Decide whether a constant transitively reaches a disallowed axiom.

This mirrors `Lean.collectAxioms`, but shares its memo table across declarations.
Exact offending axiom names are collected later only for failures. -/
partial def reachesDisallowedAxiom (constantName : Name) : AxiomCacheM Bool := do
  if let some result := (← get).find? constantName then
    return result
  modify (·.insert constantName false)
  let environment ← read
  let anyExpression (expressions : Array Expr) : AxiomCacheM Bool :=
    expressions.anyM fun expression =>
      expression.getUsedConstants.anyM reachesDisallowedAxiom
  let result ←
    match environment.checked.get.find? constantName with
    | some (.axiomInfo value) =>
        if !allowedAxioms.contains constantName then
          pure true
        else
          anyExpression #[value.type]
    | some (.defnInfo value) => anyExpression #[value.type, value.value]
    | some (.thmInfo value) => anyExpression #[value.type, value.value]
    | some (.opaqueInfo value) => anyExpression #[value.type, value.value]
    | some (.quotInfo _) => pure false
    | some (.ctorInfo value) => anyExpression #[value.type]
    | some (.recInfo value) => anyExpression #[value.type]
    | some (.inductInfo value) =>
        if (← anyExpression #[value.type]) then
          pure true
        else
          value.ctors.anyM reachesDisallowedAxiom
    | none => pure false
  modify (·.insert constantName result)
  return result

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
  let offenders : Array Name :=
    (candidates.filterM reachesDisallowedAxiom |>.run environment).run' {}
  let mut messages : Array String := #[]
  for declarationName in offenders do
    let axioms ← collectAxioms declarationName
    let disallowed := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
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
