/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Lean

/-!
# Kernel audit for challenge contracts

The executable resolves every registered declaration by its exact kernel name.
An open contract may use exactly the challenge placeholder `sorryAx`, but its
type must already be axiom-clean. A closed contract must be axiom-clean and
transitively reach its permanent destination. Registered acceptance consumers
can be audited with the same dependency check.
-/

open Lean

/-- One lifecycle or acceptance target supplied on the command line. -/
structure AuditTarget where
  label : String
  declarationName : Name
  mayUseSorry : Bool
  requiredDependency : Option Name

/-- Axioms permitted in completed formalizations. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Parse a dotted declaration name without invoking the Lean parser. -/
def dottedName (value : String) : Name :=
  value.splitOn "." |>.foldl Name.mkStr Name.anonymous

/-- Parse one lifecycle-qualified command-line target. -/
def parseTarget (argument : String) : Except String AuditTarget :=
  match argument.splitOn ":" with
  | ["open", declaration] =>
      .ok ⟨"open contract", dottedName declaration, true, none⟩
  | ["closed", declaration, destination] =>
      .ok
        ⟨"closed contract", dottedName declaration, false,
          some (dottedName destination)⟩
  | ["uses", consumer, destination] =>
      .ok
        ⟨"acceptance consumer", dottedName consumer, false,
          some (dottedName destination)⟩
  | _ =>
      .error s!"invalid audit target {argument}; expected open:<name>, \
        closed:<name>:<destination>, or uses:<consumer>:<destination>"

/-- Import the challenge environment and, when needed, all consumer roots. -/
def withContractEnvironment {α}
    (includeConsumerRoots : Bool) (action : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  let modules :=
    if includeConsumerRoots then
      #[{ module := `Challenge }, { module := `MazurTorsion },
        { module := `EllipticCurves }]
    else
      #[{ module := `Challenge }]
  unsafe Lean.withImportModules
    modules
    {}
    (trustLevel := 1024)
    fun environment =>
      Prod.fst <$> Core.CoreM.toIO action
        (ctx := { fileName := "<contract-axioms>", fileMap := default })
        (s := { env := environment })

/-- Collect the transitive axioms reached from the constants in an expression. -/
def expressionAxioms (expression : Expr) : CoreM (List Name) := do
  let mut result := []
  for constantName in expression.getUsedConstants do
    for axiomName in (← collectAxioms constantName) do
      if !result.contains axiomName then
        result := axiomName :: result
  return result

/-- Constants used directly in one declaration's type or value. -/
def declarationDependencies (environment : Environment) (source : Name) : Array Name :=
  let expressions : Array Expr :=
    match environment.constants.find? source with
    | some (.axiomInfo value) => #[value.type]
    | some (.defnInfo value) => #[value.type, value.value]
    | some (.thmInfo value) => #[value.type, value.value]
    | some (.opaqueInfo value) => #[value.type, value.value]
    | some (.quotInfo _) => #[]
    | some (.ctorInfo value) => #[value.type]
    | some (.recInfo value) => #[value.type]
    | some (.inductInfo value) => #[value.type]
    | none => #[]
  expressions.foldl
    (fun dependencies expression =>
      dependencies ++ expression.getUsedConstants)
    #[]

/-- Whether `source` transitively uses `target` in its type or value. -/
def reachesDeclaration
    (environment : Environment) (target source : Name) : Bool := Id.run do
  let mut pending := [source]
  let mut visited : NameMap Bool := {}
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail
    if current == target then
      return true
    if !visited.contains current then
      visited := visited.insert current true
      for dependency in declarationDependencies environment current do
        pending := dependency :: pending
  return false

/-- Check every target against its lifecycle and permanent dependency. -/
def audit (targets : Array AuditTarget) : CoreM (Array String) := do
  let environment ← getEnv
  let mut failures := #[]
  for target in targets do
    let some declarationInfo := environment.constants.find? target.declarationName
      | failures := failures.push s!"missing declaration {target.declarationName}"
        continue
    let typeAxioms ← expressionAxioms declarationInfo.type
    let disallowedType :=
      typeAxioms.filter fun name => !allowedAxioms.contains name
    let axioms ← collectAxioms target.declarationName
    let disallowed := axioms.filter fun name => !allowedAxioms.contains name
    let axiomValid :=
      disallowedType.isEmpty &&
        if target.mayUseSorry then
          disallowed.size == 1 && disallowed.contains ``sorryAx
        else
          disallowed.isEmpty
    if !axiomValid then
      failures := failures.push
        s!"{target.label} {target.declarationName} has disallowed type axioms \
          {disallowedType} and full axioms {disallowed}"
    if let some dependency := target.requiredDependency then
      if !environment.constants.contains dependency then
        failures := failures.push s!"missing destination {dependency}"
      else
        let reaches :=
          reachesDeclaration environment dependency target.declarationName
        if !reaches then
          failures := failures.push
            s!"{target.label} {target.declarationName} does not reach {dependency}"
  return failures

/-- Run the lifecycle-aware contract audit. -/
def main (arguments : List String) : IO UInt32 := do
  if arguments.isEmpty then
    IO.eprintln "contractAxioms: no registered contracts were supplied"
    return 1
  let mut targets := #[]
  for argument in arguments do
    match parseTarget argument with
    | .ok target => targets := targets.push target
    | .error message =>
        IO.eprintln s!"contractAxioms: {message}"
        return 1
  let includeConsumerRoots :=
    targets.any fun target => target.label == "acceptance consumer"
  let failures ← withContractEnvironment includeConsumerRoots (audit targets)
  if failures.isEmpty then
    IO.println s!"contractAxioms: audited {targets.size} registered target(s)"
    return 0
  for failure in failures do
    IO.eprintln s!"contractAxioms: {failure}"
  return 1
