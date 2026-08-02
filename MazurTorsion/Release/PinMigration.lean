/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.List.Basic

/-!
# Exact-pin integration descriptor

This module gives the pin-migration release node a checked, reviewable descriptor.  The strings
are embedded from the two workspaces at elaboration time, so the declaration cannot silently
record a different lockfile from the one that was compiled.

The declarations here describe an operational build contract; they are not a kernel proof that an
external process ran.  `scripts/quality.py` parses both manifests and requires equality of the full
resolved package-revision graphs, while the Tau Ceti workflow executes every command named below.
`MazurTorsion.Release.PinMigrationAudit` is the compiled downstream consumer.
-/

namespace MazurTheorem.Release

/-- The root and Tau Ceti toolchains and manifests, embedded verbatim in that order. -/
def sharedDependencyGraph : List String :=
  [ include_str ".." / ".." / "lean-toolchain",
    include_str ".." / ".." / "lake-manifest.json",
    include_str ".." / ".." / "upstream" / "tauceti" / "lean-toolchain",
    include_str ".." / ".." / "upstream" / "tauceti" / "lake-manifest.json" ]

/-- The exact dependency descriptor and commands required of the Tau Ceti downstream consumer. -/
def tauCetiConsumerBuild : List String × List String :=
  (sharedDependencyGraph,
    [ "lake build MazurTauCetiChallenge",
      "lake exe contractAxioms",
      "lake exe runLinter MazurTauCetiChallenge",
      "lake exe lint-style MazurTauCetiChallenge",
      "python3 scripts/quality.py" ])

end MazurTheorem.Release
