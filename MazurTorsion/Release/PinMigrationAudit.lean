/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Release.PinMigration

/-!
# Compiled consumer of the exact-pin integration descriptor

These small checks prevent the release descriptor from losing either its shared graph or its
downstream build target.  Execution and manifest-semantic checks remain the responsibility of the
repository quality and CI gates documented in `MazurTorsion.Release.PinMigration`.
-/

namespace MazurTheorem.Release

/-- The downstream build contract consumes the exact shared dependency descriptor. -/
theorem tauCetiConsumerBuild_uses_sharedDependencyGraph :
    tauCetiConsumerBuild.1 = sharedDependencyGraph :=
  rfl

/-- The downstream build contract includes a focused build of the Tau Ceti aggregator. -/
theorem tauCetiConsumerBuild_checks_aggregator :
    "lake build MazurTauCetiChallenge" ∈ tauCetiConsumerBuild.2 := by
  decide

end MazurTheorem.Release
