/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowAssembly
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistPushforwardCompatibility
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreAffineRestrictionCompatibility

/-!
# Affine comparisons for relative projective Serre twists

The canonical restriction and pushforward comparisons jointly supply
the relative Serre input used by the canonical support-Chow assembly.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace
open ProjectiveSpace.IsRelativeProjectiveFactorization

/--
Relative projective Serre twists satisfy both affine comparison
properties required by the canonical support-Chow construction.
-/
theorem hasRelativeSerreAffineComparisons :
    HasRelativeSerreAffineComparisons := by
  intro Y S s g h M hfinite hquasicoherent
  exact
    ⟨h.affineRestrictionTwistCompatible M,
      h.affineTwistPushforwardCompatible⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
