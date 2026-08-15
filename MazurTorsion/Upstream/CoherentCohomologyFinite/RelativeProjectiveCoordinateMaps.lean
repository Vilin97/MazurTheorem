/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowAssembly
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveCoordinateScalarTwistNaturalTransformation

/-!
# Unconditional relative projective coordinate maps

The base-changed projective coordinate natural transformation supplies
the coordinate-map interface used by the canonical Chow assembly.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace
open ProjectiveSpace.SerreTwist

/-- Every relative projective coordinate gives the required locally
invertible map into a nonnegative scalar twist. -/
theorem hasRelativeProjectiveCoordinateMaps :
    HasRelativeProjectiveCoordinateMaps := by
  intro T d g n r M
  let α :=
    (relativeProjectiveCoordinateScalarTwistNatTrans
      ℚ d g n r).app M
  refine ⟨α, ?_⟩
  let j :=
    (g ⁻¹ᵁ standardChart ℚ r).ι
  haveI hpullback :
      IsIso ((Scheme.Modules.pullback j).map α) :=
    isIso_relativeProjectiveCoordinateScalarTwistNatTrans_restrict_preimage_standardChart
      ℚ d g n r M
  exact
    (NatIso.isIso_map_iff
      (Scheme.Modules.restrictFunctorIsoPullback j) α).mpr
        hpullback

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
