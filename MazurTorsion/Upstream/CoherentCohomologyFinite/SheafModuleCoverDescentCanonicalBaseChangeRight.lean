/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCanonicalBaseChangeData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModulePullbackPastingCoherence

/-!
# Right normalization for canonical descent base change

The explicit base-changed canonical transition reduces to the same
threefold pullback comparison as the transported transition.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

private abbrev D := 𝒰.gluedCover

/-- Hom-side normalization of the explicit base-changed canonical
transition. -/
theorem baseChangeCanonicalTransition_hom_eq_normal
    (W : (D 𝒰).glued.Modules) (i j : 𝒰.I₀) :
    (baseChangeTransition 𝒰 f
        ((restrictionFunctor (D := D 𝒰)).obj W)
        i j).hom =
      (canonicalBaseChangeNormalIso
        𝒰 f W i j).hom := by
  have htyped :
      (canonicalBaseChangePullbackIso 𝒰 f W i j).hom =
        (canonicalBaseChangeNormalIso 𝒰 f W i j).hom := by
    simpa only [canonicalBaseChangePullbackIso,
      openCoverRestrictionTransition,
      canonicalBaseChangeNormalIso] using
      pullbackSquareIso_paste_transition_hom
        (q := overlapFst (𝒰.pullback₁ f) i j)
        (a := 𝒰.pullbackHom f i)
        (q' := overlapTarget (𝒰.pullback₁ f) i j)
        (a' := 𝒰.pullbackHom f j)
        (p := baseChangeOverlapMap 𝒰 f i j)
        (r := overlapFst 𝒰 i j)
        (r' := overlapTarget 𝒰 i j)
        (u := gluedCoverChartMap 𝒰 i)
        (u' := gluedCoverChartMap 𝒰 j)
        (baseChangeOverlapMap_overlapFst 𝒰 f i j).symm
        (baseChangeOverlapMap_overlapTarget 𝒰 f i j).symm
        (openCoverRestrictionComposite_eq 𝒰 i j)
        (canonicalBaseChangeComposite_eq 𝒰 f i j)
        W
  exact Eq.trans
    (congrArg Iso.hom
      (baseChangeTransition_restriction_eq_typed
        𝒰 f W i j))
    htyped

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
