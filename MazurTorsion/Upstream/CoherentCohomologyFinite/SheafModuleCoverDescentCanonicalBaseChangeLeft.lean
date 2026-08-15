/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCanonicalBaseChangeData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModulePullbackPastingCoherence

/-!
# Left normalization for canonical descent base change

The transported canonical transition on the pulled-back glued scheme
reduces to the common threefold pullback comparison.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

private abbrev D := 𝒰.gluedCover

private abbrev D' := gluedCover (𝒰.pullback₁ f)

/-- Hom-side normalization of the transported canonical transition. -/
theorem canonicalBaseChangeTransport_hom_eq_normal
    (W : (D 𝒰).glued.Modules) (i j : 𝒰.I₀) :
    (transportTransition
        ((restrictionFunctor (D := D' 𝒰 f)).obj
          ((pullback (baseChangeGluedMap 𝒰 f)).obj W))
        (fun i =>
          (pullback (𝒰.pullbackHom f i)).obj
            (((restrictionFunctor
              (D := D 𝒰)).obj W).chart i))
        (canonicalBaseChangeChartIso 𝒰 f W)
        i j).hom =
      (canonicalBaseChangeNormalIso
        𝒰 f W i j).hom := by
  have htyped :
      (canonicalBaseChangeTransportIso 𝒰 f W i j).hom =
        (canonicalBaseChangeNormalIso 𝒰 f W i j).hom := by
    simpa only [canonicalBaseChangeTransportIso,
      canonicalBaseChangeChartIsoTyped,
      openCoverRestrictionTransition,
      canonicalBaseChangeNormalIso] using
      pullbackSquareIso_transport_transition_hom
        (q := overlapFst (𝒰.pullback₁ f) i j)
        (d := gluedCoverChartMap (𝒰.pullback₁ f) i)
        (a := 𝒰.pullbackHom f i)
        (q' := overlapTarget (𝒰.pullback₁ f) i j)
        (d' := gluedCoverChartMap (𝒰.pullback₁ f) j)
        (a' := 𝒰.pullbackHom f j)
        (g := baseChangeGluedMap 𝒰 f)
        (u := gluedCoverChartMap 𝒰 i)
        (u' := gluedCoverChartMap 𝒰 j)
        (gluedCoverChartMap_baseChangeGluedMap 𝒰 f i)
        (gluedCoverChartMap_baseChangeGluedMap 𝒰 f j)
        (openCoverRestrictionComposite_eq
          (𝒰.pullback₁ f) i j)
        (canonicalBaseChangeComposite_eq 𝒰 f i j)
        W
  exact Eq.trans
    (congrArg Iso.hom
      (canonicalBaseChangeTransport_eq_typed
        𝒰 f W i j))
    htyped

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
