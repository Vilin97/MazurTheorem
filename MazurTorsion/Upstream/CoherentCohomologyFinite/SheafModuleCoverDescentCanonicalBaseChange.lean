/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCanonicalBaseChangeLeft
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCanonicalBaseChangeRight

/-!
# Canonical module descent transitions under base change

The canonical descent datum of a pulled-back global module has the same
overlap transition as the explicit chartwise base-change construction,
after the canonical pullback-composition comparisons on the charts.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

private abbrev D := 𝒰.gluedCover

private abbrev D' := gluedCover (𝒰.pullback₁ f)

/-- Transporting the canonical overlap transition along the chart
comparisons gives the explicit base-changed canonical transition. -/
theorem canonicalBaseChangeTransition
    (W : (D 𝒰).glued.Modules) (i j : 𝒰.I₀) :
    transportTransition
        ((restrictionFunctor (D := D' 𝒰 f)).obj
          ((pullback (baseChangeGluedMap 𝒰 f)).obj W))
        (fun i =>
          (pullback (𝒰.pullbackHom f i)).obj
            (((restrictionFunctor
              (D := D 𝒰)).obj W).chart i))
        (canonicalBaseChangeChartIso 𝒰 f W)
        i j =
      baseChangeTransition 𝒰 f
        ((restrictionFunctor (D := D 𝒰)).obj W)
        i j := by
  apply Iso.ext
  exact
    (canonicalBaseChangeTransport_hom_eq_normal
      𝒰 f W i j).trans
      (baseChangeCanonicalTransition_hom_eq_normal
        𝒰 f W i j).symm

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
