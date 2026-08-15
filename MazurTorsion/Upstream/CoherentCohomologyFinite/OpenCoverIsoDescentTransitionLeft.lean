/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentTransitionData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModulePullbackPastingCoherence

/-!
# Canonical transition normalization for a cover isomorphism

The transition obtained by globally pulling back a module and then
transporting its restricted chart objects reduces to the common
threefold-pullback comparison.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Hom-side normalization of the transported canonical transition. -/
theorem coverIsoCanonicalTransport_hom_eq_normal
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    (transportTransition
        ((restrictionFunctor (D := 𝒰.gluedCover)).obj
          ((pullback (coverIsoGluedIso e).hom).obj W))
        (fun i =>
          (pullback (e.hom.h₀ i)).obj
            (((restrictionFunctor
              (D := 𝒱.gluedCover)).obj W).chart
                (e.hom.s₀ i)))
        (coverIsoCanonicalChartIso e W)
        i j).hom =
      (coverIsoCanonicalNormalIso e W i j).hom := by
  have htyped :
      (coverIsoCanonicalTransportIso e W i j).hom =
        (coverIsoCanonicalNormalIso e W i j).hom := by
    simpa only [coverIsoCanonicalTransportIso,
      coverIsoCanonicalChartIsoTyped,
      openCoverRestrictionTransition,
      coverIsoCanonicalNormalIso] using
      pullbackSquareIso_transport_transition_hom
        (q := overlapFst 𝒰 i j)
        (d := gluedCoverChartMap 𝒰 i)
        (a := e.hom.h₀ i)
        (q' := overlapTarget 𝒰 i j)
        (d' := gluedCoverChartMap 𝒰 j)
        (a' := e.hom.h₀ j)
        (g := (coverIsoGluedIso e).hom)
        (u := gluedCoverChartMap 𝒱 (e.hom.s₀ i))
        (u' := gluedCoverChartMap 𝒱 (e.hom.s₀ j))
        (gluedCover_ι_coverIsoGluedIso_hom e i)
        (gluedCover_ι_coverIsoGluedIso_hom e j)
        (openCoverRestrictionComposite_eq 𝒰 i j)
        (coverIsoCanonicalComposite_eq e i j)
        W
  exact Eq.trans
    (congrArg Iso.hom
      (coverIsoCanonicalTransport_eq_typed e W i j))
    htyped

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
