/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentTransitionData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModulePullbackPastingCoherence

/-!
# Explicit pulled transition normalization for a cover isomorphism

The explicitly pulled transition of the canonical target-cover
restriction reduces to the same common normal form as the globally
constructed transition.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Hom-side normalization of the explicitly pulled canonical
transition. -/
theorem coverIsoCanonicalPullback_hom_eq_normal
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    (coverIsoPullbackTransition e
        ((restrictionFunctor
          (D := 𝒱.gluedCover)).obj W)
        i j).hom =
      (coverIsoCanonicalNormalIso e W i j).hom := by
  have htyped :
      (coverIsoCanonicalPullbackIso e W i j).hom =
        (coverIsoCanonicalNormalIso e W i j).hom := by
    simpa only [coverIsoCanonicalPullbackIso,
      openCoverRestrictionTransition,
      coverIsoCanonicalNormalIso] using
      pullbackSquareIso_paste_transition_hom
        (q := overlapFst 𝒰 i j)
        (a := e.hom.h₀ i)
        (q' := overlapTarget 𝒰 i j)
        (a' := e.hom.h₀ j)
        (p := coverIsoOverlapMap e i j)
        (r := overlapFst 𝒱 (e.hom.s₀ i) (e.hom.s₀ j))
        (r' := overlapTarget 𝒱 (e.hom.s₀ i) (e.hom.s₀ j))
        (u := gluedCoverChartMap 𝒱 (e.hom.s₀ i))
        (u' := gluedCoverChartMap 𝒱 (e.hom.s₀ j))
        (coverIsoOverlapMap_overlapFst e i j).symm
        (coverIsoOverlapMap_gluedCover_target e i j).symm
        (openCoverRestrictionComposite_eq 𝒱
          (e.hom.s₀ i) (e.hom.s₀ j))
        (coverIsoCanonicalComposite_eq e i j)
        W
  exact Eq.trans
    (congrArg Iso.hom
      (coverIsoPullbackTransition_restriction_eq_typed
        e W i j))
    htyped

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
