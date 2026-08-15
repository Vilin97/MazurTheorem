/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentTransitionLeft
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentTransitionRight

/-!
# Transition formula for descent along an isomorphism of open covers

The chart-normalized global pullback construction has the explicit
pair-overlap transition obtained by pulling the original transition
along the induced overlap map.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

/-- Canonical global restriction and explicit transition pullback agree
for the canonical descent datum of a global module. -/
theorem coverIsoCanonicalTransition
    (e : 𝒰 ≅ 𝒱)
    (W : 𝒱.gluedCover.glued.Modules)
    (i j : 𝒰.I₀) :
    transportTransition
        ((restrictionFunctor (D := 𝒰.gluedCover)).obj
          ((pullback (coverIsoGluedIso e).hom).obj W))
        (fun i =>
          (pullback (e.hom.h₀ i)).obj
            (((restrictionFunctor
              (D := 𝒱.gluedCover)).obj W).chart
                (e.hom.s₀ i)))
        (coverIsoCanonicalChartIso e W)
        i j =
      coverIsoPullbackTransition e
        ((restrictionFunctor
          (D := 𝒱.gluedCover)).obj W)
        i j := by
  apply Iso.ext
  rw [coverIsoCanonicalTransport_hom_eq_normal,
    coverIsoCanonicalPullback_hom_eq_normal]

/-- The transition of `pullbackAlongCoverIso` is the explicit pullback
of the original target-cover transition. -/
theorem pullbackAlongCoverIso_transition
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover)
    (i j : 𝒰.I₀) :
    (pullbackAlongCoverIso e A).transition i j =
      coverIsoPullbackTransition e A i j := by
  let W :=
    (glueFunctor (D := 𝒱.gluedCover)).obj A
  let A₀ :=
    (restrictionFunctor (D := 𝒱.gluedCover)).obj W
  let R :=
    (restrictionFunctor (D := 𝒰.gluedCover)).obj
      ((pullback (coverIsoGluedIso e).hom).obj W)
  let c : ∀ i, R.chart i ≅
      (pullback (e.hom.h₀ i)).obj
        (A₀.chart (e.hom.s₀ i)) :=
    coverIsoCanonicalChartIso e W
  let d₀ : A₀ ≅ A :=
    descentGlueRestrictionIso
      (D := 𝒱.gluedCover) A
  let d : ∀ i,
      (pullback (e.hom.h₀ i)).obj
          (A₀.chart (e.hom.s₀ i)) ≅
        (pullback (e.hom.h₀ i)).obj
          (A.chart (e.hom.s₀ i)) :=
    fun i =>
      (pullback (e.hom.h₀ i)).mapIso
        (isoApp d₀ (e.hom.s₀ i))
  have hchart :
      coverIsoRestrictionChartIso e A =
        (fun i => c i ≪≫ d i) := by
    funext i
    rfl
  change transportTransition R
      (fun i =>
        (pullback (e.hom.h₀ i)).obj
          (A.chart (e.hom.s₀ i)))
      (coverIsoRestrictionChartIso e A) i j =
    coverIsoPullbackTransition e A i j
  exact calc
    transportTransition R
          (fun i =>
            (pullback (e.hom.h₀ i)).obj
              (A.chart (e.hom.s₀ i)))
          (coverIsoRestrictionChartIso e A) i j =
        transportTransition R
          (fun i =>
            (pullback (e.hom.h₀ i)).obj
              (A.chart (e.hom.s₀ i)))
          (fun i => c i ≪≫ d i) i j :=
      congrArg (fun q => transportTransition R
        (fun i =>
          (pullback (e.hom.h₀ i)).obj
            (A.chart (e.hom.s₀ i))) q i j) hchart
    _ = transportTransition
          (transport R
            (fun i =>
              (pullback (e.hom.h₀ i)).obj
                (A₀.chart (e.hom.s₀ i))) c)
          (fun i =>
            (pullback (e.hom.h₀ i)).obj
              (A.chart (e.hom.s₀ i))) d i j :=
      transportTransition_comp R
        (fun i =>
          (pullback (e.hom.h₀ i)).obj
            (A₀.chart (e.hom.s₀ i)))
        (fun i =>
          (pullback (e.hom.h₀ i)).obj
            (A.chart (e.hom.s₀ i))) c d i j
    _ = (pullback (𝒰.gluedCover.f i j)).mapIso
            (d i).symm ≪≫
          transportTransition R
            (fun i =>
              (pullback (e.hom.h₀ i)).obj
                (A₀.chart (e.hom.s₀ i))) c i j ≪≫
          (pullback
            (𝒰.gluedCover.t i j ≫
              𝒰.gluedCover.f j i)).mapIso (d j) := rfl
    _ = (pullback (𝒰.gluedCover.f i j)).mapIso
            (d i).symm ≪≫
          coverIsoPullbackTransition e A₀ i j ≪≫
          (pullback
            (𝒰.gluedCover.t i j ≫
              𝒰.gluedCover.f j i)).mapIso (d j) := by
      rw [coverIsoCanonicalTransition e W i j]
    _ = coverIsoPullbackTransition e A i j :=
      conjugatedTransition_eq_of_compatible
        (D := 𝒰.gluedCover)
        (fun i =>
          (pullback (e.hom.h₀ i)).obj
            (A₀.chart (e.hom.s₀ i)))
        (fun i =>
          (pullback (e.hom.h₀ i)).obj
            (A.chart (e.hom.s₀ i)))
        (coverIsoPullbackTransition e A₀)
        (coverIsoPullbackTransition e A)
        d
        (coverIsoPullbackTransition_naturality
          e d₀.hom)
        i j

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
