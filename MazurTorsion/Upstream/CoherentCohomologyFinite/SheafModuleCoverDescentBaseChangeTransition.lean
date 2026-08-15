/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCanonicalBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentScalarBaseChange

/-!
# Explicit transition of the cover-descent base-change functor

The globally constructed base-change functor was conjugated so that its
chart objects are literal pullbacks.  Its transition is consequently
the explicit overlap transition introduced in the pair-overlap layer.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

private abbrev D := 𝒰.gluedCover

private abbrev D' := gluedCover (𝒰.pullback₁ f)

/-- The transition of `baseChangeObject` is the explicit pullback of
the original transition. -/
theorem baseChangeObject_transition
    (A : CoverDescentData (D 𝒰)) (i j : 𝒰.I₀) :
    (baseChangeObject 𝒰 f A).transition i j =
      baseChangeTransition 𝒰 f A i j := by
  let W := (glueFunctor (D := D 𝒰)).obj A
  let A₀ := (restrictionFunctor (D := D 𝒰)).obj W
  let R :=
    (restrictionFunctor (D := D' 𝒰 f)).obj
      ((pullback (baseChangeGluedMap 𝒰 f)).obj W)
  let c : ∀ i, R.chart i ≅
      (pullback (𝒰.pullbackHom f i)).obj (A₀.chart i) :=
    canonicalBaseChangeChartIso 𝒰 f W
  let d₀ : A₀ ≅ A :=
    descentGlueRestrictionIso (D := D 𝒰) A
  let d : ∀ i,
      (pullback (𝒰.pullbackHom f i)).obj (A₀.chart i) ≅
        (pullback (𝒰.pullbackHom f i)).obj (A.chart i) :=
    fun i =>
      (pullback (𝒰.pullbackHom f i)).mapIso
        (isoApp d₀ i)
  have hchart :
      globalBaseChangeChartIso 𝒰 f A =
        (fun i => c i ≪≫ d i) := by
    funext i
    rfl
  change transportTransition R
      (fun i =>
        (pullback (𝒰.pullbackHom f i)).obj (A.chart i))
      (globalBaseChangeChartIso 𝒰 f A) i j =
    baseChangeTransition 𝒰 f A i j
  exact calc
    transportTransition R
          (fun i =>
            (pullback (𝒰.pullbackHom f i)).obj (A.chart i))
          (globalBaseChangeChartIso 𝒰 f A) i j =
        transportTransition R
          (fun i =>
            (pullback (𝒰.pullbackHom f i)).obj (A.chart i))
          (fun i => c i ≪≫ d i) i j :=
      congrArg (fun q => transportTransition R
        (fun i =>
          (pullback (𝒰.pullbackHom f i)).obj (A.chart i)) q i j) hchart
    _ = transportTransition
          (transport R
            (fun i =>
              (pullback (𝒰.pullbackHom f i)).obj (A₀.chart i)) c)
          (fun i =>
            (pullback (𝒰.pullbackHom f i)).obj (A.chart i)) d i j :=
      transportTransition_comp R
        (fun i =>
          (pullback (𝒰.pullbackHom f i)).obj (A₀.chart i))
        (fun i =>
          (pullback (𝒰.pullbackHom f i)).obj (A.chart i)) c d i j
    _ = (pullback ((D' 𝒰 f).f i j)).mapIso (d i).symm ≪≫
          transportTransition R
            (fun i =>
              (pullback (𝒰.pullbackHom f i)).obj (A₀.chart i)) c i j ≪≫
          (pullback
            ((D' 𝒰 f).t i j ≫
              (D' 𝒰 f).f j i)).mapIso (d j) := rfl
    _ = (pullback ((D' 𝒰 f).f i j)).mapIso (d i).symm ≪≫
          baseChangeTransition 𝒰 f A₀ i j ≪≫
          (pullback
            ((D' 𝒰 f).t i j ≫
              (D' 𝒰 f).f j i)).mapIso (d j) := by
      rw [canonicalBaseChangeTransition 𝒰 f W i j]
    _ = baseChangeTransition 𝒰 f A i j :=
      conjugatedTransition_eq_of_compatible
        (D := D' 𝒰 f)
        (fun i =>
          (pullback (𝒰.pullbackHom f i)).obj (A₀.chart i))
        (fun i =>
          (pullback (𝒰.pullbackHom f i)).obj (A.chart i))
        (baseChangeTransition 𝒰 f A₀)
        (baseChangeTransition 𝒰 f A)
        d
        (baseChangeTransition_naturality 𝒰 f d₀.hom)
        i j

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
