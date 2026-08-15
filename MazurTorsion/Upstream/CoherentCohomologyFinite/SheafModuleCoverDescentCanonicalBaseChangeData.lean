/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentBaseChangeFunctor
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentTransitionData

/-!
# Comparison data for canonical descent under base change

This file names the chart comparison and the common normal-form overlap
comparison used by the canonical base-change coherence theorem.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

private abbrev D := 𝒰.gluedCover

private abbrev D' := gluedCover (𝒰.pullback₁ f)

/-- The chart square for the glued base-change map, with both open-cover
chart schemes exposed. -/
theorem gluedCoverChartMap_baseChangeGluedMap (i : 𝒰.I₀) :
    gluedCoverChartMap (𝒰.pullback₁ f) i ≫
        baseChangeGluedMap 𝒰 f =
      𝒰.pullbackHom f i ≫ gluedCoverChartMap 𝒰 i :=
  gluedCover_ι_baseChangeGluedMap 𝒰 f i

/-- The base-change overlap map commutes with the publicly typed target
legs. -/
theorem baseChangeOverlapMap_overlapTarget (i j : 𝒰.I₀) :
    baseChangeOverlapMap 𝒰 f i j ≫
        overlapTarget 𝒰 i j =
      overlapTarget (𝒰.pullback₁ f) i j ≫
        𝒰.pullbackHom f j :=
  baseChangeOverlapMap_gluedCover_target 𝒰 f i j

/-- Chart comparison for pulling back a global module between the two
glued covers. -/
noncomputable def canonicalBaseChangeChartIso
    (W : (D 𝒰).glued.Modules) (i : 𝒰.I₀) :
    ((restrictionFunctor (D := D' 𝒰 f)).obj
      ((pullback (baseChangeGluedMap 𝒰 f)).obj W)).chart i ≅
      (pullback (𝒰.pullbackHom f i)).obj
        (((restrictionFunctor (D := D 𝒰)).obj W).chart i) :=
  (pullbackComp
      ((D' 𝒰 f).ι i)
      (baseChangeGluedMap 𝒰 f)).app W ≪≫
    (pullbackCongr
      (gluedCover_ι_baseChangeGluedMap 𝒰 f i)).app W ≪≫
    (pullbackComp
      (𝒰.pullbackHom f i)
      ((D 𝒰).ι i)).symm.app W

/-- The canonical base-change chart comparison with both open-cover
chart schemes exposed. -/
noncomputable def canonicalBaseChangeChartIsoTyped
    (W : 𝒰.gluedCover.glued.Modules) (i : 𝒰.I₀) :
    (pullback (gluedCoverChartMap (𝒰.pullback₁ f) i)).obj
        ((pullback (baseChangeGluedMap 𝒰 f)).obj W) ≅
      (pullback (𝒰.pullbackHom f i)).obj
        (openCoverRestriction 𝒰 W i) :=
  pullbackSquareIso
    (gluedCoverChartMap (𝒰.pullback₁ f) i)
    (baseChangeGluedMap 𝒰 f)
    (𝒰.pullbackHom f i)
    (gluedCoverChartMap 𝒰 i)
    (gluedCoverChartMap_baseChangeGluedMap 𝒰 f i)
    W

/-- The glue-data chart comparison and its publicly typed base-change
form agree. -/
theorem canonicalBaseChangeChartIso_eq_typed
    (W : 𝒰.gluedCover.glued.Modules) (i : 𝒰.I₀) :
    canonicalBaseChangeChartIso 𝒰 f W i =
      canonicalBaseChangeChartIsoTyped 𝒰 f W i :=
  rfl

/-- Pullback of the canonical transition to a base-changed cover, with
all open-cover chart types exposed. -/
noncomputable def canonicalBaseChangePullbackIso
    (W : 𝒰.gluedCover.glued.Modules) (i j : 𝒰.I₀) :
    (pullback (overlapFst (𝒰.pullback₁ f) i j)).obj
        ((pullback (𝒰.pullbackHom f i)).obj
          (openCoverRestriction 𝒰 W i)) ≅
      (pullback (overlapTarget (𝒰.pullback₁ f) i j)).obj
        ((pullback (𝒰.pullbackHom f j)).obj
          (openCoverRestriction 𝒰 W j)) :=
  pullbackSquareIso
      (overlapFst (𝒰.pullback₁ f) i j)
      (𝒰.pullbackHom f i)
      (baseChangeOverlapMap 𝒰 f i j)
      (overlapFst 𝒰 i j)
      (baseChangeOverlapMap_overlapFst 𝒰 f i j).symm
      (openCoverRestriction 𝒰 W i) ≪≫
    (pullback (baseChangeOverlapMap 𝒰 f i j)).mapIso
      (openCoverRestrictionTransition 𝒰 W i j) ≪≫
    (pullbackSquareIso
      (overlapTarget (𝒰.pullback₁ f) i j)
      (𝒰.pullbackHom f j)
      (baseChangeOverlapMap 𝒰 f i j)
      (overlapTarget 𝒰 i j)
      (baseChangeOverlapMap_overlapTarget 𝒰 f i j).symm
      (openCoverRestriction 𝒰 W j)).symm

/-- The general base-change transition agrees with its publicly typed
form on canonical restrictions. -/
theorem baseChangeTransition_restriction_eq_typed
    (W : 𝒰.gluedCover.glued.Modules) (i j : 𝒰.I₀) :
    baseChangeTransition 𝒰 f
        ((restrictionFunctor (D := 𝒰.gluedCover)).obj W) i j =
      canonicalBaseChangePullbackIso 𝒰 f W i j :=
  rfl

/-- The transported canonical base-change transition, with open-cover
chart types exposed. -/
noncomputable def canonicalBaseChangeTransportIso
    (W : 𝒰.gluedCover.glued.Modules) (i j : 𝒰.I₀) :
    (pullback (overlapFst (𝒰.pullback₁ f) i j)).obj
        ((pullback (𝒰.pullbackHom f i)).obj
          (openCoverRestriction 𝒰 W i)) ≅
      (pullback (overlapTarget (𝒰.pullback₁ f) i j)).obj
        ((pullback (𝒰.pullbackHom f j)).obj
          (openCoverRestriction 𝒰 W j)) :=
  (pullback (overlapFst (𝒰.pullback₁ f) i j)).mapIso
      (canonicalBaseChangeChartIsoTyped 𝒰 f W i).symm ≪≫
    openCoverRestrictionTransition (𝒰.pullback₁ f)
      ((pullback (baseChangeGluedMap 𝒰 f)).obj W) i j ≪≫
    (pullback (overlapTarget (𝒰.pullback₁ f) i j)).mapIso
      (canonicalBaseChangeChartIsoTyped 𝒰 f W j)

/-- The general chart transport agrees with its publicly typed form for
the canonical base-change comparison. -/
theorem canonicalBaseChangeTransport_eq_typed
    (W : 𝒰.gluedCover.glued.Modules) (i j : 𝒰.I₀) :
    transportTransition
        ((restrictionFunctor
          (D := gluedCover (𝒰.pullback₁ f))).obj
          ((pullback (baseChangeGluedMap 𝒰 f)).obj W))
        (fun i =>
          (pullback (𝒰.pullbackHom f i)).obj
            (((restrictionFunctor
              (D := 𝒰.gluedCover)).obj W).chart i))
        (canonicalBaseChangeChartIso 𝒰 f W) i j =
      canonicalBaseChangeTransportIso 𝒰 f W i j :=
  rfl

/-- The two threefold routes from a pulled-back overlap to the original
glued scheme agree. -/
theorem canonicalBaseChangeComposite_eq
    (i j : 𝒰.I₀) :
    ((overlapFst (𝒰.pullback₁ f) i j ≫
        𝒰.pullbackHom f i) ≫
      gluedCoverChartMap 𝒰 i) =
    ((overlapTarget (𝒰.pullback₁ f) i j ≫
      𝒰.pullbackHom f j) ≫
      gluedCoverChartMap 𝒰 j) := by
  let p := baseChangeOverlapMap 𝒰 f i j
  have hsource :
      (D' 𝒰 f).f i j ≫
          𝒰.pullbackHom f i =
        p ≫ (D 𝒰).f i j :=
    (baseChangeOverlapMap_gluedCover_f
      𝒰 f i j).symm
  have htarget :
      p ≫ ((D 𝒰).t i j ≫
          (D 𝒰).f j i) =
        ((D' 𝒰 f).t i j ≫
          (D' 𝒰 f).f j i) ≫
            𝒰.pullbackHom f j :=
    baseChangeOverlapMap_gluedCover_target
      𝒰 f i j
  have hglue :
      (D 𝒰).f i j ≫ (D 𝒰).ι i =
        ((D 𝒰).t i j ≫
          (D 𝒰).f j i) ≫
            (D 𝒰).ι j := by
    rw [Category.assoc]
    exact ((D 𝒰).glue_condition i j).symm
  calc
    (((D' 𝒰 f).f i j ≫
          𝒰.pullbackHom f i) ≫
        (D 𝒰).ι i) =
      (p ≫ (D 𝒰).f i j) ≫
        (D 𝒰).ι i :=
      congrArg (fun q => q ≫ (D 𝒰).ι i)
        hsource
    _ =
      p ≫ ((D 𝒰).f i j ≫
        (D 𝒰).ι i) :=
      Category.assoc _ _ _
    _ =
      p ≫ (((D 𝒰).t i j ≫
          (D 𝒰).f j i) ≫
        (D 𝒰).ι j) :=
      congrArg (fun q => p ≫ q) hglue
    _ =
      (p ≫ ((D 𝒰).t i j ≫
          (D 𝒰).f j i)) ≫
        (D 𝒰).ι j :=
      (Category.assoc _ _ _).symm
    _ =
      ((D' 𝒰 f).t i j ≫
          (D' 𝒰 f).f j i) ≫
          𝒰.pullbackHom f j ≫
        (D 𝒰).ι j :=
      congrArg (fun q => q ≫ (D 𝒰).ι j)
        htarget
    _ =
      ((((D' 𝒰 f).t i j ≫
          (D' 𝒰 f).f j i) ≫
        𝒰.pullbackHom f j) ≫
        (D 𝒰).ι j) := rfl

/-- Common normal form for both pasted pullback-comparison chains on an
overlap. -/
noncomputable def canonicalBaseChangeNormalIso
    (W : (D 𝒰).glued.Modules) (i j : 𝒰.I₀) :
    (pullback (overlapFst (𝒰.pullback₁ f) i j)).obj
        ((pullback (𝒰.pullbackHom f i)).obj
          ((pullback (gluedCoverChartMap 𝒰 i)).obj W)) ≅
      (pullback
        (overlapTarget (𝒰.pullback₁ f) i j)).obj
        ((pullback (𝒰.pullbackHom f j)).obj
          ((pullback (gluedCoverChartMap 𝒰 j)).obj W)) :=
  (pullbackComp
      (overlapFst (𝒰.pullback₁ f) i j)
      (𝒰.pullbackHom f i)).app
        ((pullback (gluedCoverChartMap 𝒰 i)).obj W) ≪≫
    (pullbackComp
      (overlapFst (𝒰.pullback₁ f) i j ≫
        𝒰.pullbackHom f i)
      (gluedCoverChartMap 𝒰 i)).app W ≪≫
    (pullbackCongr
      (canonicalBaseChangeComposite_eq
        𝒰 f i j)).app W ≪≫
    (pullbackComp
      (overlapTarget (𝒰.pullback₁ f) i j ≫
        𝒰.pullbackHom f j)
      (gluedCoverChartMap 𝒰 j)).symm.app W ≪≫
    (pullbackComp
      (overlapTarget (𝒰.pullback₁ f) i j)
      (𝒰.pullbackHom f j)).symm.app
        ((pullback (gluedCoverChartMap 𝒰 j)).obj W)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
