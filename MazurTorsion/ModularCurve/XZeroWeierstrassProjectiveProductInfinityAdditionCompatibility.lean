/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductMixedAdditionCompatibility
import MazurTorsion.ModularCurve.XZeroWeierstrassInfinityPairNeighborhoodSecantCompatibility
import MazurTorsion.ModularCurve.XZeroWeierstrassStandardPairOutputYCompatibility
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Compatibility and gluing on the infinity projective-pair chart

The three genuine members of `projectiveInfinityPairAdditionOpenCover` carry
the transported standard-pair law, the regular law around `(O, O)`, and the
normalized secant output-`Z` law.  This file identifies their categorical
pullbacks with explicit localizations, proves every pairwise equality, and
glues the local laws over the whole infinity-by-infinity chart.

The design boundary is `projectiveInfinityPairAdditionMorphism`, with named
restriction theorems for all three cover members.  It is the downstream
infinity-chart input to the final four-chart projective-product gluing.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem infinityPullback_morphism_compatible_self
    {U X Y : Scheme.{u}} (i : U ⟶ X) [Mono i] (f : U ⟶ Y) :
    pullback.fst i i ≫ f = pullback.snd i i ≫ f := by
  have hfst : pullback.fst i i = pullback.snd i i := by
    apply (cancel_mono i).mp
    exact pullback.condition
  exact congrArg (fun q => q ≫ f) hfst

private theorem infinityPullback_morphism_compatible_symm
    {U V X Y : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X)
    (f : U ⟶ Y) (g : V ⟶ Y)
    (h : pullback.fst i j ≫ f = pullback.snd i j ≫ g) :
    pullback.fst j i ≫ g = pullback.snd j i ≫ f := by
  apply (cancel_epi (pullbackSymmetry i j).hom).mp
  calc
    _ = ((pullbackSymmetry i j).hom ≫ pullback.fst j i) ≫ g :=
      (Category.assoc _ _ _).symm
    _ = pullback.snd i j ≫ g := congrArg (fun q => q ≫ g)
      (pullbackSymmetry_hom_comp_fst i j)
    _ = pullback.fst i j ≫ f := h.symm
    _ = ((pullbackSymmetry i j).hom ≫ pullback.snd j i) ≫ f :=
      congrArg (fun q => q ≫ f) (pullbackSymmetry_hom_comp_snd i j).symm
    _ = _ := Category.assoc _ _ _

/-! ## The regular/output-Z pullback -/

/-- Coordinate ring of the regular addition source further restricted to the
raw secant output-`Z` open. -/
abbrev projectiveInfinityPairOriginSecantZOverlapRing
    (W : WeierstrassCurve K) :=
  Localization.Away
    (algebraMap (projectiveInfinityPairCoordinateRing W)
      (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)))

private def projectiveInfinityPairOriginSecantZOverlapBaseRingHom
    (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W →+*
      projectiveInfinityPairOriginSecantZOverlapRing W :=
  (algebraMap (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
      (projectiveInfinityPairOriginSecantZOverlapRing W)).comp
    (algebraMap (projectiveInfinityPairCoordinateRing W)
      (projectiveInfinityPairNeighborhoodAdditionOutputRing W))

/-- Coordinate-ring restriction from the regular addition source to its
secant-`Z` intersection. -/
noncomputable def projectiveInfinityPairOriginSecantZOverlapToOriginRing
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodAdditionOutputRing W →+*
      projectiveInfinityPairOriginSecantZOverlapRing W :=
  algebraMap (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
    (projectiveInfinityPairOriginSecantZOverlapRing W)

/-- Restriction from the regular addition source to its secant-`Z`
intersection. -/
noncomputable def projectiveInfinityPairOriginSecantZOverlapToOrigin
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairOriginSecantZOverlapRing W)) ⟶
      Spec (.of (projectiveInfinityPairNeighborhoodAdditionOutputRing W)) :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairOriginSecantZOverlapToOriginRing W))

private theorem projectiveInfinityPairOriginSecantZOverlap_rawZ_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (projectiveInfinityPairOriginSecantZOverlapBaseRingHom W
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3))) := by
  simpa only [projectiveInfinityPairOriginSecantZOverlapBaseRingHom,
    RingHom.comp_apply] using
    (IsLocalization.Away.algebraMap_isUnit
      (S := projectiveInfinityPairOriginSecantZOverlapRing W)
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3))))

/-- Coordinate-ring restriction from the secant output-`Z` source to the
regular/secant intersection. -/
noncomputable def projectiveInfinityPairOriginSecantZOverlapToSecantZRing
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionOutputRing W (false, false) true →+*
      projectiveInfinityPairOriginSecantZOverlapRing W := by
  change Localization.Away
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)) →+*
    projectiveInfinityPairOriginSecantZOverlapRing W
  exact IsLocalization.Away.lift
    (R := projectiveInfinityPairCoordinateRing W)
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3)))
    (P := projectiveInfinityPairOriginSecantZOverlapRing W)
    (g := projectiveInfinityPairOriginSecantZOverlapBaseRingHom W)
    (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3))
    (projectiveInfinityPairOriginSecantZOverlap_rawZ_isUnit W)

@[simp]
theorem projectiveInfinityPairOriginSecantZOverlapToSecantZRing_algebraMap
    (W : WeierstrassCurve K)
    (a : projectiveInfinityPairCoordinateRing W) :
    projectiveInfinityPairOriginSecantZOverlapToSecantZRing W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectivePairChartAdditionOutputRing W (false, false) true) a) =
      projectiveInfinityPairOriginSecantZOverlapBaseRingHom W a := by
  change (IsLocalization.Away.lift
      (S := Localization.Away
        (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3)))
      (P := projectiveInfinityPairOriginSecantZOverlapRing W)
      (g := projectiveInfinityPairOriginSecantZOverlapBaseRingHom W)
      (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3))
      (projectiveInfinityPairOriginSecantZOverlap_rawZ_isUnit W))
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (Localization.Away
            (projectivePairChartAdditionCoordinates W (false, false)
              (2 : Fin 3))) a) = _
  exact IsLocalization.Away.lift_eq
    (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3))
    (projectiveInfinityPairOriginSecantZOverlap_rawZ_isUnit W) a

/-- Restriction from the secant output-`Z` source to the regular/secant
intersection. -/
noncomputable def projectiveInfinityPairOriginSecantZOverlapToSecantZ
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairOriginSecantZOverlapRing W)) ⟶
      Spec (.of
        (projectivePairChartAdditionOutputRing W (false, false) true)) :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairOriginSecantZOverlapToSecantZRing W))

instance projectiveInfinityPairOriginSecantZOverlapToOrigin_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectiveInfinityPairOriginSecantZOverlapToOrigin W) := by
  dsimp only [projectiveInfinityPairOriginSecantZOverlapToOrigin,
    projectiveInfinityPairOriginSecantZOverlapToOriginRing,
    projectiveInfinityPairOriginSecantZOverlapRing]
  infer_instance

/-- The two restrictions of the explicit overlap have the same map into the
infinity-by-infinity chart. -/
theorem projectiveInfinityPairOriginSecantZOverlap_open_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginSecantZOverlapToOrigin W ≫
        projectiveInfinityPairOriginAdditionOpen W =
      projectiveInfinityPairOriginSecantZOverlapToSecantZ W ≫
        projectivePairChartAdditionOutputOpen W (false, false) true := by
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (false, false)).hom).mp
  simp only [projectiveInfinityPairOriginSecantZOverlapToOrigin,
    projectiveInfinityPairOriginAdditionOpen,
    projectiveInfinityPairNeighborhoodAdditionOutputOpen,
    projectiveInfinityPairNeighborhoodOpen,
    projectiveInfinityPairOriginSecantZOverlapToSecantZ,
    projectivePairChartAdditionOutputOpen, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simp only [← Spec.map_comp]
  rw [Spec.map_inj]
  simp only [← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change projectiveInfinityPairOriginSecantZOverlapToOriginRing W
      (algebraMap (projectiveInfinityPairNeighborhoodRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W) a)) =
    projectiveInfinityPairOriginSecantZOverlapToSecantZRing W
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectivePairChartAdditionOutputRing W (false, false) true) a)
  rw [projectiveInfinityPairOriginSecantZOverlapToSecantZRing_algebraMap]
  change projectiveInfinityPairOriginSecantZOverlapToOriginRing W
      (algebraMap (projectiveInfinityPairNeighborhoodRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W) a)) =
    projectiveInfinityPairOriginSecantZOverlapToOriginRing W
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W) a)
  exact congrArg
    (projectiveInfinityPairOriginSecantZOverlapToOriginRing W)
    (IsScalarTower.algebraMap_apply
      (projectiveInfinityPairCoordinateRing W)
      (projectiveInfinityPairNeighborhoodRing W)
      (projectiveInfinityPairNeighborhoodAdditionOutputRing W) a).symm

/-- The regular source sees the secant-`Z` member precisely on the principal
open represented by the explicit overlap. -/
theorem projectiveInfinityPairOriginAddition_preimage_secantZ
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginAdditionOpen W ⁻¹ᵁ
        (projectivePairChartAdditionOutputOpen W
          (false, false) true).opensRange =
      (projectiveInfinityPairOriginSecantZOverlapToOrigin W).opensRange := by
  let e := projectivePairChartIsoSpecTensor W (false, false)
  have hsecant :
      e.hom ⁻¹ᵁ (projectiveInfinityPairSecantZOpenAffine W).opensRange =
        (projectivePairChartAdditionOutputOpen W
          (false, false) true).opensRange := by
    dsimp [e, projectiveInfinityPairSecantZOpenAffine]
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.preimage_image_eq]
  have haffine :
      (projectiveInfinityPairOriginAdditionOpenAffine W) ⁻¹ᵁ
          (projectiveInfinityPairSecantZOpenAffine W).opensRange =
        (projectiveInfinityPairOriginSecantZOverlapToOrigin W).opensRange := by
    have hsecantRange :
        (projectiveInfinityPairSecantZOpenAffine W).opensRange =
          PrimeSpectrum.basicOpen
            (show projectiveInfinityPairCoordinateRing W from
              projectivePairChartAdditionCoordinates W (false, false)
                (2 : Fin 3)) :=
      projectiveInfinityPairSecantZOpenAffine_opensRange W
    rw [hsecantRange]
    simp only [projectiveInfinityPairOriginAdditionOpenAffine,
      projectiveInfinityPairOriginAdditionOpen,
      projectiveInfinityPairNeighborhoodAdditionOutputOpen,
      projectiveInfinityPairNeighborhoodOpen, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact (Scheme.Hom.opensRange_localizationAway
      (R := .of (projectiveInfinityPairNeighborhoodAdditionOutputRing W))
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)))).symm
  calc
    projectiveInfinityPairOriginAdditionOpen W ⁻¹ᵁ
          (projectivePairChartAdditionOutputOpen W
            (false, false) true).opensRange =
        projectiveInfinityPairOriginAdditionOpen W ⁻¹ᵁ
          (e.hom ⁻¹ᵁ
            (projectiveInfinityPairSecantZOpenAffine W).opensRange) := by
              rw [hsecant]
    _ = (projectiveInfinityPairOriginAdditionOpenAffine W) ⁻¹ᵁ
          (projectiveInfinityPairSecantZOpenAffine W).opensRange := by
            rfl
    _ = (projectiveInfinityPairOriginSecantZOverlapToOrigin W).opensRange :=
      haffine

/-- The explicit regular/secant-`Z` overlap is the categorical pullback of
the corresponding infinity-cover members. -/
theorem projectiveInfinityPairOriginSecantZ_isPullback
    (W : WeierstrassCurve K) :
    IsPullback
      (projectiveInfinityPairOriginSecantZOverlapToSecantZ W)
      (projectiveInfinityPairOriginSecantZOverlapToOrigin W)
      (projectivePairChartAdditionOutputOpen W (false, false) true)
      (projectiveInfinityPairOriginAdditionOpen W) := by
  apply IsOpenImmersion.isPullback
  · exact projectiveInfinityPairOriginSecantZOverlap_open_eq W
  · exact projectiveInfinityPairOriginAddition_preimage_secantZ W

private def projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W →+*
      projectiveInfinityPairOriginSecantZOverlapRing W :=
  (projectiveInfinityPairOriginSecantZOverlapToOriginRing W).comp
    (algebraMap (projectiveInfinityPairNeighborhoodRing W)
      (projectiveInfinityPairNeighborhoodAdditionOutputRing W))

@[simp]
private theorem
    projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom_algebraMap
    (W : WeierstrassCurve K)
    (a : projectiveInfinityPairCoordinateRing W) :
    projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W) a) =
      projectiveInfinityPairOriginSecantZOverlapBaseRingHom W a := by
  change projectiveInfinityPairOriginSecantZOverlapToOriginRing W
      (algebraMap (projectiveInfinityPairNeighborhoodRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W) a)) =
    projectiveInfinityPairOriginSecantZOverlapToOriginRing W
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W) a)
  exact congrArg
    (projectiveInfinityPairOriginSecantZOverlapToOriginRing W)
    (IsScalarTower.algebraMap_apply
      (projectiveInfinityPairCoordinateRing W)
      (projectiveInfinityPairNeighborhoodRing W)
      (projectiveInfinityPairNeighborhoodAdditionOutputRing W) a).symm

private theorem projectiveInfinityPairOriginSecantZOverlap_localY_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom W
        (projectiveInfinityPairNeighborhoodAdditionCoordinates W
          (1 : Fin 3))) := by
  exact (IsLocalization.Away.algebraMap_isUnit
    (S := projectiveInfinityPairNeighborhoodAdditionOutputRing W)
    (projectiveInfinityPairNeighborhoodAdditionCoordinates W
      (1 : Fin 3))).map
        (projectiveInfinityPairOriginSecantZOverlapToOriginRing W)

private theorem projectiveInfinityPairOriginSecantZOverlap_dCube_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom W
        (projectiveInfinityPairNeighborhoodX₁ W -
          projectiveInfinityPairNeighborhoodX₂ W) ^ 3) := by
  let f := projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom W
  have hscale := congrFun
    (projectiveInfinityPairNeighborhood_rawAdditionCoordinates_eq_smul W)
    (2 : Fin 3)
  change algebraMap (projectiveInfinityPairCoordinateRing W)
      (projectiveInfinityPairNeighborhoodRing W)
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)) =
    (projectiveInfinityPairNeighborhoodX₁ W -
      projectiveInfinityPairNeighborhoodX₂ W) ^ 3 *
      projectiveInfinityPairNeighborhoodAdditionCoordinates W
        (2 : Fin 3) at hscale
  have hproduct : IsUnit
      (f (projectiveInfinityPairNeighborhoodX₁ W -
            projectiveInfinityPairNeighborhoodX₂ W) ^ 3 *
        f (projectiveInfinityPairNeighborhoodAdditionCoordinates W
          (2 : Fin 3))) := by
    rw [← map_pow, ← map_mul, ← hscale]
    exact projectiveInfinityPairOriginSecantZOverlap_rawZ_isUnit W
  exact (IsUnit.mul_iff.mp hproduct).1

private theorem projectiveInfinityPairOriginSecantZOverlap_rawY_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (projectiveInfinityPairOriginSecantZOverlapBaseRingHom W
        (projectivePairChartAdditionCoordinates W (false, false)
          (1 : Fin 3))) := by
  let f := projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom W
  have hscale := congrFun
    (projectiveInfinityPairNeighborhood_rawAdditionCoordinates_eq_smul W)
    (1 : Fin 3)
  change algebraMap (projectiveInfinityPairCoordinateRing W)
      (projectiveInfinityPairNeighborhoodRing W)
      (projectivePairChartAdditionCoordinates W (false, false)
        (1 : Fin 3)) =
    (projectiveInfinityPairNeighborhoodX₁ W -
      projectiveInfinityPairNeighborhoodX₂ W) ^ 3 *
      projectiveInfinityPairNeighborhoodAdditionCoordinates W
        (1 : Fin 3) at hscale
  rw [←
    projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom_algebraMap]
  rw [hscale, map_mul, map_pow]
  exact IsUnit.mul
    (projectiveInfinityPairOriginSecantZOverlap_dCube_isUnit W)
    (projectiveInfinityPairOriginSecantZOverlap_localY_isUnit W)

private theorem projectiveInfinityPairOriginSecantZOverlap_B_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (projectiveInfinityPairOriginSecantZOverlapBaseRingHom W
        (projectiveInfinityPairAdditionB12 W)) := by
  rw [←
    projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom_algebraMap]
  exact (IsLocalization.Away.algebraMap_isUnit
    (S := projectiveInfinityPairNeighborhoodRing W)
    (projectiveInfinityPairAdditionB12 W)).map
      (projectiveInfinityPairOriginSecantZOverlapNeighborhoodRingHom W)

private theorem projectiveInfinityPairOriginSecantZOverlap_oldDenominator_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (projectiveInfinityPairOriginSecantZOverlapBaseRingHom W
        (projectiveInfinityPairAdditionB12 W *
          projectivePairChartAdditionCoordinates W (false, false)
            (1 : Fin 3))) := by
  rw [map_mul]
  exact IsUnit.mul
    (projectiveInfinityPairOriginSecantZOverlap_B_isUnit W)
    (projectiveInfinityPairOriginSecantZOverlap_rawY_isUnit W)

/-- Restrict the old regular/secant-`Y` overlap to the new exact
regular/secant-`Z` overlap. -/
noncomputable def projectiveInfinityPairOriginSecantZOverlapToOldOverlapRing
    (W : WeierstrassCurve K) :
    projectiveInfinityPairSecantOverlapRing W →+*
      projectiveInfinityPairOriginSecantZOverlapRing W :=
  IsLocalization.Away.lift
    (R := projectiveInfinityPairCoordinateRing W)
    (S := projectiveInfinityPairSecantOverlapRing W)
    (P := projectiveInfinityPairOriginSecantZOverlapRing W)
    (g := projectiveInfinityPairOriginSecantZOverlapBaseRingHom W)
    (projectiveInfinityPairAdditionB12 W *
      projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
    (projectiveInfinityPairOriginSecantZOverlap_oldDenominator_isUnit W)

@[simp]
theorem projectiveInfinityPairOriginSecantZOverlapToOldOverlapRing_algebraMap
    (W : WeierstrassCurve K)
    (a : projectiveInfinityPairCoordinateRing W) :
    projectiveInfinityPairOriginSecantZOverlapToOldOverlapRing W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairSecantOverlapRing W) a) =
      projectiveInfinityPairOriginSecantZOverlapBaseRingHom W a := by
  exact IsLocalization.Away.lift_eq
    (projectiveInfinityPairAdditionB12 W *
      projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
    (projectiveInfinityPairOriginSecantZOverlap_oldDenominator_isUnit W) a

/-- The new overlap mapped into the old regular/secant-`Y` overlap. -/
noncomputable def projectiveInfinityPairOriginSecantZOverlapToOldOverlap
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairOriginSecantZOverlapRing W)) ⟶
      Spec (.of (projectiveInfinityPairSecantOverlapRing W)) :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairOriginSecantZOverlapToOldOverlapRing W))

private theorem projectiveInfinityPairOriginSecantZOverlap_outputYZDenominator_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (projectiveInfinityPairOriginSecantZOverlapBaseRingHom W
        (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3) *
          projectivePairChartAdditionCoordinates W (false, false)
            (1 : Fin 3))) := by
  rw [map_mul]
  exact IsUnit.mul
    (projectiveInfinityPairOriginSecantZOverlap_rawZ_isUnit W)
    (projectiveInfinityPairOriginSecantZOverlap_rawY_isUnit W)

/-- Restrict the exact secant output-`YZ` overlap to the regular/secant-`Z`
overlap. -/
noncomputable def projectiveInfinityPairOriginSecantZOverlapToOutputYZRing
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionOutputOverlapRing W (false, false) →+*
      projectiveInfinityPairOriginSecantZOverlapRing W :=
  IsLocalization.Away.lift
    (R := projectiveInfinityPairCoordinateRing W)
    (S := projectivePairChartAdditionOutputOverlapRing W (false, false))
    (P := projectiveInfinityPairOriginSecantZOverlapRing W)
    (g := projectiveInfinityPairOriginSecantZOverlapBaseRingHom W)
    (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
    (projectiveInfinityPairOriginSecantZOverlap_outputYZDenominator_isUnit W)

@[simp]
theorem projectiveInfinityPairOriginSecantZOverlapToOutputYZRing_algebraMap
    (W : WeierstrassCurve K)
    (a : projectiveInfinityPairCoordinateRing W) :
    projectiveInfinityPairOriginSecantZOverlapToOutputYZRing W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectivePairChartAdditionOutputOverlapRing W (false, false)) a) =
      projectiveInfinityPairOriginSecantZOverlapBaseRingHom W a := by
  exact IsLocalization.Away.lift_eq
    (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
    (projectiveInfinityPairOriginSecantZOverlap_outputYZDenominator_isUnit W) a

/-- The new overlap mapped into the exact secant output-`YZ` overlap. -/
noncomputable def projectiveInfinityPairOriginSecantZOverlapToOutputYZ
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairOriginSecantZOverlapRing W)) ⟶
      Spec (.of
        (projectivePairChartAdditionOutputOverlapRing W (false, false))) :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairOriginSecantZOverlapToOutputYZRing W))

private theorem
    projectiveInfinityPairOriginSecantZOverlapToOldOverlap_comp_origin
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
        projectiveInfinityPairSecantOverlapToOriginAddition W =
      projectiveInfinityPairOriginSecantZOverlapToOrigin W := by
  have hring :
      (projectiveInfinityPairOriginSecantZOverlapToOldOverlapRing W).comp
          (projectiveInfinityPairSecantOverlapToOriginAdditionRing W) =
        projectiveInfinityPairOriginSecantZOverlapToOriginRing W := by
    apply IsLocalization.ringHom_ext
      (.powers
        (projectiveInfinityPairNeighborhoodAdditionCoordinates W
          (1 : Fin 3)))
    apply IsLocalization.ringHom_ext
      (.powers (projectiveInfinityPairAdditionB12 W))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectiveInfinityPairSecantOverlapToOriginAdditionRing_algebraMap,
      projectiveInfinityPairSecantOverlapToNeighborhoodRing_algebraMap,
      projectiveInfinityPairOriginSecantZOverlapToOldOverlapRing_algebraMap,
      projectiveInfinityPairOriginSecantZOverlapBaseRingHom]
    exact congrArg
      (projectiveInfinityPairOriginSecantZOverlapToOriginRing W)
      (IsScalarTower.algebraMap_apply
        (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairNeighborhoodRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W) a).symm
  rw [projectiveInfinityPairOriginSecantZOverlapToOldOverlap,
    projectiveInfinityPairSecantOverlapToOriginAddition,
    projectiveInfinityPairOriginSecantZOverlapToOrigin, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

private theorem
    projectiveInfinityPairOriginSecantZOverlap_specMap_comp_secantZ
    (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
          (projectiveInfinityPairOriginSecantZOverlapToOutputYZRing W)) ≫
        Spec.map (CommRingCat.ofHom
          (projectivePairChartAdditionOutputOverlapToStandardRing W
            (false, false))) =
      (show
        Spec (.of (projectiveInfinityPairOriginSecantZOverlapRing W)) ⟶
          Spec (.of
            (projectivePairChartAdditionOutputRing W
              (false, false) true))
        from Spec.map (CommRingCat.ofHom
          (projectiveInfinityPairOriginSecantZOverlapToSecantZRing W))) := by
  have hring :
      (projectiveInfinityPairOriginSecantZOverlapToOutputYZRing W).comp
          (projectivePairChartAdditionOutputOverlapToStandardRing W
            (false, false)) =
        projectiveInfinityPairOriginSecantZOverlapToSecantZRing W := by
    letI : IsLocalization
        (.powers
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3)))
        (projectivePairChartAdditionOutputRing W (false, false) true) := by
      change IsLocalization
        (.powers
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3)))
        (Localization.Away
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3)))
      infer_instance
    apply IsLocalization.ringHom_ext
      (.powers
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectivePairChartAdditionOutputOverlapToStandardRing_algebraMap,
      projectiveInfinityPairOriginSecantZOverlapToOutputYZRing_algebraMap,
      projectiveInfinityPairOriginSecantZOverlapToSecantZRing_algebraMap]
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

private theorem
    projectiveInfinityPairOriginSecantZOverlapToOutputYZ_comp_secantZ
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
        projectivePairChartAdditionOutputOverlapToStandard W
          (false, false) =
      projectiveInfinityPairOriginSecantZOverlapToSecantZ W := by
  exact projectiveInfinityPairOriginSecantZOverlap_specMap_comp_secantZ W

private theorem
    projectiveInfinityPairOriginSecantZOverlap_secantY_maps_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
        projectiveInfinityPairSecantOverlapToSecant W =
      projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
        projectivePairChartAdditionOutputOverlapToInfinity W
          (false, false) := by
  apply (cancel_mono
    (projectivePairChartAdditionOutputOpen W (false, false) false)).mp
  calc
    _ = projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
        (projectiveInfinityPairSecantOverlapToSecant W ≫
          projectivePairChartAdditionOutputOpen W
            (false, false) false) := Category.assoc _ _ _
    _ = projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
        (projectiveInfinityPairSecantOverlapToOriginAddition W ≫
          projectiveInfinityPairOriginAdditionOpen W) := by
            rw [projectiveInfinityPairSecantOverlap_open_eq]
    _ = (projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
          projectiveInfinityPairSecantOverlapToOriginAddition W) ≫
        projectiveInfinityPairOriginAdditionOpen W :=
      (Category.assoc _ _ _).symm
    _ = projectiveInfinityPairOriginSecantZOverlapToOrigin W ≫
        projectiveInfinityPairOriginAdditionOpen W := by
          rw [projectiveInfinityPairOriginSecantZOverlapToOldOverlap_comp_origin]
    _ = projectiveInfinityPairOriginSecantZOverlapToSecantZ W ≫
        projectivePairChartAdditionOutputOpen W
          (false, false) true :=
      projectiveInfinityPairOriginSecantZOverlap_open_eq W
    _ = (projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
          projectivePairChartAdditionOutputOverlapToStandard W
            (false, false)) ≫
        projectivePairChartAdditionOutputOpen W
          (false, false) true := by
            rw [
              projectiveInfinityPairOriginSecantZOverlapToOutputYZ_comp_secantZ]
    _ = projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
        (projectivePairChartAdditionOutputOverlapToStandard W
            (false, false) ≫
          projectivePairChartAdditionOutputOpen W
            (false, false) true) := Category.assoc _ _ _
    _ = projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
        (projectivePairChartAdditionOutputOverlapToInfinity W
            (false, false) ≫
          projectivePairChartAdditionOutputOpen W
            (false, false) false) := by
              rw [projectivePairChartAdditionOutputOverlap_open_eq]
    _ = _ := (Category.assoc _ _ _).symm

/-- The regular origin-neighborhood law and the secant output-`Z` law agree
on their exact explicit overlap. -/
theorem projectiveInfinityPairOriginSecantZOverlap_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveInfinityPairOriginSecantZOverlapToOrigin W ≫
        projectiveInfinityPairOriginAdditionMorphism W =
      projectiveInfinityPairOriginSecantZOverlapToSecantZ W ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := by
  calc
    _ = (projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
          projectiveInfinityPairSecantOverlapToOriginAddition W) ≫
        projectiveInfinityPairOriginAdditionMorphism W := by
          rw [
            projectiveInfinityPairOriginSecantZOverlapToOldOverlap_comp_origin]
    _ = projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
        (projectiveInfinityPairSecantOverlapToOriginAddition W ≫
          projectiveInfinityPairOriginAdditionMorphism W) :=
      Category.assoc _ _ _
    _ = projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
        (projectiveInfinityPairSecantOverlapToSecant W ≫
          projectivePairChartAdditionOutputMorphism W
            (false, false) false) := by
              rw [projectiveInfinityPairSecantOverlap_morphisms_eq]
    _ = (projectiveInfinityPairOriginSecantZOverlapToOldOverlap W ≫
          projectiveInfinityPairSecantOverlapToSecant W) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) false := (Category.assoc _ _ _).symm
    _ = (projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
          projectivePairChartAdditionOutputOverlapToInfinity W
            (false, false)) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) false := by
            rw [projectiveInfinityPairOriginSecantZOverlap_secantY_maps_eq]
    _ = projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
        (projectivePairChartAdditionOutputOverlapToInfinity W
            (false, false) ≫
          projectivePairChartAdditionOutputMorphism W
            (false, false) false) := Category.assoc _ _ _
    _ = projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
        (projectivePairChartAdditionOutputOverlapToStandard W
            (false, false) ≫
          projectivePairChartAdditionOutputMorphism W
            (false, false) true) := by
              rw [projectivePairChartAdditionOutputOverlap_morphisms_eq]
    _ = (projectiveInfinityPairOriginSecantZOverlapToOutputYZ W ≫
          projectivePairChartAdditionOutputOverlapToStandard W
            (false, false)) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [projectiveInfinityPairOriginSecantZOverlapToOutputYZ_comp_secantZ]

/-- The regular and secant-`Z` laws agree on their categorical cover
pullback. -/
theorem projectiveInfinityPairOriginSecantZ_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectiveInfinityPairOriginAdditionOpen W)
          (projectivePairChartAdditionOutputOpen W (false, false) true) ≫
        projectiveInfinityPairOriginAdditionMorphism W =
      pullback.snd
          (projectiveInfinityPairOriginAdditionOpen W)
          (projectivePairChartAdditionOutputOpen W (false, false) true) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := by
  apply infinityPullback_morphism_compatible_symm
  let h := projectiveInfinityPairOriginSecantZ_isPullback W
  let hcanonical := IsPullback.of_hasPullback
    (projectivePairChartAdditionOutputOpen W (false, false) true)
    (projectiveInfinityPairOriginAdditionOpen W)
  let e := h.isoIsPullback _ _ hcanonical
  apply (cancel_epi e.hom).mp
  calc
    _ = projectiveInfinityPairOriginSecantZOverlapToSecantZ W ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := by
          rw [← Category.assoc, h.isoIsPullback_hom_fst _ _ hcanonical]
    _ = projectiveInfinityPairOriginSecantZOverlapToOrigin W ≫
        projectiveInfinityPairOriginAdditionMorphism W :=
      (projectiveInfinityPairOriginSecantZOverlap_morphisms_eq W).symm
    _ = (e.hom ≫
          pullback.snd
            (projectivePairChartAdditionOutputOpen W (false, false) true)
            (projectiveInfinityPairOriginAdditionOpen W)) ≫
        projectiveInfinityPairOriginAdditionMorphism W := by
          exact congrArg
            (fun q => q ≫ projectiveInfinityPairOriginAdditionMorphism W)
            (h.isoIsPullback_hom_snd _ _ hcanonical).symm
    _ = _ := Category.assoc _ _ _

/-! ## The double-standard/output-Z pullback -/

/-- Coordinate ring of the double input overlap further restricted to the
infinity-chart raw secant output-`Z` open. -/
abbrev projectiveInfinityPairDoubleSecantZOverlapRing
    (W : WeierstrassCurve K) :=
  Localization.Away
    (infinityPairToDoubleOverlapAlgHom W
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)))

private def projectiveInfinityPairDoubleSecantZOverlapInfinityRingHom
    (W : WeierstrassCurve K) :
    projectiveInfinityPairCoordinateRing W →+*
      projectiveInfinityPairDoubleSecantZOverlapRing W :=
  (algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
      (projectiveInfinityPairDoubleSecantZOverlapRing W)).comp
    (infinityPairToDoubleOverlapAlgHom W).toRingHom

/-- Restriction from the double input overlap to its secant-`Z`
intersection. -/
noncomputable def projectiveInfinityPairDoubleSecantZOverlapToDoubleRing
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapCoordinateRing W →+*
      projectiveInfinityPairDoubleSecantZOverlapRing W :=
  algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
    (projectiveInfinityPairDoubleSecantZOverlapRing W)

/-- Restriction from the double input overlap to its secant-`Z`
intersection. -/
noncomputable def projectiveInfinityPairDoubleSecantZOverlapToDouble
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairDoubleSecantZOverlapRing W)) ⟶
      projectivePairDoubleChartOverlapScheme W :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairDoubleSecantZOverlapToDoubleRing W))

private theorem projectiveInfinityPairDoubleSecantZOverlap_rawZ_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
        (projectiveInfinityPairDoubleSecantZOverlapRing W)
        (infinityPairToDoubleOverlapAlgHom W
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3)))) :=
  IsLocalization.Away.algebraMap_isUnit
    (S := projectiveInfinityPairDoubleSecantZOverlapRing W)
    (infinityPairToDoubleOverlapAlgHom W
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)))

private theorem projectiveInfinityPairDoubleSecantZOverlap_rawZ_hasInverse
    (W : WeierstrassCurve K) :
    ∃ b : projectiveInfinityPairDoubleSecantZOverlapRing W,
      algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
          (projectiveInfinityPairDoubleSecantZOverlapRing W)
          (infinityPairToDoubleOverlapAlgHom W
            (projectivePairChartAdditionCoordinates W (false, false)
              (2 : Fin 3))) * b = 1 :=
  (projectiveInfinityPairDoubleSecantZOverlap_rawZ_isUnit W).exists_right_inv

/-- Restriction from the infinity secant output-`Z` source to its double
input-overlap intersection. -/
noncomputable def projectiveInfinityPairDoubleSecantZOverlapToSecantZRing
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionOutputRing W (false, false) true →+*
      projectiveInfinityPairDoubleSecantZOverlapRing W := by
  change Localization.Away
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)) →+*
    projectiveInfinityPairDoubleSecantZOverlapRing W
  exact IsLocalization.Away.lift
    (R := projectiveInfinityPairCoordinateRing W)
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3)))
    (P := projectiveInfinityPairDoubleSecantZOverlapRing W)
    (g := projectiveInfinityPairDoubleSecantZOverlapInfinityRingHom W)
    (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3))
    (by
      apply isUnit_iff_exists_inv.mpr
      change ∃ b : projectiveInfinityPairDoubleSecantZOverlapRing W,
        algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
            (projectiveInfinityPairDoubleSecantZOverlapRing W)
            (infinityPairToDoubleOverlapAlgHom W
              (projectivePairChartAdditionCoordinates W (false, false)
                (2 : Fin 3))) * b = 1
      exact projectiveInfinityPairDoubleSecantZOverlap_rawZ_hasInverse W)

@[simp]
theorem projectiveInfinityPairDoubleSecantZOverlapToSecantZRing_algebraMap
    (W : WeierstrassCurve K)
    (a : projectiveInfinityPairCoordinateRing W) :
    projectiveInfinityPairDoubleSecantZOverlapToSecantZRing W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectivePairChartAdditionOutputRing W (false, false) true) a) =
      projectiveInfinityPairDoubleSecantZOverlapInfinityRingHom W a := by
  change (IsLocalization.Away.lift
      (S := Localization.Away
        (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3)))
      (P := projectiveInfinityPairDoubleSecantZOverlapRing W)
      (g := projectiveInfinityPairDoubleSecantZOverlapInfinityRingHom W)
      (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3))
      (by
        apply isUnit_iff_exists_inv.mpr
        change ∃ b : projectiveInfinityPairDoubleSecantZOverlapRing W,
          algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
              (projectiveInfinityPairDoubleSecantZOverlapRing W)
              (infinityPairToDoubleOverlapAlgHom W
                (projectivePairChartAdditionCoordinates W (false, false)
                  (2 : Fin 3))) * b = 1
        exact projectiveInfinityPairDoubleSecantZOverlap_rawZ_hasInverse W))
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (Localization.Away
            (projectivePairChartAdditionCoordinates W (false, false)
              (2 : Fin 3))) a) = _
  exact IsLocalization.Away.lift_eq
    (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3))
    (by
      apply isUnit_iff_exists_inv.mpr
      change ∃ b : projectiveInfinityPairDoubleSecantZOverlapRing W,
        algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
            (projectiveInfinityPairDoubleSecantZOverlapRing W)
            (infinityPairToDoubleOverlapAlgHom W
              (projectivePairChartAdditionCoordinates W (false, false)
                (2 : Fin 3))) * b = 1
      exact projectiveInfinityPairDoubleSecantZOverlap_rawZ_hasInverse W) a

/-- Restriction from the infinity secant output-`Z` source to its double
input-overlap intersection. -/
noncomputable def projectiveInfinityPairDoubleSecantZOverlapToSecantZ
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairDoubleSecantZOverlapRing W)) ⟶
      Spec (.of
        (projectivePairChartAdditionOutputRing W (false, false) true)) :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairDoubleSecantZOverlapToSecantZRing W))

instance projectiveInfinityPairDoubleSecantZOverlapToDouble_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectiveInfinityPairDoubleSecantZOverlapToDouble W) := by
  dsimp only [projectiveInfinityPairDoubleSecantZOverlapToDouble,
    projectiveInfinityPairDoubleSecantZOverlapToDoubleRing,
    projectiveInfinityPairDoubleSecantZOverlapRing]
  infer_instance

/-- The two restrictions of the explicit overlap have the same map into the
infinity-by-infinity chart. -/
theorem projectiveInfinityPairDoubleSecantZOverlap_open_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        projectivePairDoubleOverlapToInfinityPair W =
      projectiveInfinityPairDoubleSecantZOverlapToSecantZ W ≫
        projectivePairChartAdditionOutputOpen W (false, false) true := by
  have hring :
      (projectiveInfinityPairDoubleSecantZOverlapToDoubleRing W).comp
          (infinityPairToDoubleOverlapAlgHom W).toRingHom =
        (projectiveInfinityPairDoubleSecantZOverlapToSecantZRing W).comp
          (algebraMap (projectiveInfinityPairCoordinateRing W)
            (projectivePairChartAdditionOutputRing W
              (false, false) true)) := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectiveInfinityPairDoubleSecantZOverlapToSecantZRing_algebraMap,
      projectiveInfinityPairDoubleSecantZOverlapInfinityRingHom,
      projectiveInfinityPairDoubleSecantZOverlapToDoubleRing]
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (false, false)).hom).mp
  rw [Category.assoc,
    projectivePairDoubleOverlapToInfinityPair_comp_iso_hom]
  simp only [projectiveInfinityPairDoubleSecantZOverlapToDouble,
    projectiveInfinityPairDoubleSecantZOverlapToSecantZ,
    projectivePairChartAdditionOutputOpen, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

/-- The double input source sees the secant-`Z` member precisely on the
principal open represented by the explicit overlap. -/
theorem projectiveInfinityPairDouble_preimage_secantZ
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToInfinityPair W ⁻¹ᵁ
        (projectivePairChartAdditionOutputOpen W
          (false, false) true).opensRange =
      (projectiveInfinityPairDoubleSecantZOverlapToDouble W).opensRange := by
  let e := projectivePairChartIsoSpecTensor W (false, false)
  have hsecant :
      e.hom ⁻¹ᵁ (projectiveInfinityPairSecantZOpenAffine W).opensRange =
        (projectivePairChartAdditionOutputOpen W
          (false, false) true).opensRange := by
    dsimp [e, projectiveInfinityPairSecantZOpenAffine]
    rw [Scheme.Hom.opensRange_comp, Scheme.Hom.preimage_image_eq]
  have haffine :
      (projectivePairDoubleOverlapToInfinityPairAffine W) ⁻¹ᵁ
          (projectiveInfinityPairSecantZOpenAffine W).opensRange =
        (projectiveInfinityPairDoubleSecantZOverlapToDouble W).opensRange := by
    rw [projectiveInfinityPairSecantZOpenAffine_opensRange]
    simp only [projectivePairDoubleOverlapToInfinityPairAffine,
      projectivePairDoubleOverlapToInfinityPair_comp_iso_hom,
      projectiveInfinityPairDoubleSecantZOverlapToDouble,
      projectiveInfinityPairDoubleSecantZOverlapToDoubleRing]
    exact (Scheme.Hom.opensRange_localizationAway
      (R := .of (projectivePairDoubleChartOverlapCoordinateRing W))
      (infinityPairToDoubleOverlapAlgHom W
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)))).symm
  calc
    projectivePairDoubleOverlapToInfinityPair W ⁻¹ᵁ
          (projectivePairChartAdditionOutputOpen W
            (false, false) true).opensRange =
        projectivePairDoubleOverlapToInfinityPair W ⁻¹ᵁ
          (e.hom ⁻¹ᵁ
            (projectiveInfinityPairSecantZOpenAffine W).opensRange) := by
              rw [hsecant]
    _ = (projectivePairDoubleOverlapToInfinityPairAffine W) ⁻¹ᵁ
          (projectiveInfinityPairSecantZOpenAffine W).opensRange := by
            rfl
    _ = (projectiveInfinityPairDoubleSecantZOverlapToDouble W).opensRange :=
      haffine

/-- The explicit double/secant-`Z` overlap is the categorical pullback of
the corresponding infinity-cover members. -/
theorem projectiveInfinityPairDoubleSecantZ_isPullback
    (W : WeierstrassCurve K) :
    IsPullback
      (projectiveInfinityPairDoubleSecantZOverlapToSecantZ W)
      (projectiveInfinityPairDoubleSecantZOverlapToDouble W)
      (projectivePairChartAdditionOutputOpen W (false, false) true)
      (projectivePairDoubleOverlapToInfinityPair W) := by
  apply IsOpenImmersion.isPullback
  · exact projectiveInfinityPairDoubleSecantZOverlap_open_eq W
  · exact projectiveInfinityPairDouble_preimage_secantZ W

/-! ## Factoring through the infinity-by-standard chart -/

/-- Restrict the remaining infinity input in the second-factor overlap, so
both factors lie in the exact cubic chart overlap. -/
private noncomputable def
    projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom
    (W : WeierstrassCurve K) :
    projectivePairSecondChartOverlapCoordinateRing W false →ₐ[K]
      projectivePairDoubleChartOverlapCoordinateRing W :=
  Algebra.TensorProduct.map
    (infinityChartToCoveringChartOverlapAlgHom W)
    (AlgHom.id K (coveringChartOverlapCoordinateRing W))

private theorem projectivePairDoubleOverlap_standard_factor
    (W : WeierstrassCurve K) :
    (firstStandardOverlapToDoubleOverlapAlgHom W).comp
        (standardPairToFirstChartOverlapAlgHom W true) =
      standardPairToDoubleOverlapAlgHom W := by
  rfl

private theorem projectivePairDoubleOverlap_mixed_factors_eq
    (W : WeierstrassCurve K) :
    (firstStandardOverlapToDoubleOverlapAlgHom W).comp
        (infinityPairToFirstChartOverlapAlgHom W true) =
      (projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W).comp
        (standardPairToSecondChartOverlapAlgHom W false) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [firstStandardOverlapToDoubleOverlapAlgHom,
    infinityPairToFirstChartOverlapAlgHom,
    projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom,
    standardPairToSecondChartOverlapAlgHom]

private theorem projectivePairDoubleOverlap_infinity_factor
    (W : WeierstrassCurve K) :
    (projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W).comp
        (infinityPairToSecondChartOverlapAlgHom W false) =
      infinityPairToDoubleOverlapAlgHom W := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom,
    infinityPairToSecondChartOverlapAlgHom,
    infinityPairToDoubleOverlapAlgHom,
    firstInfinityOverlapToDoubleOverlapAlgHom,
    infinityPairToFirstChartOverlapAlgHom]

private noncomputable def projectivePairDoubleOverlapToFirstStandardOverlap
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      projectivePairFirstChartOverlapScheme W true :=
  Spec.map (CommRingCat.ofHom
    (firstStandardOverlapToDoubleOverlapAlgHom W).toRingHom)

private noncomputable def projectivePairDoubleOverlapToSecondInfinityOverlap
    (W : WeierstrassCurve K) :
    projectivePairDoubleChartOverlapScheme W ⟶
      projectivePairSecondChartOverlapScheme W false :=
  Spec.map (CommRingCat.ofHom
    (projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W).toRingHom)

private theorem
    projectivePairDoubleOverlapToFirstStandardOverlap_comp_standard
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToFirstStandardOverlap W ≫
        projectivePairFirstOverlapToStandardPair W true =
      projectivePairDoubleOverlapToStandardPair W := by
  have hring :
      (firstStandardOverlapToDoubleOverlapAlgHom W).toRingHom.comp
          (standardPairToFirstChartOverlapAlgHom W true).toRingHom =
        (standardPairToDoubleOverlapAlgHom W).toRingHom := by
    exact congrArg AlgHom.toRingHom
      (projectivePairDoubleOverlap_standard_factor W)
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (true, true)).hom).mp
  simp only [projectivePairDoubleOverlapToFirstStandardOverlap,
    projectivePairFirstOverlapToStandardPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id,
    projectivePairDoubleOverlapToStandardPair_comp_iso_hom]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

private theorem
    projectivePairDoubleOverlapToFirstStandardOverlap_comp_mixed
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToFirstStandardOverlap W ≫
        projectivePairFirstOverlapToInfinityPair W true =
      projectivePairDoubleOverlapToSecondInfinityOverlap W ≫
        projectivePairSecondOverlapToStandardPair W false := by
  have hring :
      (firstStandardOverlapToDoubleOverlapAlgHom W).toRingHom.comp
          (infinityPairToFirstChartOverlapAlgHom W true).toRingHom =
        (projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W).toRingHom.comp
          (standardPairToSecondChartOverlapAlgHom W false).toRingHom := by
    exact congrArg AlgHom.toRingHom
      (projectivePairDoubleOverlap_mixed_factors_eq W)
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (false, true)).hom).mp
  simp only [projectivePairDoubleOverlapToFirstStandardOverlap,
    projectivePairDoubleOverlapToSecondInfinityOverlap,
    projectivePairFirstOverlapToInfinityPair,
    projectivePairSecondOverlapToStandardPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

private theorem
    projectivePairDoubleOverlapToSecondInfinityOverlap_comp_infinity
    (W : WeierstrassCurve K) :
    projectivePairDoubleOverlapToSecondInfinityOverlap W ≫
        projectivePairSecondOverlapToInfinityPair W false =
      projectivePairDoubleOverlapToInfinityPair W := by
  have hring :
      (projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W).toRingHom.comp
          (infinityPairToSecondChartOverlapAlgHom W false).toRingHom =
        (infinityPairToDoubleOverlapAlgHom W).toRingHom := by
    exact congrArg AlgHom.toRingHom
      (projectivePairDoubleOverlap_infinity_factor W)
  apply (cancel_mono
    (projectivePairChartIsoSpecTensor W (false, false)).hom).mp
  simp only [projectivePairDoubleOverlapToSecondInfinityOverlap,
    projectivePairSecondOverlapToInfinityPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id,
    projectivePairDoubleOverlapToInfinityPair_comp_iso_hom]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

private def projectiveInfinityPairDoubleSecantZOverlapSecondRingHom
    (W : WeierstrassCurve K) :
    projectivePairSecondChartOverlapCoordinateRing W false →+*
      projectiveInfinityPairDoubleSecantZOverlapRing W :=
  (projectiveInfinityPairDoubleSecantZOverlapToDoubleRing W).comp
    (projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W).toRingHom

private theorem
    projectiveInfinityPairDoubleSecantZOverlap_secondDenominator_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDoubleSecantZOverlapSecondRingHom W
        (infinityPairToSecondChartOverlapAlgHom W false
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3))) =
      projectiveInfinityPairDoubleSecantZOverlapInfinityRingHom W
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)) := by
  change
    algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
        (projectiveInfinityPairDoubleSecantZOverlapRing W)
        (projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W
          (infinityPairToSecondChartOverlapAlgHom W false
            (projectivePairChartAdditionCoordinates W (false, false)
              (2 : Fin 3)))) =
      algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
        (projectiveInfinityPairDoubleSecantZOverlapRing W)
        (infinityPairToDoubleOverlapAlgHom W
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3)))
  exact congrArg
    (algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
      (projectiveInfinityPairDoubleSecantZOverlapRing W))
    (congrArg
      (fun f : projectiveInfinityPairCoordinateRing W →ₐ[K]
          projectivePairDoubleChartOverlapCoordinateRing W =>
        f (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)))
      (projectivePairDoubleOverlap_infinity_factor W))

private theorem
    projectiveInfinityPairDoubleSecantZOverlap_secondDenominator_hasInverse
    (W : WeierstrassCurve K) :
    ∃ b : projectiveInfinityPairDoubleSecantZOverlapRing W,
      projectiveInfinityPairDoubleSecantZOverlapSecondRingHom W
          (infinityPairToSecondChartOverlapAlgHom W false
            (projectivePairChartAdditionCoordinates W (false, false)
              (2 : Fin 3))) * b = 1 := by
  rw [projectiveInfinityPairDoubleSecantZOverlap_secondDenominator_eq]
  change ∃ b : projectiveInfinityPairDoubleSecantZOverlapRing W,
    algebraMap (projectivePairDoubleChartOverlapCoordinateRing W)
        (projectiveInfinityPairDoubleSecantZOverlapRing W)
        (infinityPairToDoubleOverlapAlgHom W
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3))) * b = 1
  exact projectiveInfinityPairDoubleSecantZOverlap_rawZ_hasInverse W

/-- Restrict the second-input/output compatibility source to the exact
double/secant intersection. -/
noncomputable def
    projectiveInfinityPairDoubleSecantZOverlapToSecondOutputRing
    (W : WeierstrassCurve K) :
    projectivePairSecondOverlapAdditionOutputRing W false true →+*
      projectiveInfinityPairDoubleSecantZOverlapRing W := by
  change Localization.Away
      (infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3))) →+*
    projectiveInfinityPairDoubleSecantZOverlapRing W
  exact IsLocalization.Away.lift
    (R := projectivePairSecondChartOverlapCoordinateRing W false)
    (S := Localization.Away
      (infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3))))
    (P := projectiveInfinityPairDoubleSecantZOverlapRing W)
    (g := projectiveInfinityPairDoubleSecantZOverlapSecondRingHom W)
    (infinityPairToSecondChartOverlapAlgHom W false
      (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3)))
    (isUnit_iff_exists_inv.mpr
      (projectiveInfinityPairDoubleSecantZOverlap_secondDenominator_hasInverse W))

@[simp]
theorem
    projectiveInfinityPairDoubleSecantZOverlapToSecondOutputRing_algebraMap
    (W : WeierstrassCurve K)
    (a : projectivePairSecondChartOverlapCoordinateRing W false) :
    projectiveInfinityPairDoubleSecantZOverlapToSecondOutputRing W
        (algebraMap (projectivePairSecondChartOverlapCoordinateRing W false)
          (projectivePairSecondOverlapAdditionOutputRing W false true) a) =
      projectiveInfinityPairDoubleSecantZOverlapSecondRingHom W a := by
  change (IsLocalization.Away.lift
      (S := Localization.Away
        (infinityPairToSecondChartOverlapAlgHom W false
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3))))
      (P := projectiveInfinityPairDoubleSecantZOverlapRing W)
      (g := projectiveInfinityPairDoubleSecantZOverlapSecondRingHom W)
      (infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)))
      (isUnit_iff_exists_inv.mpr
        (projectiveInfinityPairDoubleSecantZOverlap_secondDenominator_hasInverse W)))
        (algebraMap (projectivePairSecondChartOverlapCoordinateRing W false)
          (Localization.Away
            (infinityPairToSecondChartOverlapAlgHom W false
              (projectivePairChartAdditionCoordinates W (false, false)
                (2 : Fin 3)))) a) = _
  exact IsLocalization.Away.lift_eq
    (R := projectivePairSecondChartOverlapCoordinateRing W false)
    (S := Localization.Away
      (infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3))))
    (P := projectiveInfinityPairDoubleSecantZOverlapRing W)
    (g := projectiveInfinityPairDoubleSecantZOverlapSecondRingHom W)
    (infinityPairToSecondChartOverlapAlgHom W false
      (projectivePairChartAdditionCoordinates W (false, false) (2 : Fin 3)))
    (isUnit_iff_exists_inv.mpr
      (projectiveInfinityPairDoubleSecantZOverlap_secondDenominator_hasInverse W))
    a

/-- Map the exact double/secant intersection into the second-input/output
compatibility source. -/
noncomputable def
    projectiveInfinityPairDoubleSecantZOverlapToSecondOutput
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairDoubleSecantZOverlapRing W)) ⟶
      Spec (.of
        (projectivePairSecondOverlapAdditionOutputRing W false true)) :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairDoubleSecantZOverlapToSecondOutputRing W))

private theorem
    projectiveInfinityPairDoubleSecantZOverlapToSecondOutput_comp_open
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        projectivePairSecondOverlapAdditionOutputOpen W false true =
      projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        projectivePairDoubleOverlapToSecondInfinityOverlap W := by
  have hring :
      (projectiveInfinityPairDoubleSecantZOverlapToSecondOutputRing W).comp
          (algebraMap (projectivePairSecondChartOverlapCoordinateRing W false)
            (projectivePairSecondOverlapAdditionOutputRing W false true)) =
        (projectiveInfinityPairDoubleSecantZOverlapToDoubleRing W).comp
          (projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W).toRingHom := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectiveInfinityPairDoubleSecantZOverlapToSecondOutputRing_algebraMap,
      projectiveInfinityPairDoubleSecantZOverlapSecondRingHom]
  simp only [projectiveInfinityPairDoubleSecantZOverlapToSecondOutput,
    projectivePairSecondOverlapAdditionOutputOpen,
    projectiveInfinityPairDoubleSecantZOverlapToDouble,
    projectivePairDoubleOverlapToSecondInfinityOverlap]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

private theorem projectiveInfinityPairDoubleSecantZOverlap_mixed_open_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        projectivePairDoubleOverlapToFirstStandardOverlap W ≫
        projectivePairFirstOverlapToInfinityPair W true =
      projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
        projectivePairChartAdditionOutputOpen W (false, true) true := by
  calc
    _ = projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        (projectivePairDoubleOverlapToSecondInfinityOverlap W ≫
          projectivePairSecondOverlapToStandardPair W false) := by
            rw [projectivePairDoubleOverlapToFirstStandardOverlap_comp_mixed]
    _ = (projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
          projectivePairDoubleOverlapToSecondInfinityOverlap W) ≫
        projectivePairSecondOverlapToStandardPair W false :=
      (Category.assoc _ _ _).symm
    _ = (projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
          projectivePairSecondOverlapAdditionOutputOpen W false true) ≫
        projectivePairSecondOverlapToStandardPair W false := by
          rw [
            projectiveInfinityPairDoubleSecantZOverlapToSecondOutput_comp_open]
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        (projectivePairSecondOverlapAdditionOutputOpen W false true ≫
          projectivePairSecondOverlapToStandardPair W false) :=
      Category.assoc _ _ _
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        (projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
          projectivePairChartAdditionOutputOpen W
            (false, true) true) := by
              rw [
                projectivePairSecondOverlapAdditionOutput_standardOpen_eq]
    _ = _ := (Category.assoc _ _ _).symm

private theorem projectiveInfinityPairDoubleSecantZOverlap_standard_open_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        projectivePairDoubleOverlapToStandardPair W =
      projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        projectivePairDoubleOverlapToFirstStandardOverlap W ≫
        projectivePairFirstOverlapToStandardPair W true := by
  rw [projectivePairDoubleOverlapToFirstStandardOverlap_comp_standard]

private theorem projectiveInfinityPairDoubleSecantZOverlap_secant_map_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        projectivePairSecondOverlapAdditionOutputToInfinity W false true =
      projectiveInfinityPairDoubleSecantZOverlapToSecantZ W := by
  apply (cancel_mono
    (projectivePairChartAdditionOutputOpen W (false, false) true)).mp
  calc
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        (projectivePairSecondOverlapAdditionOutputToInfinity W false true ≫
          projectivePairChartAdditionOutputOpen W
            (false, false) true) := Category.assoc _ _ _
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        (projectivePairSecondOverlapAdditionOutputOpen W false true ≫
          projectivePairSecondOverlapToInfinityPair W false) := by
            rw [projectivePairSecondOverlapAdditionOutput_infinityOpen_eq]
    _ = (projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
          projectivePairSecondOverlapAdditionOutputOpen W false true) ≫
        projectivePairSecondOverlapToInfinityPair W false :=
      (Category.assoc _ _ _).symm
    _ = (projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
          projectivePairDoubleOverlapToSecondInfinityOverlap W) ≫
        projectivePairSecondOverlapToInfinityPair W false := by
          rw [
            projectiveInfinityPairDoubleSecantZOverlapToSecondOutput_comp_open]
    _ = projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        (projectivePairDoubleOverlapToSecondInfinityOverlap W ≫
          projectivePairSecondOverlapToInfinityPair W false) :=
      Category.assoc _ _ _
    _ = projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        projectivePairDoubleOverlapToInfinityPair W := by
          rw [
            projectivePairDoubleOverlapToSecondInfinityOverlap_comp_infinity]
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecantZ W ≫
        projectivePairChartAdditionOutputOpen W
          (false, false) true :=
      projectiveInfinityPairDoubleSecantZOverlap_open_eq W

/-- The transported standard-pair law and the infinity secant output-`Z`
law agree on their exact explicit overlap. -/
theorem projectiveInfinityPairDoubleSecantZOverlap_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        (projectivePairDoubleOverlapToStandardPair W ≫
          standardPairAdditionMorphism W) =
      projectiveInfinityPairDoubleSecantZOverlapToSecantZ W ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := by
  calc
    _ = (projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
          projectivePairDoubleOverlapToStandardPair W) ≫
        standardPairAdditionMorphism W :=
      (Category.assoc _ _ _).symm
    _ = (projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
          projectivePairDoubleOverlapToFirstStandardOverlap W ≫
          projectivePairFirstOverlapToStandardPair W true) ≫
        standardPairAdditionMorphism W := by
          exact congrArg
            (fun q => q ≫ standardPairAdditionMorphism W)
            (projectiveInfinityPairDoubleSecantZOverlap_standard_open_eq W)
    _ = projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        projectivePairDoubleOverlapToFirstStandardOverlap W ≫
        (projectivePairFirstOverlapToStandardPair W true ≫
          standardPairAdditionMorphism W) := by
            simp only [Category.assoc]
    _ = projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        projectivePairDoubleOverlapToFirstStandardOverlap W ≫
        (projectivePairFirstOverlapToInfinityPair W true ≫
          projectivePairInfinityStandardAdditionMorphism W) := by
            rw [
              projectivePairFirstOverlapToInfinityPair_comp_infinityStandardAddition]
    _ = (projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
          projectivePairDoubleOverlapToFirstStandardOverlap W ≫
          projectivePairFirstOverlapToInfinityPair W true) ≫
        projectivePairInfinityStandardAdditionMorphism W := by
          simp only [Category.assoc]
    _ = (projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
          projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
          projectivePairChartAdditionOutputOpen W
            (false, true) true) ≫
        projectivePairInfinityStandardAdditionMorphism W := by
          exact congrArg
            (fun q => q ≫ projectivePairInfinityStandardAdditionMorphism W)
            (projectiveInfinityPairDoubleSecantZOverlap_mixed_open_eq W)
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
        (projectivePairChartAdditionOutputOpen W (false, true) true ≫
          projectivePairInfinityStandardAdditionMorphism W) := by
            simp only [Category.assoc]
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
        projectivePairChartAdditionOutputMorphism W
          (false, true) true := by
            rw [projectivePairInfinityStandardSecantZOpen_comp_addition]
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        (projectivePairSecondOverlapAdditionOutputToStandard W false true ≫
          projectivePairChartAdditionOutputMorphism W
            (false, true) true) := rfl
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
        (projectivePairSecondOverlapAdditionOutputToInfinity W false true ≫
          projectivePairChartAdditionOutputMorphism W
            (false, false) true) := by
              rw [projectivePairSecondOverlapAdditionOutput_morphisms_eq]
    _ = (projectiveInfinityPairDoubleSecantZOverlapToSecondOutput W ≫
          projectivePairSecondOverlapAdditionOutputToInfinity W false true) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [projectiveInfinityPairDoubleSecantZOverlap_secant_map_eq]

/-- The transported standard and secant-`Z` laws agree on their categorical
cover pullback. -/
theorem projectiveInfinityPairDoubleSecantZ_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairDoubleOverlapToInfinityPair W)
          (projectivePairChartAdditionOutputOpen W (false, false) true) ≫
        (projectivePairDoubleOverlapToStandardPair W ≫
          standardPairAdditionMorphism W) =
      pullback.snd
          (projectivePairDoubleOverlapToInfinityPair W)
          (projectivePairChartAdditionOutputOpen W (false, false) true) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := by
  apply infinityPullback_morphism_compatible_symm
  let h := projectiveInfinityPairDoubleSecantZ_isPullback W
  let hcanonical := IsPullback.of_hasPullback
    (projectivePairChartAdditionOutputOpen W (false, false) true)
    (projectivePairDoubleOverlapToInfinityPair W)
  let e := h.isoIsPullback _ _ hcanonical
  apply (cancel_epi e.hom).mp
  calc
    _ = projectiveInfinityPairDoubleSecantZOverlapToSecantZ W ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := by
          rw [← Category.assoc, h.isoIsPullback_hom_fst _ _ hcanonical]
    _ = projectiveInfinityPairDoubleSecantZOverlapToDouble W ≫
        (projectivePairDoubleOverlapToStandardPair W ≫
          standardPairAdditionMorphism W) :=
      (projectiveInfinityPairDoubleSecantZOverlap_morphisms_eq W).symm
    _ = (e.hom ≫
          pullback.snd
            (projectivePairChartAdditionOutputOpen W (false, false) true)
            (projectivePairDoubleOverlapToInfinityPair W)) ≫
        (projectivePairDoubleOverlapToStandardPair W ≫
          standardPairAdditionMorphism W) := by
            exact congrArg
              (fun q => q ≫
                (projectivePairDoubleOverlapToStandardPair W ≫
                  standardPairAdditionMorphism W))
              (h.isoIsPullback_hom_snd _ _ hcanonical).symm
    _ = _ := Category.assoc _ _ _

/-! ## Density input for the remaining regular/double edge -/

private theorem secantTargetY_ne_zero_again
    (W : WeierstrassCurve K) :
    secantTargetY W ≠ 0 := by
  change AdjoinRoot.mk W.toAffine.polynomial Polynomial.X ≠ 0
  rw [AdjoinRoot.mk_X]
  simpa [WeierstrassCurve.Affine.CoordinateRing.YClass] using
    (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero
      (W' := W.toAffine) (0 : Polynomial K))

private theorem secantPairY₁_ne_zero_again
    (W : WeierstrassCurve K) :
    secantPairY₁ W ≠ 0 := by
  letI : (Ideal.span {W.toAffine.polynomial}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      W.toAffine.irreducible_polynomial.prime
  letI : IsDomain (secantTargetCoordinateRing W) := by infer_instance
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := secantTargetCoordinateRing W)
        (B := secantTargetCoordinateRing W)) :=
    Algebra.TensorProduct.includeLeft_injective
      (RingHom.injective
        (algebraMap K (secantTargetCoordinateRing W)))
  have hy :
      secantTargetY W ⊗ₜ[K] (1 : secantTargetCoordinateRing W) ≠ 0 := by
    simpa [Algebra.TensorProduct.includeLeft_apply] using
      hinj.ne (secantTargetY_ne_zero_again W)
  intro h
  apply hy
  calc
    _ = secantPairTensorEquiv W (secantPairY₁ W) :=
      (secantPairTensorEquiv_Y₁ W).symm
    _ = secantPairTensorEquiv W 0 := congrArg (secantPairTensorEquiv W) h
    _ = 0 := (secantPairTensorEquiv W).map_zero

private theorem secantPairY₂_ne_zero_again
    (W : WeierstrassCurve K) :
    secantPairY₂ W ≠ 0 := by
  letI : (Ideal.span {W.toAffine.polynomial}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      W.toAffine.irreducible_polynomial.prime
  letI : IsDomain (secantTargetCoordinateRing W) := by infer_instance
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := secantTargetCoordinateRing W)
        (B := secantTargetCoordinateRing W)) :=
    Algebra.TensorProduct.includeRight_injective
      (RingHom.injective
        (algebraMap K (secantTargetCoordinateRing W)))
  have hy :
      (1 : secantTargetCoordinateRing W) ⊗ₜ[K] secantTargetY W ≠ 0 := by
    intro h
    apply secantTargetY_ne_zero_again W
    apply hinj
    change (1 : secantTargetCoordinateRing W) ⊗ₜ[K] secantTargetY W =
      (1 : secantTargetCoordinateRing W) ⊗ₜ[K] 0
    simpa using h
  intro h
  apply hy
  calc
    _ = secantPairTensorEquiv W (secantPairY₂ W) :=
      (secantPairTensorEquiv_Y₂ W).symm
    _ = secantPairTensorEquiv W 0 := congrArg (secantPairTensorEquiv W) h
    _ = 0 := (secantPairTensorEquiv W).map_zero

private theorem projectiveStandardPair_inputYProduct_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartFirstUniversalPoint W (true, true) (1 : Fin 3) *
        projectivePairChartSecondUniversalPoint W (true, true) (1 : Fin 3) ≠
      0 := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  apply mul_ne_zero
  · rw [← standardPairCoordinateRingAlgEquiv_Y₁]
    exact (standardPairCoordinateRingAlgEquiv W).injective.ne
      (secantPairY₁_ne_zero_again W)
  · rw [← standardPairCoordinateRingAlgEquiv_Y₂]
    exact (standardPairCoordinateRingAlgEquiv W).injective.ne
      (secantPairY₂_ne_zero_again W)

private theorem standardPairToDoubleOverlapAlgHom_injective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Injective (standardPairToDoubleOverlapAlgHom W) := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  letI := (standardPairToDoubleOverlapAlgHom W).toAlgebra
  haveI := projectivePairDoubleOverlap_isLocalization_standardPair W
  change Function.Injective
    (algebraMap (projectivePairChartCoordinateRing W (true, true))
      (projectivePairDoubleChartOverlapCoordinateRing W))
  exact IsLocalization.injective
    (projectivePairDoubleChartOverlapCoordinateRing W)
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (projectiveStandardPair_inputYProduct_ne_zero W))

private noncomputable instance projectivePairDoubleOverlap_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nonempty (projectivePairDoubleChartOverlapScheme W) := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  letI : Nontrivial (projectivePairChartCoordinateRing W (true, true)) :=
    (projectivePairChartCoordinateRing_isDomain W
      (true, true)).toNontrivial
  letI : Nontrivial (projectivePairDoubleChartOverlapCoordinateRing W) :=
    (standardPairToDoubleOverlapAlgHom_injective W).nontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

private noncomputable instance projectiveInfinityPairOriginAddition_nonempty
    (W : WeierstrassCurve K) :
    Nonempty
      (Spec (.of
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W))) := by
  letI : Nontrivial
      (projectiveInfinityPairNeighborhoodAdditionOutputRing W) :=
    (projectiveInfinityPairOriginAdditionOriginAlgHom W).toRingHom.domain_nontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

private theorem projectivePairDoubleOverlap_rawZ_scaling
    (W : WeierstrassCurve K) :
    standardPairToDoubleOverlapAlgHom W
        (projectivePairChartAdditionCoordinates W (true, true)
          (2 : Fin 3)) =
      (firstStandardOverlapToDoubleOverlapAlgHom W
          (projectivePairFirstChartOverlapScale W true)) ^ 2 *
        ((projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W
            (projectivePairSecondChartOverlapScale W false)) ^ 2 *
          infinityPairToDoubleOverlapAlgHom W
            (projectivePairChartAdditionCoordinates W (false, false)
              (2 : Fin 3))) := by
  have hfirst := congrFun
    (projectivePairFirstOverlap_standardAddition_eq_smul_infinityAddition
      W true) (2 : Fin 3)
  change standardPairToFirstChartOverlapAlgHom W true
      (projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3)) =
    projectivePairFirstChartOverlapScale W true ^ 2 *
      infinityPairToFirstChartOverlapAlgHom W true
        (projectivePairChartAdditionCoordinates W (false, true)
          (2 : Fin 3)) at hfirst
  have hsecond := congrFun
    (projectivePairSecondOverlap_standardAddition_eq_smul_infinityAddition
      W false) (2 : Fin 3)
  change standardPairToSecondChartOverlapAlgHom W false
      (projectivePairChartAdditionCoordinates W (false, true) (2 : Fin 3)) =
    projectivePairSecondChartOverlapScale W false ^ 2 *
      infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)) at hsecond
  have hstandard := congrArg
    (fun f : projectivePairChartCoordinateRing W (true, true) →ₐ[K]
        projectivePairDoubleChartOverlapCoordinateRing W =>
      f (projectivePairChartAdditionCoordinates W (true, true)
        (2 : Fin 3)))
    (projectivePairDoubleOverlap_standard_factor W)
  change firstStandardOverlapToDoubleOverlapAlgHom W
      (standardPairToFirstChartOverlapAlgHom W true
        (projectivePairChartAdditionCoordinates W (true, true)
          (2 : Fin 3))) =
    standardPairToDoubleOverlapAlgHom W
      (projectivePairChartAdditionCoordinates W (true, true)
        (2 : Fin 3)) at hstandard
  have hmixed := congrArg
    (fun f : projectivePairChartCoordinateRing W (false, true) →ₐ[K]
        projectivePairDoubleChartOverlapCoordinateRing W =>
      f (projectivePairChartAdditionCoordinates W (false, true)
        (2 : Fin 3)))
    (projectivePairDoubleOverlap_mixed_factors_eq W)
  change firstStandardOverlapToDoubleOverlapAlgHom W
      (infinityPairToFirstChartOverlapAlgHom W true
        (projectivePairChartAdditionCoordinates W (false, true)
          (2 : Fin 3))) =
    projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W
      (standardPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, true)
          (2 : Fin 3))) at hmixed
  have hinfinity := congrArg
    (fun f : projectiveInfinityPairCoordinateRing W →ₐ[K]
        projectivePairDoubleChartOverlapCoordinateRing W =>
      f (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)))
    (projectivePairDoubleOverlap_infinity_factor W)
  change projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W
      (infinityPairToSecondChartOverlapAlgHom W false
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3))) =
    infinityPairToDoubleOverlapAlgHom W
      (projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3)) at hinfinity
  calc
    _ = firstStandardOverlapToDoubleOverlapAlgHom W
        (standardPairToFirstChartOverlapAlgHom W true
          (projectivePairChartAdditionCoordinates W (true, true)
            (2 : Fin 3))) := hstandard.symm
    _ = firstStandardOverlapToDoubleOverlapAlgHom W
        (projectivePairFirstChartOverlapScale W true ^ 2 *
          infinityPairToFirstChartOverlapAlgHom W true
            (projectivePairChartAdditionCoordinates W (false, true)
              (2 : Fin 3))) := by
                exact congrArg
                  (firstStandardOverlapToDoubleOverlapAlgHom W) hfirst
    _ = (firstStandardOverlapToDoubleOverlapAlgHom W
          (projectivePairFirstChartOverlapScale W true)) ^ 2 *
        firstStandardOverlapToDoubleOverlapAlgHom W
          (infinityPairToFirstChartOverlapAlgHom W true
            (projectivePairChartAdditionCoordinates W (false, true)
              (2 : Fin 3))) := by rw [map_mul, map_pow]
    _ = (firstStandardOverlapToDoubleOverlapAlgHom W
          (projectivePairFirstChartOverlapScale W true)) ^ 2 *
        projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W
          (standardPairToSecondChartOverlapAlgHom W false
            (projectivePairChartAdditionCoordinates W (false, true)
              (2 : Fin 3))) := by rw [hmixed]
    _ = (firstStandardOverlapToDoubleOverlapAlgHom W
          (projectivePairFirstChartOverlapScale W true)) ^ 2 *
        projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W
          (projectivePairSecondChartOverlapScale W false ^ 2 *
            infinityPairToSecondChartOverlapAlgHom W false
              (projectivePairChartAdditionCoordinates W (false, false)
                (2 : Fin 3))) := by
                  rw [hsecond]
    _ = (firstStandardOverlapToDoubleOverlapAlgHom W
          (projectivePairFirstChartOverlapScale W true)) ^ 2 *
        ((projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W
            (projectivePairSecondChartOverlapScale W false)) ^ 2 *
          projectivePairSecondInfinityOverlapToDoubleOverlapAlgHom W
            (infinityPairToSecondChartOverlapAlgHom W false
              (projectivePairChartAdditionCoordinates W (false, false)
                (2 : Fin 3)))) := by rw [map_mul, map_pow]
    _ = _ := by rw [hinfinity]

/-- The infinity-pair raw secant output `Z` is a genuine nonzero function. -/
theorem projectiveInfinityPairRawOutputZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionCoordinates W (false, false)
        (2 : Fin 3) ≠ 0 := by
  have hstandard :
      standardPairToDoubleOverlapAlgHom W
          (projectivePairChartAdditionCoordinates W (true, true)
            (2 : Fin 3)) ≠ 0 :=
    (standardPairToDoubleOverlapAlgHom_injective W).ne
      (standardPairRawOutputZ_ne_zero W)
  intro h
  apply hstandard
  rw [projectivePairDoubleOverlap_rawZ_scaling W, h, map_zero,
    mul_zero, mul_zero]

private noncomputable instance projectiveInfinityPairSecantZ_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Nonempty
      (Spec (.of
        (projectivePairChartAdditionOutputRing W (false, false) true))) := by
  letI : IsDomain (projectiveInfinityPairCoordinateRing W) :=
    projectivePairChartCoordinateRing_isDomain W (false, false)
  letI : Nontrivial (projectiveInfinityPairCoordinateRing W) :=
    (projectivePairChartCoordinateRing_isDomain W
      (false, false)).toNontrivial
  have hinj : Function.Injective
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (Localization.Away
          (projectivePairChartAdditionCoordinates W (false, false)
            (2 : Fin 3)))) :=
    IsLocalization.injective
      (Localization.Away
        (projectivePairChartAdditionCoordinates W (false, false)
          (2 : Fin 3)))
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (projectiveInfinityPairRawOutputZ_ne_zero W))
  letI : Nontrivial
      (projectivePairChartAdditionOutputRing W (false, false) true) :=
    hinj.nontrivial
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

/-! ## The dense triple overlap -/

/-- The categorical intersection of the double-standard and regular-origin
members of the infinity addition cover. -/
abbrev projectiveInfinityPairDoubleOriginOverlap
    (W : WeierstrassCurve K) :=
  pullback
    (projectivePairDoubleOverlapToInfinityPair W)
    (projectiveInfinityPairOriginAdditionOpen W)

/-- The double/regular intersection as an open subscheme of the infinity
pair chart. -/
noncomputable def projectiveInfinityPairDoubleOriginOverlapOpen
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDoubleOriginOverlap W ⟶
      projectivePairChartScheme W (false, false) :=
  pullback.fst
      (projectivePairDoubleOverlapToInfinityPair W)
      (projectiveInfinityPairOriginAdditionOpen W) ≫
    projectivePairDoubleOverlapToInfinityPair W

instance projectiveInfinityPairDoubleOriginOverlapOpen_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectiveInfinityPairDoubleOriginOverlapOpen W) := by
  dsimp only [projectiveInfinityPairDoubleOriginOverlapOpen]
  infer_instance

/-- The triple intersection obtained by further pulling back the secant
output-`Z` member. -/
abbrev projectiveInfinityPairDoubleOriginSecantZOverlap
    (W : WeierstrassCurve K) :=
  pullback
    (projectiveInfinityPairDoubleOriginOverlapOpen W)
    (projectivePairChartAdditionOutputOpen W (false, false) true)

/-- Projection from the triple intersection to the double/regular
intersection. -/
noncomputable def projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin
    (W : WeierstrassCurve K) :
    projectiveInfinityPairDoubleOriginSecantZOverlap W ⟶
      projectiveInfinityPairDoubleOriginOverlap W :=
  pullback.fst
    (projectiveInfinityPairDoubleOriginOverlapOpen W)
    (projectivePairChartAdditionOutputOpen W (false, false) true)

instance
    projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W) := by
  dsimp only [projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin]
  infer_instance

private noncomputable instance projectiveInfinityPairChart_isIntegral
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsIntegral (projectivePairChartScheme W (false, false)) := by
  letI : IsDomain (projectiveInfinityPairCoordinateRing W) :=
    projectivePairChartCoordinateRing_isDomain W (false, false)
  letI : IsIntegral
      (Spec (.of (projectiveInfinityPairCoordinateRing W))) :=
    (affine_isIntegral_iff
      (.of (projectiveInfinityPairCoordinateRing W))).mpr inferInstance
  exact IsIntegral.of_isIso
    (projectivePairChartIsoSpecTensor W (false, false)).inv

private noncomputable instance projectiveInfinityPairChart_irreducible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IrreducibleSpace (projectivePairChartScheme W (false, false)) := by
  letI : IsDomain (projectiveInfinityPairCoordinateRing W) :=
    projectivePairChartCoordinateRing_isDomain W (false, false)
  have hspec : IrreducibleSpace
      (Spec (.of (projectiveInfinityPairCoordinateRing W))) := by
    infer_instance
  exact
    (projectivePairChartIsoSpecTensor W
      (false, false)).hom.homeomorph.irreducibleSpace_iff.mpr hspec

private noncomputable instance projectiveInfinityPairDoubleOrigin_isIntegral
    (W : WeierstrassCurve K) [W.IsElliptic]
    [Nonempty (projectiveInfinityPairDoubleOriginOverlap W)] :
    IsIntegral (projectiveInfinityPairDoubleOriginOverlap W) :=
  isIntegral_of_isOpenImmersion
    (projectiveInfinityPairDoubleOriginOverlapOpen W)

private noncomputable instance
    projectiveInfinityPairDoubleOriginSecantZ_nonempty
    (W : WeierstrassCurve K) [W.IsElliptic]
    [Nonempty (projectiveInfinityPairDoubleOriginOverlap W)] :
    Nonempty (projectiveInfinityPairDoubleOriginSecantZOverlap W) := by
  have hinter :
      (Set.range (projectiveInfinityPairDoubleOriginOverlapOpen W) ∩
        Set.range (projectivePairChartAdditionOutputOpen W
          (false, false) true)).Nonempty :=
    nonempty_preirreducible_inter
      (projectiveInfinityPairDoubleOriginOverlapOpen W).isOpenEmbedding.isOpen_range
      (projectivePairChartAdditionOutputOpen W
        (false, false) true).isOpenEmbedding.isOpen_range
      (Set.range_nonempty
        (projectiveInfinityPairDoubleOriginOverlapOpen W))
      (Set.range_nonempty
        (projectivePairChartAdditionOutputOpen W (false, false) true))
  rw [← IsOpenImmersion.range_pullback_to_base_of_left] at hinter
  rcases hinter with ⟨_, y, _⟩
  exact ⟨y⟩

private noncomputable instance
    projectiveInfinityPairDoubleOriginSecantZ_isDominant
    (W : WeierstrassCurve K) [W.IsElliptic]
    [Nonempty (projectiveInfinityPairDoubleOriginOverlap W)] :
    IsDominant
      (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W) := by
  constructor
  have hopen :=
    (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W).isOpenEmbedding.isOpenMap
  exact hopen.denseRange_of_isPreirreducibleSpace _

private theorem
    projectiveInfinityPairDoubleOriginSecantZ_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W ≫
          pullback.fst
            (projectivePairDoubleOverlapToInfinityPair W)
            (projectiveInfinityPairOriginAdditionOpen W)) ≫
        (projectivePairDoubleOverlapToStandardPair W ≫
          standardPairAdditionMorphism W) =
      (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W ≫
          pullback.snd
            (projectivePairDoubleOverlapToInfinityPair W)
            (projectiveInfinityPairOriginAdditionOpen W)) ≫
        projectiveInfinityPairOriginAdditionMorphism W := by
  let toDoubleSecant :
      projectiveInfinityPairDoubleOriginSecantZOverlap W ⟶
        pullback
          (projectivePairDoubleOverlapToInfinityPair W)
          (projectivePairChartAdditionOutputOpen W
            (false, false) true) :=
    pullback.lift
      (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W ≫
        pullback.fst
          (projectivePairDoubleOverlapToInfinityPair W)
          (projectiveInfinityPairOriginAdditionOpen W))
      (pullback.snd
        (projectiveInfinityPairDoubleOriginOverlapOpen W)
        (projectivePairChartAdditionOutputOpen W (false, false) true))
      (by
        rw [Category.assoc]
        change
          pullback.fst
                (projectiveInfinityPairDoubleOriginOverlapOpen W)
                (projectivePairChartAdditionOutputOpen W
                  (false, false) true) ≫
              projectiveInfinityPairDoubleOriginOverlapOpen W =
            pullback.snd
                (projectiveInfinityPairDoubleOriginOverlapOpen W)
                (projectivePairChartAdditionOutputOpen W
                  (false, false) true) ≫
              projectivePairChartAdditionOutputOpen W
                (false, false) true
        exact pullback.condition)
  let toOriginSecant :
      projectiveInfinityPairDoubleOriginSecantZOverlap W ⟶
        pullback
          (projectiveInfinityPairOriginAdditionOpen W)
          (projectivePairChartAdditionOutputOpen W
            (false, false) true) :=
    pullback.lift
      (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W ≫
        pullback.snd
          (projectivePairDoubleOverlapToInfinityPair W)
          (projectiveInfinityPairOriginAdditionOpen W))
      (pullback.snd
        (projectiveInfinityPairDoubleOriginOverlapOpen W)
        (projectivePairChartAdditionOutputOpen W (false, false) true))
      (by
        rw [Category.assoc,
          ← pullback.condition
            (f := projectivePairDoubleOverlapToInfinityPair W)
            (g := projectiveInfinityPairOriginAdditionOpen W)]
        change
          pullback.fst
                (projectiveInfinityPairDoubleOriginOverlapOpen W)
                (projectivePairChartAdditionOutputOpen W
                  (false, false) true) ≫
              projectiveInfinityPairDoubleOriginOverlapOpen W =
            pullback.snd
                (projectiveInfinityPairDoubleOriginOverlapOpen W)
                (projectivePairChartAdditionOutputOpen W
                  (false, false) true) ≫
              projectivePairChartAdditionOutputOpen W
                (false, false) true
        exact pullback.condition)
  calc
    _ = toDoubleSecant ≫
        (pullback.fst
            (projectivePairDoubleOverlapToInfinityPair W)
            (projectivePairChartAdditionOutputOpen W
              (false, false) true) ≫
          (projectivePairDoubleOverlapToStandardPair W ≫
            standardPairAdditionMorphism W)) := by
              simp only [toDoubleSecant, pullback.lift_fst_assoc]
    _ = toDoubleSecant ≫
        (pullback.snd
            (projectivePairDoubleOverlapToInfinityPair W)
            (projectivePairChartAdditionOutputOpen W
              (false, false) true) ≫
          projectivePairChartAdditionOutputMorphism W
            (false, false) true) := by
              rw [projectiveInfinityPairDoubleSecantZ_compatible]
    _ = pullback.snd
          (projectiveInfinityPairDoubleOriginOverlapOpen W)
          (projectivePairChartAdditionOutputOpen W (false, false) true) ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) true := by
            simp only [toDoubleSecant, pullback.lift_snd_assoc]
    _ = toOriginSecant ≫
        (pullback.snd
            (projectiveInfinityPairOriginAdditionOpen W)
            (projectivePairChartAdditionOutputOpen W
              (false, false) true) ≫
          projectivePairChartAdditionOutputMorphism W
            (false, false) true) := by
              simp only [toOriginSecant, pullback.lift_snd_assoc]
    _ = toOriginSecant ≫
        (pullback.fst
            (projectiveInfinityPairOriginAdditionOpen W)
            (projectivePairChartAdditionOutputOpen W
              (false, false) true) ≫
          projectiveInfinityPairOriginAdditionMorphism W) := by
              rw [projectiveInfinityPairOriginSecantZ_compatible]
    _ = _ := by
      simp only [toOriginSecant, pullback.lift_fst_assoc]

/-- The transported standard-pair law and the regular origin-neighborhood
law agree on their categorical cover pullback. -/
theorem projectiveInfinityPairDoubleOrigin_compatible
    (W : WeierstrassCurve K) [W.IsElliptic] :
    pullback.fst
          (projectivePairDoubleOverlapToInfinityPair W)
          (projectiveInfinityPairOriginAdditionOpen W) ≫
        (projectivePairDoubleOverlapToStandardPair W ≫
          standardPairAdditionMorphism W) =
      pullback.snd
          (projectivePairDoubleOverlapToInfinityPair W)
          (projectiveInfinityPairOriginAdditionOpen W) ≫
        projectiveInfinityPairOriginAdditionMorphism W := by
  classical
  cases isEmpty_or_nonempty
      (projectiveInfinityPairDoubleOriginOverlap W) with
  | inl hempty =>
      letI := hempty
      exact (isInitialOfIsEmpty
        (X := projectiveInfinityPairDoubleOriginOverlap W)).hom_ext _ _
  | inr hnonempty =>
      letI := hnonempty
      have htriple :=
        projectiveInfinityPairDoubleOriginSecantZ_morphisms_eq W
      have hbase :
          (pullback.fst
                (projectivePairDoubleOverlapToInfinityPair W)
                (projectiveInfinityPairOriginAdditionOpen W) ≫
              (projectivePairDoubleOverlapToStandardPair W ≫
                standardPairAdditionMorphism W)) ≫
              structureMap W =
            (pullback.snd
                (projectivePairDoubleOverlapToInfinityPair W)
                (projectiveInfinityPairOriginAdditionOpen W) ≫
              projectiveInfinityPairOriginAdditionMorphism W) ≫
              structureMap W := by
        apply ext_of_isDominant
          (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W)
        simpa only [Category.assoc] using
          congrArg (fun q => q ≫ structureMap W) htriple
      apply ext_of_isDominant_of_isSeparated
        (structureMap W) hbase
        (projectiveInfinityPairDoubleOriginSecantZToDoubleOrigin W)
      simpa only [Category.assoc] using htriple

/-! ## Compatibility family and gluing -/

/-- The three indexed local laws satisfy the open-cover compatibility
condition on every ordered pair of members. -/
theorem projectiveInfinityPairAdditionCoverMorphism_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : ProjectiveInfinityPairAdditionCoverIndex) :
    pullback.fst
          (projectiveInfinityPairAdditionCoverMap W i)
          (projectiveInfinityPairAdditionCoverMap W j) ≫
        projectiveInfinityPairAdditionCoverMorphism W i =
      pullback.snd
          (projectiveInfinityPairAdditionCoverMap W i)
          (projectiveInfinityPairAdditionCoverMap W j) ≫
        projectiveInfinityPairAdditionCoverMorphism W j := by
  cases i <;> cases j
  · exact infinityPullback_morphism_compatible_self _ _
  · exact projectiveInfinityPairDoubleOrigin_compatible W
  · exact projectiveInfinityPairDoubleSecantZ_compatible W
  · exact infinityPullback_morphism_compatible_symm _ _ _ _
      (projectiveInfinityPairDoubleOrigin_compatible W)
  · exact infinityPullback_morphism_compatible_self _ _
  · exact projectiveInfinityPairOriginSecantZ_compatible W
  · exact infinityPullback_morphism_compatible_symm _ _ _ _
      (projectiveInfinityPairDoubleSecantZ_compatible W)
  · exact infinityPullback_morphism_compatible_symm _ _ _ _
      (projectiveInfinityPairOriginSecantZ_compatible W)
  · exact infinityPullback_morphism_compatible_self _ _

private theorem projectiveInfinityPairAdditionOpenCover_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : (projectiveInfinityPairAdditionOpenCover W).I₀) :
    pullback.fst
          ((projectiveInfinityPairAdditionOpenCover W).f i)
          ((projectiveInfinityPairAdditionOpenCover W).f j) ≫
        projectiveInfinityPairAdditionCoverMorphism W i =
      pullback.snd
          ((projectiveInfinityPairAdditionOpenCover W).f i)
          ((projectiveInfinityPairAdditionOpenCover W).f j) ≫
        projectiveInfinityPairAdditionCoverMorphism W j := by
  exact projectiveInfinityPairAdditionCoverMorphism_compatible W i j

/-- The actual addition morphism on the entire infinity-by-infinity pair
chart. -/
noncomputable def projectiveInfinityPairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartScheme W (false, false) ⟶ scheme W :=
  (projectiveInfinityPairAdditionOpenCover W).glueMorphisms
    (projectiveInfinityPairAdditionCoverMorphism W)
    (projectiveInfinityPairAdditionOpenCover_compatible W)

/-- The glued infinity-pair law restricts to the transported standard-pair
law on the double input overlap. -/
@[reassoc]
theorem projectivePairDoubleOverlapToInfinityPair_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairDoubleOverlapToInfinityPair W ≫
        projectiveInfinityPairAdditionMorphism W =
      projectivePairDoubleOverlapToStandardPair W ≫
        standardPairAdditionMorphism W := by
  exact (projectiveInfinityPairAdditionOpenCover W).ι_glueMorphisms
    (projectiveInfinityPairAdditionCoverMorphism W)
    (projectiveInfinityPairAdditionOpenCover_compatible W)
    .doubleStandard

/-- The glued infinity-pair law restricts to the regular formula on the
genuine origin-neighborhood source. -/
@[reassoc]
theorem projectiveInfinityPairOriginAdditionOpen_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveInfinityPairOriginAdditionOpen W ≫
        projectiveInfinityPairAdditionMorphism W =
      projectiveInfinityPairOriginAdditionMorphism W := by
  exact (projectiveInfinityPairAdditionOpenCover W).ι_glueMorphisms
    (projectiveInfinityPairAdditionCoverMorphism W)
    (projectiveInfinityPairAdditionOpenCover_compatible W)
    .originNeighborhood

/-- The glued infinity-pair law restricts to the normalized secant formula
on the output-`Z` member. -/
@[reassoc]
theorem projectiveInfinityPairSecantZOpen_comp_addition
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionOutputOpen W (false, false) true ≫
        projectiveInfinityPairAdditionMorphism W =
      projectivePairChartAdditionOutputMorphism W
        (false, false) true := by
  exact (projectiveInfinityPairAdditionOpenCover W).ι_glueMorphisms
    (projectiveInfinityPairAdditionCoverMorphism W)
    (projectiveInfinityPairAdditionOpenCover_compatible W)
    .secantZ

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
