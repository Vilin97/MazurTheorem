/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassStandardPairCoordinates
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductOutputCompatibility

/-!
# Compatibility of standard-pair addition formulas

On the standard-by-standard projective-pair chart, the raw homogeneous
addition triple has `Z`-coordinate `(x₁ - x₂) ^ 3`.  This file proves the
stronger coordinate identity: after passing to the secant chart, the entire
raw triple is that cube times the checked affine secant output.

The design boundary is the canonical morphism from the raw output-`Z`
localization to the secant chart.  Its source factorization and formula
compatibility are consumed by the final theorem, which identifies the raw
localized morphism with the restriction of `standardPairAdditionMorphism`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private def standardPairOutputZBaseRingHom (W : WeierstrassCurve K) :
    secantPairCoordinateRing W →+*
      projectivePairChartAdditionOutputRing W (true, true) true :=
  (algebraMap
    (projectivePairChartCoordinateRing W (true, true))
    (projectivePairChartAdditionOutputRing W (true, true) true)).comp
      (standardPairCoordinateRingAlgEquiv W).toRingHom

private theorem standardPairOutputZBaseRingHom_denominator_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (standardPairOutputZBaseRingHom W (secantDenominator W)) := by
  apply isUnit_of_dvd_unit (dvd_pow_self _ (by norm_num : (3 : ℕ) ≠ 0))
  have hraw : IsUnit
      (algebraMap
        (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) true)
        (projectivePairChartAdditionCoordinates W (true, true)
          (coveringCoordinate true))) :=
    IsLocalization.Away.algebraMap_isUnit _
  change IsUnit
    ((algebraMap
      (projectivePairChartCoordinateRing W (true, true))
      (projectivePairChartAdditionOutputRing W (true, true) true)
      (standardPairCoordinateRingAlgEquiv W (secantDenominator W))) ^ 3)
  rw [← map_pow, ← projectivePairChartAdditionCoordinates_standard_Z]
  change IsUnit
    (algebraMap
      (projectivePairChartCoordinateRing W (true, true))
      (projectivePairChartAdditionOutputRing W (true, true) true)
      (projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3))) at hraw
  exact hraw

/-- The coordinate-ring map from the secant chart to the standard-pair raw
output-`Z` localization. -/
noncomputable def standardPairOutputZToSecantRing (W : WeierstrassCurve K) :
    secantChartCoordinateRing W →+*
      projectivePairChartAdditionOutputRing W (true, true) true :=
  IsLocalization.Away.lift (secantDenominator W)
    (standardPairOutputZBaseRingHom_denominator_isUnit W)

/-- The standard-pair output map extends the coordinate equivalence on the
unlocalized affine-pair ring. -/
@[simp]
theorem standardPairOutputZToSecantRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    standardPairOutputZToSecantRing W
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W) a) =
      standardPairOutputZBaseRingHom W a := by
  exact IsLocalization.Away.lift_eq
    (x := secantDenominator W)
    (g := standardPairOutputZBaseRingHom W)
    (standardPairOutputZBaseRingHom_denominator_isUnit W) a

/-- The canonical map from the standard-pair raw output-`Z` localization to
the checked secant chart. -/
noncomputable def standardPairOutputZToSecant (W : WeierstrassCurve K) :
    Spec (.of (projectivePairChartAdditionOutputRing W (true, true) true)) ⟶
      Spec (.of (secantChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (standardPairOutputZToSecantRing W))

/-- The canonical output-to-secant map has the same map to the affine-pair
presentation as the raw output open. -/
@[reassoc]
theorem standardPairOutputZToSecant_comp_secantChartToPair
    (W : WeierstrassCurve K) :
    standardPairOutputZToSecant W ≫ secantChartToPair W =
      projectivePairChartAdditionOutputOpen W (true, true) true ≫
        (standardPairIsoAffinePair W).hom := by
  rw [←
    projectivePairChartIsoSpecTensor_hom_comp_standardPairCoordinateRingAlgEquiv_specMap]
  rw [projectivePairChartAdditionOutputOpen_comp_iso_hom_assoc]
  rw [standardPairOutputZToSecant, secantChartToPair,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  change (standardPairOutputZToSecantRing W).comp
      (algebraMap (secantPairCoordinateRing W)
        (secantChartCoordinateRing W)) =
    standardPairOutputZBaseRingHom W
  exact IsLocalization.Away.lift_comp
    (x := secantDenominator W)
    (g := standardPairOutputZBaseRingHom W)
    (standardPairOutputZBaseRingHom_denominator_isUnit W)

private theorem affineChart_secantCoordinates_eq_smul
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (x₁ x₂ y₁ y₂ ℓ : R)
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂) :
    W.toProjective.addXYZ ![x₁, y₁, 1] ![x₂, y₂, 1] =
      (x₁ - x₂) ^ 3 •
        ![W.toAffine.addX x₁ x₂ ℓ,
          W.toAffine.addY x₁ x₂ y₁ ℓ, 1] := by
  let P : Fin 3 → R := ![x₁, y₁, 1]
  let Q : Fin 3 → R := ![x₂, y₂, 1]
  have hP : W.toProjective.Equation P := by
    exact (W.toProjective.equation_some x₁ y₁).mpr h₁
  have hQ : W.toProjective.Equation Q := by
    exact (W.toProjective.equation_some x₂ y₂).mpr h₂
  have hZ := W.toProjective.addZ_eq' hP hQ
  have hX := W.toProjective.addX_eq' hP hQ
  have hNegY := W.toProjective.negAddY_eq' hP hQ
  have hZ' : W.toProjective.addZ P Q = (x₁ - x₂) ^ 3 := by
    simpa [P, Q] using hZ
  have hX' : W.toProjective.addX P Q =
      (x₁ - x₂) ^ 3 * W.toAffine.addX x₁ x₂ ℓ := by
    have hX₀ : W.toProjective.addX P Q =
        ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
          W.a₂ * (x₁ - x₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2 -
          x₂ * (x₁ - x₂) ^ 2) * (x₁ - x₂) := by
      simpa [P, Q] using hX
    rw [hX₀, ← hℓ]
    simp only [WeierstrassCurve.Affine.addX]
    ring
  have hNegY' : W.toProjective.negAddY P Q =
      (x₁ - x₂) ^ 3 * W.toAffine.negAddY x₁ x₂ y₁ ℓ := by
    have hNegY₀ : W.toProjective.negAddY P Q =
        (y₁ - y₂) *
            ((y₁ - y₂) ^ 2 + W.a₁ * (y₁ - y₂) * (x₁ - x₂) -
              W.a₂ * (x₁ - x₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2 -
              x₂ * (x₁ - x₂) ^ 2 - x₁ * (x₁ - x₂) ^ 2) +
          y₁ * (x₁ - x₂) ^ 3 := by
      simpa [P, Q] using hNegY
    rw [hNegY₀, ← hℓ]
    simp only [WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX]
    ring
  change W.toProjective.addXYZ P Q =
    (x₁ - x₂) ^ 3 •
      ![W.toAffine.addX x₁ x₂ ℓ,
        W.toAffine.addY x₁ x₂ y₁ ℓ, 1]
  funext j
  fin_cases j
  · simpa [P, Q, WeierstrassCurve.Projective.addXYZ,
      Pi.smul_apply, smul_eq_mul] using hX'
  · change W.toProjective.addY P Q =
      (x₁ - x₂) ^ 3 * W.toAffine.addY x₁ x₂ y₁ ℓ
    rw [WeierstrassCurve.Projective.addY,
      WeierstrassCurve.Projective.negY_eq, hNegY', hX', hZ']
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  · simpa [P, Q, WeierstrassCurve.Projective.addXYZ,
      Pi.smul_apply, smul_eq_mul] using hZ'

private theorem secantChart_addXYZ_eq_smul
    (W : WeierstrassCurve K) :
    let W' := W.map (secantCoefficientHom W)
    W'.toProjective.addXYZ
        ![secantChartX₁ W, secantChartY₁ W, 1]
        ![secantChartX₂ W, secantChartY₂ W, 1] =
      (secantChartX₁ W - secantChartX₂ W) ^ 3 •
        ![secantChartAddX W, secantChartAddY W, 1] := by
  dsimp only
  apply affineChart_secantCoordinates_eq_smul
  · have h := (secantPair_equation_left W).map
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W))
    change ((W.map (secantPairCoefficientHom W)).map
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W))).toAffine.Equation _ _ at h
    rw [WeierstrassCurve.map_map] at h
    rw [secantChartX₁_eq_algebraMap_pairX₁,
      secantChartY₁_eq_algebraMap_pairY₁]
    simpa [secantCoefficientHom, secantPairCoefficientHom] using h
  · have h := (secantPair_equation_right W).map
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W))
    change ((W.map (secantPairCoefficientHom W)).map
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W))).toAffine.Equation _ _ at h
    rw [WeierstrassCurve.map_map] at h
    rw [secantChartX₂_eq_algebraMap_pairX₂,
      secantChartY₂_eq_algebraMap_pairY₂]
    simpa [secantCoefficientHom, secantPairCoefficientHom] using h
  · exact secantChartSlope_mul_sub W

private theorem standardPairOutputZToSecantRing_rawAdditionCoordinate
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardPairOutputZToSecantRing W
        ((W.map (secantCoefficientHom W)).toProjective.addXYZ
          ![secantChartX₁ W, secantChartY₁ W, 1]
          ![secantChartX₂ W, secantChartY₂ W, 1] j) =
      algebraMap (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) true)
        (projectivePairChartAdditionCoordinates W (true, true) j) := by
  let S := secantPairCoordinateRing W
  let U := secantChartCoordinateRing W
  let f : S →+* U := algebraMap S U
  have hf : f.comp (algebraMap K S) = secantCoefficientHom W := by
    rw [secantCoefficientHom_eq_algebraMap]
    exact (IsScalarTower.algebraMap_eq K S U).symm
  have hP : f ∘ affinePairFirstProjectivePoint W =
      ![secantChartX₁ W, secantChartY₁ W, 1] := by
    funext k
    fin_cases k
    · exact (secantChartX₁_eq_algebraMap_pairX₁ W).symm
    · exact (secantChartY₁_eq_algebraMap_pairY₁ W).symm
    · simp [affinePairFirstProjectivePoint]
  have hQ : f ∘ affinePairSecondProjectivePoint W =
      ![secantChartX₂ W, secantChartY₂ W, 1] := by
    funext k
    fin_cases k
    · exact (secantChartX₂_eq_algebraMap_pairX₂ W).symm
    · exact (secantChartY₂_eq_algebraMap_pairY₂ W).symm
    · simp [affinePairSecondProjectivePoint]
  have hmap := congrFun (WeierstrassCurve.Projective.map_addXYZ
    (W' := (W.map (algebraMap K S)).toProjective) f
    (affinePairFirstProjectivePoint W)
    (affinePairSecondProjectivePoint W)) j
  change (((W.map (algebraMap K S)).map f).toProjective.addXYZ
      (f ∘ affinePairFirstProjectivePoint W)
      (f ∘ affinePairSecondProjectivePoint W)) j = _ at hmap
  rw [WeierstrassCurve.map_map, hf, hP, hQ] at hmap
  rw [hmap]
  change standardPairOutputZToSecantRing W
      (algebraMap S U
        ((W.map (algebraMap K S)).toProjective.addXYZ
          (affinePairFirstProjectivePoint W)
          (affinePairSecondProjectivePoint W) j)) = _
  rw [standardPairOutputZToSecantRing_algebraMap]
  change algebraMap (projectivePairChartCoordinateRing W (true, true))
      (projectivePairChartAdditionOutputRing W (true, true) true)
      (standardPairCoordinateRingAlgEquiv W
        ((W.map (algebraMap K S)).toProjective.addXYZ
          (affinePairFirstProjectivePoint W)
          (affinePairSecondProjectivePoint W) j)) = _
  have hstandard := congrFun
    (standardPairCoordinateRingAlgEquiv_additionCoordinates W) j
  change standardPairCoordinateRingAlgEquiv W
      ((W.map (algebraMap K S)).toProjective.addXYZ
        (affinePairFirstProjectivePoint W)
        (affinePairSecondProjectivePoint W) j) =
    projectivePairChartAdditionCoordinates W (true, true) j at hstandard
  rw [hstandard]

private theorem standardPairOutputZ_rawCoordinate_eq_denominatorCube_mul
    (W : WeierstrassCurve K) (j : Fin 3) :
    algebraMap (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) true)
        (projectivePairChartAdditionCoordinates W (true, true) j) =
      (standardPairOutputZToSecantRing W
          (secantChartX₁ W - secantChartX₂ W)) ^ 3 *
        standardPairOutputZToSecantRing W
          (![secantChartAddX W, secantChartAddY W, 1] j) := by
  have hraw := congrFun (secantChart_addXYZ_eq_smul W) j
  have h := congrArg (standardPairOutputZToSecantRing W) hraw
  rw [standardPairOutputZToSecantRing_rawAdditionCoordinate] at h
  simpa only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow] using h

private theorem standardPairOutputZPoint_eq_secantPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    projectivePairChartAdditionOutputPoint W (true, true) true j =
      standardPairOutputZToSecantRing W
        (![secantChartAddX W, secantChartAddY W, 1] j) := by
  let T := projectivePairChartAdditionOutputRing W (true, true) true
  let u : Tˣ := projectivePairChartAdditionOutputUnit W (true, true) true
  let d : T := standardPairOutputZToSecantRing W
    (secantChartX₁ W - secantChartX₂ W)
  let p : T := standardPairOutputZToSecantRing W
    (![secantChartAddX W, secantChartAddY W, 1] j)
  let raw : T := algebraMap
    (projectivePairChartCoordinateRing W (true, true)) T
    (projectivePairChartAdditionCoordinates W (true, true) j)
  have hraw : raw = d ^ 3 * p := by
    simpa only [raw, d, p] using
      standardPairOutputZ_rawCoordinate_eq_denominatorCube_mul W j
  have hZ := standardPairOutputZ_rawCoordinate_eq_denominatorCube_mul W (2 : Fin 3)
  have hu : (u : T) = d ^ 3 := by
    change (projectivePairChartAdditionOutputUnit W
      (true, true) true : T) = d ^ 3
    rw [projectivePairChartAdditionOutputUnit, IsUnit.unit_spec]
    simpa [d, coveringCoordinate] using hZ
  change (↑u⁻¹ : T) * raw = p
  apply u.isUnit.mul_left_cancel
  calc
    (u : T) * ((↑u⁻¹ : T) * raw) = raw := by
      rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = d ^ 3 * p := hraw
    _ = (u : T) * p := by rw [hu]

private theorem standardPairOutputZToSecantRing_coefficient
    (W : WeierstrassCurve K) (a : K) :
    standardPairOutputZToSecantRing W (secantCoefficientHom W a) =
      algebraMap K
        (projectivePairChartAdditionOutputRing W (true, true) true) a := by
  rw [secantCoefficientHom_eq_algebraMap]
  calc
    standardPairOutputZToSecantRing W
        (algebraMap K (secantChartCoordinateRing W) a) =
      standardPairOutputZToSecantRing W
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W)
          (algebraMap K (secantPairCoordinateRing W) a)) := by
            apply congrArg (standardPairOutputZToSecantRing W)
            exact (IsScalarTower.algebraMap_apply K
              (secantPairCoordinateRing W)
              (secantChartCoordinateRing W) a).symm
    _ = _ := by
      rw [standardPairOutputZToSecantRing_algebraMap]
      change algebraMap (projectivePairChartCoordinateRing W (true, true))
          (projectivePairChartAdditionOutputRing W (true, true) true)
          (standardPairCoordinateRingAlgEquiv W
            (algebraMap K (secantPairCoordinateRing W) a)) = _
      rw [(standardPairCoordinateRingAlgEquiv W).commutes]
      exact IsScalarTower.algebraMap_apply K
        (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) true) a

private def standardPairOutputZSecantRingHom (W : WeierstrassCurve K) :
    coveringChartCoordinateRing W true →+*
      projectivePairChartAdditionOutputRing W (true, true) true :=
  (standardPairOutputZToSecantRing W).comp
    ((secantAdditionToAffineRing W).comp
      (standardAffineChartAlgEquiv W).symm.toRingHom)

private theorem standardPairOutputZSecantRingHom_ratio
    (W : WeierstrassCurve K) (j : Fin 3) :
    standardPairOutputZSecantRingHom W
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (coveringCoordinate true) j)) =
      standardPairOutputZToSecantRing W
        (![secantChartAddX W, secantChartAddY W, 1] j) := by
  fin_cases j
  · change standardPairOutputZToSecantRing W
      (secantAdditionToAffineRing W
        ((standardAffineChartAlgEquiv W).symm
          (coveringChartUniversalPoint W true 0))) = _
    rw [← standardAffineChartAlgEquiv_X,
      AlgEquiv.symm_apply_apply]
    change standardPairOutputZToSecantRing W
      (secantAdditionToAffineRing W (secantTargetX W)) =
        standardPairOutputZToSecantRing W (secantChartAddX W)
    exact congrArg (standardPairOutputZToSecantRing W)
      (secantAdditionToAffineRing_abscissa W)
  · change standardPairOutputZToSecantRing W
      (secantAdditionToAffineRing W
        ((standardAffineChartAlgEquiv W).symm
          (coveringChartUniversalPoint W true 1))) = _
    rw [← standardAffineChartAlgEquiv_Y,
      AlgEquiv.symm_apply_apply]
    change standardPairOutputZToSecantRing W
      (secantAdditionToAffineRing W (secantTargetY W)) =
        standardPairOutputZToSecantRing W (secantChartAddY W)
    exact congrArg (standardPairOutputZToSecantRing W)
      (secantAdditionToAffineRing_ordinate W)
  · change standardPairOutputZToSecantRing W
      (secantAdditionToAffineRing W
        ((standardAffineChartAlgEquiv W).symm
          (coveringChartUniversalPoint W true 2))) = _
    rw [show coveringChartUniversalPoint W true 2 = 1 by
        simpa [coveringCoordinate] using
          coveringChartUniversalPoint_normalized W true,
      map_one, map_one, map_one]
    change 1 = standardPairOutputZToSecantRing W 1
    exact (map_one (standardPairOutputZToSecantRing W)).symm

private theorem standardPairOutputZSecantRingHom_coefficient
    (W : WeierstrassCurve K) (a : K) :
    standardPairOutputZSecantRingHom W
        (algebraMap K (coveringChartCoordinateRing W true) a) =
      algebraMap K
        (projectivePairChartAdditionOutputRing W (true, true) true) a := by
  change standardPairOutputZToSecantRing W
    (secantAdditionToAffineRing W
      ((standardAffineChartAlgEquiv W).symm
        (algebraMap K (coveringChartCoordinateRing W true) a))) = _
  rw [(standardAffineChartAlgEquiv W).symm.commutes]
  rw [← secantTargetCoefficientHom_eq_algebraMap,
    secantAdditionToAffineRing_coefficient,
    standardPairOutputZToSecantRing_coefficient]

private theorem standardPairOutputZSecantRingHom_eq_rawOutputRingHom
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardPairOutputZSecantRingHom W =
      (projectivePairChartAdditionOutputAlgHom W
        (true, true) true).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate true)
  · ext a
    change standardPairOutputZSecantRingHom W
        (coveringChartStructureRingHom W true a) =
      projectivePairChartAdditionOutputAlgHom W (true, true) true
        (coveringChartStructureRingHom W true a)
    rw [← coveringChartCoordinateRing_algebraMap,
      standardPairOutputZSecantRingHom_coefficient,
      (projectivePairChartAdditionOutputAlgHom W
        (true, true) true).commutes]
  · intro j
    change standardPairOutputZSecantRingHom W
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (coveringCoordinate true) j)) =
      projectivePairChartAdditionOutputAlgHom W (true, true) true
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (coveringCoordinate true) j))
    rw [standardPairOutputZSecantRingHom_ratio,
      projectivePairChartAdditionOutputAlgHom_ratio]
    exact (standardPairOutputZPoint_eq_secantPoint W j).symm

private theorem affineEquationToStandardChartRingEquiv_toRingHom
    (W : WeierstrassCurve K) :
    (affineEquationToStandardChartRingEquiv W).toRingHom =
      (standardAffineChartAlgEquiv W).toRingHom := by
  rfl

private theorem standardPairOutputZ_preAffineRingHom_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (standardPairOutputZToSecantRing W).comp (secantAdditionToAffineRing W) =
      (projectivePairChartAdditionOutputAlgHom W
        (true, true) true).toRingHom.comp
          (standardAffineChartAlgEquiv W).toRingHom := by
  have h := congrArg
    (fun f : coveringChartCoordinateRing W true →+*
        projectivePairChartAdditionOutputRing W (true, true) true ↦
      f.comp (standardAffineChartAlgEquiv W).toRingHom)
    (standardPairOutputZSecantRingHom_eq_rawOutputRingHom W)
  apply DFunLike.ext _ _
  intro a
  have ha := DFunLike.congr_fun h a
  simpa [standardPairOutputZSecantRingHom] using ha

private theorem standardPairOutputZ_preAffineRingHom_eq_original
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (standardPairOutputZToSecantRing W).comp (secantAdditionToAffineRing W) =
      (projectivePairChartAdditionOutputAlgHom W
        (true, true) true).toRingHom.comp
          (affineEquationToStandardChartRingEquiv W).toRingHom := by
  rw [affineEquationToStandardChartRingEquiv_toRingHom]
  exact standardPairOutputZ_preAffineRingHom_eq W

private theorem affineEquationSchemeIsoStandardChart_inv_specMap
    (W : WeierstrassCurve K) :
    (affineEquationSchemeIsoStandardChart W).inv =
      Spec.map (CommRingCat.ofHom
        (affineEquationToStandardChartRingEquiv W).toRingHom) := by
  rfl

private def standardPairOutputZToStandardRingHom
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardAffineChartCoordinateRing W →+*
      projectivePairChartAdditionOutputRing W (true, true) true where
  toFun x := projectivePairChartAdditionOutputAlgHom W
    (true, true) true x
  map_one' := by
    with_unfolding_all
      exact map_one (projectivePairChartAdditionOutputAlgHom W
        (true, true) true)
  map_mul' x y := by
    with_unfolding_all
      exact map_mul (projectivePairChartAdditionOutputAlgHom W
        (true, true) true) x y
  map_zero' := by
    with_unfolding_all
      exact map_zero (projectivePairChartAdditionOutputAlgHom W
        (true, true) true)
  map_add' x y := by
    with_unfolding_all
      exact map_add (projectivePairChartAdditionOutputAlgHom W
        (true, true) true) x y

private def standardPairOutputZToStandardChart
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Spec (.of (projectivePairChartAdditionOutputRing W
      (true, true) true)) ⟶ standardAffineChartScheme W :=
  Spec.map (CommRingCat.ofHom (standardPairOutputZToStandardRingHom W))

private theorem standardPairRawOutputZMorphism_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
  projectivePairChartAdditionOutputMorphism W (true, true) true =
      standardPairOutputZToStandardChart W ≫ standardSecantChartMap W := by
  with_unfolding_all rfl

private def standardPairOutputZToAffineChart
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Spec (.of (projectivePairChartAdditionOutputRing W
      (true, true) true)) ⟶
        Spec (.of (affineWeierstrassCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    ((standardPairOutputZToStandardRingHom W).comp
        (affineEquationToStandardChartRingEquiv W).toRingHom))

private theorem standardPairOutputZToStandardChart_comp_inv
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardPairOutputZToStandardChart W ≫
        (affineEquationSchemeIsoStandardChart W).inv =
      standardPairOutputZToAffineChart W := by
  rw [standardPairOutputZToStandardChart,
    affineEquationSchemeIsoStandardChart_inv_specMap,
    standardPairOutputZToAffineChart]
  with_reducible_and_instances
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem standardPairOutputZ_preAffineRingHom_eq_typed
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (standardPairOutputZToSecantRing W).comp (secantAdditionToAffineRing W) =
      (standardPairOutputZToStandardRingHom W).comp
        (affineEquationToStandardChartRingEquiv W).toRingHom := by
  apply DFunLike.ext _ _
  intro a
  have h := RingHom.congr_fun
    (standardPairOutputZ_preAffineRingHom_eq_original W) a
  with_unfolding_all exact h

/-- Pulling the checked secant formula back to the raw standard-pair
output-`Z` localization gives the localized homogeneous formula exactly. -/
@[reassoc]
theorem standardPairOutputZToSecant_comp_secantAdditionProjectiveMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    standardPairOutputZToSecant W ≫ secantAdditionProjectiveMorphism W =
      projectivePairChartAdditionOutputMorphism W
        (true, true) true := by
  rw [standardPairRawOutputZMorphism_eq]
  rw [standardPairOutputZToSecant, secantAdditionProjectiveMorphism,
    secantAdditionAffineMorphism]
  have hfactor :
      Spec.map (CommRingCat.ofHom (standardPairOutputZToSecantRing W)) ≫
          Spec.map (CommRingCat.ofHom (secantAdditionToAffineRing W)) ≫
            (affineEquationSchemeIsoStandardChart W).hom =
        standardPairOutputZToStandardChart W := by
    apply (cancel_mono (affineEquationSchemeIsoStandardChart W).inv).1
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [standardPairOutputZToStandardChart_comp_inv,
      standardPairOutputZToAffineChart]
    rw [← Spec.map_comp, Spec.map_inj,
      ← CommRingCat.ofHom_comp]
    apply CommRingCat.hom_ext
    exact standardPairOutputZ_preAffineRingHom_eq_typed W
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ standardSecantChartMap W) hfactor

/-- On the standard projective-pair chart, the localized raw secant formula
is exactly the restriction of the addition morphism transported from the
checked affine-pair atlas. -/
@[reassoc]
theorem projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionOutputOpen W (true, true) true ≫
        standardPairAdditionMorphism W =
      projectivePairChartAdditionOutputMorphism W
        (true, true) true := by
  calc
    projectivePairChartAdditionOutputOpen W (true, true) true ≫
        standardPairAdditionMorphism W =
      (projectivePairChartAdditionOutputOpen W (true, true) true ≫
          (standardPairIsoAffinePair W).hom) ≫
        affinePairAdditionMorphism W := by
          rw [standardPairAdditionMorphism, Category.assoc]
    _ = (standardPairOutputZToSecant W ≫ secantChartToPair W) ≫
        affinePairAdditionMorphism W := by
          rw [standardPairOutputZToSecant_comp_secantChartToPair]
    _ = standardPairOutputZToSecant W ≫
        secantAdditionProjectiveMorphism W := by
          rw [Category.assoc,
            secantChartToPair_comp_affinePairAdditionMorphism]
    _ = projectivePairChartAdditionOutputMorphism W
        (true, true) true :=
      standardPairOutputZToSecant_comp_secantAdditionProjectiveMorphism W

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
