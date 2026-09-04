/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductFirstInputOverlapCompatibility

/-!
# Addition compatibility on the second projective-pair input overlap

Changing the second input from its standard representative to its infinity
representative multiplies the raw secant triple by the square of the invertible
transition coordinate.  This file localizes the exact second-factor input
overlap at either selected infinity-side output coordinate and proves that the
two normalized secant points agree there.

The design boundary is the resulting equality of genuine cubic-valued
morphisms.  The named downstream consumer
`projectivePairSecondOverlapAdditionOutput_morphisms_eq` supplies the
second-factor compatibility edge for gluing the local addition laws; this file
does not compare secant and doubling formulas or construct the global law.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## The localized overlap ring -/

/-- The second-factor transition coordinate remains invertible after tensoring
with the unchanged first chart. -/
theorem projectivePairSecondChartOverlapScale_isUnit
    (W : WeierstrassCurve K) (i : Bool) :
    IsUnit (projectivePairSecondChartOverlapScale W i) := by
  exact (coveringChartOverlapScale_isUnit W).map
    (Algebra.TensorProduct.includeRight
      (R := K)
      (A := coveringChartCoordinateRing W i)
      (B := coveringChartOverlapCoordinateRing W)).toRingHom

/-- The common second-input overlap, further localized where the chosen raw
infinity-side secant output coordinate is invertible. -/
abbrev projectivePairSecondOverlapAdditionOutputRing
    (W : WeierstrassCurve K) (i out : Bool) :=
  Localization.Away
    (infinityPairToSecondChartOverlapAlgHom W i
      (projectivePairChartAdditionCoordinates W (i, false)
        (coveringCoordinate out)))

private theorem projectivePairSecondOverlapAdditionOutput_infinity_isUnit
    (W : WeierstrassCurve K) (i out : Bool) :
    IsUnit
      (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
        (projectivePairSecondOverlapAdditionOutputRing W i out)
        (infinityPairToSecondChartOverlapAlgHom W i
          (projectivePairChartAdditionCoordinates W (i, false)
            (coveringCoordinate out)))) :=
  IsLocalization.Away.algebraMap_isUnit _

private theorem projectivePairSecondOverlapAdditionOutput_standard_isUnit
    (W : WeierstrassCurve K) (i out : Bool) :
    IsUnit
      (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
        (projectivePairSecondOverlapAdditionOutputRing W i out)
        (standardPairToSecondChartOverlapAlgHom W i
          (projectivePairChartAdditionCoordinates W (i, true)
            (coveringCoordinate out)))) := by
  have hscale := congrFun
    (projectivePairSecondOverlap_standardAddition_eq_smul_infinityAddition W i)
    (coveringCoordinate out)
  have hmapped := congrArg
    (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
      (projectivePairSecondOverlapAdditionOutputRing W i out)) hscale
  rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    at hmapped
  rw [hmapped]
  exact IsUnit.mul
    (((projectivePairSecondChartOverlapScale_isUnit W i).map
      (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
        (projectivePairSecondOverlapAdditionOutputRing W i out))).pow 2)
    (projectivePairSecondOverlapAdditionOutput_infinity_isUnit W i out)

/-- Restrict the standard-side output-coordinate localization to the common
second-input/output overlap. -/
noncomputable def projectivePairSecondOverlapAdditionOutputToStandardRing
    (W : WeierstrassCurve K) (i out : Bool) :
    projectivePairChartAdditionOutputRing W (i, true) out →+*
      projectivePairSecondOverlapAdditionOutputRing W i out :=
  IsLocalization.Away.lift
    (R := projectivePairChartCoordinateRing W (i, true))
    (S := projectivePairChartAdditionOutputRing W (i, true) out)
    (P := projectivePairSecondOverlapAdditionOutputRing W i out)
    (g := (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
      (projectivePairSecondOverlapAdditionOutputRing W i out)).comp
        (standardPairToSecondChartOverlapAlgHom W i).toRingHom)
    (projectivePairChartAdditionCoordinates W (i, true)
      (coveringCoordinate out))
    (projectivePairSecondOverlapAdditionOutput_standard_isUnit W i out)

/-- Restrict the infinity-side output-coordinate localization to the common
second-input/output overlap. -/
noncomputable def projectivePairSecondOverlapAdditionOutputToInfinityRing
    (W : WeierstrassCurve K) (i out : Bool) :
    projectivePairChartAdditionOutputRing W (i, false) out →+*
      projectivePairSecondOverlapAdditionOutputRing W i out :=
  IsLocalization.Away.lift
    (R := projectivePairChartCoordinateRing W (i, false))
    (S := projectivePairChartAdditionOutputRing W (i, false) out)
    (P := projectivePairSecondOverlapAdditionOutputRing W i out)
    (g := (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
      (projectivePairSecondOverlapAdditionOutputRing W i out)).comp
        (infinityPairToSecondChartOverlapAlgHom W i).toRingHom)
    (projectivePairChartAdditionCoordinates W (i, false)
      (coveringCoordinate out))
    (projectivePairSecondOverlapAdditionOutput_infinity_isUnit W i out)

@[simp]
theorem projectivePairSecondOverlapAdditionOutputToStandardRing_algebraMap
    (W : WeierstrassCurve K) (i out : Bool)
    (a : projectivePairChartCoordinateRing W (i, true)) :
    projectivePairSecondOverlapAdditionOutputToStandardRing W i out
        (algebraMap (projectivePairChartCoordinateRing W (i, true))
          (projectivePairChartAdditionOutputRing W (i, true) out) a) =
      algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
        (projectivePairSecondOverlapAdditionOutputRing W i out)
        (standardPairToSecondChartOverlapAlgHom W i a) := by
  exact IsLocalization.Away.lift_eq
    (R := projectivePairChartCoordinateRing W (i, true))
    (S := projectivePairChartAdditionOutputRing W (i, true) out)
    (P := projectivePairSecondOverlapAdditionOutputRing W i out)
    (g := (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
      (projectivePairSecondOverlapAdditionOutputRing W i out)).comp
        (standardPairToSecondChartOverlapAlgHom W i).toRingHom)
    (projectivePairChartAdditionCoordinates W (i, true)
      (coveringCoordinate out)) _ a

@[simp]
theorem projectivePairSecondOverlapAdditionOutputToInfinityRing_algebraMap
    (W : WeierstrassCurve K) (i out : Bool)
    (a : projectivePairChartCoordinateRing W (i, false)) :
    projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
        (algebraMap (projectivePairChartCoordinateRing W (i, false))
          (projectivePairChartAdditionOutputRing W (i, false) out) a) =
      algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
        (projectivePairSecondOverlapAdditionOutputRing W i out)
        (infinityPairToSecondChartOverlapAlgHom W i a) := by
  exact IsLocalization.Away.lift_eq
    (R := projectivePairChartCoordinateRing W (i, false))
    (S := projectivePairChartAdditionOutputRing W (i, false) out)
    (P := projectivePairSecondOverlapAdditionOutputRing W i out)
    (g := (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
      (projectivePairSecondOverlapAdditionOutputRing W i out)).comp
        (infinityPairToSecondChartOverlapAlgHom W i).toRingHom)
    (projectivePairChartAdditionCoordinates W (i, false)
      (coveringCoordinate out)) _ a

/-! ## Equality of normalized output points -/

private noncomputable def
    projectivePairSecondOverlapAdditionOutputStandardUnit
    (W : WeierstrassCurve K) (i out : Bool) :
    (projectivePairSecondOverlapAdditionOutputRing W i out)ˣ :=
  (projectivePairSecondOverlapAdditionOutput_standard_isUnit W i out).unit

private noncomputable def
    projectivePairSecondOverlapAdditionOutputInfinityUnit
    (W : WeierstrassCurve K) (i out : Bool) :
    (projectivePairSecondOverlapAdditionOutputRing W i out)ˣ :=
  (projectivePairSecondOverlapAdditionOutput_infinity_isUnit W i out).unit

@[simp]
private theorem projectivePairSecondOverlapAdditionOutputStandardUnit_spec
    (W : WeierstrassCurve K) (i out : Bool) :
    (projectivePairSecondOverlapAdditionOutputStandardUnit W i out :
      projectivePairSecondOverlapAdditionOutputRing W i out) =
      algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
        (projectivePairSecondOverlapAdditionOutputRing W i out)
        (standardPairToSecondChartOverlapAlgHom W i
          (projectivePairChartAdditionCoordinates W (i, true)
            (coveringCoordinate out))) :=
  (projectivePairSecondOverlapAdditionOutput_standard_isUnit W i out).unit_spec

@[simp]
private theorem projectivePairSecondOverlapAdditionOutputInfinityUnit_spec
    (W : WeierstrassCurve K) (i out : Bool) :
    (projectivePairSecondOverlapAdditionOutputInfinityUnit W i out :
      projectivePairSecondOverlapAdditionOutputRing W i out) =
      algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
        (projectivePairSecondOverlapAdditionOutputRing W i out)
        (infinityPairToSecondChartOverlapAlgHom W i
          (projectivePairChartAdditionCoordinates W (i, false)
            (coveringCoordinate out))) :=
  (projectivePairSecondOverlapAdditionOutput_infinity_isUnit W i out).unit_spec

private theorem
    projectivePairSecondOverlapAdditionOutput_standardUnit_map
    (W : WeierstrassCurve K) (i out : Bool) :
    Units.map
        (projectivePairSecondOverlapAdditionOutputToStandardRing W i out).toMonoidHom
        (projectivePairChartAdditionOutputUnit W (i, true) out) =
      projectivePairSecondOverlapAdditionOutputStandardUnit W i out := by
  apply Units.ext
  change projectivePairSecondOverlapAdditionOutputToStandardRing W i out
      (algebraMap (projectivePairChartCoordinateRing W (i, true))
        (projectivePairChartAdditionOutputRing W (i, true) out)
        (projectivePairChartAdditionCoordinates W (i, true)
          (coveringCoordinate out))) = _
  rw [projectivePairSecondOverlapAdditionOutputToStandardRing_algebraMap,
    projectivePairSecondOverlapAdditionOutputStandardUnit_spec]

private theorem
    projectivePairSecondOverlapAdditionOutput_infinityUnit_map
    (W : WeierstrassCurve K) (i out : Bool) :
    Units.map
        (projectivePairSecondOverlapAdditionOutputToInfinityRing W i out).toMonoidHom
        (projectivePairChartAdditionOutputUnit W (i, false) out) =
      projectivePairSecondOverlapAdditionOutputInfinityUnit W i out := by
  apply Units.ext
  change projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
      (algebraMap (projectivePairChartCoordinateRing W (i, false))
        (projectivePairChartAdditionOutputRing W (i, false) out)
        (projectivePairChartAdditionCoordinates W (i, false)
          (coveringCoordinate out))) = _
  rw [projectivePairSecondOverlapAdditionOutputToInfinityRing_algebraMap,
    projectivePairSecondOverlapAdditionOutputInfinityUnit_spec]

private theorem projectivePairSecondOverlapAdditionOutput_standardPoint
    (W : WeierstrassCurve K) (i out : Bool) (k : Fin 3) :
    projectivePairSecondOverlapAdditionOutputToStandardRing W i out
        (projectivePairChartAdditionOutputPoint W (i, true) out k) =
      ↑(projectivePairSecondOverlapAdditionOutputStandardUnit W i out)⁻¹ *
        algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
          (projectivePairSecondOverlapAdditionOutputRing W i out)
          (standardPairToSecondChartOverlapAlgHom W i
            (projectivePairChartAdditionCoordinates W (i, true) k)) := by
  let u := projectivePairChartAdditionOutputUnit W (i, true) out
  have hu :
      projectivePairSecondOverlapAdditionOutputToStandardRing W i out
          (↑u⁻¹ : projectivePairChartAdditionOutputRing W (i, true) out) =
        (↑(projectivePairSecondOverlapAdditionOutputStandardUnit W i out)⁻¹ :
          projectivePairSecondOverlapAdditionOutputRing W i out) := by
    calc
      _ = ↑(Units.map
            (projectivePairSecondOverlapAdditionOutputToStandardRing W i out).toMonoidHom
            u)⁻¹ :=
        (Units.coe_map_inv
          (projectivePairSecondOverlapAdditionOutputToStandardRing W i out).toMonoidHom
          u).symm
      _ = _ := congrArg
        (fun v : (projectivePairSecondOverlapAdditionOutputRing W i out)ˣ ↦
          (↑v⁻¹ : projectivePairSecondOverlapAdditionOutputRing W i out))
        (projectivePairSecondOverlapAdditionOutput_standardUnit_map W i out)
  change projectivePairSecondOverlapAdditionOutputToStandardRing W i out
      ((↑u⁻¹ : projectivePairChartAdditionOutputRing W (i, true) out) *
        algebraMap (projectivePairChartCoordinateRing W (i, true))
          (projectivePairChartAdditionOutputRing W (i, true) out)
          (projectivePairChartAdditionCoordinates W (i, true) k)) = _
  rw [map_mul,
    projectivePairSecondOverlapAdditionOutputToStandardRing_algebraMap, hu]

private theorem projectivePairSecondOverlapAdditionOutput_infinityPoint
    (W : WeierstrassCurve K) (i out : Bool) (k : Fin 3) :
    projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
        (projectivePairChartAdditionOutputPoint W (i, false) out k) =
      ↑(projectivePairSecondOverlapAdditionOutputInfinityUnit W i out)⁻¹ *
        algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
          (projectivePairSecondOverlapAdditionOutputRing W i out)
          (infinityPairToSecondChartOverlapAlgHom W i
            (projectivePairChartAdditionCoordinates W (i, false) k)) := by
  let u := projectivePairChartAdditionOutputUnit W (i, false) out
  have hu :
      projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
          (↑u⁻¹ : projectivePairChartAdditionOutputRing W (i, false) out) =
        (↑(projectivePairSecondOverlapAdditionOutputInfinityUnit W i out)⁻¹ :
          projectivePairSecondOverlapAdditionOutputRing W i out) := by
    calc
      _ = ↑(Units.map
            (projectivePairSecondOverlapAdditionOutputToInfinityRing W i out).toMonoidHom
            u)⁻¹ :=
        (Units.coe_map_inv
          (projectivePairSecondOverlapAdditionOutputToInfinityRing W i out).toMonoidHom
          u).symm
      _ = _ := congrArg
        (fun v : (projectivePairSecondOverlapAdditionOutputRing W i out)ˣ ↦
          (↑v⁻¹ : projectivePairSecondOverlapAdditionOutputRing W i out))
        (projectivePairSecondOverlapAdditionOutput_infinityUnit_map W i out)
  change projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
      ((↑u⁻¹ : projectivePairChartAdditionOutputRing W (i, false) out) *
        algebraMap (projectivePairChartCoordinateRing W (i, false))
          (projectivePairChartAdditionOutputRing W (i, false) out)
          (projectivePairChartAdditionCoordinates W (i, false) k)) = _
  rw [map_mul,
    projectivePairSecondOverlapAdditionOutputToInfinityRing_algebraMap, hu]

private theorem projectivePairSecondOverlapAdditionOutput_rawCoordinate
    (W : WeierstrassCurve K) (i out : Bool) (k : Fin 3) :
    algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
        (projectivePairSecondOverlapAdditionOutputRing W i out)
        (standardPairToSecondChartOverlapAlgHom W i
          (projectivePairChartAdditionCoordinates W (i, true) k)) =
      algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
          (projectivePairSecondOverlapAdditionOutputRing W i out)
          (projectivePairSecondChartOverlapScale W i) ^ 2 *
        algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
          (projectivePairSecondOverlapAdditionOutputRing W i out)
          (infinityPairToSecondChartOverlapAlgHom W i
            (projectivePairChartAdditionCoordinates W (i, false) k)) := by
  have hscale := congrFun
    (projectivePairSecondOverlap_standardAddition_eq_smul_infinityAddition W i) k
  have h := congrArg
    (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
      (projectivePairSecondOverlapAdditionOutputRing W i out)) hscale
  simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    using h

/-- The standard- and infinity-side secant triples have identical normalized
coordinates on the common second-input/output overlap. -/
theorem projectivePairSecondOverlapAdditionOutput_points_eq
    (W : WeierstrassCurve K) (i out : Bool) (k : Fin 3) :
    projectivePairSecondOverlapAdditionOutputToStandardRing W i out
        (projectivePairChartAdditionOutputPoint W (i, true) out k) =
      projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
        (projectivePairChartAdditionOutputPoint W (i, false) out k) := by
  rw [projectivePairSecondOverlapAdditionOutput_standardPoint,
    projectivePairSecondOverlapAdditionOutput_infinityPoint]
  let P := projectivePairSecondOverlapAdditionOutputRing W i out
  let uStandard := projectivePairSecondOverlapAdditionOutputStandardUnit W i out
  let uInfinity := projectivePairSecondOverlapAdditionOutputInfinityUnit W i out
  let t := algebraMap (projectivePairSecondChartOverlapCoordinateRing W i) P
    (projectivePairSecondChartOverlapScale W i)
  let pStandard := algebraMap
    (projectivePairSecondChartOverlapCoordinateRing W i) P
    (standardPairToSecondChartOverlapAlgHom W i
      (projectivePairChartAdditionCoordinates W (i, true) k))
  let pInfinity := algebraMap
    (projectivePairSecondChartOverlapCoordinateRing W i) P
    (infinityPairToSecondChartOverlapAlgHom W i
      (projectivePairChartAdditionCoordinates W (i, false) k))
  have hOutput := projectivePairSecondOverlapAdditionOutput_rawCoordinate
    W i out (coveringCoordinate out)
  have hPoint := projectivePairSecondOverlapAdditionOutput_rawCoordinate
    W i out k
  have huStandard : (↑uStandard : P) = t ^ 2 * (↑uInfinity : P) := by
    simpa only [uStandard, uInfinity, t,
      projectivePairSecondOverlapAdditionOutputStandardUnit_spec,
      projectivePairSecondOverlapAdditionOutputInfinityUnit_spec] using hOutput
  have hpStandard : pStandard = t ^ 2 * pInfinity := by
    simpa only [pStandard, pInfinity, t] using hPoint
  apply uStandard.isUnit.mul_left_cancel
  calc
    (↑uStandard : P) * ((↑uStandard⁻¹ : P) * pStandard) = pStandard := by
      rw [← mul_assoc, Units.mul_inv, one_mul]
    _ = t ^ 2 * pInfinity := hpStandard
    _ = (↑uStandard : P) * ((↑uInfinity⁻¹ : P) * pInfinity) := by
      rw [huStandard, mul_assoc, ← mul_assoc (↑uInfinity : P),
        Units.mul_inv, one_mul]

/-! ## Equality of actual morphisms -/

private theorem projectivePairSecondOverlapAdditionOutput_ringMaps_eq
    (W : WeierstrassCurve K) [W.IsElliptic] (i out : Bool) :
    (projectivePairSecondOverlapAdditionOutputToStandardRing W i out).comp
        (projectivePairChartAdditionOutputAlgHom W
          (i, true) out).toRingHom =
      (projectivePairSecondOverlapAdditionOutputToInfinityRing W i out).comp
        (projectivePairChartAdditionOutputAlgHom W
          (i, false) out).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate out)
  · ext a
    change projectivePairSecondOverlapAdditionOutputToStandardRing W i out
        (projectivePairChartAdditionOutputAlgHom W (i, true) out
          (coveringChartStructureRingHom W out a)) =
      projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
        (projectivePairChartAdditionOutputAlgHom W (i, false) out
          (coveringChartStructureRingHom W out a))
    rw [← coveringChartCoordinateRing_algebraMap,
      (projectivePairChartAdditionOutputAlgHom W (i, true) out).commutes,
      (projectivePairChartAdditionOutputAlgHom W (i, false) out).commutes]
    change projectivePairSecondOverlapAdditionOutputToStandardRing W i out
        (algebraMap (projectivePairChartCoordinateRing W (i, true))
          (projectivePairChartAdditionOutputRing W (i, true) out)
          (algebraMap K (projectivePairChartCoordinateRing W (i, true)) a)) =
      projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
        (algebraMap (projectivePairChartCoordinateRing W (i, false))
          (projectivePairChartAdditionOutputRing W (i, false) out)
          (algebraMap K (projectivePairChartCoordinateRing W (i, false)) a))
    rw [projectivePairSecondOverlapAdditionOutputToStandardRing_algebraMap,
      projectivePairSecondOverlapAdditionOutputToInfinityRing_algebraMap,
      (standardPairToSecondChartOverlapAlgHom W i).commutes,
      (infinityPairToSecondChartOverlapAlgHom W i).commutes]
  · intro k
    change projectivePairSecondOverlapAdditionOutputToStandardRing W i out
        (projectivePairChartAdditionOutputAlgHom W (i, true) out
          (Ideal.Quotient.mk (coveringChartIdeal W out)
            (coordinateChartRatio (coveringCoordinate out) k))) =
      projectivePairSecondOverlapAdditionOutputToInfinityRing W i out
        (projectivePairChartAdditionOutputAlgHom W (i, false) out
          (Ideal.Quotient.mk (coveringChartIdeal W out)
            (coordinateChartRatio (coveringCoordinate out) k)))
    rw [projectivePairChartAdditionOutputAlgHom_ratio,
      projectivePairChartAdditionOutputAlgHom_ratio]
    exact projectivePairSecondOverlapAdditionOutput_points_eq W i out k

/-- Restriction from the standard-side secant output source to the common
second-input/output overlap. -/
noncomputable def projectivePairSecondOverlapAdditionOutputToStandard
    (W : WeierstrassCurve K) (i out : Bool) :
    Spec (.of (projectivePairSecondOverlapAdditionOutputRing W i out)) ⟶
      Spec (.of (projectivePairChartAdditionOutputRing W (i, true) out)) :=
  Spec.map (CommRingCat.ofHom
    (projectivePairSecondOverlapAdditionOutputToStandardRing W i out))

/-- Restriction from the infinity-side secant output source to the common
second-input/output overlap. -/
noncomputable def projectivePairSecondOverlapAdditionOutputToInfinity
    (W : WeierstrassCurve K) (i out : Bool) :
    Spec (.of (projectivePairSecondOverlapAdditionOutputRing W i out)) ⟶
      Spec (.of (projectivePairChartAdditionOutputRing W (i, false) out)) :=
  Spec.map (CommRingCat.ofHom
    (projectivePairSecondOverlapAdditionOutputToInfinityRing W i out))

/-- The common output-coordinate localization as an intrinsic principal open
of the second-factor input overlap. -/
noncomputable def projectivePairSecondOverlapAdditionOutputOpen
    (W : WeierstrassCurve K) (i out : Bool) :
    Spec (.of (projectivePairSecondOverlapAdditionOutputRing W i out)) ⟶
      projectivePairSecondChartOverlapScheme W i :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
      (projectivePairSecondOverlapAdditionOutputRing W i out)))

instance projectivePairSecondOverlapAdditionOutputOpen_isOpenImmersion
    (W : WeierstrassCurve K) (i out : Bool) :
    IsOpenImmersion (projectivePairSecondOverlapAdditionOutputOpen W i out) := by
  dsimp only [projectivePairSecondOverlapAdditionOutputOpen,
    projectivePairSecondOverlapAdditionOutputRing]
  infer_instance

/-- The standard-side restriction is the intrinsic common output open followed
by the standard embedding of the second-factor input overlap. -/
theorem projectivePairSecondOverlapAdditionOutput_standardOpen_eq
    (W : WeierstrassCurve K) (i out : Bool) :
    projectivePairSecondOverlapAdditionOutputToStandard W i out ≫
        projectivePairChartAdditionOutputOpen W (i, true) out =
      projectivePairSecondOverlapAdditionOutputOpen W i out ≫
        projectivePairSecondOverlapToStandardPair W i := by
  have hring :
      (projectivePairSecondOverlapAdditionOutputToStandardRing W i out).comp
          (algebraMap (projectivePairChartCoordinateRing W (i, true))
            (projectivePairChartAdditionOutputRing W (i, true) out)) =
        (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
            (projectivePairSecondOverlapAdditionOutputRing W i out)).comp
          (standardPairToSecondChartOverlapAlgHom W i).toRingHom := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectivePairSecondOverlapAdditionOutputToStandardRing_algebraMap]
    rfl
  apply (cancel_mono (projectivePairChartIsoSpecTensor W (i, true)).hom).mp
  simp only [projectivePairSecondOverlapAdditionOutputToStandard,
    projectivePairChartAdditionOutputOpen,
    projectivePairSecondOverlapAdditionOutputOpen,
    projectivePairSecondOverlapToStandardPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f : projectivePairChartCoordinateRing W (i, true) →+*
      projectivePairSecondOverlapAdditionOutputRing W i out ↦
        Spec.map (CommRingCat.ofHom f)) hring

/-- The infinity-side restriction is the intrinsic common output open followed
by the infinity embedding of the second-factor input overlap. -/
theorem projectivePairSecondOverlapAdditionOutput_infinityOpen_eq
    (W : WeierstrassCurve K) (i out : Bool) :
    projectivePairSecondOverlapAdditionOutputToInfinity W i out ≫
        projectivePairChartAdditionOutputOpen W (i, false) out =
      projectivePairSecondOverlapAdditionOutputOpen W i out ≫
        projectivePairSecondOverlapToInfinityPair W i := by
  have hring :
      (projectivePairSecondOverlapAdditionOutputToInfinityRing W i out).comp
          (algebraMap (projectivePairChartCoordinateRing W (i, false))
            (projectivePairChartAdditionOutputRing W (i, false) out)) =
        (algebraMap (projectivePairSecondChartOverlapCoordinateRing W i)
            (projectivePairSecondOverlapAdditionOutputRing W i out)).comp
          (infinityPairToSecondChartOverlapAlgHom W i).toRingHom := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectivePairSecondOverlapAdditionOutputToInfinityRing_algebraMap]
    rfl
  apply (cancel_mono (projectivePairChartIsoSpecTensor W (i, false)).hom).mp
  simp only [projectivePairSecondOverlapAdditionOutputToInfinity,
    projectivePairChartAdditionOutputOpen,
    projectivePairSecondOverlapAdditionOutputOpen,
    projectivePairSecondOverlapToInfinityPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f : projectivePairChartCoordinateRing W (i, false) →+*
      projectivePairSecondOverlapAdditionOutputRing W i out ↦
        Spec.map (CommRingCat.ofHom f)) hring

instance
    projectivePairSecondOverlapAdditionOutputToStandard_comp_isOpenImmersion
    (W : WeierstrassCurve K) (i out : Bool) :
    IsOpenImmersion
      (projectivePairSecondOverlapAdditionOutputToStandard W i out ≫
        projectivePairChartAdditionOutputOpen W (i, true) out) := by
  rw [projectivePairSecondOverlapAdditionOutput_standardOpen_eq]
  infer_instance

instance projectivePairSecondOverlapAdditionOutputToStandard_isOpenImmersion
    (W : WeierstrassCurve K) (i out : Bool) :
    IsOpenImmersion
      (projectivePairSecondOverlapAdditionOutputToStandard W i out) :=
  IsOpenImmersion.of_comp _
    (projectivePairChartAdditionOutputOpen W (i, true) out)

instance
    projectivePairSecondOverlapAdditionOutputToInfinity_comp_isOpenImmersion
    (W : WeierstrassCurve K) (i out : Bool) :
    IsOpenImmersion
      (projectivePairSecondOverlapAdditionOutputToInfinity W i out ≫
        projectivePairChartAdditionOutputOpen W (i, false) out) := by
  rw [projectivePairSecondOverlapAdditionOutput_infinityOpen_eq]
  infer_instance

instance projectivePairSecondOverlapAdditionOutputToInfinity_isOpenImmersion
    (W : WeierstrassCurve K) (i out : Bool) :
    IsOpenImmersion
      (projectivePairSecondOverlapAdditionOutputToInfinity W i out) :=
  IsOpenImmersion.of_comp _
    (projectivePairChartAdditionOutputOpen W (i, false) out)

/-- The two restrictions of the localized overlap have the same composite
into the full projective product. -/
theorem projectivePairSecondOverlapAdditionOutput_maps_eq
    (W : WeierstrassCurve K) (i out : Bool) :
    projectivePairSecondOverlapAdditionOutputToStandard W i out ≫
        projectivePairChartAdditionOutputOpen W (i, true) out ≫
        projectivePairChartMap W (i, true) =
      projectivePairSecondOverlapAdditionOutputToInfinity W i out ≫
        projectivePairChartAdditionOutputOpen W (i, false) out ≫
        projectivePairChartMap W (i, false) := by
  calc
    _ = projectivePairSecondOverlapAdditionOutputOpen W i out ≫
          projectivePairSecondOverlapToStandardPair W i ≫
          projectivePairChartMap W (i, true) := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ projectivePairChartMap W (i, true))
        (projectivePairSecondOverlapAdditionOutput_standardOpen_eq W i out)
    _ = projectivePairSecondOverlapAdditionOutputOpen W i out ≫
          projectivePairSecondOverlapToInfinityPair W i ≫
          projectivePairChartMap W (i, false) := by
      rw [projectivePairSecondOverlap_maps_eq]
    _ = _ := by
      simpa only [Category.assoc] using (congrArg
        (fun f ↦ f ≫ projectivePairChartMap W (i, false))
        (projectivePairSecondOverlapAdditionOutput_infinityOpen_eq W i out)).symm

/-- The two normalized secant formulas define the same genuine morphism to
the cubic on the common second-input/output overlap. -/
theorem projectivePairSecondOverlapAdditionOutput_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] (i out : Bool) :
    projectivePairSecondOverlapAdditionOutputToStandard W i out ≫
        projectivePairChartAdditionOutputMorphism W (i, true) out =
      projectivePairSecondOverlapAdditionOutputToInfinity W i out ≫
        projectivePairChartAdditionOutputMorphism W (i, false) out := by
  rw [projectivePairChartAdditionOutputMorphism,
    projectivePairChartAdditionOutputMorphism,
    projectivePairSecondOverlapAdditionOutputToStandard,
    projectivePairSecondOverlapAdditionOutputToInfinity]
  rw [← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    projectivePairSecondOverlapAdditionOutput_ringMaps_eq]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
