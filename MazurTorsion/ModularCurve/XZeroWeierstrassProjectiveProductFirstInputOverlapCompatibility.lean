/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectivePointComparison
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductInputOverlapSchemes
import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductOutputCharts

/-!
# Addition compatibility on the first projective-pair input overlap

Changing the first input from its standard representative to its infinity
representative multiplies the raw secant triple by the square of the invertible
transition coordinate.  This file localizes the exact first-factor input
overlap at either selected infinity-side output coordinate and proves that the
two normalized secant points agree there.

The design boundary is the resulting equality of genuine cubic-valued
morphisms.  The named downstream consumer
`projectivePairFirstOverlapAdditionOutput_morphisms_eq` supplies the
first-factor compatibility edge for gluing the local addition laws; this file
does not compare secant and doubling formulas or construct the global law.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## The localized overlap ring -/

/-- The standard-to-infinity transition coordinate is invertible on the
exact cubic overlap. -/
theorem coveringChartOverlapScale_isUnit (W : WeierstrassCurve K) :
    IsUnit (coveringChartOverlapScale W) := by
  letI := (standardChartToCoveringChartOverlapRing W).toAlgebra
  haveI : IsLocalization.Away
      (Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartRatio (K := K) 2 1))
      (coveringChartOverlapCoordinateRing W) :=
    coveringChartOverlap_isLocalization_standardChart W
  change IsUnit
    (algebraMap (coveringChartCoordinateRing W true)
      (coveringChartOverlapCoordinateRing W)
      (Ideal.Quotient.mk (coveringChartIdeal W true)
        (coordinateChartRatio (K := K) 2 1)))
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The first-factor transition coordinate remains invertible after tensoring
with the unchanged second chart. -/
theorem projectivePairFirstChartOverlapScale_isUnit
    (W : WeierstrassCurve K) (j : Bool) :
    IsUnit (projectivePairFirstChartOverlapScale W j) := by
  exact (coveringChartOverlapScale_isUnit W).map
    (Algebra.TensorProduct.includeLeft
      (R := K)
      (S := K)
      (A := coveringChartOverlapCoordinateRing W)
      (B := coveringChartCoordinateRing W j)).toRingHom

/-- The common first-input overlap, further localized where the chosen raw
infinity-side secant output coordinate is invertible. -/
abbrev projectivePairFirstOverlapAdditionOutputRing
    (W : WeierstrassCurve K) (j out : Bool) :=
  Localization.Away
    (infinityPairToFirstChartOverlapAlgHom W j
      (projectivePairChartAdditionCoordinates W (false, j)
        (coveringCoordinate out)))

private theorem projectivePairFirstOverlapAdditionOutput_infinity_isUnit
    (W : WeierstrassCurve K) (j out : Bool) :
    IsUnit
      (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
        (projectivePairFirstOverlapAdditionOutputRing W j out)
        (infinityPairToFirstChartOverlapAlgHom W j
          (projectivePairChartAdditionCoordinates W (false, j)
            (coveringCoordinate out)))) :=
  IsLocalization.Away.algebraMap_isUnit _

private theorem projectivePairFirstOverlapAdditionOutput_standard_isUnit
    (W : WeierstrassCurve K) (j out : Bool) :
    IsUnit
      (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
        (projectivePairFirstOverlapAdditionOutputRing W j out)
        (standardPairToFirstChartOverlapAlgHom W j
          (projectivePairChartAdditionCoordinates W (true, j)
            (coveringCoordinate out)))) := by
  have hscale := congrFun
    (projectivePairFirstOverlap_standardAddition_eq_smul_infinityAddition W j)
    (coveringCoordinate out)
  have hmapped := congrArg
    (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
      (projectivePairFirstOverlapAdditionOutputRing W j out)) hscale
  rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    at hmapped
  rw [hmapped]
  exact IsUnit.mul
    (((projectivePairFirstChartOverlapScale_isUnit W j).map
      (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
        (projectivePairFirstOverlapAdditionOutputRing W j out))).pow 2)
    (projectivePairFirstOverlapAdditionOutput_infinity_isUnit W j out)

/-- Restrict the standard-side output-coordinate localization to the common
first-input/output overlap. -/
noncomputable def projectivePairFirstOverlapAdditionOutputToStandardRing
    (W : WeierstrassCurve K) (j out : Bool) :
    projectivePairChartAdditionOutputRing W (true, j) out →+*
      projectivePairFirstOverlapAdditionOutputRing W j out :=
  IsLocalization.Away.lift
    (R := projectivePairChartCoordinateRing W (true, j))
    (S := projectivePairChartAdditionOutputRing W (true, j) out)
    (P := projectivePairFirstOverlapAdditionOutputRing W j out)
    (g := (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
      (projectivePairFirstOverlapAdditionOutputRing W j out)).comp
        (standardPairToFirstChartOverlapAlgHom W j).toRingHom)
    (projectivePairChartAdditionCoordinates W (true, j)
      (coveringCoordinate out))
    (projectivePairFirstOverlapAdditionOutput_standard_isUnit W j out)

/-- Restrict the infinity-side output-coordinate localization to the common
first-input/output overlap. -/
noncomputable def projectivePairFirstOverlapAdditionOutputToInfinityRing
    (W : WeierstrassCurve K) (j out : Bool) :
    projectivePairChartAdditionOutputRing W (false, j) out →+*
      projectivePairFirstOverlapAdditionOutputRing W j out :=
  IsLocalization.Away.lift
    (R := projectivePairChartCoordinateRing W (false, j))
    (S := projectivePairChartAdditionOutputRing W (false, j) out)
    (P := projectivePairFirstOverlapAdditionOutputRing W j out)
    (g := (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
      (projectivePairFirstOverlapAdditionOutputRing W j out)).comp
        (infinityPairToFirstChartOverlapAlgHom W j).toRingHom)
    (projectivePairChartAdditionCoordinates W (false, j)
      (coveringCoordinate out))
    (projectivePairFirstOverlapAdditionOutput_infinity_isUnit W j out)

@[simp]
theorem projectivePairFirstOverlapAdditionOutputToStandardRing_algebraMap
    (W : WeierstrassCurve K) (j out : Bool)
    (a : projectivePairChartCoordinateRing W (true, j)) :
    projectivePairFirstOverlapAdditionOutputToStandardRing W j out
        (algebraMap (projectivePairChartCoordinateRing W (true, j))
          (projectivePairChartAdditionOutputRing W (true, j) out) a) =
      algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
        (projectivePairFirstOverlapAdditionOutputRing W j out)
        (standardPairToFirstChartOverlapAlgHom W j a) := by
  exact IsLocalization.Away.lift_eq
    (R := projectivePairChartCoordinateRing W (true, j))
    (S := projectivePairChartAdditionOutputRing W (true, j) out)
    (P := projectivePairFirstOverlapAdditionOutputRing W j out)
    (g := (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
      (projectivePairFirstOverlapAdditionOutputRing W j out)).comp
        (standardPairToFirstChartOverlapAlgHom W j).toRingHom)
    (projectivePairChartAdditionCoordinates W (true, j)
      (coveringCoordinate out)) _ a

@[simp]
theorem projectivePairFirstOverlapAdditionOutputToInfinityRing_algebraMap
    (W : WeierstrassCurve K) (j out : Bool)
    (a : projectivePairChartCoordinateRing W (false, j)) :
    projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
        (algebraMap (projectivePairChartCoordinateRing W (false, j))
          (projectivePairChartAdditionOutputRing W (false, j) out) a) =
      algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
        (projectivePairFirstOverlapAdditionOutputRing W j out)
        (infinityPairToFirstChartOverlapAlgHom W j a) := by
  exact IsLocalization.Away.lift_eq
    (R := projectivePairChartCoordinateRing W (false, j))
    (S := projectivePairChartAdditionOutputRing W (false, j) out)
    (P := projectivePairFirstOverlapAdditionOutputRing W j out)
    (g := (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
      (projectivePairFirstOverlapAdditionOutputRing W j out)).comp
        (infinityPairToFirstChartOverlapAlgHom W j).toRingHom)
    (projectivePairChartAdditionCoordinates W (false, j)
      (coveringCoordinate out)) _ a

/-! ## Equality of normalized output points -/

private noncomputable def
    projectivePairFirstOverlapAdditionOutputStandardUnit
    (W : WeierstrassCurve K) (j out : Bool) :
    (projectivePairFirstOverlapAdditionOutputRing W j out)ˣ :=
  (projectivePairFirstOverlapAdditionOutput_standard_isUnit W j out).unit

private noncomputable def
    projectivePairFirstOverlapAdditionOutputInfinityUnit
    (W : WeierstrassCurve K) (j out : Bool) :
    (projectivePairFirstOverlapAdditionOutputRing W j out)ˣ :=
  (projectivePairFirstOverlapAdditionOutput_infinity_isUnit W j out).unit

@[simp]
private theorem projectivePairFirstOverlapAdditionOutputStandardUnit_spec
    (W : WeierstrassCurve K) (j out : Bool) :
    (projectivePairFirstOverlapAdditionOutputStandardUnit W j out :
      projectivePairFirstOverlapAdditionOutputRing W j out) =
      algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
        (projectivePairFirstOverlapAdditionOutputRing W j out)
        (standardPairToFirstChartOverlapAlgHom W j
          (projectivePairChartAdditionCoordinates W (true, j)
            (coveringCoordinate out))) :=
  (projectivePairFirstOverlapAdditionOutput_standard_isUnit W j out).unit_spec

@[simp]
private theorem projectivePairFirstOverlapAdditionOutputInfinityUnit_spec
    (W : WeierstrassCurve K) (j out : Bool) :
    (projectivePairFirstOverlapAdditionOutputInfinityUnit W j out :
      projectivePairFirstOverlapAdditionOutputRing W j out) =
      algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
        (projectivePairFirstOverlapAdditionOutputRing W j out)
        (infinityPairToFirstChartOverlapAlgHom W j
          (projectivePairChartAdditionCoordinates W (false, j)
            (coveringCoordinate out))) :=
  (projectivePairFirstOverlapAdditionOutput_infinity_isUnit W j out).unit_spec

private theorem
    projectivePairFirstOverlapAdditionOutput_standardUnit_map
    (W : WeierstrassCurve K) (j out : Bool) :
    Units.map
        (projectivePairFirstOverlapAdditionOutputToStandardRing W j out).toMonoidHom
        (projectivePairChartAdditionOutputUnit W (true, j) out) =
      projectivePairFirstOverlapAdditionOutputStandardUnit W j out := by
  apply Units.ext
  change projectivePairFirstOverlapAdditionOutputToStandardRing W j out
      (algebraMap (projectivePairChartCoordinateRing W (true, j))
        (projectivePairChartAdditionOutputRing W (true, j) out)
        (projectivePairChartAdditionCoordinates W (true, j)
          (coveringCoordinate out))) = _
  rw [projectivePairFirstOverlapAdditionOutputToStandardRing_algebraMap,
    projectivePairFirstOverlapAdditionOutputStandardUnit_spec]

private theorem
    projectivePairFirstOverlapAdditionOutput_infinityUnit_map
    (W : WeierstrassCurve K) (j out : Bool) :
    Units.map
        (projectivePairFirstOverlapAdditionOutputToInfinityRing W j out).toMonoidHom
        (projectivePairChartAdditionOutputUnit W (false, j) out) =
      projectivePairFirstOverlapAdditionOutputInfinityUnit W j out := by
  apply Units.ext
  change projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
      (algebraMap (projectivePairChartCoordinateRing W (false, j))
        (projectivePairChartAdditionOutputRing W (false, j) out)
        (projectivePairChartAdditionCoordinates W (false, j)
          (coveringCoordinate out))) = _
  rw [projectivePairFirstOverlapAdditionOutputToInfinityRing_algebraMap,
    projectivePairFirstOverlapAdditionOutputInfinityUnit_spec]

private theorem projectivePairFirstOverlapAdditionOutput_standardPoint
    (W : WeierstrassCurve K) (j out : Bool) (k : Fin 3) :
    projectivePairFirstOverlapAdditionOutputToStandardRing W j out
        (projectivePairChartAdditionOutputPoint W (true, j) out k) =
      ↑(projectivePairFirstOverlapAdditionOutputStandardUnit W j out)⁻¹ *
        algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
          (projectivePairFirstOverlapAdditionOutputRing W j out)
          (standardPairToFirstChartOverlapAlgHom W j
            (projectivePairChartAdditionCoordinates W (true, j) k)) := by
  let u := projectivePairChartAdditionOutputUnit W (true, j) out
  have hu :
      projectivePairFirstOverlapAdditionOutputToStandardRing W j out
          (↑u⁻¹ : projectivePairChartAdditionOutputRing W (true, j) out) =
        (↑(projectivePairFirstOverlapAdditionOutputStandardUnit W j out)⁻¹ :
          projectivePairFirstOverlapAdditionOutputRing W j out) := by
    calc
      _ = ↑(Units.map
            (projectivePairFirstOverlapAdditionOutputToStandardRing W j out).toMonoidHom
            u)⁻¹ :=
        (Units.coe_map_inv
          (projectivePairFirstOverlapAdditionOutputToStandardRing W j out).toMonoidHom
          u).symm
      _ = _ := congrArg
        (fun v : (projectivePairFirstOverlapAdditionOutputRing W j out)ˣ ↦
          (↑v⁻¹ : projectivePairFirstOverlapAdditionOutputRing W j out))
        (projectivePairFirstOverlapAdditionOutput_standardUnit_map W j out)
  change projectivePairFirstOverlapAdditionOutputToStandardRing W j out
      ((↑u⁻¹ : projectivePairChartAdditionOutputRing W (true, j) out) *
        algebraMap (projectivePairChartCoordinateRing W (true, j))
          (projectivePairChartAdditionOutputRing W (true, j) out)
          (projectivePairChartAdditionCoordinates W (true, j) k)) = _
  rw [map_mul,
    projectivePairFirstOverlapAdditionOutputToStandardRing_algebraMap, hu]

private theorem projectivePairFirstOverlapAdditionOutput_infinityPoint
    (W : WeierstrassCurve K) (j out : Bool) (k : Fin 3) :
    projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
        (projectivePairChartAdditionOutputPoint W (false, j) out k) =
      ↑(projectivePairFirstOverlapAdditionOutputInfinityUnit W j out)⁻¹ *
        algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
          (projectivePairFirstOverlapAdditionOutputRing W j out)
          (infinityPairToFirstChartOverlapAlgHom W j
            (projectivePairChartAdditionCoordinates W (false, j) k)) := by
  let u := projectivePairChartAdditionOutputUnit W (false, j) out
  have hu :
      projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
          (↑u⁻¹ : projectivePairChartAdditionOutputRing W (false, j) out) =
        (↑(projectivePairFirstOverlapAdditionOutputInfinityUnit W j out)⁻¹ :
          projectivePairFirstOverlapAdditionOutputRing W j out) := by
    calc
      _ = ↑(Units.map
            (projectivePairFirstOverlapAdditionOutputToInfinityRing W j out).toMonoidHom
            u)⁻¹ :=
        (Units.coe_map_inv
          (projectivePairFirstOverlapAdditionOutputToInfinityRing W j out).toMonoidHom
          u).symm
      _ = _ := congrArg
        (fun v : (projectivePairFirstOverlapAdditionOutputRing W j out)ˣ ↦
          (↑v⁻¹ : projectivePairFirstOverlapAdditionOutputRing W j out))
        (projectivePairFirstOverlapAdditionOutput_infinityUnit_map W j out)
  change projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
      ((↑u⁻¹ : projectivePairChartAdditionOutputRing W (false, j) out) *
        algebraMap (projectivePairChartCoordinateRing W (false, j))
          (projectivePairChartAdditionOutputRing W (false, j) out)
          (projectivePairChartAdditionCoordinates W (false, j) k)) = _
  rw [map_mul,
    projectivePairFirstOverlapAdditionOutputToInfinityRing_algebraMap, hu]

private theorem projectivePairFirstOverlapAdditionOutput_rawCoordinate
    (W : WeierstrassCurve K) (j out : Bool) (k : Fin 3) :
    algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
        (projectivePairFirstOverlapAdditionOutputRing W j out)
        (standardPairToFirstChartOverlapAlgHom W j
          (projectivePairChartAdditionCoordinates W (true, j) k)) =
      algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
          (projectivePairFirstOverlapAdditionOutputRing W j out)
          (projectivePairFirstChartOverlapScale W j) ^ 2 *
        algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
          (projectivePairFirstOverlapAdditionOutputRing W j out)
          (infinityPairToFirstChartOverlapAlgHom W j
            (projectivePairChartAdditionCoordinates W (false, j) k)) := by
  have hscale := congrFun
    (projectivePairFirstOverlap_standardAddition_eq_smul_infinityAddition W j) k
  have h := congrArg
    (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
      (projectivePairFirstOverlapAdditionOutputRing W j out)) hscale
  simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    using h

/-- The standard- and infinity-side secant triples have identical normalized
coordinates on the common first-input/output overlap. -/
theorem projectivePairFirstOverlapAdditionOutput_points_eq
    (W : WeierstrassCurve K) (j out : Bool) (k : Fin 3) :
    projectivePairFirstOverlapAdditionOutputToStandardRing W j out
        (projectivePairChartAdditionOutputPoint W (true, j) out k) =
      projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
        (projectivePairChartAdditionOutputPoint W (false, j) out k) := by
  rw [projectivePairFirstOverlapAdditionOutput_standardPoint,
    projectivePairFirstOverlapAdditionOutput_infinityPoint]
  let P := projectivePairFirstOverlapAdditionOutputRing W j out
  let uStandard := projectivePairFirstOverlapAdditionOutputStandardUnit W j out
  let uInfinity := projectivePairFirstOverlapAdditionOutputInfinityUnit W j out
  let t := algebraMap (projectivePairFirstChartOverlapCoordinateRing W j) P
    (projectivePairFirstChartOverlapScale W j)
  let pStandard := algebraMap
    (projectivePairFirstChartOverlapCoordinateRing W j) P
    (standardPairToFirstChartOverlapAlgHom W j
      (projectivePairChartAdditionCoordinates W (true, j) k))
  let pInfinity := algebraMap
    (projectivePairFirstChartOverlapCoordinateRing W j) P
    (infinityPairToFirstChartOverlapAlgHom W j
      (projectivePairChartAdditionCoordinates W (false, j) k))
  have hOutput := projectivePairFirstOverlapAdditionOutput_rawCoordinate
    W j out (coveringCoordinate out)
  have hPoint := projectivePairFirstOverlapAdditionOutput_rawCoordinate
    W j out k
  have huStandard : (↑uStandard : P) = t ^ 2 * (↑uInfinity : P) := by
    simpa only [uStandard, uInfinity, t,
      projectivePairFirstOverlapAdditionOutputStandardUnit_spec,
      projectivePairFirstOverlapAdditionOutputInfinityUnit_spec] using hOutput
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

private theorem projectivePairFirstOverlapAdditionOutput_ringMaps_eq
    (W : WeierstrassCurve K) [W.IsElliptic] (j out : Bool) :
    (projectivePairFirstOverlapAdditionOutputToStandardRing W j out).comp
        (projectivePairChartAdditionOutputAlgHom W
          (true, j) out).toRingHom =
      (projectivePairFirstOverlapAdditionOutputToInfinityRing W j out).comp
        (projectivePairChartAdditionOutputAlgHom W
          (false, j) out).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate out)
  · ext a
    change projectivePairFirstOverlapAdditionOutputToStandardRing W j out
        (projectivePairChartAdditionOutputAlgHom W (true, j) out
          (coveringChartStructureRingHom W out a)) =
      projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
        (projectivePairChartAdditionOutputAlgHom W (false, j) out
          (coveringChartStructureRingHom W out a))
    rw [← coveringChartCoordinateRing_algebraMap,
      (projectivePairChartAdditionOutputAlgHom W (true, j) out).commutes,
      (projectivePairChartAdditionOutputAlgHom W (false, j) out).commutes]
    change projectivePairFirstOverlapAdditionOutputToStandardRing W j out
        (algebraMap (projectivePairChartCoordinateRing W (true, j))
          (projectivePairChartAdditionOutputRing W (true, j) out)
          (algebraMap K (projectivePairChartCoordinateRing W (true, j)) a)) =
      projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
        (algebraMap (projectivePairChartCoordinateRing W (false, j))
          (projectivePairChartAdditionOutputRing W (false, j) out)
          (algebraMap K (projectivePairChartCoordinateRing W (false, j)) a))
    rw [projectivePairFirstOverlapAdditionOutputToStandardRing_algebraMap,
      projectivePairFirstOverlapAdditionOutputToInfinityRing_algebraMap,
      (standardPairToFirstChartOverlapAlgHom W j).commutes,
      (infinityPairToFirstChartOverlapAlgHom W j).commutes]
  · intro k
    change projectivePairFirstOverlapAdditionOutputToStandardRing W j out
        (projectivePairChartAdditionOutputAlgHom W (true, j) out
          (Ideal.Quotient.mk (coveringChartIdeal W out)
            (coordinateChartRatio (coveringCoordinate out) k))) =
      projectivePairFirstOverlapAdditionOutputToInfinityRing W j out
        (projectivePairChartAdditionOutputAlgHom W (false, j) out
          (Ideal.Quotient.mk (coveringChartIdeal W out)
            (coordinateChartRatio (coveringCoordinate out) k)))
    rw [projectivePairChartAdditionOutputAlgHom_ratio,
      projectivePairChartAdditionOutputAlgHom_ratio]
    exact projectivePairFirstOverlapAdditionOutput_points_eq W j out k

/-- Restriction from the standard-side secant output source to the common
first-input/output overlap. -/
noncomputable def projectivePairFirstOverlapAdditionOutputToStandard
    (W : WeierstrassCurve K) (j out : Bool) :
    Spec (.of (projectivePairFirstOverlapAdditionOutputRing W j out)) ⟶
      Spec (.of (projectivePairChartAdditionOutputRing W (true, j) out)) :=
  Spec.map (CommRingCat.ofHom
    (projectivePairFirstOverlapAdditionOutputToStandardRing W j out))

/-- Restriction from the infinity-side secant output source to the common
first-input/output overlap. -/
noncomputable def projectivePairFirstOverlapAdditionOutputToInfinity
    (W : WeierstrassCurve K) (j out : Bool) :
    Spec (.of (projectivePairFirstOverlapAdditionOutputRing W j out)) ⟶
      Spec (.of (projectivePairChartAdditionOutputRing W (false, j) out)) :=
  Spec.map (CommRingCat.ofHom
    (projectivePairFirstOverlapAdditionOutputToInfinityRing W j out))

/-- The common output-coordinate localization as an intrinsic principal open
of the first-factor input overlap. -/
noncomputable def projectivePairFirstOverlapAdditionOutputOpen
    (W : WeierstrassCurve K) (j out : Bool) :
    Spec (.of (projectivePairFirstOverlapAdditionOutputRing W j out)) ⟶
      projectivePairFirstChartOverlapScheme W j :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
      (projectivePairFirstOverlapAdditionOutputRing W j out)))

instance projectivePairFirstOverlapAdditionOutputOpen_isOpenImmersion
    (W : WeierstrassCurve K) (j out : Bool) :
    IsOpenImmersion (projectivePairFirstOverlapAdditionOutputOpen W j out) := by
  dsimp only [projectivePairFirstOverlapAdditionOutputOpen,
    projectivePairFirstOverlapAdditionOutputRing]
  infer_instance

/-- The standard-side restriction is the intrinsic common output open followed
by the standard embedding of the first-factor input overlap. -/
theorem projectivePairFirstOverlapAdditionOutput_standardOpen_eq
    (W : WeierstrassCurve K) (j out : Bool) :
    projectivePairFirstOverlapAdditionOutputToStandard W j out ≫
        projectivePairChartAdditionOutputOpen W (true, j) out =
      projectivePairFirstOverlapAdditionOutputOpen W j out ≫
        projectivePairFirstOverlapToStandardPair W j := by
  have hring :
      (projectivePairFirstOverlapAdditionOutputToStandardRing W j out).comp
          (algebraMap (projectivePairChartCoordinateRing W (true, j))
            (projectivePairChartAdditionOutputRing W (true, j) out)) =
        (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
            (projectivePairFirstOverlapAdditionOutputRing W j out)).comp
          (standardPairToFirstChartOverlapAlgHom W j).toRingHom := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectivePairFirstOverlapAdditionOutputToStandardRing_algebraMap]
    rfl
  apply (cancel_mono (projectivePairChartIsoSpecTensor W (true, j)).hom).mp
  simp only [projectivePairFirstOverlapAdditionOutputToStandard,
    projectivePairChartAdditionOutputOpen,
    projectivePairFirstOverlapAdditionOutputOpen,
    projectivePairFirstOverlapToStandardPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f : projectivePairChartCoordinateRing W (true, j) →+*
      projectivePairFirstOverlapAdditionOutputRing W j out ↦
        Spec.map (CommRingCat.ofHom f)) hring

/-- The infinity-side restriction is the intrinsic common output open followed
by the infinity embedding of the first-factor input overlap. -/
theorem projectivePairFirstOverlapAdditionOutput_infinityOpen_eq
    (W : WeierstrassCurve K) (j out : Bool) :
    projectivePairFirstOverlapAdditionOutputToInfinity W j out ≫
        projectivePairChartAdditionOutputOpen W (false, j) out =
      projectivePairFirstOverlapAdditionOutputOpen W j out ≫
        projectivePairFirstOverlapToInfinityPair W j := by
  have hring :
      (projectivePairFirstOverlapAdditionOutputToInfinityRing W j out).comp
          (algebraMap (projectivePairChartCoordinateRing W (false, j))
            (projectivePairChartAdditionOutputRing W (false, j) out)) =
        (algebraMap (projectivePairFirstChartOverlapCoordinateRing W j)
            (projectivePairFirstOverlapAdditionOutputRing W j out)).comp
          (infinityPairToFirstChartOverlapAlgHom W j).toRingHom := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectivePairFirstOverlapAdditionOutputToInfinityRing_algebraMap]
    rfl
  apply (cancel_mono (projectivePairChartIsoSpecTensor W (false, j)).hom).mp
  simp only [projectivePairFirstOverlapAdditionOutputToInfinity,
    projectivePairChartAdditionOutputOpen,
    projectivePairFirstOverlapAdditionOutputOpen,
    projectivePairFirstOverlapToInfinityPair, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f : projectivePairChartCoordinateRing W (false, j) →+*
      projectivePairFirstOverlapAdditionOutputRing W j out ↦
        Spec.map (CommRingCat.ofHom f)) hring

instance
    projectivePairFirstOverlapAdditionOutputToStandard_comp_isOpenImmersion
    (W : WeierstrassCurve K) (j out : Bool) :
    IsOpenImmersion
      (projectivePairFirstOverlapAdditionOutputToStandard W j out ≫
        projectivePairChartAdditionOutputOpen W (true, j) out) := by
  rw [projectivePairFirstOverlapAdditionOutput_standardOpen_eq]
  infer_instance

instance projectivePairFirstOverlapAdditionOutputToStandard_isOpenImmersion
    (W : WeierstrassCurve K) (j out : Bool) :
    IsOpenImmersion
      (projectivePairFirstOverlapAdditionOutputToStandard W j out) :=
  IsOpenImmersion.of_comp _
    (projectivePairChartAdditionOutputOpen W (true, j) out)

instance
    projectivePairFirstOverlapAdditionOutputToInfinity_comp_isOpenImmersion
    (W : WeierstrassCurve K) (j out : Bool) :
    IsOpenImmersion
      (projectivePairFirstOverlapAdditionOutputToInfinity W j out ≫
        projectivePairChartAdditionOutputOpen W (false, j) out) := by
  rw [projectivePairFirstOverlapAdditionOutput_infinityOpen_eq]
  infer_instance

instance projectivePairFirstOverlapAdditionOutputToInfinity_isOpenImmersion
    (W : WeierstrassCurve K) (j out : Bool) :
    IsOpenImmersion
      (projectivePairFirstOverlapAdditionOutputToInfinity W j out) :=
  IsOpenImmersion.of_comp _
    (projectivePairChartAdditionOutputOpen W (false, j) out)

/-- The two restrictions of the localized overlap have the same composite
into the full projective product. -/
theorem projectivePairFirstOverlapAdditionOutput_maps_eq
    (W : WeierstrassCurve K) (j out : Bool) :
    projectivePairFirstOverlapAdditionOutputToStandard W j out ≫
        projectivePairChartAdditionOutputOpen W (true, j) out ≫
        projectivePairChartMap W (true, j) =
      projectivePairFirstOverlapAdditionOutputToInfinity W j out ≫
        projectivePairChartAdditionOutputOpen W (false, j) out ≫
        projectivePairChartMap W (false, j) := by
  calc
    _ = projectivePairFirstOverlapAdditionOutputOpen W j out ≫
          projectivePairFirstOverlapToStandardPair W j ≫
          projectivePairChartMap W (true, j) := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ projectivePairChartMap W (true, j))
        (projectivePairFirstOverlapAdditionOutput_standardOpen_eq W j out)
    _ = projectivePairFirstOverlapAdditionOutputOpen W j out ≫
          projectivePairFirstOverlapToInfinityPair W j ≫
          projectivePairChartMap W (false, j) := by
      rw [projectivePairFirstOverlap_maps_eq]
    _ = _ := by
      simpa only [Category.assoc] using (congrArg
        (fun f ↦ f ≫ projectivePairChartMap W (false, j))
        (projectivePairFirstOverlapAdditionOutput_infinityOpen_eq W j out)).symm

/-- The two normalized secant formulas define the same genuine morphism to
the cubic on the common first-input/output overlap. -/
theorem projectivePairFirstOverlapAdditionOutput_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] (j out : Bool) :
    projectivePairFirstOverlapAdditionOutputToStandard W j out ≫
        projectivePairChartAdditionOutputMorphism W (true, j) out =
      projectivePairFirstOverlapAdditionOutputToInfinity W j out ≫
        projectivePairChartAdditionOutputMorphism W (false, j) out := by
  rw [projectivePairChartAdditionOutputMorphism,
    projectivePairChartAdditionOutputMorphism,
    projectivePairFirstOverlapAdditionOutputToStandard,
    projectivePairFirstOverlapAdditionOutputToInfinity]
  rw [← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    projectivePairFirstOverlapAdditionOutput_ringMaps_eq]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
