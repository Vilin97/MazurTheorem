/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassInfinityPairNeighborhoodAdditionFormula

/-!
# Compatibility of the infinity-pair and secant addition formulas

The regular addition formula on `D(B∞)` removes the cubic diagonal factor
from the homogeneous secant triple.  This file forms the exact principal
overlap `D(B∞ · Ysec)` with the old `Ysec` output chart.  The scaling
identity makes the new output `Y` coordinate automatically invertible there,
so the overlap maps to both actual source opens.

After both triples are normalized to `Y = 1`, their points agree coordinate
by coordinate.  Consequently the two genuine cubic-valued morphisms, and
their maps into the common infinity-pair source chart, agree on this overlap.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## The exact source overlap -/

/-- Coordinate ring of the intersection of the infinity neighborhood
`D(B∞)` and the old secant-output open `D(Ysec)`. -/
abbrev projectiveInfinityPairSecantOverlapRing
    (W : WeierstrassCurve K) :=
  Localization.Away
    (projectiveInfinityPairAdditionB12 W *
      projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))

/-- Restriction from `D(B∞)` to `D(B∞ · Ysec)`. -/
noncomputable def projectiveInfinityPairSecantOverlapToNeighborhoodRing
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodRing W →+*
      projectiveInfinityPairSecantOverlapRing W := by
  change Localization.Away (projectiveInfinityPairAdditionB12 W) →+*
    projectiveInfinityPairSecantOverlapRing W
  exact IsLocalization.Away.awayToAwayRight
    (S := projectiveInfinityPairNeighborhoodRing W)
    (P := projectiveInfinityPairSecantOverlapRing W)
    (projectiveInfinityPairAdditionB12 W)
    (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))

/-- Restriction from the old secant `Y`-output localization to the common
overlap. -/
noncomputable def projectiveInfinityPairSecantOverlapToSecantRing
    (W : WeierstrassCurve K) :
    projectivePairChartAdditionOutputRing W (false, false) false →+*
      projectiveInfinityPairSecantOverlapRing W := by
  change Localization.Away
      (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3)) →+*
    projectiveInfinityPairSecantOverlapRing W
  exact IsLocalization.Away.awayToAwayLeft
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3)))
    (P := projectiveInfinityPairSecantOverlapRing W)
    (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
    (projectiveInfinityPairAdditionB12 W)

@[simp]
theorem projectiveInfinityPairSecantOverlapToNeighborhoodRing_algebraMap
    (W : WeierstrassCurve K)
    (a : projectiveInfinityPairCoordinateRing W) :
    projectiveInfinityPairSecantOverlapToNeighborhoodRing W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairNeighborhoodRing W) a) =
      algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairSecantOverlapRing W) a := by
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := projectiveInfinityPairNeighborhoodRing W)
    (P := projectiveInfinityPairSecantOverlapRing W)
    (projectiveInfinityPairAdditionB12 W)
    (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3)) a

@[simp]
theorem projectiveInfinityPairSecantOverlapToSecantRing_algebraMap
    (W : WeierstrassCurve K)
    (a : projectiveInfinityPairCoordinateRing W) :
    projectiveInfinityPairSecantOverlapToSecantRing W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectivePairChartAdditionOutputRing W (false, false) false) a) =
      algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairSecantOverlapRing W) a := by
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3)))
    (P := projectiveInfinityPairSecantOverlapRing W)
    (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
    (projectiveInfinityPairAdditionB12 W) a

/-- The old secant `Y` coordinate is a unit on the overlap by construction. -/
noncomputable def projectiveInfinityPairSecantOverlapRawYUnit
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairSecantOverlapRing W)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd
    (S := projectiveInfinityPairSecantOverlapRing W)
    (projectiveInfinityPairAdditionB12 W *
      projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
    (dvd_mul_left
      (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
      (projectiveInfinityPairAdditionB12 W))).unit

@[simp]
private theorem projectiveInfinityPairSecantOverlapRawYUnit_spec
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairSecantOverlapRawYUnit W :
      projectiveInfinityPairSecantOverlapRing W) =
      algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairSecantOverlapRing W)
        (projectivePairChartAdditionCoordinates W (false, false)
          (1 : Fin 3)) := by
  rw [projectiveInfinityPairSecantOverlapRawYUnit]
  exact (IsLocalization.Away.isUnit_of_dvd
    (S := projectiveInfinityPairSecantOverlapRing W)
    (projectiveInfinityPairAdditionB12 W *
      projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
    (dvd_mul_left
      (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3))
      (projectiveInfinityPairAdditionB12 W))).unit_spec

/-- On the common overlap, the new formula's `Y` coordinate is also a unit.
This is the key consequence of `Ysec = (x₁ - x₂)³ Ynew`. -/
theorem projectiveInfinityPairSecantOverlap_localY_isUnit
    (W : WeierstrassCurve K) :
    IsUnit
      (projectiveInfinityPairSecantOverlapToNeighborhoodRing W
        (projectiveInfinityPairNeighborhoodAdditionCoordinates W
          (1 : Fin 3))) := by
  let R := projectiveInfinityPairCoordinateRing W
  let S := projectiveInfinityPairNeighborhoodRing W
  let P := projectiveInfinityPairSecantOverlapRing W
  let f : S →+* P :=
    projectiveInfinityPairSecantOverlapToNeighborhoodRing W
  let d := projectiveInfinityPairNeighborhoodX₁ W -
    projectiveInfinityPairNeighborhoodX₂ W
  have hscale := congrFun
    (projectiveInfinityPairNeighborhood_rawAdditionCoordinates_eq_smul W)
    (1 : Fin 3)
  change algebraMap R S
      (projectivePairChartAdditionCoordinates W (false, false) (1 : Fin 3)) =
    d ^ 3 * projectiveInfinityPairNeighborhoodAdditionCoordinates W
      (1 : Fin 3) at hscale
  have hmapped := congrArg f hscale
  have hraw : IsUnit
      (algebraMap R P
        (projectivePairChartAdditionCoordinates W (false, false)
          (1 : Fin 3))) := by
    rw [← projectiveInfinityPairSecantOverlapRawYUnit_spec]
    exact (projectiveInfinityPairSecantOverlapRawYUnit W).isUnit
  have hproduct : IsUnit
      (f d ^ 3 *
        f (projectiveInfinityPairNeighborhoodAdditionCoordinates W
          (1 : Fin 3))) := by
    rw [← map_pow, ← map_mul, ← hscale,
      projectiveInfinityPairSecantOverlapToNeighborhoodRing_algebraMap]
    exact hraw
  exact (IsUnit.mul_iff.mp hproduct).2

/-- Restriction from the actual new addition source to the overlap. -/
noncomputable def projectiveInfinityPairSecantOverlapToOriginAdditionRing
    (W : WeierstrassCurve K) :
    projectiveInfinityPairNeighborhoodAdditionOutputRing W →+*
      projectiveInfinityPairSecantOverlapRing W :=
  IsLocalization.Away.lift
    (R := projectiveInfinityPairNeighborhoodRing W)
    (S := projectiveInfinityPairNeighborhoodAdditionOutputRing W)
    (P := projectiveInfinityPairSecantOverlapRing W)
    (g := projectiveInfinityPairSecantOverlapToNeighborhoodRing W)
    (projectiveInfinityPairNeighborhoodAdditionCoordinates W (1 : Fin 3))
    (projectiveInfinityPairSecantOverlap_localY_isUnit W)

@[simp]
theorem projectiveInfinityPairSecantOverlapToOriginAdditionRing_algebraMap
    (W : WeierstrassCurve K)
    (a : projectiveInfinityPairNeighborhoodRing W) :
    projectiveInfinityPairSecantOverlapToOriginAdditionRing W
        (algebraMap (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairNeighborhoodAdditionOutputRing W) a) =
      projectiveInfinityPairSecantOverlapToNeighborhoodRing W a := by
  exact IsLocalization.Away.lift_eq
    (R := projectiveInfinityPairNeighborhoodRing W)
    (S := projectiveInfinityPairNeighborhoodAdditionOutputRing W)
    (P := projectiveInfinityPairSecantOverlapRing W)
    (g := projectiveInfinityPairSecantOverlapToNeighborhoodRing W)
    (projectiveInfinityPairNeighborhoodAdditionCoordinates W (1 : Fin 3))
    _ a

/-! ## Equality of the normalized output points -/

noncomputable def projectiveInfinityPairSecantOverlapLocalYUnit
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairSecantOverlapRing W)ˣ :=
  (projectiveInfinityPairSecantOverlap_localY_isUnit W).unit

@[simp]
private theorem projectiveInfinityPairSecantOverlapLocalYUnit_spec
    (W : WeierstrassCurve K) :
    (projectiveInfinityPairSecantOverlapLocalYUnit W :
      projectiveInfinityPairSecantOverlapRing W) =
      projectiveInfinityPairSecantOverlapToNeighborhoodRing W
        (projectiveInfinityPairNeighborhoodAdditionCoordinates W
          (1 : Fin 3)) := by
  exact (projectiveInfinityPairSecantOverlap_localY_isUnit W).unit_spec

private theorem projectiveInfinityPairSecantOverlap_rawYUnit_map
    (W : WeierstrassCurve K) :
    Units.map
        (projectiveInfinityPairSecantOverlapToSecantRing W).toMonoidHom
        (projectivePairChartAdditionOutputUnit W (false, false) false) =
      projectiveInfinityPairSecantOverlapRawYUnit W := by
  apply Units.ext
  change projectiveInfinityPairSecantOverlapToSecantRing W
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectivePairChartAdditionOutputRing W (false, false) false)
        (projectivePairChartAdditionCoordinates W (false, false)
          (1 : Fin 3))) = _
  rw [
    projectiveInfinityPairSecantOverlapToSecantRing_algebraMap,
    projectiveInfinityPairSecantOverlapRawYUnit_spec]

private theorem projectiveInfinityPairSecantOverlap_localYUnit_map
    (W : WeierstrassCurve K) :
    Units.map
        (projectiveInfinityPairSecantOverlapToOriginAdditionRing W).toMonoidHom
        (projectiveInfinityPairNeighborhoodAdditionOutputUnit W) =
      projectiveInfinityPairSecantOverlapLocalYUnit W := by
  apply Units.ext
  change projectiveInfinityPairSecantOverlapToOriginAdditionRing W
      (algebraMap (projectiveInfinityPairNeighborhoodRing W)
        (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
        (projectiveInfinityPairNeighborhoodAdditionCoordinates W
          (1 : Fin 3))) = _
  rw [
    projectiveInfinityPairSecantOverlapToOriginAdditionRing_algebraMap,
    projectiveInfinityPairSecantOverlapLocalYUnit_spec]

private theorem projectiveInfinityPairSecantOverlap_secantPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    projectiveInfinityPairSecantOverlapToSecantRing W
        (projectivePairChartAdditionOutputPoint W (false, false) false j) =
      ↑(projectiveInfinityPairSecantOverlapRawYUnit W)⁻¹ *
        algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairSecantOverlapRing W)
          (projectivePairChartAdditionCoordinates W (false, false) j) := by
  let u := projectivePairChartAdditionOutputUnit W (false, false) false
  have hu :
      projectiveInfinityPairSecantOverlapToSecantRing W
          (↑u⁻¹ : projectivePairChartAdditionOutputRing W
            (false, false) false) =
        (↑(projectiveInfinityPairSecantOverlapRawYUnit W)⁻¹ :
          projectiveInfinityPairSecantOverlapRing W) := by
    calc
      _ = ↑(Units.map
            (projectiveInfinityPairSecantOverlapToSecantRing W).toMonoidHom
            u)⁻¹ :=
        (Units.coe_map_inv
          (projectiveInfinityPairSecantOverlapToSecantRing W).toMonoidHom
          u).symm
      _ = _ := congrArg
        (fun v : (projectiveInfinityPairSecantOverlapRing W)ˣ ↦
          (↑v⁻¹ : projectiveInfinityPairSecantOverlapRing W))
        (projectiveInfinityPairSecantOverlap_rawYUnit_map W)
  change projectiveInfinityPairSecantOverlapToSecantRing W
      ((↑u⁻¹ : projectivePairChartAdditionOutputRing W
          (false, false) false) *
        algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectivePairChartAdditionOutputRing W (false, false) false)
          (projectivePairChartAdditionCoordinates W (false, false) j)) = _
  rw [map_mul,
    projectiveInfinityPairSecantOverlapToSecantRing_algebraMap, hu]

private theorem projectiveInfinityPairSecantOverlap_originPoint
    (W : WeierstrassCurve K) (j : Fin 3) :
    projectiveInfinityPairSecantOverlapToOriginAdditionRing W
        (projectiveInfinityPairNeighborhoodAdditionOutputPoint W j) =
      ↑(projectiveInfinityPairSecantOverlapLocalYUnit W)⁻¹ *
        projectiveInfinityPairSecantOverlapToNeighborhoodRing W
          (projectiveInfinityPairNeighborhoodAdditionCoordinates W j) := by
  let u := projectiveInfinityPairNeighborhoodAdditionOutputUnit W
  have hu :
      projectiveInfinityPairSecantOverlapToOriginAdditionRing W
          (↑u⁻¹ : projectiveInfinityPairNeighborhoodAdditionOutputRing W) =
        (↑(projectiveInfinityPairSecantOverlapLocalYUnit W)⁻¹ :
          projectiveInfinityPairSecantOverlapRing W) := by
    calc
      _ = ↑(Units.map
            (projectiveInfinityPairSecantOverlapToOriginAdditionRing W).toMonoidHom
            u)⁻¹ :=
        (Units.coe_map_inv
          (projectiveInfinityPairSecantOverlapToOriginAdditionRing W).toMonoidHom
          u).symm
      _ = _ := congrArg
        (fun v : (projectiveInfinityPairSecantOverlapRing W)ˣ ↦
          (↑v⁻¹ : projectiveInfinityPairSecantOverlapRing W))
        (projectiveInfinityPairSecantOverlap_localYUnit_map W)
  change projectiveInfinityPairSecantOverlapToOriginAdditionRing W
      ((↑u⁻¹ : projectiveInfinityPairNeighborhoodAdditionOutputRing W) *
        algebraMap (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
          (projectiveInfinityPairNeighborhoodAdditionCoordinates W j)) = _
  rw [map_mul,
    projectiveInfinityPairSecantOverlapToOriginAdditionRing_algebraMap, hu]

private theorem projectiveInfinityPairSecantOverlap_rawCoordinate
    (W : WeierstrassCurve K) (j : Fin 3) :
    algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairSecantOverlapRing W)
        (projectivePairChartAdditionCoordinates W (false, false) j) =
      projectiveInfinityPairSecantOverlapToNeighborhoodRing W
          (projectiveInfinityPairNeighborhoodX₁ W -
            projectiveInfinityPairNeighborhoodX₂ W) ^ 3 *
        projectiveInfinityPairSecantOverlapToNeighborhoodRing W
          (projectiveInfinityPairNeighborhoodAdditionCoordinates W j) := by
  have hscale := congrFun
    (projectiveInfinityPairNeighborhood_rawAdditionCoordinates_eq_smul W) j
  have h := congrArg
    (projectiveInfinityPairSecantOverlapToNeighborhoodRing W) hscale
  simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow,
    projectiveInfinityPairSecantOverlapToNeighborhoodRing_algebraMap] using h

/-- The old secant point and the new regular point have identical normalized
coordinates on their exact common overlap. -/
theorem projectiveInfinityPairSecantOverlap_outputPoints_eq
    (W : WeierstrassCurve K) (j : Fin 3) :
    projectiveInfinityPairSecantOverlapToOriginAdditionRing W
        (projectiveInfinityPairNeighborhoodAdditionOutputPoint W j) =
      projectiveInfinityPairSecantOverlapToSecantRing W
        (projectivePairChartAdditionOutputPoint W (false, false) false j) := by
  rw [projectiveInfinityPairSecantOverlap_originPoint,
    projectiveInfinityPairSecantOverlap_secantPoint]
  let P := projectiveInfinityPairSecantOverlapRing W
  let uNew := projectiveInfinityPairSecantOverlapLocalYUnit W
  let uRaw := projectiveInfinityPairSecantOverlapRawYUnit W
  let d := projectiveInfinityPairSecantOverlapToNeighborhoodRing W
    (projectiveInfinityPairNeighborhoodX₁ W -
      projectiveInfinityPairNeighborhoodX₂ W)
  let pNew := projectiveInfinityPairSecantOverlapToNeighborhoodRing W
    (projectiveInfinityPairNeighborhoodAdditionCoordinates W j)
  let pRaw := algebraMap (projectiveInfinityPairCoordinateRing W) P
    (projectivePairChartAdditionCoordinates W (false, false) j)
  have hRaw := projectiveInfinityPairSecantOverlap_rawCoordinate W j
  have hY := projectiveInfinityPairSecantOverlap_rawCoordinate W (1 : Fin 3)
  have huRaw : (↑uRaw : P) = d ^ 3 * (↑uNew : P) := by
    simpa only [uRaw, uNew, d,
      projectiveInfinityPairSecantOverlapRawYUnit_spec,
      projectiveInfinityPairSecantOverlapLocalYUnit_spec] using hY
  have hpRaw : pRaw = d ^ 3 * pNew := by
    simpa only [pRaw, pNew, d] using hRaw
  apply uRaw.isUnit.mul_left_cancel
  calc
    (↑uRaw : P) * ((↑uNew⁻¹ : P) * pNew) = d ^ 3 * pNew := by
      rw [huRaw]
      rw [mul_assoc (d ^ 3), ← mul_assoc (↑uNew : P), Units.mul_inv,
        one_mul]
    _ = pRaw := hpRaw.symm
    _ = (↑uRaw : P) * ((↑uRaw⁻¹ : P) * pRaw) := by
      symm
      rw [← mul_assoc, Units.mul_inv, one_mul]

/-! ## Equality of ring maps and scheme morphisms -/

private theorem projectiveInfinityPairSecantOverlap_outputRingMaps_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (projectiveInfinityPairSecantOverlapToOriginAdditionRing W).comp
        (projectiveInfinityPairNeighborhoodAdditionOutputAlgHom W).toRingHom =
      (projectiveInfinityPairSecantOverlapToSecantRing W).comp
        (projectivePairChartAdditionOutputAlgHom W
          (false, false) false).toRingHom := by
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate false)
  · ext a
    change projectiveInfinityPairSecantOverlapToOriginAdditionRing W
        (projectiveInfinityPairNeighborhoodAdditionOutputAlgHom W
          (coveringChartStructureRingHom W false a)) =
      projectiveInfinityPairSecantOverlapToSecantRing W
        (projectivePairChartAdditionOutputAlgHom W (false, false) false
          (coveringChartStructureRingHom W false a))
    rw [← coveringChartCoordinateRing_algebraMap,
      (projectiveInfinityPairNeighborhoodAdditionOutputAlgHom W).commutes,
      (projectivePairChartAdditionOutputAlgHom W
        (false, false) false).commutes]
    change projectiveInfinityPairSecantOverlapToOriginAdditionRing W
        (algebraMap (projectiveInfinityPairNeighborhoodRing W)
          (projectiveInfinityPairNeighborhoodAdditionOutputRing W)
          (algebraMap K (projectiveInfinityPairNeighborhoodRing W) a)) =
      projectiveInfinityPairSecantOverlapToSecantRing W
        (algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectivePairChartAdditionOutputRing W (false, false) false)
          (algebraMap K (projectiveInfinityPairCoordinateRing W) a))
    rw [projectiveInfinityPairSecantOverlapToOriginAdditionRing_algebraMap,
      projectiveInfinityPairSecantOverlapToSecantRing_algebraMap]
    rw [IsScalarTower.algebraMap_apply K
      (projectiveInfinityPairCoordinateRing W)
      (projectiveInfinityPairNeighborhoodRing W),
      projectiveInfinityPairSecantOverlapToNeighborhoodRing_algebraMap]
  · intro j
    change projectiveInfinityPairSecantOverlapToOriginAdditionRing W
        (projectiveInfinityPairNeighborhoodAdditionOutputAlgHom W
          (Ideal.Quotient.mk (coveringChartIdeal W false)
            (coordinateChartRatio (coveringCoordinate false) j))) =
      projectiveInfinityPairSecantOverlapToSecantRing W
        (projectivePairChartAdditionOutputAlgHom W (false, false) false
          (Ideal.Quotient.mk (coveringChartIdeal W false)
            (coordinateChartRatio (coveringCoordinate false) j)))
    rw [projectiveInfinityPairNeighborhoodAdditionOutputAlgHom_ratio,
      projectivePairChartAdditionOutputAlgHom_ratio]
    exact projectiveInfinityPairSecantOverlap_outputPoints_eq W j

/-- The common overlap, restricted to the new infinity-pair addition source. -/
noncomputable def projectiveInfinityPairSecantOverlapToOriginAddition
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairSecantOverlapRing W)) ⟶
      Spec (.of (projectiveInfinityPairNeighborhoodAdditionOutputRing W)) :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairSecantOverlapToOriginAdditionRing W))

/-- The common overlap, restricted to the old secant `Y`-output source. -/
noncomputable def projectiveInfinityPairSecantOverlapToSecant
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairSecantOverlapRing W)) ⟶
      Spec (.of
        (projectivePairChartAdditionOutputRing W (false, false) false)) :=
  Spec.map (CommRingCat.ofHom
    (projectiveInfinityPairSecantOverlapToSecantRing W))

/-- The overlap as its intrinsic principal open inside the infinity-pair
chart. -/
noncomputable def projectiveInfinityPairSecantOverlapOpen
    (W : WeierstrassCurve K) :
    Spec (.of (projectiveInfinityPairSecantOverlapRing W)) ⟶
      projectivePairChartScheme W (false, false) :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (projectiveInfinityPairCoordinateRing W)
        (projectiveInfinityPairSecantOverlapRing W))) ≫
    (projectivePairChartIsoSpecTensor W (false, false)).inv

instance projectiveInfinityPairSecantOverlapOpen_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectiveInfinityPairSecantOverlapOpen W) := by
  dsimp only [projectiveInfinityPairSecantOverlapOpen,
    projectiveInfinityPairSecantOverlapRing]
  infer_instance

/-- The old secant restriction is the intrinsic principal-open inclusion. -/
theorem projectiveInfinityPairSecantOverlap_secantOpen_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairSecantOverlapToSecant W ≫
        projectivePairChartAdditionOutputOpen W (false, false) false =
      projectiveInfinityPairSecantOverlapOpen W := by
  have hring :
      (projectiveInfinityPairSecantOverlapToSecantRing W).comp
          (algebraMap (projectiveInfinityPairCoordinateRing W)
            (projectivePairChartAdditionOutputRing W
              (false, false) false)) =
        algebraMap (projectiveInfinityPairCoordinateRing W)
          (projectiveInfinityPairSecantOverlapRing W) := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectiveInfinityPairSecantOverlapToSecantRing_algebraMap]
  apply (cancel_mono (projectivePairChartIsoSpecTensor W (false, false)).hom).mp
  simp only [projectiveInfinityPairSecantOverlapToSecant,
    projectivePairChartAdditionOutputOpen,
    projectiveInfinityPairSecantOverlapOpen, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
    congrArg (fun f : projectiveInfinityPairCoordinateRing W →+*
      projectiveInfinityPairSecantOverlapRing W ↦
        Spec.map (CommRingCat.ofHom f)) hring

/-- Both restrictions have the same map into the infinity-by-infinity member
of the projective-pair cover. -/
theorem projectiveInfinityPairSecantOverlap_open_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairSecantOverlapToOriginAddition W ≫
        projectiveInfinityPairOriginAdditionOpen W =
      projectiveInfinityPairSecantOverlapToSecant W ≫
        projectivePairChartAdditionOutputOpen W (false, false) false := by
  have hring :
      ((projectiveInfinityPairSecantOverlapToOriginAdditionRing W).comp
          (algebraMap (projectiveInfinityPairNeighborhoodRing W)
            (projectiveInfinityPairNeighborhoodAdditionOutputRing W))).comp
          (algebraMap (projectiveInfinityPairCoordinateRing W)
            (projectiveInfinityPairNeighborhoodRing W)) =
        (projectiveInfinityPairSecantOverlapToSecantRing W).comp
          (algebraMap (projectiveInfinityPairCoordinateRing W)
            (projectivePairChartAdditionOutputRing W
              (false, false) false)) := by
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,
      projectiveInfinityPairSecantOverlapToOriginAdditionRing_algebraMap,
      projectiveInfinityPairSecantOverlapToNeighborhoodRing_algebraMap,
      projectiveInfinityPairSecantOverlapToSecantRing_algebraMap]
  have hmap := congrArg
    (fun f : projectiveInfinityPairCoordinateRing W →+*
        projectiveInfinityPairSecantOverlapRing W ↦
      Spec.map (CommRingCat.ofHom f)) hring
  apply (cancel_mono (projectivePairChartIsoSpecTensor W (false, false)).hom).mp
  simp only [projectiveInfinityPairOriginAdditionOpen,
    projectivePairChartAdditionOutputOpen,
    projectiveInfinityPairNeighborhoodOpen,
    projectiveInfinityPairSecantOverlapToOriginAddition,
    projectiveInfinityPairNeighborhoodAdditionOutputOpen,
    projectiveInfinityPairSecantOverlapToSecant, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  simpa only [← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp] using hmap

/-- The new restriction is also the intrinsic principal-open inclusion. -/
theorem projectiveInfinityPairSecantOverlap_originOpen_eq
    (W : WeierstrassCurve K) :
    projectiveInfinityPairSecantOverlapToOriginAddition W ≫
        projectiveInfinityPairOriginAdditionOpen W =
      projectiveInfinityPairSecantOverlapOpen W :=
  (projectiveInfinityPairSecantOverlap_open_eq W).trans
    (projectiveInfinityPairSecantOverlap_secantOpen_eq W)

instance projectiveInfinityPairSecantOverlapToSecant_comp_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectiveInfinityPairSecantOverlapToSecant W ≫
        projectivePairChartAdditionOutputOpen W (false, false) false) := by
  rw [projectiveInfinityPairSecantOverlap_secantOpen_eq]
  infer_instance

instance projectiveInfinityPairSecantOverlapToSecant_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (projectiveInfinityPairSecantOverlapToSecant W) :=
  IsOpenImmersion.of_comp _
    (projectivePairChartAdditionOutputOpen W (false, false) false)

instance projectiveInfinityPairSecantOverlapToOriginAddition_comp_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectiveInfinityPairSecantOverlapToOriginAddition W ≫
        projectiveInfinityPairOriginAdditionOpen W) := by
  rw [projectiveInfinityPairSecantOverlap_originOpen_eq]
  infer_instance

instance projectiveInfinityPairSecantOverlapToOriginAddition_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion
      (projectiveInfinityPairSecantOverlapToOriginAddition W) :=
  IsOpenImmersion.of_comp _ (projectiveInfinityPairOriginAdditionOpen W)

/-- The regular infinity-neighborhood formula and the old secant formula
define the same morphism to the concrete cubic on their common overlap. -/
theorem projectiveInfinityPairSecantOverlap_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectiveInfinityPairSecantOverlapToOriginAddition W ≫
        projectiveInfinityPairOriginAdditionMorphism W =
      projectiveInfinityPairSecantOverlapToSecant W ≫
        projectivePairChartAdditionOutputMorphism W
          (false, false) false := by
  rw [projectiveInfinityPairOriginAdditionMorphism,
    projectivePairChartAdditionOutputMorphism,
    projectiveInfinityPairSecantOverlapToOriginAddition,
    projectiveInfinityPairSecantOverlapToSecant]
  rw [← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    projectiveInfinityPairSecantOverlap_outputRingMaps_eq]

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
