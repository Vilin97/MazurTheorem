/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductAdditionCover

/-!
# Compatibility of projective-pair output charts

The same nonzero homogeneous triple can be normalized in either the
`Z != 0` or the `Y != 0` chart.  This file constructs the exact intersection
of those two output-coordinate principal opens for the universal secant
triple and proves that the resulting cubic-valued morphisms agree there.

No compatibility between the secant and doubling triples is asserted: away
from the diagonal they represent different projective points.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-! ## The secant-output overlap -/

/-- Coordinate ring of the exact intersection of the secant output `Z` and
`Y` principal opens. -/
abbrev projectivePairChartAdditionOutputOverlapRing
    (W : WeierstrassCurve K) (ij : Bool × Bool) :=
  Localization.Away
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W ij (1 : Fin 3))

/-- Restriction from the secant output `Z` localization to the exact output
overlap. -/
noncomputable def projectivePairChartAdditionOutputOverlapToStandardRing
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartAdditionOutputRing W ij true →+*
      projectivePairChartAdditionOutputOverlapRing W ij := by
  change Localization.Away
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)) →+*
    projectivePairChartAdditionOutputOverlapRing W ij
  exact IsLocalization.Away.awayToAwayRight
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)))
    (P := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))
    (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))

/-- Restriction from the secant output `Y` localization to the exact output
overlap. -/
noncomputable def projectivePairChartAdditionOutputOverlapToInfinityRing
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartAdditionOutputRing W ij false →+*
      projectivePairChartAdditionOutputOverlapRing W ij := by
  change Localization.Away
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)) →+*
    projectivePairChartAdditionOutputOverlapRing W ij
  exact IsLocalization.Away.awayToAwayLeft
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)))
    (P := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))

@[simp]
theorem projectivePairChartAdditionOutputOverlapToStandardRing_algebraMap
    (W : WeierstrassCurve K) (ij : Bool × Bool)
    (a : projectivePairChartCoordinateRing W ij) :
    projectivePairChartAdditionOutputOverlapToStandardRing W ij
        (algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputRing W ij true) a) =
      algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputOverlapRing W ij) a := by
  change IsLocalization.Away.awayToAwayRight
      (S := Localization.Away
        (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)))
      (P := projectivePairChartAdditionOutputOverlapRing W ij)
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
      (algebraMap (projectivePairChartCoordinateRing W ij)
        (Localization.Away
          (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))) a) = _
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)))
    (P := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))
    (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)) a

@[simp]
theorem projectivePairChartAdditionOutputOverlapToInfinityRing_algebraMap
    (W : WeierstrassCurve K) (ij : Bool × Bool)
    (a : projectivePairChartCoordinateRing W ij) :
    projectivePairChartAdditionOutputOverlapToInfinityRing W ij
        (algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputRing W ij false) a) =
      algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputOverlapRing W ij) a := by
  change IsLocalization.Away.awayToAwayLeft
      (S := Localization.Away
        (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)))
      (P := projectivePairChartAdditionOutputOverlapRing W ij)
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))
      (algebraMap (projectivePairChartCoordinateRing W ij)
        (Localization.Away
          (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))) a) = _
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := Localization.Away
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)))
    (P := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)) a

/-- The secant output `Z` coordinate as a unit on the exact overlap. -/
noncomputable def projectivePairChartAdditionOutputOverlapStandardUnit
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartAdditionOutputOverlapRing W ij)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd
    (S := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
    (dvd_mul_right
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)))).unit

/-- The secant output `Y` coordinate as a unit on the exact overlap. -/
noncomputable def projectivePairChartAdditionOutputOverlapInfinityUnit
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartAdditionOutputOverlapRing W ij)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd
    (S := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
    (dvd_mul_left
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)))).unit

private theorem projectivePairChartAdditionOutputOverlap_standardUnit_map
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Units.map
        (projectivePairChartAdditionOutputOverlapToStandardRing W ij).toMonoidHom
        (projectivePairChartAdditionOutputUnit W ij true) =
      projectivePairChartAdditionOutputOverlapStandardUnit W ij := by
  let u : (projectivePairChartAdditionOutputRing W ij true)ˣ :=
    projectivePairChartAdditionOutputUnit W ij true
  change Units.map
      (projectivePairChartAdditionOutputOverlapToStandardRing W ij).toMonoidHom
      u = projectivePairChartAdditionOutputOverlapStandardUnit W ij
  apply Units.ext
  change projectivePairChartAdditionOutputOverlapToStandardRing W ij
      (u : projectivePairChartAdditionOutputRing W ij true) = _
  simp only [u]
  rw [projectivePairChartAdditionOutputUnit, IsUnit.unit_spec]
  change projectivePairChartAdditionOutputOverlapToStandardRing W ij
      (algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputRing W ij true)
        (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))) = _
  rw [projectivePairChartAdditionOutputOverlapToStandardRing_algebraMap]
  rw [projectivePairChartAdditionOutputOverlapStandardUnit]
  exact (IsLocalization.Away.isUnit_of_dvd
    (S := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
    (dvd_mul_right
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)))).unit_spec.symm

private theorem projectivePairChartAdditionOutputOverlap_infinityUnit_map
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Units.map
        (projectivePairChartAdditionOutputOverlapToInfinityRing W ij).toMonoidHom
        (projectivePairChartAdditionOutputUnit W ij false) =
      projectivePairChartAdditionOutputOverlapInfinityUnit W ij := by
  let u : (projectivePairChartAdditionOutputRing W ij false)ˣ :=
    projectivePairChartAdditionOutputUnit W ij false
  change Units.map
      (projectivePairChartAdditionOutputOverlapToInfinityRing W ij).toMonoidHom
      u = projectivePairChartAdditionOutputOverlapInfinityUnit W ij
  apply Units.ext
  change projectivePairChartAdditionOutputOverlapToInfinityRing W ij
      (u : projectivePairChartAdditionOutputRing W ij false) = _
  simp only [u]
  rw [projectivePairChartAdditionOutputUnit, IsUnit.unit_spec]
  change projectivePairChartAdditionOutputOverlapToInfinityRing W ij
      (algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputRing W ij false)
        (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))) = _
  rw [projectivePairChartAdditionOutputOverlapToInfinityRing_algebraMap]
  rw [projectivePairChartAdditionOutputOverlapInfinityUnit]
  exact (IsLocalization.Away.isUnit_of_dvd
    (S := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
    (dvd_mul_left
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)))).unit_spec.symm

@[simp]
private theorem projectivePairChartAdditionOutputOverlapStandardUnit_spec
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartAdditionOutputOverlapStandardUnit W ij :
      projectivePairChartAdditionOutputOverlapRing W ij) =
      algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputOverlapRing W ij)
        (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)) := by
  rw [projectivePairChartAdditionOutputOverlapStandardUnit]
  exact (IsLocalization.Away.isUnit_of_dvd
    (S := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
    (dvd_mul_right
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3))
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)))).unit_spec

@[simp]
private theorem projectivePairChartAdditionOutputOverlapInfinityUnit_spec
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    (projectivePairChartAdditionOutputOverlapInfinityUnit W ij :
      projectivePairChartAdditionOutputOverlapRing W ij) =
      algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputOverlapRing W ij)
        (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)) := by
  rw [projectivePairChartAdditionOutputOverlapInfinityUnit]
  exact (IsLocalization.Away.isUnit_of_dvd
    (S := projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (2 : Fin 3) *
      projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
    (dvd_mul_left
      (projectivePairChartAdditionCoordinates W ij (1 : Fin 3))
      (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)))).unit_spec

private theorem projectivePairChartAdditionOutputOverlap_standardPoint
    (W : WeierstrassCurve K) (ij : Bool × Bool) (j : Fin 3) :
    projectivePairChartAdditionOutputOverlapToStandardRing W ij
        (projectivePairChartAdditionOutputPoint W ij true j) =
      ↑(projectivePairChartAdditionOutputOverlapStandardUnit W ij)⁻¹ *
        algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputOverlapRing W ij)
          (projectivePairChartAdditionCoordinates W ij j) := by
  let u : (projectivePairChartAdditionOutputRing W ij true)ˣ :=
    projectivePairChartAdditionOutputUnit W ij true
  have hu :
      projectivePairChartAdditionOutputOverlapToStandardRing W ij
          (↑u⁻¹ : projectivePairChartAdditionOutputRing W ij true) =
        (↑(projectivePairChartAdditionOutputOverlapStandardUnit W ij)⁻¹ :
          projectivePairChartAdditionOutputOverlapRing W ij) := by
    calc
      _ = ↑(Units.map
            (projectivePairChartAdditionOutputOverlapToStandardRing W ij).toMonoidHom
            u)⁻¹ :=
        (Units.coe_map_inv
          (projectivePairChartAdditionOutputOverlapToStandardRing W ij).toMonoidHom
          u).symm
      _ = _ := congrArg
        (fun v : (projectivePairChartAdditionOutputOverlapRing W ij)ˣ ↦
          (↑v⁻¹ : projectivePairChartAdditionOutputOverlapRing W ij))
        (projectivePairChartAdditionOutputOverlap_standardUnit_map W ij)
  change projectivePairChartAdditionOutputOverlapToStandardRing W ij
      ((↑u⁻¹ : projectivePairChartAdditionOutputRing W ij true) *
        algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputRing W ij true)
          (projectivePairChartAdditionCoordinates W ij j)) = _
  rw [map_mul,
    projectivePairChartAdditionOutputOverlapToStandardRing_algebraMap]
  rw [hu]

private theorem projectivePairChartAdditionOutputOverlap_infinityPoint
    (W : WeierstrassCurve K) (ij : Bool × Bool) (j : Fin 3) :
    projectivePairChartAdditionOutputOverlapToInfinityRing W ij
        (projectivePairChartAdditionOutputPoint W ij false j) =
      ↑(projectivePairChartAdditionOutputOverlapInfinityUnit W ij)⁻¹ *
        algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputOverlapRing W ij)
          (projectivePairChartAdditionCoordinates W ij j) := by
  let u : (projectivePairChartAdditionOutputRing W ij false)ˣ :=
    projectivePairChartAdditionOutputUnit W ij false
  have hu :
      projectivePairChartAdditionOutputOverlapToInfinityRing W ij
          (↑u⁻¹ : projectivePairChartAdditionOutputRing W ij false) =
        (↑(projectivePairChartAdditionOutputOverlapInfinityUnit W ij)⁻¹ :
          projectivePairChartAdditionOutputOverlapRing W ij) := by
    calc
      _ = ↑(Units.map
            (projectivePairChartAdditionOutputOverlapToInfinityRing W ij).toMonoidHom
            u)⁻¹ :=
        (Units.coe_map_inv
          (projectivePairChartAdditionOutputOverlapToInfinityRing W ij).toMonoidHom
          u).symm
      _ = _ := congrArg
        (fun v : (projectivePairChartAdditionOutputOverlapRing W ij)ˣ ↦
          (↑v⁻¹ : projectivePairChartAdditionOutputOverlapRing W ij))
        (projectivePairChartAdditionOutputOverlap_infinityUnit_map W ij)
  change projectivePairChartAdditionOutputOverlapToInfinityRing W ij
      ((↑u⁻¹ : projectivePairChartAdditionOutputRing W ij false) *
        algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputRing W ij false)
          (projectivePairChartAdditionCoordinates W ij j)) = _
  rw [map_mul,
    projectivePairChartAdditionOutputOverlapToInfinityRing_algebraMap]
  rw [hu]

private noncomputable def
    projectivePairChartAdditionOutputOverlapToStandardAmbientRing
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2) →+*
      projectivePairChartAdditionOutputOverlapRing W ij :=
  (projectivePairChartAdditionOutputOverlapToStandardRing W ij).comp
    ((projectivePairChartAdditionOutputAlgHom W ij true).toRingHom.comp
      (Ideal.Quotient.mk (coveringChartIdeal W true)))

private noncomputable def
    projectivePairChartAdditionOutputOverlapToInfinityAmbientRing
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 1) →+*
      projectivePairChartAdditionOutputOverlapRing W ij :=
  (projectivePairChartAdditionOutputOverlapToInfinityRing W ij).comp
    ((projectivePairChartAdditionOutputAlgHom W ij false).toRingHom.comp
      (Ideal.Quotient.mk (coveringChartIdeal W false)))

private theorem
    projectivePairChartAdditionOutputOverlap_ambient_constant
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) (a : K) :
    projectivePairChartAdditionOutputOverlapToStandardAmbientRing W ij
        (coordinateChartConstantHom (K := K) 2 a) =
      projectivePairChartAdditionOutputOverlapToInfinityAmbientRing W ij
        (coordinateChartConstantHom (K := K) 1 a) := by
  change projectivePairChartAdditionOutputOverlapToStandardRing W ij
      (projectivePairChartAdditionOutputAlgHom W ij true
        (coveringChartStructureRingHom W true a)) =
    projectivePairChartAdditionOutputOverlapToInfinityRing W ij
      (projectivePairChartAdditionOutputAlgHom W ij false
        (coveringChartStructureRingHom W false a))
  rw [← coveringChartCoordinateRing_algebraMap,
    ← coveringChartCoordinateRing_algebraMap,
    (projectivePairChartAdditionOutputAlgHom W ij true).commutes,
    (projectivePairChartAdditionOutputAlgHom W ij false).commutes]
  change projectivePairChartAdditionOutputOverlapToStandardRing W ij
      (algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputRing W ij true)
        (algebraMap K (projectivePairChartCoordinateRing W ij) a)) =
    projectivePairChartAdditionOutputOverlapToInfinityRing W ij
      (algebraMap (projectivePairChartCoordinateRing W ij)
        (projectivePairChartAdditionOutputRing W ij false)
        (algebraMap K (projectivePairChartCoordinateRing W ij) a))
  rw [projectivePairChartAdditionOutputOverlapToStandardRing_algebraMap,
    projectivePairChartAdditionOutputOverlapToInfinityRing_algebraMap]

private theorem
    projectivePairChartAdditionOutputOverlap_standardAmbient_ratio
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (j : Fin 3) :
    projectivePairChartAdditionOutputOverlapToStandardAmbientRing W ij
        (coordinateChartRatio (K := K) 2 j) =
      ↑(projectivePairChartAdditionOutputOverlapStandardUnit W ij)⁻¹ *
        algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputOverlapRing W ij)
          (projectivePairChartAdditionCoordinates W ij j) := by
  change projectivePairChartAdditionOutputOverlapToStandardRing W ij
      (projectivePairChartAdditionOutputAlgHom W ij true
        (Ideal.Quotient.mk (coveringChartIdeal W true)
          (coordinateChartRatio (coveringCoordinate true) j))) = _
  rw [projectivePairChartAdditionOutputAlgHom_ratio]
  exact projectivePairChartAdditionOutputOverlap_standardPoint W ij j

private theorem
    projectivePairChartAdditionOutputOverlap_infinityAmbient_ratio
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ij : Bool × Bool) (j : Fin 3) :
    projectivePairChartAdditionOutputOverlapToInfinityAmbientRing W ij
        (coordinateChartRatio (K := K) 1 j) =
      ↑(projectivePairChartAdditionOutputOverlapInfinityUnit W ij)⁻¹ *
        algebraMap (projectivePairChartCoordinateRing W ij)
          (projectivePairChartAdditionOutputOverlapRing W ij)
          (projectivePairChartAdditionCoordinates W ij j) := by
  change projectivePairChartAdditionOutputOverlapToInfinityRing W ij
      (projectivePairChartAdditionOutputAlgHom W ij false
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (coveringCoordinate false) j))) = _
  rw [projectivePairChartAdditionOutputAlgHom_ratio]
  exact projectivePairChartAdditionOutputOverlap_infinityPoint W ij j

private theorem
    projectivePairChartAdditionOutputOverlap_standardInner_isUnit
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    IsUnit
      (projectivePairChartAdditionOutputOverlapToStandardAmbientRing W ij
        (coordinateChartRatio (K := K) 2 1)) := by
  rw [projectivePairChartAdditionOutputOverlap_standardAmbient_ratio]
  rw [← projectivePairChartAdditionOutputOverlapInfinityUnit_spec]
  exact IsUnit.mul
    ((projectivePairChartAdditionOutputOverlapStandardUnit W ij)⁻¹).isUnit
    (projectivePairChartAdditionOutputOverlapInfinityUnit W ij).isUnit

private theorem projectivePairChartAdditionOutputOverlap_outer
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    projectivePairChartAdditionOutputOverlapToInfinityAmbientRing W ij
          (coordinateChartRatio (K := K) 1 0) *
        projectivePairChartAdditionOutputOverlapToStandardAmbientRing W ij
          (coordinateChartRatio (K := K) 2 1) =
      projectivePairChartAdditionOutputOverlapToStandardAmbientRing W ij
        (coordinateChartRatio (K := K) 2 0) := by
  rw [projectivePairChartAdditionOutputOverlap_infinityAmbient_ratio,
    projectivePairChartAdditionOutputOverlap_standardAmbient_ratio,
    projectivePairChartAdditionOutputOverlap_standardAmbient_ratio,
    ← projectivePairChartAdditionOutputOverlapInfinityUnit_spec]
  let uY := projectivePairChartAdditionOutputOverlapInfinityUnit W ij
  let uZ := projectivePairChartAdditionOutputOverlapStandardUnit W ij
  let x := algebraMap (projectivePairChartCoordinateRing W ij)
    (projectivePairChartAdditionOutputOverlapRing W ij)
    (projectivePairChartAdditionCoordinates W ij (0 : Fin 3))
  have hY :
      (↑(uY⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) *
          ↑uY = 1 := by
    exact Units.inv_mul uY
  change ((↑(uY⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) * x) *
      ((↑(uZ⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) * ↑uY) =
    (↑(uZ⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) * x
  calc
    _ = ((↑(uY⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) *
          ↑uY) *
        ((↑(uZ⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) * x) := by
      ring
    _ = _ := by rw [hY, one_mul]

private theorem projectivePairChartAdditionOutputOverlap_inner
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    projectivePairChartAdditionOutputOverlapToInfinityAmbientRing W ij
          (coordinateChartRatio (K := K) 1 2) *
        projectivePairChartAdditionOutputOverlapToStandardAmbientRing W ij
          (coordinateChartRatio (K := K) 2 1) = 1 := by
  rw [projectivePairChartAdditionOutputOverlap_infinityAmbient_ratio,
    projectivePairChartAdditionOutputOverlap_standardAmbient_ratio,
    ← projectivePairChartAdditionOutputOverlapStandardUnit_spec,
    ← projectivePairChartAdditionOutputOverlapInfinityUnit_spec]
  let uY := projectivePairChartAdditionOutputOverlapInfinityUnit W ij
  let uZ := projectivePairChartAdditionOutputOverlapStandardUnit W ij
  have hY :
      (↑(uY⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) *
          ↑uY = 1 := by
    exact Units.inv_mul uY
  have hZ :
      (↑(uZ⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) *
          ↑uZ = 1 := by
    exact Units.inv_mul uZ
  change ((↑(uY⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) * ↑uZ) *
      ((↑(uZ⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) * ↑uY) = 1
  calc
    _ = ((↑(uY⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) *
          ↑uY) *
        ((↑(uZ⁻¹) : projectivePairChartAdditionOutputOverlapRing W ij) * ↑uZ) := by
      ring
    _ = 1 := by rw [hY, hZ, mul_one]

private theorem projectivePairChartAdditionOutputOverlap_ambient_maps_eq
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    Spec.map (CommRingCat.ofHom
          (projectivePairChartAdditionOutputOverlapToStandardAmbientRing W ij)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
          (MvPolynomial.isHomogeneous_X K 2) zero_lt_one =
      Spec.map (CommRingCat.ofHom
          (projectivePairChartAdditionOutputOverlapToInfinityAmbientRing W ij)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
          (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
  apply projectiveYZOverlap_ambient_maps_eq
  · exact projectivePairChartAdditionOutputOverlap_ambient_constant W ij
  · exact projectivePairChartAdditionOutputOverlap_standardInner_isUnit W ij
  · exact projectivePairChartAdditionOutputOverlap_outer W ij
  · exact projectivePairChartAdditionOutputOverlap_inner W ij

/-- Restriction from the secant output `Z` principal open to the exact
`YZ` output overlap. -/
def projectivePairChartAdditionOutputOverlapToStandard
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Spec (.of (projectivePairChartAdditionOutputOverlapRing W ij)) ⟶
      Spec (.of (projectivePairChartAdditionOutputRing W ij true)) :=
  Spec.map (CommRingCat.ofHom
    (projectivePairChartAdditionOutputOverlapToStandardRing W ij))

/-- Restriction from the secant output `Y` principal open to the exact
`YZ` output overlap. -/
def projectivePairChartAdditionOutputOverlapToInfinity
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    Spec (.of (projectivePairChartAdditionOutputOverlapRing W ij)) ⟶
      Spec (.of (projectivePairChartAdditionOutputRing W ij false)) :=
  Spec.map (CommRingCat.ofHom
    (projectivePairChartAdditionOutputOverlapToInfinityRing W ij))

/-- Both restrictions of the exact `YZ` overlap have the same map into the
ambient projective-pair chart. -/
theorem projectivePairChartAdditionOutputOverlap_open_eq
    (W : WeierstrassCurve K) (ij : Bool × Bool) :
    projectivePairChartAdditionOutputOverlapToStandard W ij ≫
        projectivePairChartAdditionOutputOpen W ij true =
      projectivePairChartAdditionOutputOverlapToInfinity W ij ≫
        projectivePairChartAdditionOutputOpen W ij false := by
  have hring :
      (projectivePairChartAdditionOutputOverlapToStandardRing W ij).comp
          (algebraMap (projectivePairChartCoordinateRing W ij)
            (projectivePairChartAdditionOutputRing W ij true)) =
        (projectivePairChartAdditionOutputOverlapToInfinityRing W ij).comp
          (algebraMap (projectivePairChartCoordinateRing W ij)
            (projectivePairChartAdditionOutputRing W ij false)) := by
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, RingHom.comp_apply,
      projectivePairChartAdditionOutputOverlapToStandardRing_algebraMap,
      projectivePairChartAdditionOutputOverlapToInfinityRing_algebraMap]
  have hmap := congrArg
    (fun f : projectivePairChartCoordinateRing W ij →+*
        projectivePairChartAdditionOutputOverlapRing W ij ↦
      Spec.map (CommRingCat.ofHom f)) hring
  apply (cancel_mono (projectivePairChartIsoSpecTensor W ij).hom).mp
  rw [Category.assoc,
    projectivePairChartAdditionOutputOpen_comp_iso_hom,
    Category.assoc,
    projectivePairChartAdditionOutputOpen_comp_iso_hom]
  rw [projectivePairChartAdditionOutputOverlapToStandard,
    projectivePairChartAdditionOutputOverlapToInfinity,
    ← Spec.map_comp, ← Spec.map_comp]
  exact hmap

private theorem
    projectivePairChartAdditionOutputOverlap_standard_ambient
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    (projectivePairChartAdditionOutputOverlapToStandard W ij ≫
        projectivePairChartAdditionOutputMorphism W ij true) ≫ inclusion W =
      Spec.map (CommRingCat.ofHom
          (projectivePairChartAdditionOutputOverlapToStandardAmbientRing W ij)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
          (MvPolynomial.isHomogeneous_X K 2) zero_lt_one := by
  calc
    _ = projectivePairChartAdditionOutputOverlapToStandard W ij ≫
          Spec.map (CommRingCat.ofHom
            (projectivePairChartAdditionOutputAlgHom W ij true).toRingHom) ≫
          coveringChartAmbientMap W true := by
      rw [projectivePairChartAdditionOutputMorphism, Category.assoc,
        Category.assoc,
        coveringChartMap_comp_inclusion]
    _ = _ := by
      change
        (Spec.map (CommRingCat.ofHom
              (projectivePairChartAdditionOutputOverlapToStandardRing W ij)) ≫
            Spec.map (CommRingCat.ofHom
              (projectivePairChartAdditionOutputAlgHom W ij true).toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (coveringChartIdeal W true)))) ≫
          Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
            (MvPolynomial.isHomogeneous_X K 2) zero_lt_one = _
      simp only [← Spec.map_comp]
      congr 2

private theorem
    projectivePairChartAdditionOutputOverlap_infinity_ambient
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    (projectivePairChartAdditionOutputOverlapToInfinity W ij ≫
        projectivePairChartAdditionOutputMorphism W ij false) ≫ inclusion W =
      Spec.map (CommRingCat.ofHom
          (projectivePairChartAdditionOutputOverlapToInfinityAmbientRing W ij)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
          (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
  calc
    _ = projectivePairChartAdditionOutputOverlapToInfinity W ij ≫
          Spec.map (CommRingCat.ofHom
            (projectivePairChartAdditionOutputAlgHom W ij false).toRingHom) ≫
          coveringChartAmbientMap W false := by
      rw [projectivePairChartAdditionOutputMorphism, Category.assoc,
        Category.assoc,
        coveringChartMap_comp_inclusion]
    _ = _ := by
      change
        (Spec.map (CommRingCat.ofHom
              (projectivePairChartAdditionOutputOverlapToInfinityRing W ij)) ≫
            Spec.map (CommRingCat.ofHom
              (projectivePairChartAdditionOutputAlgHom W ij false).toRingHom) ≫
            Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (coveringChartIdeal W false)))) ≫
          Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
            (MvPolynomial.isHomogeneous_X K 1) zero_lt_one = _
      simp only [← Spec.map_comp]
      congr 2

/-- The `Z`- and `Y`-normalized secant formulas define the same morphism into
the concrete cubic on their exact output-coordinate overlap. -/
theorem projectivePairChartAdditionOutputOverlap_morphisms_eq
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    projectivePairChartAdditionOutputOverlapToStandard W ij ≫
        projectivePairChartAdditionOutputMorphism W ij true =
      projectivePairChartAdditionOutputOverlapToInfinity W ij ≫
        projectivePairChartAdditionOutputMorphism W ij false := by
  apply (cancel_mono (inclusion W)).mp
  rw [projectivePairChartAdditionOutputOverlap_standard_ambient,
    projectivePairChartAdditionOutputOverlap_infinity_ambient]
  exact projectivePairChartAdditionOutputOverlap_ambient_maps_eq W ij

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
