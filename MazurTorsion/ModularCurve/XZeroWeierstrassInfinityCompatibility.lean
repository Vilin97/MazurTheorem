/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassVerticalAdditionMorphism

/-!
# Compatibility of the two infinity charts for Weierstrass addition

The antidiagonal and vertical denominator-cleared formulas both land in the
`Y ≠ 0` chart of the concrete projective cubic.  This file restricts them to
their exact common source `D(Y_anti Y_vert)` and proves equality as actual
scheme morphisms.  The proof uses the polynomial cross-product identities in
`XZeroWeierstrassVerticalAddition`; it does not cancel either slope
denominator and assumes no pointwise group law.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Coordinate ring of the exact intersection of the two infinity-output
charts. -/
abbrev infinityIntersectionCoordinateRing (W : WeierstrassCurve K) :=
  Localization.Away
    (antidiagonalAddYNumerator W * verticalAddYNumerator W)

/-- Restriction from the antidiagonal infinity chart to the common
intersection. -/
noncomputable def antidiagonalToInfinityIntersectionRing
    (W : WeierstrassCurve K) :
    antidiagonalChartCoordinateRing W →+*
      infinityIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayRight
    (S := antidiagonalChartCoordinateRing W)
    (P := infinityIntersectionCoordinateRing W)
    (antidiagonalAddYNumerator W) (verticalAddYNumerator W)

/-- Restriction from the vertical infinity chart to the common
intersection. -/
noncomputable def verticalToInfinityIntersectionRing
    (W : WeierstrassCurve K) :
    verticalChartCoordinateRing W →+*
      infinityIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayLeft
    (S := verticalChartCoordinateRing W)
    (P := infinityIntersectionCoordinateRing W)
    (verticalAddYNumerator W) (antidiagonalAddYNumerator W)

@[simp]
private theorem antidiagonalToInfinityIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    antidiagonalToInfinityIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (antidiagonalChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (infinityIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := antidiagonalChartCoordinateRing W)
    (P := infinityIntersectionCoordinateRing W)
    (antidiagonalAddYNumerator W) (verticalAddYNumerator W) a

@[simp]
private theorem verticalToInfinityIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    verticalToInfinityIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (verticalChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (infinityIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := verticalChartCoordinateRing W)
    (P := infinityIntersectionCoordinateRing W)
    (verticalAddYNumerator W) (antidiagonalAddYNumerator W) a

private theorem infinityIntersection_XOverY_eq
    (W : WeierstrassCurve K) :
    antidiagonalToInfinityIntersectionRing W
        (antidiagonalChartXOverY W) =
      verticalToInfinityIntersectionRing W (verticalChartXOverY W) := by
  let f := antidiagonalToInfinityIntersectionRing W
  let g := verticalToInfinityIntersectionRing W
  let Xa := f (antidiagonalChartHomogeneousX W)
  let Ya := f (antidiagonalChartHomogeneousY W)
  let ia := f (IsLocalization.Away.invSelf
    (S := antidiagonalChartCoordinateRing W)
      (antidiagonalAddYNumerator W))
  let Xv := g (verticalChartHomogeneousX W)
  let Yv := g (verticalChartHomogeneousY W)
  let iv := g (IsLocalization.Away.invSelf
    (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  have hYa : Ya * ia = 1 := by
    dsimp only [Ya, ia, f]
    simpa only [antidiagonalChartHomogeneousY, map_mul, map_one] using
      congrArg (antidiagonalToInfinityIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
        (S := antidiagonalChartCoordinateRing W)
          (antidiagonalAddYNumerator W))
  have hYv : Yv * iv = 1 := by
    dsimp only [Yv, iv, g]
    simpa only [verticalChartHomogeneousY, map_mul, map_one] using
      congrArg (verticalToInfinityIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
        (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  have hcross : Xa * Yv = Xv * Ya := by
    have h := congrArg
      (algebraMap (secantPairCoordinateRing W)
        (infinityIntersectionCoordinateRing W))
      (antidiagonalVertical_homogeneousX_mul_Y W)
    simpa only [Xa, Ya, Xv, Yv, f, g,
      antidiagonalChartHomogeneousX, antidiagonalChartHomogeneousY,
      verticalChartHomogeneousX, verticalChartHomogeneousY, map_mul,
      antidiagonalToInfinityIntersectionRing_algebraMap,
      verticalToInfinityIntersectionRing_algebraMap] using h
  simp only [antidiagonalChartXOverY, verticalChartXOverY, map_mul]
  change Xa * ia = Xv * iv
  calc
    Xa * ia = Xa * ia * (Yv * iv) := by rw [hYv, mul_one]
    _ = (Xa * Yv) * (ia * iv) := by ring
    _ = (Xv * Ya) * (ia * iv) := by rw [hcross]
    _ = Xv * iv * (Ya * ia) := by ring
    _ = Xv * iv := by rw [hYa, mul_one]

private theorem infinityIntersection_ZOverY_eq
    (W : WeierstrassCurve K) :
    antidiagonalToInfinityIntersectionRing W
        (antidiagonalChartZOverY W) =
      verticalToInfinityIntersectionRing W (verticalChartZOverY W) := by
  let f := antidiagonalToInfinityIntersectionRing W
  let g := verticalToInfinityIntersectionRing W
  let Za := f (antidiagonalChartHomogeneousZ W)
  let Ya := f (antidiagonalChartHomogeneousY W)
  let ia := f (IsLocalization.Away.invSelf
    (S := antidiagonalChartCoordinateRing W)
      (antidiagonalAddYNumerator W))
  let Zv := g (verticalChartHomogeneousZ W)
  let Yv := g (verticalChartHomogeneousY W)
  let iv := g (IsLocalization.Away.invSelf
    (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  have hYa : Ya * ia = 1 := by
    dsimp only [Ya, ia, f]
    simpa only [antidiagonalChartHomogeneousY, map_mul, map_one] using
      congrArg (antidiagonalToInfinityIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
        (S := antidiagonalChartCoordinateRing W)
          (antidiagonalAddYNumerator W))
  have hYv : Yv * iv = 1 := by
    dsimp only [Yv, iv, g]
    simpa only [verticalChartHomogeneousY, map_mul, map_one] using
      congrArg (verticalToInfinityIntersectionRing W)
        (IsLocalization.Away.mul_invSelf
        (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  have hcross : Za * Yv = Zv * Ya := by
    have h := congrArg
      (algebraMap (secantPairCoordinateRing W)
        (infinityIntersectionCoordinateRing W))
      (antidiagonalVertical_homogeneousZ_mul_Y W)
    simpa only [Za, Ya, Zv, Yv, f, g,
      antidiagonalChartHomogeneousZ, antidiagonalChartHomogeneousY,
      verticalChartHomogeneousZ, verticalChartHomogeneousY, map_mul,
      antidiagonalToInfinityIntersectionRing_algebraMap,
      verticalToInfinityIntersectionRing_algebraMap] using h
  simp only [antidiagonalChartZOverY, verticalChartZOverY, map_mul]
  change Za * ia = Zv * iv
  calc
    Za * ia = Za * ia * (Yv * iv) := by rw [hYv, mul_one]
    _ = (Za * Yv) * (ia * iv) := by ring
    _ = (Zv * Ya) * (ia * iv) := by rw [hcross]
    _ = Zv * iv * (Ya * ia) := by ring
    _ = Zv * iv := by rw [hYa, mul_one]

private theorem infinityIntersection_ring_maps_eq
    (W : WeierstrassCurve K) :
    (antidiagonalToInfinityIntersectionRing W).comp
        (antidiagonalAdditionToInfinityRing W) =
      (verticalToInfinityIntersectionRing W).comp
        (verticalAdditionToInfinityRing W) := by
  apply Ideal.Quotient.ringHom_ext
  apply chartRingHom_ext (K := K) (coveringCoordinate false)
  · ext a
    change antidiagonalToInfinityIntersectionRing W
        (antidiagonalAdditionToInfinityRing W
          (coveringChartStructureRingHom W false a)) =
      verticalToInfinityIntersectionRing W
        (verticalAdditionToInfinityRing W
          (coveringChartStructureRingHom W false a))
    simp only [antidiagonalAdditionToInfinityRing_coefficient,
      verticalAdditionToInfinityRing_coefficient,
      antidiagonalChartCoefficientHom, verticalChartCoefficientHom,
      RingHom.comp_apply,
      antidiagonalToInfinityIntersectionRing_algebraMap,
      verticalToInfinityIntersectionRing_algebraMap]
  · intro j
    simp only [coveringCoordinate] at *
    fin_cases j
    · change antidiagonalToInfinityIntersectionRing W
        (antidiagonalAdditionToInfinityRing W
            (Ideal.Quotient.mk (coveringChartIdeal W false)
              (coordinateChartRatio (K := K) 1 0))) =
        verticalToInfinityIntersectionRing W
          (verticalAdditionToInfinityRing W
            (Ideal.Quotient.mk (coveringChartIdeal W false)
              (coordinateChartRatio (K := K) 1 0)))
      simpa only [antidiagonalAdditionToInfinityRing_outerX,
        verticalAdditionToInfinityRing_outerX] using
        infinityIntersection_XOverY_eq W
    · change antidiagonalToInfinityIntersectionRing W
        (antidiagonalAdditionToInfinityRing W
            (Ideal.Quotient.mk (coveringChartIdeal W false)
              (coordinateChartRatio (K := K) 1 1))) =
        verticalToInfinityIntersectionRing W
          (verticalAdditionToInfinityRing W
            (Ideal.Quotient.mk (coveringChartIdeal W false)
              (coordinateChartRatio (K := K) 1 1)))
      have hself :
          (coordinateChartRatio (K := K) 1 1 :
            coveringChartRing K false) = 1 := by
        rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio
            (K := K) 1 1,
          isLocalizationElem_self_degree_one]
      have hquotient :
          Ideal.Quotient.mk (coveringChartIdeal W false)
              (coordinateChartRatio (K := K) 1 1 :
                coveringChartRing K false) = 1 := by
        calc
          _ = Ideal.Quotient.mk (coveringChartIdeal W false)
              (1 : coveringChartRing K false) := congrArg
                (Ideal.Quotient.mk (coveringChartIdeal W false)) hself
          _ = 1 := (Ideal.Quotient.mk
            (coveringChartIdeal W false)).map_one
      rw [hquotient]
      simp only [map_one]
    · change antidiagonalToInfinityIntersectionRing W
        (antidiagonalAdditionToInfinityRing W
            (Ideal.Quotient.mk (coveringChartIdeal W false)
              (coordinateChartRatio (K := K) 1 2))) =
        verticalToInfinityIntersectionRing W
          (verticalAdditionToInfinityRing W
            (Ideal.Quotient.mk (coveringChartIdeal W false)
              (coordinateChartRatio (K := K) 1 2)))
      simpa only [antidiagonalAdditionToInfinityRing_innerX,
        verticalAdditionToInfinityRing_innerX] using
        infinityIntersection_ZOverY_eq W

/-- Restriction from the exact common infinity overlap to the antidiagonal
chart. -/
def infinityIntersectionToAntidiagonalChart (W : WeierstrassCurve K) :
    Spec (.of (infinityIntersectionCoordinateRing W)) ⟶
      Spec (.of (antidiagonalChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (antidiagonalToInfinityIntersectionRing W))

/-- Restriction from the exact common infinity overlap to the vertical
chart. -/
def infinityIntersectionToVerticalChart (W : WeierstrassCurve K) :
    Spec (.of (infinityIntersectionCoordinateRing W)) ⟶
      Spec (.of (verticalChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (verticalToInfinityIntersectionRing W))

/-- The antidiagonal and vertical infinity formulas agree as actual
morphisms into the concrete projective cubic on `D(Y_anti Y_vert)`. -/
theorem infinityIntersection_additionProjective_eq
    (W : WeierstrassCurve K) :
    infinityIntersectionToAntidiagonalChart W ≫
        antidiagonalAdditionProjectiveMorphism W =
      infinityIntersectionToVerticalChart W ≫
        verticalAdditionProjectiveMorphism W := by
  have hinfinity :
      infinityIntersectionToAntidiagonalChart W ≫
          antidiagonalAdditionInfinityMorphism W =
        infinityIntersectionToVerticalChart W ≫
          verticalAdditionInfinityMorphism W := by
    have hmap := congrArg
      (fun f : coveringChartCoordinateRing W false →+*
          infinityIntersectionCoordinateRing W =>
        Spec.map (CommRingCat.ofHom f))
      (infinityIntersection_ring_maps_eq W)
    rw [infinityIntersectionToAntidiagonalChart,
      infinityIntersectionToVerticalChart,
      antidiagonalAdditionInfinityMorphism,
      verticalAdditionInfinityMorphism, ← Spec.map_comp, ← Spec.map_comp]
    exact hmap
  simpa only [antidiagonalAdditionProjectiveMorphism,
    verticalAdditionProjectiveMorphism, Category.assoc] using
      congrArg (fun f => f ≫ coveringChartMap W false) hinfinity

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
