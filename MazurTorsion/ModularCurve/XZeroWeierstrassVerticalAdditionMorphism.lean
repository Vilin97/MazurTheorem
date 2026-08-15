/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassAntidiagonalAdditionMorphism
import MazurTorsion.ModularCurve.XZeroWeierstrassVerticalAddition

/-!
# The vertical infinity chart of Weierstrass addition

The ordinary secant formula on `D(x₁ - x₂)` admits the denominator-cleared
homogeneous extension `[D X : Y : D³]`.  On `D(Y)` this file turns that
extension into an actual morphism to the `Y ≠ 0` chart of the concrete reduced
projective Weierstrass cubic.  It then proves equality with the ordinary
secant morphism on the exact intersection `D((x₁ - x₂)Y)`.

No group object, point equivalence, or supplied addition compatibility is an
input.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Localization map from the vertical infinity chart into the affine-pair
coordinate scheme. -/
def verticalChartToPair (W : WeierstrassCurve K) :
    Spec (.of (verticalChartCoordinateRing W)) ⟶
      Spec (.of (secantPairCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (verticalChartCoordinateRing W)))

instance verticalChartToPair_isOpenImmersion (W : WeierstrassCurve K) :
    IsOpenImmersion (verticalChartToPair W) := by
  dsimp only [verticalChartToPair, verticalChartCoordinateRing]
  infer_instance

/-- The vertical infinity localization has exactly the range `D(Y)`. -/
theorem verticalChartToPair_opensRange (W : WeierstrassCurve K) :
    (verticalChartToPair W).opensRange =
      PrimeSpectrum.basicOpen (verticalAddYNumerator W) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (Localization.Away (verticalAddYNumerator W))))).opensRange = _
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (secantPairCoordinateRing W)) (verticalAddYNumerator W)

/-- The ordinary secant chart and the vertical infinity chart cover the
principal open `D(C₁₂)`, where `C₁₂ = y₁ - y₂`. -/
theorem verticalAdditionA_basicOpen_le_secant_sup_vertical
    (W : WeierstrassCurve K) :
    PrimeSpectrum.basicOpen (verticalAdditionA W) ≤
      PrimeSpectrum.basicOpen (secantDenominator W) ⊔
        PrimeSpectrum.basicOpen (verticalAddYNumerator W) := by
  intro p hpA
  change verticalAdditionA W ∉ p.asIdeal at hpA
  change secantDenominator W ∉ p.asIdeal ∨
    verticalAddYNumerator W ∉ p.asIdeal
  by_cases hB : secantDenominator W ∈ p.asIdeal
  · right
    intro hY
    have hright :
        verticalAdditionB W *
            (-2 * secantPairCoefficientHom W W.a₁ *
                verticalAdditionA W ^ 2 +
              verticalAdditionA W *
                ((secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                    secantPairX₂ W) -
                  secantPairCoefficientHom W W.a₁ ^ 2 +
                    secantPairX₁ W) * verticalAdditionB W +
              (secantPairCoefficientHom W W.a₁ *
                  (secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                    secantPairX₂ W) -
                (secantPairY₁ W + secantPairCoefficientHom W W.a₃)) *
                  verticalAdditionB W ^ 2) ∈ p.asIdeal := by
      apply p.asIdeal.mul_mem_right
      simpa [verticalAdditionB, secantDenominator] using hB
    have hleft :
        verticalAddYNumerator W + verticalAdditionA W ^ 3 ∈ p.asIdeal := by
      rw [verticalAddYNumerator_add_A_cube]
      exact hright
    have hpow : verticalAdditionA W ^ 3 ∈ p.asIdeal := by
      simpa using p.asIdeal.sub_mem hleft hY
    exact hpA ((show p.asIdeal.IsPrime from inferInstance).mem_of_pow_mem 3 hpow)
  · exact Or.inl hB

/-! ## The exact overlap with the ordinary secant chart -/

/-- Coordinate ring of `D((x₁-x₂)Y)`, the exact intersection of the ordinary
secant and vertical infinity charts. -/
abbrev secantVerticalIntersectionCoordinateRing (W : WeierstrassCurve K) :=
  Localization.Away (secantDenominator W * verticalAddYNumerator W)

/-- Restriction from the ordinary secant chart to the exact intersection. -/
noncomputable def secantToVerticalIntersectionRing
    (W : WeierstrassCurve K) :
    secantChartCoordinateRing W →+* secantVerticalIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayRight
    (S := secantChartCoordinateRing W)
    (P := secantVerticalIntersectionCoordinateRing W)
    (secantDenominator W) (verticalAddYNumerator W)

/-- Restriction from the vertical infinity chart to the exact intersection. -/
noncomputable def verticalChartToIntersectionRing
    (W : WeierstrassCurve K) :
    verticalChartCoordinateRing W →+*
      secantVerticalIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayLeft
    (S := verticalChartCoordinateRing W)
    (P := secantVerticalIntersectionCoordinateRing W)
    (verticalAddYNumerator W) (secantDenominator W)

@[simp]
private theorem secantToVerticalIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    secantToVerticalIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (secantVerticalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := secantChartCoordinateRing W)
    (P := secantVerticalIntersectionCoordinateRing W)
    (secantDenominator W) (verticalAddYNumerator W) a

@[simp]
private theorem verticalChartToIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    verticalChartToIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (verticalChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (secantVerticalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := verticalChartCoordinateRing W)
    (P := secantVerticalIntersectionCoordinateRing W)
    (verticalAddYNumerator W) (secantDenominator W) a

/-- The exact overlap is the intersection `D(x₁-x₂) ∩ D(Y)`. -/
theorem secantVerticalIntersection_basicOpen (W : WeierstrassCurve K) :
    PrimeSpectrum.basicOpen
        (secantDenominator W * verticalAddYNumerator W) =
      PrimeSpectrum.basicOpen (secantDenominator W) ⊓
        PrimeSpectrum.basicOpen (verticalAddYNumerator W) :=
  PrimeSpectrum.basicOpen_mul _ _

private theorem secantAddX_cleared_on_verticalIntersection
    (W : WeierstrassCurve K) :
    secantToVerticalIntersectionRing W (secantChartAddX W) *
        algebraMap (secantPairCoordinateRing W)
            (secantVerticalIntersectionCoordinateRing W)
            (secantDenominator W) ^ 2 =
      algebraMap (secantPairCoordinateRing W)
        (secantVerticalIntersectionCoordinateRing W)
        (verticalAddXNumerator W) := by
  have h := congrArg (secantToVerticalIntersectionRing W)
    (secantChartAddX_mul_verticalB_sq W)
  simpa only [map_mul, map_pow,
    secantToVerticalIntersectionRing_algebraMap,
    show verticalAdditionB W = secantDenominator W by rfl] using h

private theorem secantAddY_cleared_on_verticalIntersection
    (W : WeierstrassCurve K) :
    secantToVerticalIntersectionRing W (secantChartAddY W) *
        algebraMap (secantPairCoordinateRing W)
            (secantVerticalIntersectionCoordinateRing W)
            (secantDenominator W) ^ 3 =
      algebraMap (secantPairCoordinateRing W)
        (secantVerticalIntersectionCoordinateRing W)
        (verticalAddYNumerator W) := by
  have h := congrArg (secantToVerticalIntersectionRing W)
    (secantChartAddY_mul_verticalB_cube W)
  simpa only [map_mul, map_pow,
    secantToVerticalIntersectionRing_algebraMap,
    show verticalAdditionB W = secantDenominator W by rfl] using h

private theorem verticalYNumerator_mul_invSelf_on_intersection
    (W : WeierstrassCurve K) :
    algebraMap (secantPairCoordinateRing W)
          (secantVerticalIntersectionCoordinateRing W)
          (verticalAddYNumerator W) *
        verticalChartToIntersectionRing W
          (IsLocalization.Away.invSelf (verticalAddYNumerator W)) = 1 := by
  have h := congrArg (verticalChartToIntersectionRing W)
    (IsLocalization.Away.mul_invSelf
      (S := verticalChartCoordinateRing W) (verticalAddYNumerator W))
  simpa only [map_mul, map_one,
    verticalChartToIntersectionRing_algebraMap] using h

/-- On the exact overlap, the vertical `X/Y` coordinate is the ratio of the
ordinary affine output coordinates. -/
theorem verticalXOverY_mul_secantAddY_on_intersection
    (W : WeierstrassCurve K) :
    verticalChartToIntersectionRing W (verticalChartXOverY W) *
        secantToVerticalIntersectionRing W (secantChartAddY W) =
      secantToVerticalIntersectionRing W (secantChartAddX W) := by
  have hX := secantAddX_cleared_on_verticalIntersection W
  have hY := secantAddY_cleared_on_verticalIntersection W
  have hYinv := verticalYNumerator_mul_invSelf_on_intersection W
  simp only [verticalChartXOverY, verticalChartHomogeneousX, map_mul] at ⊢
  simp only [verticalChartToIntersectionRing_algebraMap]
  rw [show verticalAdditionB W = secantDenominator W by rfl]
  calc
    _ = secantToVerticalIntersectionRing W (secantChartAddX W) *
        ((secantToVerticalIntersectionRing W (secantChartAddY W) *
            algebraMap (secantPairCoordinateRing W)
              (secantVerticalIntersectionCoordinateRing W)
              (secantDenominator W) ^ 3) *
          verticalChartToIntersectionRing W
            (IsLocalization.Away.invSelf (verticalAddYNumerator W))) := by
      rw [← hX]
      ring
    _ = secantToVerticalIntersectionRing W (secantChartAddX W) := by
      rw [hY, hYinv, mul_one]

/-- On the exact overlap, the vertical `Z/Y` coordinate times the ordinary
affine ordinate is one. -/
theorem verticalZOverY_mul_secantAddY_on_intersection
    (W : WeierstrassCurve K) :
    verticalChartToIntersectionRing W (verticalChartZOverY W) *
        secantToVerticalIntersectionRing W (secantChartAddY W) = 1 := by
  have hY := secantAddY_cleared_on_verticalIntersection W
  have hYinv := verticalYNumerator_mul_invSelf_on_intersection W
  simp only [verticalChartZOverY, verticalChartHomogeneousZ, map_mul] at ⊢
  simp only [verticalChartToIntersectionRing_algebraMap, map_pow]
  rw [show verticalAdditionB W = secantDenominator W by rfl]
  calc
    _ = (secantToVerticalIntersectionRing W (secantChartAddY W) *
          algebraMap (secantPairCoordinateRing W)
            (secantVerticalIntersectionCoordinateRing W)
            (secantDenominator W) ^ 3) *
        verticalChartToIntersectionRing W
          (IsLocalization.Away.invSelf (verticalAddYNumerator W)) := by ring
    _ = 1 := by rw [hY, hYinv]

/-! ## Equality in the common projective target overlap -/

private noncomputable def secantVerticalIntersectionToStandardAmbientRing
    (W : WeierstrassCurve K) :
    HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 2) →+* secantVerticalIntersectionCoordinateRing W :=
  (secantToVerticalIntersectionRing W).comp
    ((secantAdditionToAffineRing W).comp
      ((affineEquationToStandardChartRingEquiv W).symm.toRingHom.comp
        (Ideal.Quotient.mk (coveringChartIdeal W true))))

private noncomputable def secantVerticalIntersectionToInfinityAmbientRing
    (W : WeierstrassCurve K) :
    HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 1) →+* secantVerticalIntersectionCoordinateRing W :=
  (verticalChartToIntersectionRing W).comp
    ((verticalAdditionToInfinityRing W).comp
      (Ideal.Quotient.mk (coveringChartIdeal W false)))

@[simp]
private theorem secantVerticalStandardAmbient_constant
    (W : WeierstrassCurve K) (a : K) :
    secantVerticalIntersectionToStandardAmbientRing W
        (coordinateChartConstantHom (K := K) 2 a) =
      algebraMap (secantPairCoordinateRing W)
        (secantVerticalIntersectionCoordinateRing W)
        (secantPairCoefficientHom W a) := by
  change secantToVerticalIntersectionRing W
      (secantAdditionToAffineRing W
        ((affineEquationToStandardChartRingEquiv W).symm
          (Ideal.Quotient.mk (standardChartIdeal W)
            (coordinateChartConstantHom (K := K) 2 a)))) = _
  rw [standardChartQuotientEquivSymm_constant,
    secantAdditionToAffineRing_coefficient]
  change secantToVerticalIntersectionRing W
      (algebraMap (secantPairCoordinateRing W)
        (secantChartCoordinateRing W) (secantPairCoefficientHom W a)) = _
  exact secantToVerticalIntersectionRing_algebraMap W _

@[simp]
private theorem secantVerticalStandardAmbient_outerX
    (W : WeierstrassCurve K) :
    secantVerticalIntersectionToStandardAmbientRing W
        (coordinateChartRatio (K := K) 2 0) =
      secantToVerticalIntersectionRing W (secantChartAddX W) := by
  change secantToVerticalIntersectionRing W
      (secantAdditionToAffineRing W
        ((affineEquationToStandardChartRingEquiv W).symm
          (Ideal.Quotient.mk (standardChartIdeal W)
            (coordinateChartRatio (K := K) 2 0)))) = _
  rw [standardChartQuotientEquivSymm_outerX]
  exact congrArg (secantToVerticalIntersectionRing W)
    (secantAdditionToAffineRing_abscissa W)

@[simp]
private theorem secantVerticalStandardAmbient_innerX
    (W : WeierstrassCurve K) :
    secantVerticalIntersectionToStandardAmbientRing W
        (coordinateChartRatio (K := K) 2 1) =
      secantToVerticalIntersectionRing W (secantChartAddY W) := by
  change secantToVerticalIntersectionRing W
      (secantAdditionToAffineRing W
        ((affineEquationToStandardChartRingEquiv W).symm
          (Ideal.Quotient.mk (standardChartIdeal W)
            (coordinateChartRatio (K := K) 2 1)))) = _
  rw [standardChartQuotientEquivSymm_innerX]
  exact congrArg (secantToVerticalIntersectionRing W)
    (secantAdditionToAffineRing_ordinate W)

private theorem secantVerticalStandardAmbient_innerX_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (secantVerticalIntersectionToStandardAmbientRing W
      (coordinateChartRatio (K := K) 2 1)) := by
  rw [secantVerticalStandardAmbient_innerX]
  have hBY : IsUnit
      (algebraMap (secantPairCoordinateRing W)
        (secantVerticalIntersectionCoordinateRing W)
        (secantDenominator W * verticalAddYNumerator W)) :=
    IsLocalization.Away.algebraMap_isUnit
      (secantDenominator W * verticalAddYNumerator W)
  rw [map_mul] at hBY
  have hY : IsUnit
      (algebraMap (secantPairCoordinateRing W)
        (secantVerticalIntersectionCoordinateRing W)
        (verticalAddYNumerator W)) :=
    isUnit_of_mul_isUnit_right hBY
  have hcleared := secantAddY_cleared_on_verticalIntersection W
  have hproduct : IsUnit
      (secantToVerticalIntersectionRing W (secantChartAddY W) *
        algebraMap (secantPairCoordinateRing W)
          (secantVerticalIntersectionCoordinateRing W)
          (secantDenominator W) ^ 3) := by
    rw [hcleared]
    exact hY
  exact isUnit_of_mul_isUnit_left hproduct

@[simp]
private theorem secantVerticalInfinityAmbient_constant
    (W : WeierstrassCurve K) (a : K) :
    secantVerticalIntersectionToInfinityAmbientRing W
        (coordinateChartConstantHom (K := K) 1 a) =
      algebraMap (secantPairCoordinateRing W)
        (secantVerticalIntersectionCoordinateRing W)
        (secantPairCoefficientHom W a) := by
  change verticalChartToIntersectionRing W
      (verticalAdditionToInfinityRing W
        (coveringChartStructureRingHom W false a)) = _
  rw [verticalAdditionToInfinityRing_coefficient]
  exact verticalChartToIntersectionRing_algebraMap W _

@[simp]
private theorem secantVerticalInfinityAmbient_outerX
    (W : WeierstrassCurve K) :
    secantVerticalIntersectionToInfinityAmbientRing W
        (coordinateChartRatio (K := K) 1 0) =
      verticalChartToIntersectionRing W (verticalChartXOverY W) := by
  change verticalChartToIntersectionRing W
      (verticalAdditionToInfinityRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 0))) = _
  rw [verticalAdditionToInfinityRing_outerX]

@[simp]
private theorem secantVerticalInfinityAmbient_innerX
    (W : WeierstrassCurve K) :
    secantVerticalIntersectionToInfinityAmbientRing W
        (coordinateChartRatio (K := K) 1 2) =
      verticalChartToIntersectionRing W (verticalChartZOverY W) := by
  change verticalChartToIntersectionRing W
      (verticalAdditionToInfinityRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2))) = _
  rw [verticalAdditionToInfinityRing_innerX]

private theorem secantVertical_ambient_maps_eq
    (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
          (secantVerticalIntersectionToStandardAmbientRing W)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
          (MvPolynomial.isHomogeneous_X K 2) zero_lt_one =
      Spec.map (CommRingCat.ofHom
          (secantVerticalIntersectionToInfinityAmbientRing W)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
          (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
  apply projectiveYZOverlap_ambient_maps_eq
  · intro a
    rw [secantVerticalStandardAmbient_constant,
      secantVerticalInfinityAmbient_constant]
  · exact secantVerticalStandardAmbient_innerX_isUnit W
  · rw [secantVerticalInfinityAmbient_outerX,
      secantVerticalStandardAmbient_innerX,
      secantVerticalStandardAmbient_outerX]
    exact verticalXOverY_mul_secantAddY_on_intersection W
  · rw [secantVerticalInfinityAmbient_innerX,
      secantVerticalStandardAmbient_innerX]
    exact verticalZOverY_mul_secantAddY_on_intersection W

/-! ## The actual vertical projective morphism -/

/-- Restriction from the exact overlap to the ordinary secant chart. -/
def secantVerticalIntersectionToSecantChart (W : WeierstrassCurve K) :
    Spec (.of (secantVerticalIntersectionCoordinateRing W)) ⟶
      Spec (.of (secantChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (secantToVerticalIntersectionRing W))

/-- Restriction from the exact overlap to the vertical infinity chart. -/
def secantVerticalIntersectionToVerticalChart (W : WeierstrassCurve K) :
    Spec (.of (secantVerticalIntersectionCoordinateRing W)) ⟶
      Spec (.of (verticalChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (verticalChartToIntersectionRing W))

/-- Structure morphism of the vertical infinity chart. -/
def verticalChartStructureMap (W : WeierstrassCurve K) :
    Spec (.of (verticalChartCoordinateRing W)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (verticalChartCoefficientHom W))

/-- The normalized vertical formula as a morphism into the actual `Y ≠ 0`
chart. -/
def verticalAdditionInfinityMorphism (W : WeierstrassCurve K) :
    Spec (.of (verticalChartCoordinateRing W)) ⟶
      coveringChartScheme W false :=
  Spec.map (CommRingCat.ofHom (verticalAdditionToInfinityRing W))

/-- The vertical infinity morphism lies over the ground field. -/
@[reassoc]
theorem verticalAdditionInfinityMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    verticalAdditionInfinityMorphism W ≫
        Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W false)) =
      verticalChartStructureMap W := by
  rw [verticalAdditionInfinityMorphism, verticalChartStructureMap,
    ← Spec.map_comp, Spec.map_inj, ← CommRingCat.ofHom_comp]
  congr 1
  exact verticalAdditionToInfinityRing_comp_coefficient W

/-- The vertical formula as an actual morphism into the concrete reduced
projective Weierstrass cubic. -/
def verticalAdditionProjectiveMorphism (W : WeierstrassCurve K) :
    Spec (.of (verticalChartCoordinateRing W)) ⟶ scheme W :=
  verticalAdditionInfinityMorphism W ≫ coveringChartMap W false

/-- Projective vertical addition respects the structural maps. -/
theorem verticalAdditionProjectiveMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    verticalAdditionProjectiveMorphism W ≫ structureMap W =
      verticalChartStructureMap W := by
  have hchart : coveringChartMap W false ≫ structureMap W =
      Spec.map (CommRingCat.ofHom
        (coveringChartStructureRingHom W false)) :=
    coveringChartMap_comp_structureMap W false
  simp only [verticalAdditionProjectiveMorphism, Category.assoc,
    hchart, verticalAdditionInfinityMorphism_comp_structureMap]

private theorem secantVerticalIntersection_secant_ambient
    (W : WeierstrassCurve K) :
    (secantVerticalIntersectionToSecantChart W ≫
        secantAdditionProjectiveMorphism W) ≫ inclusion W =
      Spec.map (CommRingCat.ofHom
          (secantVerticalIntersectionToStandardAmbientRing W)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
          (MvPolynomial.isHomogeneous_X K 2) zero_lt_one := by
  calc
    _ = secantVerticalIntersectionToSecantChart W ≫
          secantAdditionAffineMorphism W ≫
          (affineEquationSchemeIsoStandardChart W).hom ≫
          coveringChartAmbientMap W true := by
            simpa only [Category.assoc] using congrArg
              (fun f => secantVerticalIntersectionToSecantChart W ≫ f)
              (secantAdditionProjectiveMorphism_comp_inclusion W)
    _ = _ := by
      change
        (Spec.map (CommRingCat.ofHom
              (secantToVerticalIntersectionRing W)) ≫
            Spec.map (CommRingCat.ofHom
              (secantAdditionToAffineRing W)) ≫
            Spec.map
              (affineEquationToStandardChartRingEquiv W).toCommRingCatIso.symm.hom ≫
            Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (coveringChartIdeal W true)))) ≫
          Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
            (MvPolynomial.isHomogeneous_X K 2) zero_lt_one = _
      simp only [← Spec.map_comp]
      congr 2

private theorem secantVerticalIntersection_vertical_ambient
    (W : WeierstrassCurve K) :
    (secantVerticalIntersectionToVerticalChart W ≫
        verticalAdditionProjectiveMorphism W) ≫ inclusion W =
      Spec.map (CommRingCat.ofHom
          (secantVerticalIntersectionToInfinityAmbientRing W)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
          (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
  calc
    _ = secantVerticalIntersectionToVerticalChart W ≫
          verticalAdditionInfinityMorphism W ≫
          coveringChartAmbientMap W false := by
            simpa only [verticalAdditionProjectiveMorphism,
              Category.assoc] using congrArg
              (fun f => secantVerticalIntersectionToVerticalChart W ≫
                verticalAdditionInfinityMorphism W ≫ f)
              (coveringChartMap_comp_inclusion W false)
    _ = _ := by
      change
        (Spec.map (CommRingCat.ofHom
              (verticalChartToIntersectionRing W)) ≫
            Spec.map (CommRingCat.ofHom
              (verticalAdditionToInfinityRing W)) ≫
            Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (coveringChartIdeal W false)))) ≫
          Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
            (MvPolynomial.isHomogeneous_X K 1) zero_lt_one = _
      simp only [← Spec.map_comp]
      congr 2

/-- The ordinary secant formula and its vertical infinity extension are the
same morphism into the concrete reduced projective cubic on their exact
intersection `D((x₁-x₂)Y)`. -/
theorem secantVerticalIntersection_additionProjective_eq
    (W : WeierstrassCurve K) :
    secantVerticalIntersectionToSecantChart W ≫
        secantAdditionProjectiveMorphism W =
      secantVerticalIntersectionToVerticalChart W ≫
        verticalAdditionProjectiveMorphism W := by
  apply (cancel_mono (inclusion W)).mp
  rw [secantVerticalIntersection_secant_ambient,
    secantVerticalIntersection_vertical_ambient]
  exact secantVertical_ambient_maps_eq W

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
