/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassAntidiagonalAddition

/-!
# The infinity-output morphism of Weierstrass addition

The denominator-cleared antidiagonal formula gives homogeneous coordinates
`[B₁₂X : Y : B₁₂³]`.  On the principal open `D(Y)` this file normalizes by
the actual unit `Y` and maps into the concrete `Y ≠ 0` chart of the reduced
projective Weierstrass cubic.

This is a genuine scheme morphism and a named cross-module consumer of the
antidiagonal coordinate-ring map.  It does not assume a group object, a point
equivalence, or a supplied addition law.  Gluing it to the existing
`D(B₁₂)` morphism is a separate step below this boundary.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- Localization map from the infinity-output chart into the affine-pair
coordinate scheme. -/
def antidiagonalChartToPair (W : WeierstrassCurve K) :
    Spec (.of (antidiagonalChartCoordinateRing W)) ⟶
      Spec (.of (secantPairCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (antidiagonalChartCoordinateRing W)))

instance antidiagonalChartToPair_isOpenImmersion
    (W : WeierstrassCurve K) :
    IsOpenImmersion (antidiagonalChartToPair W) := by
  dsimp only [antidiagonalChartToPair, antidiagonalChartCoordinateRing]
  infer_instance

/-- The infinity-output localization has exactly the range `D(Y)`. -/
theorem antidiagonalChartToPair_opensRange (W : WeierstrassCurve K) :
    (antidiagonalChartToPair W).opensRange =
      PrimeSpectrum.basicOpen (antidiagonalAddYNumerator W) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (Localization.Away (antidiagonalAddYNumerator W))))).opensRange = _
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (secantPairCoordinateRing W))
      (antidiagonalAddYNumerator W)

/-- The existing `D(B₁₂)` chart and the infinity-output `D(Y)` chart cover
the entire principal open `D(A₁₂)`.  This is the first genuine coverage
statement across inverse pairs. -/
theorem additionA12_basicOpen_le_productNeighborhood_sup_antidiagonal
    (W : WeierstrassCurve K) :
    PrimeSpectrum.basicOpen (additionA12 W) ≤
      PrimeSpectrum.basicOpen (additionB12 W) ⊔
        PrimeSpectrum.basicOpen (antidiagonalAddYNumerator W) := by
  intro p hpA
  change additionA12 W ∉ p.asIdeal at hpA
  change additionB12 W ∉ p.asIdeal ∨
    antidiagonalAddYNumerator W ∉ p.asIdeal
  by_cases hB : additionB12 W ∈ p.asIdeal
  · right
    intro hY
    have hright :
        additionB12 W *
            (-2 * secantPairCoefficientHom W W.a₁ * additionA12 W ^ 2 +
              additionA12 W *
                ((secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                    secantPairX₂ W) -
                  secantPairCoefficientHom W W.a₁ ^ 2 + secantPairX₁ W) *
                additionB12 W +
              (secantPairCoefficientHom W W.a₁ *
                  (secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                    secantPairX₂ W) -
                (secantPairY₁ W + secantPairCoefficientHom W W.a₃)) *
                additionB12 W ^ 2) ∈ p.asIdeal :=
      p.asIdeal.mul_mem_right _ hB
    have hleft :
        antidiagonalAddYNumerator W + additionA12 W ^ 3 ∈ p.asIdeal := by
      rw [antidiagonalAddYNumerator_add_A12_cube]
      exact hright
    have hpow : additionA12 W ^ 3 ∈ p.asIdeal := by
      simpa using p.asIdeal.sub_mem hleft hY
    exact hpA ((show p.asIdeal.IsPrime from inferInstance).mem_of_pow_mem 3 hpow)
  · exact Or.inl hB

/-! ## The exact overlap with `D(B₁₂)` -/

/-- Coordinate ring of `D(B₁₂Y)`, the exact intersection of the affine
product-neighbourhood and infinity-output charts. -/
abbrev productAntidiagonalIntersectionCoordinateRing
    (W : WeierstrassCurve K) :=
  Localization.Away (additionB12 W * antidiagonalAddYNumerator W)

/-- Restriction from `D(B₁₂)` to `D(B₁₂Y)`. -/
noncomputable def productNeighborhoodToAntidiagonalIntersectionRing
    (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W →+*
      productAntidiagonalIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayRight
    (S := productNeighborhoodCoordinateRing W)
    (P := productAntidiagonalIntersectionCoordinateRing W)
    (additionB12 W) (antidiagonalAddYNumerator W)

/-- Restriction from `D(Y)` to `D(B₁₂Y)`. -/
noncomputable def antidiagonalChartToIntersectionRing
    (W : WeierstrassCurve K) :
    antidiagonalChartCoordinateRing W →+*
      productAntidiagonalIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayLeft
    (S := antidiagonalChartCoordinateRing W)
    (P := productAntidiagonalIntersectionCoordinateRing W)
    (antidiagonalAddYNumerator W) (additionB12 W)

@[simp]
private theorem productNeighborhoodToAntidiagonalIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    productNeighborhoodToAntidiagonalIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (productAntidiagonalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := productNeighborhoodCoordinateRing W)
    (P := productAntidiagonalIntersectionCoordinateRing W)
    (additionB12 W) (antidiagonalAddYNumerator W) a

@[simp]
private theorem antidiagonalChartToIntersectionRing_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    antidiagonalChartToIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (antidiagonalChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (productAntidiagonalIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := antidiagonalChartCoordinateRing W)
    (P := productAntidiagonalIntersectionCoordinateRing W)
    (antidiagonalAddYNumerator W) (additionB12 W) a

/-- The exact overlap is the intersection `D(B₁₂) ∩ D(Y)`. -/
theorem productAntidiagonalIntersection_basicOpen
    (W : WeierstrassCurve K) :
    PrimeSpectrum.basicOpen
        (additionB12 W * antidiagonalAddYNumerator W) =
      PrimeSpectrum.basicOpen (additionB12 W) ⊓
        PrimeSpectrum.basicOpen (antidiagonalAddYNumerator W) :=
  PrimeSpectrum.basicOpen_mul _ _

private theorem productNeighborhoodAddX_cleared_on_antidiagonalIntersection
    (W : WeierstrassCurve K) :
    productNeighborhoodToAntidiagonalIntersectionRing W
          (productNeighborhoodAddX W) *
        algebraMap (secantPairCoordinateRing W)
            (productAntidiagonalIntersectionCoordinateRing W)
            (additionB12 W) ^ 2 =
      algebraMap (secantPairCoordinateRing W)
        (productAntidiagonalIntersectionCoordinateRing W)
        (antidiagonalAddXNumerator W) := by
  simpa [productNeighborhoodB12] using congrArg
    (productNeighborhoodToAntidiagonalIntersectionRing W)
    (productNeighborhoodAddX_mul_B12_sq W)

private theorem productNeighborhoodAddY_cleared_on_antidiagonalIntersection
    (W : WeierstrassCurve K) :
    productNeighborhoodToAntidiagonalIntersectionRing W
          (productNeighborhoodAddY W) *
        algebraMap (secantPairCoordinateRing W)
            (productAntidiagonalIntersectionCoordinateRing W)
            (additionB12 W) ^ 3 =
      algebraMap (secantPairCoordinateRing W)
        (productAntidiagonalIntersectionCoordinateRing W)
        (antidiagonalAddYNumerator W) := by
  simpa [productNeighborhoodB12] using congrArg
    (productNeighborhoodToAntidiagonalIntersectionRing W)
    (productNeighborhoodAddY_mul_B12_cube W)

private theorem antidiagonalYNumerator_mul_invSelf_on_intersection
    (W : WeierstrassCurve K) :
    algebraMap (secantPairCoordinateRing W)
          (productAntidiagonalIntersectionCoordinateRing W)
          (antidiagonalAddYNumerator W) *
        antidiagonalChartToIntersectionRing W
          (IsLocalization.Away.invSelf (antidiagonalAddYNumerator W)) = 1 := by
  have h := congrArg (antidiagonalChartToIntersectionRing W)
    (IsLocalization.Away.mul_invSelf
      (S := antidiagonalChartCoordinateRing W)
      (antidiagonalAddYNumerator W))
  simpa only [map_mul, map_one,
    antidiagonalChartToIntersectionRing_algebraMap] using h

/-- On `D(B₁₂Y)`, the normalized infinity-chart coordinate `X/Y` is exactly
the quotient of the affine output coordinates `x₃/y₃`. -/
theorem antidiagonalXOverY_mul_productNeighborhoodAddY_on_intersection
    (W : WeierstrassCurve K) :
    antidiagonalChartToIntersectionRing W
          (antidiagonalChartXOverY W) *
        productNeighborhoodToAntidiagonalIntersectionRing W
          (productNeighborhoodAddY W) =
      productNeighborhoodToAntidiagonalIntersectionRing W
        (productNeighborhoodAddX W) := by
  have hX := productNeighborhoodAddX_cleared_on_antidiagonalIntersection W
  have hY := productNeighborhoodAddY_cleared_on_antidiagonalIntersection W
  have hYinv := antidiagonalYNumerator_mul_invSelf_on_intersection W
  simp only [antidiagonalChartXOverY, antidiagonalChartHomogeneousX,
    map_mul] at ⊢
  simp only [antidiagonalChartToIntersectionRing_algebraMap]
  calc
    _ = productNeighborhoodToAntidiagonalIntersectionRing W
          (productNeighborhoodAddX W) *
        ((productNeighborhoodToAntidiagonalIntersectionRing W
              (productNeighborhoodAddY W) *
            algebraMap (secantPairCoordinateRing W)
                (productAntidiagonalIntersectionCoordinateRing W)
                (additionB12 W) ^ 3) *
          antidiagonalChartToIntersectionRing W
            (IsLocalization.Away.invSelf
              (antidiagonalAddYNumerator W))) := by
      rw [← hX]
      ring
    _ = productNeighborhoodToAntidiagonalIntersectionRing W
          (productNeighborhoodAddX W) := by
      rw [hY, hYinv, mul_one]

/-- On `D(B₁₂Y)`, the normalized infinity-chart coordinate `Z/Y` multiplied
by the affine ordinate is one.  Together with the preceding theorem this is
the exact standard-chart/infinity-chart transition law. -/
theorem antidiagonalZOverY_mul_productNeighborhoodAddY_on_intersection
    (W : WeierstrassCurve K) :
    antidiagonalChartToIntersectionRing W
          (antidiagonalChartZOverY W) *
        productNeighborhoodToAntidiagonalIntersectionRing W
          (productNeighborhoodAddY W) = 1 := by
  have hY := productNeighborhoodAddY_cleared_on_antidiagonalIntersection W
  have hYinv := antidiagonalYNumerator_mul_invSelf_on_intersection W
  simp only [antidiagonalChartZOverY, antidiagonalChartHomogeneousZ,
    map_mul] at ⊢
  simp only [antidiagonalChartToIntersectionRing_algebraMap, map_pow]
  calc
    _ = (productNeighborhoodToAntidiagonalIntersectionRing W
            (productNeighborhoodAddY W) *
          algebraMap (secantPairCoordinateRing W)
              (productAntidiagonalIntersectionCoordinateRing W)
              (additionB12 W) ^ 3) *
        antidiagonalChartToIntersectionRing W
          (IsLocalization.Away.invSelf
            (antidiagonalAddYNumerator W)) := by ring
    _ = 1 := by rw [hY, hYinv]

/-! ## The common target-chart localization -/

/-- Degree-zero homogeneous coordinate ring of the projective overlap
`D(YZ)`. -/
abbrev projectiveYZOverlapRing (K : Type u) [Field K] :=
  HomogeneousLocalization.Away (homogeneousPieces K)
    (MvPolynomial.X 2 * MvPolynomial.X 1)

/-- Restriction from the standard `Z ≠ 0` chart to `D(YZ)`. -/
noncomputable def standardChartToProjectiveYZOverlapRing :
    HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 2) →+* projectiveYZOverlapRing K :=
  HomogeneousLocalization.awayMap (homogeneousPieces K)
    (show MvPolynomial.X 1 ∈ homogeneousPieces K 1 from
      MvPolynomial.isHomogeneous_X K 1) rfl

/-- Restriction from the infinity `Y ≠ 0` chart to `D(YZ)`. -/
noncomputable def infinityChartToProjectiveYZOverlapRing :
    HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 1) →+* projectiveYZOverlapRing K :=
  HomogeneousLocalization.awayMap (homogeneousPieces K)
    (show MvPolynomial.X 2 ∈ homogeneousPieces K 1 from
      MvPolynomial.isHomogeneous_X K 2)
    (show MvPolynomial.X 2 * MvPolynomial.X 1 =
      MvPolynomial.X 1 * MvPolynomial.X 2 by ring)

/-- Both projective charts restrict base constants identically to `D(YZ)`. -/
theorem projectiveYZOverlap_transition_constant (a : K) :
    standardChartToProjectiveYZOverlapRing (K := K)
        (coordinateChartConstantHom (K := K) 2 a) =
      infinityChartToProjectiveYZOverlapRing (K := K)
        (coordinateChartConstantHom (K := K) 1 a) := by
  change
    HomogeneousLocalization.awayMap (homogeneousPieces K)
        (show MvPolynomial.X 1 ∈ homogeneousPieces K 1 from
          MvPolynomial.isHomogeneous_X K 1) rfl
        (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
          (Submonoid.powers (MvPolynomial.X 2))
          (algebraMap K (homogeneousPieces K 0) a)) =
      HomogeneousLocalization.awayMap (homogeneousPieces K)
        (show MvPolynomial.X 2 ∈ homogeneousPieces K 1 from
          MvPolynomial.isHomogeneous_X K 2)
        (show MvPolynomial.X 2 * MvPolynomial.X 1 =
          MvPolynomial.X 1 * MvPolynomial.X 2 by ring)
        (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
          (Submonoid.powers (MvPolynomial.X 1))
          (algebraMap K (homogeneousPieces K 0) a))
  rw [HomogeneousLocalization.awayMap_fromZeroRingHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom]

/-- Transition identity `(X/Y)(Y/Z) = X/Z` on `D(YZ)`. -/
theorem projectiveYZOverlap_transition_outerX :
    infinityChartToProjectiveYZOverlapRing (K := K)
          (coordinateChartRatio (K := K) 1 0) *
        standardChartToProjectiveYZOverlapRing (K := K)
          (coordinateChartRatio (K := K) 2 1) =
      standardChartToProjectiveYZOverlapRing (K := K)
        (coordinateChartRatio (K := K) 2 0) := by
  change
    HomogeneousLocalization.awayMap (homogeneousPieces K)
          (show MvPolynomial.X 2 ∈ homogeneousPieces K 1 from
            MvPolynomial.isHomogeneous_X K 2)
          (show MvPolynomial.X 2 * MvPolynomial.X 1 =
            MvPolynomial.X 1 * MvPolynomial.X 2 by ring)
          (coordinateChartRatio (K := K) 1 0) *
        HomogeneousLocalization.awayMap (homogeneousPieces K)
          (show MvPolynomial.X 1 ∈ homogeneousPieces K 1 from
            MvPolynomial.isHomogeneous_X K 1) rfl
          (coordinateChartRatio (K := K) 2 1) =
      HomogeneousLocalization.awayMap (homogeneousPieces K)
        (show MvPolynomial.X 1 ∈ homogeneousPieces K 1 from
          MvPolynomial.isHomogeneous_X K 1) rfl
        (coordinateChartRatio (K := K) 2 0)
  unfold coordinateChartRatio
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp
  ring

/-- Transition identity `(Z/Y)(Y/Z) = 1` on `D(YZ)`. -/
theorem projectiveYZOverlap_transition_innerX :
    infinityChartToProjectiveYZOverlapRing (K := K)
          (coordinateChartRatio (K := K) 1 2) *
        standardChartToProjectiveYZOverlapRing (K := K)
          (coordinateChartRatio (K := K) 2 1) = 1 := by
  change
    HomogeneousLocalization.awayMap (homogeneousPieces K)
          (show MvPolynomial.X 2 ∈ homogeneousPieces K 1 from
            MvPolynomial.isHomogeneous_X K 2)
          (show MvPolynomial.X 2 * MvPolynomial.X 1 =
            MvPolynomial.X 1 * MvPolynomial.X 2 by ring)
          (coordinateChartRatio (K := K) 1 2) *
        HomogeneousLocalization.awayMap (homogeneousPieces K)
          (show MvPolynomial.X 1 ∈ homogeneousPieces K 1 from
            MvPolynomial.isHomogeneous_X K 1) rfl
          (coordinateChartRatio (K := K) 2 1) = 1
  unfold coordinateChartRatio
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

/-- Two affine-chart maps that obey the `Z ≠ 0`/`Y ≠ 0` transition laws
define the same morphism into projective space.  This is the reusable target
gluing lemma for the denominator-cleared addition charts. -/
theorem projectiveYZOverlap_ambient_maps_eq
    {R : Type u} [CommRing R]
    (standardMap :
      HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2) →+* R)
    (infinityMap :
      HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 1) →+* R)
    (hconstant : ∀ a : K,
      standardMap (coordinateChartConstantHom (K := K) 2 a) =
        infinityMap (coordinateChartConstantHom (K := K) 1 a))
    (hstandardInnerUnit :
      IsUnit (standardMap (coordinateChartRatio (K := K) 2 1)))
    (houter :
      infinityMap (coordinateChartRatio (K := K) 1 0) *
          standardMap (coordinateChartRatio (K := K) 2 1) =
        standardMap (coordinateChartRatio (K := K) 2 0))
    (hinner :
      infinityMap (coordinateChartRatio (K := K) 1 2) *
          standardMap (coordinateChartRatio (K := K) 2 1) = 1) :
    Spec.map (CommRingCat.ofHom standardMap) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
          (MvPolynomial.isHomogeneous_X K 2) zero_lt_one =
      Spec.map (CommRingCat.ofHom infinityMap) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
          (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
  letI : Algebra
      (HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2))
      (projectiveYZOverlapRing K) :=
    (standardChartToProjectiveYZOverlapRing (K := K)).toAlgebra
  letI : IsLocalization.Away
      (HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
        (g := MvPolynomial.X 1)
        (MvPolynomial.isHomogeneous_X K 2)
        (MvPolynomial.isHomogeneous_X K 1))
      (projectiveYZOverlapRing K) :=
    HomogeneousLocalization.Away.isLocalization_mul
      (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
      (g := MvPolynomial.X 1)
      (MvPolynomial.isHomogeneous_X K 2)
      (MvPolynomial.isHomogeneous_X K 1) rfl (by omega)
  have hlocalizationElem :
      HomogeneousLocalization.Away.isLocalizationElem
          (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
          (g := MvPolynomial.X 1)
          (MvPolynomial.isHomogeneous_X K 2)
          (MvPolynomial.isHomogeneous_X K 1) =
        coordinateChartRatio (K := K) 2 1 :=
    isLocalizationElem_degree_one_eq_coordinateChartRatio 2 1
  let overlapMap : projectiveYZOverlapRing K →+* R :=
    IsLocalization.Away.lift
      (R := HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2))
      (S := projectiveYZOverlapRing K) (P := R) (g := standardMap)
      (HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
        (g := MvPolynomial.X 1)
        (MvPolynomial.isHomogeneous_X K 2)
        (MvPolynomial.isHomogeneous_X K 1))
      (hlocalizationElem ▸ hstandardInnerUnit)
  have hoverlap_standard :
      overlapMap.comp (standardChartToProjectiveYZOverlapRing (K := K)) =
        standardMap := by
    exact IsLocalization.Away.lift_comp
      (R := HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2))
      (S := projectiveYZOverlapRing K) (P := R) (g := standardMap)
      (HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
        (g := MvPolynomial.X 1)
        (MvPolynomial.isHomogeneous_X K 2)
        (MvPolynomial.isHomogeneous_X K 1))
      (hlocalizationElem ▸ hstandardInnerUnit)
  have hstandard_apply
      (z : HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2)) :
      overlapMap (standardChartToProjectiveYZOverlapRing (K := K) z) =
        standardMap z := by
    change (overlapMap.comp
      (standardChartToProjectiveYZOverlapRing (K := K))) z = _
    exact RingHom.congr_fun hoverlap_standard z
  have hoverlap_infinity :
      overlapMap.comp (infinityChartToProjectiveYZOverlapRing (K := K)) =
        infinityMap := by
    apply chartRingHom_ext (K := K) 1
    · ext a
      change overlapMap
          (infinityChartToProjectiveYZOverlapRing (K := K)
            (coordinateChartConstantHom (K := K) 1 a)) =
        infinityMap (coordinateChartConstantHom (K := K) 1 a)
      rw [← hconstant]
      rw [← projectiveYZOverlap_transition_constant]
      exact hstandard_apply (coordinateChartConstantHom (K := K) 2 a)
    · intro j
      fin_cases j
      · change overlapMap
            (infinityChartToProjectiveYZOverlapRing (K := K)
              (coordinateChartRatio (K := K) 1 0)) =
          infinityMap (coordinateChartRatio (K := K) 1 0)
        apply hstandardInnerUnit.mul_right_cancel
        have htransition := congrArg overlapMap
          (projectiveYZOverlap_transition_outerX (K := K))
        calc
          overlapMap
                (infinityChartToProjectiveYZOverlapRing (K := K)
                  (coordinateChartRatio (K := K) 1 0)) *
              standardMap (coordinateChartRatio (K := K) 2 1) =
            overlapMap
                (infinityChartToProjectiveYZOverlapRing (K := K)
                  (coordinateChartRatio (K := K) 1 0)) *
              overlapMap
                (standardChartToProjectiveYZOverlapRing (K := K)
                  (coordinateChartRatio (K := K) 2 1)) := by
                    rw [hstandard_apply]
          _ = overlapMap
                (standardChartToProjectiveYZOverlapRing (K := K)
                  (coordinateChartRatio (K := K) 2 0)) := by
                    simpa only [map_mul] using htransition
          _ = standardMap (coordinateChartRatio (K := K) 2 0) :=
            hstandard_apply _
          _ = infinityMap (coordinateChartRatio (K := K) 1 0) *
              standardMap (coordinateChartRatio (K := K) 2 1) := houter.symm
      · change overlapMap
            (infinityChartToProjectiveYZOverlapRing (K := K)
              (coordinateChartRatio (K := K) 1 1)) =
          infinityMap (coordinateChartRatio (K := K) 1 1)
        rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio
            (K := K) 1 1,
          isLocalizationElem_self_degree_one,
          (infinityChartToProjectiveYZOverlapRing (K := K)).map_one,
          overlapMap.map_one,
          infinityMap.map_one]
      · change overlapMap
            (infinityChartToProjectiveYZOverlapRing (K := K)
              (coordinateChartRatio (K := K) 1 2)) =
          infinityMap (coordinateChartRatio (K := K) 1 2)
        apply hstandardInnerUnit.mul_right_cancel
        have htransition := congrArg overlapMap
          (projectiveYZOverlap_transition_innerX (K := K))
        calc
          overlapMap
                (infinityChartToProjectiveYZOverlapRing (K := K)
                  (coordinateChartRatio (K := K) 1 2)) *
              standardMap (coordinateChartRatio (K := K) 2 1) =
            overlapMap
                (infinityChartToProjectiveYZOverlapRing (K := K)
                  (coordinateChartRatio (K := K) 1 2)) *
              overlapMap
                (standardChartToProjectiveYZOverlapRing (K := K)
                  (coordinateChartRatio (K := K) 2 1)) := by
                    rw [hstandard_apply]
          _ = 1 := by simpa only [map_mul, map_one] using htransition
          _ = infinityMap (coordinateChartRatio (K := K) 1 2) *
              standardMap (coordinateChartRatio (K := K) 2 1) := hinner.symm
  let H := homogeneousPieces K
  let X₁ : MvPolynomial (Fin 3) K := MvPolynomial.X 1
  let X₂ : MvPolynomial (Fin 3) K := MvPolynomial.X 2
  let q : MvPolynomial (Fin 3) K := X₂ * X₁
  let hq : q ∈ H 2 := by
    simpa only [H, X₁, X₂, q, one_add_one_eq_two] using
      SetLike.mul_mem_graded
        (A := homogeneousPieces K) (i := 1) (j := 1)
        (gi := MvPolynomial.X 2) (gj := MvPolynomial.X 1)
        (MvPolynomial.isHomogeneous_X K 2)
        (MvPolynomial.isHomogeneous_X K 1)
  calc
    Spec.map (CommRingCat.ofHom standardMap) ≫
        Proj.awayι H X₂ (MvPolynomial.isHomogeneous_X K 2) zero_lt_one =
      (Spec.map (CommRingCat.ofHom overlapMap) ≫
          Spec.map (CommRingCat.ofHom
            (standardChartToProjectiveYZOverlapRing (K := K)))) ≫
        Proj.awayι H X₂ (MvPolynomial.isHomogeneous_X K 2) zero_lt_one := by
          rw [← Spec.map_comp]
          congr 2
          apply CommRingCat.hom_ext
          exact hoverlap_standard.symm
    _ = Spec.map (CommRingCat.ofHom overlapMap) ≫
        Proj.awayι H q hq (by omega) := by
          simpa only [standardChartToProjectiveYZOverlapRing,
            Category.assoc] using congrArg
            (fun f => Spec.map (CommRingCat.ofHom overlapMap) ≫ f)
            (Proj.SpecMap_awayMap_awayι
              (f := X₂) (g := X₁) (x := q) H
              (MvPolynomial.isHomogeneous_X K 2) zero_lt_one
              (MvPolynomial.isHomogeneous_X K 1) rfl)
    _ = (Spec.map (CommRingCat.ofHom overlapMap) ≫
          Spec.map (CommRingCat.ofHom
            (infinityChartToProjectiveYZOverlapRing (K := K)))) ≫
        Proj.awayι H X₁ (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
          simpa only [infinityChartToProjectiveYZOverlapRing,
            Category.assoc] using congrArg
            (fun f => Spec.map (CommRingCat.ofHom overlapMap) ≫ f)
            (Proj.SpecMap_awayMap_awayι
              (f := X₁) (g := X₂) (x := q) H
              (MvPolynomial.isHomogeneous_X K 1) zero_lt_one
              (MvPolynomial.isHomogeneous_X K 2)
              (mul_comm X₂ X₁)).symm
    _ = Spec.map (CommRingCat.ofHom infinityMap) ≫
        Proj.awayι H X₁ (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
          rw [← Spec.map_comp]
          congr 2
          apply CommRingCat.hom_ext
          exact hoverlap_infinity

private noncomputable def productIntersectionToStandardAmbientRing
    (W : WeierstrassCurve K) :
    HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 2) →+*
      productAntidiagonalIntersectionCoordinateRing W :=
  (productNeighborhoodToAntidiagonalIntersectionRing W).comp
    ((productNeighborhoodAdditionToAffineRing W).comp
      ((affineEquationToStandardChartRingEquiv W).symm.toRingHom.comp
        (Ideal.Quotient.mk (coveringChartIdeal W true))))

private noncomputable def productIntersectionToInfinityAmbientRing
    (W : WeierstrassCurve K) :
    HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 1) →+*
      productAntidiagonalIntersectionCoordinateRing W :=
  (antidiagonalChartToIntersectionRing W).comp
    ((antidiagonalAdditionToInfinityRing W).comp
      (Ideal.Quotient.mk (coveringChartIdeal W false)))

/-- The standard-chart quotient equivalence sends a base constant to the
affine Weierstrass coefficient map. -/
theorem standardChartQuotientEquivSymm_constant
    (W : WeierstrassCurve K) (a : K) :
    (affineEquationToStandardChartRingEquiv W).symm
        (Ideal.Quotient.mk (standardChartIdeal W)
          (coordinateChartConstantHom (K := K) 2 a)) =
      secantTargetCoefficientHom W a := by
  apply (affineEquationToStandardChartRingEquiv W).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (standardChartIdeal W)
      (coordinateChartConstantHom (K := K) 2 a) =
    Ideal.Quotient.mk (standardChartIdeal W)
      (affineToStandardChart (K := K)
        (Polynomial.C (Polynomial.C a)))
  rw [affineToStandardChart_C_C]

/-- The standard-chart quotient equivalence sends `X/Z` to the affine
abscissa. -/
theorem standardChartQuotientEquivSymm_outerX
    (W : WeierstrassCurve K) :
    (affineEquationToStandardChartRingEquiv W).symm
        (Ideal.Quotient.mk (standardChartIdeal W)
          (coordinateChartRatio (K := K) 2 0)) =
      secantTargetX W := by
  apply (affineEquationToStandardChartRingEquiv W).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (standardChartIdeal W)
      (coordinateChartRatio (K := K) 2 0) =
    Ideal.Quotient.mk (standardChartIdeal W)
      (affineToStandardChart (K := K) (Polynomial.C Polynomial.X))
  rw [affineToStandardChart_C_X]

/-- The standard-chart quotient equivalence sends `Y/Z` to the affine
ordinate. -/
theorem standardChartQuotientEquivSymm_innerX
    (W : WeierstrassCurve K) :
    (affineEquationToStandardChartRingEquiv W).symm
        (Ideal.Quotient.mk (standardChartIdeal W)
          (coordinateChartRatio (K := K) 2 1)) =
      secantTargetY W := by
  apply (affineEquationToStandardChartRingEquiv W).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (standardChartIdeal W)
      (coordinateChartRatio (K := K) 2 1) =
    Ideal.Quotient.mk (standardChartIdeal W)
      (affineToStandardChart (K := K) Polynomial.X)
  rw [affineToStandardChart_X]

@[simp]
private theorem productIntersectionToStandardAmbientRing_constant
    (W : WeierstrassCurve K) (a : K) :
    productIntersectionToStandardAmbientRing W
        (coordinateChartConstantHom (K := K) 2 a) =
      algebraMap (secantPairCoordinateRing W)
        (productAntidiagonalIntersectionCoordinateRing W)
        (secantPairCoefficientHom W a) := by
  change productNeighborhoodToAntidiagonalIntersectionRing W
      (productNeighborhoodAdditionToAffineRing W
        ((affineEquationToStandardChartRingEquiv W).symm
          (Ideal.Quotient.mk (standardChartIdeal W)
            (coordinateChartConstantHom (K := K) 2 a)))) = _
  rw [standardChartQuotientEquivSymm_constant,
    productNeighborhoodAdditionToAffineRing_coefficient]
  change productNeighborhoodToAntidiagonalIntersectionRing W
      (algebraMap (secantPairCoordinateRing W)
        (productNeighborhoodCoordinateRing W)
        (secantPairCoefficientHom W a)) = _
  exact productNeighborhoodToAntidiagonalIntersectionRing_algebraMap W _

@[simp]
private theorem productIntersectionToStandardAmbientRing_outerX
    (W : WeierstrassCurve K) :
    productIntersectionToStandardAmbientRing W
        (coordinateChartRatio (K := K) 2 0) =
      productNeighborhoodToAntidiagonalIntersectionRing W
        (productNeighborhoodAddX W) := by
  change productNeighborhoodToAntidiagonalIntersectionRing W
      (productNeighborhoodAdditionToAffineRing W
        ((affineEquationToStandardChartRingEquiv W).symm
          (Ideal.Quotient.mk (standardChartIdeal W)
            (coordinateChartRatio (K := K) 2 0)))) = _
  rw [standardChartQuotientEquivSymm_outerX]
  exact congrArg (productNeighborhoodToAntidiagonalIntersectionRing W)
    (productNeighborhoodAdditionToAffineRing_abscissa W)

@[simp]
private theorem productIntersectionToStandardAmbientRing_innerX
    (W : WeierstrassCurve K) :
    productIntersectionToStandardAmbientRing W
        (coordinateChartRatio (K := K) 2 1) =
      productNeighborhoodToAntidiagonalIntersectionRing W
        (productNeighborhoodAddY W) := by
  change productNeighborhoodToAntidiagonalIntersectionRing W
      (productNeighborhoodAdditionToAffineRing W
        ((affineEquationToStandardChartRingEquiv W).symm
          (Ideal.Quotient.mk (standardChartIdeal W)
            (coordinateChartRatio (K := K) 2 1)))) = _
  rw [standardChartQuotientEquivSymm_innerX]
  exact congrArg (productNeighborhoodToAntidiagonalIntersectionRing W)
    (productNeighborhoodAdditionToAffineRing_ordinate W)

private theorem productIntersectionToStandardAmbientRing_innerX_isUnit
    (W : WeierstrassCurve K) :
    IsUnit (productIntersectionToStandardAmbientRing W
      (coordinateChartRatio (K := K) 2 1)) := by
  rw [productIntersectionToStandardAmbientRing_innerX]
  have hBY : IsUnit
      (algebraMap (secantPairCoordinateRing W)
        (productAntidiagonalIntersectionCoordinateRing W)
        (additionB12 W * antidiagonalAddYNumerator W)) :=
    IsLocalization.Away.algebraMap_isUnit
      (additionB12 W * antidiagonalAddYNumerator W)
  rw [map_mul] at hBY
  have hY : IsUnit
      (algebraMap (secantPairCoordinateRing W)
        (productAntidiagonalIntersectionCoordinateRing W)
        (antidiagonalAddYNumerator W)) :=
    isUnit_of_mul_isUnit_right hBY
  have hcleared :=
    productNeighborhoodAddY_cleared_on_antidiagonalIntersection W
  have hproduct : IsUnit
      (productNeighborhoodToAntidiagonalIntersectionRing W
          (productNeighborhoodAddY W) *
        algebraMap (secantPairCoordinateRing W)
            (productAntidiagonalIntersectionCoordinateRing W)
            (additionB12 W) ^ 3) := by
    rw [hcleared]
    exact hY
  exact isUnit_of_mul_isUnit_left hproduct

@[simp]
private theorem productIntersectionToInfinityAmbientRing_constant
    (W : WeierstrassCurve K) (a : K) :
    productIntersectionToInfinityAmbientRing W
        (coordinateChartConstantHom (K := K) 1 a) =
      algebraMap (secantPairCoordinateRing W)
        (productAntidiagonalIntersectionCoordinateRing W)
        (secantPairCoefficientHom W a) := by
  change antidiagonalChartToIntersectionRing W
      (antidiagonalAdditionToInfinityRing W
        (coveringChartStructureRingHom W false a)) = _
  rw [antidiagonalAdditionToInfinityRing_coefficient]
  exact antidiagonalChartToIntersectionRing_algebraMap W _

@[simp]
private theorem productIntersectionToInfinityAmbientRing_outerX
    (W : WeierstrassCurve K) :
    productIntersectionToInfinityAmbientRing W
        (coordinateChartRatio (K := K) 1 0) =
      antidiagonalChartToIntersectionRing W
        (antidiagonalChartXOverY W) := by
  change antidiagonalChartToIntersectionRing W
      (antidiagonalAdditionToInfinityRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 0))) = _
  rw [antidiagonalAdditionToInfinityRing_outerX]

@[simp]
private theorem productIntersectionToInfinityAmbientRing_innerX
    (W : WeierstrassCurve K) :
    productIntersectionToInfinityAmbientRing W
        (coordinateChartRatio (K := K) 1 2) =
      antidiagonalChartToIntersectionRing W
        (antidiagonalChartZOverY W) := by
  change antidiagonalChartToIntersectionRing W
      (antidiagonalAdditionToInfinityRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := K) 1 2))) = _
  rw [antidiagonalAdditionToInfinityRing_innerX]

private noncomputable instance projectiveYZOverlapAlgebra :
    Algebra
      (HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2))
      (projectiveYZOverlapRing K) :=
  (standardChartToProjectiveYZOverlapRing (K := K)).toAlgebra

private noncomputable instance projectiveYZOverlap_isLocalization :
    IsLocalization.Away
      (HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
        (g := MvPolynomial.X 1)
        (MvPolynomial.isHomogeneous_X K 2)
        (MvPolynomial.isHomogeneous_X K 1))
      (projectiveYZOverlapRing K) :=
  HomogeneousLocalization.Away.isLocalization_mul
    (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
    (g := MvPolynomial.X 1)
    (MvPolynomial.isHomogeneous_X K 2)
    (MvPolynomial.isHomogeneous_X K 1) rfl (by omega)

private theorem standardChartLocalizationElem_eq_innerX :
    HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
        (g := MvPolynomial.X 1)
        (MvPolynomial.isHomogeneous_X K 2)
        (MvPolynomial.isHomogeneous_X K 1) =
      coordinateChartRatio (K := K) 2 1 := by
  exact isLocalizationElem_degree_one_eq_coordinateChartRatio 2 1

private noncomputable def projectiveYZOverlapToProductIntersectionRing
    (W : WeierstrassCurve K) :
    projectiveYZOverlapRing K →+*
      productAntidiagonalIntersectionCoordinateRing W :=
  IsLocalization.Away.lift
    (R := HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 2))
    (S := projectiveYZOverlapRing K)
    (P := productAntidiagonalIntersectionCoordinateRing W)
    (g := productIntersectionToStandardAmbientRing W)
    (HomogeneousLocalization.Away.isLocalizationElem
      (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
      (g := MvPolynomial.X 1)
      (MvPolynomial.isHomogeneous_X K 2)
      (MvPolynomial.isHomogeneous_X K 1))
    (standardChartLocalizationElem_eq_innerX (K := K) ▸
      productIntersectionToStandardAmbientRing_innerX_isUnit W)

private theorem projectiveYZOverlapToProductIntersectionRing_comp_standard
    (W : WeierstrassCurve K) :
    (projectiveYZOverlapToProductIntersectionRing W).comp
        (standardChartToProjectiveYZOverlapRing (K := K)) =
      productIntersectionToStandardAmbientRing W := by
  exact IsLocalization.Away.lift_comp
    (R := HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 2))
    (S := projectiveYZOverlapRing K)
    (P := productAntidiagonalIntersectionCoordinateRing W)
    (g := productIntersectionToStandardAmbientRing W)
    (HomogeneousLocalization.Away.isLocalizationElem
      (𝒜 := homogeneousPieces K) (f := MvPolynomial.X 2)
      (g := MvPolynomial.X 1)
      (MvPolynomial.isHomogeneous_X K 2)
      (MvPolynomial.isHomogeneous_X K 1))
    (standardChartLocalizationElem_eq_innerX (K := K) ▸
      productIntersectionToStandardAmbientRing_innerX_isUnit W)

private theorem projectiveYZOverlapToProductIntersectionRing_comp_infinity
    (W : WeierstrassCurve K) :
    (projectiveYZOverlapToProductIntersectionRing W).comp
        (infinityChartToProjectiveYZOverlapRing (K := K)) =
      productIntersectionToInfinityAmbientRing W := by
  have hstandard_apply
      (z : HomogeneousLocalization.Away (homogeneousPieces K)
        (MvPolynomial.X 2)) :
      projectiveYZOverlapToProductIntersectionRing W
          (standardChartToProjectiveYZOverlapRing (K := K) z) =
        productIntersectionToStandardAmbientRing W z := by
    change ((projectiveYZOverlapToProductIntersectionRing W).comp
      (standardChartToProjectiveYZOverlapRing (K := K))) z = _
    exact RingHom.congr_fun
      (projectiveYZOverlapToProductIntersectionRing_comp_standard W) z
  apply chartRingHom_ext (K := K) 1
  · ext a
    change projectiveYZOverlapToProductIntersectionRing W
        (infinityChartToProjectiveYZOverlapRing (K := K)
          (coordinateChartConstantHom (K := K) 1 a)) =
      productIntersectionToInfinityAmbientRing W
        (coordinateChartConstantHom (K := K) 1 a)
    rw [← projectiveYZOverlap_transition_constant]
    simpa only [RingHom.comp_apply,
      productIntersectionToStandardAmbientRing_constant,
      productIntersectionToInfinityAmbientRing_constant] using
        hstandard_apply (coordinateChartConstantHom (K := K) 2 a)
  · intro j
    fin_cases j
    · change projectiveYZOverlapToProductIntersectionRing W
          (infinityChartToProjectiveYZOverlapRing (K := K)
            (coordinateChartRatio (K := K) 1 0)) =
        productIntersectionToInfinityAmbientRing W
          (coordinateChartRatio (K := K) 1 0)
      have hunit :=
        productIntersectionToStandardAmbientRing_innerX_isUnit W
      apply hunit.mul_right_cancel
      have htransition := congrArg
        (projectiveYZOverlapToProductIntersectionRing W)
        (projectiveYZOverlap_transition_outerX (K := K))
      calc
        projectiveYZOverlapToProductIntersectionRing W
              (infinityChartToProjectiveYZOverlapRing (K := K)
                (coordinateChartRatio (K := K) 1 0)) *
            productIntersectionToStandardAmbientRing W
              (coordinateChartRatio (K := K) 2 1) =
          projectiveYZOverlapToProductIntersectionRing W
              (infinityChartToProjectiveYZOverlapRing (K := K)
                (coordinateChartRatio (K := K) 1 0)) *
            projectiveYZOverlapToProductIntersectionRing W
              (standardChartToProjectiveYZOverlapRing (K := K)
                (coordinateChartRatio (K := K) 2 1)) := by
                  rw [hstandard_apply]
        _ = projectiveYZOverlapToProductIntersectionRing W
              (standardChartToProjectiveYZOverlapRing (K := K)
                (coordinateChartRatio (K := K) 2 0)) := by
                  simpa only [map_mul] using htransition
        _ = productIntersectionToStandardAmbientRing W
              (coordinateChartRatio (K := K) 2 0) :=
                hstandard_apply _
        _ = productIntersectionToInfinityAmbientRing W
              (coordinateChartRatio (K := K) 1 0) *
            productIntersectionToStandardAmbientRing W
              (coordinateChartRatio (K := K) 2 1) := by
                rw [productIntersectionToStandardAmbientRing_outerX,
                  productIntersectionToInfinityAmbientRing_outerX,
                  productIntersectionToStandardAmbientRing_innerX,
                  antidiagonalXOverY_mul_productNeighborhoodAddY_on_intersection]
    · change projectiveYZOverlapToProductIntersectionRing W
          (infinityChartToProjectiveYZOverlapRing (K := K)
            (coordinateChartRatio (K := K) 1 1)) =
        productIntersectionToInfinityAmbientRing W
          (coordinateChartRatio (K := K) 1 1)
      rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio
          (K := K) 1 1,
        isLocalizationElem_self_degree_one, map_one]
      exact (projectiveYZOverlapToProductIntersectionRing W).map_one.trans
        (productIntersectionToInfinityAmbientRing W).map_one.symm
    · change projectiveYZOverlapToProductIntersectionRing W
          (infinityChartToProjectiveYZOverlapRing (K := K)
            (coordinateChartRatio (K := K) 1 2)) =
        productIntersectionToInfinityAmbientRing W
          (coordinateChartRatio (K := K) 1 2)
      have hunit :=
        productIntersectionToStandardAmbientRing_innerX_isUnit W
      apply hunit.mul_right_cancel
      have htransition := congrArg
        (projectiveYZOverlapToProductIntersectionRing W)
        (projectiveYZOverlap_transition_innerX (K := K))
      calc
        projectiveYZOverlapToProductIntersectionRing W
              (infinityChartToProjectiveYZOverlapRing (K := K)
                (coordinateChartRatio (K := K) 1 2)) *
            productIntersectionToStandardAmbientRing W
              (coordinateChartRatio (K := K) 2 1) =
          projectiveYZOverlapToProductIntersectionRing W
              (infinityChartToProjectiveYZOverlapRing (K := K)
                (coordinateChartRatio (K := K) 1 2)) *
            projectiveYZOverlapToProductIntersectionRing W
              (standardChartToProjectiveYZOverlapRing (K := K)
                (coordinateChartRatio (K := K) 2 1)) := by
                  rw [hstandard_apply]
        _ = 1 := by simpa only [map_mul, map_one] using htransition
        _ = productIntersectionToInfinityAmbientRing W
              (coordinateChartRatio (K := K) 1 2) *
            productIntersectionToStandardAmbientRing W
              (coordinateChartRatio (K := K) 2 1) := by
                rw [productIntersectionToInfinityAmbientRing_innerX,
                  productIntersectionToStandardAmbientRing_innerX,
                  antidiagonalZOverY_mul_productNeighborhoodAddY_on_intersection]

private theorem productIntersection_ambient_maps_eq
    (W : WeierstrassCurve K) :
    Spec.map (CommRingCat.ofHom
          (productIntersectionToStandardAmbientRing W)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
          (MvPolynomial.isHomogeneous_X K 2) zero_lt_one =
      Spec.map (CommRingCat.ofHom
          (productIntersectionToInfinityAmbientRing W)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
          (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
  let H := homogeneousPieces K
  let X₁ : MvPolynomial (Fin 3) K := MvPolynomial.X 1
  let X₂ : MvPolynomial (Fin 3) K := MvPolynomial.X 2
  let q : MvPolynomial (Fin 3) K := X₂ * X₁
  let hq : q ∈ H 2 := by
    simpa only [H, X₁, X₂, q, one_add_one_eq_two] using
      SetLike.mul_mem_graded
        (A := homogeneousPieces K) (i := 1) (j := 1)
        (gi := MvPolynomial.X 2) (gj := MvPolynomial.X 1)
        (MvPolynomial.isHomogeneous_X K 2)
        (MvPolynomial.isHomogeneous_X K 1)
  have hstandard :=
    projectiveYZOverlapToProductIntersectionRing_comp_standard W
  have hinfinity :=
    projectiveYZOverlapToProductIntersectionRing_comp_infinity W
  calc
    Spec.map (CommRingCat.ofHom
          (productIntersectionToStandardAmbientRing W)) ≫
        Proj.awayι H X₂ (MvPolynomial.isHomogeneous_X K 2)
          zero_lt_one =
      (Spec.map (CommRingCat.ofHom
            (projectiveYZOverlapToProductIntersectionRing W)) ≫
          Spec.map (CommRingCat.ofHom
            (standardChartToProjectiveYZOverlapRing (K := K)))) ≫
        Proj.awayι H X₂ (MvPolynomial.isHomogeneous_X K 2)
          zero_lt_one := by
            rw [← Spec.map_comp]
            congr 2
            apply CommRingCat.hom_ext
            exact hstandard.symm
    _ = Spec.map (CommRingCat.ofHom
          (projectiveYZOverlapToProductIntersectionRing W)) ≫
        Proj.awayι H q hq (by omega) := by
          simpa only [standardChartToProjectiveYZOverlapRing,
            Category.assoc] using congrArg
            (fun f => Spec.map (CommRingCat.ofHom
              (projectiveYZOverlapToProductIntersectionRing W)) ≫ f)
            (Proj.SpecMap_awayMap_awayι
              (f := X₂) (g := X₁) (x := q) H
              (MvPolynomial.isHomogeneous_X K 2) zero_lt_one
              (MvPolynomial.isHomogeneous_X K 1) rfl)
    _ = (Spec.map (CommRingCat.ofHom
          (projectiveYZOverlapToProductIntersectionRing W)) ≫
          Spec.map (CommRingCat.ofHom
            (infinityChartToProjectiveYZOverlapRing (K := K)))) ≫
        Proj.awayι H X₁ (MvPolynomial.isHomogeneous_X K 1)
          zero_lt_one := by
            simpa only [infinityChartToProjectiveYZOverlapRing,
              Category.assoc] using congrArg
              (fun f => Spec.map (CommRingCat.ofHom
                (projectiveYZOverlapToProductIntersectionRing W)) ≫ f)
              (Proj.SpecMap_awayMap_awayι
                (f := X₁) (g := X₂) (x := q) H
                (MvPolynomial.isHomogeneous_X K 1) zero_lt_one
                (MvPolynomial.isHomogeneous_X K 2)
                (mul_comm X₂ X₁)).symm
    _ = Spec.map (CommRingCat.ofHom
          (productIntersectionToInfinityAmbientRing W)) ≫
        Proj.awayι H X₁ (MvPolynomial.isHomogeneous_X K 1)
          zero_lt_one := by
            rw [← Spec.map_comp]
            congr 2
            apply CommRingCat.hom_ext
            exact hinfinity

/-! ## Equality of the actual cubic-valued morphisms on the overlap -/

/-- Restriction from the exact overlap to the existing `D(B₁₂)` source
chart. -/
def productAntidiagonalIntersectionToProductNeighborhood
    (W : WeierstrassCurve K) :
    Spec (.of (productAntidiagonalIntersectionCoordinateRing W)) ⟶
      Spec (.of (productNeighborhoodCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (productNeighborhoodToAntidiagonalIntersectionRing W))

/-- Restriction from the exact overlap to the infinity-output `D(Y)` source
chart. -/
def productAntidiagonalIntersectionToAntidiagonalChart
    (W : WeierstrassCurve K) :
    Spec (.of (productAntidiagonalIntersectionCoordinateRing W)) ⟶
      Spec (.of (antidiagonalChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (antidiagonalChartToIntersectionRing W))

/-- Structure morphism of the infinity-output chart. -/
def antidiagonalChartStructureMap (W : WeierstrassCurve K) :
    Spec (.of (antidiagonalChartCoordinateRing W)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (antidiagonalChartCoefficientHom W))

/-- The normalized antidiagonal formula as a morphism into the actual
`Y ≠ 0` chart. -/
def antidiagonalAdditionInfinityMorphism (W : WeierstrassCurve K) :
    Spec (.of (antidiagonalChartCoordinateRing W)) ⟶
      coveringChartScheme W false :=
  Spec.map (CommRingCat.ofHom (antidiagonalAdditionToInfinityRing W))

/-- The infinity-chart addition morphism lies over the ground field. -/
@[reassoc]
theorem antidiagonalAdditionInfinityMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    antidiagonalAdditionInfinityMorphism W ≫
        Spec.map (CommRingCat.ofHom
          (coveringChartStructureRingHom W false)) =
      antidiagonalChartStructureMap W := by
  rw [antidiagonalAdditionInfinityMorphism,
    antidiagonalChartStructureMap, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  congr 1
  exact antidiagonalAdditionToInfinityRing_comp_coefficient W

/-- The antidiagonal formula as an actual morphism into the concrete reduced
projective Weierstrass cubic. -/
def antidiagonalAdditionProjectiveMorphism (W : WeierstrassCurve K) :
    Spec (.of (antidiagonalChartCoordinateRing W)) ⟶ scheme W :=
  antidiagonalAdditionInfinityMorphism W ≫ coveringChartMap W false

/-- Projective antidiagonal addition respects the structural maps to the
base field. -/
theorem antidiagonalAdditionProjectiveMorphism_comp_structureMap
    (W : WeierstrassCurve K) :
    antidiagonalAdditionProjectiveMorphism W ≫ structureMap W =
      antidiagonalChartStructureMap W := by
  have hchart : coveringChartMap W false ≫ structureMap W =
      Spec.map (CommRingCat.ofHom
        (coveringChartStructureRingHom W false)) :=
    coveringChartMap_comp_structureMap W false
  simp only [antidiagonalAdditionProjectiveMorphism, Category.assoc,
    hchart, antidiagonalAdditionInfinityMorphism_comp_structureMap]

private theorem productIntersection_productNeighborhood_ambient
    (W : WeierstrassCurve K) :
    (productAntidiagonalIntersectionToProductNeighborhood W ≫
        productNeighborhoodAdditionProjectiveMorphism W) ≫ inclusion W =
      Spec.map (CommRingCat.ofHom
          (productIntersectionToStandardAmbientRing W)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
          (MvPolynomial.isHomogeneous_X K 2) zero_lt_one := by
  calc
    _ = productAntidiagonalIntersectionToProductNeighborhood W ≫
          productNeighborhoodAdditionAffineMorphism W ≫
          (affineEquationSchemeIsoStandardChart W).hom ≫
          coveringChartAmbientMap W true := by
            simpa only [Category.assoc] using congrArg
              (fun f =>
                productAntidiagonalIntersectionToProductNeighborhood W ≫ f)
              (productNeighborhoodAdditionProjectiveMorphism_comp_inclusion W)
    _ = _ := by
      change
        (Spec.map (CommRingCat.ofHom
              (productNeighborhoodToAntidiagonalIntersectionRing W)) ≫
            Spec.map (CommRingCat.ofHom
              (productNeighborhoodAdditionToAffineRing W)) ≫
            Spec.map
              (affineEquationToStandardChartRingEquiv W).toCommRingCatIso.symm.hom ≫
            Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (coveringChartIdeal W true)))) ≫
          Proj.awayι (homogeneousPieces K) (MvPolynomial.X 2)
            (MvPolynomial.isHomogeneous_X K 2) zero_lt_one = _
      simp only [← Spec.map_comp]
      congr 2

private theorem productIntersection_antidiagonal_ambient
    (W : WeierstrassCurve K) :
    (productAntidiagonalIntersectionToAntidiagonalChart W ≫
        antidiagonalAdditionProjectiveMorphism W) ≫ inclusion W =
      Spec.map (CommRingCat.ofHom
          (productIntersectionToInfinityAmbientRing W)) ≫
        Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
          (MvPolynomial.isHomogeneous_X K 1) zero_lt_one := by
  calc
    _ = productAntidiagonalIntersectionToAntidiagonalChart W ≫
          antidiagonalAdditionInfinityMorphism W ≫
          coveringChartAmbientMap W false := by
            simpa only [antidiagonalAdditionProjectiveMorphism,
              Category.assoc] using congrArg
              (fun f =>
                productAntidiagonalIntersectionToAntidiagonalChart W ≫
                  antidiagonalAdditionInfinityMorphism W ≫ f)
              (coveringChartMap_comp_inclusion W false)
    _ = _ := by
      change
        (Spec.map (CommRingCat.ofHom
              (antidiagonalChartToIntersectionRing W)) ≫
            Spec.map (CommRingCat.ofHom
              (antidiagonalAdditionToInfinityRing W)) ≫
            Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (coveringChartIdeal W false)))) ≫
          Proj.awayι (homogeneousPieces K) (MvPolynomial.X 1)
            (MvPolynomial.isHomogeneous_X K 1) zero_lt_one = _
      simp only [← Spec.map_comp]
      congr 2

/-- The affine `D(B₁₂)` addition formula and the infinity-output `D(Y)`
formula are the same morphism into the concrete reduced projective cubic on
their exact intersection `D(B₁₂Y)`. -/
theorem productAntidiagonalIntersection_additionProjective_eq
    (W : WeierstrassCurve K) :
    productAntidiagonalIntersectionToProductNeighborhood W ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      productAntidiagonalIntersectionToAntidiagonalChart W ≫
        antidiagonalAdditionProjectiveMorphism W := by
  apply (cancel_mono (inclusion W)).mp
  rw [productIntersection_productNeighborhood_ambient,
    productIntersection_antidiagonal_ambient]
  exact productIntersection_ambient_maps_eq W

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
