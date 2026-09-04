/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCrossCompatibility

/-!
# The global affine-pair atlas for Weierstrass addition

The two affine-output charts `D(x₁-x₂)` and `D(B₁₂)` do not contain inverse
pairs.  Their two denominator-cleared infinity extensions cover the missing
locus.  All six pairwise intersections now carry equality of the actual
scheme morphisms.  The coverage proof below is the honest geometric step: if
all four chart coordinates vanished at a prime, the first universal point
would be a singular point of the elliptic Weierstrass cubic.

This file assumes ellipticity only where nonsingularity is actually used.  It
does not assume a group object or a pointwise addition law.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The ordinary secant chart, the `D(B₁₂)` product-neighbourhood chart, and
their two infinity extensions cover the entire affine-pair presentation. -/
theorem affinePairAdditionCharts_cover
    (W : WeierstrassCurve K) [W.IsElliptic] :
    PrimeSpectrum.basicOpen (additionB12 W) ⊔
        (PrimeSpectrum.basicOpen (secantDenominator W) ⊔
          (PrimeSpectrum.basicOpen (antidiagonalAddYNumerator W) ⊔
            PrimeSpectrum.basicOpen (verticalAddYNumerator W))) = ⊤ := by
  apply top_unique
  intro p _
  change additionB12 W ∉ p.asIdeal ∨
    secantDenominator W ∉ p.asIdeal ∨
    antidiagonalAddYNumerator W ∉ p.asIdeal ∨
    verticalAddYNumerator W ∉ p.asIdeal
  by_contra hcover
  push Not at hcover
  rcases hcover with ⟨hB, hD, hantiY, hvertY⟩
  have hantiRight :
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
  have hantiSum :
      antidiagonalAddYNumerator W + additionA12 W ^ 3 ∈ p.asIdeal := by
    rw [antidiagonalAddYNumerator_add_A12_cube]
    exact hantiRight
  have hA3 : additionA12 W ^ 3 ∈ p.asIdeal := by
    simpa using p.asIdeal.sub_mem hantiSum hantiY
  have hA : additionA12 W ∈ p.asIdeal :=
    (show p.asIdeal.IsPrime from inferInstance).mem_of_pow_mem 3 hA3
  have hvertRight :
      verticalAdditionB W *
          (-2 * secantPairCoefficientHom W W.a₁ * verticalAdditionA W ^ 2 +
            verticalAdditionA W *
              ((secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                  secantPairX₂ W) -
                secantPairCoefficientHom W W.a₁ ^ 2 + secantPairX₁ W) *
              verticalAdditionB W +
            (secantPairCoefficientHom W W.a₁ *
                (secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                  secantPairX₂ W) -
              (secantPairY₁ W + secantPairCoefficientHom W W.a₃)) *
              verticalAdditionB W ^ 2) ∈ p.asIdeal := by
    apply p.asIdeal.mul_mem_right
    simpa [verticalAdditionB, secantDenominator] using hD
  have hvertSum :
      verticalAddYNumerator W + verticalAdditionA W ^ 3 ∈ p.asIdeal := by
    rw [verticalAddYNumerator_add_A_cube]
    exact hvertRight
  have hC3 : verticalAdditionA W ^ 3 ∈ p.asIdeal := by
    simpa using p.asIdeal.sub_mem hvertSum hvertY
  have hC : verticalAdditionA W ∈ p.asIdeal :=
    (show p.asIdeal.IsPrime from inferInstance).mem_of_pow_mem 3 hC3
  let S := secantPairCoordinateRing W
  let Q := S ⧸ p.asIdeal
  letI : CommRing Q := Ideal.Quotient.commRing p.asIdeal
  letI : IsDomain Q :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr inferInstance
  let L := FractionRing Q
  let q₀ : S →+* Q := Ideal.Quotient.mk p.asIdeal
  let q : S →+* L := (algebraMap Q L).comp q₀
  let g : K →+* L := q.comp (secantPairCoefficientHom W)
  let x₁ : L := q (secantPairX₁ W)
  let y₁ : L := q (secantPairY₁ W)
  let x₂ : L := q (secantPairX₂ W)
  let y₂ : L := q (secantPairY₂ W)
  have hequation : (W.map g).toAffine.Equation x₁ y₁ := by
    simpa [g, x₁, y₁, WeierstrassCurve.map_map] using
      (secantPair_equation_left W).map q
  have hns := ((W.map g).toAffine.equation_iff_nonsingular).mp hequation
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  have hqB : q (additionB12 W) = 0 := by
    change algebraMap Q L (q₀ (additionB12 W)) = 0
    rw [show q₀ (additionB12 W) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hB, map_zero]
  have hqD : q (secantDenominator W) = 0 := by
    change algebraMap Q L (q₀ (secantDenominator W)) = 0
    rw [show q₀ (secantDenominator W) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hD, map_zero]
  have hqA : q (additionA12 W) = 0 := by
    change algebraMap Q L (q₀ (additionA12 W)) = 0
    rw [show q₀ (additionA12 W) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hA, map_zero]
  have hqC : q (verticalAdditionA W) = 0 := by
    change algebraMap Q L (q₀ (verticalAdditionA W)) = 0
    rw [show q₀ (verticalAdditionA W) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr hC, map_zero]
  have hx₂ : x₂ = x₁ := by
    dsimp only [x₁, x₂]
    exact (sub_eq_zero.mp (by simpa [secantDenominator] using hqD)).symm
  have hy₂ : y₂ = y₁ := by
    dsimp only [y₁, y₂]
    exact (sub_eq_zero.mp (by simpa [verticalAdditionA] using hqC)).symm
  have hderivativeX :
      (W.map g).a₁ * y₁ -
          (3 * x₁ ^ 2 + 2 * (W.map g).a₂ * x₁ + (W.map g).a₄) = 0 := by
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄]
    dsimp only [g, x₁, y₁, x₂, y₂] at hx₂ hy₂ ⊢
    simp only [RingHom.comp_apply]
    have h := hqA
    simp only [additionA12, map_sub, map_add, map_mul, map_pow] at h
    rw [hx₂, hy₂] at h
    linear_combination -h
  have hderivativeY :
      2 * y₁ + (W.map g).a₁ * x₁ + (W.map g).a₃ = 0 := by
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    dsimp only [g, x₁, y₁, x₂, y₂] at hy₂ ⊢
    simp only [RingHom.comp_apply]
    have h := hqB
    simp only [additionB12, map_add, map_mul] at h
    rw [hy₂] at h
    linear_combination h
  rcases hns.2 with hx | hy
  · exact hx hderivativeX
  · exact hy hderivativeY

/-! ## Generic gluing on two principal opens -/

private abbrev principalChartScheme (R : Type u) [CommRing R] (d : R) :=
  Spec (.of (Localization.Away d))

private def principalChartMap (R : Type u) [CommRing R] (d : R) :
    principalChartScheme R d ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away d)))

private instance principalChartMap_isOpenImmersion
    (R : Type u) [CommRing R] (d : R) :
    IsOpenImmersion (principalChartMap R d) := by
  dsimp only [principalChartMap, principalChartScheme]
  infer_instance

private abbrev principalOverlapScheme
    (R : Type u) [CommRing R] (d e : R) :=
  Spec (.of (Localization.Away (d * e)))

private def principalOverlapMap (R : Type u) [CommRing R] (d e : R) :
    principalOverlapScheme R d e ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap R (Localization.Away (d * e))))

private instance principalOverlapMap_isOpenImmersion
    (R : Type u) [CommRing R] (d e : R) :
    IsOpenImmersion (principalOverlapMap R d e) := by
  dsimp only [principalOverlapMap, principalOverlapScheme]
  infer_instance

private noncomputable def principalOverlapToLeftRing
    (R : Type u) [CommRing R] (d e : R) :
    Localization.Away d →+* Localization.Away (d * e) :=
  IsLocalization.Away.awayToAwayRight
    (S := Localization.Away d) (P := Localization.Away (d * e)) d e

private noncomputable def principalOverlapToRightRing
    (R : Type u) [CommRing R] (d e : R) :
    Localization.Away e →+* Localization.Away (d * e) :=
  IsLocalization.Away.awayToAwayLeft
    (S := Localization.Away e) (P := Localization.Away (d * e)) e d

private def principalOverlapToLeft
    (R : Type u) [CommRing R] (d e : R) :
    principalOverlapScheme R d e ⟶ principalChartScheme R d :=
  Spec.map (CommRingCat.ofHom (principalOverlapToLeftRing R d e))

private def principalOverlapToRight
    (R : Type u) [CommRing R] (d e : R) :
    principalOverlapScheme R d e ⟶ principalChartScheme R e :=
  Spec.map (CommRingCat.ofHom (principalOverlapToRightRing R d e))

private theorem principalOverlapToLeft_comp
    (R : Type u) [CommRing R] (d e : R) :
    principalOverlapToLeft R d e ≫ principalChartMap R d =
      principalOverlapMap R d e := by
  have hring : (principalOverlapToLeftRing R d e).comp
      (algebraMap R (Localization.Away d)) =
        algebraMap R (Localization.Away (d * e)) := by
    apply RingHom.ext
    intro a
    exact IsLocalization.Away.awayToAwayRight_eq
      (S := Localization.Away d) (P := Localization.Away (d * e)) d e a
  have hmap := congrArg
    (fun f : R →+* Localization.Away (d * e) =>
      Spec.map (CommRingCat.ofHom f)) hring
  rw [principalOverlapToLeft, principalChartMap, principalOverlapMap,
    ← Spec.map_comp]
  exact hmap

private theorem principalOverlapToRight_comp
    (R : Type u) [CommRing R] (d e : R) :
    principalOverlapToRight R d e ≫ principalChartMap R e =
      principalOverlapMap R d e := by
  have hring : (principalOverlapToRightRing R d e).comp
      (algebraMap R (Localization.Away e)) =
        algebraMap R (Localization.Away (d * e)) := by
    apply RingHom.ext
    intro a
    exact IsLocalization.Away.awayToAwayLeft_eq
      (S := Localization.Away e) (P := Localization.Away (d * e)) e d a
  have hmap := congrArg
    (fun f : R →+* Localization.Away (d * e) =>
      Spec.map (CommRingCat.ofHom f)) hring
  rw [principalOverlapToRight, principalChartMap, principalOverlapMap,
    ← Spec.map_comp]
  exact hmap

private theorem principalOverlap_range
    (R : Type u) [CommRing R] (d e : R) :
    Set.range ⇑(principalOverlapMap R d e) =
      Set.range ⇑(pullback.fst (principalChartMap R d)
        (principalChartMap R e) ≫ principalChartMap R d) := by
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
    ← Scheme.Hom.coe_opensRange]
  dsimp only [principalOverlapMap, principalChartMap]
  rw [Scheme.Hom.opensRange_localizationAway
      (R := CommRingCat.of R) (d * e),
    Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) d,
    Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of R) e]
  ext x
  change d * e ∉ x.asIdeal ↔ d ∉ x.asIdeal ∧ e ∉ x.asIdeal
  constructor
  · intro hde
    exact ⟨fun hd => hde (x.asIdeal.mul_mem_right e hd),
      fun he => hde (x.asIdeal.mul_mem_left d he)⟩
  · rintro ⟨hd, he⟩ hde
    exact x.isPrime.mem_or_mem hde |>.elim hd he
private theorem principalChart_morphisms_compatible
    (R : Type u) [CommRing R] (d e : R) {Y : Scheme.{u}}
    (fd : principalChartScheme R d ⟶ Y)
    (fe : principalChartScheme R e ⟶ Y)
    (h : principalOverlapToLeft R d e ≫ fd =
      principalOverlapToRight R d e ≫ fe) :
    pullback.fst (principalChartMap R d) (principalChartMap R e) ≫ fd =
      pullback.snd (principalChartMap R d) (principalChartMap R e) ≫ fe := by
  let overlapIso : principalOverlapScheme R d e ≅
      pullback (principalChartMap R d) (principalChartMap R e) :=
    IsOpenImmersion.isoOfRangeEq (principalOverlapMap R d e)
      (pullback.fst (principalChartMap R d) (principalChartMap R e) ≫
        principalChartMap R d) (principalOverlap_range R d e)
  have hfst : overlapIso.hom ≫
      pullback.fst (principalChartMap R d) (principalChartMap R e) =
        principalOverlapToLeft R d e := by
    apply (cancel_mono (principalChartMap R d)).mp
    rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
      principalOverlapToLeft_comp]
  have hsnd : overlapIso.hom ≫
      pullback.snd (principalChartMap R d) (principalChartMap R e) =
        principalOverlapToRight R d e := by
    apply (cancel_mono (principalChartMap R e)).mp
    calc
      _ = overlapIso.hom ≫
          (pullback.snd (principalChartMap R d)
            (principalChartMap R e) ≫ principalChartMap R e) :=
        Category.assoc _ _ _
      _ = overlapIso.hom ≫
          (pullback.fst (principalChartMap R d)
            (principalChartMap R e) ≫ principalChartMap R d) :=
        congrArg (fun f => overlapIso.hom ≫ f) pullback.condition.symm
      _ = principalOverlapMap R d e :=
        IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
      _ = _ := (principalOverlapToRight_comp R d e).symm
  apply (cancel_epi overlapIso.hom).mp
  calc
    _ = (overlapIso.hom ≫
          pullback.fst (principalChartMap R d) (principalChartMap R e)) ≫
        fd := (Category.assoc _ _ _).symm
    _ = principalOverlapToLeft R d e ≫ fd :=
      congrArg (fun f => f ≫ fd) hfst
    _ = principalOverlapToRight R d e ≫ fe := h
    _ = (overlapIso.hom ≫
          pullback.snd (principalChartMap R d) (principalChartMap R e)) ≫
        fe := congrArg (fun f => f ≫ fe) hsnd.symm
    _ = _ := Category.assoc _ _ _

private theorem pullback_morphism_compatible_self
    {U X Y : Scheme.{u}} (i : U ⟶ X) [Mono i] (f : U ⟶ Y) :
    pullback.fst i i ≫ f = pullback.snd i i ≫ f := by
  have hfst : pullback.fst i i = pullback.snd i i := by
    apply (cancel_mono i).mp
    exact pullback.condition
  exact congrArg (fun q => q ≫ f) hfst

private theorem pullback_morphism_compatible_symm
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

private theorem productSecant_chart_compatible
    (W : WeierstrassCurve K) :
    pullback.fst (productNeighborhoodToPair W) (secantChartToPair W) ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      pullback.snd (productNeighborhoodToPair W) (secantChartToPair W) ≫
        secantAdditionProjectiveMorphism W := by
  change pullback.fst
      (principalChartMap (secantPairCoordinateRing W) (additionB12 W))
      (principalChartMap (secantPairCoordinateRing W) (secantDenominator W)) ≫
        productNeighborhoodAdditionProjectiveMorphism W =
    pullback.snd
      (principalChartMap (secantPairCoordinateRing W) (additionB12 W))
      (principalChartMap (secantPairCoordinateRing W) (secantDenominator W)) ≫
        secantAdditionProjectiveMorphism W
  apply principalChart_morphisms_compatible
  exact additionSecantIntersection_additionProjective_eq W

private theorem productAntidiagonal_chart_compatible
    (W : WeierstrassCurve K) :
    pullback.fst (productNeighborhoodToPair W) (antidiagonalChartToPair W) ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      pullback.snd (productNeighborhoodToPair W) (antidiagonalChartToPair W) ≫
        antidiagonalAdditionProjectiveMorphism W := by
  change pullback.fst
      (principalChartMap (secantPairCoordinateRing W) (additionB12 W))
      (principalChartMap (secantPairCoordinateRing W)
        (antidiagonalAddYNumerator W)) ≫
        productNeighborhoodAdditionProjectiveMorphism W =
    pullback.snd
      (principalChartMap (secantPairCoordinateRing W) (additionB12 W))
      (principalChartMap (secantPairCoordinateRing W)
        (antidiagonalAddYNumerator W)) ≫
        antidiagonalAdditionProjectiveMorphism W
  apply principalChart_morphisms_compatible
  exact productAntidiagonalIntersection_additionProjective_eq W

private theorem productVertical_chart_compatible
    (W : WeierstrassCurve K) :
    pullback.fst (productNeighborhoodToPair W) (verticalChartToPair W) ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      pullback.snd (productNeighborhoodToPair W) (verticalChartToPair W) ≫
        verticalAdditionProjectiveMorphism W := by
  change pullback.fst
      (principalChartMap (secantPairCoordinateRing W) (additionB12 W))
      (principalChartMap (secantPairCoordinateRing W)
        (verticalAddYNumerator W)) ≫
        productNeighborhoodAdditionProjectiveMorphism W =
    pullback.snd
      (principalChartMap (secantPairCoordinateRing W) (additionB12 W))
      (principalChartMap (secantPairCoordinateRing W)
        (verticalAddYNumerator W)) ≫
        verticalAdditionProjectiveMorphism W
  apply principalChart_morphisms_compatible
  exact productVerticalIntersection_additionProjective_eq W

private theorem secantAntidiagonal_chart_compatible
    (W : WeierstrassCurve K) :
    pullback.fst (secantChartToPair W) (antidiagonalChartToPair W) ≫
        secantAdditionProjectiveMorphism W =
      pullback.snd (secantChartToPair W) (antidiagonalChartToPair W) ≫
        antidiagonalAdditionProjectiveMorphism W := by
  change pullback.fst
      (principalChartMap (secantPairCoordinateRing W) (secantDenominator W))
      (principalChartMap (secantPairCoordinateRing W)
        (antidiagonalAddYNumerator W)) ≫
        secantAdditionProjectiveMorphism W =
    pullback.snd
      (principalChartMap (secantPairCoordinateRing W) (secantDenominator W))
      (principalChartMap (secantPairCoordinateRing W)
        (antidiagonalAddYNumerator W)) ≫
        antidiagonalAdditionProjectiveMorphism W
  apply principalChart_morphisms_compatible
  exact secantAntidiagonalIntersection_additionProjective_eq W

private theorem secantVertical_chart_compatible
    (W : WeierstrassCurve K) :
    pullback.fst (secantChartToPair W) (verticalChartToPair W) ≫
        secantAdditionProjectiveMorphism W =
      pullback.snd (secantChartToPair W) (verticalChartToPair W) ≫
        verticalAdditionProjectiveMorphism W := by
  change pullback.fst
      (principalChartMap (secantPairCoordinateRing W) (secantDenominator W))
      (principalChartMap (secantPairCoordinateRing W)
        (verticalAddYNumerator W)) ≫
        secantAdditionProjectiveMorphism W =
    pullback.snd
      (principalChartMap (secantPairCoordinateRing W) (secantDenominator W))
      (principalChartMap (secantPairCoordinateRing W)
        (verticalAddYNumerator W)) ≫
        verticalAdditionProjectiveMorphism W
  apply principalChart_morphisms_compatible
  exact secantVerticalIntersection_additionProjective_eq W

private theorem antidiagonalVertical_chart_compatible
    (W : WeierstrassCurve K) :
    pullback.fst (antidiagonalChartToPair W) (verticalChartToPair W) ≫
        antidiagonalAdditionProjectiveMorphism W =
      pullback.snd (antidiagonalChartToPair W) (verticalChartToPair W) ≫
        verticalAdditionProjectiveMorphism W := by
  change pullback.fst
      (principalChartMap (secantPairCoordinateRing W)
        (antidiagonalAddYNumerator W))
      (principalChartMap (secantPairCoordinateRing W)
        (verticalAddYNumerator W)) ≫
        antidiagonalAdditionProjectiveMorphism W =
    pullback.snd
      (principalChartMap (secantPairCoordinateRing W)
        (antidiagonalAddYNumerator W))
      (principalChartMap (secantPairCoordinateRing W)
        (verticalAddYNumerator W)) ≫
        verticalAdditionProjectiveMorphism W
  apply principalChart_morphisms_compatible
  exact infinityIntersection_additionProjective_eq W

/-! ## The glued affine-pair addition morphism -/

/-- The four principal charts used to define addition on pairs of affine
Weierstrass points. -/
inductive AffinePairAdditionChart where
  | productNeighborhood
  | secant
  | antidiagonal
  | vertical
  deriving DecidableEq

/-- Source scheme of one chart in the affine-pair addition atlas. -/
def affinePairAdditionChartScheme (W : WeierstrassCurve K) :
    AffinePairAdditionChart → Scheme
  | .productNeighborhood =>
      Spec (.of (productNeighborhoodCoordinateRing W))
  | .secant => Spec (.of (secantChartCoordinateRing W))
  | .antidiagonal => Spec (.of (antidiagonalChartCoordinateRing W))
  | .vertical => Spec (.of (verticalChartCoordinateRing W))

/-- Open immersion of an addition chart into the affine-pair presentation. -/
def affinePairAdditionChartMap (W : WeierstrassCurve K) :
    (c : AffinePairAdditionChart) →
      affinePairAdditionChartScheme W c ⟶
        Spec (.of (secantPairCoordinateRing W))
  | .productNeighborhood => productNeighborhoodToPair W
  | .secant => secantChartToPair W
  | .antidiagonal => antidiagonalChartToPair W
  | .vertical => verticalChartToPair W

instance affinePairAdditionChartMap_isOpenImmersion
    (W : WeierstrassCurve K) (c : AffinePairAdditionChart) :
    IsOpenImmersion (affinePairAdditionChartMap W c) := by
  cases c <;> simp only [affinePairAdditionChartMap,
    affinePairAdditionChartScheme] <;> infer_instance

/-- The checked local addition morphism on a chart. -/
def affinePairAdditionChartMorphism (W : WeierstrassCurve K) :
    (c : AffinePairAdditionChart) →
      affinePairAdditionChartScheme W c ⟶ scheme W
  | .productNeighborhood => productNeighborhoodAdditionProjectiveMorphism W
  | .secant => secantAdditionProjectiveMorphism W
  | .antidiagonal => antidiagonalAdditionProjectiveMorphism W
  | .vertical => verticalAdditionProjectiveMorphism W

private theorem affinePairAdditionChart_preimage_exists
    (W : WeierstrassCurve K) [W.IsElliptic]
    (x : Spec (.of (secantPairCoordinateRing W))) :
    ∃ c y, affinePairAdditionChartMap W c y = x := by
  have hx :
      additionB12 W ∉ x.asIdeal ∨
        secantDenominator W ∉ x.asIdeal ∨
        antidiagonalAddYNumerator W ∉ x.asIdeal ∨
        verticalAddYNumerator W ∉ x.asIdeal := by
    have hmem : x ∈
        PrimeSpectrum.basicOpen (additionB12 W) ⊔
          (PrimeSpectrum.basicOpen (secantDenominator W) ⊔
            (PrimeSpectrum.basicOpen (antidiagonalAddYNumerator W) ⊔
              PrimeSpectrum.basicOpen (verticalAddYNumerator W))) := by
      rw [affinePairAdditionCharts_cover W]
      trivial
    exact hmem
  rcases hx with hproduct | hsecant | hanti | hvert
  · refine ⟨AffinePairAdditionChart.productNeighborhood, ?_⟩
    change ∃ y, productNeighborhoodToPair W y = x
    have hmem : x ∈ (productNeighborhoodToPair W).opensRange := by
      rw [productNeighborhoodToPair_opensRange]
      exact hproduct
    exact hmem
  · refine ⟨AffinePairAdditionChart.secant, ?_⟩
    change ∃ y, secantChartToPair W y = x
    have hmem : x ∈ (secantChartToPair W).opensRange := by
      rw [secantChartToPair_opensRange]
      exact hsecant
    exact hmem
  · refine ⟨AffinePairAdditionChart.antidiagonal, ?_⟩
    change ∃ y, antidiagonalChartToPair W y = x
    have hmem : x ∈ (antidiagonalChartToPair W).opensRange := by
      rw [antidiagonalChartToPair_opensRange]
      exact hanti
    exact hmem
  · refine ⟨AffinePairAdditionChart.vertical, ?_⟩
    change ∃ y, verticalChartToPair W y = x
    have hmem : x ∈ (verticalChartToPair W).opensRange := by
      rw [verticalChartToPair_opensRange]
      exact hvert
    exact hmem

/-- The four checked principal opens as an actual scheme open cover of the
affine-pair presentation. -/
noncomputable def affinePairAdditionOpenCover
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (Spec (.of (secantPairCoordinateRing W))).OpenCover :=
  Scheme.Cover.mkOfCovers AffinePairAdditionChart
    (affinePairAdditionChartScheme W)
    (affinePairAdditionChartMap W)
    (affinePairAdditionChart_preimage_exists W)
    (fun c => affinePairAdditionChartMap_isOpenImmersion W c)

private theorem affinePairAdditionChart_compatible
    (W : WeierstrassCurve K) (i j : AffinePairAdditionChart) :
    pullback.fst (affinePairAdditionChartMap W i)
          (affinePairAdditionChartMap W j) ≫
        affinePairAdditionChartMorphism W i =
      pullback.snd (affinePairAdditionChartMap W i)
          (affinePairAdditionChartMap W j) ≫
        affinePairAdditionChartMorphism W j := by
  cases i <;> cases j
  · exact pullback_morphism_compatible_self _ _
  · exact productSecant_chart_compatible W
  · exact productAntidiagonal_chart_compatible W
  · exact productVertical_chart_compatible W
  · exact pullback_morphism_compatible_symm _ _ _ _
      (productSecant_chart_compatible W)
  · exact pullback_morphism_compatible_self _ _
  · exact secantAntidiagonal_chart_compatible W
  · exact secantVertical_chart_compatible W
  · exact pullback_morphism_compatible_symm _ _ _ _
      (productAntidiagonal_chart_compatible W)
  · exact pullback_morphism_compatible_symm _ _ _ _
      (secantAntidiagonal_chart_compatible W)
  · exact pullback_morphism_compatible_self _ _
  · exact antidiagonalVertical_chart_compatible W
  · exact pullback_morphism_compatible_symm _ _ _ _
      (productVertical_chart_compatible W)
  · exact pullback_morphism_compatible_symm _ _ _ _
      (secantVertical_chart_compatible W)
  · exact pullback_morphism_compatible_symm _ _ _ _
      (antidiagonalVertical_chart_compatible W)
  · exact pullback_morphism_compatible_self _ _

private theorem affinePairAdditionOpenCover_compatible
    (W : WeierstrassCurve K) [W.IsElliptic]
    (i j : (affinePairAdditionOpenCover W).I₀) :
    pullback.fst ((affinePairAdditionOpenCover W).f i)
          ((affinePairAdditionOpenCover W).f j) ≫
        affinePairAdditionChartMorphism W i =
      pullback.snd ((affinePairAdditionOpenCover W).f i)
          ((affinePairAdditionOpenCover W).f j) ≫
        affinePairAdditionChartMorphism W j := by
  exact affinePairAdditionChart_compatible W i j

/-- The four local formulas glued to one honest morphism from the entire
affine-pair presentation to the concrete projective Weierstrass cubic. -/
noncomputable def affinePairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Spec (.of (secantPairCoordinateRing W)) ⟶ scheme W :=
  (affinePairAdditionOpenCover W).glueMorphisms
    (affinePairAdditionChartMorphism W)
    (affinePairAdditionOpenCover_compatible W)

@[reassoc]
theorem productNeighborhoodToPair_comp_affinePairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    productNeighborhoodToPair W ≫ affinePairAdditionMorphism W =
      productNeighborhoodAdditionProjectiveMorphism W := by
  exact (affinePairAdditionOpenCover W).ι_glueMorphisms
    (affinePairAdditionChartMorphism W)
    (affinePairAdditionOpenCover_compatible W)
    .productNeighborhood

@[reassoc]
theorem secantChartToPair_comp_affinePairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    secantChartToPair W ≫ affinePairAdditionMorphism W =
      secantAdditionProjectiveMorphism W := by
  exact (affinePairAdditionOpenCover W).ι_glueMorphisms
    (affinePairAdditionChartMorphism W)
    (affinePairAdditionOpenCover_compatible W)
    .secant

@[reassoc]
theorem antidiagonalChartToPair_comp_affinePairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    antidiagonalChartToPair W ≫ affinePairAdditionMorphism W =
      antidiagonalAdditionProjectiveMorphism W := by
  exact (affinePairAdditionOpenCover W).ι_glueMorphisms
    (affinePairAdditionChartMorphism W)
    (affinePairAdditionOpenCover_compatible W)
    .antidiagonal

@[reassoc]
theorem verticalChartToPair_comp_affinePairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    verticalChartToPair W ≫ affinePairAdditionMorphism W =
      verticalAdditionProjectiveMorphism W := by
  exact (affinePairAdditionOpenCover W).ι_glueMorphisms
    (affinePairAdditionChartMorphism W)
    (affinePairAdditionOpenCover_compatible W)
    .vertical

/-- The glued affine-pair addition is a morphism over the coefficient field. -/
@[reassoc]
theorem affinePairAdditionMorphism_comp_structureMap
    (W : WeierstrassCurve K) [W.IsElliptic] :
    affinePairAdditionMorphism W ≫ structureMap W =
      Spec.map (CommRingCat.ofHom
        (algebraMap K (secantPairCoordinateRing W))) := by
  refine (affinePairAdditionOpenCover W).hom_ext _ _ ?_
  intro c
  cases c
  · change productNeighborhoodToPair W ≫
      (affinePairAdditionMorphism W ≫ structureMap W) =
        productNeighborhoodToPair W ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantPairCoordinateRing W)))
    rw [← Category.assoc,
      productNeighborhoodToPair_comp_affinePairAdditionMorphism,
      productNeighborhoodAdditionProjectiveMorphism_comp_structureMap]
    rw [productNeighborhoodToPair,
      productNeighborhoodStructureMap, ← Spec.map_comp,
      Spec.map_inj, ← CommRingCat.ofHom_comp]
    ext a
    exact IsScalarTower.algebraMap_apply K
      (secantPairCoordinateRing W) (productNeighborhoodCoordinateRing W) a
  · change secantChartToPair W ≫
      (affinePairAdditionMorphism W ≫ structureMap W) =
        secantChartToPair W ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantPairCoordinateRing W)))
    rw [← Category.assoc, secantChartToPair_comp_affinePairAdditionMorphism,
      secantAdditionProjectiveMorphism_comp_structureMap]
    rw [secantChartToPair,
      secantChartStructureMap, ← Spec.map_comp,
      Spec.map_inj, ← CommRingCat.ofHom_comp]
    ext a
    exact IsScalarTower.algebraMap_apply K
      (secantPairCoordinateRing W) (secantChartCoordinateRing W) a
  · change antidiagonalChartToPair W ≫
      (affinePairAdditionMorphism W ≫ structureMap W) =
        antidiagonalChartToPair W ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantPairCoordinateRing W)))
    rw [← Category.assoc,
      antidiagonalChartToPair_comp_affinePairAdditionMorphism,
      antidiagonalAdditionProjectiveMorphism_comp_structureMap]
    rw [antidiagonalChartToPair,
      antidiagonalChartStructureMap, ← Spec.map_comp,
      Spec.map_inj, ← CommRingCat.ofHom_comp]
    ext a
    exact IsScalarTower.algebraMap_apply K
      (secantPairCoordinateRing W) (antidiagonalChartCoordinateRing W) a
  · change verticalChartToPair W ≫
      (affinePairAdditionMorphism W ≫ structureMap W) =
        verticalChartToPair W ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (secantPairCoordinateRing W)))
    rw [← Category.assoc, verticalChartToPair_comp_affinePairAdditionMorphism,
      verticalAdditionProjectiveMorphism_comp_structureMap]
    rw [verticalChartToPair,
      verticalChartStructureMap, ← Spec.map_comp,
      Spec.map_inj, ← CommRingCat.ofHom_comp]
    ext a
    exact IsScalarTower.algebraMap_apply K
      (secantPairCoordinateRing W) (verticalChartCoordinateRing W) a

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
