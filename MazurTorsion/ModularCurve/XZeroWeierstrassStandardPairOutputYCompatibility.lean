/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassStandardPairAdditionCompatibility
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# The output-Y formula on the standard projective pair

The raw homogeneous addition formula on the standard-by-standard input chart
was previously identified with `standardPairAdditionMorphism` after inverting
its output `Z` coordinate.  This file extends that identity to the entire
output-`Y` principal open.

The design boundary is density of the exact output-`YZ` overlap inside the
output-`Y` open.  We first prove that the universal secant denominator is
nonzero: effective descent along the faithfully flat affine coordinate ring
would otherwise force the universal abscissa to be a ground-field scalar.
Consequently the overlap localization map is injective, hence dominant on
spectra.  Separatedness of the cubic structure morphism then extends the
already checked overlap equality.  The resulting output-`Y` restriction is a
named downstream input for gluing addition across the remaining three members
of the projective-product atlas.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private theorem awayToAwayLeft_injective_of_right_ne_zero
    {A : Type u} [CommRing A] [IsDomain A] (y z : A) (hz : z ≠ 0) :
    Function.Injective
      (IsLocalization.Away.awayToAwayLeft
        (S := Localization.Away y) (P := Localization.Away (z * y)) y z) := by
  rw [IsLocalization.Away.awayToAwayLeft, IsLocalization.Away.lift,
    IsLocalization.lift_injective_iff]
  intro a b
  rw [IsLocalization.eq_iff_exists (Submonoid.powers y),
    IsLocalization.eq_iff_exists (Submonoid.powers (z * y))]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff c.1 y).mp c.2
    have hpow : (z * y) ^ n ∈ Submonoid.powers (z * y) := ⟨n, rfl⟩
    refine ⟨⟨(z * y) ^ n, hpow⟩, ?_⟩
    change (z * y) ^ n * a = (z * y) ^ n * b
    rw [← hn] at hc
    rw [mul_pow, mul_assoc, mul_assoc, hc]
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff c.1 (z * y)).mp c.2
    have hpow : y ^ n ∈ Submonoid.powers y := ⟨n, rfl⟩
    refine ⟨⟨y ^ n, hpow⟩, ?_⟩
    change y ^ n * a = y ^ n * b
    rw [← hn, mul_pow] at hc
    apply mul_left_cancel₀ (pow_ne_zero n hz)
    simpa only [mul_assoc] using hc

/-- The difference of the two universal affine abscissas is nonzero in the
coordinate ring of the affine Weierstrass pair. -/
theorem secantDenominator_ne_zero (W : WeierstrassCurve K) :
    secantDenominator W ≠ 0 := by
  letI : (Ideal.span {W.toAffine.polynomial}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime W.toAffine.irreducible_polynomial.prime
  letI : IsDomain (secantTargetCoordinateRing W) := by infer_instance
  intro h
  have htensor :
      Algebra.TensorProduct.includeLeftSubRight K
          (secantTargetCoordinateRing W) (secantTargetX W) = 0 := by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply]
    rw [← secantPairTensorEquiv_denominator]
    exact congrArg (secantPairTensorEquiv W) h
  have heffective :
      Algebra.IsEffective K (secantTargetCoordinateRing W) :=
    Algebra.IsEffective.of_faithfullyFlat K (secantTargetCoordinateRing W)
  obtain ⟨a, ha⟩ := (heffective (secantTargetX W)).mp htensor
  have hxclass : WeierstrassCurve.Affine.CoordinateRing.XClass W a = 0 := by
    change (WeierstrassCurve.Affine.CoordinateRing.mk W)
      (Polynomial.C (Polynomial.X - Polynomial.C a)) = 0
    rw [map_sub, map_sub]
    change secantTargetX W -
      (Algebra.linearMap K (secantTargetCoordinateRing W)) a = 0
    rw [ha, sub_self]
  exact WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero a hxclass

/-- On the standard input pair, the raw homogeneous output `Z` coordinate is
nonzero before any localization. -/
theorem standardPairRawOutputZ_ne_zero
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3) ≠ 0 := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  rw [projectivePairChartAdditionCoordinates_standard_Z]
  exact pow_ne_zero 3 ((standardPairCoordinateRingAlgEquiv W).injective.ne
    (by simpa using secantDenominator_ne_zero W))

/-- The ring map from the standard-pair exact output-`YZ` overlap to the
output-`Y` localization is injective. -/
theorem standardPairOutputOverlapToInfinityRing_injective
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Function.Injective
      (projectivePairChartAdditionOutputOverlapToInfinityRing W (true, true)) := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  change Function.Injective
    (IsLocalization.Away.awayToAwayLeft
      (S := Localization.Away
        (projectivePairChartAdditionCoordinates W (true, true) (1 : Fin 3)))
      (P := Localization.Away
        (projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3) *
          projectivePairChartAdditionCoordinates W (true, true) (1 : Fin 3)))
      (projectivePairChartAdditionCoordinates W (true, true) (1 : Fin 3))
      (projectivePairChartAdditionCoordinates W (true, true) (2 : Fin 3)))
  exact awayToAwayLeft_injective_of_right_ne_zero _ _
    (standardPairRawOutputZ_ne_zero W)

/-- The exact output-`YZ` overlap is dense in the output-`Y` principal open
on the standard input pair. -/
instance standardPairOutputOverlapToInfinity_isDominant
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsDominant
      (projectivePairChartAdditionOutputOverlapToInfinity W (true, true)) := by
  constructor
  change DenseRange
    (PrimeSpectrum.comap
      (projectivePairChartAdditionOutputOverlapToInfinityRing W (true, true)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  rw [(RingHom.injective_iff_ker_eq_bot _).mp
    (standardPairOutputOverlapToInfinityRing_injective W)]
  exact bot_le

private theorem standardPairOutputOverlap_infinity_formula_eq
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionOutputOverlapToInfinity W (true, true) ≫
        projectivePairChartAdditionOutputOpen W (true, true) false ≫
          standardPairAdditionMorphism W =
      projectivePairChartAdditionOutputOverlapToInfinity W (true, true) ≫
        projectivePairChartAdditionOutputMorphism W (true, true) false := by
  rw [← Category.assoc]
  rw [← projectivePairChartAdditionOutputOverlap_open_eq W (true, true)]
  rw [Category.assoc,
    projectivePairStandardOutputOpen_comp_standardPairAdditionMorphism]
  exact projectivePairChartAdditionOutputOverlap_morphisms_eq W (true, true)

private theorem standardPairOutputInfinity_maps_over_base
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (projectivePairChartAdditionOutputOpen W (true, true) false ≫
        standardPairAdditionMorphism W) ≫ structureMap W =
      projectivePairChartAdditionOutputMorphism W (true, true) false ≫
        structureMap W := by
  rw [Category.assoc,
    standardPairAdditionMorphism_comp_structureMap,
    projectivePairChartAdditionOutputMorphism_comp_structureMap]
  rw [←
    projectivePairChartIsoSpecTensor_hom_comp_standardPairCoordinateRingAlgEquiv_specMap]
  simp only [Category.assoc]
  rw [projectivePairChartAdditionOutputOpen_comp_iso_hom_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change
    algebraMap (projectivePairChartCoordinateRing W (true, true))
        (projectivePairChartAdditionOutputRing W (true, true) false)
        (standardPairCoordinateRingAlgEquiv W
          (algebraMap K (secantPairCoordinateRing W) a)) =
      algebraMap K
        (projectivePairChartAdditionOutputRing W (true, true) false) a
  rw [(standardPairCoordinateRingAlgEquiv W).commutes]
  exact (IsScalarTower.algebraMap_apply K
    (projectivePairChartCoordinateRing W (true, true))
    (projectivePairChartAdditionOutputRing W (true, true) false) a).symm

/-- On the standard projective-pair input chart, the raw output-`Y`
localization is exactly the restriction of the checked addition morphism. -/
@[reassoc]
theorem projectivePairInfinityOutputOpen_comp_standardPairAdditionMorphism
    (W : WeierstrassCurve K) [W.IsElliptic] :
    projectivePairChartAdditionOutputOpen W (true, true) false ≫
        standardPairAdditionMorphism W =
      projectivePairChartAdditionOutputMorphism W (true, true) false := by
  letI : IsDomain (projectivePairChartCoordinateRing W (true, true)) :=
    projectivePairChartCoordinateRing_isDomain W (true, true)
  apply ext_of_isDominant_of_isSeparated
    (structureMap W) (standardPairOutputInfinity_maps_over_base W)
    (projectivePairChartAdditionOutputOverlapToInfinity W (true, true))
  exact standardPairOutputOverlap_infinity_formula_eq W

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
