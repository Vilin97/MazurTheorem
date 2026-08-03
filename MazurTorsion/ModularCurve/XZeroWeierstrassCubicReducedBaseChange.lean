/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCubicBaseChange
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Reduced field base changes of the projective Weierstrass cubic

This file proves that every field base change of the concrete reduced
projective Weierstrass cubic is reduced.  The proof uses a two-chart cover:

* on `Z ≠ 0`, the checked affine Weierstrass equation is prime;
* on `Y ≠ 0`, the dehomogenized equation is Eisenstein at `Z / Y` and is
  therefore prime.

Both quotient charts are identified with actual open subschemes of the
reduced cubic.  A general quotient pushout argument then proves that their
scalar extensions are the corresponding prime quotient charts over the
extension field.  Pulling the two-chart cover through the field-base-change
square proves reducedness locally and hence globally.

The final declarations discharge the reducedness hypothesis formerly needed
by `fieldBaseChangeIsoMappedCubic` and provide an unconditional
`StandardChartComparison` consumer.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped Polynomial.Bivariate

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

noncomputable def dehomogenizeY :
    MvPolynomial (Fin 3) K →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
      (Polynomial.C : K →+* Polynomial K))
    ![Polynomial.X, 1, Polynomial.C Polynomial.X]

@[simp] theorem dehomogenizeY_X_zero :
    dehomogenizeY (K := K) (MvPolynomial.X 0) = Polynomial.X := by
  simp [dehomogenizeY]

@[simp] theorem dehomogenizeY_X_one :
    dehomogenizeY (K := K) (MvPolynomial.X 1) = 1 := by
  simp [dehomogenizeY]

@[simp] theorem dehomogenizeY_X_two :
    dehomogenizeY (K := K) (MvPolynomial.X 2) =
      Polynomial.C Polynomial.X := by
  simp [dehomogenizeY]

def infinityChartCoeffTwo (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.C W.a₂ * Polynomial.X

def infinityChartCoeffOne (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.C W.a₄ * Polynomial.X ^ 2 -
    Polynomial.C W.a₁ * Polynomial.X

def infinityChartCoeffZero (W : WeierstrassCurve K) : Polynomial K :=
  Polynomial.C W.a₆ * Polynomial.X ^ 3 -
    Polynomial.C W.a₃ * Polynomial.X ^ 2 - Polynomial.X

def infinityChartPolynomial (W : WeierstrassCurve K) :
    Polynomial (Polynomial K) :=
  Polynomial.X ^ 3 +
    (Polynomial.C (infinityChartCoeffTwo W) * Polynomial.X ^ 2 +
      Polynomial.C (infinityChartCoeffOne W) * Polynomial.X +
      Polynomial.C (infinityChartCoeffZero W))

theorem neg_dehomogenizeY_polynomial (W : WeierstrassCurve K) :
    -dehomogenizeY W.toProjective.polynomial = infinityChartPolynomial W := by
  simp [dehomogenizeY, infinityChartPolynomial, infinityChartCoeffTwo,
    infinityChartCoeffOne, infinityChartCoeffZero,
    WeierstrassCurve.Projective.polynomial]
  ring

theorem infinityChartTail_degree_lt (W : WeierstrassCurve K) :
    (Polynomial.C (infinityChartCoeffTwo W) * Polynomial.X ^ 2 +
      Polynomial.C (infinityChartCoeffOne W) * Polynomial.X +
      Polynomial.C (infinityChartCoeffZero W)).degree <
        (↑(3 : ℕ) : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_C,
    if_neg (by omega : n ≠ 2),
    if_neg (by omega : (1 : ℕ) ≠ n), if_neg (by omega : n ≠ 0)]

theorem infinityChartPolynomial_monic (W : WeierstrassCurve K) :
    (infinityChartPolynomial W).Monic := by
  apply Polynomial.monic_X_pow_add
  exact infinityChartTail_degree_lt W

theorem infinityChartPolynomial_natDegree (W : WeierstrassCurve K) :
    (infinityChartPolynomial W).natDegree = 3 := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq (infinityChartPolynomial_monic W).ne_zero]
  change (infinityChartPolynomial W).degree = (3 : WithBot ℕ)
  rw [infinityChartPolynomial]
  calc
    (Polynomial.X ^ 3 +
        (Polynomial.C (infinityChartCoeffTwo W) * Polynomial.X ^ 2 +
          Polynomial.C (infinityChartCoeffOne W) * Polynomial.X +
          Polynomial.C (infinityChartCoeffZero W))).degree =
        (Polynomial.X ^ 3 : Polynomial (Polynomial K)).degree :=
      Polynomial.degree_add_eq_left_of_degree_lt
        (by simpa only [Polynomial.degree_X_pow] using infinityChartTail_degree_lt W)
    _ = (3 : WithBot ℕ) := Polynomial.degree_X_pow 3

theorem infinityChartPolynomial_coeff_zero (W : WeierstrassCurve K) :
    (infinityChartPolynomial W).coeff 0 =
      infinityChartCoeffZero W := by
  simp [infinityChartPolynomial]

theorem infinityChartPolynomial_coeff_one (W : WeierstrassCurve K) :
    (infinityChartPolynomial W).coeff 1 =
      infinityChartCoeffOne W := by
  simp [infinityChartPolynomial]

theorem infinityChartPolynomial_coeff_two (W : WeierstrassCurve K) :
    (infinityChartPolynomial W).coeff 2 =
      infinityChartCoeffTwo W := by
  simp [infinityChartPolynomial]

theorem infinityChartPolynomial_isEisenstein (W : WeierstrassCurve K) :
    (infinityChartPolynomial W).IsEisensteinAt
      (Ideal.span {Polynomial.X}) := by
  apply (infinityChartPolynomial_monic W).isEisensteinAt_of_mem_of_notMem
  · exact (Ideal.isPrime_span_singleton_of_prime
      (Polynomial.irreducible_X (R := K)).prime).ne_top
  · intro n hn
    rw [infinityChartPolynomial_natDegree] at hn
    interval_cases n
    · rw [infinityChartPolynomial_coeff_zero]
      rw [Ideal.mem_span_singleton]
      refine ⟨Polynomial.C W.a₆ * Polynomial.X ^ 2 -
        Polynomial.C W.a₃ * Polynomial.X - 1, ?_⟩
      simp only [infinityChartCoeffZero]
      ring
    · rw [infinityChartPolynomial_coeff_one]
      rw [Ideal.mem_span_singleton]
      refine ⟨Polynomial.C W.a₄ * Polynomial.X - Polynomial.C W.a₁, ?_⟩
      simp only [infinityChartCoeffOne]
      ring
    · rw [infinityChartPolynomial_coeff_two]
      simp [infinityChartCoeffTwo, Ideal.mem_span_singleton]
  · rw [Ideal.span_singleton_pow]
    rw [Ideal.mem_span_singleton]
    intro h
    have hcoeff := (Polynomial.X_pow_dvd_iff.mp h) 1 (by omega)
    rw [infinityChartPolynomial_coeff_zero] at hcoeff
    simp [infinityChartCoeffZero] at hcoeff

theorem infinityChartPolynomial_irreducible (W : WeierstrassCurve K) :
    Irreducible (infinityChartPolynomial W) :=
  (infinityChartPolynomial_isEisenstein W).irreducible
    (Ideal.isPrime_span_singleton_of_prime
      (Polynomial.irreducible_X (R := K)).prime)
    (infinityChartPolynomial_monic W).isPrimitive
    (by rw [infinityChartPolynomial_natDegree]; omega)

instance infinityChartIdeal_isPrime (W : WeierstrassCurve K) :
    (Ideal.span {infinityChartPolynomial W}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime
    (infinityChartPolynomial_irreducible W).prime

/-- The `Y ≠ 0` ambient projective chart, normalized so that the outer
polynomial variable is `X / Y` and the inner variable is `Z / Y`. -/
noncomputable def infinityChartRingEquiv :
    Polynomial (Polynomial K) ≃+*
      HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 1) :=
  (Polynomial.Bivariate.swap (R := K)).toRingEquiv |>.trans
    (standardChartRingEquiv (K := K)) |>.trans
      (standardCoordinateChartRingEquiv (K := K) 1)

@[simp]
theorem coordinateChartRatio_self (i : Fin 3) :
    coordinateChartRatio (K := K) i i = 1 := by
  rw [← isLocalizationElem_degree_one_eq_coordinateChartRatio i i,
    isLocalizationElem_self_degree_one]

@[simp]
theorem infinityChartRingEquiv_outerX :
    infinityChartRingEquiv (K := K) Polynomial.X = coordinateChartRatio 1 0 := by
  change standardToCoordinateChart 1
    (affineToStandardChart (Polynomial.Bivariate.swap Polynomial.X)) = _
  rw [Polynomial.Bivariate.swap_Y]
  simp [affineToStandardChart, Equiv.swap_apply_def]

@[simp]
theorem infinityChartRingEquiv_innerX :
    infinityChartRingEquiv (K := K) (Polynomial.C Polynomial.X) =
      coordinateChartRatio 1 2 := by
  change standardToCoordinateChart 1
    (affineToStandardChart
      (Polynomial.Bivariate.swap (Polynomial.C Polynomial.X))) = _
  rw [Polynomial.Bivariate.swap_X]
  simp [affineToStandardChart]

@[simp]
theorem infinityChartRingEquiv_constant (a : K) :
    infinityChartRingEquiv (K := K) (Polynomial.C (Polynomial.C a)) =
      coordinateChartConstantHom 1 a := by
  change standardToCoordinateChart 1
    (affineToStandardChart
      (Polynomial.Bivariate.swap (Polynomial.C (Polynomial.C a)))) = _
  rw [Polynomial.Bivariate.swap_C_C]
  simp [affineToStandardChart]

noncomputable def infinityLocalizedEquation (W : WeierstrassCurve K) :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X 1) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K)
    (MvPolynomial.isHomogeneous_X K 1) 3 W.toProjective.polynomial
    (polynomial_mem_degree_three W)

theorem infinityLocalizedEquation_explicit (W : WeierstrassCurve K) :
    infinityLocalizedEquation W =
      coordinateChartRatio 1 2 +
        coordinateChartConstantHom 1 W.a₁ * coordinateChartRatio 1 0 *
          coordinateChartRatio 1 2 +
        coordinateChartConstantHom 1 W.a₃ * coordinateChartRatio 1 2 ^ 2 -
        (coordinateChartRatio 1 0 ^ 3 +
          coordinateChartConstantHom 1 W.a₂ * coordinateChartRatio 1 0 ^ 2 *
            coordinateChartRatio 1 2 +
          coordinateChartConstantHom 1 W.a₄ * coordinateChartRatio 1 0 *
            coordinateChartRatio 1 2 ^ 2 +
          coordinateChartConstantHom 1 W.a₆ * coordinateChartRatio 1 2 ^ 3) := by
  rw [show infinityLocalizedEquation W =
      MvPolynomial.eval₂Hom (coordinateChartConstantHom 1)
        (coordinateChartRatio 1) W.toProjective.polynomial from
    coordinateChartAwayMk_eq_eval₂Hom 1 W.toProjective.polynomial
      (polynomial_mem_degree_three W)]
  simp [WeierstrassCurve.Projective.polynomial]

theorem infinityChartRingEquiv_polynomial (W : WeierstrassCurve K) :
    infinityChartRingEquiv (infinityChartPolynomial W) =
      -infinityLocalizedEquation W := by
  rw [infinityLocalizedEquation_explicit]
  simp [infinityChartPolynomial, infinityChartCoeffTwo,
    infinityChartCoeffOne, infinityChartCoeffZero]
  ring

/-- The principal equation ideal on the `Y ≠ 0` chart. -/
def infinityChartIdeal (W : WeierstrassCurve K) :
    Ideal (HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X 1)) :=
  Ideal.span {infinityLocalizedEquation W}

theorem infinityChartIdeal_eq_map (W : WeierstrassCurve K) :
    infinityChartIdeal W =
      Ideal.map (infinityChartRingEquiv (K := K))
        (Ideal.span {infinityChartPolynomial W}) := by
  rw [infinityChartIdeal, Ideal.map_span, Set.image_singleton,
    infinityChartRingEquiv_polynomial, Ideal.span_singleton_neg]

instance infinityLocalizedIdeal_isPrime (W : WeierstrassCurve K) :
    (infinityChartIdeal W).IsPrime := by
  rw [infinityChartIdeal_eq_map]
  infer_instance

/-- The two coordinate charts used below: `false` is `Y ≠ 0` and `true`
is `Z ≠ 0`. -/
def coveringCoordinate : Bool → Fin 3
  | false => 1
  | true => 2

noncomputable def coveringChartEquation (W : WeierstrassCurve K) :
    (b : Bool) → HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X (coveringCoordinate b))
  | false => infinityLocalizedEquation W
  | true => standardChartEquation W

def coveringChartIdeal (W : WeierstrassCurve K) (b : Bool) :
    Ideal (HomogeneousLocalization.Away (homogeneousPieces K)
      (MvPolynomial.X (coveringCoordinate b))) :=
  Ideal.span {coveringChartEquation W b}

instance coveringChartIdeal_isPrime (W : WeierstrassCurve K) (b : Bool) :
    (coveringChartIdeal W b).IsPrime := by
  cases b
  · change (infinityChartIdeal W).IsPrime
    infer_instance
  · change (standardChartIdeal W).IsPrime
    infer_instance

theorem coordinateChartBaseChangeMap_localizedEquation
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (i : Fin 3) :
    coordinateChartBaseChangeMap (K := K) (L := L) i
        (HomogeneousLocalization.Away.mk (homogeneousPieces K)
          (MvPolynomial.isHomogeneous_X K i) 3 W.toProjective.polynomial
          (polynomial_mem_degree_three W)) =
      HomogeneousLocalization.Away.mk (homogeneousPieces L)
        (MvPolynomial.isHomogeneous_X L i) 3
        (W.map (algebraMap K L)).toProjective.polynomial
        (polynomial_mem_degree_three (W.map (algebraMap K L))) := by
  rw [coordinateChartAwayMk_eq_eval₂Hom i W.toProjective.polynomial
      (polynomial_mem_degree_three W),
    coordinateChartAwayMk_eq_eval₂Hom i
      (W.map (algebraMap K L)).toProjective.polynomial
      (polynomial_mem_degree_three (W.map (algebraMap K L)))]
  simp [WeierstrassCurve.Projective.polynomial]

@[simp]
theorem coveringChartEquation_baseChange
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (b : Bool) :
    coordinateChartBaseChangeMap (K := K) (L := L) (coveringCoordinate b)
        (coveringChartEquation W b) =
      coveringChartEquation (W.map (algebraMap K L)) b := by
  cases b
  · exact coordinateChartBaseChangeMap_localizedEquation W 1
  · exact coordinateChartBaseChangeMap_localizedEquation W 2

theorem coveringChartIdeal_baseChange
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (b : Bool) :
    Ideal.map
        (coordinateChartBaseChangeMap (K := K) (L := L) (coveringCoordinate b))
        (coveringChartIdeal W b) =
      coveringChartIdeal (W.map (algebraMap K L)) b := by
  rw [coveringChartIdeal, coveringChartIdeal, Ideal.map_span]
  simp

abbrev coveringChartRing (K : Type u) [Field K] (b : Bool) :=
  HomogeneousLocalization.Away (homogeneousPieces K)
    (MvPolynomial.X (coveringCoordinate b))

abbrev coveringChartCoordinateRing (W : WeierstrassCurve K) (b : Bool) :=
  coveringChartRing K b ⧸ coveringChartIdeal W b

instance coveringChartCoordinateRing_isDomain (W : WeierstrassCurve K) (b : Bool) :
    IsDomain (coveringChartCoordinateRing W b) := by
  infer_instance

abbrev coveringChartScheme (W : WeierstrassCurve K) (b : Bool) : Scheme.{u} :=
  Spec (.of (coveringChartCoordinateRing W b))

noncomputable def coveringChartQuotientInclusion (W : WeierstrassCurve K) (b : Bool) :
    coveringChartScheme W b ⟶ Spec (.of (coveringChartRing K b)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (coveringChartIdeal W b)))

noncomputable def coveringChartAway (K : Type u) [Field K] (b : Bool) :
    Spec (.of (coveringChartRing K b)) ⟶ projectivePlane K :=
  Proj.awayι (homogeneousPieces K)
    (MvPolynomial.X (coveringCoordinate b))
    (MvPolynomial.isHomogeneous_X K (coveringCoordinate b)) (by omega)

instance coveringChartQuotientInclusion_isClosedImmersion
    (W : WeierstrassCurve K) (b : Bool) :
    IsClosedImmersion (coveringChartQuotientInclusion W b) := by
  dsimp only [coveringChartQuotientInclusion]
  exact IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (coveringChartRing K b)) (coveringChartIdeal W b)

instance coveringChartAway_isOpenImmersion
    (K : Type u) [Field K] (b : Bool) : IsOpenImmersion (coveringChartAway K b) := by
  dsimp only [coveringChartAway]
  exact Proj.instIsOpenImmersionAwayι _ _ _ _

instance coveringChartAway_quasiCompact
    (K : Type u) [Field K] (b : Bool) : QuasiCompact (coveringChartAway K b) := by
  letI : QuasiSeparatedSpace (projectivePlane K) :=
    quasiSeparatedSpace_of_quasiSeparated (projectivePlaneStructureMap K)
  infer_instance

noncomputable def coveringChartAmbientMap (W : WeierstrassCurve K) (b : Bool) :
    coveringChartScheme W b ⟶ projectivePlane K :=
  coveringChartQuotientInclusion W b ≫ coveringChartAway K b

instance coveringChartAmbientMap_quasiCompact (W : WeierstrassCurve K) (b : Bool) :
    QuasiCompact (coveringChartAmbientMap W b) := by
  dsimp only [coveringChartAmbientMap]
  infer_instance

theorem coveringChartAmbientMap_mem_carrier
    (W : WeierstrassCurve K) (b : Bool) (x : coveringChartScheme W b) :
    coveringChartAmbientMap W b x ∈ carrier W := by
  apply (mem_zeroLocus_iff W (coveringChartAmbientMap W b x)).mpr
  change W.toProjective.polynomial ∈
    ((coveringChartAway K b)
      (coveringChartQuotientInclusion W b x)).asHomogeneousIdeal
  apply (polynomial_mem_awayι_iff_awayMk_mem
    (K := K) (coveringCoordinate b)
    (coveringChartQuotientInclusion W b x)
    W.toProjective.polynomial (polynomial_mem_degree_three W)).mpr
  rw [show
    (HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (MvPolynomial.isHomogeneous_X K (coveringCoordinate b)) 3
        W.toProjective.polynomial (polynomial_mem_degree_three W) :
      coveringChartRing K b) = coveringChartEquation W b by
        cases b <;> rfl]
  change Ideal.Quotient.mk (coveringChartIdeal W b)
    (coveringChartEquation W b) ∈ x.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr]
  · exact x.asIdeal.zero_mem
  · exact Ideal.subset_span (Set.mem_singleton _)

noncomputable def coveringChartMap (W : WeierstrassCurve K) (b : Bool) :
    coveringChartScheme W b ⟶ scheme W :=
  MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.lift
    (coveringChartAmbientMap W b) (closedCarrier W) (by
      rintro _ ⟨x, rfl⟩
      exact coveringChartAmbientMap_mem_carrier W b x)

@[reassoc (attr := simp)]
theorem coveringChartMap_comp_inclusion (W : WeierstrassCurve K) (b : Bool) :
    coveringChartMap W b ≫ inclusion W = coveringChartAmbientMap W b :=
  MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.lift_comp_subschemeι
    (coveringChartAmbientMap W b) (closedCarrier W) _

theorem range_coveringChartQuotientInclusion
    (W : WeierstrassCurve K) (b : Bool) :
    Set.range (coveringChartQuotientInclusion W b) =
      {q | coveringChartEquation W b ∈ q.asIdeal} := by
  ext q
  change q ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (coveringChartIdeal W b))) ↔
    coveringChartEquation W b ∈ q.asIdeal
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
  rw [Ideal.mk_ker]
  change coveringChartIdeal W b ≤ q.asIdeal ↔ _
  rw [coveringChartIdeal, Ideal.span_singleton_le_iff_mem]

theorem range_coveringChartQuotientInclusion_eq_preimage_carrier
    (W : WeierstrassCurve K) (b : Bool) :
    Set.range (coveringChartQuotientInclusion W b) =
      coveringChartAway K b ⁻¹' carrier W := by
  ext q
  rw [range_coveringChartQuotientInclusion]
  let q' : PrimeSpectrum (coveringChartRing K b) := q
  change coveringChartEquation W b ∈ q'.asIdeal ↔
    Proj.awayι (homogeneousPieces K)
      (MvPolynomial.X (coveringCoordinate b))
      (MvPolynomial.isHomogeneous_X K (coveringCoordinate b)) (by omega) q' ∈
      ProjectiveSpectrum.zeroLocus (homogeneousPieces K)
        {W.toProjective.polynomial}
  have heq :
      (HomogeneousLocalization.Away.mk (homogeneousPieces K)
          (MvPolynomial.isHomogeneous_X K (coveringCoordinate b)) 3
          W.toProjective.polynomial (polynomial_mem_degree_three W) :
        coveringChartRing K b) = coveringChartEquation W b := by
    cases b <;> rfl
  constructor
  · intro h
    apply (mem_zeroLocus_iff W _).mpr
    apply (polynomial_mem_awayι_iff_awayMk_mem
      (K := K) (coveringCoordinate b) q' W.toProjective.polynomial
      (polynomial_mem_degree_three W)).mpr
    rwa [heq]
  · intro h
    have h' := (polynomial_mem_awayι_iff_awayMk_mem
      (K := K) (coveringCoordinate b) q' W.toProjective.polynomial
      (polynomial_mem_degree_three W)).mp
        ((mem_zeroLocus_iff W _).mp h)
    rwa [heq] at h'

theorem ker_inclusion (W : WeierstrassCurve K) :
    (inclusion W).ker = idealSheaf W := by
  simpa only [inclusion] using (idealSheaf W).ker_subschemeι

theorem coveringChart_kernel_eq_comap (W : WeierstrassCurve K) (b : Bool) :
    (inclusion W).ker.comap (coveringChartAway K b) =
      (coveringChartQuotientInclusion W b).ker := by
  let q := coveringChartQuotientInclusion W b
  let a := coveringChartAway K b
  have hsupport : ((inclusion W).ker.comap a).support = q.ker.support := by
    calc
      ((inclusion W).ker.comap a).support =
          (inclusion W).ker.support.preimage a.continuous :=
        Scheme.IdealSheafData.support_comap _ _
      _ = (closedCarrier W).preimage a.continuous := by
        apply SetLike.coe_injective
        simp only [ker_inclusion, idealSheaf,
          TopologicalSpace.Closeds.coe_preimage,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
      _ = q.ker.support := by
        apply SetLike.coe_injective
        simp only [TopologicalSpace.Closeds.coe_preimage]
        rw [Scheme.Hom.support_ker,
          q.isClosedEmbedding.isClosed_range.closure_eq,
          range_coveringChartQuotientInclusion_eq_preimage_carrier]
        ext x
        rfl
  have hcomapRadical :
      ((inclusion W).ker.comap a).radical = (inclusion W).ker.comap a := by
    let i := pullback.fst a (inclusion W)
    letI : IsReduced (pullback a (inclusion W)) :=
      isReduced_of_isOpenImmersion (pullback.snd a (inclusion W))
    have hi :=
      MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.hom_ker_radical_of_isReduced i
    simpa only [i, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion] using hi
  have hqRadical : q.ker.radical = q.ker :=
    MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme.hom_ker_radical_of_isReduced q
  calc
    (inclusion W).ker.comap a = ((inclusion W).ker.comap a).radical :=
      hcomapRadical.symm
    _ = Scheme.IdealSheafData.vanishingIdeal
        ((inclusion W).ker.comap a).support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal q.ker.support := by rw [hsupport]
    _ = q.ker.radical := Scheme.IdealSheafData.vanishingIdeal_support
    _ = q.ker := hqRadical

theorem coveringChart_isPullback (W : WeierstrassCurve K) (b : Bool) :
    IsPullback (coveringChartQuotientInclusion W b) (coveringChartMap W b)
      (coveringChartAway K b) (inclusion W) := by
  apply isPullback_of_isClosedImmersion
  · exact (coveringChartMap_comp_inclusion W b).symm
  · exact coveringChart_kernel_eq_comap W b

instance coveringChartMap_isOpenImmersion (W : WeierstrassCurve K) (b : Bool) :
    IsOpenImmersion (coveringChartMap W b) :=
  MorphismProperty.of_isPullback (coveringChart_isPullback W b) inferInstance

theorem coveringChartMap_opensRange (W : WeierstrassCurve K) (b : Bool) :
    (coveringChartMap W b).opensRange =
      inclusion W ⁻¹ᵁ (coveringChartAway K b).opensRange := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (coveringChart_isPullback W b) (⊤ : (Spec (.of (coveringChartRing K b))).Opens)
  simpa using h

theorem mem_basicOpen_one_or_basicOpen_two_of_mem_carrier
    (W : WeierstrassCurve K) (p : projectivePlane K) (hp : p ∈ carrier W) :
    p ∈ Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X 1) ∨
      p ∈ Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X 2) := by
  by_contra hcover
  rw [not_or] at hcover
  have hY : MvPolynomial.X (1 : Fin 3) ∈ p.asHomogeneousIdeal := by
    by_contra hY
    exact hcover.1 ((ProjectiveSpectrum.mem_basicOpen
      (homogeneousPieces K) (MvPolynomial.X 1) p).mpr hY)
  have hZ : MvPolynomial.X (2 : Fin 3) ∈ p.asHomogeneousIdeal := by
    by_contra hZ
    exact hcover.2 ((ProjectiveSpectrum.mem_basicOpen
      (homogeneousPieces K) (MvPolynomial.X 2) p).mpr hZ)
  let I := p.asHomogeneousIdeal.toIdeal
  letI : I.IsPrime := p.isPrime
  let π : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K ⧸ I :=
    Ideal.Quotient.mk I
  have hπY : π (MvPolynomial.X 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hY
  have hπZ : π (MvPolynomial.X 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hZ
  have hπpoly : π W.toProjective.polynomial = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_zeroLocus_iff W p).mp hp)
  have hπXpow : π (MvPolynomial.X 0) ^ 3 = 0 := by
    simpa [π, WeierstrassCurve.Projective.polynomial, hπY, hπZ] using hπpoly
  have hπX : π (MvPolynomial.X 0) = 0 := eq_zero_of_pow_eq_zero hπXpow
  have hX : MvPolynomial.X (0 : Fin 3) ∈ p.asHomogeneousIdeal :=
    Ideal.Quotient.eq_zero_iff_mem.mp hπX
  obtain ⟨i, hi⟩ := exists_coordinate_not_mem p
  fin_cases i <;> contradiction

noncomputable def coveringChartsOpenCover (W : WeierstrassCurve K) :
    (scheme W).OpenCover where
  I₀ := Bool
  X b := coveringChartScheme W b
  f b := coveringChartMap W b
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ ↦ inferInstance⟩
    intro x
    have hx : inclusion W x ∈ carrier W := by
      rw [← range_inclusion W]
      exact ⟨x, rfl⟩
    by_cases hxY : inclusion W x ∈
        Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X 1)
    · refine ⟨false, ?_⟩
      rw [← Scheme.Hom.coe_opensRange,
        coveringChartMap_opensRange]
      have hAway : (coveringChartAway K false).opensRange =
          Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X 1) := by
        exact Proj.opensRange_awayι (homogeneousPieces K)
          (MvPolynomial.X 1) (MvPolynomial.isHomogeneous_X K 1) (by omega)
      rw [hAway]
      exact hxY
    · have hxZ : inclusion W x ∈
          Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X 2) :=
        (mem_basicOpen_one_or_basicOpen_two_of_mem_carrier W (inclusion W x) hx).resolve_left hxY
      refine ⟨true, ?_⟩
      rw [← Scheme.Hom.coe_opensRange,
        coveringChartMap_opensRange]
      have hAway : (coveringChartAway K true).opensRange =
          Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X 2) := by
        exact Proj.opensRange_awayι (homogeneousPieces K)
          (MvPolynomial.X 2) (MvPolynomial.isHomogeneous_X K 2) (by omega)
      rw [hAway]
      exact hxZ

private theorem quotient_map_isPushout
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) :
    IsPushout
      (CommRingCat.ofHom f)
      (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.map f I)))
      (CommRingCat.ofHom
        (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)) := by
  apply IsPushout.mk'
  · apply CommRingCat.hom_ext
    ext x
    simp
  · intro T φ φ' hφ _
    apply CommRingCat.hom_ext
    ext z
    exact congrArg
      (fun ψ : CommRingCat.of B ⟶ T ↦ ψ.hom z) hφ
  · intro T a b hab
    have hkill : Ideal.map f I ≤ RingHom.ker a.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change a.hom (f x) = 0
      have hcompat := congrArg
        (fun ψ : CommRingCat.of A ⟶ T ↦ ψ.hom x) hab
      change a.hom (f x) = b.hom (Ideal.Quotient.mk I x) at hcompat
      rw [hcompat, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    let l : B ⧸ (Ideal.map f I) →+* T :=
      Ideal.Quotient.lift (Ideal.map f I) a.hom hkill
    refine ⟨CommRingCat.ofHom l, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      ext x
      rfl
    · apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      ext x
      change a.hom (f x) = b.hom (Ideal.Quotient.mk I x)
      have hcompat := congrArg
        (fun ψ : CommRingCat.of A ⟶ T ↦ ψ.hom x) hab
      change a.hom (f x) = b.hom (Ideal.Quotient.mk I x) at hcompat
      exact hcompat

private theorem quotient_map_isPushout_of_map_eq
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hJ : Ideal.map f I = J) (hIJ : I ≤ Ideal.comap f J) :
    IsPushout
      (CommRingCat.ofHom f)
      (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.quotientMap J f hIJ)) := by
  subst J
  simpa only using quotient_map_isPushout f I

/-- The scalar-extension map between the two quotient coordinate rings. -/
noncomputable def coveringChartQuotientBaseChangeMap
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (b : Bool) :
    coveringChartCoordinateRing W b →+*
      coveringChartCoordinateRing (W.map (algebraMap K L)) b :=
  Ideal.quotientMap (coveringChartIdeal (W.map (algebraMap K L)) b)
    (coordinateChartBaseChangeMap (K := K) (L := L) (coveringCoordinate b)) <| by
      rw [← coveringChartIdeal_baseChange (K := K) (L := L) W b]
      exact Ideal.le_comap_map

@[simp]
theorem coveringChartQuotientBaseChangeMap_mk
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (b : Bool) (x : coveringChartRing K b) :
    coveringChartQuotientBaseChangeMap (L := L) W b
        (Ideal.Quotient.mk (coveringChartIdeal W b) x) =
      Ideal.Quotient.mk (coveringChartIdeal (W.map (algebraMap K L)) b)
        (coordinateChartBaseChangeMap (K := K) (L := L)
          (coveringCoordinate b) x) := by
  simp [coveringChartQuotientBaseChangeMap]

/-- A quotient coordinate ring receives its field structure through chart constants. -/
noncomputable def coveringChartStructureRingHom
    (W : WeierstrassCurve K) (b : Bool) :
    K →+* coveringChartCoordinateRing W b :=
  (Ideal.Quotient.mk (coveringChartIdeal W b)).comp
    (coordinateChartConstantHom (K := K) (coveringCoordinate b))

/-- Quotienting the chart equation commutes with the affine chart pushout. -/
theorem coveringChartQuotient_isPushout
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (b : Bool) :
    IsPushout
      (CommRingCat.ofHom
        (coordinateChartBaseChangeMap (K := K) (L := L) (coveringCoordinate b)))
      (CommRingCat.ofHom (Ideal.Quotient.mk (coveringChartIdeal W b)))
      (CommRingCat.ofHom
        (Ideal.Quotient.mk (coveringChartIdeal (W.map (algebraMap K L)) b)))
      (CommRingCat.ofHom (coveringChartQuotientBaseChangeMap (L := L) W b)) := by
  unfold coveringChartQuotientBaseChangeMap
  apply quotient_map_isPushout_of_map_eq
  exact coveringChartIdeal_baseChange (K := K) (L := L) W b

/-- The field extension square of the quotient coordinate rings is a pushout. -/
theorem coveringChart_isPushout
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (b : Bool) :
    IsPushout
      (CommRingCat.ofHom (algebraMap K L))
      (CommRingCat.ofHom (coveringChartStructureRingHom W b))
      (CommRingCat.ofHom
        (coveringChartStructureRingHom (W.map (algebraMap K L)) b))
      (CommRingCat.ofHom (coveringChartQuotientBaseChangeMap (L := L) W b)) := by
  let h := (coordinateChart_isPushout (K := K) (L := L)
    (coveringCoordinate b)).paste_vert
      (coveringChartQuotient_isPushout (K := K) (L := L) W b)
  simpa only [coveringChartStructureRingHom, CommRingCat.ofHom_comp] using h

/-- A quotient chart's structural morphism is the restriction of the cubic's
structural morphism. -/
@[reassoc]
theorem coveringChartMap_comp_structureMap
    (W : WeierstrassCurve K) (b : Bool) :
    coveringChartMap W b ≫ structureMap W =
      Spec.map (CommRingCat.ofHom (coveringChartStructureRingHom W b)) := by
  have hAway : coveringChartAway K b ≫ projectivePlaneStructureMap K =
      Spec.map (CommRingCat.ofHom
        (coordinateChartConstantHom (K := K) (coveringCoordinate b))) := by
    exact awayι_comp_projectivePlaneStructureMap
      (K := K) (coveringCoordinate b)
  rw [structureMap, ← Category.assoc, coveringChartMap_comp_inclusion,
    coveringChartAmbientMap, Category.assoc, hAway,
    coveringChartQuotientInclusion, ← Spec.map_comp]
  rfl

/-- Contravariantly, each quotient coordinate chart after field extension is
the actual pullback of its structural morphism. -/
theorem coveringChart_isPullback_baseChange
    {L : Type u} [Field L] [Algebra K L]
    (W : WeierstrassCurve K) (b : Bool) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (coveringChartQuotientBaseChangeMap (L := L) W b)))
      (coveringChartMap (W.map (algebraMap K L)) b ≫
        structureMap (W.map (algebraMap K L)))
      (coveringChartMap W b ≫ structureMap W)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  let h := (coveringChart_isPushout (K := K) (L := L) W b).op.map Scheme.Spec
  change IsPullback
      (Spec.map (CommRingCat.ofHom
        (coveringChartQuotientBaseChangeMap (L := L) W b)))
      (Spec.map (CommRingCat.ofHom
        (coveringChartStructureRingHom (W.map (algebraMap K L)) b)))
      (Spec.map (CommRingCat.ofHom (coveringChartStructureRingHom W b)))
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) at h
  simpa only [coveringChartMap_comp_structureMap] using h

/-- Every field base change of the reduced projective Weierstrass cubic is reduced.

The proof is concrete: pull back the two-chart open cover, identify each
component with the corresponding prime quotient chart over the extension
field, and descend reducedness across that open cover. -/
theorem fieldBaseChange_isReduced
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    IsReduced (fieldBaseChange W L) := by
  let 𝒰 := coveringChartsOpenCover W
  let 𝒱 := 𝒰.pullback₁ (fieldBaseChangeProjection W L)
  letI (b : 𝒱.I₀) : IsReduced (𝒱.X b) := by
    let hlocal := coveringChart_isPullback_baseChange
      (K := K) (L := L) W b
    letI : IsDomain
        (coveringChartCoordinateRing (W.map (algebraMap K L)) b) :=
      coveringChartCoordinateRing_isDomain (W.map (algebraMap K L)) b
    letI : _root_.IsReduced
        (coveringChartCoordinateRing (W.map (algebraMap K L)) b) := by
      infer_instance
    letI : IsReduced
        (coveringChartScheme (W.map (algebraMap K L)) b) := by
      infer_instance
    letI : IsReduced
        (pullback (coveringChartMap W b ≫ structureMap W)
          (Spec.map (CommRingCat.ofHom (algebraMap K L)))) :=
      isReduced_of_isOpenImmersion hlocal.isoPullback.inv
    let e : 𝒱.X b ≅
        pullback (coveringChartMap W b ≫ structureMap W)
          (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
      (pullbackSymmetry (fieldBaseChangeProjection W L)
        (coveringChartMap W b)).trans
          (pullbackRightPullbackFstIso (structureMap W)
            (Spec.map (CommRingCat.ofHom (algebraMap K L)))
            (coveringChartMap W b))
    exact isReduced_of_isOpenImmersion e.hom
  exact IsReduced.of_openCover (fieldBaseChange W L) 𝒱

instance fieldBaseChange_isReduced_instance
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    IsReduced (fieldBaseChange W L) :=
  fieldBaseChange_isReduced W L

/-- The cubic structure morphism is geometrically reduced.  This is the
scheme-level downstream form of the field-by-field theorem above. -/
instance structureMap_geometricallyReduced (W : WeierstrassCurve K) :
    GeometricallyReduced (structureMap W) := by
  constructor
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro L _ _
  exact fieldBaseChange_isReduced W L

/-- The canonical reduction map is now unconditionally an isomorphism. -/
instance mappedCubicReductionMap_isIso_instance
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L] :
    IsIso (mappedCubicReductionMap W L) :=
  (mappedCubicReductionMap_isIso_iff_isReduced W L).mpr
    (fieldBaseChange_isReduced W L)

/-- The standard-chart comparison no longer needs a reducedness hypothesis;
only the independent chart identification and density remain to be supplied. -/
noncomputable def standardChartComparisonOfFieldBaseChange
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    (chartIso : standardAffineChartScheme (W.map (algebraMap K L)) ≅
      canonicalStandardOpen W L)
    (canonicalMap_denseRange : DenseRange (canonicalStandardOpenMap W L)) :
    StandardChartComparison W L :=
  standardChartComparisonOfReducedFieldBaseChange W L chartIso
    canonicalMap_denseRange

/-- The unconditional standard-chart consumer carries the required ambient
compatibility equation. -/
theorem standardChartComparisonOfFieldBaseChange_isAmbientCompatible
    (W : WeierstrassCurve K) (L : Type u) [Field L] [Algebra K L]
    (chartIso : standardAffineChartScheme (W.map (algebraMap K L)) ≅
      canonicalStandardOpen W L)
    (canonicalMap_denseRange : DenseRange (canonicalStandardOpenMap W L)) :
    (standardChartComparisonOfFieldBaseChange W L chartIso
      canonicalMap_denseRange).IsAmbientCompatible W L :=
  fieldBaseChangeIsoMappedCubic_isAmbientCompatible W L

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
