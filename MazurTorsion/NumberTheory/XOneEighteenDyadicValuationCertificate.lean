/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenGlobalSelmerBridge
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionPrincipalSmallPrimes

/-!
# The two dyadic valuations in the `X₁(18)` two-division field

This file turns the checked ideal factorization

`(2) = (alpha) * (beta)^2`

into the exact two-place valuation certificate used by the global Selmer
enumeration.  An explicit polynomial Bezout identity modulo `2` first
separates the two displayed ideals; primality and exhaustiveness then follow
from the already checked inertia lower bound and absolute norms.
-/

open Polynomial NumberField

namespace MazurTorsion.XOneEighteenDyadicValuationCertificate

noncomputable section

open EllipticCurves.X18SelmerCardinality
open MazurTorsion.XOneEighteenCoefficientDyadicSelmer
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open IsDedekindDomain Ideal RingOfIntegers UniqueFactorizationMonoid

private abbrev K := MazurTorsion.XOneEighteenGlobalSelmerBridge.K

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

private abbrev OM := NumberField.RingOfIntegers M

private abbrev alphaIdeal : Ideal OM := Ideal.span {alphaInteger}

private abbrev betaIdeal : Ideal OM := Ideal.span {betaInteger}

/-! ## A checked Bezout separation of the two ideals -/

private def alphaBezoutPolynomial : Polynomial ℤ :=
  X ^ 7 + X ^ 6 + X ^ 3 + 1

private def betaBezoutPolynomial : Polynomial ℤ :=
  X ^ 8 + X ^ 7 + X ^ 4 + X

private def relationBezoutPolynomial : Polynomial ℤ :=
  X ^ 2 + X + 1

private def dyadicBezoutQuotient : Polynomial ℤ :=
  -X ^ 16 + 3 * X ^ 15 - 8 * X ^ 13 + 4 * X ^ 12 +
    15 * X ^ 11 - 12 * X ^ 10 - 13 * X ^ 9 + 20 * X ^ 8 +
    3 * X ^ 7 - 15 * X ^ 6 + 6 * X ^ 5 + 5 * X ^ 4 -
    4 * X ^ 3 + 4 * X ^ 2 + 3 * X - 1

private theorem dyadicBezoutPolynomial_identity :
    alphaBezoutPolynomial * alphaPolynomialInt +
        betaBezoutPolynomial * betaPolynomialInt +
      relationBezoutPolynomial * normalizedPolynomialInt =
        1 + 2 * dyadicBezoutQuotient := by
  simp only [alphaBezoutPolynomial, betaBezoutPolynomial,
    relationBezoutPolynomial, dyadicBezoutQuotient,
    alphaPolynomialInt, betaPolynomialInt, normalizedPolynomialInt]
  ring

private theorem alphaInteger_eq_aeval :
    alphaInteger = Polynomial.aeval normalizedInteger alphaPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change alpha =
    (IsScalarTower.toAlgHom ℤ OM M)
      (Polynomial.aeval normalizedInteger alphaPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ OM M) normalizedInteger alphaPolynomialInt]
  simpa only [normalizedInteger_coe, IsScalarTower.toAlgHom_apply] using
    alpha_formula

private theorem betaInteger_eq_aeval :
    betaInteger = Polynomial.aeval normalizedInteger betaPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change beta =
    (IsScalarTower.toAlgHom ℤ OM M)
      (Polynomial.aeval normalizedInteger betaPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ OM M) normalizedInteger betaPolynomialInt]
  simpa only [normalizedInteger_coe, IsScalarTower.toAlgHom_apply] using
    beta_formula

private theorem dyadicBezout_evaluated :
    Polynomial.aeval normalizedInteger alphaBezoutPolynomial * alphaInteger +
        Polynomial.aeval normalizedInteger betaBezoutPolynomial * betaInteger =
      1 + 2 * Polynomial.aeval normalizedInteger dyadicBezoutQuotient := by
  rw [alphaInteger_eq_aeval, betaInteger_eq_aeval, ← map_mul, ← map_mul]
  have h := congrArg (Polynomial.aeval normalizedInteger)
    dyadicBezoutPolynomial_identity
  simp only [map_add, map_mul, map_one, map_ofNat,
    normalizedInteger_aeval, mul_zero, add_zero] at h
  simpa only [map_mul] using h

private theorem two_mem_alphaIdeal : (2 : OM) ∈ alphaIdeal := by
  rw [← Ideal.span_singleton_le_iff_mem]
  rw [span_two_eq_span_alpha_mul_span_beta_sq]
  exact Ideal.mul_le_right

private theorem two_mem_betaIdeal : (2 : OM) ∈ betaIdeal := by
  rw [← Ideal.span_singleton_le_iff_mem]
  rw [span_two_eq_span_alpha_mul_span_beta_sq]
  exact Ideal.mul_le_left.trans (Ideal.pow_le_self (by norm_num))

private theorem alphaIdeal_ne_betaIdeal : alphaIdeal ≠ betaIdeal := by
  intro hEq
  have hAlpha : alphaInteger ∈ alphaIdeal :=
    Ideal.subset_span (Set.mem_singleton alphaInteger)
  have hBeta : betaInteger ∈ alphaIdeal := by
    rw [hEq]
    exact Ideal.subset_span (Set.mem_singleton betaInteger)
  have hLeft :
      Polynomial.aeval normalizedInteger alphaBezoutPolynomial * alphaInteger +
          Polynomial.aeval normalizedInteger betaBezoutPolynomial * betaInteger ∈
        alphaIdeal :=
    alphaIdeal.add_mem
      (alphaIdeal.mul_mem_left _ hAlpha) (alphaIdeal.mul_mem_left _ hBeta)
  have hTwoMultiple :
      2 * Polynomial.aeval normalizedInteger dyadicBezoutQuotient ∈
        alphaIdeal := alphaIdeal.mul_mem_right _ two_mem_alphaIdeal
  have hOne : (1 : OM) ∈ alphaIdeal := by
    rw [dyadicBezout_evaluated] at hLeft
    have hsub := alphaIdeal.sub_mem hLeft hTwoMultiple
    convert hsub using 1
    ring
  have hTop : alphaIdeal = ⊤ := (Ideal.eq_top_iff_one alphaIdeal).mpr hOne
  have hNorm := absNorm_span_alpha
  change Ideal.absNorm alphaIdeal = 8 at hNorm
  rw [hTop, Ideal.absNorm_top] at hNorm
  norm_num at hNorm

private theorem eq_of_dvd_of_absNorm_eq
    {I J : Ideal OM} (hdiv : I ∣ J)
    (hI : I.absNorm = 8) (hJ : J.absNorm = 8) : I = J := by
  obtain ⟨C, hC⟩ := hdiv
  have hnorm := congrArg Ideal.absNorm hC
  rw [map_mul, hI, hJ] at hnorm
  have hCnorm : C.absNorm = 1 := by omega
  have hCtop : C = ⊤ := Ideal.absNorm_eq_one_iff.mp hCnorm
  rw [hCtop, mul_top] at hC
  exact hC.symm

private theorem alphaIdeal_ne_bot : alphaIdeal ≠ ⊥ := by
  intro hbot
  have hnorm := absNorm_span_alpha
  change Ideal.absNorm alphaIdeal = 8 at hnorm
  rw [hbot, Ideal.absNorm_bot] at hnorm
  norm_num at hnorm

private theorem betaIdeal_ne_bot : betaIdeal ≠ ⊥ := by
  intro hbot
  have hnorm := absNorm_span_beta
  change Ideal.absNorm betaIdeal = 8 at hnorm
  rw [hbot, Ideal.absNorm_bot] at hnorm
  norm_num at hnorm

private theorem alphaIdeal_not_isUnit : ¬ IsUnit alphaIdeal := by
  intro hunit
  have htop : alphaIdeal = ⊤ := Ideal.isUnit_iff.mp hunit
  have hnorm := absNorm_span_alpha
  change Ideal.absNorm alphaIdeal = 8 at hnorm
  rw [htop, Ideal.absNorm_top] at hnorm
  norm_num at hnorm

private theorem betaIdeal_not_isUnit : ¬ IsUnit betaIdeal := by
  intro hunit
  have htop : betaIdeal = ⊤ := Ideal.isUnit_iff.mp hunit
  have hnorm := absNorm_span_beta
  change Ideal.absNorm betaIdeal = 8 at hnorm
  rw [htop, Ideal.absNorm_top] at hnorm
  norm_num at hnorm

private theorem primeFactor_mem_primesOver_two
    {P I : Ideal OM} (hP : P.IsPrime) (hPdivI : P ∣ I)
    (hIdivTwo : I ∣ Ideal.span {(2 : OM)}) :
    P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) OM := by
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  refine ⟨hP, ?_⟩
  apply (Ideal.liesOver_iff_dvd_map hP.ne_top).mpr
  have hPdivTwo : P ∣ Ideal.span {(2 : OM)} := hPdivI.trans hIdivTwo
  simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hPdivTwo

private theorem alphaIdeal_isPrime : alphaIdeal.IsPrime := by
  obtain ⟨P, hPirr, hPdiv⟩ :=
    WfDvdMonoid.exists_irreducible_factor alphaIdeal_not_isUnit
      alphaIdeal_ne_bot
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hPirr)
  have hAlphaDivTwo : alphaIdeal ∣ Ideal.span {(2 : OM)} :=
    ⟨betaIdeal ^ 2, span_two_eq_span_alpha_mul_span_beta_sq⟩
  have hPover := primeFactor_mem_primesOver_two hPprime hPdiv hAlphaDivTwo
  rcases prime_over_two_eq_span_alpha_or_beta P hPover with hEq | hEq
  · simpa only [hEq] using hPprime
  · have hBetaDivAlpha : betaIdeal ∣ alphaIdeal := by simpa only [hEq] using hPdiv
    have hBetaAlpha : betaIdeal = alphaIdeal :=
      eq_of_dvd_of_absNorm_eq hBetaDivAlpha absNorm_span_beta absNorm_span_alpha
    exact False.elim (alphaIdeal_ne_betaIdeal hBetaAlpha.symm)

private theorem betaIdeal_isPrime : betaIdeal.IsPrime := by
  obtain ⟨P, hPirr, hPdiv⟩ :=
    WfDvdMonoid.exists_irreducible_factor betaIdeal_not_isUnit
      betaIdeal_ne_bot
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hPirr)
  have hBetaDivTwo : betaIdeal ∣ Ideal.span {(2 : OM)} := by
    refine ⟨alphaIdeal * betaIdeal, ?_⟩
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      span_two_eq_span_alpha_mul_span_beta_sq
  have hPover := primeFactor_mem_primesOver_two hPprime hPdiv hBetaDivTwo
  rcases prime_over_two_eq_span_alpha_or_beta P hPover with hEq | hEq
  · have hAlphaDivBeta : alphaIdeal ∣ betaIdeal := by simpa only [hEq] using hPdiv
    have hAlphaBeta : alphaIdeal = betaIdeal :=
      eq_of_dvd_of_absNorm_eq hAlphaDivBeta absNorm_span_alpha absNorm_span_beta
    exact False.elim (alphaIdeal_ne_betaIdeal hAlphaBeta)
  · simpa only [hEq] using hPprime

/-! ## Transport to the relative integral closure -/

private def absoluteAlphaPrime : HeightOneSpectrum OM where
  asIdeal := alphaIdeal
  isPrime := alphaIdeal_isPrime
  ne_bot := alphaIdeal_ne_bot

private def absoluteBetaPrime : HeightOneSpectrum OM where
  asIdeal := betaIdeal
  isPrime := betaIdeal_isPrime
  ne_bot := betaIdeal_ne_bot

private def relativeAbsolutePlaceEquiv :
    HeightOneSpectrum RelativeIntegers ≃ HeightOneSpectrum OM :=
  HeightOneSpectrum.equivOfRingEquiv relativeIntegersEquiv

private def relativeAlphaPrime : HeightOneSpectrum RelativeIntegers :=
  relativeAbsolutePlaceEquiv.symm absoluteAlphaPrime

private def relativeBetaPrime : HeightOneSpectrum RelativeIntegers :=
  relativeAbsolutePlaceEquiv.symm absoluteBetaPrime

private theorem relativeAlphaPrime_ne_relativeBetaPrime :
    relativeAlphaPrime ≠ relativeBetaPrime := by
  intro h
  have habs : absoluteAlphaPrime = absoluteBetaPrime := by
    simpa [relativeAlphaPrime, relativeBetaPrime] using
      congrArg relativeAbsolutePlaceEquiv h
  exact alphaIdeal_ne_betaIdeal (HeightOneSpectrum.ext_iff.mp habs)

private def relativeAlphaInteger : RelativeIntegers :=
  relativeIntegersEquiv.symm alphaInteger

private def relativeBetaInteger : RelativeIntegers :=
  relativeIntegersEquiv.symm betaInteger

@[simp] private theorem relativeIntegersEquiv_relativeAlphaInteger :
    relativeIntegersEquiv relativeAlphaInteger = alphaInteger := by
  simp [relativeAlphaInteger]

@[simp] private theorem relativeIntegersEquiv_relativeBetaInteger :
    relativeIntegersEquiv relativeBetaInteger = betaInteger := by
  simp [relativeBetaInteger]

private theorem relativeAlphaPrime_span :
    relativeAlphaPrime.asIdeal = Ideal.span {relativeAlphaInteger} := by
  have hmap :
      (Ideal.span {relativeAlphaInteger}).map
          relativeIntegersEquiv.toRingHom = alphaIdeal := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {relativeIntegersEquiv relativeAlphaInteger} = alphaIdeal
    rw [relativeIntegersEquiv_relativeAlphaInteger]
  change alphaIdeal.comap relativeIntegersEquiv.toRingHom =
    Ideal.span {relativeAlphaInteger}
  rw [← hmap]
  exact Ideal.comap_map_of_bijective
    relativeIntegersEquiv.toRingHom relativeIntegersEquiv.bijective

private theorem relativeBetaPrime_span :
    relativeBetaPrime.asIdeal = Ideal.span {relativeBetaInteger} := by
  have hmap :
      (Ideal.span {relativeBetaInteger}).map
          relativeIntegersEquiv.toRingHom = betaIdeal := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {relativeIntegersEquiv relativeBetaInteger} = betaIdeal
    rw [relativeIntegersEquiv_relativeBetaInteger]
  change betaIdeal.comap relativeIntegersEquiv.toRingHom =
    Ideal.span {relativeBetaInteger}
  rw [← hmap]
  exact Ideal.comap_map_of_bijective
    relativeIntegersEquiv.toRingHom relativeIntegersEquiv.bijective

private theorem relativeAlphaInteger_coe :
    algebraMap RelativeIntegers M relativeAlphaInteger = alpha := by
  have h := IsIntegralClosure.algebraMap_equiv
    (𝓞 K) RelativeIntegers M (𝓞 M) relativeAlphaInteger
  simpa [relativeIntegersEquiv, relativeAlphaInteger] using h.symm

private theorem relativeBetaInteger_coe :
    algebraMap RelativeIntegers M relativeBetaInteger = beta := by
  have h := IsIntegralClosure.algebraMap_equiv
    (𝓞 K) RelativeIntegers M (𝓞 M) relativeBetaInteger
  simpa [relativeIntegersEquiv, relativeBetaInteger] using h.symm

private theorem relativeIntegersEquiv_algebraMap (x : 𝓞 K) :
    relativeIntegersEquiv
        (algebraMap (𝓞 K) RelativeIntegers x) =
      algebraMap (𝓞 K) (𝓞 M) x := by
  apply RingOfIntegers.coe_injective
  calc
    algebraMap (𝓞 M) M
        (relativeIntegersEquiv
          (algebraMap (𝓞 K) RelativeIntegers x)) =
        algebraMap RelativeIntegers M
          (algebraMap (𝓞 K) RelativeIntegers x) := by
      exact IsIntegralClosure.algebraMap_equiv
        (𝓞 K) RelativeIntegers M (𝓞 M)
          (algebraMap (𝓞 K) RelativeIntegers x)
    _ = algebraMap (𝓞 K) M x :=
      IsScalarTower.algebraMap_apply (𝓞 K) RelativeIntegers M x
    _ = algebraMap (𝓞 M) M
        (algebraMap (𝓞 K) (𝓞 M) x) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M]

private theorem relativeAlphaPrime_below :
    relativeAlphaPrime.below (𝓞 K) = coefficientPrimeTwo := by
  apply HeightOneSpectrum.ext
  symm
  apply coefficientPrimeTwo.isMaximal.eq_of_le
    (relativeAlphaPrime.below (𝓞 K)).isPrime.ne_top
  rw [coefficientPrimeTwo_span, Ideal.span_singleton_le_iff_mem]
  change relativeIntegersEquiv
      (algebraMap (𝓞 K) RelativeIntegers 2) ∈ alphaIdeal
  rw [relativeIntegersEquiv_algebraMap]
  exact two_mem_alphaIdeal

private theorem relativeBetaPrime_below :
    relativeBetaPrime.below (𝓞 K) = coefficientPrimeTwo := by
  apply HeightOneSpectrum.ext
  symm
  apply coefficientPrimeTwo.isMaximal.eq_of_le
    (relativeBetaPrime.below (𝓞 K)).isPrime.ne_top
  rw [coefficientPrimeTwo_span, Ideal.span_singleton_le_iff_mem]
  change relativeIntegersEquiv
      (algebraMap (𝓞 K) RelativeIntegers 2) ∈ betaIdeal
  rw [relativeIntegersEquiv_algebraMap]
  exact two_mem_betaIdeal

private theorem relativeAlphaPrime_mem :
    relativeAlphaPrime ∈ compositumDyadicSupport := by
  rw [compositumDyadicSupport,
    HeightOneSpectrum.mem_primesAbove_iff,
    coefficientDyadicSupport_eq_singleton,
    Set.mem_singleton_iff]
  exact relativeAlphaPrime_below

private theorem relativeBetaPrime_mem :
    relativeBetaPrime ∈ compositumDyadicSupport := by
  rw [compositumDyadicSupport,
    HeightOneSpectrum.mem_primesAbove_iff,
    coefficientDyadicSupport_eq_singleton,
    Set.mem_singleton_iff]
  exact relativeBetaPrime_below

private theorem relative_prime_eq_alpha_or_beta
    (w : HeightOneSpectrum RelativeIntegers)
    (hw : w ∈ compositumDyadicSupport) :
    w = relativeAlphaPrime ∨ w = relativeBetaPrime := by
  have hwBelow : w.below (𝓞 K) = coefficientPrimeTwo := by
    rw [compositumDyadicSupport,
      HeightOneSpectrum.mem_primesAbove_iff,
      coefficientDyadicSupport_eq_singleton,
      Set.mem_singleton_iff] at hw
    exact hw
  let P : HeightOneSpectrum OM := relativeAbsolutePlaceEquiv w
  have htwoRelative :
      algebraMap (𝓞 K) RelativeIntegers (2 : 𝓞 K) ∈ w.asIdeal := by
    change (2 : 𝓞 K) ∈ (w.below (𝓞 K)).asIdeal
    rw [hwBelow, coefficientPrimeTwo_span]
    exact Ideal.subset_span (Set.mem_singleton (2 : 𝓞 K))
  have htwoAbsolute : (2 : OM) ∈ P.asIdeal := by
    change relativeIntegersEquiv.symm (2 : OM) ∈ w.asIdeal
    have hmap := relativeIntegersEquiv_algebraMap (2 : 𝓞 K)
    have hsymm :
        relativeIntegersEquiv.symm (2 : OM) =
          algebraMap (𝓞 K) RelativeIntegers (2 : 𝓞 K) := by
      apply relativeIntegersEquiv.injective
      exact (relativeIntegersEquiv.apply_symm_apply (2 : OM)).trans hmap.symm
    rw [hsymm]
    exact htwoRelative
  have hPover : P.asIdeal ∈
      Ideal.primesOver (Ideal.span {(2 : ℤ)}) OM := by
    letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
      Int.ideal_span_isMaximal_of_prime 2
    refine ⟨P.isPrime, ?_⟩
    apply (Ideal.liesOver_iff_dvd_map P.isPrime.ne_top).mpr
    rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem]
    exact htwoAbsolute
  rcases prime_over_two_eq_span_alpha_or_beta P.asIdeal hPover with hP | hP
  · left
    apply relativeAbsolutePlaceEquiv.injective
    apply HeightOneSpectrum.ext
    simpa only [relativeAlphaPrime, Equiv.apply_symm_apply,
      absoluteAlphaPrime] using hP
  · right
    apply relativeAbsolutePlaceEquiv.injective
    apply HeightOneSpectrum.ext
    simpa only [relativeBetaPrime, Equiv.apply_symm_apply,
      absoluteBetaPrime] using hP

/-! ## The exact two-place indexing -/

private def dyadicPlaceMap : Fin 2 → compositumDyadicSupport
  | 0 => ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩
  | 1 => ⟨relativeBetaPrime, relativeBetaPrime_mem⟩

private theorem dyadicPlaceMap_injective :
    Function.Injective dyadicPlaceMap := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (relativeAlphaPrime_ne_relativeBetaPrime
      (congrArg Subtype.val hij))
  · exact False.elim (relativeAlphaPrime_ne_relativeBetaPrime
      (congrArg Subtype.val hij).symm)
  · rfl

private theorem dyadicPlaceMap_surjective :
    Function.Surjective dyadicPlaceMap := by
  intro w
  rcases relative_prime_eq_alpha_or_beta w w.property with hw | hw
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    exact hw.symm
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    exact hw.symm

private def dyadicPlaceEquiv : Fin 2 ≃ compositumDyadicSupport :=
  Equiv.ofBijective dyadicPlaceMap
    ⟨dyadicPlaceMap_injective, dyadicPlaceMap_surjective⟩

/-! ## The valuation-parity matrix -/

private theorem alpha_ne_zero : alpha ≠ 0 := by
  intro hz
  have h := norm_alpha
  rw [hz, Algebra.norm_zero] at h
  norm_num at h

private theorem beta_ne_zero : beta ≠ 0 := by
  intro hz
  have h := norm_beta
  rw [hz, Algebra.norm_zero] at h
  have htau : Q.tau + 1 ≠ 0 := by
    have ht :=
      MazurTorsion.XOneEighteenRealCubicQuotient.rational_add_tau_ne_zero
        (1 : ℚ)
    change (1 : K) + Q.tau ≠ 0 at ht
    simpa only [add_comm] using ht
  apply htau
  linear_combination (-1 / 2) * h

private theorem relativeAlphaInteger_ne_zero : relativeAlphaInteger ≠ 0 := by
  intro hz
  have h := congrArg (algebraMap RelativeIntegers M) hz
  rw [relativeAlphaInteger_coe, map_zero] at h
  exact alpha_ne_zero h

private theorem relativeBetaInteger_ne_zero : relativeBetaInteger ≠ 0 := by
  intro hz
  have h := congrArg (algebraMap RelativeIntegers M) hz
  rw [relativeBetaInteger_coe, map_zero] at h
  exact beta_ne_zero h

private theorem relativeAlphaInteger_not_mem_betaPrime :
    relativeAlphaInteger ∉ relativeBetaPrime.asIdeal := by
  intro hmem
  have hle : relativeAlphaPrime.asIdeal ≤ relativeBetaPrime.asIdeal := by
    rw [relativeAlphaPrime_span, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hideals :
      relativeAlphaPrime.asIdeal = relativeBetaPrime.asIdeal :=
    relativeAlphaPrime.isMaximal.eq_of_le
      relativeBetaPrime.isPrime.ne_top hle
  exact relativeAlphaPrime_ne_relativeBetaPrime
    (HeightOneSpectrum.ext hideals)

private theorem relativeBetaInteger_not_mem_alphaPrime :
    relativeBetaInteger ∉ relativeAlphaPrime.asIdeal := by
  intro hmem
  have hle : relativeBetaPrime.asIdeal ≤ relativeAlphaPrime.asIdeal := by
    rw [relativeBetaPrime_span, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hideals :
      relativeBetaPrime.asIdeal = relativeAlphaPrime.asIdeal :=
    relativeBetaPrime.isMaximal.eq_of_le
      relativeAlphaPrime.isPrime.ne_top hle
  exact relativeAlphaPrime_ne_relativeBetaPrime
    (HeightOneSpectrum.ext hideals).symm

private theorem alphaSquareclass_mem : alphaSquareclass ∈ DyadicSelmerM := by
  intro w hw
  rw [alphaSquareclass, fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  have hwne : w ≠ relativeAlphaPrime := by
    intro heq
    apply hw
    simpa only [heq] using relativeAlphaPrime_mem
  have hnotmem : relativeAlphaInteger ∉ w.asIdeal := by
    intro hmem
    have hle : relativeAlphaPrime.asIdeal ≤ w.asIdeal := by
      rw [relativeAlphaPrime_span, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have hideals : relativeAlphaPrime.asIdeal = w.asIdeal :=
      relativeAlphaPrime.isMaximal.eq_of_le w.isPrime.ne_top hle
    exact hwne (HeightOneSpectrum.ext hideals.symm)
  have hval : w.valuation M alpha = 1 := by
    rw [← relativeAlphaInteger_coe]
    exact w.valuation_eq_one_iff_notMem.mpr hnotmem
  have hvalUnit :
      w.valuationOfNeZero (Units.mk0 alpha alpha_ne_zero) = 1 := by
    rw [w.valuationOfNeZero_eq_iff]
    simpa only [Units.val_mk0, WithZero.coe_one] using hval
  rw [hvalUnit]
  simp

private theorem betaSquareclass_mem : betaSquareclass ∈ DyadicSelmerM := by
  intro w hw
  rw [betaSquareclass, fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  have hwne : w ≠ relativeBetaPrime := by
    intro heq
    apply hw
    simpa only [heq] using relativeBetaPrime_mem
  have hnotmem : relativeBetaInteger ∉ w.asIdeal := by
    intro hmem
    have hle : relativeBetaPrime.asIdeal ≤ w.asIdeal := by
      rw [relativeBetaPrime_span, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have hideals : relativeBetaPrime.asIdeal = w.asIdeal :=
      relativeBetaPrime.isMaximal.eq_of_le w.isPrime.ne_top hle
    exact hwne (HeightOneSpectrum.ext hideals.symm)
  have hval : w.valuation M beta = 1 := by
    rw [← relativeBetaInteger_coe]
    exact w.valuation_eq_one_iff_notMem.mpr hnotmem
  have hvalUnit :
      w.valuationOfNeZero (Units.mk0 beta beta_ne_zero) = 1 := by
    rw [w.valuationOfNeZero_eq_iff]
    simpa only [Units.val_mk0, WithZero.coe_one] using hval
  rw [hvalUnit]
  simp

private def supportedAlpha : DyadicSelmerM :=
  ⟨alphaSquareclass, alphaSquareclass_mem⟩

private def supportedBeta : DyadicSelmerM :=
  ⟨betaSquareclass, betaSquareclass_mem⟩

private theorem relativeAlphaPrime_valuation_alpha :
    relativeAlphaPrime.valuation M alpha = WithZero.exp (-1 : ℤ) := by
  calc
    relativeAlphaPrime.valuation M alpha =
        relativeAlphaPrime.valuation M
          (algebraMap RelativeIntegers M relativeAlphaInteger) := by
      rw [relativeAlphaInteger_coe]
    _ = relativeAlphaPrime.intValuation relativeAlphaInteger := by
      exact relativeAlphaPrime.valuation_of_algebraMap
        (K := M) relativeAlphaInteger
    _ = WithZero.exp (-1 : ℤ) :=
      relativeAlphaPrime.intValuation_singleton
        relativeAlphaInteger_ne_zero relativeAlphaPrime_span

private theorem relativeBetaPrime_valuation_beta :
    relativeBetaPrime.valuation M beta = WithZero.exp (-1 : ℤ) := by
  calc
    relativeBetaPrime.valuation M beta =
        relativeBetaPrime.valuation M
          (algebraMap RelativeIntegers M relativeBetaInteger) := by
      rw [relativeBetaInteger_coe]
    _ = relativeBetaPrime.intValuation relativeBetaInteger := by
      exact relativeBetaPrime.valuation_of_algebraMap
        (K := M) relativeBetaInteger
    _ = WithZero.exp (-1 : ℤ) :=
      relativeBetaPrime.intValuation_singleton
        relativeBetaInteger_ne_zero relativeBetaPrime_span

private theorem relativeAlphaPrime_valuation_beta :
    relativeAlphaPrime.valuation M beta = 1 := by
  rw [← relativeBetaInteger_coe]
  exact relativeAlphaPrime.valuation_eq_one_iff_notMem.mpr
    relativeBetaInteger_not_mem_alphaPrime

private theorem relativeBetaPrime_valuation_alpha :
    relativeBetaPrime.valuation M alpha = 1 := by
  rw [← relativeAlphaInteger_coe]
  exact relativeBetaPrime.valuation_eq_one_iff_notMem.mpr
    relativeAlphaInteger_not_mem_betaPrime

private theorem relativeAlphaPrime_valuationOfNeZero_alpha :
    relativeAlphaPrime.valuationOfNeZero
        (Units.mk0 alpha alpha_ne_zero) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  rw [relativeAlphaPrime.valuationOfNeZero_eq_iff]
  change relativeAlphaPrime.valuation M alpha = WithZero.exp (-1 : ℤ)
  exact relativeAlphaPrime_valuation_alpha

private theorem relativeBetaPrime_valuationOfNeZero_beta :
    relativeBetaPrime.valuationOfNeZero
        (Units.mk0 beta beta_ne_zero) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  rw [relativeBetaPrime.valuationOfNeZero_eq_iff]
  change relativeBetaPrime.valuation M beta = WithZero.exp (-1 : ℤ)
  exact relativeBetaPrime_valuation_beta

private theorem relativeAlphaPrime_valuationOfNeZero_beta :
    relativeAlphaPrime.valuationOfNeZero
        (Units.mk0 beta beta_ne_zero) = 1 := by
  rw [relativeAlphaPrime.valuationOfNeZero_eq_iff]
  simpa only [Units.val_mk0, WithZero.coe_one] using
    relativeAlphaPrime_valuation_beta

private theorem relativeBetaPrime_valuationOfNeZero_alpha :
    relativeBetaPrime.valuationOfNeZero
        (Units.mk0 alpha alpha_ne_zero) = 1 := by
  rw [relativeBetaPrime.valuationOfNeZero_eq_iff]
  simpa only [Units.val_mk0, WithZero.coe_one] using
    relativeBetaPrime_valuation_alpha

private theorem eq_one_or_parityOne (z : Multiplicative (ZMod 2)) :
    z = 1 ∨ z = parityOne := by
  cases z with
  | ofAdd z =>
      fin_cases z
      · left
        apply Multiplicative.toAdd.injective
        rfl
      · right
        rfl

private theorem supportedAlpha_at_alpha_ne_one :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedAlpha
          ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ ≠ 1 := by
  intro hone
  have hdvd : (2 : ℤ) ∣ Multiplicative.toAdd
      (relativeAlphaPrime.valuationOfNeZero
        (Units.mk0 alpha alpha_ne_zero)) := by
    apply (HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
      relativeAlphaPrime 2 (Units.mk0 alpha alpha_ne_zero)).mp
    exact hone
  rw [relativeAlphaPrime_valuationOfNeZero_alpha] at hdvd
  norm_num at hdvd

private theorem supportedBeta_at_beta_ne_one :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedBeta
          ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ ≠ 1 := by
  intro hone
  have hdvd : (2 : ℤ) ∣ Multiplicative.toAdd
      (relativeBetaPrime.valuationOfNeZero
        (Units.mk0 beta beta_ne_zero)) := by
    apply (HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
      relativeBetaPrime 2 (Units.mk0 beta beta_ne_zero)).mp
    exact hone
  rw [relativeBetaPrime_valuationOfNeZero_beta] at hdvd
  norm_num at hdvd

private theorem supportedAlpha_at_alpha :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedAlpha
          ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ = parityOne := by
  rcases eq_one_or_parityOne
    (supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedAlpha
        ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩) with h | h
  · exact False.elim (supportedAlpha_at_alpha_ne_one h)
  · exact h

private theorem supportedBeta_at_beta :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedBeta
          ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ = parityOne := by
  rcases eq_one_or_parityOne
    (supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedBeta
        ⟨relativeBetaPrime, relativeBetaPrime_mem⟩) with h | h
  · exact False.elim (supportedBeta_at_beta_ne_one h)
  · exact h

private theorem supportedAlpha_at_beta :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedAlpha
          ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ = 1 := by
  change relativeBetaPrime.valuationOfNeZeroMod 2 alphaSquareclass = 1
  rw [alphaSquareclass, fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff,
    relativeBetaPrime_valuationOfNeZero_alpha]
  simp

private theorem supportedBeta_at_alpha :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedBeta
          ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ = 1 := by
  change relativeAlphaPrime.valuationOfNeZeroMod 2 betaSquareclass = 1
  rw [betaSquareclass, fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff,
    relativeAlphaPrime_valuationOfNeZero_beta]
  simp

/-- The exact two-prime valuation certificate for the degree-nine dyadic
supported squareclass group. -/
def dyadicValuationCertificate : DyadicValuationCertificate where
  places := dyadicPlaceEquiv
  alpha_mem := alphaSquareclass_mem
  beta_mem := betaSquareclass_mem
  alpha_at_zero := by
    change supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedAlpha
        ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ = parityOne
    exact supportedAlpha_at_alpha
  alpha_at_one := by
    change supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedAlpha
        ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ = 1
    exact supportedAlpha_at_beta
  beta_at_zero := by
    change supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedBeta
        ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ = 1
    exact supportedBeta_at_alpha
  beta_at_one := by
    change supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedBeta
        ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ = parityOne
    exact supportedBeta_at_beta

end


end MazurTorsion.XOneEighteenDyadicValuationCertificate
