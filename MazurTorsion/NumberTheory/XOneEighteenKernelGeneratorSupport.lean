/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenGlobalSelmerBridge
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionIntegralElements

/-!
# Dyadic support of the four `X₁(18)` norm-kernel generators

The four explicit field elements used in the global two-descent are units
away from `2`.  This file verifies that statement by integral Bézout
certificates in the normalized degree-nine order.  The first two elements
have integral inverses; the last two have an integral complementary factor
whose product with the element is exactly `2`.
-/

open IsDedekindDomain NumberField Polynomial

namespace MazurTorsion.XOneEighteenKernelGeneratorSupport

noncomputable section

open MazurTorsion.XOneEighteenCoefficientDyadicSelmer
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

abbrev K := MazurTorsion.XOneEighteenGlobalSelmerBridge.K

/-! ## Integral Bézout certificates -/

private def h1InversePolynomialInt : Polynomial ℤ :=
  X ^ 8 - 4 * X ^ 7 + 4 * X ^ 6 + 3 * X ^ 5 -
    6 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 + X

private def h1BezoutPolynomialInt : Polynomial ℤ :=
  X ^ 7 - 4 * X ^ 6 + 4 * X ^ 5 + 4 * X ^ 4 -
    10 * X ^ 3 + 3 * X ^ 2 + 3 * X - 1

private theorem h1_bezout_identity :
    h1PolynomialInt * h1InversePolynomialInt +
        h1BezoutPolynomialInt * normalizedPolynomialInt = 1 := by
  simp only [h1PolynomialInt, h1InversePolynomialInt,
    h1BezoutPolynomialInt, normalizedPolynomialInt]
  ring

private def h2InversePolynomialInt : Polynomial ℤ :=
  X ^ 7 - 4 * X ^ 6 + 4 * X ^ 5 + 3 * X ^ 4 -
    6 * X ^ 3 - 2 * X ^ 2 + 4 * X + 1

private def h2BezoutPolynomialInt : Polynomial ℤ :=
  X ^ 4 - 4 * X ^ 3 + 5 * X ^ 2 - X - 2

private theorem h2_bezout_identity :
    h2PolynomialInt * h2InversePolynomialInt +
        h2BezoutPolynomialInt * normalizedPolynomialInt = 1 := by
  simp only [h2PolynomialInt, h2InversePolynomialInt,
    h2BezoutPolynomialInt, normalizedPolynomialInt]
  ring

private def h3InversePolynomialInt : Polynomial ℤ :=
  6 * X ^ 8 - 22 * X ^ 7 + 14 * X ^ 6 + 35 * X ^ 5 -
    43 * X ^ 4 - 27 * X ^ 3 + 38 * X ^ 2 + 11 * X - 8

private def h3BezoutPolynomialInt : Polynomial ℤ :=
  6 * X ^ 7 - 28 * X ^ 6 + 42 * X ^ 5 - X ^ 4 -
    64 * X ^ 3 + 45 * X ^ 2 + 20 * X - 34

private theorem h3_bezout_identity :
    h3PolynomialInt * h3InversePolynomialInt +
        h3BezoutPolynomialInt * normalizedPolynomialInt = 2 := by
  simp only [h3PolynomialInt, h3InversePolynomialInt,
    h3BezoutPolynomialInt, normalizedPolynomialInt]
  ring

private def h4InversePolynomialInt : Polynomial ℤ :=
  7 * X ^ 8 - 25 * X ^ 7 + 14 * X ^ 6 + 42 * X ^ 5 -
    46 * X ^ 4 - 37 * X ^ 3 + 44 * X ^ 2 + 16 * X - 10

private def h4BezoutPolynomialInt : Polynomial ℤ :=
  7 * X ^ 5 - 25 * X ^ 4 + 21 * X ^ 3 + 10 * X ^ 2 -
    14 * X - 12

private theorem h4_bezout_identity :
    h4PolynomialInt * h4InversePolynomialInt +
        h4BezoutPolynomialInt * normalizedPolynomialInt = 2 := by
  simp only [h4PolynomialInt, h4InversePolynomialInt,
    h4BezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-! ## Evaluation in the relative integral closure -/

private def normalizedAbsoluteInteger : 𝓞 M :=
  ⟨normalizedElement, normalizedElement_isIntegral_int⟩

private def normalizedRelativeInteger : RelativeIntegers :=
  relativeIntegersEquiv.symm normalizedAbsoluteInteger

private theorem normalizedRelativeInteger_algebraMap :
    algebraMap RelativeIntegers M normalizedRelativeInteger =
      normalizedElement := by
  rw [← IsIntegralClosure.algebraMap_equiv
    (𝓞 K) RelativeIntegers M (𝓞 M) normalizedRelativeInteger]
  change algebraMap (𝓞 M) M
      (relativeIntegersEquiv normalizedRelativeInteger) = normalizedElement
  rw [normalizedRelativeInteger,
    relativeIntegersEquiv.apply_symm_apply]
  rfl

private theorem normalizedRelativeInteger_aeval :
    Polynomial.aeval normalizedRelativeInteger normalizedPolynomialInt = 0 := by
  apply IsIntegralClosure.algebraMap_injective RelativeIntegers (𝓞 K) M
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger
        normalizedPolynomialInt) = 0
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger normalizedPolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap, map_zero] using
      normalizedPolynomialInt_aeval

private def h1RelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h1PolynomialInt

private def h2RelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h2PolynomialInt

private def h3RelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h3PolynomialInt

private def h4RelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h4PolynomialInt

private def h1InverseRelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h1InversePolynomialInt

private def h2InverseRelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h2InversePolynomialInt

private def h3InverseRelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h3InversePolynomialInt

private def h4InverseRelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h4InversePolynomialInt

private theorem h1RelativeInteger_algebraMap :
    algebraMap RelativeIntegers M h1RelativeInteger = h1 := by
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger h1PolynomialInt) = h1
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger h1PolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap] using h1_formula.symm

private theorem h2RelativeInteger_algebraMap :
    algebraMap RelativeIntegers M h2RelativeInteger = h2 := by
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger h2PolynomialInt) = h2
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger h2PolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap] using h2_formula.symm

private theorem h3RelativeInteger_algebraMap :
    algebraMap RelativeIntegers M h3RelativeInteger = h3 := by
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger h3PolynomialInt) = h3
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger h3PolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap] using h3_formula.symm

private theorem h4RelativeInteger_algebraMap :
    algebraMap RelativeIntegers M h4RelativeInteger = h4 := by
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger h4PolynomialInt) = h4
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger h4PolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap] using h4_formula.symm

private theorem h1RelativeInteger_mul_inverse :
    h1RelativeInteger * h1InverseRelativeInteger = 1 := by
  have h := congrArg (Polynomial.aeval normalizedRelativeInteger)
    h1_bezout_identity
  simpa only [map_add, map_mul, map_one,
    normalizedRelativeInteger_aeval, mul_zero, add_zero,
    h1RelativeInteger, h1InverseRelativeInteger] using h

private theorem h2RelativeInteger_mul_inverse :
    h2RelativeInteger * h2InverseRelativeInteger = 1 := by
  have h := congrArg (Polynomial.aeval normalizedRelativeInteger)
    h2_bezout_identity
  simpa only [map_add, map_mul, map_one,
    normalizedRelativeInteger_aeval, mul_zero, add_zero,
    h2RelativeInteger, h2InverseRelativeInteger] using h

private theorem h3RelativeInteger_mul_inverse :
    h3RelativeInteger * h3InverseRelativeInteger = 2 := by
  have h := congrArg (Polynomial.aeval normalizedRelativeInteger)
    h3_bezout_identity
  simpa only [map_add, map_mul, map_ofNat,
    normalizedRelativeInteger_aeval, mul_zero, add_zero,
    h3RelativeInteger, h3InverseRelativeInteger] using h

private theorem h4RelativeInteger_mul_inverse :
    h4RelativeInteger * h4InverseRelativeInteger = 2 := by
  have h := congrArg (Polynomial.aeval normalizedRelativeInteger)
    h4_bezout_identity
  simpa only [map_add, map_mul, map_ofNat,
    normalizedRelativeInteger_aeval, mul_zero, add_zero,
    h4RelativeInteger, h4InverseRelativeInteger] using h

private theorem h1_mul_inverse :
    h1 * algebraMap RelativeIntegers M h1InverseRelativeInteger = 1 := by
  rw [← h1RelativeInteger_algebraMap]
  simpa only [map_mul, map_one] using
    congrArg (algebraMap RelativeIntegers M)
      h1RelativeInteger_mul_inverse

private theorem h2_mul_inverse :
    h2 * algebraMap RelativeIntegers M h2InverseRelativeInteger = 1 := by
  rw [← h2RelativeInteger_algebraMap]
  simpa only [map_mul, map_one] using
    congrArg (algebraMap RelativeIntegers M)
      h2RelativeInteger_mul_inverse

private theorem h3_mul_inverse :
    h3 * algebraMap RelativeIntegers M h3InverseRelativeInteger = 2 := by
  rw [← h3RelativeInteger_algebraMap]
  simpa only [map_mul, map_ofNat] using
    congrArg (algebraMap RelativeIntegers M)
      h3RelativeInteger_mul_inverse

private theorem h4_mul_inverse :
    h4 * algebraMap RelativeIntegers M h4InverseRelativeInteger = 2 := by
  rw [← h4RelativeInteger_algebraMap]
  simpa only [map_mul, map_ofNat] using
    congrArg (algebraMap RelativeIntegers M)
      h4RelativeInteger_mul_inverse

/-! ## Valuations away from the dyadic support -/

private theorem valuation_two_eq_one
    (w : HeightOneSpectrum RelativeIntegers)
    (hw : w ∉ compositumDyadicSupport) :
    w.valuation M (2 : M) = 1 := by
  have hv : w.below (𝓞 K) ∉ coefficientDyadicSupport := by
    intro hv
    apply hw
    exact (HeightOneSpectrum.mem_primesAbove_iff
      (𝓞 K) RelativeIntegers coefficientDyadicSupport w).mpr hv
  have hbase : (w.below (𝓞 K)).valuation K (2 : K) = 1 := by
    simpa only [coefficientDyadicSupport, Set.mem_setOf_eq,
      not_not] using hv
  have hlies := HeightOneSpectrum.valuation_liesOver M
    (w.below (𝓞 K)) w (2 : K)
  rw [hbase, one_pow] at hlies
  simpa only [map_ofNat] using hlies.symm

private theorem valuation_h1_eq_one
    (w : HeightOneSpectrum RelativeIntegers) :
    w.valuation M h1 = 1 := by
  have hrel :
      w.valuation M (algebraMap RelativeIntegers M h1RelativeInteger) = 1 := by
    apply (w.valuation M).eq_one_of_mul_eq_one
    · exact w.valuation_le_one (K := M) h1RelativeInteger
    · exact w.valuation_le_one (K := M) h1InverseRelativeInteger
    · have hprod := congrArg (algebraMap RelativeIntegers M)
        h1RelativeInteger_mul_inverse
      have hval := congrArg (w.valuation M) hprod
      simpa only [map_mul, map_one] using hval
  rw [h1RelativeInteger_algebraMap] at hrel
  exact hrel

private theorem valuation_h2_eq_one
    (w : HeightOneSpectrum RelativeIntegers) :
    w.valuation M h2 = 1 := by
  have hrel :
      w.valuation M (algebraMap RelativeIntegers M h2RelativeInteger) = 1 := by
    apply (w.valuation M).eq_one_of_mul_eq_one
    · exact w.valuation_le_one (K := M) h2RelativeInteger
    · exact w.valuation_le_one (K := M) h2InverseRelativeInteger
    · have hprod := congrArg (algebraMap RelativeIntegers M)
        h2RelativeInteger_mul_inverse
      have hval := congrArg (w.valuation M) hprod
      simpa only [map_mul, map_one] using hval
  rw [h2RelativeInteger_algebraMap] at hrel
  exact hrel

private theorem valuation_h3_eq_one
    (w : HeightOneSpectrum RelativeIntegers)
    (hw : w ∉ compositumDyadicSupport) :
    w.valuation M h3 = 1 := by
  have hrel :
      w.valuation M (algebraMap RelativeIntegers M h3RelativeInteger) = 1 := by
    apply (w.valuation M).eq_one_of_mul_eq_one
    · exact w.valuation_le_one (K := M) h3RelativeInteger
    · exact w.valuation_le_one (K := M) h3InverseRelativeInteger
    · have hprod := congrArg (algebraMap RelativeIntegers M)
        h3RelativeInteger_mul_inverse
      have hval := congrArg (w.valuation M) hprod
      exact hval.trans (valuation_two_eq_one w hw)
  rw [h3RelativeInteger_algebraMap] at hrel
  exact hrel

private theorem valuation_h4_eq_one
    (w : HeightOneSpectrum RelativeIntegers)
    (hw : w ∉ compositumDyadicSupport) :
    w.valuation M h4 = 1 := by
  have hrel :
      w.valuation M (algebraMap RelativeIntegers M h4RelativeInteger) = 1 := by
    apply (w.valuation M).eq_one_of_mul_eq_one
    · exact w.valuation_le_one (K := M) h4RelativeInteger
    · exact w.valuation_le_one (K := M) h4InverseRelativeInteger
    · have hprod := congrArg (algebraMap RelativeIntegers M)
        h4RelativeInteger_mul_inverse
      have hval := congrArg (w.valuation M) hprod
      exact hval.trans (valuation_two_eq_one w hw)
  rw [h4RelativeInteger_algebraMap] at hrel
  exact hrel

private theorem fieldSquareclass_mem_of_valuation_eq_one
    (x : M) (hx : x ≠ 0)
    (hval : ∀ w : HeightOneSpectrum RelativeIntegers,
      w ∉ compositumDyadicSupport → w.valuation M x = 1) :
    fieldSquareclass x hx ∈ DyadicSelmerM := by
  intro w hw
  rw [fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  have hv : w.valuationOfNeZero (Units.mk0 x hx) = 1 := by
    rw [w.valuationOfNeZero_eq_iff]
    simpa only [Units.val_mk0, WithZero.coe_one] using hval w hw
  rw [hv]
  simp

private theorem support_h1_ne_zero : h1 ≠ 0 := by
  intro hz
  have h := h1_mul_inverse
  rw [hz, zero_mul] at h
  norm_num at h

private theorem support_h2_ne_zero : h2 ≠ 0 := by
  intro hz
  have h := h2_mul_inverse
  rw [hz, zero_mul] at h
  norm_num at h

private theorem support_h3_ne_zero : h3 ≠ 0 := by
  intro hz
  have h := h3_mul_inverse
  rw [hz, zero_mul] at h
  norm_num at h

private theorem support_h4_ne_zero : h4 ≠ 0 := by
  intro hz
  have h := h4_mul_inverse
  rw [hz, zero_mul] at h
  norm_num at h

/-- Every explicit relative-norm-kernel generator is supported only at
the dyadic primes. -/
theorem kernelGenerator_mem_dyadicSelmer (i : Fin 4) :
    kernelGenerator i ∈ DyadicSelmerM := by
  fin_cases i
  · simpa only [kernelGenerator] using
      fieldSquareclass_mem_of_valuation_eq_one h1 support_h1_ne_zero
        (fun w _ ↦ valuation_h1_eq_one w)
  · simpa only [kernelGenerator] using
      fieldSquareclass_mem_of_valuation_eq_one h2 support_h2_ne_zero
        (fun w _ ↦ valuation_h2_eq_one w)
  · simpa only [kernelGenerator] using
      fieldSquareclass_mem_of_valuation_eq_one h3 support_h3_ne_zero
        valuation_h3_eq_one
  · simpa only [kernelGenerator] using
      fieldSquareclass_mem_of_valuation_eq_one h4 support_h4_ne_zero
        valuation_h4_eq_one

/-- The unconditional support certificate consumed by the global Selmer
enumeration. -/
theorem kernelGeneratorSupportCertificate :
    KernelGeneratorSupportCertificate :=
  ⟨kernelGenerator_mem_dyadicSelmer⟩

end

end MazurTorsion.XOneEighteenKernelGeneratorSupport
