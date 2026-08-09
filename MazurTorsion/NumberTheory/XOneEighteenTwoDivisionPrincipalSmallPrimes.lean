/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionMinkowski
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes

/-!
# Principal ideals above the small ramified primes in the `X₁(18)` compositum

The integral quotients constructed in
`XOneEighteenTwoDivisionIntegralElements` are units.  This is verified by
explicit integral Bezout inverses modulo the normalized degree-nine
polynomial.  Consequently the advertised element factorizations give exact
ideal identities

`(2) = (alpha) * (beta)^2` and `(3) = (rho)^3`.

No maximal-order assertion about the normalized power order is used.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements

/-! ## Explicit inverses for the two integral quotients -/

/-- An inverse of `beta^2 * alpha / 2` in the normalized integral order. -/
def dyadicQuotientInversePolynomialInt : Polynomial ℤ :=
  4 * X ^ 8 - 14 * X ^ 7 + 7 * X ^ 6 + 25 * X ^ 5 -
    26 * X ^ 4 - 22 * X ^ 3 + 24 * X ^ 2 + 10 * X - 5

private def dyadicQuotientBezoutPolynomialInt : Polynomial ℤ :=
  -8 * X ^ 7 + 28 * X ^ 6 - 22 * X ^ 5 - 26 * X ^ 4 +
    44 * X ^ 3 + 7 * X ^ 2 - 15 * X + 6

private theorem dyadicQuotient_bezout_identity :
    dyadicQuotientPolynomialInt * dyadicQuotientInversePolynomialInt =
      1 + dyadicQuotientBezoutPolynomialInt * normalizedPolynomialInt := by
  simp only [dyadicQuotientPolynomialInt,
    dyadicQuotientInversePolynomialInt,
    dyadicQuotientBezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-- The explicit inverse of the dyadic quotient in the full ring of
integers. -/
def dyadicQuotientInverseInteger : NumberField.RingOfIntegers M :=
  Polynomial.aeval normalizedInteger dyadicQuotientInversePolynomialInt

private theorem dyadicQuotientInteger_eq_aeval :
    dyadicQuotientInteger =
      Polynomial.aeval normalizedInteger dyadicQuotientPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change (dyadicQuotientInteger : M) =
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      (Polynomial.aeval normalizedInteger dyadicQuotientPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      normalizedInteger dyadicQuotientPolynomialInt]
  simpa only [dyadicQuotientInteger_coe, normalizedInteger_coe,
    IsScalarTower.toAlgHom_apply] using beta_sq_mul_alpha_div_two_formula

theorem dyadicQuotientInteger_mul_inverse :
    dyadicQuotientInteger * dyadicQuotientInverseInteger = 1 := by
  rw [dyadicQuotientInteger_eq_aeval, dyadicQuotientInverseInteger,
    ← map_mul, dyadicQuotient_bezout_identity]
  simp only [map_add, map_one, map_mul, normalizedInteger_aeval,
    mul_zero, add_zero]

/-- The integral quotient `beta^2 * alpha / 2` is a unit. -/
theorem dyadicQuotientInteger_isUnit : IsUnit dyadicQuotientInteger := by
  exact ⟨⟨dyadicQuotientInteger, dyadicQuotientInverseInteger,
    dyadicQuotientInteger_mul_inverse,
    by rw [mul_comm, dyadicQuotientInteger_mul_inverse]⟩, rfl⟩

/-- An inverse of `rho^3 / 3` in the normalized integral order. -/
def triadicQuotientInversePolynomialInt : Polynomial ℤ :=
  X ^ 8 - 4 * X ^ 7 + 4 * X ^ 6 + 3 * X ^ 5 -
    7 * X ^ 4 - X ^ 3 + 5 * X ^ 2 - 1

private def triadicQuotientBezoutPolynomialInt : Polynomial ℤ :=
  -3 * X ^ 7 + 13 * X ^ 6 - 16 * X ^ 5 - 5 * X ^ 4 +
    25 * X ^ 3 - 8 * X ^ 2 - 11 * X + 4

private theorem triadicQuotient_bezout_identity :
    triadicQuotientPolynomialInt * triadicQuotientInversePolynomialInt =
      1 + triadicQuotientBezoutPolynomialInt * normalizedPolynomialInt := by
  simp only [triadicQuotientPolynomialInt,
    triadicQuotientInversePolynomialInt,
    triadicQuotientBezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-- The explicit inverse of the triadic quotient in the full ring of
integers. -/
def triadicQuotientInverseInteger : NumberField.RingOfIntegers M :=
  Polynomial.aeval normalizedInteger triadicQuotientInversePolynomialInt

private theorem triadicQuotientInteger_eq_aeval :
    triadicQuotientInteger =
      Polynomial.aeval normalizedInteger triadicQuotientPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change (triadicQuotientInteger : M) =
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      (Polynomial.aeval normalizedInteger triadicQuotientPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      normalizedInteger triadicQuotientPolynomialInt]
  simpa only [triadicQuotientInteger_coe, normalizedInteger_coe,
    IsScalarTower.toAlgHom_apply] using rho_cube_div_three_formula

theorem triadicQuotientInteger_mul_inverse :
    triadicQuotientInteger * triadicQuotientInverseInteger = 1 := by
  rw [triadicQuotientInteger_eq_aeval, triadicQuotientInverseInteger,
    ← map_mul, triadicQuotient_bezout_identity]
  simp only [map_add, map_one, map_mul, normalizedInteger_aeval,
    mul_zero, add_zero]

/-- The integral quotient `rho^3 / 3` is a unit. -/
theorem triadicQuotientInteger_isUnit : IsUnit triadicQuotientInteger := by
  exact ⟨⟨triadicQuotientInteger, triadicQuotientInverseInteger,
    triadicQuotientInteger_mul_inverse,
    by rw [mul_comm, triadicQuotientInteger_mul_inverse]⟩, rfl⟩

/-! ## Exact principal-ideal factorizations -/

private theorem dyadic_element_factorization :
    betaInteger ^ 2 * alphaInteger =
      dyadicQuotientInteger * (2 : NumberField.RingOfIntegers M) := by
  apply RingOfIntegers.coe_injective
  simp only [map_mul, map_pow, betaInteger_coe, alphaInteger_coe,
    dyadicQuotientInteger_coe, map_ofNat]
  field_simp

/-- Exact factorization of the rational dyadic ideal in the compositum. -/
theorem span_two_eq_span_alpha_mul_span_beta_sq :
    Ideal.span {(2 : NumberField.RingOfIntegers M)} =
      Ideal.span {alphaInteger} * Ideal.span {betaInteger} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
    mul_comm alphaInteger (betaInteger ^ 2), dyadic_element_factorization]
  exact (Ideal.span_singleton_mul_left_unit dyadicQuotientInteger_isUnit 2).symm

private theorem triadic_element_factorization :
    rhoInteger ^ 3 =
      triadicQuotientInteger * (3 : NumberField.RingOfIntegers M) := by
  apply RingOfIntegers.coe_injective
  simp only [map_pow, rhoInteger_coe, triadicQuotientInteger_coe, map_mul,
    map_ofNat]
  field_simp

/-- Exact total-cube factorization of the rational triadic ideal in the
compositum. -/
theorem span_three_eq_span_rho_cube :
    Ideal.span {(3 : NumberField.RingOfIntegers M)} =
      Ideal.span {rhoInteger} ^ 3 := by
  rw [Ideal.span_singleton_pow, triadic_element_factorization]
  exact (Ideal.span_singleton_mul_left_unit triadicQuotientInteger_isUnit 3).symm

end

end MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
