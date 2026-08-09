/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionIntegralModel
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionNorms

/-!
# Integral elements in the `X₁(18)` two-division compositum

This file expresses the explicit descent generators as integer polynomials in
the normalized algebraic integer.  The identities are checked by bounded
polynomial reduction modulo its monic degree-nine equation.  They therefore
do not assume that the normalized power order is the full ring of integers.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralElements

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel

/-- The coefficient-field generator as a reduced polynomial in the
normalized generator. -/
def coefficientPolynomial : Polynomial ℚ :=
  -X ^ 8 + 4 * X ^ 7 - 5 * X ^ 6 + 5 * X ^ 4 -
    2 * X ^ 3 - X ^ 2 + 2 * X - 1

/-- The relative cubic generator as a reduced polynomial in the normalized
generator. -/
def relativePolynomialInNormalized : Polynomial ℚ :=
  -X ^ 8 + 4 * X ^ 7 - 4 * X ^ 6 - 4 * X ^ 5 +
    9 * X ^ 4 + 2 * X ^ 3 - 9 * X ^ 2 + 2 * X + 3

private def coefficientGeneratorNumerator : Polynomial ℚ :=
  1944 - 1944 * X + 2511 * X ^ 2 - 810 * X ^ 3 +
    135 * X ^ 4 + 216 * X ^ 5 - 72 * X ^ 6 - 6 * X ^ 7 + 4 * X ^ 8

private theorem coefficientGeneratorPolynomial_eq :
    coefficientGeneratorPolynomial =
      C (1 / 2673) * coefficientGeneratorNumerator := by
  rfl

private def coefficientReductionQuotient : Polynomial ℚ :=
  4 * X ^ 39 - 116 * X ^ 38 + 1572 * X ^ 37 - 13104 * X ^ 36 +
      74152 * X ^ 35 - 294204 * X ^ 34 + 798830 * X ^ 33 -
      1263102 * X ^ 32 - 49722 * X ^ 31 + 6055080 * X ^ 30 -
      15642084 * X ^ 29 + 14596854 * X ^ 28 + 19949788 * X ^ 27 -
      80612276 * X ^ 26 + 88045260 * X ^ 25 + 51038096 * X ^ 24 -
      264079212 * X ^ 23 + 255207684 * X ^ 22 + 154030532 * X ^ 21 -
      590624884 * X ^ 20 + 397288638 * X ^ 19 + 407446306 * X ^ 18 -
      857304078 * X ^ 17 + 263874420 * X ^ 16 + 664663143 * X ^ 15 -
      718287213 * X ^ 14 - 76011993 * X ^ 13 + 580162460 * X ^ 12 -
      272499070 * X ^ 11 - 202705341 * X ^ 10 + 234062868 * X ^ 9 -
      6549256 * X ^ 8 - 86738118 * X ^ 7 + 30274846 * X ^ 6 +
      13634238 * X ^ 5 - 9014574 * X ^ 4 - 215009 * X ^ 3 +
      680953 * X ^ 2 + 5346 * X + 16679

private theorem coefficientNumerator_comp_inverse_identity :
    coefficientGeneratorNumerator.comp inversePolynomial =
      2673 * coefficientPolynomial +
        coefficientReductionQuotient * normalizedPolynomial := by
  simp only [coefficientGeneratorNumerator, inversePolynomial,
    coefficientPolynomial, coefficientReductionQuotient,
    normalizedPolynomial, add_comp, sub_comp, mul_comp, pow_comp,
    X_comp, ofNat_comp]
  ring

/-- Reconstruction of the coefficient-field generator from the normalized
integral generator. -/
theorem coefficientGenerator_formula :
    t = Polynomial.aeval normalizedElement coefficientPolynomial := by
  rw [← coefficientGenerator_reconstruction,
    coefficientGeneratorPolynomial_eq, map_mul, aeval_C,
    ← normalizedElement_reconstruction, ← Polynomial.aeval_comp]
  rw [coefficientNumerator_comp_inverse_identity]
  simp only [map_add, map_mul, map_ofNat, normalizedElement_root,
    mul_zero, add_zero]
  rw [map_div₀, map_one, map_ofNat]
  field_simp

/-- Reconstruction of the relative generator from the normalized integral
generator. -/
theorem relativeGenerator_formula :
    s = Polynomial.aeval normalizedElement relativePolynomialInNormalized := by
  calc
    s = t - primitiveElement := by simp only [primitiveElement]; ring
    _ = Polynomial.aeval normalizedElement coefficientPolynomial -
        Polynomial.aeval normalizedElement inversePolynomial := by
      rw [coefficientGenerator_formula, normalizedElement_reconstruction]
    _ = Polynomial.aeval normalizedElement
        (coefficientPolynomial - inversePolynomial) := by rw [map_sub]
    _ = Polynomial.aeval normalizedElement
        relativePolynomialInNormalized := by
      congr 1
      simp only [coefficientPolynomial, inversePolynomial,
        relativePolynomialInNormalized]
      ring

private theorem scaled_aeval_of_reduction (n : ℕ) (hn : n ≠ 0)
    {raw target quotient : Polynomial ℚ}
    (hred : raw = n * target + quotient * normalizedPolynomial) :
    (1 / (n : M)) * Polynomial.aeval normalizedElement raw =
      Polynomial.aeval normalizedElement target := by
  rw [hred]
  simp only [map_add, map_mul, map_natCast, normalizedElement_root,
    mul_zero, add_zero, div_eq_mul_inv, one_mul]
  have hnM : (n : M) ≠ 0 := by exact_mod_cast hn
  rw [← mul_assoc, inv_mul_cancel₀ hnM, one_mul]

/-! ## Integral polynomial representatives -/

/-- Integer polynomial representing `alpha`. -/
def alphaPolynomialInt : Polynomial ℤ :=
  X * (X ^ 7 - 3 * X ^ 6 + 7 * X ^ 4 - 3 * X ^ 3 -
    9 * X ^ 2 + 4 * X + 5)

private def alphaPolynomial : Polynomial ℚ :=
  X * (X ^ 7 - 3 * X ^ 6 + 7 * X ^ 4 - 3 * X ^ 3 -
    9 * X ^ 2 + 4 * X + 5)

theorem alphaPolynomialInt_map :
    alphaPolynomialInt.map (algebraMap ℤ ℚ) = alphaPolynomial := by
  norm_num [alphaPolynomialInt, alphaPolynomial]

private def alphaNumerator : Polynomial ℚ :=
  (2 * coefficientPolynomial ^ 2 - coefficientPolynomial - 1) *
      relativePolynomialInNormalized ^ 2 +
    (-4 * coefficientPolynomial ^ 2 - coefficientPolynomial + 11) *
      relativePolynomialInNormalized +
    (-4 * coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 14)

private def alphaReductionQuotient : Polynomial ℚ :=
  2 * X ^ 23 - 26 * X ^ 22 + 150 * X ^ 21 - 492 * X ^ 20 +
    946 * X ^ 19 - 848 * X ^ 18 - 494 * X ^ 17 + 2212 * X ^ 16 -
    1759 * X ^ 15 - 1699 * X ^ 14 + 4642 * X ^ 13 -
    3073 * X ^ 12 - 1526 * X ^ 11 + 3832 * X ^ 10 -
    1816 * X ^ 9 - 1428 * X ^ 8 + 2503 * X ^ 7 - 1325 * X ^ 6 -
    126 * X ^ 5 + 587 * X ^ 4 - 316 * X ^ 3 + 14 * X ^ 2 +
    78 * X - 50

private theorem alpha_reduction_identity :
    alphaNumerator = 18 * alphaPolynomial +
      alphaReductionQuotient * normalizedPolynomial := by
  simp only [alphaNumerator, alphaPolynomial, alphaReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem alpha_formula_rat :
    alpha = Polynomial.aeval normalizedElement alphaPolynomial := by
  calc
    alpha = (1 / 18 : M) *
        Polynomial.aeval normalizedElement alphaNumerator := by
      rw [alpha, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_one, map_neg]
      change ((2 * t ^ 2 - t - 1) / 18) * s ^ 2 +
          ((-4 * t ^ 2 - t + 11) / 18) * s +
          ((-4 * t ^ 2 + 2 * t + 14) / 18) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [alphaNumerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_one, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement alphaPolynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        alpha_reduction_identity

/-- The first dyadic generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem alpha_formula :
    alpha = Polynomial.aeval normalizedElement alphaPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    alphaPolynomialInt, alphaPolynomialInt_map]
  exact alpha_formula_rat

/-- Integer polynomial representing `beta`. -/
def betaPolynomialInt : Polynomial ℤ :=
  -(X - 2) * (2 * X ^ 7 - 3 * X ^ 6 - X ^ 5 + 6 * X ^ 4 +
    X ^ 3 - 4 * X ^ 2 + 1)

private def betaPolynomial : Polynomial ℚ :=
  -(X - 2) * (2 * X ^ 7 - 3 * X ^ 6 - X ^ 5 + 6 * X ^ 4 +
    X ^ 3 - 4 * X ^ 2 + 1)

theorem betaPolynomialInt_map :
    betaPolynomialInt.map (algebraMap ℤ ℚ) = betaPolynomial := by
  norm_num [betaPolynomialInt, betaPolynomial]

private def betaNumerator : Polynomial ℚ :=
  (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 2) *
      relativePolynomialInNormalized ^ 2 +
    (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 8) *
      relativePolynomialInNormalized +
    (8 * coefficientPolynomial ^ 2 + 8 * coefficientPolynomial - 10)

private def betaReductionQuotient : Polynomial ℚ :=
  -X ^ 23 + 13 * X ^ 22 - 75 * X ^ 21 + 246 * X ^ 20 -
    473 * X ^ 19 + 424 * X ^ 18 + 247 * X ^ 17 - 1106 * X ^ 16 +
    881 * X ^ 15 + 836 * X ^ 14 - 2267 * X ^ 13 +
    1412 * X ^ 12 + 937 * X ^ 11 - 2042 * X ^ 10 + 881 * X ^ 9 +
    888 * X ^ 8 - 1403 * X ^ 7 + 580 * X ^ 6 + 387 * X ^ 5 -
    610 * X ^ 4 + 266 * X ^ 3 + 35 * X ^ 2 - 96 * X + 40

private theorem beta_reduction_identity :
    betaNumerator = 18 * betaPolynomial +
      betaReductionQuotient * normalizedPolynomial := by
  simp only [betaNumerator, betaPolynomial, betaReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem beta_formula_rat :
    beta = Polynomial.aeval normalizedElement betaPolynomial := by
  calc
    beta = (1 / 18 : M) *
        Polynomial.aeval normalizedElement betaNumerator := by
      rw [beta, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_neg]
      change ((-t ^ 2 + 2 * t + 2) / 18) * s ^ 2 +
          ((-t ^ 2 + 2 * t + 8) / 18) * s +
          ((8 * t ^ 2 + 8 * t - 10) / 18) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [betaNumerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement betaPolynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        beta_reduction_identity

/-- The second dyadic generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem beta_formula :
    beta = Polynomial.aeval normalizedElement betaPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    betaPolynomialInt, betaPolynomialInt_map]
  exact beta_formula_rat

/-- Integer polynomial representing `rho`. -/
def rhoPolynomialInt : Polynomial ℤ :=
  (X - 1) * (3 * X ^ 7 - 8 * X ^ 6 - X ^ 5 + 17 * X ^ 4 -
    6 * X ^ 3 - 19 * X ^ 2 + 2 * X + 6)

private def rhoPolynomial : Polynomial ℚ :=
  (X - 1) * (3 * X ^ 7 - 8 * X ^ 6 - X ^ 5 + 17 * X ^ 4 -
    6 * X ^ 3 - 19 * X ^ 2 + 2 * X + 6)

theorem rhoPolynomialInt_map :
    rhoPolynomialInt.map (algebraMap ℤ ℚ) = rhoPolynomial := by
  norm_num [rhoPolynomialInt, rhoPolynomial]

private def rhoNumerator : Polynomial ℚ :=
  -coefficientPolynomial * relativePolynomialInNormalized ^ 2 +
    (coefficientPolynomial - 2) * relativePolynomialInNormalized +
    (2 * coefficientPolynomial ^ 2 + 2 * coefficientPolynomial - 8)

private def rhoReductionQuotient : Polynomial ℚ :=
  X ^ 15 - 9 * X ^ 14 + 34 * X ^ 13 - 65 * X ^ 12 + 48 * X ^ 11 +
    46 * X ^ 10 - 116 * X ^ 9 + 30 * X ^ 8 + 138 * X ^ 7 -
    176 * X ^ 6 + 63 * X ^ 5 + 33 * X ^ 4 - 28 * X ^ 3 -
    15 * X ^ 2 + 34 * X - 28

private theorem rho_reduction_identity :
    rhoNumerator = 6 * rhoPolynomial +
      rhoReductionQuotient * normalizedPolynomial := by
  simp only [rhoNumerator, rhoPolynomial, rhoReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem rho_formula_rat :
    rho = Polynomial.aeval normalizedElement rhoPolynomial := by
  calc
    rho = (1 / 6 : M) *
        Polynomial.aeval normalizedElement rhoNumerator := by
      rw [rho, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_neg]
      change (-t / 6) * s ^ 2 + ((t - 2) / 6) * s +
          ((2 * t ^ 2 + 2 * t - 8) / 6) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [rhoNumerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement rhoPolynomial := by
      exact scaled_aeval_of_reduction 6 (by norm_num)
        rho_reduction_identity

/-- The triadic generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem rho_formula :
    rho = Polynomial.aeval normalizedElement rhoPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    rhoPolynomialInt, rhoPolynomialInt_map]
  exact rho_formula_rat

/-- Integer polynomial representing `h1`. -/
def h1PolynomialInt : Polynomial ℤ :=
  -X ^ 8 + 3 * X ^ 7 - 8 * X ^ 5 + 6 * X ^ 4 +
    8 * X ^ 3 - 7 * X ^ 2 - 3 * X + 3

private def h1Polynomial : Polynomial ℚ :=
  -X ^ 8 + 3 * X ^ 7 - 8 * X ^ 5 + 6 * X ^ 4 +
    8 * X ^ 3 - 7 * X ^ 2 - 3 * X + 3

theorem h1PolynomialInt_map :
    h1PolynomialInt.map (algebraMap ℤ ℚ) = h1Polynomial := by
  norm_num [h1PolynomialInt, h1Polynomial]

private def h1Numerator : Polynomial ℚ :=
  (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 2) *
      relativePolynomialInNormalized ^ 2 +
    (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 8) *
      relativePolynomialInNormalized +
    2 * (4 * coefficientPolynomial ^ 2 - 5 * coefficientPolynomial - 5)

private theorem h1_reduction_identity :
    h1Numerator = 18 * h1Polynomial +
      betaReductionQuotient * normalizedPolynomial := by
  simp only [h1Numerator, h1Polynomial, betaReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem h1_formula_rat :
    h1 = Polynomial.aeval normalizedElement h1Polynomial := by
  calc
    h1 = (1 / 18 : M) *
        Polynomial.aeval normalizedElement h1Numerator := by
      rw [h1, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_neg]
      change ((-t ^ 2 + 2 * t + 2) / 18) * s ^ 2 +
          ((-t ^ 2 + 2 * t + 8) / 18) * s +
          ((4 * t ^ 2 - 5 * t - 5) / 9) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [h1Numerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement h1Polynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        h1_reduction_identity

/-- The first norm-one generator is the value of an integer polynomial in
the normalized algebraic integer. -/
theorem h1_formula :
    h1 = Polynomial.aeval normalizedElement h1PolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    h1PolynomialInt, h1PolynomialInt_map]
  exact h1_formula_rat

/-- Integer polynomial representing `h2`. -/
def h2PolynomialInt : Polynomial ℤ :=
  -X ^ 6 + 3 * X ^ 5 - X ^ 4 - 4 * X ^ 3 + 3 * X ^ 2 + 3 * X - 1

private def h2Polynomial : Polynomial ℚ :=
  -X ^ 6 + 3 * X ^ 5 - X ^ 4 - 4 * X ^ 3 + 3 * X ^ 2 + 3 * X - 1

theorem h2PolynomialInt_map :
    h2PolynomialInt.map (algebraMap ℤ ℚ) = h2Polynomial := by
  norm_num [h2PolynomialInt, h2Polynomial]

private def h2Numerator : Polynomial ℚ :=
  relativePolynomialInNormalized ^ 2 + relativePolynomialInNormalized +
    2 * (coefficientPolynomial ^ 2 + coefficientPolynomial) - 6

private def h2ReductionQuotient : Polynomial ℚ :=
  3 * X ^ 7 - 15 * X ^ 6 + 31 * X ^ 5 - 32 * X ^ 4 +
    14 * X ^ 3 - 5 * X ^ 2 + 8 * X - 12

private theorem h2_reduction_identity :
    h2Numerator = 6 * h2Polynomial +
      h2ReductionQuotient * normalizedPolynomial := by
  simp only [h2Numerator, h2Polynomial, h2ReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem h2_formula_rat :
    h2 = Polynomial.aeval normalizedElement h2Polynomial := by
  calc
    h2 = (1 / 6 : M) *
        Polynomial.aeval normalizedElement h2Numerator := by
      rw [h2, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_pow, map_ofNat, map_one]
      change (1 / 6 : M) * s ^ 2 + (1 / 6 : M) * s +
          ((t ^ 2 + t) / 3 - 1) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [h2Numerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat]
      ring
    _ = Polynomial.aeval normalizedElement h2Polynomial := by
      exact scaled_aeval_of_reduction 6 (by norm_num)
        h2_reduction_identity

/-- The second norm-one generator is the value of an integer polynomial in
the normalized algebraic integer. -/
theorem h2_formula :
    h2 = Polynomial.aeval normalizedElement h2PolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    h2PolynomialInt, h2PolynomialInt_map]
  exact h2_formula_rat

/-- Integer polynomial representing `h3`. -/
def h3PolynomialInt : Polynomial ℤ :=
  -(X ^ 3 - X ^ 2 + 1) *
    (X ^ 5 - 3 * X ^ 4 + X ^ 3 + 4 * X ^ 2 - 3 * X - 4)

private def h3Polynomial : Polynomial ℚ :=
  -(X ^ 3 - X ^ 2 + 1) *
    (X ^ 5 - 3 * X ^ 4 + X ^ 3 + 4 * X ^ 2 - 3 * X - 4)

theorem h3PolynomialInt_map :
    h3PolynomialInt.map (algebraMap ℤ ℚ) = h3Polynomial := by
  norm_num [h3PolynomialInt, h3Polynomial]

private def h3Numerator : Polynomial ℚ :=
  (2 * coefficientPolynomial ^ 2 - coefficientPolynomial + 2) *
      relativePolynomialInNormalized ^ 2 +
    (2 * coefficientPolynomial ^ 2 - 7 * coefficientPolynomial + 14) *
      relativePolynomialInNormalized +
    2 * (4 * coefficientPolynomial ^ 2 - 5 * coefficientPolynomial + 4)

private def h3ReductionQuotient : Polynomial ℚ :=
  2 * X ^ 23 - 26 * X ^ 22 + 150 * X ^ 21 - 492 * X ^ 20 +
    946 * X ^ 19 - 848 * X ^ 18 - 494 * X ^ 17 + 2212 * X ^ 16 -
    1765 * X ^ 15 - 1645 * X ^ 14 + 4432 * X ^ 13 -
    2629 * X ^ 12 - 2018 * X ^ 11 + 3946 * X ^ 10 -
    1414 * X ^ 9 - 1866 * X ^ 8 + 2428 * X ^ 7 - 812 * X ^ 6 -
    579 * X ^ 5 + 677 * X ^ 4 - 166 * X ^ 3 - 163 * X ^ 2 +
    156 * X - 68

private theorem h3_reduction_identity :
    h3Numerator = 18 * h3Polynomial +
      h3ReductionQuotient * normalizedPolynomial := by
  simp only [h3Numerator, h3Polynomial, h3ReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem h3_formula_rat :
    h3 = Polynomial.aeval normalizedElement h3Polynomial := by
  calc
    h3 = (1 / 18 : M) *
        Polynomial.aeval normalizedElement h3Numerator := by
      rw [h3, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat]
      change ((2 * t ^ 2 - t + 2) / 18) * s ^ 2 +
          ((2 * t ^ 2 - 7 * t + 14) / 18) * s +
          ((4 * t ^ 2 - 5 * t + 4) / 9) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [h3Numerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat]
      ring
    _ = Polynomial.aeval normalizedElement h3Polynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        h3_reduction_identity

/-- The first norm-four generator is the value of an integer polynomial in
the normalized algebraic integer. -/
theorem h3_formula :
    h3 = Polynomial.aeval normalizedElement h3PolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    h3PolynomialInt, h3PolynomialInt_map]
  exact h3_formula_rat

/-- Integer polynomial representing `h4`. -/
def h4PolynomialInt : Polynomial ℤ :=
  -(X ^ 3 - 2 * X ^ 2 + X + 1) * (X ^ 3 - X ^ 2 - 2 * X - 1)

private def h4Polynomial : Polynomial ℚ :=
  -(X ^ 3 - 2 * X ^ 2 + X + 1) * (X ^ 3 - X ^ 2 - 2 * X - 1)

theorem h4PolynomialInt_map :
    h4PolynomialInt.map (algebraMap ℤ ℚ) = h4Polynomial := by
  norm_num [h4PolynomialInt, h4Polynomial]

private def h4Numerator : Polynomial ℚ :=
  (-coefficientPolynomial ^ 2 + 3) * relativePolynomialInNormalized ^ 2 +
    (coefficientPolynomial ^ 2 + 1) * relativePolynomialInNormalized +
    6 * coefficientPolynomial ^ 2 - 10

private def h4ReductionQuotient : Polynomial ℚ :=
  -X ^ 23 + 13 * X ^ 22 - 75 * X ^ 21 + 246 * X ^ 20 -
    473 * X ^ 19 + 424 * X ^ 18 + 247 * X ^ 17 - 1106 * X ^ 16 +
    881 * X ^ 15 + 836 * X ^ 14 - 2269 * X ^ 13 +
    1430 * X ^ 12 + 869 * X ^ 11 - 1912 * X ^ 10 + 783 * X ^ 9 +
    802 * X ^ 8 - 1164 * X ^ 7 + 459 * X ^ 6 + 232 * X ^ 5 -
    356 * X ^ 4 + 148 * X ^ 3 - 10 * X - 14

private theorem h4_reduction_identity :
    h4Numerator = 6 * h4Polynomial +
      h4ReductionQuotient * normalizedPolynomial := by
  simp only [h4Numerator, h4Polynomial, h4ReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem h4_formula_rat :
    h4 = Polynomial.aeval normalizedElement h4Polynomial := by
  calc
    h4 = (1 / 6 : M) *
        Polynomial.aeval normalizedElement h4Numerator := by
      rw [h4, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_pow, map_ofNat,
        map_one, map_neg]
      change ((-t ^ 2 + 3) / 6) * s ^ 2 +
          ((t ^ 2 + 1) / 6) * s + (t ^ 2 - 5 / 3) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [h4Numerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_one, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement h4Polynomial := by
      exact scaled_aeval_of_reduction 6 (by norm_num)
        h4_reduction_identity

/-- The final kernel generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem h4_formula :
    h4 = Polynomial.aeval normalizedElement h4PolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    h4PolynomialInt, h4PolynomialInt_map]
  exact h4_formula_rat

/-- Integer polynomial representing the integral quotient
`beta² * alpha / 2`. -/
def dyadicQuotientPolynomialInt : Polynomial ℤ :=
  -2 * X ^ 8 + 6 * X ^ 7 - 2 * X ^ 6 - 9 * X ^ 5 +
    7 * X ^ 4 + 8 * X ^ 3 - 3 * X ^ 2 - X + 1

private def dyadicQuotientPolynomial : Polynomial ℚ :=
  -2 * X ^ 8 + 6 * X ^ 7 - 2 * X ^ 6 - 9 * X ^ 5 +
    7 * X ^ 4 + 8 * X ^ 3 - 3 * X ^ 2 - X + 1

theorem dyadicQuotientPolynomialInt_map :
    dyadicQuotientPolynomialInt.map (algebraMap ℤ ℚ) =
      dyadicQuotientPolynomial := by
  norm_num [dyadicQuotientPolynomialInt, dyadicQuotientPolynomial]

private def dyadicQuotientReduction : Polynomial ℚ :=
  4 * X ^ 15 - 28 * X ^ 14 + 69 * X ^ 13 - 38 * X ^ 12 -
    131 * X ^ 11 + 210 * X ^ 10 + 74 * X ^ 9 - 364 * X ^ 8 +
    120 * X ^ 7 + 278 * X ^ 6 - 173 * X ^ 5 - 110 * X ^ 4 +
    97 * X ^ 3 + 10 * X ^ 2 - 22 * X + 2

private theorem dyadicQuotient_reduction_identity :
    betaPolynomial ^ 2 * alphaPolynomial =
      2 * dyadicQuotientPolynomial +
        dyadicQuotientReduction * normalizedPolynomial := by
  simp only [betaPolynomial, alphaPolynomial, dyadicQuotientPolynomial,
    dyadicQuotientReduction, normalizedPolynomial]
  ring

private theorem beta_sq_mul_alpha_div_two_formula_rat :
    beta ^ 2 * alpha / 2 =
      Polynomial.aeval normalizedElement dyadicQuotientPolynomial := by
  calc
    beta ^ 2 * alpha / 2 = (1 / 2 : M) *
        Polynomial.aeval normalizedElement
          (betaPolynomial ^ 2 * alphaPolynomial) := by
      rw [beta_formula_rat, alpha_formula_rat]
      simp only [map_mul, map_pow]
      ring
    _ = Polynomial.aeval normalizedElement dyadicQuotientPolynomial := by
      exact scaled_aeval_of_reduction 2 (by norm_num)
        dyadicQuotient_reduction_identity

theorem beta_sq_mul_alpha_div_two_formula :
    beta ^ 2 * alpha / 2 =
      Polynomial.aeval normalizedElement dyadicQuotientPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    dyadicQuotientPolynomialInt, dyadicQuotientPolynomialInt_map]
  exact beta_sq_mul_alpha_div_two_formula_rat

/-- Integer polynomial representing the integral quotient `rho³ / 3`. -/
def triadicQuotientPolynomialInt : Polynomial ℤ :=
  -3 * X ^ 8 + 10 * X ^ 7 - 3 * X ^ 6 - 21 * X ^ 5 +
    17 * X ^ 4 + 21 * X ^ 3 - 17 * X ^ 2 - 11 * X + 3

private def triadicQuotientPolynomial : Polynomial ℚ :=
  -3 * X ^ 8 + 10 * X ^ 7 - 3 * X ^ 6 - 21 * X ^ 5 +
    17 * X ^ 4 + 21 * X ^ 3 - 17 * X ^ 2 - 11 * X + 3

theorem triadicQuotientPolynomialInt_map :
    triadicQuotientPolynomialInt.map (algebraMap ℤ ℚ) =
      triadicQuotientPolynomial := by
  norm_num [triadicQuotientPolynomialInt, triadicQuotientPolynomial]

private def triadicQuotientReduction : Polynomial ℚ :=
  27 * X ^ 15 - 216 * X ^ 14 + 630 * X ^ 13 - 530 * X ^ 12 -
    1200 * X ^ 11 + 2973 * X ^ 10 - 669 * X ^ 9 - 4320 * X ^ 8 +
    3882 * X ^ 7 + 2433 * X ^ 6 - 4476 * X ^ 5 + 87 * X ^ 4 +
    2312 * X ^ 3 - 681 * X ^ 2 - 465 * X + 225

private theorem triadicQuotient_reduction_identity :
    rhoPolynomial ^ 3 = 3 * triadicQuotientPolynomial +
      triadicQuotientReduction * normalizedPolynomial := by
  simp only [rhoPolynomial, triadicQuotientPolynomial,
    triadicQuotientReduction, normalizedPolynomial]
  ring

private theorem rho_cube_div_three_formula_rat :
    rho ^ 3 / 3 =
      Polynomial.aeval normalizedElement triadicQuotientPolynomial := by
  calc
    rho ^ 3 / 3 = (1 / 3 : M) *
        Polynomial.aeval normalizedElement (rhoPolynomial ^ 3) := by
      rw [rho_formula_rat]
      simp only [map_pow]
      ring
    _ = Polynomial.aeval normalizedElement triadicQuotientPolynomial := by
      exact scaled_aeval_of_reduction 3 (by norm_num)
        triadicQuotient_reduction_identity

theorem rho_cube_div_three_formula :
    rho ^ 3 / 3 =
      Polynomial.aeval normalizedElement triadicQuotientPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    triadicQuotientPolynomialInt, triadicQuotientPolynomialInt_map]
  exact rho_cube_div_three_formula_rat

private theorem normalized_aeval_isIntegral (p : Polynomial ℤ) :
    IsIntegral ℤ (Polynomial.aeval normalizedElement p) := by
  rw [← mem_integralClosure_iff]
  have hv : normalizedElement ∈ integralClosure ℤ M :=
    normalizedElement_isIntegral_int
  have hle : Algebra.adjoin ℤ ({normalizedElement} : Set M) ≤
      integralClosure ℤ M :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hv)
  exact hle (Polynomial.aeval_mem_adjoin_singleton ℤ normalizedElement)

theorem alpha_isIntegral : IsIntegral ℤ alpha := by
  rw [alpha_formula]
  exact normalized_aeval_isIntegral alphaPolynomialInt

theorem beta_isIntegral : IsIntegral ℤ beta := by
  rw [beta_formula]
  exact normalized_aeval_isIntegral betaPolynomialInt

theorem rho_isIntegral : IsIntegral ℤ rho := by
  rw [rho_formula]
  exact normalized_aeval_isIntegral rhoPolynomialInt

theorem h1_isIntegral : IsIntegral ℤ h1 := by
  rw [h1_formula]
  exact normalized_aeval_isIntegral h1PolynomialInt

theorem h2_isIntegral : IsIntegral ℤ h2 := by
  rw [h2_formula]
  exact normalized_aeval_isIntegral h2PolynomialInt

theorem h3_isIntegral : IsIntegral ℤ h3 := by
  rw [h3_formula]
  exact normalized_aeval_isIntegral h3PolynomialInt

theorem h4_isIntegral : IsIntegral ℤ h4 := by
  rw [h4_formula]
  exact normalized_aeval_isIntegral h4PolynomialInt

theorem beta_sq_mul_alpha_div_two_isIntegral :
    IsIntegral ℤ (beta ^ 2 * alpha / 2) := by
  rw [beta_sq_mul_alpha_div_two_formula]
  exact normalized_aeval_isIntegral dyadicQuotientPolynomialInt

theorem rho_cube_div_three_isIntegral :
    IsIntegral ℤ (rho ^ 3 / 3) := by
  rw [rho_cube_div_three_formula]
  exact normalized_aeval_isIntegral triadicQuotientPolynomialInt

/-- The first dyadic generator in the full ring of integers. -/
def alphaInteger : NumberField.RingOfIntegers M := ⟨alpha, alpha_isIntegral⟩

/-- The second dyadic generator in the full ring of integers. -/
def betaInteger : NumberField.RingOfIntegers M := ⟨beta, beta_isIntegral⟩

/-- The triadic generator in the full ring of integers. -/
def rhoInteger : NumberField.RingOfIntegers M := ⟨rho, rho_isIntegral⟩

/-- The first norm-one generator in the full ring of integers. -/
def h1Integer : NumberField.RingOfIntegers M := ⟨h1, h1_isIntegral⟩

/-- The second norm-one generator in the full ring of integers. -/
def h2Integer : NumberField.RingOfIntegers M := ⟨h2, h2_isIntegral⟩

/-- The first norm-four generator in the full ring of integers. -/
def h3Integer : NumberField.RingOfIntegers M := ⟨h3, h3_isIntegral⟩

/-- The final kernel generator in the full ring of integers. -/
def h4Integer : NumberField.RingOfIntegers M := ⟨h4, h4_isIntegral⟩

/-- The integral quotient `beta² * alpha / 2`. -/
def dyadicQuotientInteger : NumberField.RingOfIntegers M :=
  ⟨beta ^ 2 * alpha / 2, beta_sq_mul_alpha_div_two_isIntegral⟩

/-- The integral quotient `rho³ / 3`. -/
def triadicQuotientInteger : NumberField.RingOfIntegers M :=
  ⟨rho ^ 3 / 3, rho_cube_div_three_isIntegral⟩

@[simp] theorem alphaInteger_coe : (alphaInteger : M) = alpha := rfl
@[simp] theorem betaInteger_coe : (betaInteger : M) = beta := rfl
@[simp] theorem rhoInteger_coe : (rhoInteger : M) = rho := rfl
@[simp] theorem h1Integer_coe : (h1Integer : M) = h1 := rfl
@[simp] theorem h2Integer_coe : (h2Integer : M) = h2 := rfl
@[simp] theorem h3Integer_coe : (h3Integer : M) = h3 := rfl
@[simp] theorem h4Integer_coe : (h4Integer : M) = h4 := rfl
@[simp] theorem dyadicQuotientInteger_coe :
    (dyadicQuotientInteger : M) = beta ^ 2 * alpha / 2 := rfl
@[simp] theorem triadicQuotientInteger_coe :
    (triadicQuotientInteger : M) = rho ^ 3 / 3 := rfl

end

end MazurTorsion.XOneEighteenTwoDivisionIntegralElements
