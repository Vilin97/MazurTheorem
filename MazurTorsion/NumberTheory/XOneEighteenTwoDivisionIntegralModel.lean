/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallDiscriminant

/-!
# The integral normalized model of the `X₁(18)` two-division compositum

This file records the integer polynomial underlying the normalized rational
power basis and lifts its generator to the full ring of integers.  It makes
no claim that the resulting order is the maximal order.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralModel

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

/-- The monic integer polynomial underlying `normalizedPolynomial`. -/
def normalizedPolynomialInt : Polynomial ℤ :=
  X ^ 9 - 3 * X ^ 8 + 7 * X ^ 6 - 3 * X ^ 5 - 9 * X ^ 4 +
    3 * X ^ 3 + 6 * X ^ 2 - 1

theorem normalizedPolynomialInt_monic : normalizedPolynomialInt.Monic := by
  simp only [normalizedPolynomialInt]
  monicity <;> norm_num

theorem normalizedPolynomialInt_natDegree :
    normalizedPolynomialInt.natDegree = 9 := by
  simp only [normalizedPolynomialInt]
  compute_degree!

theorem normalizedPolynomialInt_map_rat :
    normalizedPolynomialInt.map (algebraMap ℤ ℚ) =
      normalizedPolynomial := by
  norm_num [normalizedPolynomialInt, normalizedPolynomial]

theorem normalizedPolynomialInt_aeval :
    Polynomial.aeval normalizedElement normalizedPolynomialInt = 0 := by
  simpa only [normalizedPolynomialInt, normalizedPolynomial, map_add, map_sub,
    map_mul, map_pow, map_ofNat, map_one, aeval_X] using
      normalizedElement_root

/-- The normalized generator is an algebraic integer. -/
theorem normalizedElement_isIntegral_int :
    IsIntegral ℤ normalizedElement :=
  ⟨normalizedPolynomialInt, normalizedPolynomialInt_monic,
    normalizedPolynomialInt_aeval⟩

/-- The normalized generator as an element of the full ring of integers. -/
def normalizedInteger : NumberField.RingOfIntegers M :=
  ⟨normalizedElement, normalizedElement_isIntegral_int⟩

@[simp]
theorem normalizedInteger_coe :
    (normalizedInteger : M) = normalizedElement := rfl

theorem normalizedInteger_aeval :
    Polynomial.aeval normalizedInteger normalizedPolynomialInt = 0 := by
  rw [← RingOfIntegers.coe_eq_zero_iff]
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  simpa only [← IsScalarTower.algebraMap_eq ℤ
      (NumberField.RingOfIntegers M) M, normalizedInteger_coe,
    ← Polynomial.aeval_def] using normalizedPolynomialInt_aeval

theorem normalizedPolynomialInt_irreducible :
    Irreducible normalizedPolynomialInt := by
  apply normalizedPolynomialInt_monic.irreducible_of_irreducible_map
    (algebraMap ℤ ℚ)
  simpa only [normalizedPolynomialInt_map_rat] using
    normalizedPolynomial_irreducible

/-- The integer polynomial is the exact minimal polynomial of the integral
normalized generator. -/
theorem normalizedInteger_minpoly :
    minpoly ℤ normalizedInteger = normalizedPolynomialInt := by
  let ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd
    (RingOfIntegers.isIntegral normalizedInteger) normalizedInteger_aeval
  symm
  exact Polynomial.eq_of_monic_of_associated
    normalizedPolynomialInt_monic
    (minpoly.monic (RingOfIntegers.isIntegral normalizedInteger)) <| by
      convert Associated.mul_left (minpoly ℤ normalizedInteger) <|
        associated_one_iff_isUnit.mpr <|
          (normalizedPolynomialInt_irreducible.isUnit_or_isUnit hq).resolve_left <|
            minpoly.not_isUnit ℤ normalizedInteger using 1
      rw [mul_one]

end

end MazurTorsion.XOneEighteenTwoDivisionIntegralModel
