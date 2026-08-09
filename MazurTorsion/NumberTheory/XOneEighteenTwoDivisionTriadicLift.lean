/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionTriadicPrime

/-!
# The triadic prime in the `X₁(18)` two-division compositum

The normalized integral generator has a relative cubic polynomial over the
real cubic coefficient field.  Its discriminant is `-8`, so reduction at the
unique coefficient prime above `3` is controlled by Kummer--Dedekind.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicLift

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The relative normalized polynomial -/

/-- The relative cubic polynomial of the normalized generator over the
coefficient field. -/
def normalizedRelativePolynomial : Polynomial Q.K :=
  X ^ 3 + C (Q.tau ^ 2 - 3) * X ^ 2 +
    C (-2 * Q.tau ^ 2 + Q.tau + 4) * X - 1

theorem normalizedRelativePolynomial_monic :
    normalizedRelativePolynomial.Monic := by
  simp only [normalizedRelativePolynomial]
  monicity <;> norm_num

theorem normalizedRelativePolynomial_natDegree :
    normalizedRelativePolynomial.natDegree = 3 := by
  simp only [normalizedRelativePolynomial]
  compute_degree!

private def normalizedRelativeExpression : Polynomial ℚ :=
  X ^ 3 + (coefficientPolynomial ^ 2 - 3) * X ^ 2 +
    (-2 * coefficientPolynomial ^ 2 + coefficientPolynomial + 4) * X - 1

private def normalizedRelativeReductionQuotient : Polynomial ℚ :=
  X ^ 9 - 7 * X ^ 8 + 21 * X ^ 7 - 36 * X ^ 6 +
    39 * X ^ 5 - 28 * X ^ 4 + 13 * X ^ 3 -
    2 * X ^ 2 - X + 1

private theorem normalizedRelative_reduction_identity :
    normalizedRelativeExpression =
      normalizedRelativeReductionQuotient * normalizedPolynomial := by
  simp only [normalizedRelativeExpression,
    normalizedRelativeReductionQuotient, coefficientPolynomial,
    normalizedPolynomial]
  ring

private theorem normalizedRelativeExpression_root :
    Polynomial.aeval normalizedElement normalizedRelativeExpression = 0 := by
  rw [normalizedRelative_reduction_identity]
  simp only [map_mul, normalizedElement_root, mul_zero]

/-- The normalized generator satisfies the displayed relative cubic. -/
theorem normalizedElement_relative_root :
    Polynomial.aeval normalizedElement normalizedRelativePolynomial = 0 := by
  simp only [normalizedRelativePolynomial, map_sub, map_add, map_mul,
    map_pow, aeval_X, aeval_C, map_neg, map_one, map_ofNat]
  change normalizedElement ^ 3 +
      (t ^ 2 - 3) * normalizedElement ^ 2 +
      (-2 * t ^ 2 + t + 4) * normalizedElement - 1 = 0
  rw [coefficientGenerator_formula]
  simpa only [normalizedRelativeExpression, map_sub, map_add, map_mul,
    map_pow, map_ofNat, map_neg, map_one, aeval_X] using
    normalizedRelativeExpression_root

/-- The normalized generator also generates the compositum over the
coefficient field. -/
theorem normalizedElement_adjoin_coefficient_eq_top :
    Algebra.adjoin Q.K ({normalizedElement} : Set M) = ⊤ := by
  apply top_unique
  intro z hz
  have hzRat : z ∈ Algebra.adjoin ℚ ({normalizedElement} : Set M) := by
    rw [normalizedElement_adjoin_eq_top]
    trivial
  have hle : Algebra.adjoin ℚ ({normalizedElement} : Set M) ≤
      (Algebra.adjoin Q.K ({normalizedElement} : Set M)).restrictScalars ℚ := by
    apply Algebra.adjoin_le
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Algebra.subset_adjoin (R := Q.K) (Set.mem_singleton normalizedElement)
  exact hle hzRat

private theorem normalizedElement_relative_minpoly_natDegree :
    (minpoly Q.K normalizedElement).natDegree = 3 := by
  let pb : PowerBasis Q.K M :=
    PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite Q.K normalizedElement)
      normalizedElement_adjoin_coefficient_eq_top
  calc
    (minpoly Q.K normalizedElement).natDegree = pb.dim := by
      simpa only [pb, PowerBasis.ofAdjoinEqTop_gen] using
        pb.natDegree_minpoly
    _ = Module.finrank Q.K M := pb.finrank.symm
    _ = 3 := finrank_M_over_K

/-- The displayed relative cubic is exactly the minimal polynomial of the
normalized generator over the coefficient field. -/
theorem normalizedElement_minpoly_relative :
    minpoly Q.K normalizedElement = normalizedRelativePolynomial := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (IsIntegral.of_finite Q.K normalizedElement))
    normalizedRelativePolynomial_monic
    (minpoly.dvd Q.K normalizedElement normalizedElement_relative_root)
    (by rw [normalizedRelativePolynomial_natDegree,
      normalizedElement_relative_minpoly_natDegree])).symm

/-- The relative cubic has discriminant `-8`. -/
theorem normalizedRelativePolynomial_discriminant :
    normalizedRelativePolynomial.discr = -8 := by
  have hcoeffZero : normalizedRelativePolynomial.coeff 0 = -1 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffOne : normalizedRelativePolynomial.coeff 1 =
      -2 * Q.tau ^ 2 + Q.tau + 4 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffTwo : normalizedRelativePolynomial.coeff 2 =
      Q.tau ^ 2 - 3 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  have hcoeffThree : normalizedRelativePolynomial.coeff 3 = 1 := by
    simp only [normalizedRelativePolynomial, coeff_sub, coeff_add,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_one]
    norm_num
  rw [Polynomial.discr_of_degree_eq_three]
  · rw [hcoeffZero, hcoeffOne, hcoeffTwo, hcoeffThree]
    ring_nf
    linear_combination
      (4 * Q.tau ^ 5 - 4 * Q.tau ^ 4 + 9 * Q.tau ^ 3 -
        24 * Q.tau ^ 2 - 3 * Q.tau + 23) * Q.tau_cubic
  · rw [degree_eq_natDegree normalizedRelativePolynomial_monic.ne_zero,
      normalizedRelativePolynomial_natDegree]
    norm_num

/-! ## The integral relative polynomial -/

/-- The same relative polynomial over the coefficient ring of integers. -/
def normalizedRelativePolynomialInteger :
    Polynomial (NumberField.RingOfIntegers Q.K) :=
  X ^ 3 + C (coefficientInteger ^ 2 - 3) * X ^ 2 +
    C (-2 * coefficientInteger ^ 2 + coefficientInteger + 4) * X - 1

theorem normalizedRelativePolynomialInteger_monic :
    normalizedRelativePolynomialInteger.Monic := by
  simp only [normalizedRelativePolynomialInteger]
  monicity <;> norm_num

theorem normalizedRelativePolynomialInteger_map :
    normalizedRelativePolynomialInteger.map
        (algebraMap (NumberField.RingOfIntegers Q.K) Q.K) =
      normalizedRelativePolynomial := by
  have hcoefficient :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K
          coefficientInteger = Q.tau := rfl
  have htwo :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 2 = 2 := by
    exact map_ofNat _ 2
  have hthree :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 3 = 3 := by
    exact map_ofNat _ 3
  have hfour :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 4 = 4 := by
    exact map_ofNat _ 4
  simp [normalizedRelativePolynomialInteger,
    normalizedRelativePolynomial, hcoefficient, htwo, hthree, hfour]

/-- The displayed integral cubic is the minimal polynomial of the normalized
integer over the coefficient ring of integers. -/
theorem normalizedInteger_minpoly_relative :
    minpoly (NumberField.RingOfIntegers Q.K) normalizedInteger =
      normalizedRelativePolynomialInteger := by
  apply Polynomial.map_injective
    (algebraMap (NumberField.RingOfIntegers Q.K) Q.K)
    RingOfIntegers.coe_injective
  rw [normalizedRelativePolynomialInteger_map]
  have hInt : IsIntegral (NumberField.RingOfIntegers Q.K)
      normalizedInteger :=
    Algebra.IsIntegral.isIntegral (R := NumberField.RingOfIntegers Q.K)
      normalizedInteger
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions Q.K M
    hInt
  rw [← hfield]
  change minpoly Q.K normalizedElement = normalizedRelativePolynomial
  exact normalizedElement_minpoly_relative

end

end MazurTorsion.XOneEighteenTwoDivisionTriadicLift
