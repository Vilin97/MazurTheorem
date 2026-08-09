/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentSextic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Explicit units in the `X₁(13)` two-descent field

This file checks two concrete units in the ring of integers of the sextic
field used by the `X₁(13)` two-descent.  The formulas were recomputed with
exact rational polynomial arithmetic.  The proofs below retain only small
polynomial identities checked by Lean.

These declarations do **not** assert that the two units generate the full
unit group.  Such an exhaustiveness statement requires a separate regulator
or class-group certificate.
-/

namespace MazurTorsion.XOneThirteenTwoDescentUnits

open NumberField Polynomial
open XOneThirteenTwoDescentSextic

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

/-- The first explicit unit value in the sextic field. -/
def unitOneValue : SexticField :=
  (theta ^ 4 + theta ^ 3 + 3 * theta + 4) / 2

/-- An explicit inverse of `unitOneValue`. -/
def unitOneInverseValue : SexticField :=
  -(theta * (theta ^ 4 + theta ^ 3 + 3 * theta + 4)) / 2

/-- The second explicit unit value in the sextic field. -/
def unitTwoValue : SexticField :=
  (2 * theta ^ 5 + 4 * theta ^ 4 + theta ^ 3 + 3 * theta ^ 2 +
    12 * theta + 5) / 2

/-- An explicit inverse of `unitTwoValue`. -/
def unitTwoInverseValue : SexticField :=
  -(2 * theta ^ 5 + 3 * theta ^ 4 + 3 * theta ^ 2 + 9 * theta + 3) / 2

theorem unitOne_mul_inverse : unitOneValue * unitOneInverseValue = 1 := by
  have h := theta_spec
  simp only [unitOneValue, unitOneInverseValue]
  field_simp
  linear_combination -(theta ^ 3 + 4) * h

theorem unitTwo_mul_inverse : unitTwoValue * unitTwoInverseValue = 1 := by
  have h := theta_spec
  simp only [unitTwoValue, unitTwoInverseValue]
  field_simp
  linear_combination
    -(4 * theta ^ 4 + 6 * theta ^ 3 - 2 * theta ^ 2 + 5 * theta + 19) * h

/-- A monic equation for the first explicit unit value. -/
theorem unitOne_equation :
    unitOneValue ^ 6 - 2 * unitOneValue ^ 5 +
      2 * unitOneValue ^ 3 - unitOneValue ^ 2 + 1 = 0 := by
  have h := theta_spec
  simp only [unitOneValue]
  field_simp
  linear_combination
    (theta ^ 18 + 4 * theta ^ 17 + 6 * theta ^ 16 + 20 * theta ^ 15 +
      65 * theta ^ 14 + 96 * theta ^ 13 + 166 * theta ^ 12 +
      424 * theta ^ 11 + 606 * theta ^ 10 + 716 * theta ^ 9 +
      1384 * theta ^ 8 + 1880 * theta ^ 7 + 1657 * theta ^ 6 +
      2252 * theta ^ 5 + 2848 * theta ^ 4 + 1904 * theta ^ 3 +
      1456 * theta ^ 2 + 1664 * theta + 832) * h

/-- A monic equation for the second explicit unit value. -/
theorem unitTwo_equation :
    unitTwoValue ^ 6 + 2 * unitTwoValue ^ 5 +
      3 * unitTwoValue ^ 4 + 4 * unitTwoValue ^ 3 +
      4 * unitTwoValue ^ 2 + 2 * unitTwoValue + 1 = 0 := by
  have h := theta_spec
  simp only [unitTwoValue]
  field_simp
  linear_combination
    (64 * theta ^ 24 + 640 * theta ^ 23 + 2688 * theta ^ 22 +
      6592 * theta ^ 21 + 13808 * theta ^ 20 + 34496 * theta ^ 19 +
      79200 * theta ^ 18 + 136608 * theta ^ 17 + 219900 * theta ^ 16 +
      409640 * theta ^ 15 + 684952 * theta ^ 14 + 904412 * theta ^ 13 +
      1216085 * theta ^ 12 + 1832744 * theta ^ 11 +
      2313426 * theta ^ 10 + 2385844 * theta ^ 9 +
      2710757 * theta ^ 8 + 3234232 * theta ^ 7 +
      2988694 * theta ^ 6 + 2285904 * theta ^ 5 +
      2011622 * theta ^ 4 + 1741264 * theta ^ 3 +
      1007696 * theta ^ 2 + 317812 * theta + 41609) * h

/-- The reciprocal monic equation for the first inverse. -/
theorem unitOneInverse_equation :
    unitOneInverseValue ^ 6 - unitOneInverseValue ^ 4 +
      2 * unitOneInverseValue ^ 3 - 2 * unitOneInverseValue + 1 = 0 := by
  have hu : unitOneValue ≠ 0 := by
    intro hz
    have hmul := unitOne_mul_inverse
    rw [hz, zero_mul] at hmul
    exact zero_ne_one hmul
  have hv : unitOneInverseValue = unitOneValue⁻¹ :=
    ((mul_eq_one_iff_inv_eq₀ hu).1 unitOne_mul_inverse).symm
  rw [hv]
  field_simp [hu]
  linear_combination unitOne_equation

/-- The reciprocal monic equation for the second inverse. -/
theorem unitTwoInverse_equation :
    unitTwoInverseValue ^ 6 + 2 * unitTwoInverseValue ^ 5 +
      4 * unitTwoInverseValue ^ 4 + 4 * unitTwoInverseValue ^ 3 +
      3 * unitTwoInverseValue ^ 2 + 2 * unitTwoInverseValue + 1 = 0 := by
  have hu : unitTwoValue ≠ 0 := by
    intro hz
    have hmul := unitTwo_mul_inverse
    rw [hz, zero_mul] at hmul
    exact zero_ne_one hmul
  have hv : unitTwoInverseValue = unitTwoValue⁻¹ :=
    ((mul_eq_one_iff_inv_eq₀ hu).1 unitTwo_mul_inverse).symm
  rw [hv]
  field_simp [hu]
  linear_combination unitTwo_equation

private def unitOnePolynomial : ℤ[X] :=
  X ^ 6 - 2 * X ^ 5 + 2 * X ^ 3 - X ^ 2 + 1

private def unitOneInversePolynomial : ℤ[X] :=
  X ^ 6 - X ^ 4 + 2 * X ^ 3 - 2 * X + 1

private def unitTwoPolynomial : ℤ[X] :=
  X ^ 6 + 2 * X ^ 5 + 3 * X ^ 4 + 4 * X ^ 3 +
    4 * X ^ 2 + 2 * X + 1

private def unitTwoInversePolynomial : ℤ[X] :=
  X ^ 6 + 2 * X ^ 5 + 4 * X ^ 4 + 4 * X ^ 3 +
    3 * X ^ 2 + 2 * X + 1

private theorem unitOnePolynomial_monic : unitOnePolynomial.Monic := by
  simp only [unitOnePolynomial]
  monicity!

private theorem unitOneInversePolynomial_monic : unitOneInversePolynomial.Monic := by
  simp only [unitOneInversePolynomial]
  monicity!

private theorem unitTwoPolynomial_monic : unitTwoPolynomial.Monic := by
  simp only [unitTwoPolynomial]
  monicity!

private theorem unitTwoInversePolynomial_monic : unitTwoInversePolynomial.Monic := by
  simp only [unitTwoInversePolynomial]
  monicity!

theorem unitOne_isIntegral : IsIntegral ℤ unitOneValue := by
  refine ⟨unitOnePolynomial, unitOnePolynomial_monic, ?_⟩
  simp only [unitOnePolynomial, eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_ofNat]
  norm_num
  exact unitOne_equation

theorem unitOneInverse_isIntegral : IsIntegral ℤ unitOneInverseValue := by
  refine ⟨unitOneInversePolynomial, unitOneInversePolynomial_monic, ?_⟩
  simp only [unitOneInversePolynomial, eval₂_sub, eval₂_add, eval₂_mul,
    eval₂_pow, eval₂_X, eval₂_ofNat]
  norm_num
  exact unitOneInverse_equation

theorem unitTwo_isIntegral : IsIntegral ℤ unitTwoValue := by
  refine ⟨unitTwoPolynomial, unitTwoPolynomial_monic, ?_⟩
  simp only [unitTwoPolynomial, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_ofNat]
  norm_num
  exact unitTwo_equation

theorem unitTwoInverse_isIntegral : IsIntegral ℤ unitTwoInverseValue := by
  refine ⟨unitTwoInversePolynomial, unitTwoInversePolynomial_monic, ?_⟩
  simp only [unitTwoInversePolynomial, eval₂_add, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_ofNat]
  norm_num
  exact unitTwoInverse_equation

/-- The first value, regarded as an algebraic integer. -/
def unitOneInteger : 𝓞 SexticField :=
  ⟨unitOneValue, unitOne_isIntegral⟩

/-- Its explicit inverse, regarded as an algebraic integer. -/
def unitOneInverseInteger : 𝓞 SexticField :=
  ⟨unitOneInverseValue, unitOneInverse_isIntegral⟩

/-- The second value, regarded as an algebraic integer. -/
def unitTwoInteger : 𝓞 SexticField :=
  ⟨unitTwoValue, unitTwo_isIntegral⟩

/-- Its explicit inverse, regarded as an algebraic integer. -/
def unitTwoInverseInteger : 𝓞 SexticField :=
  ⟨unitTwoInverseValue, unitTwoInverse_isIntegral⟩

private theorem unitOneInteger_mul_inverse :
    unitOneInteger * unitOneInverseInteger = 1 := by
  apply NumberField.RingOfIntegers.ext
  exact unitOne_mul_inverse

private theorem unitTwoInteger_mul_inverse :
    unitTwoInteger * unitTwoInverseInteger = 1 := by
  apply NumberField.RingOfIntegers.ext
  exact unitTwo_mul_inverse

/-- A checked unit of the full ring of integers of the sextic field. -/
def unitOne : (𝓞 SexticField)ˣ :=
  Units.mkOfMulEqOne unitOneInteger unitOneInverseInteger
    unitOneInteger_mul_inverse

/-- A second checked unit of the full ring of integers of the sextic field. -/
def unitTwo : (𝓞 SexticField)ˣ :=
  Units.mkOfMulEqOne unitTwoInteger unitTwoInverseInteger
    unitTwoInteger_mul_inverse

@[simp] theorem unitOne_coe : (unitOne : 𝓞 SexticField) = unitOneInteger := rfl

@[simp] theorem unitTwo_coe : (unitTwo : 𝓞 SexticField) = unitTwoInteger := rfl

end

end MazurTorsion.XOneThirteenTwoDescentUnits
