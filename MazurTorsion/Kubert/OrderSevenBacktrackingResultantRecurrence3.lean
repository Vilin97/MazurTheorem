/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence3DenseBridge
import Mathlib.Tactic.LinearCombination

/-!
# The third order-seven resultant recurrence

This module transports the checked dense integer residuals back to the
coefficient-polynomial ring and assembles the missing quintic/quartic
pseudo-division identity.
-/

public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

namespace IntegerDenseCertificate

private theorem unscale_dense_identity
    (left main error : Coefficient)
    (hscaled :
      C (85566736552441 : ℚ) * left =
        C (85566736552441 : ℚ) * main + error) :
    left = main + C ((1 : ℚ) / 85566736552441) * error := by
  have hunit :
      (C ((1 : ℚ) / 85566736552441) : Coefficient) *
          C (85566736552441 : ℚ) = 1 := by
    rw [← map_mul]
    norm_num
  calc
    left = C ((1 : ℚ) / 85566736552441) *
        (C (85566736552441 : ℚ) * left) := by
      rw [← mul_assoc, hunit, one_mul]
    _ = C ((1 : ℚ) / 85566736552441) *
        (C (85566736552441 : ℚ) * main + error) := by rw [hscaled]
    _ = main + C ((1 : ℚ) / 85566736552441) * error := by
      rw [mul_add, ← mul_assoc, hunit, one_mul]

theorem scalarResidual3Coefficient0 :
    remainder4Coefficient4 ^ 2 * remainder3Coefficient0 =
      remainder4Coefficient0 *
          (remainder4Coefficient4 * remainder3Coefficient4 -
            remainder4Coefficient3 * remainder3Coefficient5) +
        remainder3Coefficient5 ^ 2 * exceptional3 *
          remainder5Coefficient0 := by
  have hscaled := congrArg toPolynomial scalar0_scaled_checked
  unfold scalar0ScaledLeft scalar0ScaledRight at hscaled
  simp only [toPolynomial_scale, toPolynomial_mul, toPolynomial_add] at hscaled
  rw [toPolynomial_b4Square, toPolynomial_a0, toPolynomial_b0,
    toPolynomial_quotientConstant,
    toPolynomial_exceptionalProductNumerator, toPolynomial_c0] at hscaled
  norm_num at hscaled
  unfold exceptional3 exceptionalUnit3
  norm_num
  have hunit :
      (C ((1 : ℚ) / 85566736552441) : Coefficient) *
          C (85566736552441 : ℚ) = 1 := by
    rw [← map_mul]
    norm_num
  calc
    remainder4Coefficient4 ^ 2 * remainder3Coefficient0 =
        C ((1 : ℚ) / 85566736552441) *
          (C (85566736552441 : ℚ) *
            (remainder4Coefficient4 ^ 2 * remainder3Coefficient0)) := by
      rw [← mul_assoc, hunit, one_mul]
    _ = C ((1 : ℚ) / 85566736552441) *
          (C (85566736552441 : ℚ) *
              (remainder4Coefficient0 *
                (remainder4Coefficient4 * remainder3Coefficient4 -
                  remainder4Coefficient3 * remainder3Coefficient5)) +
            remainder3Coefficient5 ^ 2 * discriminantFactor ^ 22 *
              remainder5Coefficient0) := by rw [hscaled]
    _ = remainder4Coefficient0 *
            (remainder4Coefficient4 * remainder3Coefficient4 -
              remainder4Coefficient3 * remainder3Coefficient5) +
          remainder3Coefficient5 ^ 2 *
              (C ((1 : ℚ) / 85566736552441) *
                discriminantFactor ^ 22) *
            remainder5Coefficient0 := by
      rw [mul_add, ← mul_assoc, hunit, one_mul]
      ring

theorem scalarResidual3Coefficient1 :
    remainder4Coefficient4 ^ 2 * remainder3Coefficient1 =
      remainder4Coefficient0 *
          (remainder4Coefficient4 * remainder3Coefficient5) +
        remainder4Coefficient1 *
          (remainder4Coefficient4 * remainder3Coefficient4 -
            remainder4Coefficient3 * remainder3Coefficient5) +
        remainder3Coefficient5 ^ 2 * exceptional3 *
          remainder5Coefficient1 := by
  have hscaled := congrArg toPolynomial scalar1_scaled_checked
  unfold scalar1ScaledLeft scalar1ScaledRight at hscaled
  simp only [toPolynomial_scale, toPolynomial_mul, toPolynomial_add] at hscaled
  rw [toPolynomial_b4Square, toPolynomial_a1, toPolynomial_b0,
    toPolynomial_quotientLinear, toPolynomial_b1,
    toPolynomial_quotientConstant,
    toPolynomial_exceptionalProductNumerator, toPolynomial_c1] at hscaled
  norm_num at hscaled
  have hscaled' :
      C (85566736552441 : ℚ) *
          (remainder4Coefficient4 ^ 2 * remainder3Coefficient1) =
        C (85566736552441 : ℚ) *
            (remainder4Coefficient0 *
                (remainder4Coefficient4 * remainder3Coefficient5) +
              remainder4Coefficient1 *
                (remainder4Coefficient4 * remainder3Coefficient4 -
                  remainder4Coefficient3 * remainder3Coefficient5)) +
          remainder3Coefficient5 ^ 2 * discriminantFactor ^ 22 *
            remainder5Coefficient1 := by
    linear_combination hscaled
  have hunscaled := unscale_dense_identity _ _ _ hscaled'
  unfold exceptional3 exceptionalUnit3
  norm_num
  calc
    remainder4Coefficient4 ^ 2 * remainder3Coefficient1 =
        remainder4Coefficient0 *
            (remainder4Coefficient4 * remainder3Coefficient5) +
          remainder4Coefficient1 *
            (remainder4Coefficient4 * remainder3Coefficient4 -
              remainder4Coefficient3 * remainder3Coefficient5) +
          C ((1 : ℚ) / 85566736552441) *
            (remainder3Coefficient5 ^ 2 * discriminantFactor ^ 22 *
              remainder5Coefficient1) := hunscaled
    _ = remainder4Coefficient0 *
            (remainder4Coefficient4 * remainder3Coefficient5) +
          remainder4Coefficient1 *
            (remainder4Coefficient4 * remainder3Coefficient4 -
              remainder4Coefficient3 * remainder3Coefficient5) +
          remainder3Coefficient5 ^ 2 *
              (C ((1 : ℚ) / 85566736552441) * discriminantFactor ^ 22) *
            remainder5Coefficient1 := by ring

theorem scalarResidual3Coefficient2 :
    remainder4Coefficient4 ^ 2 * remainder3Coefficient2 =
      remainder4Coefficient1 *
          (remainder4Coefficient4 * remainder3Coefficient5) +
        remainder4Coefficient2 *
          (remainder4Coefficient4 * remainder3Coefficient4 -
            remainder4Coefficient3 * remainder3Coefficient5) +
        remainder3Coefficient5 ^ 2 * exceptional3 *
          remainder5Coefficient2 := by
  have hscaled := congrArg toPolynomial scalar2_scaled_checked
  unfold scalar2ScaledLeft scalar2ScaledRight at hscaled
  simp only [toPolynomial_scale, toPolynomial_mul, toPolynomial_add] at hscaled
  rw [toPolynomial_b4Square, toPolynomial_a2, toPolynomial_b1,
    toPolynomial_quotientLinear, toPolynomial_b2,
    toPolynomial_quotientConstant,
    toPolynomial_exceptionalProductNumerator, toPolynomial_c2] at hscaled
  norm_num at hscaled
  have hscaled' :
      C (85566736552441 : ℚ) *
          (remainder4Coefficient4 ^ 2 * remainder3Coefficient2) =
        C (85566736552441 : ℚ) *
            (remainder4Coefficient1 *
                (remainder4Coefficient4 * remainder3Coefficient5) +
              remainder4Coefficient2 *
                (remainder4Coefficient4 * remainder3Coefficient4 -
                  remainder4Coefficient3 * remainder3Coefficient5)) +
          remainder3Coefficient5 ^ 2 * discriminantFactor ^ 22 *
            remainder5Coefficient2 := by
    linear_combination hscaled
  have hunscaled := unscale_dense_identity _ _ _ hscaled'
  unfold exceptional3 exceptionalUnit3
  norm_num
  calc
    remainder4Coefficient4 ^ 2 * remainder3Coefficient2 =
        remainder4Coefficient1 *
            (remainder4Coefficient4 * remainder3Coefficient5) +
          remainder4Coefficient2 *
            (remainder4Coefficient4 * remainder3Coefficient4 -
              remainder4Coefficient3 * remainder3Coefficient5) +
          C ((1 : ℚ) / 85566736552441) *
            (remainder3Coefficient5 ^ 2 * discriminantFactor ^ 22 *
              remainder5Coefficient2) := hunscaled
    _ = remainder4Coefficient1 *
            (remainder4Coefficient4 * remainder3Coefficient5) +
          remainder4Coefficient2 *
            (remainder4Coefficient4 * remainder3Coefficient4 -
              remainder4Coefficient3 * remainder3Coefficient5) +
          remainder3Coefficient5 ^ 2 *
              (C ((1 : ℚ) / 85566736552441) * discriminantFactor ^ 22) *
            remainder5Coefficient2 := by ring

theorem scalarResidual3Coefficient3 :
    remainder4Coefficient4 ^ 2 * remainder3Coefficient3 =
      remainder4Coefficient2 *
          (remainder4Coefficient4 * remainder3Coefficient5) +
        remainder4Coefficient3 *
          (remainder4Coefficient4 * remainder3Coefficient4 -
            remainder4Coefficient3 * remainder3Coefficient5) +
        remainder3Coefficient5 ^ 2 * exceptional3 *
          remainder5Coefficient3 := by
  have hscaled := congrArg toPolynomial scalar3_scaled_checked
  unfold scalar3ScaledLeft scalar3ScaledRight at hscaled
  simp only [toPolynomial_scale, toPolynomial_mul, toPolynomial_add] at hscaled
  rw [toPolynomial_b4Square, toPolynomial_a3, toPolynomial_b2,
    toPolynomial_quotientLinear, toPolynomial_b3,
    toPolynomial_quotientConstant,
    toPolynomial_exceptionalProductNumerator, toPolynomial_c3] at hscaled
  norm_num at hscaled
  have hscaled' :
      C (85566736552441 : ℚ) *
          (remainder4Coefficient4 ^ 2 * remainder3Coefficient3) =
        C (85566736552441 : ℚ) *
            (remainder4Coefficient2 *
                (remainder4Coefficient4 * remainder3Coefficient5) +
              remainder4Coefficient3 *
                (remainder4Coefficient4 * remainder3Coefficient4 -
                  remainder4Coefficient3 * remainder3Coefficient5)) +
          remainder3Coefficient5 ^ 2 * discriminantFactor ^ 22 *
            remainder5Coefficient3 := by
    linear_combination hscaled
  have hunscaled := unscale_dense_identity _ _ _ hscaled'
  unfold exceptional3 exceptionalUnit3
  norm_num
  calc
    remainder4Coefficient4 ^ 2 * remainder3Coefficient3 =
        remainder4Coefficient2 *
            (remainder4Coefficient4 * remainder3Coefficient5) +
          remainder4Coefficient3 *
            (remainder4Coefficient4 * remainder3Coefficient4 -
              remainder4Coefficient3 * remainder3Coefficient5) +
          C ((1 : ℚ) / 85566736552441) *
            (remainder3Coefficient5 ^ 2 * discriminantFactor ^ 22 *
              remainder5Coefficient3) := hunscaled
    _ = remainder4Coefficient2 *
            (remainder4Coefficient4 * remainder3Coefficient5) +
          remainder4Coefficient3 *
            (remainder4Coefficient4 * remainder3Coefficient4 -
              remainder4Coefficient3 * remainder3Coefficient5) +
          remainder3Coefficient5 ^ 2 *
              (C ((1 : ℚ) / 85566736552441) * discriminantFactor ^ 22) *
            remainder5Coefficient3 := by ring

end IntegerDenseCertificate

open IntegerDenseCertificate

private def quintic
    (a0 a1 a2 a3 a4 a5 : Coefficient) : Bivariate :=
  C a5 * X ^ 5 + C a4 * X ^ 4 + C a3 * X ^ 3 +
    C a2 * X ^ 2 + C a1 * X + C a0

private def quartic
    (b0 b1 b2 b3 b4 : Coefficient) : Bivariate :=
  C b4 * X ^ 4 + C b3 * X ^ 3 + C b2 * X ^ 2 +
    C b1 * X + C b0

private def cubic
    (c0 c1 c2 c3 : Coefficient) : Bivariate :=
  C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

private def quotientDerived
    (a4 a5 b3 b4 : Coefficient) : Bivariate :=
  C (b4 * a5) * X + C (b4 * a4 - b3 * a5)

private theorem quintic_quartic_pseudodivision
    (a0 a1 a2 a3 a4 a5 : Coefficient)
    (b0 b1 b2 b3 b4 : Coefficient)
    (c0 c1 c2 c3 exceptional : Coefficient)
    (residual0 : b4 ^ 2 * a0 =
      b0 * (b4 * a4 - b3 * a5) + a5 ^ 2 * exceptional * c0)
    (residual1 : b4 ^ 2 * a1 =
      b0 * (b4 * a5) + b1 * (b4 * a4 - b3 * a5) +
        a5 ^ 2 * exceptional * c1)
    (residual2 : b4 ^ 2 * a2 =
      b1 * (b4 * a5) + b2 * (b4 * a4 - b3 * a5) +
        a5 ^ 2 * exceptional * c2)
    (residual3 : b4 ^ 2 * a3 =
      b2 * (b4 * a5) + b3 * (b4 * a4 - b3 * a5) +
        a5 ^ 2 * exceptional * c3) :
    C (b4 ^ 2) * quintic a0 a1 a2 a3 a4 a5 =
      quartic b0 b1 b2 b3 b4 * quotientDerived a4 a5 b3 b4 +
        C (a5 ^ 2 * exceptional) * cubic c0 c1 c2 c3 := by
  unfold quintic quartic cubic quotientDerived
  have mapped0 := congrArg C residual0
  have mapped1 := congrArg C residual1
  have mapped2 := congrArg C residual2
  have mapped3 := congrArg C residual3
  simp only [map_mul, map_pow, map_add, map_sub] at mapped0 mapped1 mapped2 mapped3
  simp only [map_mul, map_pow, map_sub]
  linear_combination mapped0 + mapped1 * X + mapped2 * X ^ 2 +
    mapped3 * X ^ 3

private theorem remainder3_coefficient0 :
    remainder3.coeff 0 = remainder3Coefficient0 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient1 :
    remainder3.coeff 1 = remainder3Coefficient1 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient2 :
    remainder3.coeff 2 = remainder3Coefficient2 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient3 :
    remainder3.coeff 3 = remainder3Coefficient3 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient4 :
    remainder3.coeff 4 = remainder3Coefficient4 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder3_coefficient5 :
    remainder3.coeff 5 = remainder3Coefficient5 := by
  unfold remainder3 outerTerm
  simp

private theorem remainder4_coefficient0 :
    remainder4.coeff 0 = remainder4Coefficient0 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder4_coefficient1 :
    remainder4.coeff 1 = remainder4Coefficient1 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder4_coefficient2 :
    remainder4.coeff 2 = remainder4Coefficient2 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder4_coefficient3 :
    remainder4.coeff 3 = remainder4Coefficient3 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder4_coefficient4 :
    remainder4.coeff 4 = remainder4Coefficient4 := by
  unfold remainder4 outerTerm
  simp

private theorem remainder5_coefficient0 :
    remainder5.coeff 0 = remainder5Coefficient0 := by
  unfold remainder5 outerTerm
  simp

private theorem remainder5_coefficient1 :
    remainder5.coeff 1 = remainder5Coefficient1 := by
  unfold remainder5 outerTerm
  simp

private theorem remainder5_coefficient2 :
    remainder5.coeff 2 = remainder5Coefficient2 := by
  unfold remainder5 outerTerm
  simp

private theorem remainder5_coefficient3 :
    remainder5.coeff 3 = remainder5Coefficient3 := by
  unfold remainder5 outerTerm
  simp

/-- The checked dense residuals establish the third pseudo-division recurrence. -/
theorem recurrence3_checked : recurrence3 := by
  have division := quintic_quartic_pseudodivision
    remainder3Coefficient0 remainder3Coefficient1
    remainder3Coefficient2 remainder3Coefficient3
    remainder3Coefficient4 remainder3Coefficient5
    remainder4Coefficient0 remainder4Coefficient1
    remainder4Coefficient2 remainder4Coefficient3
    remainder4Coefficient4 remainder5Coefficient0
    remainder5Coefficient1 remainder5Coefficient2
    remainder5Coefficient3 exceptional3
    scalarResidual3Coefficient0 scalarResidual3Coefficient1
    scalarResidual3Coefficient2 scalarResidual3Coefficient3
  unfold recurrence3
  rw [remainder4_coefficient4, remainder3_coefficient5]
  unfold quotient3 linearPseudoQuotient
  rw [remainder3_coefficient4, remainder3_coefficient5]
  rw [remainder4_coefficient3, remainder4_coefficient4]
  unfold outerTerm
  unfold quintic quartic cubic quotientDerived at division
  unfold remainder3 remainder4 remainder5 outerTerm
  linear_combination division

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
