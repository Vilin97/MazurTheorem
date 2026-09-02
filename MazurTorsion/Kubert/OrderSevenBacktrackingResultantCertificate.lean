/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.Polynomial.BoundedResultant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantFactors
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2Lookup
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4Lookup
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5Lookup
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

/-!
# Generic resultant certificate for order-seven backtracking

This file checks the degree and leading-coefficient side conditions
for the primitive pseudo-remainder sequence and telescopes its seven
recurrences to the factored generic resultant. The recurrence proofs
are separate exact-arithmetic certificate shards.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open MazurTorsion.PolynomialResultant

namespace Internal.ResultantCertificate

private lemma remainder1_degree : remainder1.natDegree ≤ 7 := by
  simpa [remainder1] using divisionCofactorData0_degree

private lemma remainder2_degree :
    remainder2.natDegree ≤ 6 := by
  unfold remainder2 outerTerm
  compute_degree

private lemma remainder3_degree :
    remainder3.natDegree ≤ 5 := by
  unfold remainder3 outerTerm
  compute_degree

private lemma remainder4_degree :
    remainder4.natDegree ≤ 4 := by
  unfold remainder4 outerTerm
  compute_degree

private lemma remainder5_degree :
    remainder5.natDegree ≤ 3 := by
  unfold remainder5 outerTerm
  compute_degree

private lemma remainder6_degree :
    remainder6.natDegree ≤ 2 := by
  unfold remainder6 outerTerm
  compute_degree

private lemma remainder7_degree :
    remainder7.natDegree ≤ 1 := by
  unfold remainder7 outerTerm
  compute_degree

private lemma remainder8_degree :
    remainder8.natDegree ≤ 0 := by
  unfold remainder8 outerTerm
  compute_degree

private lemma quotient0_degree :
    quotient0.natDegree ≤ 26 := by
  unfold quotient0 outerTerm
  compute_degree

private lemma quotient1_degree :
    quotient1.natDegree ≤ 1 := by
  unfold quotient1 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient2_degree :
    quotient2.natDegree ≤ 1 := by
  unfold quotient2 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient3_degree :
    quotient3.natDegree ≤ 1 := by
  unfold quotient3 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient4_degree :
    quotient4.natDegree ≤ 1 := by
  unfold quotient4 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient5_degree :
    quotient5.natDegree ≤ 1 := by
  unfold quotient5 linearPseudoQuotient outerTerm
  compute_degree

private lemma quotient6_degree :
    quotient6.natDegree ≤ 1 := by
  unfold quotient6 linearPseudoQuotient outerTerm
  compute_degree

private lemma remainder1_coeff_seven : remainder1.coeff 7 = 1 := by
  simp [remainder1]

private lemma remainder2Coefficient6Block0_topCoefficient :
    (remainder2Coefficient6Block0.coeff 95) =
      (-((1 : ℚ))) := by
  norm_num [remainder2Coefficient6Block0, remainder2Coefficient6Chunk0,
    remainder2Coefficient6Chunk1, remainder2Coefficient6Chunk2,
    remainder2Coefficient6Chunk3, remainder2Coefficient6Chunk4,
    remainder2Coefficient6Chunk5, remainder2Coefficient6Chunk6,
    remainder2Coefficient6Chunk7, remainder2Coefficient6Chunk8,
    remainder2Coefficient6Chunk9, remainder2Coefficient6Chunk10,
    remainder2Coefficient6Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder2Coefficient6_topCoefficient :
    (remainder2Coefficient6.coeff 95) =
      (-((1 : ℚ))) := by
  simp [remainder2Coefficient6,
    remainder2Coefficient6Block0_topCoefficient]

private lemma remainder2_leadingCoeff_ne_zero :
    remainder2.coeff 6 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder2Coefficient6 = 0 := by
    simpa [remainder2, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 95)
    hcoefficient
  rw [remainder2Coefficient6_topCoefficient] at htop
  norm_num at htop

private lemma remainder3Coefficient5Block0_topCoefficient :
    (remainder3Coefficient5Block0.coeff 134) =
      (-((9250229 : ℚ))) := by
  norm_num [remainder3Coefficient5Block0, remainder3Coefficient5Chunk0,
    remainder3Coefficient5Chunk1, remainder3Coefficient5Chunk2,
    remainder3Coefficient5Chunk3, remainder3Coefficient5Chunk4,
    remainder3Coefficient5Chunk5, remainder3Coefficient5Chunk6,
    remainder3Coefficient5Chunk7, remainder3Coefficient5Chunk8,
    remainder3Coefficient5Chunk9, remainder3Coefficient5Chunk10,
    remainder3Coefficient5Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder3Coefficient5Block1_topCoefficient :
    (remainder3Coefficient5Block1.coeff 134) =
      (0 : ℚ) := by
  norm_num [remainder3Coefficient5Block1, remainder3Coefficient5Chunk12,
    remainder3Coefficient5Chunk13, remainder3Coefficient5Chunk14,
    remainder3Coefficient5Chunk15, remainder3Coefficient5Chunk16,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder3Coefficient5_topCoefficient :
    (remainder3Coefficient5.coeff 134) =
      (-((9250229 : ℚ))) := by
  simp [remainder3Coefficient5,
    remainder3Coefficient5Block0_topCoefficient,
    remainder3Coefficient5Block1_topCoefficient]

private lemma remainder3_leadingCoeff_ne_zero :
    remainder3.coeff 5 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder3Coefficient5 = 0 := by
    simpa [remainder3, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 134)
    hcoefficient
  rw [remainder3Coefficient5_topCoefficient] at htop
  norm_num at htop

private lemma remainder4Coefficient4Block0_topCoefficient :
    (remainder4Coefficient4Block0.coeff 178) =
      (-((152365481437 : ℚ))) := by
  norm_num [remainder4Coefficient4Block0, remainder4Coefficient4Chunk0,
    remainder4Coefficient4Chunk1, remainder4Coefficient4Chunk2,
    remainder4Coefficient4Chunk3, remainder4Coefficient4Chunk4,
    remainder4Coefficient4Chunk5, remainder4Coefficient4Chunk6,
    remainder4Coefficient4Chunk7, remainder4Coefficient4Chunk8,
    remainder4Coefficient4Chunk9, remainder4Coefficient4Chunk10,
    remainder4Coefficient4Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder4Coefficient4Block1_topCoefficient :
    (remainder4Coefficient4Block1.coeff 178) =
      (0 : ℚ) := by
  norm_num [remainder4Coefficient4Block1, remainder4Coefficient4Chunk12,
    remainder4Coefficient4Chunk13, remainder4Coefficient4Chunk14,
    remainder4Coefficient4Chunk15, remainder4Coefficient4Chunk16,
    remainder4Coefficient4Chunk17, remainder4Coefficient4Chunk18,
    remainder4Coefficient4Chunk19, remainder4Coefficient4Chunk20,
    remainder4Coefficient4Chunk21, remainder4Coefficient4Chunk22,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder4Coefficient4_topCoefficient :
    (remainder4Coefficient4.coeff 178) =
      (-((152365481437 : ℚ))) := by
  simp [remainder4Coefficient4,
    remainder4Coefficient4Block0_topCoefficient,
    remainder4Coefficient4Block1_topCoefficient]

private lemma remainder4_leadingCoeff_ne_zero :
    remainder4.coeff 4 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder4Coefficient4 = 0 := by
    simpa [remainder4, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 178)
    hcoefficient
  rw [remainder4Coefficient4_topCoefficient] at htop
  norm_num at htop

private lemma remainder5Coefficient3Block0_topCoefficient :
    (remainder5Coefficient3Block0.coeff 164) =
      (-((447151549834258283177195510 : ℚ))) := by
  norm_num [remainder5Coefficient3Block0, remainder5Coefficient3Chunk0,
    remainder5Coefficient3Chunk1, remainder5Coefficient3Chunk2,
    remainder5Coefficient3Chunk3, remainder5Coefficient3Chunk4,
    remainder5Coefficient3Chunk5, remainder5Coefficient3Chunk6,
    remainder5Coefficient3Chunk7, remainder5Coefficient3Chunk8,
    remainder5Coefficient3Chunk9, remainder5Coefficient3Chunk10,
    remainder5Coefficient3Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder5Coefficient3Block1_topCoefficient :
    (remainder5Coefficient3Block1.coeff 164) =
      (0 : ℚ) := by
  norm_num [remainder5Coefficient3Block1, remainder5Coefficient3Chunk12,
    remainder5Coefficient3Chunk13, remainder5Coefficient3Chunk14,
    remainder5Coefficient3Chunk15, remainder5Coefficient3Chunk16,
    remainder5Coefficient3Chunk17, remainder5Coefficient3Chunk18,
    remainder5Coefficient3Chunk19, remainder5Coefficient3Chunk20,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder5Coefficient3_topCoefficient :
    (remainder5Coefficient3.coeff 164) =
      (-((447151549834258283177195510 : ℚ))) := by
  simp [remainder5Coefficient3,
    remainder5Coefficient3Block0_topCoefficient,
    remainder5Coefficient3Block1_topCoefficient]

private lemma remainder5_leadingCoeff_ne_zero :
    remainder5.coeff 3 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder5Coefficient3 = 0 := by
    simpa [remainder5, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 164)
    hcoefficient
  rw [remainder5Coefficient3_topCoefficient] at htop
  norm_num at htop

private lemma remainder6Coefficient2Block0_topCoefficient :
    (remainder6Coefficient2Block0.coeff 145) =
      (-(((53701746906274322922389292 : ℚ) * 10 ^ 36 +
        413329009090012362832185396756764943))) := by
  norm_num [remainder6Coefficient2Block0, remainder6Coefficient2Chunk0,
    remainder6Coefficient2Chunk1, remainder6Coefficient2Chunk2,
    remainder6Coefficient2Chunk3, remainder6Coefficient2Chunk4,
    remainder6Coefficient2Chunk5, remainder6Coefficient2Chunk6,
    remainder6Coefficient2Chunk7, remainder6Coefficient2Chunk8,
    remainder6Coefficient2Chunk9, remainder6Coefficient2Chunk10,
    remainder6Coefficient2Chunk11, coefficientTerm,
    Polynomial.coeff_monomial]

private lemma remainder6Coefficient2Block1_topCoefficient :
    (remainder6Coefficient2Block1.coeff 145) =
      (0 : ℚ) := by
  norm_num [remainder6Coefficient2Block1, remainder6Coefficient2Chunk12,
    remainder6Coefficient2Chunk13, remainder6Coefficient2Chunk14,
    remainder6Coefficient2Chunk15, remainder6Coefficient2Chunk16,
    remainder6Coefficient2Chunk17, remainder6Coefficient2Chunk18,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder6Coefficient2_topCoefficient :
    (remainder6Coefficient2.coeff 145) =
      (-(((53701746906274322922389292 : ℚ) * 10 ^ 36 +
        413329009090012362832185396756764943))) := by
  simp [remainder6Coefficient2,
    remainder6Coefficient2Block0_topCoefficient,
    remainder6Coefficient2Block1_topCoefficient]

private lemma remainder6_leadingCoeff_ne_zero :
    remainder6.coeff 2 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder6Coefficient2 = 0 := by
    simpa [remainder6, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 145)
    hcoefficient
  rw [remainder6Coefficient2_topCoefficient] at htop
  norm_num at htop

private lemma remainder7Coefficient1Block0_topCoefficient :
    (remainder7Coefficient1Block0.coeff 84) =
      (-((((((1557 : ℚ) * 10 ^ 36 +
        411197222661268025367413836777879542) * 10 ^ 36 +
        082863389056330876674739520938317083) * 10 ^ 36 +
        162921568205678358405098446864079426) * 10 ^ 36 +
        408781113703694420237088677512308100))) := by
  norm_num [remainder7Coefficient1Block0, remainder7Coefficient1Chunk0,
    remainder7Coefficient1Chunk1, remainder7Coefficient1Chunk2,
    remainder7Coefficient1Chunk3, remainder7Coefficient1Chunk4,
    remainder7Coefficient1Chunk5, remainder7Coefficient1Chunk6,
    remainder7Coefficient1Chunk7, remainder7Coefficient1Chunk8,
    remainder7Coefficient1Chunk9, remainder7Coefficient1Chunk10,
    coefficientTerm, Polynomial.coeff_monomial]

private lemma remainder7Coefficient1_topCoefficient :
    (remainder7Coefficient1.coeff 84) =
      (-((((((1557 : ℚ) * 10 ^ 36 +
        411197222661268025367413836777879542) * 10 ^ 36 +
        082863389056330876674739520938317083) * 10 ^ 36 +
        162921568205678358405098446864079426) * 10 ^ 36 +
        408781113703694420237088677512308100))) := by
  simp [remainder7Coefficient1,
    remainder7Coefficient1Block0_topCoefficient]

private lemma remainder7_leadingCoeff_ne_zero :
    remainder7.coeff 1 ≠ 0 := by
  intro hzero
  have hcoefficient : remainder7Coefficient1 = 0 := by
    simpa [remainder7, outerTerm] using hzero
  have htop := congrArg
    (fun p : Coefficient ↦ p.coeff 84)
    hcoefficient
  rw [remainder7Coefficient1_topCoefficient] at htop
  norm_num at htop

private lemma remainder8_eq : remainder8 = C (-1) := by
  norm_num [remainder8, remainder8Coefficient0,
    remainder8Coefficient0Block0, remainder8Coefficient0Chunk0,
    outerTerm, coefficientTerm]

private theorem cmSix_eq_resultantFactorSix :
    cmSix = resultantFactorSix.map (Int.castRingHom ℚ) := by
  simp [cmSix, resultantFactorSix, parameter]

private theorem cmTwelve_eq_resultantFactorTwelve :
    cmTwelve = resultantFactorTwelve.map (Int.castRingHom ℚ) := by
  simp [cmTwelve, resultantFactorTwelve, parameter]

private theorem exceptional_monomial_identity
    {M : Type} [CommMonoid M]
    (a b q c6 c12 u3 u4 u5 u6 : M)
    (hunit : u3 ^ 4 * u4 ^ 3 * u5 ^ 2 * u6 = 1) :
    ((b ^ 6 * a ^ 7) ^ 7) * (q ^ 21) ^ 6 *
      (b * a ^ 2) ^ 5 * (u3 * q ^ 22) ^ 4 *
      (u4 * b * q ^ 4) ^ 3 * (u5 * a ^ 2 * q ^ 14 * c6) ^ 2 *
      (u6 * b * q ^ 6 * c12) =
        a ^ 63 * b ^ 51 * q ^ 260 * c6 ^ 2 * c12 := by
  have ha : a ^ 63 = a ^ 49 * a ^ 10 * a ^ 4 := by
    rw [show 63 = 49 + 10 + 4 by omega, pow_add, pow_add]
  have hb : b ^ 51 = b ^ 42 * b ^ 5 * b ^ 3 * b := by
    rw [show 51 = 42 + 5 + 3 + 1 by omega,
      pow_add, pow_add, pow_add, pow_one]
  have hq : q ^ 260 = q ^ 126 * q ^ 88 * q ^ 12 * q ^ 28 *
      q ^ 6 := by
    rw [show 260 = 126 + 88 + 12 + 28 + 6 by omega,
      pow_add, pow_add, pow_add, pow_add]
  calc
    _ = (u3 ^ 4 * u4 ^ 3 * u5 ^ 2 * u6) *
        (a ^ 49 * a ^ 10 * a ^ 4) *
        (b ^ 42 * b ^ 5 * b ^ 3 * b) *
        (q ^ 126 * q ^ 88 * q ^ 12 * q ^ 28 * q ^ 6) *
        c6 ^ 2 * c12 := by
      simp only [mul_pow]
      repeat rw [← pow_mul]
      norm_num
      ac_rfl
    _ = _ := by rw [hunit, ha, hb, hq]; ac_rfl

private theorem factored_expression_eq_resultantFactorData :
    parameter ^ 63 * (parameter - 1) ^ 51 *
      discriminantFactor ^ 260 * cmSix ^ 2 * cmTwelve =
      resultantFactorData := by
  have hp : parameter = X := rfl
  have h8 : (8 : Coefficient) = C 8 := rfl
  have h5 : (5 : Coefficient) = C 5 := rfl
  have hd : discriminantFactor =
      X ^ 3 - C 8 * X ^ 2 + C 5 * X + 1 := by
    rw [discriminantFactor, hp, h8, h5]
  unfold resultantFactorData
  rw [← cmSix_eq_resultantFactorSix,
    ← cmTwelve_eq_resultantFactorTwelve, hp, hd]

private theorem exceptional_product_eq_resultantFactorData :
    exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
      exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
      exceptional6 = resultantFactorData := by
  have hunit : exceptionalUnit3 ^ 4 * exceptionalUnit4 ^ 3 *
      exceptionalUnit5 ^ 2 * exceptionalUnit6 = 1 := by
    unfold exceptionalUnit3 exceptionalUnit4 exceptionalUnit5
      exceptionalUnit6
    rw [← map_pow, ← map_pow, ← map_pow,
      ← map_mul, ← map_mul, ← map_mul]
    norm_num
  have hmonomial := exceptional_monomial_identity
    parameter (parameter - 1) discriminantFactor cmSix cmTwelve
    exceptionalUnit3 exceptionalUnit4 exceptionalUnit5
    exceptionalUnit6 hunit
  rw [← factored_expression_eq_resultantFactorData, ← hmonomial]
  unfold exceptional0 exceptional1 exceptional2 exceptional3
    exceptional4 exceptional5 exceptional6
  simp only [exceptionalUnit0, exceptionalUnit1, exceptionalUnit2,
    map_one, one_mul, pow_one]

end Internal.ResultantCertificate

open Internal.ResultantCertificate

/-- The seven checked pseudo-remainder recurrences imply the exact
factorization of the first bounded resultant over `ℚ[D]`. -/
theorem generic_resultant_eq_resultantFactorData :
    resultant selectionCofactorData divisionCofactorData0 33 7 =
      resultantFactorData := by
  have h := bounded_resultant_telescope_33_7
    remainder0 remainder1 remainder2 remainder3 remainder4
    remainder5 remainder6 remainder7 remainder8
    quotient0 quotient1 quotient2 quotient3 quotient4 quotient5 quotient6
    (remainder2.coeff 6) (remainder3.coeff 5)
    (remainder4.coeff 4) (remainder5.coeff 3)
    (remainder6.coeff 2) (remainder7.coeff 1)
    exceptional0 exceptional1 exceptional2 exceptional3
    exceptional4 exceptional5 exceptional6 (-1)
    remainder1_degree remainder2_degree remainder3_degree
    remainder4_degree remainder5_degree remainder6_degree
    remainder7_degree remainder8_degree
    (by have := quotient0_degree; omega)
    (by have := quotient1_degree; omega)
    (by have := quotient2_degree; omega)
    (by have := quotient3_degree; omega)
    (by have := quotient4_degree; omega)
    (by have := quotient5_degree; omega)
    (by have := quotient6_degree; omega)
    remainder1_coeff_seven rfl rfl rfl rfl rfl rfl
    remainder2_leadingCoeff_ne_zero
    remainder3_leadingCoeff_ne_zero
    remainder4_leadingCoeff_ne_zero
    remainder5_leadingCoeff_ne_zero
    remainder6_leadingCoeff_ne_zero
    remainder7_leadingCoeff_ne_zero
    (by simpa only [recurrence0] using recurrence0_checked)
    (by simpa only [recurrence1] using recurrence1_checked)
    (by simpa only [recurrence2] using recurrence2_checked)
    (by simpa only [recurrence3] using recurrence3_checked)
    (by simpa only [recurrence4] using recurrence4_checked)
    (by simpa only [recurrence5] using recurrence5_checked)
    (by simpa only [recurrence6] using recurrence6_checked)
    remainder8_eq
  calc
    resultant selectionCofactorData divisionCofactorData0 33 7 =
        exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
          exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
          exceptional6 := by
      rw [← remainder0, ← remainder1]
      calc
        resultant remainder0 remainder1 33 7 =
            -exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
              exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
              exceptional6 * (-1) := h
        _ = exceptional0 ^ 7 * exceptional1 ^ 6 * exceptional2 ^ 5 *
              exceptional3 ^ 4 * exceptional4 ^ 3 * exceptional5 ^ 2 *
              exceptional6 := by ring
    _ = resultantFactorData := exceptional_product_eq_resultantFactorData

/-- Specializing the checked generic identity gives the first bounded
resultant without requiring the selection cofactor to preserve its degree. -/
theorem selection_divisionCofactor0_resultant_eq_resultantFactorData_eval
    (d : ℚ) :
    resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 =
      resultantFactorData.eval d := by
  change _ = (evalRingHom d) resultantFactorData
  have hgeneric := congrArg (evalRingHom d)
    generic_resultant_eq_resultantFactorData
  simpa only [selectionCofactor, divisionCofactor0,
    resultant_map_map] using hgeneric

/-- The first bounded resultant is nonzero at every nonsingular Kubert
parameter. -/
theorem selection_divisionCofactor0_resultant_ne_zero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0 := by
  rw [selection_divisionCofactor0_resultant_eq_resultantFactorData_eval
    d]
  exact resultantFactorData_eval_ne_zero d hd0 hd1 hcubic

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
