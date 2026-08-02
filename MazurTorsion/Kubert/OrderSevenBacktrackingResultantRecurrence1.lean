/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence1Inner
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: Terminal

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal

private lemma coeff_mul_linearPseudoQuotient_zero
    (dividend divisor : Bivariate)
    (dividendDegree divisorDegree : ℕ) :
    (divisor * linearPseudoQuotient
      dividend divisor dividendDegree divisorDegree).coeff 0 =
      divisor.coeff 0 *
        (divisor.coeff divisorDegree *
            dividend.coeff (dividendDegree - 1) -
          divisor.coeff (divisorDegree - 1) *
            dividend.coeff dividendDegree) := by
  unfold linearPseudoQuotient outerTerm
  rw [mul_add, coeff_add]
  simp [coeff_mul]

private lemma coeff_mul_linearPseudoQuotient_succ
    (dividend divisor : Bivariate)
    (dividendDegree divisorDegree n : ℕ) :
    (divisor * linearPseudoQuotient
      dividend divisor dividendDegree divisorDegree).coeff (n + 1) =
      divisor.coeff n *
          (divisor.coeff divisorDegree *
            dividend.coeff dividendDegree) +
        divisor.coeff (n + 1) *
          (divisor.coeff divisorDegree *
              dividend.coeff (dividendDegree - 1) -
            divisor.coeff (divisorDegree - 1) *
              dividend.coeff dividendDegree) := by
  unfold linearPseudoQuotient outerTerm
  rw [mul_add, coeff_add]
  simp only [pow_one, pow_zero, mul_one]
  rw [← mul_assoc divisor (C _) X, coeff_mul_X, coeff_mul_C]
  rw [coeff_mul_C]

private lemma source_coeff_0 :
    remainder1.coeff 0 = divisionCofactor0Coefficient0 := by
  simp [remainder1, divisionCofactorData0]

private lemma source_coeff_1 :
    remainder1.coeff 1 = divisionCofactor0Coefficient1 := by
  simp [remainder1, divisionCofactorData0]

private lemma source_coeff_2 :
    remainder1.coeff 2 = divisionCofactor0Coefficient2 := by
  simp [remainder1, divisionCofactorData0]

private lemma source_coeff_3 :
    remainder1.coeff 3 = divisionCofactor0Coefficient3 := by
  simp [remainder1, divisionCofactorData0]

private lemma source_coeff_4 :
    remainder1.coeff 4 = divisionCofactor0Coefficient4 := by
  simp [remainder1, divisionCofactorData0]

private lemma source_coeff_5 :
    remainder1.coeff 5 = divisionCofactor0Coefficient5 := by
  simp [remainder1, divisionCofactorData0]

private lemma source_coeff_6 :
    remainder1.coeff 6 = divisionCofactor0Coefficient6 := by
  simp [remainder1, divisionCofactorData0]

private lemma source_coeff_7 :
    remainder1.coeff 7 = divisionCofactor0Coefficient7 := by
  simp [remainder1, divisionCofactorData0]

private lemma remainder2_coeff_0 :
    remainder2.coeff 0 = remainder2Coefficient0 := by
  simp [remainder2, outerTerm]

private lemma remainder2_coeff_1 :
    remainder2.coeff 1 = remainder2Coefficient1 := by
  simp [remainder2, outerTerm]

private lemma remainder2_coeff_2 :
    remainder2.coeff 2 = remainder2Coefficient2 := by
  simp [remainder2, outerTerm]

private lemma remainder2_coeff_3 :
    remainder2.coeff 3 = remainder2Coefficient3 := by
  simp [remainder2, outerTerm]

private lemma remainder2_coeff_4 :
    remainder2.coeff 4 = remainder2Coefficient4 := by
  simp [remainder2, outerTerm]

private lemma remainder2_coeff_5 :
    remainder2.coeff 5 = remainder2Coefficient5 := by
  simp [remainder2, outerTerm]

private lemma remainder2_coeff_6 :
    remainder2.coeff 6 = remainder2Coefficient6 := by
  simp [remainder2, outerTerm]

private lemma remainder2_coeff_7 : remainder2.coeff 7 = 0 := by
  simp [remainder2, outerTerm]

private lemma remainder3_coeff_0 :
    remainder3.coeff 0 = remainder3Coefficient0 := by
  simp [remainder3, outerTerm]

private lemma remainder3_coeff_1 :
    remainder3.coeff 1 = remainder3Coefficient1 := by
  simp [remainder3, outerTerm]

private lemma remainder3_coeff_2 :
    remainder3.coeff 2 = remainder3Coefficient2 := by
  simp [remainder3, outerTerm]

private lemma remainder3_coeff_3 :
    remainder3.coeff 3 = remainder3Coefficient3 := by
  simp [remainder3, outerTerm]

private lemma remainder3_coeff_4 :
    remainder3.coeff 4 = remainder3Coefficient4 := by
  simp [remainder3, outerTerm]

private lemma remainder3_coeff_5 :
    remainder3.coeff 5 = remainder3Coefficient5 := by
  simp [remainder3, outerTerm]

private lemma remainder3_coeff_6 :
    remainder3.coeff 6 = 0 := by
  simp [remainder3, outerTerm]

private lemma remainder3_coeff_7 :
    remainder3.coeff 7 = 0 := by
  simp [remainder3, outerTerm]

private lemma remainder1_degree : remainder1.natDegree ≤ 7 := by
  simpa [remainder1] using divisionCofactorData0_degree

private lemma remainder2_degree : remainder2.natDegree ≤ 6 := by
  unfold remainder2 outerTerm
  compute_degree

private lemma remainder3_degree : remainder3.natDegree ≤ 5 := by
  unfold remainder3 outerTerm
  compute_degree

private lemma quotient1_degree : quotient1.natDegree ≤ 1 := by
  unfold quotient1 linearPseudoQuotient outerTerm
  compute_degree

theorem recurrence1_checked : recurrence1 := by
  unfold recurrence1
  apply Polynomial.ext
  intro n
  by_cases h0 : n = 0
  · subst n
    rw [coeff_C_mul, coeff_add, quotient1,
      coeff_mul_linearPseudoQuotient_zero, coeff_C_mul]
    norm_num
    rw [source_coeff_0, source_coeff_6, source_coeff_7,
    remainder2_coeff_0, remainder2_coeff_5, remainder2_coeff_6,
    remainder3_coeff_0]
    exact recurrence1_inner_0
  by_cases h1 : n = 1
  · subst n
    rw [coeff_C_mul, coeff_add, quotient1,
      coeff_mul_linearPseudoQuotient_succ remainder1 remainder2 7 6 0, coeff_C_mul]
    norm_num
    rw [source_coeff_1, source_coeff_6, source_coeff_7,
    remainder2_coeff_1, remainder2_coeff_5, remainder2_coeff_6,
    remainder3_coeff_1, remainder2_coeff_0]
    exact recurrence1_inner_1
  by_cases h2 : n = 2
  · subst n
    rw [coeff_C_mul, coeff_add, quotient1,
      coeff_mul_linearPseudoQuotient_succ remainder1 remainder2 7 6 1, coeff_C_mul]
    norm_num
    rw [source_coeff_2, source_coeff_6, source_coeff_7,
    remainder2_coeff_2, remainder2_coeff_5, remainder2_coeff_6,
    remainder3_coeff_2, remainder2_coeff_1]
    exact recurrence1_inner_2
  by_cases h3 : n = 3
  · subst n
    rw [coeff_C_mul, coeff_add, quotient1,
      coeff_mul_linearPseudoQuotient_succ remainder1 remainder2 7 6 2, coeff_C_mul]
    norm_num
    rw [source_coeff_3, source_coeff_6, source_coeff_7,
    remainder2_coeff_3, remainder2_coeff_5, remainder2_coeff_6,
    remainder3_coeff_3, remainder2_coeff_2]
    exact recurrence1_inner_3
  by_cases h4 : n = 4
  · subst n
    rw [coeff_C_mul, coeff_add, quotient1,
      coeff_mul_linearPseudoQuotient_succ remainder1 remainder2 7 6 3, coeff_C_mul]
    norm_num
    rw [source_coeff_4, source_coeff_6, source_coeff_7,
    remainder2_coeff_4, remainder2_coeff_5, remainder2_coeff_6,
    remainder3_coeff_4, remainder2_coeff_3]
    exact recurrence1_inner_4
  by_cases h5 : n = 5
  · subst n
    rw [coeff_C_mul, coeff_add, quotient1,
      coeff_mul_linearPseudoQuotient_succ remainder1 remainder2 7 6 4, coeff_C_mul]
    norm_num
    rw [source_coeff_5, source_coeff_6, source_coeff_7,
    remainder2_coeff_5, remainder2_coeff_6, remainder3_coeff_5,
    remainder2_coeff_4]
    exact recurrence1_inner_5
  by_cases h6 : n = 6
  · subst n
    rw [coeff_C_mul, coeff_add, quotient1,
      coeff_mul_linearPseudoQuotient_succ remainder1 remainder2 7 6 5, coeff_C_mul]
    norm_num
    rw [source_coeff_6, source_coeff_7, remainder2_coeff_6,
    remainder2_coeff_5, remainder3_coeff_6]
    ring
  by_cases h7 : n = 7
  · subst n
    rw [coeff_C_mul, coeff_add, quotient1,
      coeff_mul_linearPseudoQuotient_succ remainder1 remainder2 7 6 6, coeff_C_mul]
    norm_num
    rw [source_coeff_7, source_coeff_6, remainder2_coeff_7,
    remainder2_coeff_5, remainder2_coeff_6, remainder3_coeff_7]
    ring
  have hn : 7 < n := by omega
  have hsource : remainder1.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (remainder1_degree.trans_lt hn)
  have hremainder3 : remainder3.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (remainder3_degree.trans_lt (by omega))
  have hproductDegree :
      (remainder2 * quotient1).natDegree ≤ 7 := by
    exact natDegree_mul_le.trans (by
      have h2 := remainder2_degree
      have hq := quotient1_degree
      omega)
  have hproduct : (remainder2 * quotient1).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt (hproductDegree.trans_lt hn)
  rw [coeff_C_mul, coeff_add, coeff_C_mul, hsource,
    hremainder3, hproduct]
  ring
end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
