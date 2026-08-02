/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalData
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ComputeDegree

/-!
# Recurrence 4 lookup certificate: exceptional coefficient lookup

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4Exceptional_coeff_0 :
    exceptional4.coeff 0 =
      (
        (-1) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_1 :
    exceptional4.coeff 1 =
      (
        (-19) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_2 :
    exceptional4.coeff 2 =
      (
        (-98) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_3 :
    exceptional4.coeff 3 =
      (
        (94) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_4 :
    exceptional4.coeff 4 =
      (
        (1355) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_5 :
    exceptional4.coeff 5 =
      (
        (-1375) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_6 :
    exceptional4.coeff 6 =
      (
        (-7054) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_7 :
    exceptional4.coeff 7 =
      (
        (18910) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_8 :
    exceptional4.coeff 8 =
      (
        (-19802) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_9 :
    exceptional4.coeff 9 =
      (
        (10514) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_10 :
    exceptional4.coeff 10 =
      (
        (-2928) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_11 :
    exceptional4.coeff 11 =
      (
        (436) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_12 :
    exceptional4.coeff 12 =
      (
        (-33) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem recurrence4Exceptional_coeff_13 :
    exceptional4.coeff 13 =
      (
        (1) /
        (23215239933528791584969 : ℚ)
      ) := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial, Polynomial.coeff_one]

private theorem recurrence4ExceptionalNormalized_natDegree_le :
    recurrence4ExceptionalNormalized.natDegree ≤ 13 := by
  unfold recurrence4ExceptionalNormalized
  unfold
    recurrence4ExceptionalNormalizedBlock0
    recurrence4ExceptionalNormalizedBlock1
  unfold coefficientTerm
  compute_degree

theorem recurrence4Exceptional_coeff_high
    (n : ℕ) (h : 13 < n) : exceptional4.coeff n = 0 := by
  rw [exceptional4_eq_recurrence4ExceptionalNormalized]
  unfold exceptionalUnit4
  rw [Polynomial.coeff_C_mul]
  have hzero : recurrence4ExceptionalNormalized.coeff n = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt
      recurrence4ExceptionalNormalized_natDegree_le h
  rw [hzero]
  norm_num

theorem recurrence4Exceptional_natDegree_le :
    exceptional4.natDegree ≤ 13 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence4Exceptional_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
