/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ComputeDegree

/-!
# Recurrence 2 lookup certificate: exceptional coefficient lookup

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2Exceptional_coeff_0 :
    exceptional2.coeff 0 =
      (0 : ℚ) := by
  unfold exceptional2 exceptionalUnit2 parameter
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, Polynomial.coeff_one]

theorem recurrence2Exceptional_coeff_1 :
    exceptional2.coeff 1 =
      (0 : ℚ) := by
  unfold exceptional2 exceptionalUnit2 parameter
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, Polynomial.coeff_one]

theorem recurrence2Exceptional_coeff_2 :
    exceptional2.coeff 2 =
      (-1 : ℚ) := by
  unfold exceptional2 exceptionalUnit2 parameter
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, Polynomial.coeff_one]

theorem recurrence2Exceptional_coeff_3 :
    exceptional2.coeff 3 =
      (1 : ℚ) := by
  unfold exceptional2 exceptionalUnit2 parameter
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ, Polynomial.coeff_one]

theorem recurrence2Exceptional_natDegree_le :
    exceptional2.natDegree ≤ 3 := by
  unfold exceptional2 exceptionalUnit2 parameter
  compute_degree

theorem recurrence2Exceptional_coeff_high
    (n : ℕ) (h : 3 < n) : exceptional2.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2Exceptional_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
