/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart4Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases

/-!
# Recurrence 4 scalar-zero tail convolution

This internal shard checks the bounded convolution window used at the top
fifty-four coefficients of the fourth pseudo-division scalar identity.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private theorem coeff_mul_totalDegree522_tail
    (p q : Coefficient) (a b n : ℕ)
    (hab : a + b = 522) (ha : a ≤ 469) (hb : b ≤ 469)
    (hlo : 469 ≤ n) (hhi : n ≤ 522)
    (hp : ∀ k, a < k → p.coeff k = 0) (hq : ∀ k, b < k → q.coeff k = 0) :
    (p * q).coeff n = ∑ x ∈ Finset.range (523 - n),
      p.coeff ((n - b) + x) * q.coeff (n - ((n - b) + x)) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Nat.succ_eq_add_one]
  rw [show n + 1 = (n - b) + (b + 1) by omega, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show b + 1 = (523 - n) + (n - a) by omega, Finset.sum_range_add]
  have hprefix : (∑ x ∈ Finset.range (n - b),
      p.coeff x * q.coeff (n - x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hq (n - x) (by simp only [Finset.mem_range] at hx; omega)]
    norm_num
  have hsuffix : (∑ x ∈ Finset.range (n - a),
      p.coeff ((n - b + (523 - n)) + x) *
        q.coeff (n - ((n - b + (523 - n)) + x))) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hp ((n - b + (523 - n)) + x) (by omega)]
    norm_num
  rw [hprefix]
  norm_num only [zero_add, ← Nat.add_assoc]
  rw [hsuffix, add_zero]

private def scalarResidual4Coefficient0TailEquation (n : ℕ) : Prop :=
  (∑ x ∈ Finset.range (523 - n),
    recurrence4LeadingSquare.coeff ((n - 194) + x) *
      remainder4Coefficient0.coeff (n - ((n - 194) + x))) =
    (∑ x ∈ Finset.range (523 - n),
      remainder5Coefficient0.coeff ((n - 346) + x) *
        recurrence4QuotientConstant.coeff (n - ((n - 346) + x))) +
      ∑ x ∈ Finset.range (523 - n),
        recurrence4ExceptionalProduct.coeff ((n - 153) + x) *
          remainder6Coefficient0.coeff (n - ((n - 153) + x))

private theorem scalarResidual4Coefficient0_tail_469_477
    (n : ℕ) (hlo : 469 ≤ n) (hhi : n ≤ 477) :
    scalarResidual4Coefficient0TailEquation n := by
  unfold scalarResidual4Coefficient0TailEquation
  interval_cases n <;> norm_num only <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;> norm_num only <;>
    simp (config := { failIfUnchanged := false }) only [orderSevenCoefficient] <;> norm_num

private theorem scalarResidual4Coefficient0_tail_478_486
    (n : ℕ) (hlo : 478 ≤ n) (hhi : n ≤ 486) :
    scalarResidual4Coefficient0TailEquation n := by
  unfold scalarResidual4Coefficient0TailEquation
  interval_cases n <;> norm_num only <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;> norm_num only <;>
    simp (config := { failIfUnchanged := false }) only [orderSevenCoefficient] <;> norm_num

private theorem scalarResidual4Coefficient0_tail_487_495
    (n : ℕ) (hlo : 487 ≤ n) (hhi : n ≤ 495) :
    scalarResidual4Coefficient0TailEquation n := by
  unfold scalarResidual4Coefficient0TailEquation
  interval_cases n <;> norm_num only <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;> norm_num only <;>
    simp (config := { failIfUnchanged := false }) only [orderSevenCoefficient] <;> norm_num

private theorem scalarResidual4Coefficient0_tail_496_504
    (n : ℕ) (hlo : 496 ≤ n) (hhi : n ≤ 504) :
    scalarResidual4Coefficient0TailEquation n := by
  unfold scalarResidual4Coefficient0TailEquation
  interval_cases n <;> norm_num only <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;> norm_num only <;>
    simp (config := { failIfUnchanged := false }) only [orderSevenCoefficient] <;> norm_num

private theorem scalarResidual4Coefficient0_tail_505_513
    (n : ℕ) (hlo : 505 ≤ n) (hhi : n ≤ 513) :
    scalarResidual4Coefficient0TailEquation n := by
  unfold scalarResidual4Coefficient0TailEquation
  interval_cases n <;> norm_num only <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;> norm_num only <;>
    simp (config := { failIfUnchanged := false }) only [orderSevenCoefficient] <;> norm_num

private theorem scalarResidual4Coefficient0_tail_514_522
    (n : ℕ) (hlo : 514 ≤ n) (hhi : n ≤ 522) :
    scalarResidual4Coefficient0TailEquation n := by
  unfold scalarResidual4Coefficient0TailEquation
  interval_cases n <;> norm_num only <;>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] <;> norm_num only <;>
    simp (config := { failIfUnchanged := false }) only [orderSevenCoefficient] <;> norm_num

theorem scalarResidual4Coefficient0_tail
    (n : ℕ) (hlo : 469 ≤ n) (hhi : n ≤ 522) :
    recurrence4Scalar0Left.coeff n =
      (recurrence4Scalar0Main + recurrence4Scalar0Exceptional).coeff n := by
  unfold recurrence4Scalar0Left recurrence4Scalar0Main
    recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_add]
  rw [coeff_mul_totalDegree522_tail recurrence4LeadingSquare remainder4Coefficient0
    328 194 n (by norm_num) (by norm_num) (by norm_num) hlo hhi
    recurrence4LeadingSquare_coeff_high recurrence4A0_coeff_high]
  rw [coeff_mul_totalDegree522_tail remainder5Coefficient0 recurrence4QuotientConstant
    176 346 n (by norm_num) (by norm_num) (by norm_num) hlo hhi
    recurrence4B0_coeff_high recurrence4QuotientConstant_coeff_high]
  rw [coeff_mul_totalDegree522_tail recurrence4ExceptionalProduct remainder6Coefficient0
    369 153 n (by norm_num) (by norm_num) (by norm_num) hlo hhi
    recurrence4ExceptionalProduct_coeff_high recurrence4C0_coeff_high]
  change scalarResidual4Coefficient0TailEquation n
  by_cases h₀ : n ≤ 477
  · exact scalarResidual4Coefficient0_tail_469_477 n hlo h₀
  by_cases h₁ : n ≤ 486
  · exact scalarResidual4Coefficient0_tail_478_486 n (by omega) h₁
  by_cases h₂ : n ≤ 495
  · exact scalarResidual4Coefficient0_tail_487_495 n (by omega) h₂
  by_cases h : n ≤ 504
  · exact scalarResidual4Coefficient0_tail_496_504 n (by omega) h
  by_cases h' : n ≤ 513
  · exact scalarResidual4Coefficient0_tail_505_513 n (by omega) h'
  · exact scalarResidual4Coefficient0_tail_514_522 n (by omega) hhi

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
