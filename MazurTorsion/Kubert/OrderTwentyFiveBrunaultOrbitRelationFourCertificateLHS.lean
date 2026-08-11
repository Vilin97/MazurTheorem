/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateLHSHigh
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateLHSLow
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateLHSMid
import Mathlib.Tactic.LinearCombination

/-!
# Assembly of the split RelationFour left-side certificate

The aggregate coefficient functions are supported in degrees `0` through `34`
(their catch-all branch is zero), and this module consumes a checked equality
for every one of those coefficients.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

private theorem lhs_coefficients_all (s : ℚ) (n : Nat) (hn : n ≤ 34) :
    lhsCoefficientEq n s := by
  by_cases hlow : n ≤ 11
  · exact lhs_coefficients_low s n hlow
  by_cases hmid : n ≤ 23
  · exact lhs_coefficients_mid s n (by omega) hmid
  · exact lhs_coefficients_high s n (by omega) hn

private theorem evalThirtyFive_sum_four
    (a b c d e : Nat → ℚ) (r : ℚ)
    (h : ∀ n, n ≤ 34 → a n + b n + c n + d n = e n) :
    evalThirtyFive a r + evalThirtyFive b r +
        evalThirtyFive c r + evalThirtyFive d r =
      evalThirtyFive e r := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  have h5 := h 5 (by omega)
  have h6 := h 6 (by omega)
  have h7 := h 7 (by omega)
  have h8 := h 8 (by omega)
  have h9 := h 9 (by omega)
  have h10 := h 10 (by omega)
  have h11 := h 11 (by omega)
  have h12 := h 12 (by omega)
  have h13 := h 13 (by omega)
  have h14 := h 14 (by omega)
  have h15 := h 15 (by omega)
  have h16 := h 16 (by omega)
  have h17 := h 17 (by omega)
  have h18 := h 18 (by omega)
  have h19 := h 19 (by omega)
  have h20 := h 20 (by omega)
  have h21 := h 21 (by omega)
  have h22 := h 22 (by omega)
  have h23 := h 23 (by omega)
  have h24 := h 24 (by omega)
  have h25 := h 25 (by omega)
  have h26 := h 26 (by omega)
  have h27 := h 27 (by omega)
  have h28 := h 28 (by omega)
  have h29 := h 29 (by omega)
  have h30 := h 30 (by omega)
  have h31 := h 31 (by omega)
  have h32 := h 32 (by omega)
  have h33 := h 33 (by omega)
  have h34 := h 34 (by omega)
  simp only [evalThirtyFive]
  linear_combination r ^ 34 * h34 +
    r ^ 33 * h33 +
    r ^ 32 * h32 +
    r ^ 31 * h31 +
    r ^ 30 * h30 +
    r ^ 29 * h29 +
    r ^ 28 * h28 +
    r ^ 27 * h27 +
    r ^ 26 * h26 +
    r ^ 25 * h25 +
    r ^ 24 * h24 +
    r ^ 23 * h23 +
    r ^ 22 * h22 +
    r ^ 21 * h21 +
    r ^ 20 * h20 +
    r ^ 19 * h19 +
    r ^ 18 * h18 +
    r ^ 17 * h17 +
    r ^ 16 * h16 +
    r ^ 15 * h15 +
    r ^ 14 * h14 +
    r ^ 13 * h13 +
    r ^ 12 * h12 +
    r ^ 11 * h11 +
    r ^ 10 * h10 +
    r ^ 9 * h9 +
    r ^ 8 * h8 +
    r ^ 7 * h7 +
    r ^ 6 * h6 +
    r ^ 5 * h5 +
    r ^ 4 * h4 +
    r ^ 3 * h3 +
    r ^ 2 * h2 +
    r * h1 +
    1 * h0

/-- The four frozen numerator terms sum to the frozen quotient numerator. -/
theorem terms_eq_numerator (r s : ℚ) :
    term0 r s + term1 r s + term2 r s + term3 r s = numerator r s := by
  rw [termZero_eq_evalThirtyFive, termOne_eq_evalThirtyFive,
    termTwo_eq_evalThirtyFive, termThree_eq_evalThirtyFive]
  change
    evalThirtyFive (fun n => termZeroCoefficient n s) r +
        evalThirtyFive (fun n => termOneCoefficient n s) r +
        evalThirtyFive (fun n => termTwoCoefficient n s) r +
        evalThirtyFive (fun n => termThreeCoefficient n s) r =
      evalThirtyFive (fun n => numeratorCoefficient n s) r
  apply evalThirtyFive_sum_four
  intro n hn
  simpa only [lhsCoefficientEq] using lhs_coefficients_all s n hn

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
