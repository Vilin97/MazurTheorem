/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveQuotientPoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The quotient-side degeneracy map for order twenty five

The explicit quotient point supplies a point-selected order-five Tate
parameter on the degree-five quotient.  Its invariant relation places the two
order-five parameters on the standard degeneracy curve.  The second
degeneracy map is strictly increasing over the rationals: after translating
its argument by one, it is `x⁵ + 5x³ + 5x - 11`.  Consequently the
Hauptmodul recovered from the quotient pair is exactly the orbit Hauptmodul
already identified from the fifth multiple.

This proves the complementary first-degeneracy identity without expanding
the quotient coordinates into a large raw-chart certificate.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

private theorem secondDegeneracyParameter_injective :
    Function.Injective orderTwentyFiveSecondDegeneracyParameter := by
  have hstrict : StrictMono orderTwentyFiveSecondDegeneracyParameter := by
    intro a b hab
    have hab' : a + 1 < b + 1 := by linarith
    have hfive : (a + 1) ^ 5 < (b + 1) ^ 5 :=
      (show Odd 5 by norm_num).strictMono_pow hab'
    have hthree : (a + 1) ^ 3 < (b + 1) ^ 3 :=
      (show Odd 3 by norm_num).strictMono_pow hab'
    simp only [orderTwentyFiveSecondDegeneracyParameter,
      orderTwentyFiveHauptmodulDenominator]
    have ha :
        a * (a ^ 4 + 5 * a ^ 3 + 15 * a ^ 2 + 25 * a + 25) =
          (a + 1) ^ 5 + 5 * (a + 1) ^ 3 + 5 * (a + 1) - 11 := by
      ring
    have hb :
        b * (b ^ 4 + 5 * b ^ 3 + 15 * b ^ 2 + 25 * b + 25) =
          (b + 1) ^ 5 + 5 * (b + 1) ^ 3 + 5 * (b + 1) - 11 := by
      ring
    rw [ha, hb]
    linarith
  exact hstrict.injective

private theorem degeneracyRelation_eq_zero_of_invariantRelation
    {c d : ℚ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hrelation : orderTwentyFiveFiveDivisionRelation c d = 0) :
    orderTwentyFiveDegeneracyRelation
      (orderFiveXZeroParameter d) (orderFiveXZeroParameter c) = 0 := by
  have hfactors :
      orderTwentyFiveFiveDivisionFactor c d *
          orderTwentyFiveFiveDivisionReverseFactor c d = 0 := by
    rcases orderTwentyFiveFiveDivisionFactor_or_reverse hrelation with
      hforward | hreverse
    · rw [hforward, zero_mul]
    · rw [hreverse, mul_zero]
  have hcleared :=
    orderTwentyFiveDegeneracyRelation_cleared c d hc hd
  rw [hfactors] at hcleared
  exact (mul_eq_zero.mp hcleared).resolve_left
    (mul_ne_zero (pow_ne_zero 5 hc) (pow_ne_zero 5 hd))

/-- The explicit quotient point realizes the first degeneracy map at the
same recovered orbit Hauptmodul as the fifth-multiple normalization. -/
theorem orderTwentyFive_quotient_xZeroParameter_eq_orbitDegeneracy
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25)
    [(tateNormalCurve b c).IsElliptic] :
    orderFiveXZeroParameter
        (pointTateC
          (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
          (orderTwentyFiveQuotientGeneratorX b c)
          (orderTwentyFiveQuotientGeneratorY b c)) =
      orderTwentyFiveFirstDegeneracyParameter
        (-(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c))) := by
  let c5 := orderTwentyFiveFiveTateParameter b c
  let d := pointTateC
    (orderFiveVeluTarget c5)
    (orderTwentyFiveQuotientGeneratorX b c)
    (orderTwentyFiveQuotientGeneratorY b c)
  let n := -(orderTwentyFiveOrbitParameter
    (orderTwentyFiveBrunaultXZero b c)
    (orderTwentyFiveBrunaultXOne b c)
    (orderTwentyFiveBrunaultXTwo b c)
    (orderTwentyFiveBrunaultXThree b c)
    (orderTwentyFiveBrunaultXFour b c))
  obtain ⟨hc5, -, -, -, -, -, -, -, -, -, -, -, hd⟩ :=
    explicitQuotientPointPackage b c hb h00 horder
  have hrelation : orderTwentyFiveFiveDivisionRelation c5 d = 0 := by
    simpa only [c5, d] using
      orderTwentyFiveQuotientParameter_relation b c hb h00 horder
  have hdegeneracy :
      orderTwentyFiveDegeneracyRelation
        (orderFiveXZeroParameter d) (orderFiveXZeroParameter c5) = 0 :=
    degeneracyRelation_eq_zero_of_invariantRelation hc5 hd hrelation
  let m := orderTwentyFiveHauptmodulAt
    (orderFiveXZeroParameter d) (orderFiveXZeroParameter c5)
  obtain ⟨hfirst, hsecond⟩ :=
    orderTwentyFiveHauptmodulAt_spec hdegeneracy
  have hsecondKnown :
      orderFiveXZeroParameter c5 =
        orderTwentyFiveSecondDegeneracyParameter n := by
    simpa only [c5, n, orderTwentyFiveFiveTateParameter] using
      orderTwentyFive_fiveMultiple_xZeroParameter_eq_orbitDegeneracy
        b c hb h00 horder
  have hmn : m = n := by
    apply secondDegeneracyParameter_injective
    exact hsecond.trans hsecondKnown
  calc
    orderFiveXZeroParameter
          (pointTateC
            (orderFiveVeluTarget (orderTwentyFiveFiveTateParameter b c))
            (orderTwentyFiveQuotientGeneratorX b c)
            (orderTwentyFiveQuotientGeneratorY b c)) =
        orderFiveXZeroParameter d := rfl
    _ = orderTwentyFiveFirstDegeneracyParameter m := hfirst.symm
    _ = orderTwentyFiveFirstDegeneracyParameter n := by rw [hmn]
    _ = orderTwentyFiveFirstDegeneracyParameter
        (-(orderTwentyFiveOrbitParameter
          (orderTwentyFiveBrunaultXZero b c)
          (orderTwentyFiveBrunaultXOne b c)
          (orderTwentyFiveBrunaultXTwo b c)
          (orderTwentyFiveBrunaultXThree b c)
          (orderTwentyFiveBrunaultXFour b c))) := rfl

end MazurTorsion.Kubert
