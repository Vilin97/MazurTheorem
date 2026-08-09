/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenQuotientRankZero
import MazurTorsion.NumberTheory.XOneEighteenQuotientReductionAtSeventeen

/-!
# Final rank-zero consumer for `X₁(18)`

This module is the downstream consumer of the concrete two-descent.  Once
the arithmetic calculation proves that the image of `x - T` is trivial,
the checked rank-zero bridge makes the real-cubic quotient finite.  Genuine
reduction at the degree-one prime above `17` then classifies its points and
excludes both noncuspidal points on the sextic and rational points of exact
order eighteen.

The unconditional arithmetic theorem is added here only after the global
and dyadic certificates close; the two theorems below record the exact
consumer contract without replacing that missing proof by an assumption.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenFinalRankZero

noncomputable section

open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenQuotientRankZero
open MazurTorsion.XOneEighteenQuotientReductionAtSeventeen
open MazurTorsion.XOneEighteenRealCubicQuotient

/-- A completed proof that the concrete descent image is trivial excludes
every noncuspidal rational point on the order-eighteen sextic. -/
theorem no_noncuspidal_point_of_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥)
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False := by
  letI : Finite quotientCurve.toAffine.Point :=
    quotient_point_finite_of_range_mu_eq_bot hmu
  exact no_noncuspidal_point_of_finite_quotient x y hx0 hx1 hcurve

/-- The same concrete rank-zero input is consumed by the genuine
Tate-normal-form exact-order-eighteen reduction. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_range_mu_eq_bot
    (hmu :
      (WeierstrassCurve.Affine.μ
        (W := descentCurve.toAffine)).range = ⊥)
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 18 := by
  apply
    MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_eighteen_of_noNoncuspidalPoint
      E Q
  intro x y hx0 hx1 hcurve
  exact no_noncuspidal_point_of_range_mu_eq_bot
    hmu x y hx0 hx1 hcurve

end

end MazurTorsion.XOneEighteenFinalRankZero
