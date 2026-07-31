/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirteenModel

/-!
# Challenge: rational points on the order-thirteen curve

The compiled Tate-normal-form reduction sends a point of exact order
thirteen to a rational point on this sextic with abscissa different from
zero and negative one. Thus this statement is exactly the missing
rational-point classification needed by that branch.
-/

namespace MazurTheorem.Challenge

/-- The explicit `X₁(13)` sextic has no rational point away from its two
rational affine cusp abscissas. -/
theorem xOneThirteen_no_noncuspidal_point
    (x y : ℚ) (hx0 : x ≠ 0) (hxnegOne : x ≠ -1)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderThirteenHyperellipticPolynomial x) :
    False := sorry

end MazurTheorem.Challenge
