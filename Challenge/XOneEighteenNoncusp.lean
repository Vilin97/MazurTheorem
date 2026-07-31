/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneEighteenDescent

/-!
# Challenge: rational points on the order-eighteen curve

The compiled Tate-normal-form reduction sends a point of exact order
eighteen to a rational point on this sextic with abscissa different from
zero and one. Thus this statement is exactly the missing rational-point
classification needed by that branch.
-/

namespace MazurTheorem.Challenge

/-- The explicit order-eighteen genus-two model has no rational point away
from its two cusp abscissas. -/
theorem xOneEighteen_no_noncuspidal_point
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 =
        MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False := sorry

end MazurTheorem.Challenge
