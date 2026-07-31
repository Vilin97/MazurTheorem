/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFive

/-!
# Challenge: exclude rational points of order thirty-five
-/

open scoped WeierstrassCurve.Affine

namespace MazurTheorem.Challenge

/-- An elliptic curve over the rationals has no rational point of exact
additive order thirty-five. -/
theorem no_rational_point_of_order_thirtyFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) :
    addOrderOf P ≠ 35 := sorry

end MazurTheorem.Challenge
