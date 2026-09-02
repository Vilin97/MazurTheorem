/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XZeroFortyNineTransfer

/-!
# Challenge: exclude rational points of order forty-nine

The recommended route is to bridge the marked seven-isogeny tower to the
already compiled rational-point classification of the explicit `X_0(49)`
correspondence.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTheorem.Challenge

/-- An elliptic curve over the rationals has no rational point of exact
additive order forty-nine. -/
theorem no_rational_point_of_order_fortyNine
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) :
    addOrderOf P ≠ 49 :=
  MazurTorsion.XZeroFortyNine.rationalPoint_addOrderOf_ne_fortyNine E P

end MazurTheorem.Challenge
