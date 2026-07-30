/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderFourteenModel
import MazurTorsion.NumberTheory.XOneFourteenReduction

open scoped WeierstrassCurve.Affine

/-!
# Excluding rational points of order fourteen

An exact order-fourteen point produces, through Tate normal form, a rational
point on

`V² = U(U² - 11U + 32)`

whose abscissa is different from `0`, `4`, and `8`.  The two-isogeny descent
and reduction modulo three show that every affine rational point on this
curve has one of precisely those three abscissae.  This contradiction closes
the order-fourteen branch.
-/

namespace MazurTorsion.Kubert

/-- No rational elliptic curve has a rational point of exact order
fourteen. -/
theorem no_rational_point_of_order_fourteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 14 := by
  intro hQ
  obtain ⟨b, c, hmodel, hU0, hU4, hU8⟩ :=
    exists_orderFourteenModel_of_exact_order E Q hQ
  rcases
      XOneFourteen.point_abscissa_eq_zero_four_or_eight
        hmodel with h | h | h
  · exact hU0 h
  · exact hU4 h
  · exact hU8 h

/-- Obstruction-form restatement on the canonical rational base change. -/
theorem rationalPoint_addOrderOf_ne_fourteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 14 :=
  no_rational_point_of_order_fourteen E Q

end MazurTorsion.Kubert
