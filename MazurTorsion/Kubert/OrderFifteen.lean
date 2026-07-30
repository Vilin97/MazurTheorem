/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderFifteenModel
import MazurTorsion.NumberTheory.XOneFifteenReduction

open scoped WeierstrassCurve.Affine

/-!
# Excluding rational points of order fifteen

An exact order-fifteen point produces, through Tate normal form, a rational
point on

`V² = U(U² - 7U + 16)`

whose abscissa is different from `0` and `4`.  The specialized two-isogeny
descent, reduction modulo seven, and order-eight obstruction show that every
affine rational point on this curve has one of exactly those two abscissae.
This contradiction closes the order-fifteen branch.
-/

namespace MazurTorsion.Kubert

/-- No rational elliptic curve has a rational point of exact order
fifteen. -/
theorem no_rational_point_of_order_fifteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 15 := by
  intro hQ
  obtain ⟨b, c, hmodel, hU0, hU4⟩ :=
    exists_orderFifteenModel_of_exact_order E Q hQ
  rcases XOneFifteen.point_abscissa_eq_zero_or_four hmodel with h | h
  · exact hU0 h
  · exact hU4 h

/-- Obstruction-form restatement on the canonical rational base change. -/
theorem rationalPoint_addOrderOf_ne_fifteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 15 :=
  no_rational_point_of_order_fifteen E Q

end MazurTorsion.Kubert
