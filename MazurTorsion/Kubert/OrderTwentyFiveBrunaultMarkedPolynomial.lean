/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveNormalizedModel
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCertificate

/-!
# Brunault's polynomial at a marked point of order twenty-five

The normalized Tate recurrence supplies a point on Sutherland's raw curve and
all denominator conditions needed by the checked Lécacheux certificate.  The
raw modular units are then identified with Brunault's public coordinates.
-/

namespace MazurTorsion.Kubert

open OrderTwentyFiveRawOrbitFactorCertificate

/-- Brunault's two modular-unit coordinates attached to an exact-order-25
marked Tate point satisfy his characteristic-zero polynomial. -/
theorem orderTwentyFiveBrunaultPolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveBrunaultPolynomial
        (orderTwentyFiveBrunaultU b c)
        (orderTwentyFiveBrunaultV b c) = 0 := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hopen : OrderTwentyFiveRawOrbitOpenCertificate r s := by
    simpa only [r, s] using
      orderTwentyFiveRawOrbit_openCertificate_of_marked_order
        b c hb h00 horder
  have hA : A r s ≠ 0 := by
    simpa only [A] using hopen.r_sub_s_ne_zero
  have hB : B r s ≠ 0 := by
    simpa only [B] using hopen.s_sub_one_ne_zero
  have hC : C r s ≠ 0 := by
    simpa only [C] using hopen.seven_factor_ne_zero
  have hK : K r s ≠ 0 := by
    simpa only [K] using hopen.eight_factor_ne_zero
  have hD : D r s ≠ 0 := by
    simpa only [D] using hopen.eleven_factor_ne_zero
  have hE : E r s ≠ 0 := by
    simpa only [E] using hopen.twelve_factor_ne_zero
  have hraw :
      orderTwentyFiveBrunaultPolynomial
          (orderTwentyFiveRawOrbitXZero r s)
          (-orderTwentyFiveRawOrbitXTwo r s) = 0 :=
    orderTwentyFiveRawOrbit_brunaultPolynomial_eq_zero
      r s hopen.r_ne_zero hopen.s_ne_zero hA hB hC hK hD hE
      hopen.yOne_denominator_ne_zero hopen.yFour_denominator_ne_zero
      hopen.yNine_denominator_ne_zero hopen.sutherland_eq_zero
  obtain ⟨hU, hV⟩ :=
    orderTwentyFiveBrunault_coordinates_eq_rawOrbit_of_marked_order
      b c hb h00 horder
  rw [hU, hV]
  exact hraw

end MazurTorsion.Kubert
