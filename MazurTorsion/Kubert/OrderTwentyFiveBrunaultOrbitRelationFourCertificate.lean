/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateConvolution
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateLHS
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A checked certificate for the fifth raw order-25 orbit relation

The exact generated coefficient data has been split into small kernel-checked
leaves. The sole root-level public endpoint below is stated over the canonical
raw orbit coordinates and factor data.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

private theorem polynomial_certificate (r s : ℚ) :
    term0 r s + term1 r s + term2 r s + term3 r s = F r s * Q r s := by
  rw [terms_eq_numerator, F_mul_Q_eq_numerator]

private theorem F_eq_rawSutherlandF (r s : ℚ) :
    F r s = orderTwentyFiveRawSutherlandF r s := by
  simp only [F, evalEleven, fCoefficient, orderTwentyFiveRawSutherlandF]
  ring

private theorem N_eq_rawOrbitFactorN (r s : ℚ) :
    N r s = OrderTwentyFiveRawOrbitFactorCertificate.N r s := by
  simp only [N, OrderTwentyFiveRawOrbitFactorCertificate.N,
    OrderTwentyFiveRawOrbitFactorCertificate.A,
    OrderTwentyFiveRawOrbitFactorCertificate.C,
    OrderTwentyFiveRawOrbitFactorCertificate.G,
    OrderTwentyFiveRawOrbitFactorCertificate.K]
  ring

private theorem unit_relation_four
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hL : L r s ≠ 0)
    (hJ : J r s ≠ 0) (hP9 : P9 r s ≠ 0) (hF : F r s = 0) :
    y9 r s - y8 r s - y9 r s * y4 r s * (y1 r s - y9 r s) = 0 := by
  have hpoly : term0 r s + term1 r s + term2 r s + term3 r s = 0 := by
    rw [polynomial_certificate, hF]
    ring
  simp only [y1, y4, y8, y9]
  field_simp [hr, hs, hA, hB, hC, hD, hE, hL, hJ, hP9]
  simp only [term0, term1, term2, term3] at hpoly
  linear_combination hpoly

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate

open OrderTwentyFiveRawOrbitFactorCertificate

/-- Sutherland's raw equation and the nonvanishing denominators of the first,
fourth, eighth, and ninth Lécacheux units imply the fifth cyclic raw-orbit
relation. -/
theorem _root_.MazurTorsion.Kubert.orderTwentyFiveRawOrbit_relationFour_eq_zero
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hK : K r s ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYEight : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0)
    (hF : orderTwentyFiveRawSutherlandF r s = 0) :
    orderTwentyFiveOrbitRelationFour
      (orderTwentyFiveRawOrbitXZero r s)
      (orderTwentyFiveRawOrbitXOne r s)
      (orderTwentyFiveRawOrbitXTwo r s)
      (orderTwentyFiveRawOrbitXThree r s)
      (orderTwentyFiveRawOrbitXFour r s) = 0 := by
  have hJ :=
    j_ne_zero_of_yFourDenominator_ne_zero r s hB hE hK hYFour
  have hL :=
    l_ne_zero_of_yEightDenominator_ne_zero r s hA hB hC hYEight
  have hP9 :=
    p9_ne_zero_of_yNineDenominator_ne_zero r s hB hD hE hK hYNine
  have hAI := hA
  change Internal.A r s ≠ 0 at hAI
  have hBI := hB
  change Internal.B r s ≠ 0 at hBI
  have hCI := hC
  change Internal.C r s ≠ 0 at hCI
  have hDI := hD
  change Internal.D r s ≠ 0 at hDI
  have hEI := hE
  change Internal.E r s ≠ 0 at hEI
  have hLI := hL
  change Internal.L r s ≠ 0 at hLI
  have hJI := hJ
  change Internal.J r s ≠ 0 at hJI
  have hP9I := hP9
  change Internal.P9 r s ≠ 0 at hP9I
  have hFI : Internal.F r s = 0 := by
    rw [Internal.F_eq_rawSutherlandF]
    exact hF
  have hyOneI :=
    yOne_eq_factor r s hr hA hB hE hK hYOne
  change orderTwentyFiveRawOrbitYOne r s = Internal.y1 r s at hyOneI
  have hyFourI :=
    yFour_eq_factor r s hB hC hD hE hK hYFour
  change orderTwentyFiveRawOrbitYFour r s = Internal.y4 r s at hyFourI
  have hyEightI :=
    yEight_eq_factor r s hA hB hC hYEight
  change orderTwentyFiveRawOrbitYEight r s = Internal.y8 r s at hyEightI
  have hyNineI :=
    yNine_eq_factor r s hs hA hB hC hD hE hK hYNine
  rw [← Internal.N_eq_rawOrbitFactorN] at hyNineI
  change orderTwentyFiveRawOrbitYNine r s = Internal.y9 r s at hyNineI
  have hu4 :=
    Internal.unit_relation_four r s hr hs hAI hBI hCI hDI hEI hLI hJI hP9I hFI
  rw [← hyOneI, ← hyFourI, ← hyEightI, ← hyNineI] at hu4
  simp only [orderTwentyFiveOrbitRelationFour,
    orderTwentyFiveRawOrbitXZero, orderTwentyFiveRawOrbitXOne,
    orderTwentyFiveRawOrbitXTwo, orderTwentyFiveRawOrbitXFour]
  linear_combination orderTwentyFiveRawOrbitYTwo r s * hu4

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate
