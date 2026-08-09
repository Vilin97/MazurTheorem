/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateConvolution
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateLHS
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Checked raw certificate for the first Lécacheux orbit relation

Exact polynomial division produced the generated coefficient data in the leaf
modules imported above.  Lean checks each shard and this small module combines
the two sides.  A public theorem over the raw orbit definitions is supplied
below the private certificate.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate

private theorem polynomial_certificate (r s : ℚ) :
    Internal.term0 r s + Internal.term1 r s + Internal.term2 r s +
        Internal.term3 r s =
      Internal.rawF r s * Internal.qN r s := by
  rw [Internal.terms_eq_lhs, Internal.lhs_eq_H, Internal.rhs_eq_H]

open OrderTwentyFiveRawOrbitFactorCertificate

private theorem rawOrbitXZero_eq_aa (r s : ℚ)
    (hr : r ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hJ : J r s ≠ 0)
    (hK : K r s ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitXZero r s = Internal.aa r s := by
  rw [orderTwentyFiveRawOrbitXZero,
    yOne_eq_factor r s hr hA hB hE hK hYOne,
    yFour_eq_factor r s hB hC hD hE hK hYFour,
    Internal.aa_eq_factor]
  field_simp [hr, hA, hB, hC, hD, hE, hJ, hK]

private theorem rawOrbitXTwo_eq_cc (r s : ℚ)
    (hs : s ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hJ : J r s ≠ 0)
    (hK : K r s ≠ 0) (hP9 : P9 r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitXTwo r s = Internal.cc r s := by
  rw [orderTwentyFiveRawOrbitXTwo,
    yFour_eq_factor r s hB hC hD hE hK hYFour,
    yNine_eq_factor r s hs hA hB hC hD hE hK hYNine,
    Internal.cc_eq_factor]
  field_simp [hs, hA, hB, hC, hD, hE, hJ, hK, hP9]

private theorem rawOrbitXZero_mul_XOne_eq_aabb (r s : ℚ)
    (hr : r ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hJ : J r s ≠ 0)
    (hK : K r s ≠ 0) (hL : L r s ≠ 0) (hP6 : P6 r s ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0)
    (hYTwo : orderTwentyFiveRawOrbitYTwoDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYEight : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitXZero r s *
        orderTwentyFiveRawOrbitXOne r s = Internal.aabb r s := by
  rw [orderTwentyFiveRawOrbitXZero, orderTwentyFiveRawOrbitXOne,
    yOne_eq_factor r s hr hA hB hE hK hYOne,
    yTwo_eq_factor r s hA hB hC hD hYTwo,
    yFour_eq_factor r s hB hC hD hE hK hYFour,
    yEight_eq_factor r s hA hB hC hYEight,
    Internal.aabb_eq_factor]
  field_simp [hr, hA, hB, hC, hD, hE, hJ, hK, hL, hP6]

private theorem rawOrbitXZero_mul_XThree_eq_aadd (r s : ℚ)
    (hr : r ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hD : D r s ≠ 0) (hE : E r s ≠ 0) (hJ : J r s ≠ 0)
    (hK : K r s ≠ 0) (hL : L r s ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYEight : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0) :
    orderTwentyFiveRawOrbitXZero r s *
        orderTwentyFiveRawOrbitXThree r s = Internal.aadd r s := by
  rw [orderTwentyFiveRawOrbitXZero, orderTwentyFiveRawOrbitXThree,
    yOne_eq_factor r s hr hA hB hE hK hYOne,
    yFour_eq_factor r s hB hC hD hE hK hYFour,
    yEight_eq_factor r s hA hB hC hYEight,
    Internal.aadd_eq_factor]
  field_simp [hr, hA, hB, hC, hD, hE, hJ, hK, hL]

/-- Sutherland's raw equation and the nonvanishing denominators of the five
Lécacheux modular units imply the first raw cyclic orbit relation. -/
theorem _root_.MazurTorsion.Kubert.orderTwentyFiveRawOrbit_relationZero_eq_zero
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hA : A r s ≠ 0) (hB : B r s ≠ 0) (hC : C r s ≠ 0)
    (hK : K r s ≠ 0) (hD : D r s ≠ 0) (hE : E r s ≠ 0)
    (hYOne : orderTwentyFiveRawOrbitYOneDenominator r s ≠ 0)
    (hYTwo : orderTwentyFiveRawOrbitYTwoDenominator r s ≠ 0)
    (hYFour : orderTwentyFiveRawOrbitYFourDenominator r s ≠ 0)
    (hYEight : orderTwentyFiveRawOrbitYEightDenominator r s ≠ 0)
    (hYNine : orderTwentyFiveRawOrbitYNineDenominator r s ≠ 0)
    (hF : orderTwentyFiveRawSutherlandF r s = 0) :
    orderTwentyFiveOrbitRelationZero
      (orderTwentyFiveRawOrbitXZero r s)
      (orderTwentyFiveRawOrbitXOne r s)
      (orderTwentyFiveRawOrbitXTwo r s)
      (orderTwentyFiveRawOrbitXThree r s)
      (orderTwentyFiveRawOrbitXFour r s) = 0 := by
  have hJ :=
    j_ne_zero_of_yFourDenominator_ne_zero r s hB hE hK hYFour
  have hL :=
    l_ne_zero_of_yEightDenominator_ne_zero r s hA hB hC hYEight
  have hP6 :=
    p6_ne_zero_of_yTwoDenominator_ne_zero r s hB hC hD hYTwo
  have hP9 :=
    p9_ne_zero_of_yNineDenominator_ne_zero r s hB hD hE hK hYNine
  have hBI : Internal.B r s ≠ 0 := by
    simpa only [Internal.B, B] using hB
  have hCI : Internal.C r s ≠ 0 := by
    simpa only [Internal.C, C] using hC
  have hKI : Internal.K r s ≠ 0 := by
    simpa only [Internal.K, K] using hK
  have hDI : Internal.D r s ≠ 0 := by
    simpa only [Internal.D, D] using hD
  have hEI : Internal.E r s ≠ 0 := by
    simpa only [Internal.E, E] using hE
  have hJI : Internal.J r s ≠ 0 := by
    simpa only [Internal.J, J] using hJ
  have hP6I : Internal.P6 r s ≠ 0 := by
    simpa only [Internal.P6_eq_factor] using hP6
  have hP9I : Internal.P9 r s ≠ 0 := by
    simpa only [Internal.P9_eq_factor] using hP9
  have hxZero :=
    rawOrbitXZero_eq_aa r s hr hA hB hC hD hE hJ hK hYOne hYFour
  have hxTwo :=
    rawOrbitXTwo_eq_cc r s hs hA hB hC hD hE hJ hK hP9 hYFour hYNine
  have hxZeroOne :=
    rawOrbitXZero_mul_XOne_eq_aabb r s hr hA hB hC hD hE hJ hK hL hP6
      hYOne hYTwo hYFour hYEight
  have hxZeroThree :=
    rawOrbitXZero_mul_XThree_eq_aadd r s hr hA hB hC hD hE hJ hK hL
      hYOne hYFour hYEight
  have hqD : Internal.qD r s ≠ 0 := by
    rw [Internal.qD_eq_factor]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero
                (mul_ne_zero
                  (mul_ne_zero
                    (mul_ne_zero hr hs) (pow_ne_zero 2 hB))
                    (pow_ne_zero 3 hC))
                  (pow_ne_zero 2 hK))
                (pow_ne_zero 2 hD))
              (pow_ne_zero 2 hE)) hJ) hP6) hP9
  have hcleared :
      Internal.qD r s *
          (Internal.aa r s - Internal.cc r s - Internal.aabb r s +
            Internal.aadd r s) =
        Internal.term0 r s + Internal.term1 r s + Internal.term2 r s +
          Internal.term3 r s := by
    simp only [Internal.qD, Internal.aa, Internal.cc, Internal.aabb,
      Internal.aadd, Internal.term0, Internal.term1, Internal.term2,
      Internal.term3]
    field_simp [hr, hs, hBI, hCI, hDI, hEI, hJI, hKI, hP6I, hP9I]
    ring
  have hsum :
      Internal.term0 r s + Internal.term1 r s + Internal.term2 r s +
          Internal.term3 r s = 0 := by
    have hcertificate := polynomial_certificate r s
    rw [Internal.rawF_eq_rawSutherlandF, hF, zero_mul] at hcertificate
    exact hcertificate
  have hinternal :
      Internal.aa r s - Internal.cc r s - Internal.aabb r s +
          Internal.aadd r s = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hqD
    rw [hcleared, hsum]
  simp only [orderTwentyFiveOrbitRelationZero]
  calc
    orderTwentyFiveRawOrbitXZero r s - orderTwentyFiveRawOrbitXTwo r s -
          orderTwentyFiveRawOrbitXZero r s *
            (orderTwentyFiveRawOrbitXOne r s -
              orderTwentyFiveRawOrbitXThree r s) =
        orderTwentyFiveRawOrbitXZero r s - orderTwentyFiveRawOrbitXTwo r s -
          orderTwentyFiveRawOrbitXZero r s *
            orderTwentyFiveRawOrbitXOne r s +
          orderTwentyFiveRawOrbitXZero r s *
            orderTwentyFiveRawOrbitXThree r s := by ring
    _ = Internal.aa r s - Internal.cc r s - Internal.aabb r s +
          Internal.aadd r s := by
      rw [hxZeroOne, hxZeroThree, hxZero, hxTwo]
    _ = 0 := hinternal

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate
