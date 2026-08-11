/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitPadic
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationTwoCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFiveCertificate
import MazurTorsion.Kubert.OrderTwentyFiveNormalizedModel

/-!
# Three-adic units on the checked raw order-twenty-five orbit

This module is the downstream consumer of the generated raw-relation
certificates.  An open raw Sutherland point supplies four cyclic equations
and the norm-one equation; a small checked identity recovers the remaining
cyclic equation.  Norm one also proves that every orbit coordinate is
nonzero, after which the valuation classifier can be applied.

The remaining premise is deliberately a valuation statement.  The local
equations admit five nonzero cusp rays, so rational nonvanishing alone cannot
show that a coordinate has nonzero reduction modulo three.  A future global
cusp-exclusion theorem need only prove that the first valuation is zero.
-/

namespace MazurTorsion.Kubert

open OrderTwentyFiveRawOrbitFactorCertificate

private theorem orderTwentyFiveOrbit_nonzero_of_relationFive
    (a b c d e : ℚ)
    (h₅ : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 := by
  have hproduct : a * b * c * d * e = 1 :=
    sub_eq_zero.mp (by
      simpa only [orderTwentyFiveOrbitRelationFive] using h₅)
  constructor
  · intro ha
    rw [ha] at hproduct
    norm_num at hproduct
  constructor
  · intro hb
    rw [hb] at hproduct
    norm_num at hproduct
  constructor
  · intro hc
    rw [hc] at hproduct
    norm_num at hproduct
  constructor
  · intro hd
    rw [hd] at hproduct
    norm_num at hproduct
  · intro he
    rw [he] at hproduct
    norm_num at hproduct

private theorem orderTwentyFiveRawOrbit_other_relations_of_openCertificate
    (r s : ℚ) (hopen : OrderTwentyFiveRawOrbitOpenCertificate r s) :
    orderTwentyFiveOrbitRelationZero
          (orderTwentyFiveRawOrbitXZero r s)
          (orderTwentyFiveRawOrbitXOne r s)
          (orderTwentyFiveRawOrbitXTwo r s)
          (orderTwentyFiveRawOrbitXThree r s)
          (orderTwentyFiveRawOrbitXFour r s) = 0 ∧
      orderTwentyFiveOrbitRelationTwo
          (orderTwentyFiveRawOrbitXZero r s)
          (orderTwentyFiveRawOrbitXOne r s)
          (orderTwentyFiveRawOrbitXTwo r s)
          (orderTwentyFiveRawOrbitXThree r s)
          (orderTwentyFiveRawOrbitXFour r s) = 0 ∧
      orderTwentyFiveOrbitRelationThree
          (orderTwentyFiveRawOrbitXZero r s)
          (orderTwentyFiveRawOrbitXOne r s)
          (orderTwentyFiveRawOrbitXTwo r s)
          (orderTwentyFiveRawOrbitXThree r s)
          (orderTwentyFiveRawOrbitXFour r s) = 0 ∧
      orderTwentyFiveOrbitRelationFour
          (orderTwentyFiveRawOrbitXZero r s)
          (orderTwentyFiveRawOrbitXOne r s)
          (orderTwentyFiveRawOrbitXTwo r s)
          (orderTwentyFiveRawOrbitXThree r s)
          (orderTwentyFiveRawOrbitXFour r s) = 0 ∧
      orderTwentyFiveOrbitRelationFive
          (orderTwentyFiveRawOrbitXZero r s)
          (orderTwentyFiveRawOrbitXOne r s)
          (orderTwentyFiveRawOrbitXTwo r s)
          (orderTwentyFiveRawOrbitXThree r s)
          (orderTwentyFiveRawOrbitXFour r s) = 0 := by
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
  exact
    ⟨orderTwentyFiveRawOrbit_relationZero_eq_zero
        r s hopen.r_ne_zero hopen.s_ne_zero hA hB hC hK hD hE
        hopen.yOne_denominator_ne_zero hopen.yTwo_denominator_ne_zero
        hopen.yFour_denominator_ne_zero hopen.yEight_denominator_ne_zero
        hopen.yNine_denominator_ne_zero hopen.sutherland_eq_zero,
      orderTwentyFiveRawOrbit_relationTwo_eq_zero
        r s hopen.r_ne_zero hA hB hC hK hD hE
        hopen.yOne_denominator_ne_zero hopen.yTwo_denominator_ne_zero
        hopen.yFour_denominator_ne_zero hopen.yEight_denominator_ne_zero
        hopen.sutherland_eq_zero,
      orderTwentyFiveRawOrbit_relationThree_eq_zero
        r s hopen.s_ne_zero hA hB hC hD hE hK
        hopen.yTwo_denominator_ne_zero hopen.yFour_denominator_ne_zero
        hopen.yEight_denominator_ne_zero hopen.yNine_denominator_ne_zero
        hopen.sutherland_eq_zero,
      orderTwentyFiveRawOrbit_relationFour_eq_zero
        r s hopen.r_ne_zero hopen.s_ne_zero hA hB hC hD hE hK
        hopen.yOne_denominator_ne_zero hopen.yFour_denominator_ne_zero
        hopen.yEight_denominator_ne_zero hopen.yNine_denominator_ne_zero
        hopen.sutherland_eq_zero,
      orderTwentyFiveRawOrbit_relationFive_eq_zero
        r s hopen.r_ne_zero hopen.s_ne_zero hopen.r_sub_s_ne_zero
        hopen.s_sub_one_ne_zero hopen.seven_factor_ne_zero
        hopen.eight_factor_ne_zero hopen.eleven_factor_ne_zero
        hopen.twelve_factor_ne_zero hopen.yOne_denominator_ne_zero
        hopen.yTwo_denominator_ne_zero hopen.yFour_denominator_ne_zero
        hopen.yEight_denominator_ne_zero hopen.yNine_denominator_ne_zero
        hopen.sutherland_eq_zero⟩

/-- An open raw Sutherland point whose first Lécacheux coordinate has
three-adic valuation zero has five explicit three-adic unit coordinates.
This is the checked local consumer intended for a future global
cusp-exclusion theorem. -/
theorem orderTwentyFiveRawOrbit_threeUnits_of_openCertificate
    (r s : ℚ) (hopen : OrderTwentyFiveRawOrbitOpenCertificate r s)
    (hfirst : padicValRat 3 (orderTwentyFiveRawOrbitXZero r s) = 0) :
    orderTwentyFiveRatIsThreeUnit (orderTwentyFiveRawOrbitXZero r s) ∧
      orderTwentyFiveRatIsThreeUnit (orderTwentyFiveRawOrbitXOne r s) ∧
      orderTwentyFiveRatIsThreeUnit (orderTwentyFiveRawOrbitXTwo r s) ∧
      orderTwentyFiveRatIsThreeUnit (orderTwentyFiveRawOrbitXThree r s) ∧
      orderTwentyFiveRatIsThreeUnit (orderTwentyFiveRawOrbitXFour r s) := by
  let a := orderTwentyFiveRawOrbitXZero r s
  let b := orderTwentyFiveRawOrbitXOne r s
  let c := orderTwentyFiveRawOrbitXTwo r s
  let d := orderTwentyFiveRawOrbitXThree r s
  let e := orderTwentyFiveRawOrbitXFour r s
  obtain ⟨h₀, h₂, h₃, h₄, h₅⟩ :=
    orderTwentyFiveRawOrbit_other_relations_of_openCertificate r s hopen
  change orderTwentyFiveOrbitRelationZero a b c d e = 0 at h₀
  change orderTwentyFiveOrbitRelationTwo a b c d e = 0 at h₂
  change orderTwentyFiveOrbitRelationThree a b c d e = 0 at h₃
  change orderTwentyFiveOrbitRelationFour a b c d e = 0 at h₄
  change orderTwentyFiveOrbitRelationFive a b c d e = 0 at h₅
  change padicValRat 3 a = 0 at hfirst
  obtain ⟨ha, hb, hc, hd, he⟩ :=
    orderTwentyFiveOrbit_nonzero_of_relationFive a b c d e h₅
  have h₁ : orderTwentyFiveOrbitRelationOne a b c d e = 0 :=
    orderTwentyFiveOrbitRelationOne_eq_zero_of_other_relations
      a b c d e h₀ h₂ h₃ h₄ h₅
  simpa only [a, b, c, d, e] using
    orderTwentyFiveOrbit_threeUnits_of_first_padicVal_eq_zero
      a b c d e ha hb hc hd he h₀ h₁ h₂ h₃ h₄ h₅ hfirst

end MazurTorsion.Kubert
