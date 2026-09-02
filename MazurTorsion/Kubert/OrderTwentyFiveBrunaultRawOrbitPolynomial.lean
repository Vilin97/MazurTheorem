/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationTwoCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFiveCertificate
import MazurTorsion.Kubert.OrderTwentyFiveNormalizedModel

/-!
# Brunault's equation on the checked raw order-twenty-five orbit

The five generated raw identities and the small cyclic completion theorem
supply all six Lécacheux relations.  The orbit certificate then proves
Brunault's equation away from its algebraic exceptional component.
-/

namespace MazurTorsion.Kubert

open OrderTwentyFiveRawOrbitFactorCertificate

private theorem orderTwentyFiveRawOrbit_other_relations_of_openCertificate'
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

/-- The checked raw Sutherland orbit satisfies Brunault's equation once its
first coordinate is known not to lie on the exceptional component. -/
theorem orderTwentyFiveRawOrbit_brunaultPolynomial_eq_zero_of_ne_one
    (r s : ℚ) (hopen : OrderTwentyFiveRawOrbitOpenCertificate r s)
    (hfirst : orderTwentyFiveRawOrbitXZero r s ≠ 1) :
    orderTwentyFiveBrunaultPolynomial
        (orderTwentyFiveRawOrbitXZero r s)
        (-orderTwentyFiveRawOrbitXTwo r s) = 0 := by
  let a := orderTwentyFiveRawOrbitXZero r s
  let b := orderTwentyFiveRawOrbitXOne r s
  let c := orderTwentyFiveRawOrbitXTwo r s
  let d := orderTwentyFiveRawOrbitXThree r s
  let e := orderTwentyFiveRawOrbitXFour r s
  obtain ⟨h₀, h₂, h₃, h₄, h₅⟩ :=
    orderTwentyFiveRawOrbit_other_relations_of_openCertificate' r s hopen
  change orderTwentyFiveOrbitRelationZero a b c d e = 0 at h₀
  change orderTwentyFiveOrbitRelationTwo a b c d e = 0 at h₂
  change orderTwentyFiveOrbitRelationThree a b c d e = 0 at h₃
  change orderTwentyFiveOrbitRelationFour a b c d e = 0 at h₄
  change orderTwentyFiveOrbitRelationFive a b c d e = 0 at h₅
  have h₁ : orderTwentyFiveOrbitRelationOne a b c d e = 0 :=
    orderTwentyFiveOrbitRelationOne_eq_zero_of_other_relations
      a b c d e h₀ h₂ h₃ h₄ h₅
  exact orderTwentyFiveBrunaultPolynomial_eq_zero_of_orbit
    a b c d e (by simpa only [a] using hfirst) h₀ h₁ h₂ h₃ h₄ h₅

end MazurTorsion.Kubert
