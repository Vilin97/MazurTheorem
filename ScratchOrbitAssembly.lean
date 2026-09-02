import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import Mathlib.Tactic.LinearCombination

namespace ScratchOrbitAssembly

open MazurTorsion.Kubert

private theorem relation_one_of_others
    (a b c d e : ℚ) (ha : a ≠ 0)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    orderTwentyFiveOrbitRelationOne a b c d e = 0 := by
  have hidentity :
      a * orderTwentyFiveOrbitRelationOne a b c d e =
        -orderTwentyFiveOrbitRelationZero a b c d e -
          a * b * orderTwentyFiveOrbitRelationTwo a b c d e -
          a * b * c * orderTwentyFiveOrbitRelationThree a b c d e -
          a * b * c * d * orderTwentyFiveOrbitRelationFour a b c d e -
          (a - c) * orderTwentyFiveOrbitRelationFive a b c d e := by
    simp only [orderTwentyFiveOrbitRelationZero,
      orderTwentyFiveOrbitRelationOne, orderTwentyFiveOrbitRelationTwo,
      orderTwentyFiveOrbitRelationThree, orderTwentyFiveOrbitRelationFour,
      orderTwentyFiveOrbitRelationFive]
    ring
  have hmul : a * orderTwentyFiveOrbitRelationOne a b c d e = 0 := by
    rw [hidentity, h0, h2, h3, h4, h5]
    ring
  exact (mul_eq_zero.mp hmul).resolve_left ha

theorem unit_relations_to_orbit
    (y1 y2 y4 y8 y9 : ℚ)
    (hy1 : y1 ≠ 0) (hy4 : y4 ≠ 0)
    (hu0 : y1 - y9 - y1 * y8 * (y2 - y1) = 0)
    (hu2 : y4 - y2 - y4 * y1 * (y8 - y4) = 0)
    (hu3 : y8 - y4 - y8 * y2 * (y9 - y8) = 0)
    (hu4 : y9 - y8 - y9 * y4 * (y1 - y9) = 0)
    (hu5 : y1 * y2 * y4 * y8 * y9 - 1 = 0) :
    let a := y1 * y4
    let b := y2 * y8
    let c := y4 * y9
    let d := y8 * y1
    let e := y9 * y2
    orderTwentyFiveOrbitRelationZero a b c d e = 0 ∧
      orderTwentyFiveOrbitRelationOne a b c d e = 0 ∧
      orderTwentyFiveOrbitRelationTwo a b c d e = 0 ∧
      orderTwentyFiveOrbitRelationThree a b c d e = 0 ∧
      orderTwentyFiveOrbitRelationFour a b c d e = 0 ∧
      orderTwentyFiveOrbitRelationFive a b c d e = 0 := by
  dsimp only
  have h0 : orderTwentyFiveOrbitRelationZero
      (y1 * y4) (y2 * y8) (y4 * y9) (y8 * y1) (y9 * y2) = 0 := by
    simp only [orderTwentyFiveOrbitRelationZero]
    linear_combination y4 * hu0
  have h2 : orderTwentyFiveOrbitRelationTwo
      (y1 * y4) (y2 * y8) (y4 * y9) (y8 * y1) (y9 * y2) = 0 := by
    simp only [orderTwentyFiveOrbitRelationTwo]
    linear_combination y9 * hu2
  have h3 : orderTwentyFiveOrbitRelationThree
      (y1 * y4) (y2 * y8) (y4 * y9) (y8 * y1) (y9 * y2) = 0 := by
    simp only [orderTwentyFiveOrbitRelationThree]
    linear_combination y1 * hu3
  have h4 : orderTwentyFiveOrbitRelationFour
      (y1 * y4) (y2 * y8) (y4 * y9) (y8 * y1) (y9 * y2) = 0 := by
    simp only [orderTwentyFiveOrbitRelationFour]
    linear_combination y2 * hu4
  have hp : y1 * y2 * y4 * y8 * y9 = 1 := sub_eq_zero.mp hu5
  have h5 : orderTwentyFiveOrbitRelationFive
      (y1 * y4) (y2 * y8) (y4 * y9) (y8 * y1) (y9 * y2) = 0 := by
    simp only [orderTwentyFiveOrbitRelationFive]
    rw [show (y1 * y4) * (y2 * y8) * (y4 * y9) * (y8 * y1) * (y9 * y2) =
      (y1 * y2 * y4 * y8 * y9) ^ 2 by ring, hp]
    norm_num
  have h1 := relation_one_of_others
    (y1 * y4) (y2 * y8) (y4 * y9) (y8 * y1) (y9 * y2)
    (mul_ne_zero hy1 hy4) h0 h2 h3 h4 h5
  exact ⟨h0, h1, h2, h3, h4, h5⟩

end ScratchOrbitAssembly
