/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockFour
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockFive
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockSix

/-! # Assembly of the sharded fourth-relation coefficient certificate -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

open OrderTwentyFiveDensePolynomial
open Internal

private theorem eq_of_take_eq_and_drop_eq (n : ℕ) {xs ys : List α}
    (hTake : xs.take n = ys.take n) (hDrop : xs.drop n = ys.drop n) :
    xs = ys := by
  calc
    xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n ++ ys.drop n := by rw [hTake, hDrop]
    _ = ys := List.take_append_drop n ys

private theorem closed_coefficient_certificate :
    leftCertificate = rightCertificate := by
  apply eq_of_take_eq_and_drop_eq 5 certificateBlockZero
  change leftTailOne = rightTailOne
  apply eq_of_take_eq_and_drop_eq 5 certificateBlockOne
  change leftTailTwo = rightTailTwo
  apply eq_of_take_eq_and_drop_eq 5 certificateBlockTwo
  change leftTailThree = rightTailThree
  apply eq_of_take_eq_and_drop_eq 5 certificateBlockThree
  change leftTailFour = rightTailFour
  apply eq_of_take_eq_and_drop_eq 5 certificateBlockFour
  change leftTailFive = rightTailFive
  apply eq_of_take_eq_and_drop_eq 5 certificateBlockFive
  change leftTailSix = rightTailSix
  exact certificateBlockSix

private theorem evaluated_coefficient_certificate (r s : ℚ) :
    Two.eval relationThreePolynomial r s = Two.eval certificateProduct r s := by
  have h := congrArg (fun p => Two.eval p r s) closed_coefficient_certificate
  simpa only [leftCertificate, rightCertificate, eval_rectangularize] using h

/-- The cleared factor expression for the fourth cyclic relation vanishes on
Sutherland's raw order-twenty-five curve. -/
theorem clearedRelationThree_eq_zero_of_sutherland (r s : ℚ)
    (hF : orderTwentyFiveRawSutherlandF r s = 0) :
    clearedRelationThree r s = 0 := by
  have hcertificate := evaluated_coefficient_certificate r s
  rw [eval_relationThreePolynomial, certificateProduct, Two.eval_mul,
    eval_sutherlandPolynomial, hF, zero_mul] at hcertificate
  exact hcertificate

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate
