/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockSixRowZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockSixRowOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockSixRowTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockSixRowThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockSixRowFour

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

private theorem eq_of_take_eq_and_drop_eq (n : ℕ) {xs ys : List α}
    (hTake : xs.take n = ys.take n) (hDrop : xs.drop n = ys.drop n) :
    xs = ys := by
  calc
    xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n ++ ys.drop n := by rw [hTake, hDrop]
    _ = ys := List.take_append_drop n ys

theorem certificateBlockSix : leftTailSix = rightTailSix := by
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockSixRowZero
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockSixRowOne
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockSixRowTwo
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockSixRowThree
  exact certificateBlockSixRowFour

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate
