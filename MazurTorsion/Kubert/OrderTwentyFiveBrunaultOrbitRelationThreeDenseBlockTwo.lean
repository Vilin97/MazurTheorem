/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockTwoRowZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockTwoRowOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockTwoRowTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockTwoRowThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockTwoRowFour

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

private theorem eq_of_take_eq_and_drop_eq (n : ℕ) {xs ys : List α}
    (hTake : xs.take n = ys.take n) (hDrop : xs.drop n = ys.drop n) :
    xs = ys := by
  calc
    xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n ++ ys.drop n := by rw [hTake, hDrop]
    _ = ys := List.take_append_drop n ys

theorem certificateBlockTwo :
    leftTailTwo.take 5 = rightTailTwo.take 5 := by
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockTwoRowZero
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockTwoRowOne
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockTwoRowTwo
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockTwoRowThree
  exact certificateBlockTwoRowFour

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate
