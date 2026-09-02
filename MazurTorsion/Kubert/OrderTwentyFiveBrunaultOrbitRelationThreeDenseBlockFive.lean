/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockFiveRowZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockFiveRowOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockFiveRowTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockFiveRowThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockFiveRowFour

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

private theorem eq_of_take_eq_and_drop_eq (n : ℕ) {xs ys : List α}
    (hTake : xs.take n = ys.take n) (hDrop : xs.drop n = ys.drop n) :
    xs = ys := by
  calc
    xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n ++ ys.drop n := by rw [hTake, hDrop]
    _ = ys := List.take_append_drop n ys

theorem certificateBlockFive :
    leftTailFive.take 5 = rightTailFive.take 5 := by
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockFiveRowZero
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockFiveRowOne
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockFiveRowTwo
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockFiveRowThree
  exact certificateBlockFiveRowFour

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate
