/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockOneRowZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockOneRowOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockOneRowTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockOneRowThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockOneRowFour

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

private theorem eq_of_take_eq_and_drop_eq (n : ℕ) {xs ys : List α}
    (hTake : xs.take n = ys.take n) (hDrop : xs.drop n = ys.drop n) :
    xs = ys := by
  calc
    xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n ++ ys.drop n := by rw [hTake, hDrop]
    _ = ys := List.take_append_drop n ys

theorem certificateBlockOne :
    leftTailOne.take 5 = rightTailOne.take 5 := by
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockOneRowZero
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockOneRowOne
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockOneRowTwo
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockOneRowThree
  exact certificateBlockOneRowFour

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate
