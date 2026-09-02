/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockThreeRowZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockThreeRowOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockThreeRowTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockThreeRowThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockThreeRowFour

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

private theorem eq_of_take_eq_and_drop_eq (n : ℕ) {xs ys : List α}
    (hTake : xs.take n = ys.take n) (hDrop : xs.drop n = ys.drop n) :
    xs = ys := by
  calc
    xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n ++ ys.drop n := by rw [hTake, hDrop]
    _ = ys := List.take_append_drop n ys

theorem certificateBlockThree :
    leftTailThree.take 5 = rightTailThree.take 5 := by
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockThreeRowZero
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockThreeRowOne
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockThreeRowTwo
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockThreeRowThree
  exact certificateBlockThreeRowFour

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate
