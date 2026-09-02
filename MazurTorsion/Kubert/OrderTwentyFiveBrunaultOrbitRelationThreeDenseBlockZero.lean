/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockZeroRowZero
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockZeroRowOne
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockZeroRowTwo
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockZeroRowThree
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseBlockZeroRowFour

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

private theorem eq_of_take_eq_and_drop_eq (n : ℕ) {xs ys : List α}
    (hTake : xs.take n = ys.take n) (hDrop : xs.drop n = ys.drop n) :
    xs = ys := by
  calc
    xs = xs.take n ++ xs.drop n := (List.take_append_drop n xs).symm
    _ = ys.take n ++ ys.drop n := by rw [hTake, hDrop]
    _ = ys := List.take_append_drop n ys

theorem certificateBlockZero :
    leftCertificate.take 5 = rightCertificate.take 5 := by
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockZeroRowZero
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockZeroRowOne
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockZeroRowTwo
  apply eq_of_take_eq_and_drop_eq 1 certificateBlockZeroRowThree
  exact certificateBlockZeroRowFour

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate
