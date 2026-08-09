/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermThree

/-!
# Dense term-three coefficient checks 0 through 10
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t3_coefficient_0 (s : ℚ) :
    One.eval T3Stage12C0 s = T3C0 s := by
  norm_num [One.eval, evalWith, T3Stage12C0, T3C0]
  ring

theorem t3_coefficient_1 (s : ℚ) :
    One.eval T3Stage12C1 s = T3C1 s := by
  norm_num [One.eval, evalWith, T3Stage12C1, T3C1]
  ring

theorem t3_coefficient_2 (s : ℚ) :
    One.eval T3Stage12C2 s = T3C2 s := by
  norm_num [One.eval, evalWith, T3Stage12C2, T3C2]
  ring

theorem t3_coefficient_3 (s : ℚ) :
    One.eval T3Stage12C3 s = T3C3 s := by
  norm_num [One.eval, evalWith, T3Stage12C3, T3C3]
  ring

theorem t3_coefficient_4 (s : ℚ) :
    One.eval T3Stage12C4 s = T3C4 s := by
  norm_num [One.eval, evalWith, T3Stage12C4, T3C4]
  ring

theorem t3_coefficient_5 (s : ℚ) :
    One.eval T3Stage12C5 s = T3C5 s := by
  norm_num [One.eval, evalWith, T3Stage12C5, T3C5]
  ring

theorem t3_coefficient_6 (s : ℚ) :
    One.eval T3Stage12C6 s = T3C6 s := by
  norm_num [One.eval, evalWith, T3Stage12C6, T3C6]
  ring

theorem t3_coefficient_7 (s : ℚ) :
    One.eval T3Stage12C7 s = T3C7 s := by
  norm_num [One.eval, evalWith, T3Stage12C7, T3C7]
  ring

theorem t3_coefficient_8 (s : ℚ) :
    One.eval T3Stage12C8 s = T3C8 s := by
  norm_num [One.eval, evalWith, T3Stage12C8, T3C8]
  ring

theorem t3_coefficient_9 (s : ℚ) :
    One.eval T3Stage12C9 s = T3C9 s := by
  norm_num [One.eval, evalWith, T3Stage12C9, T3C9]
  ring

theorem t3_coefficient_10 (s : ℚ) :
    One.eval T3Stage12C10 s = T3C10 s := by
  norm_num [One.eval, evalWith, T3Stage12C10, T3C10]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
