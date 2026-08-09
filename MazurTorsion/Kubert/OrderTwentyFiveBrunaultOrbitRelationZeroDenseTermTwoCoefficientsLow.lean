/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermTwo

/-!
# Dense term-two coefficient checks 0 through 10
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t2_coefficient_0 (s : ℚ) :
    One.eval T2Stage20C0 s = T2C0 s := by
  norm_num [One.eval, evalWith, T2Stage20C0, T2C0]

theorem t2_coefficient_1 (s : ℚ) :
    One.eval T2Stage20C1 s = T2C1 s := by
  norm_num [One.eval, evalWith, T2Stage20C1, T2C1]

theorem t2_coefficient_2 (s : ℚ) :
    One.eval T2Stage20C2 s = T2C2 s := by
  norm_num [One.eval, evalWith, T2Stage20C2, T2C2]
  ring

theorem t2_coefficient_3 (s : ℚ) :
    One.eval T2Stage20C3 s = T2C3 s := by
  norm_num [One.eval, evalWith, T2Stage20C3, T2C3]
  ring

theorem t2_coefficient_4 (s : ℚ) :
    One.eval T2Stage20C4 s = T2C4 s := by
  norm_num [One.eval, evalWith, T2Stage20C4, T2C4]
  ring

theorem t2_coefficient_5 (s : ℚ) :
    One.eval T2Stage20C5 s = T2C5 s := by
  norm_num [One.eval, evalWith, T2Stage20C5, T2C5]
  ring

theorem t2_coefficient_6 (s : ℚ) :
    One.eval T2Stage20C6 s = T2C6 s := by
  norm_num [One.eval, evalWith, T2Stage20C6, T2C6]
  ring

theorem t2_coefficient_7 (s : ℚ) :
    One.eval T2Stage20C7 s = T2C7 s := by
  norm_num [One.eval, evalWith, T2Stage20C7, T2C7]
  ring

theorem t2_coefficient_8 (s : ℚ) :
    One.eval T2Stage20C8 s = T2C8 s := by
  norm_num [One.eval, evalWith, T2Stage20C8, T2C8]
  ring

theorem t2_coefficient_9 (s : ℚ) :
    One.eval T2Stage20C9 s = T2C9 s := by
  norm_num [One.eval, evalWith, T2Stage20C9, T2C9]
  ring

theorem t2_coefficient_10 (s : ℚ) :
    One.eval T2Stage20C10 s = T2C10 s := by
  norm_num [One.eval, evalWith, T2Stage20C10, T2C10]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
