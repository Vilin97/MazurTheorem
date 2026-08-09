/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermOne

/-!
# Dense term-one coefficient checks 0 through 10
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t1_coefficient_0 (s : ℚ) :
    One.eval T1Stage18C0 s = T1C0 s := by
  norm_num [One.eval, evalWith, T1Stage18C0, T1C0]

theorem t1_coefficient_1 (s : ℚ) :
    One.eval T1Stage18C1 s = T1C1 s := by
  norm_num [One.eval, evalWith, T1Stage18C1, T1C1]

theorem t1_coefficient_2 (s : ℚ) :
    One.eval T1Stage18C2 s = T1C2 s := by
  norm_num [One.eval, evalWith, T1Stage18C2, T1C2]
  ring

theorem t1_coefficient_3 (s : ℚ) :
    One.eval T1Stage18C3 s = T1C3 s := by
  norm_num [One.eval, evalWith, T1Stage18C3, T1C3]
  ring

theorem t1_coefficient_4 (s : ℚ) :
    One.eval T1Stage18C4 s = T1C4 s := by
  norm_num [One.eval, evalWith, T1Stage18C4, T1C4]
  ring

theorem t1_coefficient_5 (s : ℚ) :
    One.eval T1Stage18C5 s = T1C5 s := by
  norm_num [One.eval, evalWith, T1Stage18C5, T1C5]
  ring

theorem t1_coefficient_6 (s : ℚ) :
    One.eval T1Stage18C6 s = T1C6 s := by
  norm_num [One.eval, evalWith, T1Stage18C6, T1C6]
  ring

theorem t1_coefficient_7 (s : ℚ) :
    One.eval T1Stage18C7 s = T1C7 s := by
  norm_num [One.eval, evalWith, T1Stage18C7, T1C7]
  ring

theorem t1_coefficient_8 (s : ℚ) :
    One.eval T1Stage18C8 s = T1C8 s := by
  norm_num [One.eval, evalWith, T1Stage18C8, T1C8]
  ring

theorem t1_coefficient_9 (s : ℚ) :
    One.eval T1Stage18C9 s = T1C9 s := by
  norm_num [One.eval, evalWith, T1Stage18C9, T1C9]
  ring

theorem t1_coefficient_10 (s : ℚ) :
    One.eval T1Stage18C10 s = T1C10 s := by
  norm_num [One.eval, evalWith, T1Stage18C10, T1C10]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
