/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermTwo

/-!
# Dense term-two coefficient checks 22 through 31
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t2_coefficient_22 (s : ℚ) :
    One.eval T2Stage20C22 s = T2C22 s := by
  norm_num [One.eval, evalWith, T2Stage20C22, T2C22]
  ring

theorem t2_coefficient_23 (s : ℚ) :
    One.eval T2Stage20C23 s = T2C23 s := by
  norm_num [One.eval, evalWith, T2Stage20C23, T2C23]
  ring

theorem t2_coefficient_24 (s : ℚ) :
    One.eval T2Stage20C24 s = T2C24 s := by
  norm_num [One.eval, evalWith, T2Stage20C24, T2C24]
  ring

theorem t2_coefficient_25 (s : ℚ) :
    One.eval T2Stage20C25 s = T2C25 s := by
  norm_num [One.eval, evalWith, T2Stage20C25, T2C25]
  ring

theorem t2_coefficient_26 (s : ℚ) :
    One.eval T2Stage20C26 s = T2C26 s := by
  norm_num [One.eval, evalWith, T2Stage20C26, T2C26]
  ring

theorem t2_coefficient_27 (s : ℚ) :
    One.eval T2Stage20C27 s = T2C27 s := by
  norm_num [One.eval, evalWith, T2Stage20C27, T2C27]
  ring

theorem t2_coefficient_28 (s : ℚ) :
    One.eval T2Stage20C28 s = T2C28 s := by
  norm_num [One.eval, evalWith, T2Stage20C28, T2C28]
  ring

theorem t2_coefficient_29 (s : ℚ) :
    One.eval T2Stage20C29 s = T2C29 s := by
  norm_num [One.eval, evalWith, T2Stage20C29, T2C29]
  ring

theorem t2_coefficient_30 (s : ℚ) :
    One.eval T2Stage20C30 s = T2C30 s := by
  norm_num [One.eval, evalWith, T2Stage20C30, T2C30]
  ring

theorem t2_coefficient_31 (s : ℚ) :
    One.eval T2Stage20C31 s = T2C31 s := by
  norm_num [One.eval, evalWith, T2Stage20C31, T2C31]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
