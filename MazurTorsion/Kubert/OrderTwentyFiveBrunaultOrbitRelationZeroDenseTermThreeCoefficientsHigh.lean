/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermThree

/-!
# Dense term-three coefficient checks 22 through 32
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t3_coefficient_22 (s : ℚ) :
    One.eval T3Stage12C22 s = T3C22 s := by
  norm_num [One.eval, evalWith, T3Stage12C22, T3C22]
  ring

theorem t3_coefficient_23 (s : ℚ) :
    One.eval T3Stage12C23 s = T3C23 s := by
  norm_num [One.eval, evalWith, T3Stage12C23, T3C23]
  ring

theorem t3_coefficient_24 (s : ℚ) :
    One.eval T3Stage12C24 s = T3C24 s := by
  norm_num [One.eval, evalWith, T3Stage12C24, T3C24]
  ring

theorem t3_coefficient_25 (s : ℚ) :
    One.eval T3Stage12C25 s = T3C25 s := by
  norm_num [One.eval, evalWith, T3Stage12C25, T3C25]
  ring

theorem t3_coefficient_26 (s : ℚ) :
    One.eval T3Stage12C26 s = T3C26 s := by
  norm_num [One.eval, evalWith, T3Stage12C26, T3C26]
  ring

theorem t3_coefficient_27 (s : ℚ) :
    One.eval T3Stage12C27 s = T3C27 s := by
  norm_num [One.eval, evalWith, T3Stage12C27, T3C27]
  ring

theorem t3_coefficient_28 (s : ℚ) :
    One.eval T3Stage12C28 s = T3C28 s := by
  norm_num [One.eval, evalWith, T3Stage12C28, T3C28]
  ring

theorem t3_coefficient_29 (s : ℚ) :
    One.eval T3Stage12C29 s = T3C29 s := by
  norm_num [One.eval, evalWith, T3Stage12C29, T3C29]
  ring

theorem t3_coefficient_30 (s : ℚ) :
    One.eval T3Stage12C30 s = T3C30 s := by
  norm_num [One.eval, evalWith, T3Stage12C30, T3C30]
  ring

theorem t3_coefficient_31 (s : ℚ) :
    One.eval T3Stage12C31 s = T3C31 s := by
  norm_num [One.eval, evalWith, T3Stage12C31, T3C31]
  ring

theorem t3_coefficient_32 (s : ℚ) :
    One.eval T3Stage12C32 s = T3C32 s := by
  norm_num [One.eval, evalWith, T3Stage12C32, T3C32]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
