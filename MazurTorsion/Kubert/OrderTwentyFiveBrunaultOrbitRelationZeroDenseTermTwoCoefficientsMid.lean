/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermTwo

/-!
# Dense term-two coefficient checks 11 through 21
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t2_coefficient_11 (s : ℚ) :
    One.eval T2Stage20C11 s = T2C11 s := by
  norm_num [One.eval, evalWith, T2Stage20C11, T2C11]
  ring

theorem t2_coefficient_12 (s : ℚ) :
    One.eval T2Stage20C12 s = T2C12 s := by
  norm_num [One.eval, evalWith, T2Stage20C12, T2C12]
  ring

theorem t2_coefficient_13 (s : ℚ) :
    One.eval T2Stage20C13 s = T2C13 s := by
  norm_num [One.eval, evalWith, T2Stage20C13, T2C13]
  ring

theorem t2_coefficient_14 (s : ℚ) :
    One.eval T2Stage20C14 s = T2C14 s := by
  norm_num [One.eval, evalWith, T2Stage20C14, T2C14]
  ring

theorem t2_coefficient_15 (s : ℚ) :
    One.eval T2Stage20C15 s = T2C15 s := by
  norm_num [One.eval, evalWith, T2Stage20C15, T2C15]
  ring

theorem t2_coefficient_16 (s : ℚ) :
    One.eval T2Stage20C16 s = T2C16 s := by
  norm_num [One.eval, evalWith, T2Stage20C16, T2C16]
  ring

theorem t2_coefficient_17 (s : ℚ) :
    One.eval T2Stage20C17 s = T2C17 s := by
  norm_num [One.eval, evalWith, T2Stage20C17, T2C17]
  ring

theorem t2_coefficient_18 (s : ℚ) :
    One.eval T2Stage20C18 s = T2C18 s := by
  norm_num [One.eval, evalWith, T2Stage20C18, T2C18]
  ring

theorem t2_coefficient_19 (s : ℚ) :
    One.eval T2Stage20C19 s = T2C19 s := by
  norm_num [One.eval, evalWith, T2Stage20C19, T2C19]
  ring

theorem t2_coefficient_20 (s : ℚ) :
    One.eval T2Stage20C20 s = T2C20 s := by
  norm_num [One.eval, evalWith, T2Stage20C20, T2C20]
  ring

theorem t2_coefficient_21 (s : ℚ) :
    One.eval T2Stage20C21 s = T2C21 s := by
  norm_num [One.eval, evalWith, T2Stage20C21, T2C21]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
