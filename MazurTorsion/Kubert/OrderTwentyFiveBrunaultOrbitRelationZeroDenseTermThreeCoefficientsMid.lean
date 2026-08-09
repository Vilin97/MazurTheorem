/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermThree

/-!
# Dense term-three coefficient checks 11 through 21
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t3_coefficient_11 (s : ℚ) :
    One.eval T3Stage12C11 s = T3C11 s := by
  norm_num [One.eval, evalWith, T3Stage12C11, T3C11]
  ring

theorem t3_coefficient_12 (s : ℚ) :
    One.eval T3Stage12C12 s = T3C12 s := by
  norm_num [One.eval, evalWith, T3Stage12C12, T3C12]
  ring

theorem t3_coefficient_13 (s : ℚ) :
    One.eval T3Stage12C13 s = T3C13 s := by
  norm_num [One.eval, evalWith, T3Stage12C13, T3C13]
  ring

theorem t3_coefficient_14 (s : ℚ) :
    One.eval T3Stage12C14 s = T3C14 s := by
  norm_num [One.eval, evalWith, T3Stage12C14, T3C14]
  ring

theorem t3_coefficient_15 (s : ℚ) :
    One.eval T3Stage12C15 s = T3C15 s := by
  norm_num [One.eval, evalWith, T3Stage12C15, T3C15]
  ring

theorem t3_coefficient_16 (s : ℚ) :
    One.eval T3Stage12C16 s = T3C16 s := by
  norm_num [One.eval, evalWith, T3Stage12C16, T3C16]
  ring

theorem t3_coefficient_17 (s : ℚ) :
    One.eval T3Stage12C17 s = T3C17 s := by
  norm_num [One.eval, evalWith, T3Stage12C17, T3C17]
  ring

theorem t3_coefficient_18 (s : ℚ) :
    One.eval T3Stage12C18 s = T3C18 s := by
  norm_num [One.eval, evalWith, T3Stage12C18, T3C18]
  ring

theorem t3_coefficient_19 (s : ℚ) :
    One.eval T3Stage12C19 s = T3C19 s := by
  norm_num [One.eval, evalWith, T3Stage12C19, T3C19]
  ring

theorem t3_coefficient_20 (s : ℚ) :
    One.eval T3Stage12C20 s = T3C20 s := by
  norm_num [One.eval, evalWith, T3Stage12C20, T3C20]
  ring

theorem t3_coefficient_21 (s : ℚ) :
    One.eval T3Stage12C21 s = T3C21 s := by
  norm_num [One.eval, evalWith, T3Stage12C21, T3C21]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
