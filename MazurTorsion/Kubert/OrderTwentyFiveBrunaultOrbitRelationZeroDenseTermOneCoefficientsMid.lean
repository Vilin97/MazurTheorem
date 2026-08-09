/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermOne

/-!
# Dense term-one coefficient checks 11 through 21
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t1_coefficient_11 (s : ℚ) :
    One.eval T1Stage18C11 s = T1C11 s := by
  norm_num [One.eval, evalWith, T1Stage18C11, T1C11]
  ring

theorem t1_coefficient_12 (s : ℚ) :
    One.eval T1Stage18C12 s = T1C12 s := by
  norm_num [One.eval, evalWith, T1Stage18C12, T1C12]
  ring

theorem t1_coefficient_13 (s : ℚ) :
    One.eval T1Stage18C13 s = T1C13 s := by
  norm_num [One.eval, evalWith, T1Stage18C13, T1C13]
  ring

theorem t1_coefficient_14 (s : ℚ) :
    One.eval T1Stage18C14 s = T1C14 s := by
  norm_num [One.eval, evalWith, T1Stage18C14, T1C14]
  ring

theorem t1_coefficient_15 (s : ℚ) :
    One.eval T1Stage18C15 s = T1C15 s := by
  norm_num [One.eval, evalWith, T1Stage18C15, T1C15]
  ring

theorem t1_coefficient_16 (s : ℚ) :
    One.eval T1Stage18C16 s = T1C16 s := by
  norm_num [One.eval, evalWith, T1Stage18C16, T1C16]
  ring

theorem t1_coefficient_17 (s : ℚ) :
    One.eval T1Stage18C17 s = T1C17 s := by
  norm_num [One.eval, evalWith, T1Stage18C17, T1C17]
  ring

theorem t1_coefficient_18 (s : ℚ) :
    One.eval T1Stage18C18 s = T1C18 s := by
  norm_num [One.eval, evalWith, T1Stage18C18, T1C18]
  ring

theorem t1_coefficient_19 (s : ℚ) :
    One.eval T1Stage18C19 s = T1C19 s := by
  norm_num [One.eval, evalWith, T1Stage18C19, T1C19]
  ring

theorem t1_coefficient_20 (s : ℚ) :
    One.eval T1Stage18C20 s = T1C20 s := by
  norm_num [One.eval, evalWith, T1Stage18C20, T1C20]
  ring

theorem t1_coefficient_21 (s : ℚ) :
    One.eval T1Stage18C21 s = T1C21 s := by
  norm_num [One.eval, evalWith, T1Stage18C21, T1C21]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
