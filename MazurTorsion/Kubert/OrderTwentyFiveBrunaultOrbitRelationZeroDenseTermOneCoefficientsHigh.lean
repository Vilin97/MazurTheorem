/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermOne

/-!
# Dense term-one coefficient checks 22 through 32
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial

open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t1_coefficient_22 (s : ℚ) :
    One.eval T1Stage18C22 s = T1C22 s := by
  norm_num [One.eval, evalWith, T1Stage18C22, T1C22]
  ring

theorem t1_coefficient_23 (s : ℚ) :
    One.eval T1Stage18C23 s = T1C23 s := by
  norm_num [One.eval, evalWith, T1Stage18C23, T1C23]
  ring

theorem t1_coefficient_24 (s : ℚ) :
    One.eval T1Stage18C24 s = T1C24 s := by
  norm_num [One.eval, evalWith, T1Stage18C24, T1C24]
  ring

theorem t1_coefficient_25 (s : ℚ) :
    One.eval T1Stage18C25 s = T1C25 s := by
  norm_num [One.eval, evalWith, T1Stage18C25, T1C25]
  ring

theorem t1_coefficient_26 (s : ℚ) :
    One.eval T1Stage18C26 s = T1C26 s := by
  norm_num [One.eval, evalWith, T1Stage18C26, T1C26]
  ring

theorem t1_coefficient_27 (s : ℚ) :
    One.eval T1Stage18C27 s = T1C27 s := by
  norm_num [One.eval, evalWith, T1Stage18C27, T1C27]
  ring

theorem t1_coefficient_28 (s : ℚ) :
    One.eval T1Stage18C28 s = T1C28 s := by
  norm_num [One.eval, evalWith, T1Stage18C28, T1C28]
  ring

theorem t1_coefficient_29 (s : ℚ) :
    One.eval T1Stage18C29 s = T1C29 s := by
  norm_num [One.eval, evalWith, T1Stage18C29, T1C29]
  ring

theorem t1_coefficient_30 (s : ℚ) :
    One.eval T1Stage18C30 s = T1C30 s := by
  norm_num [One.eval, evalWith, T1Stage18C30, T1C30]
  ring

theorem t1_coefficient_31 (s : ℚ) :
    One.eval T1Stage18C31 s = T1C31 s := by
  norm_num [One.eval, evalWith, T1Stage18C31, T1C31]
  ring

theorem t1_coefficient_32 (s : ℚ) :
    One.eval T1Stage18C32 s = T1C32 s := by
  norm_num [One.eval, evalWith, T1Stage18C32, T1C32]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
