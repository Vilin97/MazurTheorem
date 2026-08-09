/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermZeroC

/-!
# Dense term-zero coefficients twenty-two through thirty-two

Each generated integer row is checked against the corresponding symbolic coefficient.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t0_coefficient_22 (s : ℚ) :
    One.eval T0Stage15C22 s = T0C22 s := by
  norm_num [One.eval, evalWith, T0Stage15C22, T0C22]
  ring

theorem t0_coefficient_23 (s : ℚ) :
    One.eval T0Stage15C23 s = T0C23 s := by
  norm_num [One.eval, evalWith, T0Stage15C23, T0C23]
  ring

theorem t0_coefficient_24 (s : ℚ) :
    One.eval T0Stage15C24 s = T0C24 s := by
  norm_num [One.eval, evalWith, T0Stage15C24, T0C24]
  ring

theorem t0_coefficient_25 (s : ℚ) :
    One.eval T0Stage15C25 s = T0C25 s := by
  norm_num [One.eval, evalWith, T0Stage15C25, T0C25]
  ring

theorem t0_coefficient_26 (s : ℚ) :
    One.eval T0Stage15C26 s = T0C26 s := by
  norm_num [One.eval, evalWith, T0Stage15C26, T0C26]
  ring

theorem t0_coefficient_27 (s : ℚ) :
    One.eval T0Stage15C27 s = T0C27 s := by
  norm_num [One.eval, evalWith, T0Stage15C27, T0C27]
  ring

theorem t0_coefficient_28 (s : ℚ) :
    One.eval T0Stage15C28 s = T0C28 s := by
  norm_num [One.eval, evalWith, T0Stage15C28, T0C28]
  ring

theorem t0_coefficient_29 (s : ℚ) :
    One.eval T0Stage15C29 s = T0C29 s := by
  norm_num [One.eval, evalWith, T0Stage15C29, T0C29]
  ring

theorem t0_coefficient_30 (s : ℚ) :
    One.eval T0Stage15C30 s = T0C30 s := by
  norm_num [One.eval, evalWith, T0Stage15C30, T0C30]
  ring

theorem t0_coefficient_31 (s : ℚ) :
    One.eval T0Stage15C31 s = T0C31 s := by
  norm_num [One.eval, evalWith, T0Stage15C31, T0C31]
  ring

theorem t0_coefficient_32 (s : ℚ) :
    One.eval T0Stage15C32 s = T0C32 s := by
  norm_num [One.eval, evalWith, T0Stage15C32, T0C32]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
