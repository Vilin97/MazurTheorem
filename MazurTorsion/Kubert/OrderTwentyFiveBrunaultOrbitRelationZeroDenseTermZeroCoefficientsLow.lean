/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermZeroC

/-!
# Dense term-zero coefficients zero through ten

Each generated integer row is checked against the corresponding symbolic coefficient.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t0_coefficient_0 (s : ℚ) :
    One.eval T0Stage15C0 s = T0C0 s := by
  norm_num [One.eval, evalWith, T0Stage15C0, T0C0]

theorem t0_coefficient_1 (s : ℚ) :
    One.eval T0Stage15C1 s = T0C1 s := by
  norm_num [One.eval, evalWith, T0Stage15C1, T0C1]
  ring

theorem t0_coefficient_2 (s : ℚ) :
    One.eval T0Stage15C2 s = T0C2 s := by
  norm_num [One.eval, evalWith, T0Stage15C2, T0C2]
  ring

theorem t0_coefficient_3 (s : ℚ) :
    One.eval T0Stage15C3 s = T0C3 s := by
  norm_num [One.eval, evalWith, T0Stage15C3, T0C3]
  ring

theorem t0_coefficient_4 (s : ℚ) :
    One.eval T0Stage15C4 s = T0C4 s := by
  norm_num [One.eval, evalWith, T0Stage15C4, T0C4]
  ring

theorem t0_coefficient_5 (s : ℚ) :
    One.eval T0Stage15C5 s = T0C5 s := by
  norm_num [One.eval, evalWith, T0Stage15C5, T0C5]
  ring

theorem t0_coefficient_6 (s : ℚ) :
    One.eval T0Stage15C6 s = T0C6 s := by
  norm_num [One.eval, evalWith, T0Stage15C6, T0C6]
  ring

theorem t0_coefficient_7 (s : ℚ) :
    One.eval T0Stage15C7 s = T0C7 s := by
  norm_num [One.eval, evalWith, T0Stage15C7, T0C7]
  ring

theorem t0_coefficient_8 (s : ℚ) :
    One.eval T0Stage15C8 s = T0C8 s := by
  norm_num [One.eval, evalWith, T0Stage15C8, T0C8]
  ring

theorem t0_coefficient_9 (s : ℚ) :
    One.eval T0Stage15C9 s = T0C9 s := by
  norm_num [One.eval, evalWith, T0Stage15C9, T0C9]
  ring

theorem t0_coefficient_10 (s : ℚ) :
    One.eval T0Stage15C10 s = T0C10 s := by
  norm_num [One.eval, evalWith, T0Stage15C10, T0C10]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
