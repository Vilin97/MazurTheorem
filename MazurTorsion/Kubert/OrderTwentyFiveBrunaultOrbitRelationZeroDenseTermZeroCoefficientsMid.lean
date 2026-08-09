/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroDenseTermZeroC

/-!
# Dense term-zero coefficients eleven through twenty-one

Each generated integer row is checked against the corresponding symbolic coefficient.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Internal

theorem t0_coefficient_11 (s : ℚ) :
    One.eval T0Stage15C11 s = T0C11 s := by
  norm_num [One.eval, evalWith, T0Stage15C11, T0C11]
  ring

theorem t0_coefficient_12 (s : ℚ) :
    One.eval T0Stage15C12 s = T0C12 s := by
  norm_num [One.eval, evalWith, T0Stage15C12, T0C12]
  ring

theorem t0_coefficient_13 (s : ℚ) :
    One.eval T0Stage15C13 s = T0C13 s := by
  norm_num [One.eval, evalWith, T0Stage15C13, T0C13]
  ring

theorem t0_coefficient_14 (s : ℚ) :
    One.eval T0Stage15C14 s = T0C14 s := by
  norm_num [One.eval, evalWith, T0Stage15C14, T0C14]
  ring

theorem t0_coefficient_15 (s : ℚ) :
    One.eval T0Stage15C15 s = T0C15 s := by
  norm_num [One.eval, evalWith, T0Stage15C15, T0C15]
  ring

theorem t0_coefficient_16 (s : ℚ) :
    One.eval T0Stage15C16 s = T0C16 s := by
  norm_num [One.eval, evalWith, T0Stage15C16, T0C16]
  ring

theorem t0_coefficient_17 (s : ℚ) :
    One.eval T0Stage15C17 s = T0C17 s := by
  norm_num [One.eval, evalWith, T0Stage15C17, T0C17]
  ring

theorem t0_coefficient_18 (s : ℚ) :
    One.eval T0Stage15C18 s = T0C18 s := by
  norm_num [One.eval, evalWith, T0Stage15C18, T0C18]
  ring

theorem t0_coefficient_19 (s : ℚ) :
    One.eval T0Stage15C19 s = T0C19 s := by
  norm_num [One.eval, evalWith, T0Stage15C19, T0C19]
  ring

theorem t0_coefficient_20 (s : ℚ) :
    One.eval T0Stage15C20 s = T0C20 s := by
  norm_num [One.eval, evalWith, T0Stage15C20, T0C20]
  ring

theorem t0_coefficient_21 (s : ℚ) :
    One.eval T0Stage15C21 s = T0C21 s := by
  norm_num [One.eval, evalWith, T0Stage15C21, T0C21]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Dense
