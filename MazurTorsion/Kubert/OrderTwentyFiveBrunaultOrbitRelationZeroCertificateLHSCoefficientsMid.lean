/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateData
import Mathlib.Tactic.Ring

/-!
# Checked left-hand coefficients in outer degrees eleven through twenty-one

This leaf checks a bounded range of the four-term coefficient sums.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem lhs_coefficient_11 (s : ℚ) :
    LC11 s = HC11 s := by
  simp only [LC11, T0C11, T1C11, T2C11, T3C11, HC11]
  ring

theorem lhs_coefficient_12 (s : ℚ) :
    LC12 s = HC12 s := by
  simp only [LC12, T0C12, T1C12, T2C12, T3C12, HC12]
  ring

theorem lhs_coefficient_13 (s : ℚ) :
    LC13 s = HC13 s := by
  simp only [LC13, T0C13, T1C13, T2C13, T3C13, HC13]
  ring

theorem lhs_coefficient_14 (s : ℚ) :
    LC14 s = HC14 s := by
  simp only [LC14, T0C14, T1C14, T2C14, T3C14, HC14]
  ring

theorem lhs_coefficient_15 (s : ℚ) :
    LC15 s = HC15 s := by
  simp only [LC15, T0C15, T1C15, T2C15, T3C15, HC15]
  ring

theorem lhs_coefficient_16 (s : ℚ) :
    LC16 s = HC16 s := by
  simp only [LC16, T0C16, T1C16, T2C16, T3C16, HC16]
  ring

theorem lhs_coefficient_17 (s : ℚ) :
    LC17 s = HC17 s := by
  simp only [LC17, T0C17, T1C17, T2C17, T3C17, HC17]
  ring

theorem lhs_coefficient_18 (s : ℚ) :
    LC18 s = HC18 s := by
  simp only [LC18, T0C18, T1C18, T2C18, T3C18, HC18]
  ring

theorem lhs_coefficient_19 (s : ℚ) :
    LC19 s = HC19 s := by
  simp only [LC19, T0C19, T1C19, T2C19, T3C19, HC19]
  ring

theorem lhs_coefficient_20 (s : ℚ) :
    LC20 s = HC20 s := by
  simp only [LC20, T0C20, T1C20, T2C20, T3C20, HC20]
  ring

theorem lhs_coefficient_21 (s : ℚ) :
    LC21 s = HC21 s := by
  simp only [LC21, T0C21, T1C21, T2C21, T3C21, HC21]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
