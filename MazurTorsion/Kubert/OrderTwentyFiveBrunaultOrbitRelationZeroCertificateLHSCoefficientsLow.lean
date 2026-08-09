/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateData
import Mathlib.Tactic.Ring

/-!
# Checked left-hand coefficients in outer degrees zero through ten

This leaf checks a bounded range of the four-term coefficient sums.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem lhs_coefficient_0 (s : ℚ) :
    LC0 s = HC0 s := by
  simp only [LC0, T0C0, T1C0, T2C0, T3C0, HC0]
  ring

theorem lhs_coefficient_1 (s : ℚ) :
    LC1 s = HC1 s := by
  simp only [LC1, T0C1, T1C1, T2C1, T3C1, HC1]
  ring

theorem lhs_coefficient_2 (s : ℚ) :
    LC2 s = HC2 s := by
  simp only [LC2, T0C2, T1C2, T2C2, T3C2, HC2]
  ring

theorem lhs_coefficient_3 (s : ℚ) :
    LC3 s = HC3 s := by
  simp only [LC3, T0C3, T1C3, T2C3, T3C3, HC3]
  ring

theorem lhs_coefficient_4 (s : ℚ) :
    LC4 s = HC4 s := by
  simp only [LC4, T0C4, T1C4, T2C4, T3C4, HC4]
  ring

theorem lhs_coefficient_5 (s : ℚ) :
    LC5 s = HC5 s := by
  simp only [LC5, T0C5, T1C5, T2C5, T3C5, HC5]
  ring

theorem lhs_coefficient_6 (s : ℚ) :
    LC6 s = HC6 s := by
  simp only [LC6, T0C6, T1C6, T2C6, T3C6, HC6]
  ring

theorem lhs_coefficient_7 (s : ℚ) :
    LC7 s = HC7 s := by
  simp only [LC7, T0C7, T1C7, T2C7, T3C7, HC7]
  ring

theorem lhs_coefficient_8 (s : ℚ) :
    LC8 s = HC8 s := by
  simp only [LC8, T0C8, T1C8, T2C8, T3C8, HC8]
  ring

theorem lhs_coefficient_9 (s : ℚ) :
    LC9 s = HC9 s := by
  simp only [LC9, T0C9, T1C9, T2C9, T3C9, HC9]
  ring

theorem lhs_coefficient_10 (s : ℚ) :
    LC10 s = HC10 s := by
  simp only [LC10, T0C10, T1C10, T2C10, T3C10, HC10]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
