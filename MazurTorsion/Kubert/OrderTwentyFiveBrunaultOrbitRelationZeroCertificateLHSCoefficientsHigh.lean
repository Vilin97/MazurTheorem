/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationZeroCertificateData
import Mathlib.Tactic.Ring

/-!
# Checked left-hand coefficients in outer degrees twenty-two through thirty-two

This leaf checks a bounded range of the four-term coefficient sums.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal

theorem lhs_coefficient_22 (s : ℚ) :
    LC22 s = HC22 s := by
  simp only [LC22, T0C22, T1C22, T2C22, T3C22, HC22]
  ring

theorem lhs_coefficient_23 (s : ℚ) :
    LC23 s = HC23 s := by
  simp only [LC23, T0C23, T1C23, T2C23, T3C23, HC23]
  ring

theorem lhs_coefficient_24 (s : ℚ) :
    LC24 s = HC24 s := by
  simp only [LC24, T0C24, T1C24, T2C24, T3C24, HC24]
  ring

theorem lhs_coefficient_25 (s : ℚ) :
    LC25 s = HC25 s := by
  simp only [LC25, T0C25, T1C25, T2C25, T3C25, HC25]
  ring

theorem lhs_coefficient_26 (s : ℚ) :
    LC26 s = HC26 s := by
  simp only [LC26, T0C26, T1C26, T2C26, T3C26, HC26]
  ring

theorem lhs_coefficient_27 (s : ℚ) :
    LC27 s = HC27 s := by
  simp only [LC27, T0C27, T1C27, T2C27, T3C27, HC27]
  ring

theorem lhs_coefficient_28 (s : ℚ) :
    LC28 s = HC28 s := by
  simp only [LC28, T0C28, T1C28, T2C28, T3C28, HC28]
  ring

theorem lhs_coefficient_29 (s : ℚ) :
    LC29 s = HC29 s := by
  simp only [LC29, T0C29, T1C29, T2C29, T3C29, HC29]
  ring

theorem lhs_coefficient_30 (s : ℚ) :
    LC30 s = HC30 s := by
  simp only [LC30, T0C30, T1C30, T2C30, T3C30, HC30]
  ring

theorem lhs_coefficient_31 (s : ℚ) :
    LC31 s = HC31 s := by
  simp only [LC31, T0C31, T1C31, T2C31, T3C31, HC31]
  ring

theorem lhs_coefficient_32 (s : ℚ) :
    LC32 s = HC32 s := by
  simp only [LC32, T0C32, T1C32, T2C32, T3C32, HC32]
  ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationZeroCertificate.Internal
