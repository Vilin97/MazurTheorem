/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateConvolutionData
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! Checked RelationFour convolution coefficients of degrees zero through eleven. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

theorem convolution_coefficients_low (s : ℚ) (n : Nat) (hn : n ≤ 11) :
    convolutionCoefficientEq n s := by
  interval_cases n <;>
    simp only [convolutionCoefficientEq, convolutionCoefficient, convolutionOf,
      fCoefficient, quotientCoefficient, numeratorCoefficient] <;>
    ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
