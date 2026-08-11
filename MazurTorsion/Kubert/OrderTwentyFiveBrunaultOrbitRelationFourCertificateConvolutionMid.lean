/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateConvolutionData
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! Checked RelationFour convolution coefficients of degrees twelve through twenty-three. -/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

theorem convolution_coefficients_mid (s : ℚ) (n : Nat)
    (hlo : 12 ≤ n) (hi : n ≤ 23) :
    convolutionCoefficientEq n s := by
  interval_cases n <;>
    simp only [convolutionCoefficientEq, convolutionCoefficient, convolutionOf,
      fCoefficient, quotientCoefficient, numeratorCoefficient] <;>
    ring

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
