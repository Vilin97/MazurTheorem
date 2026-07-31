/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNum

/-!
# The kernel cubic identity

The cubic identity obtained from the combined numerator certificate.
-/

namespace MazurTorsion.Kubert

lemma kernel_cubic_at {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0)
    (hD : tlD0 f ξ + tlD1 f ξ ≠ 0) :
    kernelCubicM f (((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) / (tlD0 f ξ + tlD1 f ξ)) = 0
      := by
  have h := tl_mnum hT
  simp only [kernelCubicM]
  field_simp
  linear_combination h


end MazurTorsion.Kubert
