/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Third-leg numerator-denominator product

The staged product of the third-leg numerator and denominator, reduced against the
kernel cubic.
-/

namespace MazurTorsion.Kubert

lemma zlTNTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z + zlTN1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + zlTNTDP0c4
        f Z := by
  linear_combination (norm := skip)
    (zlTNTDQ0c0 f Z) * hM + (zlTNTDQ0c1 f Z) * hM + (zlTNTDQ0c2 f Z) * hM + (zlTNTDQ0c3 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTN0, zlTN1, zlTNTDP0c0,
      zlTNTDP0c1, zlTNTDP0c2, zlTNTDP0c3, zlTNTDP0c4, zlTNTDQ0c0, zlTNTDQ0c1,
      zlTNTDQ0c2, zlTNTDQ0c3]
  ring1

lemma zlTNTD_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN2 f Z + zlTN3 Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) + (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z)) + zlTNTDP1c4
        f Z := by
  linear_combination (norm := skip)
    (zlTNTDQ1c0 f Z) * hM + (zlTNTDQ1c1 f Z) * hM + (zlTNTDQ1c2 f Z) * hM + (zlTNTDQ1c3 f Z) * hM
      + (zlTNTDQ1c4 f Z) * hM + (zlTNTDQ1c5 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTN2, zlTN3, zlTNTDP1c0,
      zlTNTDP1c1, zlTNTDP1c2, zlTNTDP1c3, zlTNTDP1c4, zlTNTDQ1c0, zlTNTDQ1c1,
      zlTNTDQ1c2, zlTNTDQ1c3, zlTNTDQ1c4, zlTNTDQ1c5]
  ring1

lemma zlTNTD_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      (((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) +
        ((zlTNTDP0c4 f Z + zlTNTDP1c0 f Z) + (zlTNTDP1c1 f Z + zlTNTDP1c2 f Z))) +
        (zlTNTDP1c3 f Z + zlTNTDP1c4 f Z) := by
  linear_combination
    (zlTNTD_s0 hM) + (zlTNTD_s1 hM)

end MazurTorsion.Kubert
