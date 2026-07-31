/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegStagesD.DenominatorPowers

/-!
# High-degree weighted third-leg identities

The cubic and quadratic coefficient-weighted identities used in the final
Fricke-twisted correspondence certificate.
-/

namespace MazurTorsion.Kubert

lemma zlWThree_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNCbP0c0 f + zlTNCbP0c1 f + zlTNCbP0c2 f) * zlCThree0 f =
      (zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCThree0, zlTNCbP0c0, zlTNCbP0c1, zlTNCbP0c2, zlWThreeP0c0,
      zlWThreeP0c1, zlWThreeP0c2, zlWThreeP0c3]
  ring1

lemma zlWThree_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f) * zlCThree0 f =
      (zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f) := by
  linear_combination
    (zlWThree_s0 hM)

lemma zlWTwo_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z + zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z + zlTNSqTDP0c4 f Z
      + zlTNSqTDP0c5 f Z + zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z) * zlCTwo0 f =
      (((zlWTwoP0c0 f Z + zlWTwoP0c1 f Z) + (zlWTwoP0c2 f Z + zlWTwoP0c3 f Z)) +
        ((zlWTwoP0c4 f Z + zlWTwoP0c5 f Z) + (zlWTwoP0c6 f Z + zlWTwoP0c7 f Z))) +
        (zlWTwoP0c8 f Z + zlWTwoP0c9 f Z) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCTwo0, zlTNSqTDP0c0, zlTNSqTDP0c1, zlTNSqTDP0c2, zlTNSqTDP0c3,
      zlTNSqTDP0c4, zlTNSqTDP0c5, zlTNSqTDP0c6, zlTNSqTDP0c7, zlWTwoP0c0,
      zlWTwoP0c1, zlWTwoP0c2, zlWTwoP0c3, zlWTwoP0c4, zlWTwoP0c5, zlWTwoP0c6,
      zlWTwoP0c7, zlWTwoP0c8, zlWTwoP0c9]
  ring1

lemma zlWTwo_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
      ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z))) * zlCTwo0 f
      =
      (((zlWTwoP0c0 f Z + zlWTwoP0c1 f Z) + (zlWTwoP0c2 f Z + zlWTwoP0c3 f Z)) +
        ((zlWTwoP0c4 f Z + zlWTwoP0c5 f Z) + (zlWTwoP0c6 f Z + zlWTwoP0c7 f Z))) +
        (zlWTwoP0c8 f Z + zlWTwoP0c9 f Z) := by
  linear_combination
    (zlWTwo_s0 hM)

end MazurTorsion.Kubert
