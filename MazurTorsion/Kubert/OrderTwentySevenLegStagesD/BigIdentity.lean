/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegStagesD.ZeroSum

/-!
# Final third-leg correspondence identity

The staged certificates combine into the cleared Fricke-twisted correspondence
identity for the third leg.
-/

namespace MazurTorsion.Kubert

lemma zl_big {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * ((zlTN0 f Z +
      zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) ^ 3 + (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f *
      (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) *
      (f ^ 2 - f + 1) ^ 3) ^ 2) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) ^ 2 * zlE0 f Z
      ^ 2 + (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) +
      26244 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 +
      531441 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z +
      zlTN3 Z)) * zlE0 f Z ^ 4 + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) * zlE0 f Z ^ 6 = 0 := by
  linear_combination
    (((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * ((zlTN0 f Z +
      zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) + (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f -
      1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^
      2 - f + 1) ^ 3) ^ 2) * zlE0 f Z ^ 2) * zlTNSq_val hM + ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6
      * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) * zlTNCb_val hM + ((36 * (f ^ 3 - 6 * f ^ 2 + 3 * f +
      1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 *
      (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) + (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f
      - 1) * (f ^ 2 - f + 1) ^ 3) + 26244 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) *
      (f ^ 2 - f + 1) ^ 3) ^ 2 + 531441 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * ((zlTN0 f Z +
      zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * (zlE0 f Z ^ 2 + ((zlTDP0c0 f Z + zlTDP0c1 f Z) +
      zlTDP0c2 f Z)) + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) * (zlE0 f Z ^ 4 + zlE0 f Z ^ 2 *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) + ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f
      Z) ^ 2)) * zlTD_val hM + (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 -
      f + 1) ^ 3) + 729 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^
      3) ^ 2) * zlTNSqTD_val hM + (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^
      2 - f + 1) ^ 3) + 26244 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f +
      1) ^ 3) ^ 2 + 531441 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * ((zlTDP0c0 f Z + zlTDP0c1
      f Z) + zlTDP0c2 f Z) * zlTNTD_val hM + (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f
      - 1) * (f ^ 2 - f + 1) ^ 3) + 26244 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) *
      (f ^ 2 - f + 1) ^ 3) ^ 2 + 531441 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) * zlTNTDSq_val
      hM + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
      * zlTDSq_val hM + (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) * zlTDCb_val hM + zlWThree_val hM +
      zlWTwo_val hM + zlWOne_val hM + zlWZero_val hM - ((zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2
      f) * zl_brC3 f - (((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3
      f Z)) + ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z))) *
      zl_brC2 f - (((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f
      Z)) + ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
      (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
      ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z)))) +
      (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
      (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z))) * zl_brC1 f - ((((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) +
      (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + ((zlTDCbP0c4 f Z + zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z +
      zlTDCbP1c2 f Z))) + ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) + zlTDCbP1c5 f Z)) * zl_brC0 f +
      zl_zeroZ f Z

end MazurTorsion.Kubert
