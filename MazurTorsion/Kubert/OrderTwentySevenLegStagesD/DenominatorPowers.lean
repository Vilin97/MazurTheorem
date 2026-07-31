/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegStagesD.NumeratorDenominatorSquare

/-!
# Third-leg denominator powers

The square and cube certificates for the third-leg denominator, reduced against the
kernel cubic.
-/

namespace MazurTorsion.Kubert

lemma zlTDSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z)
      =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z := by
  linear_combination (norm := skip)
    (zlTDSqQ0c0 f Z) * hM + (zlTDSqQ0c1 f Z) * hM + (zlTDSqQ0c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTDSqP0c0, zlTDSqP0c1, zlTDSqP0c2,
      zlTDSqP0c3, zlTDSqP0c4, zlTDSqQ0c0, zlTDSqQ0c1, zlTDSqQ0c2]
  ring1

lemma zlTDSq_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f
      Z) =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z := by
  linear_combination
    (zlTDSq_s0 hM)

lemma zlTDCb_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + zlTDCbP0c4
        f Z := by
  linear_combination (norm := skip)
    (zlTDCbQ0c0 f Z) * hM + (zlTDCbQ0c1 f Z) * hM + (zlTDCbQ0c2 f Z) * hM
  simp only [kernelCubicM, zlTDCbP0c0, zlTDCbP0c1, zlTDCbP0c2, zlTDCbP0c3, zlTDCbP0c4,
      zlTDCbQ0c0, zlTDCbQ0c1, zlTDCbQ0c2, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTDSqP0c0,
      zlTDSqP0c1]
  ring1

lemma zlTDCb_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z + zlTDSqP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTDCbP1c0 f Z + zlTDCbP1c1 f Z) + (zlTDCbP1c2 f Z + zlTDCbP1c3 f Z)) +
        (zlTDCbP1c4 f Z + zlTDCbP1c5 f Z) := by
  linear_combination (norm := skip)
    (zlTDCbQ1c0 f Z) * hM + (zlTDCbQ1c1 f Z) * hM + (zlTDCbQ1c2 f Z) * hM
  simp only [kernelCubicM, zlTDCbP1c0, zlTDCbP1c1, zlTDCbP1c2, zlTDCbP1c3, zlTDCbP1c4,
      zlTDCbP1c5, zlTDCbQ1c0, zlTDCbQ1c1, zlTDCbQ1c2, zlTDP0c0, zlTDP0c1, zlTDP0c2,
      zlTDSqP0c2, zlTDSqP0c3, zlTDSqP0c4]
  ring1

lemma zlTDCb_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4 f Z) *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      (((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) +
        ((zlTDCbP0c4 f Z + zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z + zlTDCbP1c2 f Z))) +
        ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) + zlTDCbP1c5 f Z) := by
  linear_combination
    (zlTDCb_s0 hM) + (zlTDCb_s1 hM)

end MazurTorsion.Kubert
