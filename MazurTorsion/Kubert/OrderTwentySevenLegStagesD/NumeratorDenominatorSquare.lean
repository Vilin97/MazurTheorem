/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Third-leg numerator times the denominator square

The staged product certificate for the third-leg numerator and the square of its
denominator.
-/

namespace MazurTorsion.Kubert

lemma zlTNTDSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        zlTNTDSqP0c4 f Z := by
  linear_combination (norm := skip)
    (zlTNTDSqQ0c0 f Z) * hM + (zlTNTDSqQ0c1 f Z) * hM + (zlTNTDSqQ0c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNTDP0c0, zlTNTDP0c1,
      zlTNTDSqP0c0, zlTNTDSqP0c1, zlTNTDSqP0c2, zlTNTDSqP0c3, zlTNTDSqP0c4,
      zlTNTDSqQ0c0, zlTNTDSqQ0c1, zlTNTDSqQ0c2]
  ring1

lemma zlTNTDSq_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z + zlTNTDP0c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP1c0 f Z + zlTNTDSqP1c1 f Z) + (zlTNTDSqP1c2 f Z + zlTNTDSqP1c3 f Z)) +
        (zlTNTDSqP1c4 f Z + zlTNTDSqP1c5 f Z) := by
  linear_combination (norm := skip)
    (zlTNTDSqQ1c0 f Z) * hM + (zlTNTDSqQ1c1 f Z) * hM + (zlTNTDSqQ1c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNTDP0c2, zlTNTDP0c3, zlTNTDP0c4,
      zlTNTDSqP1c0, zlTNTDSqP1c1, zlTNTDSqP1c2, zlTNTDSqP1c3, zlTNTDSqP1c4,
      zlTNTDSqP1c5, zlTNTDSqQ1c0, zlTNTDSqQ1c1, zlTNTDSqQ1c2]
  ring1

lemma zlTNTDSq_s2 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP1c0 f Z + zlTNTDP1c1 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((zlTNTDSqP2c0 f Z + zlTNTDSqP2c1 f Z) + (zlTNTDSqP2c2 f Z + zlTNTDSqP2c3 f Z)) +
        zlTNTDSqP2c4 f Z := by
  linear_combination (norm := skip)
    (zlTNTDSqQ2c0 f Z) * hM + (zlTNTDSqQ2c1 f Z) * hM + (zlTNTDSqQ2c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNTDP1c0, zlTNTDP1c1,
      zlTNTDSqP2c0, zlTNTDSqP2c1, zlTNTDSqP2c2, zlTNTDSqP2c3, zlTNTDSqP2c4,
      zlTNTDSqQ2c0, zlTNTDSqQ2c1, zlTNTDSqQ2c2]
  ring1

lemma zlTNTDSq_s3 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDP1c2 f Z + zlTNTDP1c3 f Z + zlTNTDP1c4 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      ((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
        (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z) := by
  linear_combination (norm := skip)
    (zlTNTDSqQ3c0 f Z) * hM + (zlTNTDSqQ3c1 f Z) * hM + (zlTNTDSqQ3c2 f Z) * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNTDP1c2, zlTNTDP1c3, zlTNTDP1c4,
      zlTNTDSqP3c0, zlTNTDSqP3c1, zlTNTDSqP3c2, zlTNTDSqP3c3, zlTNTDSqP3c4,
      zlTNTDSqP3c5, zlTNTDSqQ3c0, zlTNTDSqQ3c1, zlTNTDSqQ3c2]
  ring1

lemma zlTNTDSq_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + ((zlTNTDP0c4 f Z +
      zlTNTDP1c0 f Z) + (zlTNTDP1c1 f Z + zlTNTDP1c2 f Z))) + (zlTNTDP1c3 f Z + zlTNTDP1c4 f Z)) *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
        (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
        ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z))))
        + (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z))
        + (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z)) := by
  linear_combination
    ((zlTNTDSq_s0 hM) + (zlTNTDSq_s1 hM)) + ((zlTNTDSq_s2 hM) + (zlTNTDSq_s3 hM))

end MazurTorsion.Kubert
