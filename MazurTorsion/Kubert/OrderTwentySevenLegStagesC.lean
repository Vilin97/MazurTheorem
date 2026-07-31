/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Kernel-cubic-side staged products

Staged products of the kernel-cubic-side certificate chain: powers of the
third-leg numerator and denominator reduced against the kernel cubic.
-/

namespace MazurTorsion.Kubert

lemma zlTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlE0 f Z) * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z := by
  linear_combination (norm := skip)
    (zlTDQ0c0 f Z) * hM
  simp only [kernelCubicM, zlE0, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTDQ0c0]
  ring1

lemma zlTD_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    zlE0 f Z * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z := by
  linear_combination
    (zlTD_s0 hM)

lemma zlTNSq_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      (zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z) := by
  linear_combination (norm := skip)
    (zlTNSqQ0c0 f Z) * hM + (zlTNSqQ0c1 f Z) * hM + (zlTNSqQ0c2 f Z) * hM + (zlTNSqQ0c3 f Z) * hM
  simp only [kernelCubicM, zlTN0, zlTN1, zlTN2, zlTN3, zlTNSqP0c0, zlTNSqP0c1, zlTNSqP0c2,
      zlTNSqP0c3, zlTNSqQ0c0, zlTNSqQ0c1, zlTNSqQ0c2, zlTNSqQ0c3]
  ring1

lemma zlTNSq_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN1 f Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z)) + zlTNSqP1c4
        f Z := by
  linear_combination (norm := skip)
    (zlTNSqQ1c0 f Z) * hM + (zlTNSqQ1c1 f Z) * hM + (zlTNSqQ1c2 f Z) * hM + (zlTNSqQ1c3 f Z) * hM
      + (zlTNSqQ1c4 f Z) * hM
  simp only [kernelCubicM, zlTN0, zlTN1, zlTN2, zlTN3, zlTNSqP1c0, zlTNSqP1c1, zlTNSqP1c2,
      zlTNSqP1c3, zlTNSqP1c4, zlTNSqQ1c0, zlTNSqQ1c1, zlTNSqQ1c2, zlTNSqQ1c3,
      zlTNSqQ1c4]
  ring1

lemma zlTNSq_s2 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN2 f Z + zlTN3 Z) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) =
      ((zlTNSqP2c0 f Z + zlTNSqP2c1 f Z) + (zlTNSqP2c2 f Z + zlTNSqP2c3 f Z)) + zlTNSqP2c4
        f Z := by
  linear_combination (norm := skip)
    (zlTNSqQ2c0 f Z) * hM + (zlTNSqQ2c1 f Z) * hM + (zlTNSqQ2c2 f Z) * hM + (zlTNSqQ2c3 f Z) * hM
      + (zlTNSqQ2c4 f Z) * hM + (zlTNSqQ2c5 f Z) * hM + (zlTNSqQ2c6 f Z) * hM
  simp only [kernelCubicM, zlTN0, zlTN1, zlTN2, zlTN3, zlTNSqP2c0, zlTNSqP2c1, zlTNSqP2c2,
      zlTNSqP2c3, zlTNSqP2c4, zlTNSqQ2c0, zlTNSqQ2c1, zlTNSqQ2c2, zlTNSqQ2c3,
      zlTNSqQ2c4, zlTNSqQ2c5, zlTNSqQ2c6]
  ring1

lemma zlTNSq_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z +
      zlTN3 Z)) =
      (((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) +
        ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z))) +
        (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z)) +
        (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z)) := by
  linear_combination
    ((zlTNSq_s0 hM) + (zlTNSq_s1 hM)) + (zlTNSq_s2 hM)

lemma zlTNCb_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTN0 f Z + zlTN1 f Z + zlTN2 f Z + zlTN3 Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f := by
  linear_combination (norm := skip)
    (zlTNCbQ0c0 f Z) * hM + (zlTNCbQ0c1 f Z) * hM + (zlTNCbQ0c2 f Z) * hM + (zlTNCbQ0c3 f Z) * hM
      + (zlTNCbQ0c4 f Z) * hM + (zlTNCbQ0c5 f Z) * hM + (zlTNCbQ0c6 f Z) * hM + (zlTNCbQ0c7 f Z) *
      hM
  simp only [kernelCubicM, zlTN0, zlTN1, zlTN2, zlTN3, zlTNCbP0c0, zlTNCbP0c1, zlTNCbP0c2,
      zlTNCbQ0c0, zlTNCbQ0c1, zlTNCbQ0c2, zlTNCbQ0c3, zlTNCbQ0c4, zlTNCbQ0c5,
      zlTNCbQ0c6, zlTNCbQ0c7, zlTNSqP0c0, zlTNSqP0c1, zlTNSqP0c2, zlTNSqP0c3,
      zlTNSqP1c0, zlTNSqP1c1, zlTNSqP1c2, zlTNSqP1c3, zlTNSqP1c4, zlTNSqP2c0,
      zlTNSqP2c1, zlTNSqP2c2, zlTNSqP2c3, zlTNSqP2c4]
  ring1

lemma zlTNCb_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f := by
  linear_combination
    (zlTNCb_s0 hM)

lemma zlTNSqTD_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDP0c0 f Z + zlTDP0c1 f Z + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z)) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlTDP0c0, zlTDP0c1, zlTDP0c2, zlTNSqP0c0, zlTNSqP0c1, zlTNSqP0c2,
      zlTNSqP0c3, zlTNSqP1c0, zlTNSqP1c1, zlTNSqP1c2, zlTNSqP1c3, zlTNSqP1c4,
      zlTNSqP2c0, zlTNSqP2c1, zlTNSqP2c2, zlTNSqP2c3, zlTNSqP2c4, zlTNSqTDP0c0,
      zlTNSqTDP0c1, zlTNSqTDP0c2, zlTNSqTDP0c3, zlTNSqTDP0c4, zlTNSqTDP0c5,
      zlTNSqTDP0c6, zlTNSqTDP0c7]
  ring1

lemma zlTNSqTD_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z)) := by
  linear_combination
    (zlTNSqTD_s0 hM)

end MazurTorsion.Kubert
