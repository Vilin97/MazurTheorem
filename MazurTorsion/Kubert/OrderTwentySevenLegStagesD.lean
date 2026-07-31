/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegStagesC

/-!
# The third-leg correspondence certificate

The Fricke-twisted correspondence certificate: the third leg satisfies the
cleared `X₀(9)` relation against the second leg, and its denominator is
invertible by the Bezout certificate.
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

lemma zlWOne_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z + zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z + zlTNTDSqP0c4 f Z
      + zlTNTDSqP1c0 f Z + zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z + zlTNTDSqP1c3 f Z) * zlCOne0 f =
      (((zlWOneP0c0 f Z + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) +
        ((zlWOneP0c4 f Z + zlWOneP0c5 f Z) + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) +
        zlWOneP0c8 f Z := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCOne0, zlTNTDSqP0c0, zlTNTDSqP0c1, zlTNTDSqP0c2, zlTNTDSqP0c3,
      zlTNTDSqP0c4, zlTNTDSqP1c0, zlTNTDSqP1c1, zlTNTDSqP1c2, zlTNTDSqP1c3,
      zlWOneP0c0, zlWOneP0c1, zlWOneP0c2, zlWOneP0c3, zlWOneP0c4, zlWOneP0c5,
      zlWOneP0c6, zlWOneP0c7, zlWOneP0c8]
  ring1

lemma zlWOne_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDSqP1c4 f Z + zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z + zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z
      + zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z + zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z + zlTNTDSqP3c2 f
      Z) * zlCOne0 f =
      (((zlWOneP1c0 f Z + zlWOneP1c1 f Z) + (zlWOneP1c2 f Z + zlWOneP1c3 f Z)) +
        ((zlWOneP1c4 f Z + zlWOneP1c5 f Z) + (zlWOneP1c6 f Z + zlWOneP1c7 f Z))) +
        (zlWOneP1c8 f Z + zlWOneP1c9 f Z) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCOne0, zlTNTDSqP1c4, zlTNTDSqP1c5, zlTNTDSqP2c0, zlTNTDSqP2c1,
      zlTNTDSqP2c2, zlTNTDSqP2c3, zlTNTDSqP2c4, zlTNTDSqP3c0, zlTNTDSqP3c1,
      zlTNTDSqP3c2, zlWOneP1c0, zlWOneP1c1, zlWOneP1c2, zlWOneP1c3, zlWOneP1c4,
      zlWOneP1c5, zlWOneP1c6, zlWOneP1c7, zlWOneP1c8, zlWOneP1c9]
  ring1

lemma zlWOne_s2 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTNTDSqP3c3 f Z + zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z) * zlCOne0 f =
      ((zlWOneP2c0 f Z + zlWOneP2c1 f Z) + (zlWOneP2c2 f Z + zlWOneP2c3 f Z)) +
        (zlWOneP2c4 f Z + zlWOneP2c5 f Z) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCOne0, zlTNTDSqP3c3, zlTNTDSqP3c4, zlTNTDSqP3c5, zlWOneP2c0,
      zlWOneP2c1, zlWOneP2c2, zlWOneP2c3, zlWOneP2c4, zlWOneP2c5]
  ring1

lemma zlWOne_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
      ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
      (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
      ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z)))) +
      (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z)) +
      (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z))) * zlCOne0 f =
      ((((zlWOneP0c0 f Z + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) +
        ((zlWOneP0c4 f Z + zlWOneP0c5 f Z) + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) +
        (((zlWOneP0c8 f Z + zlWOneP1c0 f Z) + (zlWOneP1c1 f Z + zlWOneP1c2 f Z)) +
        ((zlWOneP1c3 f Z + zlWOneP1c4 f Z) + (zlWOneP1c5 f Z + zlWOneP1c6 f Z)))) +
        ((((zlWOneP1c7 f Z + zlWOneP1c8 f Z) + (zlWOneP1c9 f Z + zlWOneP2c0 f Z)) +
        ((zlWOneP2c1 f Z + zlWOneP2c2 f Z) + (zlWOneP2c3 f Z + zlWOneP2c4 f Z))) +
        zlWOneP2c5 f Z) := by
  linear_combination
    ((zlWOne_s0 hM) + (zlWOne_s1 hM)) + (zlWOne_s2 hM)

lemma zlWZero_s0 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDCbP0c0 f Z + zlTDCbP0c1 f Z + zlTDCbP0c2 f Z + zlTDCbP0c3 f Z + zlTDCbP0c4 f Z +
      zlTDCbP1c0 f Z + zlTDCbP1c1 f Z + zlTDCbP1c2 f Z) * zlCZero0 f =
      ((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) +
        ((zlWZeroP0c4 f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z)) := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCZero0, zlTDCbP0c0, zlTDCbP0c1, zlTDCbP0c2, zlTDCbP0c3,
      zlTDCbP0c4, zlTDCbP1c0, zlTDCbP1c1, zlTDCbP1c2, zlWZeroP0c0, zlWZeroP0c1,
      zlWZeroP0c2, zlWZeroP0c3, zlWZeroP0c4, zlWZeroP0c5, zlWZeroP0c6, zlWZeroP0c7]
  ring1

lemma zlWZero_s1 {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (zlTDCbP1c3 f Z + zlTDCbP1c4 f Z + zlTDCbP1c5 f Z) * zlCZero0 f =
      ((zlWZeroP1c0 f Z + zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) +
        zlWZeroP1c4 f Z := by
  linear_combination (norm := skip)
    0 * hM
  simp only [kernelCubicM, zlCZero0, zlTDCbP1c3, zlTDCbP1c4, zlTDCbP1c5, zlWZeroP1c0,
      zlWZeroP1c1, zlWZeroP1c2, zlWZeroP1c3, zlWZeroP1c4]
  ring1

lemma zlWZero_val {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    ((((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) + ((zlTDCbP0c4 f Z +
      zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z + zlTDCbP1c2 f Z))) + ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) +
      zlTDCbP1c5 f Z)) * zlCZero0 f =
      (((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) +
        ((zlWZeroP0c4 f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z))) +
        (((zlWZeroP1c0 f Z + zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) +
        zlWZeroP1c4 f Z) := by
  linear_combination
    (zlWZero_s0 hM) + (zlWZero_s1 hM)

lemma zl_brC3 (f : ℚ) :
    zlCThree0 f =
      ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) := by
  simp only [zlCThree0]
  ring1

lemma zl_brC2 (f : ℚ) :
    zlCTwo0 f =
      (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^
        3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2) := by
  simp only [zlCTwo0]
  ring1

lemma zl_brC1 (f : ℚ) :
    zlCOne0 f =
      (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 26244 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 + 531441 *
        (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) := by
  simp only [zlCOne0]
  ring1

lemma zl_brC0 (f : ℚ) :
    zlCZero0 f =
      (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) := by
  simp only [zlCZero0]
  ring1

lemma zl_zeroZ (f Z : ℚ) :
    (zlWThreeP0c0 f + zlWThreeP0c1 f) + (zlWThreeP0c2 f + zlWThreeP0c3 f) + (((zlWTwoP0c0 f Z +
      zlWTwoP0c1 f Z) + (zlWTwoP0c2 f Z + zlWTwoP0c3 f Z)) + ((zlWTwoP0c4 f Z + zlWTwoP0c5 f Z) +
      (zlWTwoP0c6 f Z + zlWTwoP0c7 f Z))) + (zlWTwoP0c8 f Z + zlWTwoP0c9 f Z) + ((((zlWOneP0c0 f Z
      + zlWOneP0c1 f Z) + (zlWOneP0c2 f Z + zlWOneP0c3 f Z)) + ((zlWOneP0c4 f Z + zlWOneP0c5 f Z)
      + (zlWOneP0c6 f Z + zlWOneP0c7 f Z))) + (((zlWOneP0c8 f Z + zlWOneP1c0 f Z) + (zlWOneP1c1 f
      Z + zlWOneP1c2 f Z)) + ((zlWOneP1c3 f Z + zlWOneP1c4 f Z) + (zlWOneP1c5 f Z + zlWOneP1c6 f
      Z)))) + ((((zlWOneP1c7 f Z + zlWOneP1c8 f Z) + (zlWOneP1c9 f Z + zlWOneP2c0 f Z)) +
      ((zlWOneP2c1 f Z + zlWOneP2c2 f Z) + (zlWOneP2c3 f Z + zlWOneP2c4 f Z))) + zlWOneP2c5 f Z) +
      (((zlWZeroP0c0 f Z + zlWZeroP0c1 f Z) + (zlWZeroP0c2 f Z + zlWZeroP0c3 f Z)) + ((zlWZeroP0c4
      f Z + zlWZeroP0c5 f Z) + (zlWZeroP0c6 f Z + zlWZeroP0c7 f Z))) + (((zlWZeroP1c0 f Z +
      zlWZeroP1c1 f Z) + (zlWZeroP1c2 f Z + zlWZeroP1c3 f Z)) + zlWZeroP1c4 f Z) = 0 := by
  simp only [zlWThreeP0c0, zlWThreeP0c1, zlWThreeP0c2, zlWThreeP0c3, zlWTwoP0c0, zlWTwoP0c1,
      zlWTwoP0c2, zlWTwoP0c3, zlWTwoP0c4, zlWTwoP0c5, zlWTwoP0c6, zlWTwoP0c7,
      zlWTwoP0c8, zlWTwoP0c9, zlWOneP0c0, zlWOneP0c1, zlWOneP0c2, zlWOneP0c3,
      zlWOneP0c4, zlWOneP0c5, zlWOneP0c6, zlWOneP0c7, zlWOneP0c8, zlWOneP1c0,
      zlWOneP1c1, zlWOneP1c2, zlWOneP1c3, zlWOneP1c4, zlWOneP1c5, zlWOneP1c6,
      zlWOneP1c7, zlWOneP1c8, zlWOneP1c9, zlWOneP2c0, zlWOneP2c1, zlWOneP2c2,
      zlWOneP2c3, zlWOneP2c4, zlWOneP2c5, zlWZeroP0c0, zlWZeroP0c1, zlWZeroP0c2,
      zlWZeroP0c3, zlWZeroP0c4, zlWZeroP0c5, zlWZeroP0c6, zlWZeroP0c7, zlWZeroP1c0,
      zlWZeroP1c1, zlWZeroP1c2, zlWZeroP1c3, zlWZeroP1c4]
  ring1

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

lemma zl_bezout {f Z : ℚ} (hM : kernelCubicM f Z = 0) :
    (tlBezB0 f Z + tlBezB1 f Z + tlBezB2 f Z + tlBezB3 f Z) * zlE0 f Z =
      (f * (f - 1) * (f ^ 2 - f + 1) ^ 6 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 18) := by
  linear_combination (norm := skip)
    (-(tlBezA0 f Z + tlBezA1 f Z + tlBezA2 f Z + tlBezA3 f Z + tlBezA4 Z)) * hM
  simp only [kernelCubicM, tlBezA0, tlBezA1, tlBezA2, tlBezA3, tlBezA4, tlBezB0, tlBezB1,
      tlBezB2, tlBezB3, zlE0]
  ring1

lemma zl_e_ne {f Z : ℚ} (hM : kernelCubicM f Z = 0) (hf0 : f ≠ 0)
    (hf1 : f ≠ 1) (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) :
    zlE0 f Z ≠ 0 := by
  intro h0
  have hb := zl_bezout hM
  rw [h0, mul_zero] at hb
  rcases mul_eq_zero.mp hb.symm with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact hf0 h''
      · exact hf1 (sub_eq_zero.mp h'')
    · exact quad_ne f (pow_eq_zero_iff (by norm_num) |>.mp h')
  · exact hK (pow_eq_zero_iff (by norm_num) |>.mp h)

end MazurTorsion.Kubert
