/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegStagesA

/-!
# The kernel cubic certificate

The kernel cubic certificate: the weighted staged values combine to the zero polynomial, so the third-story kernel abscissa satisfies its monic cubic.
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s0 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP0c0 f ξ + tlNSqP0c1 f ξ + tlNSqP0c2 f ξ + tlNSqP0c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
        tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ
        + tlTTwoP0c10 f ξ + tlTTwoP0c11 f ξ + tlTTwoP0c12 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ0c0 f ξ) * hT + (tlTTwoQ0c1 f ξ) * hT + (tlTTwoQ0c2 f ξ) * hT + (tlTTwoQ0c3 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP0c0, tlNSqP0c1, tlNSqP0c2, tlNSqP0c3, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP0c0, tlTTwoP0c1, tlTTwoP0c10, tlTTwoP0c11, tlTTwoP0c12, tlTTwoP0c2,
      tlTTwoP0c3, tlTTwoP0c4, tlTTwoP0c5, tlTTwoP0c6, tlTTwoP0c7, tlTTwoP0c8,
      tlTTwoP0c9, tlTTwoQ0c0, tlTTwoQ0c1, tlTTwoQ0c2, tlTTwoQ0c3]
  ring1

lemma tlTTwo_s1 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP0c4 f ξ + tlNSqP0c5 f ξ + tlNSqP0c6 f ξ + tlNSqP0c7 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ + tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ +
        tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ
        + tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ + tlTTwoP1c12 f ξ + tlTTwoP1c13 f ξ +
        tlTTwoP1c14 f ξ + tlTTwoP1c15 f ξ + tlTTwoP1c16 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ1c0 f ξ) * hT + (tlTTwoQ1c1 f ξ) * hT + (tlTTwoQ1c2 f ξ) * hT + (tlTTwoQ1c3 f ξ) * hT
      + (tlTTwoQ1c4 f ξ) * hT + (tlTTwoQ1c5 f ξ) * hT + (tlTTwoQ1c6 f ξ) * hT + (tlTTwoQ1c7 f ξ) *
      hT
  simp only [tlD0, tlD1, tlNSqP0c4, tlNSqP0c5, tlNSqP0c6, tlNSqP0c7, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP1c0, tlTTwoP1c1, tlTTwoP1c10, tlTTwoP1c11, tlTTwoP1c12, tlTTwoP1c13,
      tlTTwoP1c14, tlTTwoP1c15, tlTTwoP1c16, tlTTwoP1c2, tlTTwoP1c3, tlTTwoP1c4,
      tlTTwoP1c5, tlTTwoP1c6, tlTTwoP1c7, tlTTwoP1c8, tlTTwoP1c9, tlTTwoQ1c0,
      tlTTwoQ1c1, tlTTwoQ1c2, tlTTwoQ1c3, tlTTwoQ1c4, tlTTwoQ1c5, tlTTwoQ1c6,
      tlTTwoQ1c7]
  ring1

lemma tlTTwo_s2 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP0c8 f ξ + tlNSqP0c9 f ξ + tlNSqP1c0 f ξ + tlNSqP1c1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ + tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ +
        tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ + tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ
        + tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ + tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ +
        tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ + tlTTwoP2c16 f ξ + tlTTwoP2c17 f ξ +
        tlTTwoP2c18 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ2c0 f ξ) * hT + (tlTTwoQ2c1 f ξ) * hT + (tlTTwoQ2c2 f ξ) * hT + (tlTTwoQ2c3 f ξ) * hT
      + (tlTTwoQ2c4 f ξ) * hT + (tlTTwoQ2c5 f ξ) * hT + (tlTTwoQ2c6 f ξ) * hT + (tlTTwoQ2c7 f ξ) *
      hT
  simp only [tlD0, tlD1, tlNSqP0c8, tlNSqP0c9, tlNSqP1c0, tlNSqP1c1, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP2c0, tlTTwoP2c1, tlTTwoP2c10, tlTTwoP2c11, tlTTwoP2c12, tlTTwoP2c13,
      tlTTwoP2c14, tlTTwoP2c15, tlTTwoP2c16, tlTTwoP2c17, tlTTwoP2c18, tlTTwoP2c2,
      tlTTwoP2c3, tlTTwoP2c4, tlTTwoP2c5, tlTTwoP2c6, tlTTwoP2c7, tlTTwoP2c8,
      tlTTwoP2c9, tlTTwoQ2c0, tlTTwoQ2c1, tlTTwoQ2c2, tlTTwoQ2c3, tlTTwoQ2c4,
      tlTTwoQ2c5, tlTTwoQ2c6, tlTTwoQ2c7]
  ring1

lemma tlTTwo_s3 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP1c2 f ξ + tlNSqP1c3 f ξ + tlNSqP1c4 f ξ + tlNSqP1c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP3c0 f ξ + tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ +
        tlTTwoP3c5 f ξ + tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ
        + tlTTwoP3c10 f ξ + tlTTwoP3c11 f ξ + tlTTwoP3c12 f ξ + tlTTwoP3c13 f ξ +
        tlTTwoP3c14 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ3c0 f ξ) * hT + (tlTTwoQ3c1 f ξ) * hT + (tlTTwoQ3c2 f ξ) * hT + (tlTTwoQ3c3 f ξ) * hT
      + (tlTTwoQ3c4 f ξ) * hT + (tlTTwoQ3c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP1c2, tlNSqP1c3, tlNSqP1c4, tlNSqP1c5, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP3c0, tlTTwoP3c1, tlTTwoP3c10, tlTTwoP3c11, tlTTwoP3c12, tlTTwoP3c13,
      tlTTwoP3c14, tlTTwoP3c2, tlTTwoP3c3, tlTTwoP3c4, tlTTwoP3c5, tlTTwoP3c6,
      tlTTwoP3c7, tlTTwoP3c8, tlTTwoP3c9, tlTTwoQ3c0, tlTTwoQ3c1, tlTTwoQ3c2,
      tlTTwoQ3c3, tlTTwoQ3c4, tlTTwoQ3c5]
  ring1

lemma tlTTwo_s4 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP1c6 f ξ + tlNSqP1c7 f ξ + tlNSqP1c8 f ξ + tlNSqP1c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ +
        tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ
        + tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ +
        tlTTwoP4c14 f ξ + tlTTwoP4c15 f ξ + tlTTwoP4c16 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ4c0 f ξ) * hT + (tlTTwoQ4c1 f ξ) * hT + (tlTTwoQ4c2 f ξ) * hT + (tlTTwoQ4c3 f ξ) * hT
      + (tlTTwoQ4c4 f ξ) * hT + (tlTTwoQ4c5 f ξ) * hT + (tlTTwoQ4c6 f ξ) * hT + (tlTTwoQ4c7 f ξ) *
      hT
  simp only [tlD0, tlD1, tlNSqP1c6, tlNSqP1c7, tlNSqP1c8, tlNSqP1c9, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP4c0, tlTTwoP4c1, tlTTwoP4c10, tlTTwoP4c11, tlTTwoP4c12, tlTTwoP4c13,
      tlTTwoP4c14, tlTTwoP4c15, tlTTwoP4c16, tlTTwoP4c2, tlTTwoP4c3, tlTTwoP4c4,
      tlTTwoP4c5, tlTTwoP4c6, tlTTwoP4c7, tlTTwoP4c8, tlTTwoP4c9, tlTTwoQ4c0,
      tlTTwoQ4c1, tlTTwoQ4c2, tlTTwoQ4c3, tlTTwoQ4c4, tlTTwoQ4c5, tlTTwoQ4c6,
      tlTTwoQ4c7]
  ring1

lemma tlTTwo_s5 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP1c10 f ξ + tlNSqP1c11 f ξ + tlNSqP2c0 f ξ + tlNSqP2c1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ +
        tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ
        + tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ +
        tlTTwoP5c14 f ξ + tlTTwoP5c15 f ξ + tlTTwoP5c16 f ξ + tlTTwoP5c17 f ξ +
        tlTTwoP5c18 f ξ + tlTTwoP5c19 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ5c0 f ξ) * hT + (tlTTwoQ5c1 f ξ) * hT + (tlTTwoQ5c2 f ξ) * hT + (tlTTwoQ5c3 f ξ) * hT
      + (tlTTwoQ5c4 f ξ) * hT + (tlTTwoQ5c5 f ξ) * hT + (tlTTwoQ5c6 f ξ) * hT + (tlTTwoQ5c7 f ξ) *
      hT
  simp only [tlD0, tlD1, tlNSqP1c10, tlNSqP1c11, tlNSqP2c0, tlNSqP2c1, tlT0, tlT1, tlT2,
      tlT3, tlTTwoP5c0, tlTTwoP5c1, tlTTwoP5c10, tlTTwoP5c11, tlTTwoP5c12,
      tlTTwoP5c13, tlTTwoP5c14, tlTTwoP5c15, tlTTwoP5c16, tlTTwoP5c17, tlTTwoP5c18,
      tlTTwoP5c19, tlTTwoP5c2, tlTTwoP5c3, tlTTwoP5c4, tlTTwoP5c5, tlTTwoP5c6,
      tlTTwoP5c7, tlTTwoP5c8, tlTTwoP5c9, tlTTwoQ5c0, tlTTwoQ5c1, tlTTwoQ5c2,
      tlTTwoQ5c3, tlTTwoQ5c4, tlTTwoQ5c5, tlTTwoQ5c6, tlTTwoQ5c7]
  ring1

lemma tlTTwo_s6 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP2c2 f ξ + tlNSqP2c3 f ξ + tlNSqP2c4 f ξ + tlNSqP2c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ +
        tlTTwoP6c5 f ξ + tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ
        + tlTTwoP6c10 f ξ + tlTTwoP6c11 f ξ + tlTTwoP6c12 f ξ + tlTTwoP6c13 f ξ +
        tlTTwoP6c14 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ6c0 f ξ) * hT + (tlTTwoQ6c1 f ξ) * hT + (tlTTwoQ6c2 f ξ) * hT + (tlTTwoQ6c3 f ξ) * hT
      + (tlTTwoQ6c4 f ξ) * hT + (tlTTwoQ6c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c2, tlNSqP2c3, tlNSqP2c4, tlNSqP2c5, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP6c0, tlTTwoP6c1, tlTTwoP6c10, tlTTwoP6c11, tlTTwoP6c12, tlTTwoP6c13,
      tlTTwoP6c14, tlTTwoP6c2, tlTTwoP6c3, tlTTwoP6c4, tlTTwoP6c5, tlTTwoP6c6,
      tlTTwoP6c7, tlTTwoP6c8, tlTTwoP6c9, tlTTwoQ6c0, tlTTwoQ6c1, tlTTwoQ6c2,
      tlTTwoQ6c3, tlTTwoQ6c4, tlTTwoQ6c5]
  ring1

lemma tlTTwo_s7 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ + tlNSqP2c8 f ξ + tlNSqP2c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ + tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ +
        tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ
        + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ + tlTTwoP7c12 f ξ + tlTTwoP7c13 f ξ +
        tlTTwoP7c14 f ξ + tlTTwoP7c15 f ξ + tlTTwoP7c16 f ξ + tlTTwoP7c17 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ7c0 f ξ) * hT + (tlTTwoQ7c1 f ξ) * hT + (tlTTwoQ7c2 f ξ) * hT + (tlTTwoQ7c3 f ξ) * hT
      + (tlTTwoQ7c4 f ξ) * hT + (tlTTwoQ7c5 f ξ) * hT + (tlTTwoQ7c6 f ξ) * hT + (tlTTwoQ7c7 f ξ) *
      hT
  simp only [tlD0, tlD1, tlNSqP2c6, tlNSqP2c7, tlNSqP2c8, tlNSqP2c9, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP7c0, tlTTwoP7c1, tlTTwoP7c10, tlTTwoP7c11, tlTTwoP7c12, tlTTwoP7c13,
      tlTTwoP7c14, tlTTwoP7c15, tlTTwoP7c16, tlTTwoP7c17, tlTTwoP7c2, tlTTwoP7c3,
      tlTTwoP7c4, tlTTwoP7c5, tlTTwoP7c6, tlTTwoP7c7, tlTTwoP7c8, tlTTwoP7c9,
      tlTTwoQ7c0, tlTTwoQ7c1, tlTTwoQ7c2, tlTTwoQ7c3, tlTTwoQ7c4, tlTTwoQ7c5,
      tlTTwoQ7c6, tlTTwoQ7c7]
  ring1

lemma tlTTwo_s8 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP2c10 f ξ + tlNSqP2c11 f ξ + tlNSqP2c12 f ξ + tlNSqP3c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ + tlTTwoP8c4 f ξ +
        tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ + tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ
        + tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ +
        tlTTwoP8c14 f ξ + tlTTwoP8c15 f ξ + tlTTwoP8c16 f ξ + tlTTwoP8c17 f ξ +
        tlTTwoP8c18 f ξ + tlTTwoP8c19 f ξ + tlTTwoP8c20 f ξ + tlTTwoP8c21 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ8c0 f ξ) * hT + (tlTTwoQ8c1 f ξ) * hT + (tlTTwoQ8c2 f ξ) * hT + (tlTTwoQ8c3 f ξ) * hT
      + (tlTTwoQ8c4 f ξ) * hT + (tlTTwoQ8c5 f ξ) * hT + (tlTTwoQ8c6 f ξ) * hT + (tlTTwoQ8c7 f ξ) *
      hT
  simp only [tlD0, tlD1, tlNSqP2c10, tlNSqP2c11, tlNSqP2c12, tlNSqP3c0, tlT0, tlT1, tlT2,
      tlT3, tlTTwoP8c0, tlTTwoP8c1, tlTTwoP8c10, tlTTwoP8c11, tlTTwoP8c12,
      tlTTwoP8c13, tlTTwoP8c14, tlTTwoP8c15, tlTTwoP8c16, tlTTwoP8c17, tlTTwoP8c18,
      tlTTwoP8c19, tlTTwoP8c2, tlTTwoP8c20, tlTTwoP8c21, tlTTwoP8c3, tlTTwoP8c4,
      tlTTwoP8c5, tlTTwoP8c6, tlTTwoP8c7, tlTTwoP8c8, tlTTwoP8c9, tlTTwoQ8c0,
      tlTTwoQ8c1, tlTTwoQ8c2, tlTTwoQ8c3, tlTTwoQ8c4, tlTTwoQ8c5, tlTTwoQ8c6,
      tlTTwoQ8c7]
  ring1

lemma tlTTwo_s9 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP3c1 f ξ + tlNSqP3c2 f ξ + tlNSqP3c3 f ξ + tlNSqP3c4 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ +
        tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ + tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ
        + tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ9c0 f ξ) * hT + (tlTTwoQ9c1 f ξ) * hT + (tlTTwoQ9c2 f ξ) * hT + (tlTTwoQ9c3 f ξ) * hT
      + (tlTTwoQ9c4 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c1, tlNSqP3c2, tlNSqP3c3, tlNSqP3c4, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP9c0, tlTTwoP9c1, tlTTwoP9c10, tlTTwoP9c11, tlTTwoP9c12, tlTTwoP9c13,
      tlTTwoP9c2, tlTTwoP9c3, tlTTwoP9c4, tlTTwoP9c5, tlTTwoP9c6, tlTTwoP9c7,
      tlTTwoP9c8, tlTTwoP9c9, tlTTwoQ9c0, tlTTwoQ9c1, tlTTwoQ9c2, tlTTwoQ9c3,
      tlTTwoQ9c4]
  ring1

lemma tlTTwo_s10 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP3c5 f ξ + tlNSqP3c6 f ξ + tlNSqP3c7 f ξ + tlNSqP3c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ + tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4
        f ξ + tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ +
        tlTTwoP10c9 f ξ + tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ + tlTTwoP10c12 f ξ +
        tlTTwoP10c13 f ξ + tlTTwoP10c14 f ξ + tlTTwoP10c15 f ξ + tlTTwoP10c16 f ξ +
        tlTTwoP10c17 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ10c0 f ξ) * hT + (tlTTwoQ10c1 f ξ) * hT + (tlTTwoQ10c2 f ξ) * hT + (tlTTwoQ10c3 f ξ) *
      hT + (tlTTwoQ10c4 f ξ) * hT + (tlTTwoQ10c5 f ξ) * hT + (tlTTwoQ10c6 f ξ) * hT + (tlTTwoQ10c7
      f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c5, tlNSqP3c6, tlNSqP3c7, tlNSqP3c8, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP10c0, tlTTwoP10c1, tlTTwoP10c10, tlTTwoP10c11, tlTTwoP10c12,
      tlTTwoP10c13, tlTTwoP10c14, tlTTwoP10c15, tlTTwoP10c16, tlTTwoP10c17,
      tlTTwoP10c2, tlTTwoP10c3, tlTTwoP10c4, tlTTwoP10c5, tlTTwoP10c6, tlTTwoP10c7,
      tlTTwoP10c8, tlTTwoP10c9, tlTTwoQ10c0, tlTTwoQ10c1, tlTTwoQ10c2, tlTTwoQ10c3,
      tlTTwoQ10c4, tlTTwoQ10c5, tlTTwoQ10c6, tlTTwoQ10c7]
  ring1

lemma tlTTwo_s11 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP3c9 f ξ + tlNSqP3c10 f ξ + tlNSqP3c11 f ξ + tlNSqP3c12 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ + tlTTwoP11c4
        f ξ + tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ +
        tlTTwoP11c9 f ξ + tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ + tlTTwoP11c12 f ξ +
        tlTTwoP11c13 f ξ + tlTTwoP11c14 f ξ + tlTTwoP11c15 f ξ + tlTTwoP11c16 f ξ +
        tlTTwoP11c17 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ11c0 f ξ) * hT + (tlTTwoQ11c1 f ξ) * hT + (tlTTwoQ11c2 f ξ) * hT + (tlTTwoQ11c3 f ξ) *
      hT + (tlTTwoQ11c4 f ξ) * hT + (tlTTwoQ11c5 f ξ) * hT + (tlTTwoQ11c6 f ξ) * hT + (tlTTwoQ11c7
      f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c10, tlNSqP3c11, tlNSqP3c12, tlNSqP3c9, tlT0, tlT1, tlT2,
      tlT3, tlTTwoP11c0, tlTTwoP11c1, tlTTwoP11c10, tlTTwoP11c11, tlTTwoP11c12,
      tlTTwoP11c13, tlTTwoP11c14, tlTTwoP11c15, tlTTwoP11c16, tlTTwoP11c17,
      tlTTwoP11c2, tlTTwoP11c3, tlTTwoP11c4, tlTTwoP11c5, tlTTwoP11c6, tlTTwoP11c7,
      tlTTwoP11c8, tlTTwoP11c9, tlTTwoQ11c0, tlTTwoQ11c1, tlTTwoQ11c2, tlTTwoQ11c3,
      tlTTwoQ11c4, tlTTwoQ11c5, tlTTwoQ11c6, tlTTwoQ11c7]
  ring1

lemma tlTTwo_s12 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP3c13 f ξ + tlNSqP3c14 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ + tlTTwoP12c4
        f ξ + tlTTwoP12c5 f ξ + tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ +
        tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ +
        tlTTwoP12c13 f ξ := by
  linear_combination (norm := skip)
    (tlTTwoQ12c0 f ξ) * hT + (tlTTwoQ12c1 f ξ) * hT + (tlTTwoQ12c2 f ξ) * hT + (tlTTwoQ12c3 f ξ) *
      hT + (tlTTwoQ12c4 f ξ) * hT + (tlTTwoQ12c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c13, tlNSqP3c14, tlT0, tlT1, tlT2, tlT3, tlTTwoP12c0,
      tlTTwoP12c1, tlTTwoP12c10, tlTTwoP12c11, tlTTwoP12c12, tlTTwoP12c13,
      tlTTwoP12c2, tlTTwoP12c3, tlTTwoP12c4, tlTTwoP12c5, tlTTwoP12c6, tlTTwoP12c7,
      tlTTwoP12c8, tlTTwoP12c9, tlTTwoQ12c0, tlTTwoQ12c1, tlTTwoQ12c2, tlTTwoQ12c3,
      tlTTwoQ12c4, tlTTwoQ12c5]
  ring1

lemma tlTTwo_val {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlNSqP0c0 f ξ + tlNSqP0c1 f ξ + tlNSqP0c2 f ξ + tlNSqP0c3 f ξ + tlNSqP0c4 f ξ + tlNSqP0c5 f ξ
      + tlNSqP0c6 f ξ + tlNSqP0c7 f ξ + tlNSqP0c8 f ξ + tlNSqP0c9 f ξ + tlNSqP1c0 f ξ + tlNSqP1c1
      f ξ + tlNSqP1c2 f ξ + tlNSqP1c3 f ξ + tlNSqP1c4 f ξ + tlNSqP1c5 f ξ + tlNSqP1c6 f ξ +
      tlNSqP1c7 f ξ + tlNSqP1c8 f ξ + tlNSqP1c9 f ξ + tlNSqP1c10 f ξ + tlNSqP1c11 f ξ + tlNSqP2c0
      f ξ + tlNSqP2c1 f ξ + tlNSqP2c2 f ξ + tlNSqP2c3 f ξ + tlNSqP2c4 f ξ + tlNSqP2c5 f ξ +
      tlNSqP2c6 f ξ + tlNSqP2c7 f ξ + tlNSqP2c8 f ξ + tlNSqP2c9 f ξ + tlNSqP2c10 f ξ + tlNSqP2c11
      f ξ + tlNSqP2c12 f ξ + tlNSqP3c0 f ξ + tlNSqP3c1 f ξ + tlNSqP3c2 f ξ + tlNSqP3c3 f ξ +
      tlNSqP3c4 f ξ + tlNSqP3c5 f ξ + tlNSqP3c6 f ξ + tlNSqP3c7 f ξ + tlNSqP3c8 f ξ + tlNSqP3c9 f
      ξ + tlNSqP3c10 f ξ + tlNSqP3c11 f ξ + tlNSqP3c12 f ξ + tlNSqP3c13 f ξ + tlNSqP3c14 f ξ) *
      (tlD0 f ξ + tlD1 f ξ) =
      tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
        tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ
        + tlTTwoP0c10 f ξ + tlTTwoP0c11 f ξ + tlTTwoP0c12 f ξ + tlTTwoP1c0 f ξ +
        tlTTwoP1c1 f ξ + tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ
        + tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ + tlTTwoP1c10
        f ξ + tlTTwoP1c11 f ξ + tlTTwoP1c12 f ξ + tlTTwoP1c13 f ξ + tlTTwoP1c14 f ξ +
        tlTTwoP1c15 f ξ + tlTTwoP1c16 f ξ + tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ + tlTTwoP2c2 f
        ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ + tlTTwoP2c7
        f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ +
        tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ +
        tlTTwoP2c16 f ξ + tlTTwoP2c17 f ξ + tlTTwoP2c18 f ξ + tlTTwoP3c0 f ξ + tlTTwoP3c1
        f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ +
        tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f
        ξ + tlTTwoP3c11 f ξ + tlTTwoP3c12 f ξ + tlTTwoP3c13 f ξ + tlTTwoP3c14 f ξ +
        tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ
        + tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ + tlTTwoP4c9 f
        ξ + tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ +
        tlTTwoP4c14 f ξ + tlTTwoP4c15 f ξ + tlTTwoP4c16 f ξ + tlTTwoP5c0 f ξ + tlTTwoP5c1
        f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ +
        tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ + tlTTwoP5c10 f
        ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ + tlTTwoP5c14 f ξ +
        tlTTwoP5c15 f ξ + tlTTwoP5c16 f ξ + tlTTwoP5c17 f ξ + tlTTwoP5c18 f ξ +
        tlTTwoP5c19 f ξ + tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f
        ξ + tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ + tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8
        f ξ + tlTTwoP6c9 f ξ + tlTTwoP6c10 f ξ + tlTTwoP6c11 f ξ + tlTTwoP6c12 f ξ +
        tlTTwoP6c13 f ξ + tlTTwoP6c14 f ξ + tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ + tlTTwoP7c2 f
        ξ + tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ + tlTTwoP7c7
        f ξ + tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ +
        tlTTwoP7c12 f ξ + tlTTwoP7c13 f ξ + tlTTwoP7c14 f ξ + tlTTwoP7c15 f ξ +
        tlTTwoP7c16 f ξ + tlTTwoP7c17 f ξ + tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f
        ξ + tlTTwoP8c3 f ξ + tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7
        f ξ + tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ + tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ +
        tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ + tlTTwoP8c14 f ξ + tlTTwoP8c15 f ξ +
        tlTTwoP8c16 f ξ + tlTTwoP8c17 f ξ + tlTTwoP8c18 f ξ + tlTTwoP8c19 f ξ +
        tlTTwoP8c20 f ξ + tlTTwoP8c21 f ξ + tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f
        ξ + tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7
        f ξ + tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ + tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ +
        tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ + tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ +
        tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ +
        tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ +
        tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ + tlTTwoP10c12 f ξ + tlTTwoP10c13 f ξ +
        tlTTwoP10c14 f ξ + tlTTwoP10c15 f ξ + tlTTwoP10c16 f ξ + tlTTwoP10c17 f ξ +
        tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ +
        tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ +
        tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ + tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ +
        tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ + tlTTwoP11c14 f ξ + tlTTwoP11c15 f ξ +
        tlTTwoP11c16 f ξ + tlTTwoP11c17 f ξ + tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ +
        tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ + tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ +
        tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ +
        tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ := by
  linear_combination
    tlTTwo_s0 hT + tlTTwo_s1 hT + tlTTwo_s2 hT + tlTTwo_s3 hT + tlTTwo_s4 hT + tlTTwo_s5 hT +
      tlTTwo_s6 hT + tlTTwo_s7 hT + tlTTwo_s8 hT + tlTTwo_s9 hT + tlTTwo_s10 hT + tlTTwo_s11 hT +
      tlTTwo_s12 hT

lemma tlTOne_s0 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c0 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
        tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP0c9 f ξ
        := by
  linear_combination (norm := skip)
    (tlTOneQ0c0 f ξ) * hT + (tlTOneQ0c1 f ξ) * hT
  simp only [tlDSqP0c0, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP0c0,
      tlTOneP0c1, tlTOneP0c2, tlTOneP0c3, tlTOneP0c4, tlTOneP0c5, tlTOneP0c6,
      tlTOneP0c7, tlTOneP0c8, tlTOneP0c9, tlTOneQ0c0, tlTOneQ0c1]
  ring1

lemma tlTOne_s1 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c1 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP1c0 f ξ + tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ +
        tlTOneP1c5 f ξ + tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ
        + tlTOneP1c10 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ1c0 f ξ) * hT + (tlTOneQ1c1 f ξ) * hT + (tlTOneQ1c2 f ξ) * hT
  simp only [tlDSqP0c1, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP1c0,
      tlTOneP1c1, tlTOneP1c10, tlTOneP1c2, tlTOneP1c3, tlTOneP1c4, tlTOneP1c5,
      tlTOneP1c6, tlTOneP1c7, tlTOneP1c8, tlTOneP1c9, tlTOneQ1c0, tlTOneQ1c1,
      tlTOneQ1c2]
  ring1

lemma tlTOne_s2 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c2 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP2c0 f ξ + tlTOneP2c1 f ξ + tlTOneP2c2 f ξ + tlTOneP2c3 f ξ + tlTOneP2c4 f ξ +
        tlTOneP2c5 f ξ + tlTOneP2c6 f ξ + tlTOneP2c7 f ξ + tlTOneP2c8 f ξ + tlTOneP2c9 f ξ
        + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ + tlTOneP2c12 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ2c0 f ξ) * hT + (tlTOneQ2c1 f ξ) * hT + (tlTOneQ2c2 f ξ) * hT + (tlTOneQ2c3 f ξ) * hT
  simp only [tlDSqP0c2, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP2c0,
      tlTOneP2c1, tlTOneP2c10, tlTOneP2c11, tlTOneP2c12, tlTOneP2c2, tlTOneP2c3,
      tlTOneP2c4, tlTOneP2c5, tlTOneP2c6, tlTOneP2c7, tlTOneP2c8, tlTOneP2c9,
      tlTOneQ2c0, tlTOneQ2c1, tlTOneQ2c2, tlTOneQ2c3]
  ring1

lemma tlTOne_s3 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c3 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP3c0 f ξ + tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ +
        tlTOneP3c5 f ξ + tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ
        + tlTOneP3c10 f ξ + tlTOneP3c11 f ξ + tlTOneP3c12 f ξ + tlTOneP3c13 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ3c0 f ξ) * hT + (tlTOneQ3c1 f ξ) * hT + (tlTOneQ3c2 f ξ) * hT + (tlTOneQ3c3 f ξ) * hT
      + (tlTOneQ3c4 f ξ) * hT
  simp only [tlDSqP0c3, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP3c0,
      tlTOneP3c1, tlTOneP3c10, tlTOneP3c11, tlTOneP3c12, tlTOneP3c13, tlTOneP3c2,
      tlTOneP3c3, tlTOneP3c4, tlTOneP3c5, tlTOneP3c6, tlTOneP3c7, tlTOneP3c8,
      tlTOneP3c9, tlTOneQ3c0, tlTOneQ3c1, tlTOneQ3c2, tlTOneQ3c3, tlTOneQ3c4]
  ring1

lemma tlTOne_s4 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c4 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP4c0 f ξ + tlTOneP4c1 f ξ + tlTOneP4c2 f ξ + tlTOneP4c3 f ξ + tlTOneP4c4 f ξ +
        tlTOneP4c5 f ξ + tlTOneP4c6 f ξ + tlTOneP4c7 f ξ + tlTOneP4c8 f ξ + tlTOneP4c9 f ξ
        + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ + tlTOneP4c12 f ξ + tlTOneP4c13 f ξ +
        tlTOneP4c14 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ4c0 f ξ) * hT + (tlTOneQ4c1 f ξ) * hT + (tlTOneQ4c2 f ξ) * hT + (tlTOneQ4c3 f ξ) * hT
      + (tlTOneQ4c4 f ξ) * hT + (tlTOneQ4c5 f ξ) * hT
  simp only [tlDSqP0c4, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP4c0,
      tlTOneP4c1, tlTOneP4c10, tlTOneP4c11, tlTOneP4c12, tlTOneP4c13, tlTOneP4c14,
      tlTOneP4c2, tlTOneP4c3, tlTOneP4c4, tlTOneP4c5, tlTOneP4c6, tlTOneP4c7,
      tlTOneP4c8, tlTOneP4c9, tlTOneQ4c0, tlTOneQ4c1, tlTOneQ4c2, tlTOneQ4c3,
      tlTOneQ4c4, tlTOneQ4c5]
  ring1

lemma tlTOne_s5 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c5 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP5c0 f ξ + tlTOneP5c1 f ξ + tlTOneP5c2 f ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ +
        tlTOneP5c5 f ξ + tlTOneP5c6 f ξ + tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ
        + tlTOneP5c10 f ξ + tlTOneP5c11 f ξ + tlTOneP5c12 f ξ + tlTOneP5c13 f ξ +
        tlTOneP5c14 f ξ + tlTOneP5c15 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ5c0 f ξ) * hT + (tlTOneQ5c1 f ξ) * hT + (tlTOneQ5c2 f ξ) * hT + (tlTOneQ5c3 f ξ) * hT
      + (tlTOneQ5c4 f ξ) * hT + (tlTOneQ5c5 f ξ) * hT + (tlTOneQ5c6 f) * hT
  simp only [tlDSqP0c5, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP5c0,
      tlTOneP5c1, tlTOneP5c10, tlTOneP5c11, tlTOneP5c12, tlTOneP5c13, tlTOneP5c14,
      tlTOneP5c15, tlTOneP5c2, tlTOneP5c3, tlTOneP5c4, tlTOneP5c5, tlTOneP5c6,
      tlTOneP5c7, tlTOneP5c8, tlTOneP5c9, tlTOneQ5c0, tlTOneQ5c1, tlTOneQ5c2,
      tlTOneQ5c3, tlTOneQ5c4, tlTOneQ5c5, tlTOneQ5c6]
  ring1

lemma tlTOne_s6 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c6 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP6c0 f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ + tlTOneP6c3 f ξ + tlTOneP6c4 f ξ +
        tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ + tlTOneP6c8 f ξ + tlTOneP6c9 f ξ
        + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ + tlTOneP6c13 f ξ +
        tlTOneP6c14 f ξ + tlTOneP6c15 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ6c0 f ξ) * hT + (tlTOneQ6c1 f ξ) * hT + (tlTOneQ6c2 f ξ) * hT + (tlTOneQ6c3 f ξ) * hT
      + (tlTOneQ6c4 f ξ) * hT + (tlTOneQ6c5 f ξ) * hT + (tlTOneQ6c6 f ξ) * hT
  simp only [tlDSqP0c6, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP6c0,
      tlTOneP6c1, tlTOneP6c10, tlTOneP6c11, tlTOneP6c12, tlTOneP6c13, tlTOneP6c14,
      tlTOneP6c15, tlTOneP6c2, tlTOneP6c3, tlTOneP6c4, tlTOneP6c5, tlTOneP6c6,
      tlTOneP6c7, tlTOneP6c8, tlTOneP6c9, tlTOneQ6c0, tlTOneQ6c1, tlTOneQ6c2,
      tlTOneQ6c3, tlTOneQ6c4, tlTOneQ6c5, tlTOneQ6c6]
  ring1

lemma tlTOne_s7 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c7 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ +
        tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ
        + tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP7c13 f ξ +
        tlTOneP7c14 f ξ + tlTOneP7c15 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ7c0 f ξ) * hT + (tlTOneQ7c1 f ξ) * hT + (tlTOneQ7c2 f ξ) * hT + (tlTOneQ7c3 f ξ) * hT
      + (tlTOneQ7c4 f ξ) * hT + (tlTOneQ7c5 f ξ) * hT + (tlTOneQ7c6 f ξ) * hT
  simp only [tlDSqP0c7, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP7c0,
      tlTOneP7c1, tlTOneP7c10, tlTOneP7c11, tlTOneP7c12, tlTOneP7c13, tlTOneP7c14,
      tlTOneP7c15, tlTOneP7c2, tlTOneP7c3, tlTOneP7c4, tlTOneP7c5, tlTOneP7c6,
      tlTOneP7c7, tlTOneP7c8, tlTOneP7c9, tlTOneQ7c0, tlTOneQ7c1, tlTOneQ7c2,
      tlTOneQ7c3, tlTOneQ7c4, tlTOneQ7c5, tlTOneQ7c6]
  ring1

lemma tlTOne_s8 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c8 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP8c0 f ξ + tlTOneP8c1 f ξ + tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ +
        tlTOneP8c5 f ξ + tlTOneP8c6 f ξ + tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ
        + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ + tlTOneP8c12 f ξ + tlTOneP8c13 f ξ +
        tlTOneP8c14 f ξ + tlTOneP8c15 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ8c0 f ξ) * hT + (tlTOneQ8c1 f ξ) * hT + (tlTOneQ8c2 f ξ) * hT + (tlTOneQ8c3 f ξ) * hT
      + (tlTOneQ8c4 f ξ) * hT + (tlTOneQ8c5 f ξ) * hT + (tlTOneQ8c6 f ξ) * hT
  simp only [tlDSqP0c8, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP8c0,
      tlTOneP8c1, tlTOneP8c10, tlTOneP8c11, tlTOneP8c12, tlTOneP8c13, tlTOneP8c14,
      tlTOneP8c15, tlTOneP8c2, tlTOneP8c3, tlTOneP8c4, tlTOneP8c5, tlTOneP8c6,
      tlTOneP8c7, tlTOneP8c8, tlTOneP8c9, tlTOneQ8c0, tlTOneQ8c1, tlTOneQ8c2,
      tlTOneQ8c3, tlTOneQ8c4, tlTOneQ8c5, tlTOneQ8c6]
  ring1

lemma tlTOne_s9 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c9 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ + tlTOneP9c3 f ξ + tlTOneP9c4 f ξ +
        tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ + tlTOneP9c8 f ξ + tlTOneP9c9 f ξ
        + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ + tlTOneP9c13 f ξ +
        tlTOneP9c14 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ9c0 f ξ) * hT + (tlTOneQ9c1 f ξ) * hT + (tlTOneQ9c2 f ξ) * hT + (tlTOneQ9c3 f ξ) * hT
      + (tlTOneQ9c4 f ξ) * hT + (tlTOneQ9c5 f ξ) * hT + (tlTOneQ9c6 f ξ) * hT
  simp only [tlDSqP0c9, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3, tlTOneP9c0,
      tlTOneP9c1, tlTOneP9c10, tlTOneP9c11, tlTOneP9c12, tlTOneP9c13, tlTOneP9c14,
      tlTOneP9c2, tlTOneP9c3, tlTOneP9c4, tlTOneP9c5, tlTOneP9c6, tlTOneP9c7,
      tlTOneP9c8, tlTOneP9c9, tlTOneQ9c0, tlTOneQ9c1, tlTOneQ9c2, tlTOneQ9c3,
      tlTOneQ9c4, tlTOneQ9c5, tlTOneQ9c6]
  ring1

lemma tlTOne_s10 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c10 f ξ + tlDSqP0c11 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP10c0 f ξ + tlTOneP10c1 f ξ + tlTOneP10c2 f ξ + tlTOneP10c3 f ξ + tlTOneP10c4
        f ξ + tlTOneP10c5 f ξ + tlTOneP10c6 f ξ + tlTOneP10c7 f ξ + tlTOneP10c8 f ξ +
        tlTOneP10c9 f ξ + tlTOneP10c10 f ξ + tlTOneP10c11 f ξ + tlTOneP10c12 f ξ +
        tlTOneP10c13 f ξ + tlTOneP10c14 f ξ + tlTOneP10c15 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ10c0 f ξ) * hT + (tlTOneQ10c1 f ξ) * hT + (tlTOneQ10c2 f ξ) * hT + (tlTOneQ10c3 f ξ) *
      hT + (tlTOneQ10c4 f ξ) * hT + (tlTOneQ10c5 f ξ) * hT + (tlTOneQ10c6 f ξ) * hT + (tlTOneQ10c7
      f ξ) * hT
  simp only [tlDSqP0c10, tlDSqP0c11, tlN0, tlN1, tlN2, tlN3, tlN4, tlT0, tlT1, tlT2, tlT3,
      tlTOneP10c0, tlTOneP10c1, tlTOneP10c10, tlTOneP10c11, tlTOneP10c12,
      tlTOneP10c13, tlTOneP10c14, tlTOneP10c15, tlTOneP10c2, tlTOneP10c3,
      tlTOneP10c4, tlTOneP10c5, tlTOneP10c6, tlTOneP10c7, tlTOneP10c8, tlTOneP10c9,
      tlTOneQ10c0, tlTOneQ10c1, tlTOneQ10c2, tlTOneQ10c3, tlTOneQ10c4, tlTOneQ10c5,
      tlTOneQ10c6, tlTOneQ10c7]
  ring1

lemma tlTOne_val {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDSqP0c0 f ξ + tlDSqP0c1 f ξ + tlDSqP0c2 f ξ + tlDSqP0c3 f ξ + tlDSqP0c4 f ξ + tlDSqP0c5 f ξ
      + tlDSqP0c6 f ξ + tlDSqP0c7 f ξ + tlDSqP0c8 f ξ + tlDSqP0c9 f ξ + tlDSqP0c10 f ξ +
      tlDSqP0c11 f ξ) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) =
      tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
        tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP0c9 f ξ
        + tlTOneP1c0 f ξ + tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f
        ξ + tlTOneP1c5 f ξ + tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9
        f ξ + tlTOneP1c10 f ξ + tlTOneP2c0 f ξ + tlTOneP2c1 f ξ + tlTOneP2c2 f ξ +
        tlTOneP2c3 f ξ + tlTOneP2c4 f ξ + tlTOneP2c5 f ξ + tlTOneP2c6 f ξ + tlTOneP2c7 f ξ
        + tlTOneP2c8 f ξ + tlTOneP2c9 f ξ + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ +
        tlTOneP2c12 f ξ + tlTOneP3c0 f ξ + tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f
        ξ + tlTOneP3c4 f ξ + tlTOneP3c5 f ξ + tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8
        f ξ + tlTOneP3c9 f ξ + tlTOneP3c10 f ξ + tlTOneP3c11 f ξ + tlTOneP3c12 f ξ +
        tlTOneP3c13 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ + tlTOneP4c2 f ξ + tlTOneP4c3 f
        ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ + tlTOneP4c7 f ξ + tlTOneP4c8
        f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ + tlTOneP4c12 f ξ +
        tlTOneP4c13 f ξ + tlTOneP4c14 f ξ + tlTOneP5c0 f ξ + tlTOneP5c1 f ξ + tlTOneP5c2 f
        ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ + tlTOneP5c5 f ξ + tlTOneP5c6 f ξ + tlTOneP5c7
        f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ + tlTOneP5c11 f ξ +
        tlTOneP5c12 f ξ + tlTOneP5c13 f ξ + tlTOneP5c14 f ξ + tlTOneP5c15 f ξ + tlTOneP6c0
        f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ + tlTOneP6c3 f ξ + tlTOneP6c4 f ξ +
        tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ + tlTOneP6c8 f ξ + tlTOneP6c9 f ξ
        + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ + tlTOneP6c13 f ξ +
        tlTOneP6c14 f ξ + tlTOneP6c15 f ξ + tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f
        ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ + tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7
        f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ + tlTOneP7c10 f ξ + tlTOneP7c11 f ξ +
        tlTOneP7c12 f ξ + tlTOneP7c13 f ξ + tlTOneP7c14 f ξ + tlTOneP7c15 f ξ + tlTOneP8c0
        f ξ + tlTOneP8c1 f ξ + tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ +
        tlTOneP8c5 f ξ + tlTOneP8c6 f ξ + tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ
        + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ + tlTOneP8c12 f ξ + tlTOneP8c13 f ξ +
        tlTOneP8c14 f ξ + tlTOneP8c15 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f
        ξ + tlTOneP9c3 f ξ + tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7
        f ξ + tlTOneP9c8 f ξ + tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ +
        tlTOneP9c12 f ξ + tlTOneP9c13 f ξ + tlTOneP9c14 f ξ + tlTOneP10c0 f ξ +
        tlTOneP10c1 f ξ + tlTOneP10c2 f ξ + tlTOneP10c3 f ξ + tlTOneP10c4 f ξ +
        tlTOneP10c5 f ξ + tlTOneP10c6 f ξ + tlTOneP10c7 f ξ + tlTOneP10c8 f ξ +
        tlTOneP10c9 f ξ + tlTOneP10c10 f ξ + tlTOneP10c11 f ξ + tlTOneP10c12 f ξ +
        tlTOneP10c13 f ξ + tlTOneP10c14 f ξ + tlTOneP10c15 f ξ := by
  linear_combination
    tlTOne_s0 hT + tlTOne_s1 hT + tlTOne_s2 hT + tlTOne_s3 hT + tlTOne_s4 hT + tlTOne_s5 hT +
      tlTOne_s6 hT + tlTOne_s7 hT + tlTOne_s8 hT + tlTOne_s9 hT + tlTOne_s10 hT

lemma tlWTwoX_s0 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
      tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ +
      tlTTwoP0c10 f ξ + tlTTwoP0c11 f ξ + tlTTwoP0c12 f ξ + tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ +
      tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ +
      tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ + tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ +
      tlTTwoP1c12 f ξ + tlTTwoP1c13 f ξ + tlTTwoP1c14 f ξ + tlTTwoP1c15 f ξ + tlTTwoP1c16 f ξ +
      tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ + tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ +
      tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ + tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ +
      tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ + tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ +
      tlTTwoP2c15 f ξ + tlTTwoP2c16 f ξ + tlTTwoP2c17 f ξ + tlTTwoP2c18 f ξ + tlTTwoP3c0 f ξ +
      tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) *
      tlMTwoV0 f =
      tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ + tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ + tlWTwoXP0c4
        f ξ + tlWTwoXP0c5 f ξ + tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ + tlWTwoXP0c8 f ξ +
        tlWTwoXP0c9 f ξ + tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ + tlWTwoXP0c12 f ξ +
        tlWTwoXP0c13 f ξ + tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ + tlWTwoXP0c16 f ξ +
        tlWTwoXP0c17 f ξ + tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP0c0, tlTTwoP0c1, tlTTwoP0c10,
      tlTTwoP0c11, tlTTwoP0c12, tlTTwoP0c2, tlTTwoP0c3, tlTTwoP0c4, tlTTwoP0c5,
      tlTTwoP0c6, tlTTwoP0c7, tlTTwoP0c8, tlTTwoP0c9, tlTTwoP1c0, tlTTwoP1c1,
      tlTTwoP1c10, tlTTwoP1c11, tlTTwoP1c12, tlTTwoP1c13, tlTTwoP1c14, tlTTwoP1c15,
      tlTTwoP1c16, tlTTwoP1c2, tlTTwoP1c3, tlTTwoP1c4, tlTTwoP1c5, tlTTwoP1c6,
      tlTTwoP1c7, tlTTwoP1c8, tlTTwoP1c9, tlTTwoP2c0, tlTTwoP2c1, tlTTwoP2c10,
      tlTTwoP2c11, tlTTwoP2c12, tlTTwoP2c13, tlTTwoP2c14, tlTTwoP2c15, tlTTwoP2c16,
      tlTTwoP2c17, tlTTwoP2c18, tlTTwoP2c2, tlTTwoP2c3, tlTTwoP2c4, tlTTwoP2c5,
      tlTTwoP2c6, tlTTwoP2c7, tlTTwoP2c8, tlTTwoP2c9, tlTTwoP3c0, tlTTwoP3c1,
      tlTTwoP3c2, tlTTwoP3c3, tlTTwoP3c4, tlTTwoP3c5, tlWTwoXP0c0, tlWTwoXP0c1,
      tlWTwoXP0c10, tlWTwoXP0c11, tlWTwoXP0c12, tlWTwoXP0c13, tlWTwoXP0c14,
      tlWTwoXP0c15, tlWTwoXP0c16, tlWTwoXP0c17, tlWTwoXP0c18, tlWTwoXP0c19,
      tlWTwoXP0c2, tlWTwoXP0c3, tlWTwoXP0c4, tlWTwoXP0c5, tlWTwoXP0c6, tlWTwoXP0c7,
      tlWTwoXP0c8, tlWTwoXP0c9]
  ring1

lemma tlWTwoX_s1 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ +
      tlTTwoP3c11 f ξ + tlTTwoP3c12 f ξ + tlTTwoP3c13 f ξ + tlTTwoP3c14 f ξ + tlTTwoP4c0 f ξ +
      tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ +
      tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ +
      tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ + tlTTwoP4c14 f ξ + tlTTwoP4c15 f ξ +
      tlTTwoP4c16 f ξ + tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ +
      tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ +
      tlTTwoP5c9 f ξ + tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ +
      tlTTwoP5c14 f ξ + tlTTwoP5c15 f ξ + tlTTwoP5c16 f ξ + tlTTwoP5c17 f ξ + tlTTwoP5c18 f ξ +
      tlTTwoP5c19 f ξ + tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ +
      tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ + tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ) * tlMTwoV0 f =
      tlWTwoXP1c0 f ξ + tlWTwoXP1c1 f ξ + tlWTwoXP1c2 f ξ + tlWTwoXP1c3 f ξ + tlWTwoXP1c4
        f ξ + tlWTwoXP1c5 f ξ + tlWTwoXP1c6 f ξ + tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ +
        tlWTwoXP1c9 f ξ + tlWTwoXP1c10 f ξ + tlWTwoXP1c11 f ξ + tlWTwoXP1c12 f ξ +
        tlWTwoXP1c13 f ξ + tlWTwoXP1c14 f ξ + tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ +
        tlWTwoXP1c17 f ξ + tlWTwoXP1c18 f ξ + tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ +
        tlWTwoXP1c21 f ξ + tlWTwoXP1c22 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP3c10, tlTTwoP3c11, tlTTwoP3c12,
      tlTTwoP3c13, tlTTwoP3c14, tlTTwoP3c6, tlTTwoP3c7, tlTTwoP3c8, tlTTwoP3c9,
      tlTTwoP4c0, tlTTwoP4c1, tlTTwoP4c10, tlTTwoP4c11, tlTTwoP4c12, tlTTwoP4c13,
      tlTTwoP4c14, tlTTwoP4c15, tlTTwoP4c16, tlTTwoP4c2, tlTTwoP4c3, tlTTwoP4c4,
      tlTTwoP4c5, tlTTwoP4c6, tlTTwoP4c7, tlTTwoP4c8, tlTTwoP4c9, tlTTwoP5c0,
      tlTTwoP5c1, tlTTwoP5c10, tlTTwoP5c11, tlTTwoP5c12, tlTTwoP5c13, tlTTwoP5c14,
      tlTTwoP5c15, tlTTwoP5c16, tlTTwoP5c17, tlTTwoP5c18, tlTTwoP5c19, tlTTwoP5c2,
      tlTTwoP5c3, tlTTwoP5c4, tlTTwoP5c5, tlTTwoP5c6, tlTTwoP5c7, tlTTwoP5c8,
      tlTTwoP5c9, tlTTwoP6c0, tlTTwoP6c1, tlTTwoP6c2, tlTTwoP6c3, tlTTwoP6c4,
      tlTTwoP6c5, tlTTwoP6c6, tlTTwoP6c7, tlWTwoXP1c0, tlWTwoXP1c1, tlWTwoXP1c10,
      tlWTwoXP1c11, tlWTwoXP1c12, tlWTwoXP1c13, tlWTwoXP1c14, tlWTwoXP1c15,
      tlWTwoXP1c16, tlWTwoXP1c17, tlWTwoXP1c18, tlWTwoXP1c19, tlWTwoXP1c2,
      tlWTwoXP1c20, tlWTwoXP1c21, tlWTwoXP1c22, tlWTwoXP1c3, tlWTwoXP1c4,
      tlWTwoXP1c5, tlWTwoXP1c6, tlWTwoXP1c7, tlWTwoXP1c8, tlWTwoXP1c9]
  ring1

lemma tlWTwoX_s2 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ + tlTTwoP6c10 f ξ + tlTTwoP6c11 f ξ + tlTTwoP6c12 f ξ +
      tlTTwoP6c13 f ξ + tlTTwoP6c14 f ξ + tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ + tlTTwoP7c2 f ξ +
      tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ +
      tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ + tlTTwoP7c12 f ξ +
      tlTTwoP7c13 f ξ + tlTTwoP7c14 f ξ + tlTTwoP7c15 f ξ + tlTTwoP7c16 f ξ + tlTTwoP7c17 f ξ +
      tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ + tlTTwoP8c4 f ξ +
      tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ + tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ +
      tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ + tlTTwoP8c14 f ξ +
      tlTTwoP8c15 f ξ + tlTTwoP8c16 f ξ + tlTTwoP8c17 f ξ + tlTTwoP8c18 f ξ + tlTTwoP8c19 f ξ +
      tlTTwoP8c20 f ξ + tlTTwoP8c21 f ξ + tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ +
      tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ +
      tlTTwoP9c8 f ξ) * tlMTwoV0 f =
      tlWTwoXP2c0 f ξ + tlWTwoXP2c1 f ξ + tlWTwoXP2c2 f ξ + tlWTwoXP2c3 f ξ + tlWTwoXP2c4
        f ξ + tlWTwoXP2c5 f ξ + tlWTwoXP2c6 f ξ + tlWTwoXP2c7 f ξ + tlWTwoXP2c8 f ξ +
        tlWTwoXP2c9 f ξ + tlWTwoXP2c10 f ξ + tlWTwoXP2c11 f ξ + tlWTwoXP2c12 f ξ +
        tlWTwoXP2c13 f ξ + tlWTwoXP2c14 f ξ + tlWTwoXP2c15 f ξ + tlWTwoXP2c16 f ξ +
        tlWTwoXP2c17 f ξ + tlWTwoXP2c18 f ξ + tlWTwoXP2c19 f ξ + tlWTwoXP2c20 f ξ +
        tlWTwoXP2c21 f ξ + tlWTwoXP2c22 f ξ + tlWTwoXP2c23 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP6c10, tlTTwoP6c11, tlTTwoP6c12,
      tlTTwoP6c13, tlTTwoP6c14, tlTTwoP6c8, tlTTwoP6c9, tlTTwoP7c0, tlTTwoP7c1,
      tlTTwoP7c10, tlTTwoP7c11, tlTTwoP7c12, tlTTwoP7c13, tlTTwoP7c14, tlTTwoP7c15,
      tlTTwoP7c16, tlTTwoP7c17, tlTTwoP7c2, tlTTwoP7c3, tlTTwoP7c4, tlTTwoP7c5,
      tlTTwoP7c6, tlTTwoP7c7, tlTTwoP7c8, tlTTwoP7c9, tlTTwoP8c0, tlTTwoP8c1,
      tlTTwoP8c10, tlTTwoP8c11, tlTTwoP8c12, tlTTwoP8c13, tlTTwoP8c14, tlTTwoP8c15,
      tlTTwoP8c16, tlTTwoP8c17, tlTTwoP8c18, tlTTwoP8c19, tlTTwoP8c2, tlTTwoP8c20,
      tlTTwoP8c21, tlTTwoP8c3, tlTTwoP8c4, tlTTwoP8c5, tlTTwoP8c6, tlTTwoP8c7,
      tlTTwoP8c8, tlTTwoP8c9, tlTTwoP9c0, tlTTwoP9c1, tlTTwoP9c2, tlTTwoP9c3,
      tlTTwoP9c4, tlTTwoP9c5, tlTTwoP9c6, tlTTwoP9c7, tlTTwoP9c8, tlWTwoXP2c0,
      tlWTwoXP2c1, tlWTwoXP2c10, tlWTwoXP2c11, tlWTwoXP2c12, tlWTwoXP2c13,
      tlWTwoXP2c14, tlWTwoXP2c15, tlWTwoXP2c16, tlWTwoXP2c17, tlWTwoXP2c18,
      tlWTwoXP2c19, tlWTwoXP2c2, tlWTwoXP2c20, tlWTwoXP2c21, tlWTwoXP2c22,
      tlWTwoXP2c23, tlWTwoXP2c3, tlWTwoXP2c4, tlWTwoXP2c5, tlWTwoXP2c6, tlWTwoXP2c7,
      tlWTwoXP2c8, tlWTwoXP2c9]
  ring1

lemma tlWTwoX_s3 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTTwoP9c9 f ξ + tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ +
      tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ + tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ +
      tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ +
      tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ + tlTTwoP10c12 f ξ + tlTTwoP10c13 f ξ + tlTTwoP10c14 f ξ
      + tlTTwoP10c15 f ξ + tlTTwoP10c16 f ξ + tlTTwoP10c17 f ξ + tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ
      + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ + tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ +
      tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ + tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ +
      tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ + tlTTwoP11c14 f ξ + tlTTwoP11c15 f ξ + tlTTwoP11c16 f ξ
      + tlTTwoP11c17 f ξ + tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ +
      tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ + tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ +
      tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ)
      * tlMTwoV0 f =
      tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ + tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ + tlWTwoXP3c4
        f ξ + tlWTwoXP3c5 f ξ + tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ + tlWTwoXP3c8 f ξ +
        tlWTwoXP3c9 f ξ + tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ + tlWTwoXP3c12 f ξ +
        tlWTwoXP3c13 f ξ + tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ + tlWTwoXP3c16 f ξ +
        tlWTwoXP3c17 f ξ + tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ + tlWTwoXP3c20 f ξ +
        tlWTwoXP3c21 f ξ + tlWTwoXP3c22 f ξ + tlWTwoXP3c23 f ξ + tlWTwoXP3c24 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMTwoV0, tlT0, tlT1, tlT2, tlT3, tlTTwoP10c0, tlTTwoP10c1, tlTTwoP10c10,
      tlTTwoP10c11, tlTTwoP10c12, tlTTwoP10c13, tlTTwoP10c14, tlTTwoP10c15,
      tlTTwoP10c16, tlTTwoP10c17, tlTTwoP10c2, tlTTwoP10c3, tlTTwoP10c4,
      tlTTwoP10c5, tlTTwoP10c6, tlTTwoP10c7, tlTTwoP10c8, tlTTwoP10c9, tlTTwoP11c0,
      tlTTwoP11c1, tlTTwoP11c10, tlTTwoP11c11, tlTTwoP11c12, tlTTwoP11c13,
      tlTTwoP11c14, tlTTwoP11c15, tlTTwoP11c16, tlTTwoP11c17, tlTTwoP11c2,
      tlTTwoP11c3, tlTTwoP11c4, tlTTwoP11c5, tlTTwoP11c6, tlTTwoP11c7, tlTTwoP11c8,
      tlTTwoP11c9, tlTTwoP12c0, tlTTwoP12c1, tlTTwoP12c10, tlTTwoP12c11,
      tlTTwoP12c12, tlTTwoP12c13, tlTTwoP12c2, tlTTwoP12c3, tlTTwoP12c4,
      tlTTwoP12c5, tlTTwoP12c6, tlTTwoP12c7, tlTTwoP12c8, tlTTwoP12c9, tlTTwoP9c10,
      tlTTwoP9c11, tlTTwoP9c12, tlTTwoP9c13, tlTTwoP9c9, tlWTwoXP3c0, tlWTwoXP3c1,
      tlWTwoXP3c10, tlWTwoXP3c11, tlWTwoXP3c12, tlWTwoXP3c13, tlWTwoXP3c14,
      tlWTwoXP3c15, tlWTwoXP3c16, tlWTwoXP3c17, tlWTwoXP3c18, tlWTwoXP3c19,
      tlWTwoXP3c2, tlWTwoXP3c20, tlWTwoXP3c21, tlWTwoXP3c22, tlWTwoXP3c23,
      tlWTwoXP3c24, tlWTwoXP3c3, tlWTwoXP3c4, tlWTwoXP3c5, tlWTwoXP3c6, tlWTwoXP3c7,
      tlWTwoXP3c8, tlWTwoXP3c9]
  ring1

lemma tlWTwoX_val {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ + tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ +
      tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ +
      tlTTwoP0c10 f ξ + tlTTwoP0c11 f ξ + tlTTwoP0c12 f ξ + tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ +
      tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ + tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ +
      tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ + tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ +
      tlTTwoP1c12 f ξ + tlTTwoP1c13 f ξ + tlTTwoP1c14 f ξ + tlTTwoP1c15 f ξ + tlTTwoP1c16 f ξ +
      tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ + tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ +
      tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ + tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ +
      tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ + tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ +
      tlTTwoP2c15 f ξ + tlTTwoP2c16 f ξ + tlTTwoP2c17 f ξ + tlTTwoP2c18 f ξ + tlTTwoP3c0 f ξ +
      tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ +
      tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ + tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ +
      tlTTwoP3c11 f ξ + tlTTwoP3c12 f ξ + tlTTwoP3c13 f ξ + tlTTwoP3c14 f ξ + tlTTwoP4c0 f ξ +
      tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ +
      tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ + tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ +
      tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ + tlTTwoP4c14 f ξ + tlTTwoP4c15 f ξ +
      tlTTwoP4c16 f ξ + tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ +
      tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ + tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ +
      tlTTwoP5c9 f ξ + tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ +
      tlTTwoP5c14 f ξ + tlTTwoP5c15 f ξ + tlTTwoP5c16 f ξ + tlTTwoP5c17 f ξ + tlTTwoP5c18 f ξ +
      tlTTwoP5c19 f ξ + tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ +
      tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ + tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ +
      tlTTwoP6c9 f ξ + tlTTwoP6c10 f ξ + tlTTwoP6c11 f ξ + tlTTwoP6c12 f ξ + tlTTwoP6c13 f ξ +
      tlTTwoP6c14 f ξ + tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ + tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ +
      tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ + tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ +
      tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ + tlTTwoP7c12 f ξ + tlTTwoP7c13 f ξ +
      tlTTwoP7c14 f ξ + tlTTwoP7c15 f ξ + tlTTwoP7c16 f ξ + tlTTwoP7c17 f ξ + tlTTwoP8c0 f ξ +
      tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ + tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ +
      tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ + tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ + tlTTwoP8c10 f ξ +
      tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ + tlTTwoP8c14 f ξ + tlTTwoP8c15 f ξ +
      tlTTwoP8c16 f ξ + tlTTwoP8c17 f ξ + tlTTwoP8c18 f ξ + tlTTwoP8c19 f ξ + tlTTwoP8c20 f ξ +
      tlTTwoP8c21 f ξ + tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ +
      tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ + tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ + tlTTwoP9c8 f ξ +
      tlTTwoP9c9 f ξ + tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ +
      tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ + tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ +
      tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ +
      tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ + tlTTwoP10c12 f ξ + tlTTwoP10c13 f ξ + tlTTwoP10c14 f ξ
      + tlTTwoP10c15 f ξ + tlTTwoP10c16 f ξ + tlTTwoP10c17 f ξ + tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ
      + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ + tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ +
      tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ + tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ +
      tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ + tlTTwoP11c14 f ξ + tlTTwoP11c15 f ξ + tlTTwoP11c16 f ξ
      + tlTTwoP11c17 f ξ + tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ +
      tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ + tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ +
      tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ)
      * tlMTwoV0 f =
      tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ + tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ + tlWTwoXP0c4
        f ξ + tlWTwoXP0c5 f ξ + tlWTwoXP0c6 f ξ + tlWTwoXP0c7 f ξ + tlWTwoXP0c8 f ξ +
        tlWTwoXP0c9 f ξ + tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ + tlWTwoXP0c12 f ξ +
        tlWTwoXP0c13 f ξ + tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ + tlWTwoXP0c16 f ξ +
        tlWTwoXP0c17 f ξ + tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ + tlWTwoXP1c0 f ξ +
        tlWTwoXP1c1 f ξ + tlWTwoXP1c2 f ξ + tlWTwoXP1c3 f ξ + tlWTwoXP1c4 f ξ +
        tlWTwoXP1c5 f ξ + tlWTwoXP1c6 f ξ + tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ +
        tlWTwoXP1c9 f ξ + tlWTwoXP1c10 f ξ + tlWTwoXP1c11 f ξ + tlWTwoXP1c12 f ξ +
        tlWTwoXP1c13 f ξ + tlWTwoXP1c14 f ξ + tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ +
        tlWTwoXP1c17 f ξ + tlWTwoXP1c18 f ξ + tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ +
        tlWTwoXP1c21 f ξ + tlWTwoXP1c22 f ξ + tlWTwoXP2c0 f ξ + tlWTwoXP2c1 f ξ +
        tlWTwoXP2c2 f ξ + tlWTwoXP2c3 f ξ + tlWTwoXP2c4 f ξ + tlWTwoXP2c5 f ξ +
        tlWTwoXP2c6 f ξ + tlWTwoXP2c7 f ξ + tlWTwoXP2c8 f ξ + tlWTwoXP2c9 f ξ +
        tlWTwoXP2c10 f ξ + tlWTwoXP2c11 f ξ + tlWTwoXP2c12 f ξ + tlWTwoXP2c13 f ξ +
        tlWTwoXP2c14 f ξ + tlWTwoXP2c15 f ξ + tlWTwoXP2c16 f ξ + tlWTwoXP2c17 f ξ +
        tlWTwoXP2c18 f ξ + tlWTwoXP2c19 f ξ + tlWTwoXP2c20 f ξ + tlWTwoXP2c21 f ξ +
        tlWTwoXP2c22 f ξ + tlWTwoXP2c23 f ξ + tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ +
        tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ + tlWTwoXP3c4 f ξ + tlWTwoXP3c5 f ξ +
        tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ + tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ +
        tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ + tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ +
        tlWTwoXP3c14 f ξ + tlWTwoXP3c15 f ξ + tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ +
        tlWTwoXP3c18 f ξ + tlWTwoXP3c19 f ξ + tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ +
        tlWTwoXP3c22 f ξ + tlWTwoXP3c23 f ξ + tlWTwoXP3c24 f ξ := by
  linear_combination
    tlWTwoX_s0 hT + tlWTwoX_s1 hT + tlWTwoX_s2 hT + tlWTwoX_s3 hT

lemma tlWOneX_s0 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
      tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP0c9 f ξ +
      tlTOneP1c0 f ξ + tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ +
      tlTOneP1c5 f ξ + tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ +
      tlTOneP1c10 f ξ + tlTOneP2c0 f ξ + tlTOneP2c1 f ξ + tlTOneP2c2 f ξ + tlTOneP2c3 f ξ) *
      tlMOneV0 f =
      tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ + tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ + tlWOneXP0c4
        f ξ + tlWOneXP0c5 f ξ + tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ + tlWOneXP0c8 f ξ +
        tlWOneXP0c9 f ξ + tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ + tlWOneXP0c12 f ξ +
        tlWOneXP0c13 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP0c0, tlTOneP0c1, tlTOneP0c2,
      tlTOneP0c3, tlTOneP0c4, tlTOneP0c5, tlTOneP0c6, tlTOneP0c7, tlTOneP0c8,
      tlTOneP0c9, tlTOneP1c0, tlTOneP1c1, tlTOneP1c10, tlTOneP1c2, tlTOneP1c3,
      tlTOneP1c4, tlTOneP1c5, tlTOneP1c6, tlTOneP1c7, tlTOneP1c8, tlTOneP1c9,
      tlTOneP2c0, tlTOneP2c1, tlTOneP2c2, tlTOneP2c3, tlWOneXP0c0, tlWOneXP0c1,
      tlWOneXP0c10, tlWOneXP0c11, tlWOneXP0c12, tlWOneXP0c13, tlWOneXP0c2,
      tlWOneXP0c3, tlWOneXP0c4, tlWOneXP0c5, tlWOneXP0c6, tlWOneXP0c7, tlWOneXP0c8,
      tlWOneXP0c9]
  ring1

lemma tlWOneX_s1 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTOneP2c4 f ξ + tlTOneP2c5 f ξ + tlTOneP2c6 f ξ + tlTOneP2c7 f ξ + tlTOneP2c8 f ξ +
      tlTOneP2c9 f ξ + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ + tlTOneP2c12 f ξ + tlTOneP3c0 f ξ +
      tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ + tlTOneP3c5 f ξ +
      tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ + tlTOneP3c10 f ξ +
      tlTOneP3c11 f ξ + tlTOneP3c12 f ξ + tlTOneP3c13 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) *
      tlMOneV0 f =
      tlWOneXP1c0 f ξ + tlWOneXP1c1 f ξ + tlWOneXP1c2 f ξ + tlWOneXP1c3 f ξ + tlWOneXP1c4
        f ξ + tlWOneXP1c5 f ξ + tlWOneXP1c6 f ξ + tlWOneXP1c7 f ξ + tlWOneXP1c8 f ξ +
        tlWOneXP1c9 f ξ + tlWOneXP1c10 f ξ + tlWOneXP1c11 f ξ + tlWOneXP1c12 f ξ +
        tlWOneXP1c13 f ξ + tlWOneXP1c14 f ξ + tlWOneXP1c15 f ξ + tlWOneXP1c16 f ξ +
        tlWOneXP1c17 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP2c10, tlTOneP2c11, tlTOneP2c12,
      tlTOneP2c4, tlTOneP2c5, tlTOneP2c6, tlTOneP2c7, tlTOneP2c8, tlTOneP2c9,
      tlTOneP3c0, tlTOneP3c1, tlTOneP3c10, tlTOneP3c11, tlTOneP3c12, tlTOneP3c13,
      tlTOneP3c2, tlTOneP3c3, tlTOneP3c4, tlTOneP3c5, tlTOneP3c6, tlTOneP3c7,
      tlTOneP3c8, tlTOneP3c9, tlTOneP4c0, tlTOneP4c1, tlWOneXP1c0, tlWOneXP1c1,
      tlWOneXP1c10, tlWOneXP1c11, tlWOneXP1c12, tlWOneXP1c13, tlWOneXP1c14,
      tlWOneXP1c15, tlWOneXP1c16, tlWOneXP1c17, tlWOneXP1c2, tlWOneXP1c3,
      tlWOneXP1c4, tlWOneXP1c5, tlWOneXP1c6, tlWOneXP1c7, tlWOneXP1c8, tlWOneXP1c9]
  ring1

lemma tlWOneX_s2 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTOneP4c2 f ξ + tlTOneP4c3 f ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ +
      tlTOneP4c7 f ξ + tlTOneP4c8 f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ +
      tlTOneP4c12 f ξ + tlTOneP4c13 f ξ + tlTOneP4c14 f ξ + tlTOneP5c0 f ξ + tlTOneP5c1 f ξ +
      tlTOneP5c2 f ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ + tlTOneP5c5 f ξ + tlTOneP5c6 f ξ +
      tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ) * tlMOneV0 f =
      tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ + tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ + tlWOneXP2c4
        f ξ + tlWOneXP2c5 f ξ + tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ + tlWOneXP2c8 f ξ +
        tlWOneXP2c9 f ξ + tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ + tlWOneXP2c12 f ξ +
        tlWOneXP2c13 f ξ + tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ + tlWOneXP2c16 f ξ +
        tlWOneXP2c17 f ξ + tlWOneXP2c18 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP4c10, tlTOneP4c11, tlTOneP4c12,
      tlTOneP4c13, tlTOneP4c14, tlTOneP4c2, tlTOneP4c3, tlTOneP4c4, tlTOneP4c5,
      tlTOneP4c6, tlTOneP4c7, tlTOneP4c8, tlTOneP4c9, tlTOneP5c0, tlTOneP5c1,
      tlTOneP5c10, tlTOneP5c2, tlTOneP5c3, tlTOneP5c4, tlTOneP5c5, tlTOneP5c6,
      tlTOneP5c7, tlTOneP5c8, tlTOneP5c9, tlWOneXP2c0, tlWOneXP2c1, tlWOneXP2c10,
      tlWOneXP2c11, tlWOneXP2c12, tlWOneXP2c13, tlWOneXP2c14, tlWOneXP2c15,
      tlWOneXP2c16, tlWOneXP2c17, tlWOneXP2c18, tlWOneXP2c2, tlWOneXP2c3,
      tlWOneXP2c4, tlWOneXP2c5, tlWOneXP2c6, tlWOneXP2c7, tlWOneXP2c8, tlWOneXP2c9]
  ring1

lemma tlWOneX_s3 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTOneP5c11 f ξ + tlTOneP5c12 f ξ + tlTOneP5c13 f ξ + tlTOneP5c14 f ξ + tlTOneP5c15 f ξ +
      tlTOneP6c0 f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ + tlTOneP6c3 f ξ + tlTOneP6c4 f ξ +
      tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ + tlTOneP6c8 f ξ + tlTOneP6c9 f ξ +
      tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ + tlTOneP6c13 f ξ + tlTOneP6c14 f ξ +
      tlTOneP6c15 f ξ + tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ +
      tlTOneP7c4 f ξ) * tlMOneV0 f =
      tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ + tlWOneXP3c2 f ξ + tlWOneXP3c3 f ξ + tlWOneXP3c4
        f ξ + tlWOneXP3c5 f ξ + tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ + tlWOneXP3c8 f ξ +
        tlWOneXP3c9 f ξ + tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ + tlWOneXP3c12 f ξ +
        tlWOneXP3c13 f ξ + tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ + tlWOneXP3c16 f ξ +
        tlWOneXP3c17 f ξ + tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP5c11, tlTOneP5c12, tlTOneP5c13,
      tlTOneP5c14, tlTOneP5c15, tlTOneP6c0, tlTOneP6c1, tlTOneP6c10, tlTOneP6c11,
      tlTOneP6c12, tlTOneP6c13, tlTOneP6c14, tlTOneP6c15, tlTOneP6c2, tlTOneP6c3,
      tlTOneP6c4, tlTOneP6c5, tlTOneP6c6, tlTOneP6c7, tlTOneP6c8, tlTOneP6c9,
      tlTOneP7c0, tlTOneP7c1, tlTOneP7c2, tlTOneP7c3, tlTOneP7c4, tlWOneXP3c0,
      tlWOneXP3c1, tlWOneXP3c10, tlWOneXP3c11, tlWOneXP3c12, tlWOneXP3c13,
      tlWOneXP3c14, tlWOneXP3c15, tlWOneXP3c16, tlWOneXP3c17, tlWOneXP3c18,
      tlWOneXP3c19, tlWOneXP3c2, tlWOneXP3c3, tlWOneXP3c4, tlWOneXP3c5, tlWOneXP3c6,
      tlWOneXP3c7, tlWOneXP3c8, tlWOneXP3c9]
  ring1

lemma tlWOneX_s4 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ +
      tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP7c13 f ξ + tlTOneP7c14 f ξ +
      tlTOneP7c15 f ξ + tlTOneP8c0 f ξ + tlTOneP8c1 f ξ + tlTOneP8c2 f ξ + tlTOneP8c3 f ξ +
      tlTOneP8c4 f ξ + tlTOneP8c5 f ξ + tlTOneP8c6 f ξ + tlTOneP8c7 f ξ + tlTOneP8c8 f ξ +
      tlTOneP8c9 f ξ + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ + tlTOneP8c12 f ξ + tlTOneP8c13 f ξ) *
      tlMOneV0 f =
      tlWOneXP4c0 f ξ + tlWOneXP4c1 f ξ + tlWOneXP4c2 f ξ + tlWOneXP4c3 f ξ + tlWOneXP4c4
        f ξ + tlWOneXP4c5 f ξ + tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ + tlWOneXP4c8 f ξ +
        tlWOneXP4c9 f ξ + tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ + tlWOneXP4c12 f ξ +
        tlWOneXP4c13 f ξ + tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ + tlWOneXP4c16 f ξ +
        tlWOneXP4c17 f ξ + tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP7c10, tlTOneP7c11, tlTOneP7c12,
      tlTOneP7c13, tlTOneP7c14, tlTOneP7c15, tlTOneP7c5, tlTOneP7c6, tlTOneP7c7,
      tlTOneP7c8, tlTOneP7c9, tlTOneP8c0, tlTOneP8c1, tlTOneP8c10, tlTOneP8c11,
      tlTOneP8c12, tlTOneP8c13, tlTOneP8c2, tlTOneP8c3, tlTOneP8c4, tlTOneP8c5,
      tlTOneP8c6, tlTOneP8c7, tlTOneP8c8, tlTOneP8c9, tlWOneXP4c0, tlWOneXP4c1,
      tlWOneXP4c10, tlWOneXP4c11, tlWOneXP4c12, tlWOneXP4c13, tlWOneXP4c14,
      tlWOneXP4c15, tlWOneXP4c16, tlWOneXP4c17, tlWOneXP4c18, tlWOneXP4c19,
      tlWOneXP4c2, tlWOneXP4c3, tlWOneXP4c4, tlWOneXP4c5, tlWOneXP4c6, tlWOneXP4c7,
      tlWOneXP4c8, tlWOneXP4c9]
  ring1

lemma tlWOneX_s5 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTOneP8c14 f ξ + tlTOneP8c15 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ +
      tlTOneP9c3 f ξ + tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ +
      tlTOneP9c8 f ξ + tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ +
      tlTOneP9c13 f ξ + tlTOneP9c14 f ξ + tlTOneP10c0 f ξ + tlTOneP10c1 f ξ + tlTOneP10c2 f ξ +
      tlTOneP10c3 f ξ + tlTOneP10c4 f ξ + tlTOneP10c5 f ξ + tlTOneP10c6 f ξ + tlTOneP10c7 f ξ) *
      tlMOneV0 f =
      tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ + tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ + tlWOneXP5c4
        f ξ + tlWOneXP5c5 f ξ + tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ + tlWOneXP5c8 f ξ +
        tlWOneXP5c9 f ξ + tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ + tlWOneXP5c12 f ξ +
        tlWOneXP5c13 f ξ + tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ + tlWOneXP5c16 f ξ +
        tlWOneXP5c17 f ξ + tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP10c0, tlTOneP10c1, tlTOneP10c2,
      tlTOneP10c3, tlTOneP10c4, tlTOneP10c5, tlTOneP10c6, tlTOneP10c7, tlTOneP8c14,
      tlTOneP8c15, tlTOneP9c0, tlTOneP9c1, tlTOneP9c10, tlTOneP9c11, tlTOneP9c12,
      tlTOneP9c13, tlTOneP9c14, tlTOneP9c2, tlTOneP9c3, tlTOneP9c4, tlTOneP9c5,
      tlTOneP9c6, tlTOneP9c7, tlTOneP9c8, tlTOneP9c9, tlWOneXP5c0, tlWOneXP5c1,
      tlWOneXP5c10, tlWOneXP5c11, tlWOneXP5c12, tlWOneXP5c13, tlWOneXP5c14,
      tlWOneXP5c15, tlWOneXP5c16, tlWOneXP5c17, tlWOneXP5c18, tlWOneXP5c19,
      tlWOneXP5c2, tlWOneXP5c3, tlWOneXP5c4, tlWOneXP5c5, tlWOneXP5c6, tlWOneXP5c7,
      tlWOneXP5c8, tlWOneXP5c9]
  ring1

lemma tlWOneX_s6 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTOneP10c8 f ξ + tlTOneP10c9 f ξ + tlTOneP10c10 f ξ + tlTOneP10c11 f ξ + tlTOneP10c12 f ξ +
      tlTOneP10c13 f ξ + tlTOneP10c14 f ξ + tlTOneP10c15 f ξ) * tlMOneV0 f =
      tlWOneXP6c0 f ξ + tlWOneXP6c1 f ξ + tlWOneXP6c2 f ξ + tlWOneXP6c3 f ξ + tlWOneXP6c4
        f ξ + tlWOneXP6c5 f ξ + tlWOneXP6c6 f ξ + tlWOneXP6c7 f ξ + tlWOneXP6c8 f ξ +
        tlWOneXP6c9 f ξ + tlWOneXP6c10 f ξ + tlWOneXP6c11 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP10c10, tlTOneP10c11, tlTOneP10c12,
      tlTOneP10c13, tlTOneP10c14, tlTOneP10c15, tlTOneP10c8, tlTOneP10c9,
      tlWOneXP6c0, tlWOneXP6c1, tlWOneXP6c10, tlWOneXP6c11, tlWOneXP6c2,
      tlWOneXP6c3, tlWOneXP6c4, tlWOneXP6c5, tlWOneXP6c6, tlWOneXP6c7, tlWOneXP6c8,
      tlWOneXP6c9]
  ring1

lemma tlWOneX_val {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
      tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP0c9 f ξ +
      tlTOneP1c0 f ξ + tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ +
      tlTOneP1c5 f ξ + tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ +
      tlTOneP1c10 f ξ + tlTOneP2c0 f ξ + tlTOneP2c1 f ξ + tlTOneP2c2 f ξ + tlTOneP2c3 f ξ +
      tlTOneP2c4 f ξ + tlTOneP2c5 f ξ + tlTOneP2c6 f ξ + tlTOneP2c7 f ξ + tlTOneP2c8 f ξ +
      tlTOneP2c9 f ξ + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ + tlTOneP2c12 f ξ + tlTOneP3c0 f ξ +
      tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ + tlTOneP3c5 f ξ +
      tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ + tlTOneP3c10 f ξ +
      tlTOneP3c11 f ξ + tlTOneP3c12 f ξ + tlTOneP3c13 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ +
      tlTOneP4c2 f ξ + tlTOneP4c3 f ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ +
      tlTOneP4c7 f ξ + tlTOneP4c8 f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ +
      tlTOneP4c12 f ξ + tlTOneP4c13 f ξ + tlTOneP4c14 f ξ + tlTOneP5c0 f ξ + tlTOneP5c1 f ξ +
      tlTOneP5c2 f ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ + tlTOneP5c5 f ξ + tlTOneP5c6 f ξ +
      tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ + tlTOneP5c11 f ξ +
      tlTOneP5c12 f ξ + tlTOneP5c13 f ξ + tlTOneP5c14 f ξ + tlTOneP5c15 f ξ + tlTOneP6c0 f ξ +
      tlTOneP6c1 f ξ + tlTOneP6c2 f ξ + tlTOneP6c3 f ξ + tlTOneP6c4 f ξ + tlTOneP6c5 f ξ +
      tlTOneP6c6 f ξ + tlTOneP6c7 f ξ + tlTOneP6c8 f ξ + tlTOneP6c9 f ξ + tlTOneP6c10 f ξ +
      tlTOneP6c11 f ξ + tlTOneP6c12 f ξ + tlTOneP6c13 f ξ + tlTOneP6c14 f ξ + tlTOneP6c15 f ξ +
      tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ +
      tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ +
      tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP7c13 f ξ + tlTOneP7c14 f ξ +
      tlTOneP7c15 f ξ + tlTOneP8c0 f ξ + tlTOneP8c1 f ξ + tlTOneP8c2 f ξ + tlTOneP8c3 f ξ +
      tlTOneP8c4 f ξ + tlTOneP8c5 f ξ + tlTOneP8c6 f ξ + tlTOneP8c7 f ξ + tlTOneP8c8 f ξ +
      tlTOneP8c9 f ξ + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ + tlTOneP8c12 f ξ + tlTOneP8c13 f ξ +
      tlTOneP8c14 f ξ + tlTOneP8c15 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ +
      tlTOneP9c3 f ξ + tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ +
      tlTOneP9c8 f ξ + tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ +
      tlTOneP9c13 f ξ + tlTOneP9c14 f ξ + tlTOneP10c0 f ξ + tlTOneP10c1 f ξ + tlTOneP10c2 f ξ +
      tlTOneP10c3 f ξ + tlTOneP10c4 f ξ + tlTOneP10c5 f ξ + tlTOneP10c6 f ξ + tlTOneP10c7 f ξ +
      tlTOneP10c8 f ξ + tlTOneP10c9 f ξ + tlTOneP10c10 f ξ + tlTOneP10c11 f ξ + tlTOneP10c12 f ξ +
      tlTOneP10c13 f ξ + tlTOneP10c14 f ξ + tlTOneP10c15 f ξ) * tlMOneV0 f =
      tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ + tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ + tlWOneXP0c4
        f ξ + tlWOneXP0c5 f ξ + tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ + tlWOneXP0c8 f ξ +
        tlWOneXP0c9 f ξ + tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ + tlWOneXP0c12 f ξ +
        tlWOneXP0c13 f ξ + tlWOneXP1c0 f ξ + tlWOneXP1c1 f ξ + tlWOneXP1c2 f ξ +
        tlWOneXP1c3 f ξ + tlWOneXP1c4 f ξ + tlWOneXP1c5 f ξ + tlWOneXP1c6 f ξ +
        tlWOneXP1c7 f ξ + tlWOneXP1c8 f ξ + tlWOneXP1c9 f ξ + tlWOneXP1c10 f ξ +
        tlWOneXP1c11 f ξ + tlWOneXP1c12 f ξ + tlWOneXP1c13 f ξ + tlWOneXP1c14 f ξ +
        tlWOneXP1c15 f ξ + tlWOneXP1c16 f ξ + tlWOneXP1c17 f ξ + tlWOneXP2c0 f ξ +
        tlWOneXP2c1 f ξ + tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ + tlWOneXP2c4 f ξ +
        tlWOneXP2c5 f ξ + tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ + tlWOneXP2c8 f ξ +
        tlWOneXP2c9 f ξ + tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ + tlWOneXP2c12 f ξ +
        tlWOneXP2c13 f ξ + tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ + tlWOneXP2c16 f ξ +
        tlWOneXP2c17 f ξ + tlWOneXP2c18 f ξ + tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ +
        tlWOneXP3c2 f ξ + tlWOneXP3c3 f ξ + tlWOneXP3c4 f ξ + tlWOneXP3c5 f ξ +
        tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ + tlWOneXP3c8 f ξ + tlWOneXP3c9 f ξ +
        tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ + tlWOneXP3c12 f ξ + tlWOneXP3c13 f ξ +
        tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ + tlWOneXP3c16 f ξ + tlWOneXP3c17 f ξ +
        tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ + tlWOneXP4c0 f ξ + tlWOneXP4c1 f ξ +
        tlWOneXP4c2 f ξ + tlWOneXP4c3 f ξ + tlWOneXP4c4 f ξ + tlWOneXP4c5 f ξ +
        tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ + tlWOneXP4c8 f ξ + tlWOneXP4c9 f ξ +
        tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ + tlWOneXP4c12 f ξ + tlWOneXP4c13 f ξ +
        tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ + tlWOneXP4c16 f ξ + tlWOneXP4c17 f ξ +
        tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ + tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ +
        tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ + tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ +
        tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ + tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ +
        tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ + tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ +
        tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ + tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ +
        tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ + tlWOneXP6c0 f ξ + tlWOneXP6c1 f ξ +
        tlWOneXP6c2 f ξ + tlWOneXP6c3 f ξ + tlWOneXP6c4 f ξ + tlWOneXP6c5 f ξ +
        tlWOneXP6c6 f ξ + tlWOneXP6c7 f ξ + tlWOneXP6c8 f ξ + tlWOneXP6c9 f ξ +
        tlWOneXP6c10 f ξ + tlWOneXP6c11 f ξ := by
  linear_combination
    tlWOneX_s0 hT + tlWOneX_s1 hT + tlWOneX_s2 hT + tlWOneX_s3 hT + tlWOneX_s4 hT +
      tlWOneX_s5 hT + tlWOneX_s6 hT

lemma tlWZeroX_s0 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDCbP0c0 f ξ + tlDCbP0c1 f ξ + tlDCbP0c2 f ξ + tlDCbP0c3 f ξ + tlDCbP0c4 f ξ + tlDCbP0c5 f ξ
      + tlDCbP0c6 f ξ + tlDCbP0c7 f ξ + tlDCbP0c8 f ξ + tlDCbP0c9 f ξ + tlDCbP0c10 f ξ +
      tlDCbP0c11 f ξ + tlDCbP0c12 f ξ + tlDCbP1c0 f ξ + tlDCbP1c1 f ξ + tlDCbP1c2 f ξ) * tlMZeroV0
      f =
      tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ + tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ +
        tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ + tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ +
        tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ + tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ +
        tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ + tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f ξ +
        tlWZeroXP0c16 f ξ + tlWZeroXP0c17 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP0c0, tlDCbP0c1, tlDCbP0c10, tlDCbP0c11, tlDCbP0c12, tlDCbP0c2, tlDCbP0c3,
      tlDCbP0c4, tlDCbP0c5, tlDCbP0c6, tlDCbP0c7, tlDCbP0c8, tlDCbP0c9, tlDCbP1c0,
      tlDCbP1c1, tlDCbP1c2, tlMZeroV0, tlT0, tlT1, tlT2, tlT3, tlWZeroXP0c0,
      tlWZeroXP0c1, tlWZeroXP0c10, tlWZeroXP0c11, tlWZeroXP0c12, tlWZeroXP0c13,
      tlWZeroXP0c14, tlWZeroXP0c15, tlWZeroXP0c16, tlWZeroXP0c17, tlWZeroXP0c2,
      tlWZeroXP0c3, tlWZeroXP0c4, tlWZeroXP0c5, tlWZeroXP0c6, tlWZeroXP0c7,
      tlWZeroXP0c8, tlWZeroXP0c9]
  ring1

lemma tlWZeroX_s1 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDCbP1c3 f ξ + tlDCbP1c4 f ξ + tlDCbP1c5 f ξ + tlDCbP1c6 f ξ + tlDCbP1c7 f ξ + tlDCbP1c8 f ξ
      + tlDCbP1c9 f ξ + tlDCbP1c10 f ξ + tlDCbP1c11 f ξ + tlDCbP1c12 f ξ + tlDCbP1c13 f ξ +
      tlDCbP1c14 f ξ + tlDCbP1c15 f ξ + tlDCbP1c16 f ξ + tlDCbP2c0 f ξ + tlDCbP2c1 f ξ) *
      tlMZeroV0 f =
      tlWZeroXP1c0 f ξ + tlWZeroXP1c1 f ξ + tlWZeroXP1c2 f ξ + tlWZeroXP1c3 f ξ +
        tlWZeroXP1c4 f ξ + tlWZeroXP1c5 f ξ + tlWZeroXP1c6 f ξ + tlWZeroXP1c7 f ξ +
        tlWZeroXP1c8 f ξ + tlWZeroXP1c9 f ξ + tlWZeroXP1c10 f ξ + tlWZeroXP1c11 f ξ +
        tlWZeroXP1c12 f ξ + tlWZeroXP1c13 f ξ + tlWZeroXP1c14 f ξ + tlWZeroXP1c15 f ξ +
        tlWZeroXP1c16 f ξ + tlWZeroXP1c17 f ξ + tlWZeroXP1c18 f ξ + tlWZeroXP1c19 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP1c10, tlDCbP1c11, tlDCbP1c12, tlDCbP1c13, tlDCbP1c14, tlDCbP1c15,
      tlDCbP1c16, tlDCbP1c3, tlDCbP1c4, tlDCbP1c5, tlDCbP1c6, tlDCbP1c7, tlDCbP1c8,
      tlDCbP1c9, tlDCbP2c0, tlDCbP2c1, tlMZeroV0, tlT0, tlT1, tlT2, tlT3,
      tlWZeroXP1c0, tlWZeroXP1c1, tlWZeroXP1c10, tlWZeroXP1c11, tlWZeroXP1c12,
      tlWZeroXP1c13, tlWZeroXP1c14, tlWZeroXP1c15, tlWZeroXP1c16, tlWZeroXP1c17,
      tlWZeroXP1c18, tlWZeroXP1c19, tlWZeroXP1c2, tlWZeroXP1c3, tlWZeroXP1c4,
      tlWZeroXP1c5, tlWZeroXP1c6, tlWZeroXP1c7, tlWZeroXP1c8, tlWZeroXP1c9]
  ring1

lemma tlWZeroX_s2 {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDCbP2c2 f ξ + tlDCbP2c3 f ξ + tlDCbP2c4 f ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ
      + tlDCbP2c8 f ξ + tlDCbP2c9 f ξ + tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ +
      tlDCbP2c13 f ξ + tlDCbP2c14 f ξ + tlDCbP2c15 f ξ + tlDCbP2c16 f ξ) * tlMZeroV0 f =
      tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ + tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ +
        tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ + tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ +
        tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ + tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ +
        tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ + tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f ξ +
        tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ + tlWZeroXP2c18 f ξ + tlWZeroXP2c19 f ξ +
        tlWZeroXP2c20 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP2c10, tlDCbP2c11, tlDCbP2c12, tlDCbP2c13, tlDCbP2c14, tlDCbP2c15,
      tlDCbP2c16, tlDCbP2c2, tlDCbP2c3, tlDCbP2c4, tlDCbP2c5, tlDCbP2c6, tlDCbP2c7,
      tlDCbP2c8, tlDCbP2c9, tlMZeroV0, tlT0, tlT1, tlT2, tlT3, tlWZeroXP2c0,
      tlWZeroXP2c1, tlWZeroXP2c10, tlWZeroXP2c11, tlWZeroXP2c12, tlWZeroXP2c13,
      tlWZeroXP2c14, tlWZeroXP2c15, tlWZeroXP2c16, tlWZeroXP2c17, tlWZeroXP2c18,
      tlWZeroXP2c19, tlWZeroXP2c2, tlWZeroXP2c20, tlWZeroXP2c3, tlWZeroXP2c4,
      tlWZeroXP2c5, tlWZeroXP2c6, tlWZeroXP2c7, tlWZeroXP2c8, tlWZeroXP2c9]
  ring1

lemma tlWZeroX_val {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlDCbP0c0 f ξ + tlDCbP0c1 f ξ + tlDCbP0c2 f ξ + tlDCbP0c3 f ξ + tlDCbP0c4 f ξ + tlDCbP0c5 f ξ
      + tlDCbP0c6 f ξ + tlDCbP0c7 f ξ + tlDCbP0c8 f ξ + tlDCbP0c9 f ξ + tlDCbP0c10 f ξ +
      tlDCbP0c11 f ξ + tlDCbP0c12 f ξ + tlDCbP1c0 f ξ + tlDCbP1c1 f ξ + tlDCbP1c2 f ξ + tlDCbP1c3
      f ξ + tlDCbP1c4 f ξ + tlDCbP1c5 f ξ + tlDCbP1c6 f ξ + tlDCbP1c7 f ξ + tlDCbP1c8 f ξ +
      tlDCbP1c9 f ξ + tlDCbP1c10 f ξ + tlDCbP1c11 f ξ + tlDCbP1c12 f ξ + tlDCbP1c13 f ξ +
      tlDCbP1c14 f ξ + tlDCbP1c15 f ξ + tlDCbP1c16 f ξ + tlDCbP2c0 f ξ + tlDCbP2c1 f ξ + tlDCbP2c2
      f ξ + tlDCbP2c3 f ξ + tlDCbP2c4 f ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ +
      tlDCbP2c8 f ξ + tlDCbP2c9 f ξ + tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ +
      tlDCbP2c13 f ξ + tlDCbP2c14 f ξ + tlDCbP2c15 f ξ + tlDCbP2c16 f ξ) * tlMZeroV0 f =
      tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ + tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ +
        tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ + tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ +
        tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ + tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ +
        tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ + tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f ξ +
        tlWZeroXP0c16 f ξ + tlWZeroXP0c17 f ξ + tlWZeroXP1c0 f ξ + tlWZeroXP1c1 f ξ +
        tlWZeroXP1c2 f ξ + tlWZeroXP1c3 f ξ + tlWZeroXP1c4 f ξ + tlWZeroXP1c5 f ξ +
        tlWZeroXP1c6 f ξ + tlWZeroXP1c7 f ξ + tlWZeroXP1c8 f ξ + tlWZeroXP1c9 f ξ +
        tlWZeroXP1c10 f ξ + tlWZeroXP1c11 f ξ + tlWZeroXP1c12 f ξ + tlWZeroXP1c13 f ξ +
        tlWZeroXP1c14 f ξ + tlWZeroXP1c15 f ξ + tlWZeroXP1c16 f ξ + tlWZeroXP1c17 f ξ +
        tlWZeroXP1c18 f ξ + tlWZeroXP1c19 f ξ + tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ +
        tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ + tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ +
        tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ + tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ +
        tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ + tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ +
        tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f ξ + tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ +
        tlWZeroXP2c18 f ξ + tlWZeroXP2c19 f ξ + tlWZeroXP2c20 f ξ := by
  linear_combination
    tlWZeroX_s0 hT + tlWZeroX_s1 hT + tlWZeroX_s2 hT

lemma trisection_chunks {f ξ : ℚ} (hT : trisectionPoly f ξ = 0) :
    tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0 := by
  simp only [trisectionPoly] at hT
  simp only [tlT0, tlT1, tlT2, tlT3]
  linear_combination hT

lemma tl_brM2 (f : ℚ) :
    tlMTwoV0 f = -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) := by
  simp only [tlMTwoV0]
  ring1

lemma tl_brM1 (f : ℚ) :
    tlMOneV0 f =
      -(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4
        - 145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) := by
  simp only [tlMOneV0]
  ring1

lemma tl_brM0 (f : ℚ) :
    tlMZeroV0 f =
      -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 *
        f ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 *
        f ^ 4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) := by
  simp only [tlMZeroV0]
  ring1

lemma tl_zero (f ξ : ℚ) :
    tlNCbP0c0 f ξ + tlNCbP0c1 f ξ + tlNCbP0c2 f ξ + tlNCbP0c3 f ξ + tlNCbP0c4 f ξ + tlNCbP0c5 f ξ
      + tlNCbP0c6 f ξ + tlNCbP0c7 f ξ + tlNCbP0c8 f ξ + tlNCbP0c9 f ξ + tlNCbP1c0 f ξ + tlNCbP1c1
      f ξ + tlNCbP1c2 f ξ + tlNCbP1c3 f ξ + tlNCbP1c4 f ξ + tlNCbP1c5 f ξ + tlNCbP1c6 f ξ +
      tlNCbP1c7 f ξ + tlNCbP1c8 f ξ + tlNCbP1c9 f ξ + tlNCbP1c10 f ξ + tlNCbP2c0 f ξ + tlNCbP2c1 f
      ξ + tlNCbP2c2 f ξ + tlNCbP2c3 f ξ + tlNCbP2c4 f ξ + tlNCbP2c5 f ξ + tlNCbP2c6 f ξ +
      tlNCbP2c7 f ξ + tlNCbP2c8 f ξ + tlNCbP2c9 f ξ + tlNCbP2c10 f ξ + tlNCbP2c11 f ξ + tlNCbP2c12
      f ξ + tlNCbP3c0 f ξ + tlNCbP3c1 f ξ + tlNCbP3c2 f ξ + tlNCbP3c3 f ξ + tlNCbP3c4 f ξ +
      tlNCbP3c5 f ξ + tlNCbP3c6 f ξ + tlNCbP3c7 f ξ + tlNCbP3c8 f ξ + tlNCbP3c9 f ξ + tlNCbP3c10 f
      ξ + tlNCbP3c11 f ξ + tlNCbP3c12 f ξ + tlNCbP3c13 f ξ + tlNCbP4c0 f ξ + tlNCbP4c1 f ξ +
      tlNCbP4c2 f ξ + tlNCbP4c3 f ξ + tlNCbP4c4 f ξ + tlNCbP4c5 f ξ + tlNCbP4c6 f ξ + tlNCbP4c7 f
      ξ + tlNCbP4c8 f ξ + tlNCbP4c9 f ξ + tlNCbP4c10 f ξ + tlNCbP4c11 f ξ + tlNCbP4c12 f ξ +
      tlNCbP4c13 f ξ + tlNCbP4c14 f ξ + tlNCbP5c0 f ξ + tlNCbP5c1 f ξ + tlNCbP5c2 f ξ + tlNCbP5c3
      f ξ + tlNCbP5c4 f ξ + tlNCbP5c5 f ξ + tlNCbP5c6 f ξ + tlNCbP5c7 f ξ + tlNCbP5c8 f ξ +
      tlNCbP5c9 f ξ + tlNCbP5c10 f ξ + tlNCbP5c11 f ξ + tlNCbP5c12 f ξ + tlNCbP5c13 f ξ +
      tlNCbP5c14 f ξ + tlNCbP6c0 f ξ + tlNCbP6c1 f ξ + tlNCbP6c2 f ξ + tlNCbP6c3 f ξ + tlNCbP6c4 f
      ξ + tlNCbP6c5 f ξ + tlNCbP6c6 f ξ + tlNCbP6c7 f ξ + tlNCbP6c8 f ξ + tlNCbP6c9 f ξ +
      tlNCbP6c10 f ξ + tlNCbP6c11 f ξ + tlNCbP6c12 f ξ + tlNCbP6c13 f ξ + tlNCbP6c14 f ξ +
      tlNCbP7c0 f ξ + tlNCbP7c1 f ξ + tlNCbP7c2 f ξ + tlNCbP7c3 f ξ + tlNCbP7c4 f ξ + tlNCbP7c5 f
      ξ + tlNCbP7c6 f ξ + tlNCbP7c7 f ξ + tlNCbP7c8 f ξ + tlNCbP7c9 f ξ + tlNCbP7c10 f ξ +
      tlNCbP7c11 f ξ + tlNCbP7c12 f ξ + tlNCbP7c13 f ξ + tlNCbP7c14 f ξ + tlNCbP8c0 f ξ +
      tlNCbP8c1 f ξ + tlNCbP8c2 f ξ + tlNCbP8c3 f ξ + tlNCbP8c4 f ξ + tlNCbP8c5 f ξ + tlNCbP8c6 f
      ξ + tlNCbP8c7 f ξ + tlNCbP8c8 f ξ + tlNCbP8c9 f ξ + tlNCbP8c10 f ξ + tlNCbP8c11 f ξ +
      tlNCbP8c12 f ξ + tlNCbP8c13 f ξ + tlNCbP8c14 f ξ + tlNCbP8c15 f ξ + tlNCbP9c0 f ξ +
      tlNCbP9c1 f ξ + tlNCbP9c2 f ξ + tlNCbP9c3 f ξ + tlNCbP9c4 f ξ + tlNCbP9c5 f ξ + tlNCbP9c6 f
      ξ + tlNCbP9c7 f ξ + tlNCbP9c8 f ξ + tlNCbP9c9 f ξ + tlNCbP10c0 f ξ + tlNCbP10c1 f ξ +
      tlNCbP10c2 f ξ + tlNCbP10c3 f ξ + tlNCbP10c4 f ξ + tlNCbP10c5 f ξ + tlNCbP10c6 f ξ +
      tlNCbP10c7 f ξ + tlNCbP10c8 f ξ + tlNCbP10c9 f ξ + tlNCbP10c10 f ξ + tlNCbP11c0 f ξ +
      tlNCbP11c1 f ξ + tlNCbP11c2 f ξ + tlNCbP11c3 f ξ + tlNCbP11c4 f ξ + tlNCbP11c5 f ξ +
      tlNCbP11c6 f ξ + tlNCbP11c7 f ξ + tlNCbP11c8 f ξ + tlNCbP11c9 f ξ + tlNCbP11c10 f ξ +
      tlNCbP11c11 f ξ + tlNCbP11c12 f ξ + tlNCbP12c0 f ξ + tlNCbP12c1 f ξ + tlNCbP12c2 f ξ +
      tlNCbP12c3 f ξ + tlNCbP12c4 f ξ + tlNCbP12c5 f ξ + tlNCbP12c6 f ξ + tlNCbP12c7 f ξ +
      tlNCbP12c8 f ξ + tlNCbP12c9 f ξ + tlNCbP12c10 f ξ + tlNCbP12c11 f ξ + tlNCbP12c12 f ξ +
      tlNCbP12c13 f ξ + tlNCbP13c0 f ξ + tlNCbP13c1 f ξ + tlNCbP13c2 f ξ + tlNCbP13c3 f ξ +
      tlNCbP13c4 f ξ + tlNCbP13c5 f ξ + tlNCbP13c6 f ξ + tlNCbP13c7 f ξ + tlNCbP13c8 f ξ +
      tlNCbP13c9 f ξ + tlNCbP13c10 f ξ + tlNCbP13c11 f ξ + tlNCbP13c12 f ξ + tlNCbP13c13 f ξ +
      tlNCbP13c14 f ξ + tlNCbP14c0 f ξ + tlNCbP14c1 f ξ + tlNCbP14c2 f ξ + tlNCbP14c3 f ξ +
      tlNCbP14c4 f ξ + tlNCbP14c5 f ξ + tlNCbP14c6 f ξ + tlNCbP14c7 f ξ + tlNCbP14c8 f ξ +
      tlNCbP14c9 f ξ + tlNCbP14c10 f ξ + tlNCbP14c11 f ξ + tlNCbP14c12 f ξ + tlNCbP14c13 f ξ +
      tlNCbP14c14 f ξ + tlNCbP14c15 f ξ + tlNCbP15c0 f ξ + tlNCbP15c1 f ξ + tlNCbP15c2 f ξ +
      tlNCbP15c3 f ξ + tlNCbP15c4 f ξ + tlNCbP15c5 f ξ + tlNCbP15c6 f ξ + tlNCbP15c7 f ξ +
      tlNCbP15c8 f ξ + tlNCbP15c9 f ξ + tlNCbP15c10 f ξ + tlNCbP15c11 f ξ + tlNCbP15c12 f ξ +
      tlNCbP15c13 f ξ + tlNCbP15c14 f ξ + tlNCbP15c15 f ξ + tlNCbP16c0 f ξ + tlNCbP16c1 f ξ +
      tlNCbP16c2 f ξ + tlNCbP16c3 f ξ + tlNCbP16c4 f ξ + tlNCbP16c5 f ξ + tlNCbP16c6 f ξ +
      tlNCbP16c7 f ξ + tlNCbP16c8 f ξ + tlNCbP16c9 f ξ + tlNCbP16c10 f ξ + tlNCbP16c11 f ξ +
      tlNCbP16c12 f ξ + tlNCbP16c13 f ξ + tlNCbP16c14 f ξ + tlNCbP16c15 f ξ + tlNCbP17c0 f ξ +
      tlNCbP17c1 f ξ + tlNCbP17c2 f ξ + tlNCbP17c3 f ξ + tlNCbP17c4 f ξ + tlNCbP17c5 f ξ +
      tlNCbP17c6 f ξ + tlNCbP17c7 f ξ + tlNCbP17c8 f ξ + tlNCbP17c9 f ξ + tlNCbP17c10 f ξ +
      tlNCbP17c11 f ξ + tlNCbP17c12 f ξ + tlNCbP17c13 f ξ + tlNCbP17c14 f ξ + tlNCbP17c15 f ξ +
      tlNCbP18c0 f ξ + tlNCbP18c1 f ξ + tlNCbP18c2 f ξ + tlNCbP18c3 f ξ + tlNCbP18c4 f ξ +
      tlNCbP18c5 f ξ + tlNCbP18c6 f ξ + tlNCbP18c7 f ξ + tlNCbP18c8 f ξ + tlNCbP18c9 f ξ +
      tlNCbP18c10 f ξ + tlNCbP18c11 f ξ + tlNCbP18c12 f ξ + tlNCbP18c13 f ξ + tlNCbP18c14 f ξ +
      tlNCbP18c15 f ξ + tlNCbP19c0 f ξ + tlNCbP19c1 f ξ + tlNCbP19c2 f ξ + tlNCbP19c3 f ξ +
      tlNCbP19c4 f ξ + tlNCbP19c5 f ξ + tlNCbP19c6 f ξ + tlNCbP19c7 f ξ + tlNCbP19c8 f ξ +
      tlNCbP19c9 f ξ + tlNCbP19c10 f ξ + tlNCbP19c11 f ξ + tlNCbP19c12 f ξ + tlNCbP19c13 f ξ +
      tlNCbP19c14 f ξ + tlNCbP19c15 f ξ + tlNCbP20c0 f ξ + tlNCbP20c1 f ξ + tlNCbP20c2 f ξ +
      tlNCbP20c3 f ξ + tlNCbP20c4 f ξ + tlNCbP20c5 f ξ + tlNCbP20c6 f ξ + tlNCbP20c7 f ξ +
      tlNCbP20c8 f ξ + tlNCbP20c9 f ξ + tlNCbP21c0 f ξ + tlNCbP21c1 f ξ + tlNCbP21c2 f ξ +
      tlNCbP21c3 f ξ + tlNCbP21c4 f ξ + tlNCbP21c5 f ξ + tlNCbP21c6 f ξ + tlNCbP21c7 f ξ +
      tlNCbP21c8 f ξ + tlNCbP21c9 f ξ + tlNCbP21c10 f ξ + tlNCbP22c0 f ξ + tlNCbP22c1 f ξ +
      tlNCbP22c2 f ξ + tlNCbP22c3 f ξ + tlNCbP22c4 f ξ + tlNCbP22c5 f ξ + tlNCbP22c6 f ξ +
      tlNCbP22c7 f ξ + tlNCbP22c8 f ξ + tlNCbP22c9 f ξ + tlNCbP22c10 f ξ + tlNCbP22c11 f ξ +
      tlNCbP22c12 f ξ + tlNCbP23c0 f ξ + tlNCbP23c1 f ξ + tlNCbP23c2 f ξ + tlNCbP23c3 f ξ +
      tlNCbP23c4 f ξ + tlNCbP23c5 f ξ + tlNCbP23c6 f ξ + tlNCbP23c7 f ξ + tlNCbP23c8 f ξ +
      tlNCbP23c9 f ξ + tlNCbP23c10 f ξ + tlNCbP23c11 f ξ + tlNCbP23c12 f ξ + tlNCbP23c13 f ξ +
      tlNCbP24c0 f ξ + tlNCbP24c1 f ξ + tlNCbP24c2 f ξ + tlNCbP24c3 f ξ + tlNCbP24c4 f ξ +
      tlNCbP24c5 f ξ + tlNCbP24c6 f ξ + tlNCbP24c7 f ξ + tlNCbP24c8 f ξ + tlNCbP24c9 f ξ +
      tlNCbP24c10 f ξ + tlNCbP24c11 f ξ + tlNCbP24c12 f ξ + tlNCbP24c13 f ξ + tlNCbP24c14 f ξ +
      tlNCbP24c15 f ξ + tlNCbP25c0 f ξ + tlNCbP25c1 f ξ + tlNCbP25c2 f ξ + tlNCbP25c3 f ξ +
      tlNCbP25c4 f ξ + tlNCbP25c5 f ξ + tlNCbP25c6 f ξ + tlNCbP25c7 f ξ + tlNCbP25c8 f ξ +
      tlNCbP25c9 f ξ + tlNCbP25c10 f ξ + tlNCbP25c11 f ξ + tlNCbP25c12 f ξ + tlNCbP25c13 f ξ +
      tlNCbP25c14 f ξ + tlNCbP25c15 f ξ + tlNCbP26c0 f ξ + tlNCbP26c1 f ξ + tlNCbP26c2 f ξ +
      tlNCbP26c3 f ξ + tlNCbP26c4 f ξ + tlNCbP26c5 f ξ + tlNCbP26c6 f ξ + tlNCbP26c7 f ξ +
      tlNCbP26c8 f ξ + tlNCbP26c9 f ξ + tlNCbP26c10 f ξ + tlNCbP26c11 f ξ + tlNCbP26c12 f ξ +
      tlNCbP26c13 f ξ + tlNCbP26c14 f ξ + tlNCbP26c15 f ξ + tlNCbP27c0 f ξ + tlNCbP27c1 f ξ +
      tlNCbP27c2 f ξ + tlNCbP27c3 f ξ + tlNCbP27c4 f ξ + tlNCbP27c5 f ξ + tlNCbP27c6 f ξ +
      tlNCbP27c7 f ξ + tlNCbP27c8 f ξ + tlNCbP27c9 f ξ + tlNCbP27c10 f ξ + tlNCbP27c11 f ξ +
      tlNCbP27c12 f ξ + tlNCbP27c13 f ξ + tlNCbP27c14 f ξ + tlNCbP27c15 f ξ + tlNCbP27c16 f ξ +
      tlNCbP28c0 f ξ + tlNCbP28c1 f ξ + tlNCbP28c2 f ξ + tlNCbP28c3 f ξ + tlNCbP28c4 f ξ +
      tlNCbP28c5 f ξ + tlNCbP28c6 f ξ + tlNCbP28c7 f ξ + tlNCbP28c8 f ξ + tlNCbP28c9 f ξ +
      tlNCbP28c10 f ξ + tlNCbP28c11 f ξ + tlNCbP28c12 f ξ + tlNCbP28c13 f ξ + tlNCbP28c14 f ξ +
      tlNCbP28c15 f ξ + tlNCbP28c16 f ξ + tlNCbP29c0 f ξ + tlNCbP29c1 f ξ + tlNCbP29c2 f ξ +
      tlNCbP29c3 f ξ + tlNCbP29c4 f ξ + tlNCbP29c5 f ξ + tlNCbP29c6 f ξ + tlNCbP29c7 f ξ +
      tlNCbP29c8 f ξ + tlNCbP29c9 f ξ + tlNCbP29c10 f ξ + tlNCbP29c11 f ξ + tlNCbP29c12 f ξ +
      tlNCbP29c13 f ξ + tlNCbP29c14 f ξ + tlNCbP29c15 f ξ + tlNCbP29c16 f ξ + tlNCbP30c0 f ξ +
      tlNCbP30c1 f ξ + tlNCbP30c2 f ξ + tlNCbP30c3 f ξ + tlNCbP30c4 f ξ + tlNCbP30c5 f ξ +
      tlNCbP30c6 f ξ + tlNCbP30c7 f ξ + tlNCbP30c8 f ξ + tlNCbP30c9 f ξ + tlNCbP30c10 f ξ +
      tlNCbP30c11 f ξ + tlNCbP30c12 f ξ + tlNCbP30c13 f ξ + tlNCbP30c14 f ξ + tlNCbP30c15 f ξ +
      tlNCbP30c16 f ξ + tlNCbP31c0 f ξ + tlNCbP31c1 f ξ + tlNCbP31c2 f ξ + tlNCbP31c3 f ξ +
      tlNCbP31c4 f ξ + tlNCbP31c5 f ξ + tlNCbP31c6 f ξ + tlNCbP31c7 f ξ + tlNCbP31c8 f ξ +
      tlNCbP31c9 f ξ + tlNCbP31c10 f ξ + tlNCbP31c11 f ξ + tlNCbP31c12 f ξ + tlNCbP31c13 f ξ +
      tlNCbP31c14 f ξ + tlNCbP31c15 f ξ + tlNCbP31c16 f ξ + tlNCbP32c0 f ξ + tlNCbP32c1 f ξ +
      tlNCbP32c2 f ξ + tlNCbP32c3 f ξ + tlNCbP32c4 f ξ + tlNCbP32c5 f ξ + tlNCbP32c6 f ξ +
      tlNCbP32c7 f ξ + tlNCbP32c8 f ξ + tlNCbP32c9 f ξ + tlNCbP33c0 f ξ + tlNCbP33c1 f ξ +
      tlNCbP33c2 f ξ + tlNCbP33c3 f ξ + tlNCbP33c4 f ξ + tlNCbP33c5 f ξ + tlNCbP33c6 f ξ +
      tlNCbP33c7 f ξ + tlNCbP33c8 f ξ + tlNCbP33c9 f ξ + tlNCbP33c10 f ξ + tlNCbP34c0 f ξ +
      tlNCbP34c1 f ξ + tlNCbP34c2 f ξ + tlNCbP34c3 f ξ + tlNCbP34c4 f ξ + tlNCbP34c5 f ξ +
      tlNCbP34c6 f ξ + tlNCbP34c7 f ξ + tlNCbP34c8 f ξ + tlNCbP34c9 f ξ + tlNCbP34c10 f ξ +
      tlNCbP34c11 f ξ + tlNCbP34c12 f ξ + tlNCbP35c0 f ξ + tlNCbP35c1 f ξ + tlNCbP35c2 f ξ +
      tlNCbP35c3 f ξ + tlNCbP35c4 f ξ + tlNCbP35c5 f ξ + tlNCbP35c6 f ξ + tlNCbP35c7 f ξ +
      tlNCbP35c8 f ξ + tlNCbP35c9 f ξ + tlNCbP35c10 f ξ + tlNCbP35c11 f ξ + tlNCbP35c12 f ξ +
      tlNCbP35c13 f ξ + tlNCbP36c0 f ξ + tlNCbP36c1 f ξ + tlNCbP36c2 f ξ + tlNCbP36c3 f ξ +
      tlNCbP36c4 f ξ + tlNCbP36c5 f ξ + tlNCbP36c6 f ξ + tlNCbP36c7 f ξ + tlNCbP36c8 f ξ +
      tlNCbP36c9 f ξ + tlNCbP36c10 f ξ + tlNCbP36c11 f ξ + tlNCbP36c12 f ξ + tlNCbP36c13 f ξ +
      tlNCbP36c14 f ξ + tlNCbP36c15 f ξ + tlNCbP37c0 f ξ + tlNCbP37c1 f ξ + tlNCbP37c2 f ξ +
      tlNCbP37c3 f ξ + tlNCbP37c4 f ξ + tlNCbP37c5 f ξ + tlNCbP37c6 f ξ + tlNCbP37c7 f ξ +
      tlNCbP37c8 f ξ + tlNCbP37c9 f ξ + tlNCbP37c10 f ξ + tlNCbP37c11 f ξ + tlNCbP37c12 f ξ +
      tlNCbP37c13 f ξ + tlNCbP37c14 f ξ + tlNCbP37c15 f ξ + tlNCbP37c16 f ξ + tlNCbP38c0 f ξ +
      tlNCbP38c1 f ξ + tlNCbP38c2 f ξ + tlNCbP38c3 f ξ + tlNCbP38c4 f ξ + tlNCbP38c5 f ξ +
      tlNCbP38c6 f ξ + tlNCbP38c7 f ξ + tlNCbP38c8 f ξ + tlNCbP38c9 f ξ + tlNCbP38c10 f ξ +
      tlNCbP38c11 f ξ + tlNCbP38c12 f ξ + tlNCbP38c13 f ξ + tlNCbP38c14 f ξ + tlNCbP38c15 f ξ +
      tlNCbP38c16 f ξ + tlNCbP39c0 f ξ + tlNCbP39c1 f ξ + tlNCbP39c2 f ξ + tlNCbP39c3 f ξ +
      tlNCbP39c4 f ξ + tlNCbP39c5 f ξ + tlNCbP39c6 f ξ + tlNCbP39c7 f ξ + tlNCbP39c8 f ξ +
      tlNCbP39c9 f ξ + tlNCbP39c10 f ξ + tlNCbP39c11 f ξ + tlNCbP39c12 f ξ + tlNCbP39c13 f ξ +
      tlNCbP39c14 f ξ + tlNCbP39c15 f ξ + tlNCbP39c16 f ξ + tlNCbP40c0 f ξ + tlNCbP40c1 f ξ +
      tlNCbP40c2 f ξ + tlNCbP40c3 f ξ + tlNCbP40c4 f ξ + tlNCbP40c5 f ξ + tlNCbP40c6 f ξ +
      tlNCbP40c7 f ξ + tlNCbP40c8 f ξ + tlNCbP40c9 f ξ + tlNCbP40c10 f ξ + tlNCbP40c11 f ξ +
      tlNCbP40c12 f ξ + tlNCbP40c13 f ξ + tlNCbP40c14 f ξ + tlNCbP40c15 f ξ + tlNCbP40c16 f ξ +
      tlNCbP41c0 f ξ + tlNCbP41c1 f ξ + tlNCbP41c2 f ξ + tlNCbP41c3 f ξ + tlNCbP41c4 f ξ +
      tlNCbP41c5 f ξ + tlNCbP41c6 f ξ + tlNCbP41c7 f ξ + tlNCbP41c8 f ξ + tlNCbP41c9 f ξ +
      tlNCbP41c10 f ξ + tlNCbP41c11 f ξ + tlNCbP41c12 f ξ + tlNCbP41c13 f ξ + tlNCbP41c14 f ξ +
      tlNCbP41c15 f ξ + tlNCbP41c16 f ξ + tlNCbP42c0 f ξ + tlNCbP42c1 f ξ + tlNCbP42c2 f ξ +
      tlNCbP42c3 f ξ + tlNCbP42c4 f ξ + tlNCbP42c5 f ξ + tlNCbP42c6 f ξ + tlNCbP42c7 f ξ +
      tlNCbP42c8 f ξ + tlNCbP42c9 f ξ + tlNCbP42c10 f ξ + tlNCbP42c11 f ξ + tlNCbP42c12 f ξ +
      tlNCbP42c13 f ξ + tlNCbP42c14 f ξ + tlNCbP42c15 f ξ + tlNCbP42c16 f ξ + tlNCbP43c0 f ξ +
      tlNCbP43c1 f ξ + tlNCbP43c2 f ξ + tlNCbP43c3 f ξ + tlNCbP43c4 f ξ + tlNCbP43c5 f ξ +
      tlNCbP43c6 f ξ + tlNCbP43c7 f ξ + tlNCbP43c8 f ξ + tlNCbP43c9 f ξ + tlNCbP43c10 f ξ +
      tlNCbP43c11 f ξ + tlNCbP43c12 f ξ + tlNCbP43c13 f ξ + tlNCbP43c14 f ξ + tlNCbP43c15 f ξ +
      tlNCbP43c16 f ξ + tlNCbP44c0 f ξ + tlNCbP44c1 f ξ + tlNCbP44c2 f ξ + tlNCbP44c3 f ξ +
      tlNCbP44c4 f ξ + tlNCbP44c5 f ξ + tlNCbP44c6 f ξ + tlNCbP44c7 f ξ + tlNCbP44c8 f ξ +
      tlNCbP44c9 f ξ + tlNCbP44c10 f ξ + tlNCbP44c11 f ξ + tlNCbP44c12 f ξ + tlNCbP44c13 f ξ +
      tlNCbP44c14 f ξ + tlNCbP44c15 f ξ + tlNCbP45c0 f ξ + tlNCbP45c1 f ξ + tlNCbP45c2 f ξ +
      tlNCbP45c3 f ξ + tlNCbP45c4 f ξ + tlNCbP45c5 f ξ + tlNCbP45c6 f ξ + tlNCbP45c7 f ξ +
      tlNCbP45c8 f ξ + tlNCbP45c9 f ξ + tlNCbP45c10 f ξ + tlNCbP45c11 f ξ + tlNCbP45c12 f ξ +
      tlNCbP45c13 f ξ + tlNCbP45c14 f ξ + tlNCbP45c15 f ξ + tlWTwoXP0c0 f ξ + tlWTwoXP0c1 f ξ +
      tlWTwoXP0c2 f ξ + tlWTwoXP0c3 f ξ + tlWTwoXP0c4 f ξ + tlWTwoXP0c5 f ξ + tlWTwoXP0c6 f ξ +
      tlWTwoXP0c7 f ξ + tlWTwoXP0c8 f ξ + tlWTwoXP0c9 f ξ + tlWTwoXP0c10 f ξ + tlWTwoXP0c11 f ξ +
      tlWTwoXP0c12 f ξ + tlWTwoXP0c13 f ξ + tlWTwoXP0c14 f ξ + tlWTwoXP0c15 f ξ + tlWTwoXP0c16 f ξ
      + tlWTwoXP0c17 f ξ + tlWTwoXP0c18 f ξ + tlWTwoXP0c19 f ξ + tlWTwoXP1c0 f ξ + tlWTwoXP1c1 f ξ
      + tlWTwoXP1c2 f ξ + tlWTwoXP1c3 f ξ + tlWTwoXP1c4 f ξ + tlWTwoXP1c5 f ξ + tlWTwoXP1c6 f ξ +
      tlWTwoXP1c7 f ξ + tlWTwoXP1c8 f ξ + tlWTwoXP1c9 f ξ + tlWTwoXP1c10 f ξ + tlWTwoXP1c11 f ξ +
      tlWTwoXP1c12 f ξ + tlWTwoXP1c13 f ξ + tlWTwoXP1c14 f ξ + tlWTwoXP1c15 f ξ + tlWTwoXP1c16 f ξ
      + tlWTwoXP1c17 f ξ + tlWTwoXP1c18 f ξ + tlWTwoXP1c19 f ξ + tlWTwoXP1c20 f ξ + tlWTwoXP1c21 f
      ξ + tlWTwoXP1c22 f ξ + tlWTwoXP2c0 f ξ + tlWTwoXP2c1 f ξ + tlWTwoXP2c2 f ξ + tlWTwoXP2c3 f ξ
      + tlWTwoXP2c4 f ξ + tlWTwoXP2c5 f ξ + tlWTwoXP2c6 f ξ + tlWTwoXP2c7 f ξ + tlWTwoXP2c8 f ξ +
      tlWTwoXP2c9 f ξ + tlWTwoXP2c10 f ξ + tlWTwoXP2c11 f ξ + tlWTwoXP2c12 f ξ + tlWTwoXP2c13 f ξ
      + tlWTwoXP2c14 f ξ + tlWTwoXP2c15 f ξ + tlWTwoXP2c16 f ξ + tlWTwoXP2c17 f ξ + tlWTwoXP2c18 f
      ξ + tlWTwoXP2c19 f ξ + tlWTwoXP2c20 f ξ + tlWTwoXP2c21 f ξ + tlWTwoXP2c22 f ξ + tlWTwoXP2c23
      f ξ + tlWTwoXP3c0 f ξ + tlWTwoXP3c1 f ξ + tlWTwoXP3c2 f ξ + tlWTwoXP3c3 f ξ + tlWTwoXP3c4 f
      ξ + tlWTwoXP3c5 f ξ + tlWTwoXP3c6 f ξ + tlWTwoXP3c7 f ξ + tlWTwoXP3c8 f ξ + tlWTwoXP3c9 f ξ
      + tlWTwoXP3c10 f ξ + tlWTwoXP3c11 f ξ + tlWTwoXP3c12 f ξ + tlWTwoXP3c13 f ξ + tlWTwoXP3c14 f
      ξ + tlWTwoXP3c15 f ξ + tlWTwoXP3c16 f ξ + tlWTwoXP3c17 f ξ + tlWTwoXP3c18 f ξ + tlWTwoXP3c19
      f ξ + tlWTwoXP3c20 f ξ + tlWTwoXP3c21 f ξ + tlWTwoXP3c22 f ξ + tlWTwoXP3c23 f ξ +
      tlWTwoXP3c24 f ξ + tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ + tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ +
      tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ + tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ + tlWOneXP0c8 f ξ +
      tlWOneXP0c9 f ξ + tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ + tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ
      + tlWOneXP1c0 f ξ + tlWOneXP1c1 f ξ + tlWOneXP1c2 f ξ + tlWOneXP1c3 f ξ + tlWOneXP1c4 f ξ +
      tlWOneXP1c5 f ξ + tlWOneXP1c6 f ξ + tlWOneXP1c7 f ξ + tlWOneXP1c8 f ξ + tlWOneXP1c9 f ξ +
      tlWOneXP1c10 f ξ + tlWOneXP1c11 f ξ + tlWOneXP1c12 f ξ + tlWOneXP1c13 f ξ + tlWOneXP1c14 f ξ
      + tlWOneXP1c15 f ξ + tlWOneXP1c16 f ξ + tlWOneXP1c17 f ξ + tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ
      + tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ + tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ + tlWOneXP2c6 f ξ +
      tlWOneXP2c7 f ξ + tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ + tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ +
      tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ + tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ + tlWOneXP2c16 f ξ
      + tlWOneXP2c17 f ξ + tlWOneXP2c18 f ξ + tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ + tlWOneXP3c2 f ξ
      + tlWOneXP3c3 f ξ + tlWOneXP3c4 f ξ + tlWOneXP3c5 f ξ + tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ +
      tlWOneXP3c8 f ξ + tlWOneXP3c9 f ξ + tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ + tlWOneXP3c12 f ξ +
      tlWOneXP3c13 f ξ + tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ + tlWOneXP3c16 f ξ + tlWOneXP3c17 f ξ
      + tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ + tlWOneXP4c0 f ξ + tlWOneXP4c1 f ξ + tlWOneXP4c2 f ξ
      + tlWOneXP4c3 f ξ + tlWOneXP4c4 f ξ + tlWOneXP4c5 f ξ + tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ +
      tlWOneXP4c8 f ξ + tlWOneXP4c9 f ξ + tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ + tlWOneXP4c12 f ξ +
      tlWOneXP4c13 f ξ + tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ + tlWOneXP4c16 f ξ + tlWOneXP4c17 f ξ
      + tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ + tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ + tlWOneXP5c2 f ξ
      + tlWOneXP5c3 f ξ + tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ + tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ +
      tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ + tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ + tlWOneXP5c12 f ξ +
      tlWOneXP5c13 f ξ + tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ + tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ
      + tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ + tlWOneXP6c0 f ξ + tlWOneXP6c1 f ξ + tlWOneXP6c2 f ξ
      + tlWOneXP6c3 f ξ + tlWOneXP6c4 f ξ + tlWOneXP6c5 f ξ + tlWOneXP6c6 f ξ + tlWOneXP6c7 f ξ +
      tlWOneXP6c8 f ξ + tlWOneXP6c9 f ξ + tlWOneXP6c10 f ξ + tlWOneXP6c11 f ξ + tlWZeroXP0c0 f ξ +
      tlWZeroXP0c1 f ξ + tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ + tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ
      + tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ + tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ + tlWZeroXP0c10
      f ξ + tlWZeroXP0c11 f ξ + tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ + tlWZeroXP0c14 f ξ +
      tlWZeroXP0c15 f ξ + tlWZeroXP0c16 f ξ + tlWZeroXP0c17 f ξ + tlWZeroXP1c0 f ξ + tlWZeroXP1c1
      f ξ + tlWZeroXP1c2 f ξ + tlWZeroXP1c3 f ξ + tlWZeroXP1c4 f ξ + tlWZeroXP1c5 f ξ +
      tlWZeroXP1c6 f ξ + tlWZeroXP1c7 f ξ + tlWZeroXP1c8 f ξ + tlWZeroXP1c9 f ξ + tlWZeroXP1c10 f
      ξ + tlWZeroXP1c11 f ξ + tlWZeroXP1c12 f ξ + tlWZeroXP1c13 f ξ + tlWZeroXP1c14 f ξ +
      tlWZeroXP1c15 f ξ + tlWZeroXP1c16 f ξ + tlWZeroXP1c17 f ξ + tlWZeroXP1c18 f ξ +
      tlWZeroXP1c19 f ξ + tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ + tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f
      ξ + tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ + tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ + tlWZeroXP2c8
      f ξ + tlWZeroXP2c9 f ξ + tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ + tlWZeroXP2c12 f ξ +
      tlWZeroXP2c13 f ξ + tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f ξ + tlWZeroXP2c16 f ξ +
      tlWZeroXP2c17 f ξ + tlWZeroXP2c18 f ξ + tlWZeroXP2c19 f ξ + tlWZeroXP2c20 f ξ = 0 := by
  simp only [tlNCbP0c0, tlNCbP0c1, tlNCbP0c2, tlNCbP0c3, tlNCbP0c4, tlNCbP0c5, tlNCbP0c6,
      tlNCbP0c7, tlNCbP0c8, tlNCbP0c9, tlNCbP1c0, tlNCbP1c1, tlNCbP1c2, tlNCbP1c3,
      tlNCbP1c4, tlNCbP1c5, tlNCbP1c6, tlNCbP1c7, tlNCbP1c8, tlNCbP1c9, tlNCbP1c10,
      tlNCbP2c0, tlNCbP2c1, tlNCbP2c2, tlNCbP2c3, tlNCbP2c4, tlNCbP2c5, tlNCbP2c6,
      tlNCbP2c7, tlNCbP2c8, tlNCbP2c9, tlNCbP2c10, tlNCbP2c11, tlNCbP2c12,
      tlNCbP3c0, tlNCbP3c1, tlNCbP3c2, tlNCbP3c3, tlNCbP3c4, tlNCbP3c5, tlNCbP3c6,
      tlNCbP3c7, tlNCbP3c8, tlNCbP3c9, tlNCbP3c10, tlNCbP3c11, tlNCbP3c12,
      tlNCbP3c13, tlNCbP4c0, tlNCbP4c1, tlNCbP4c2, tlNCbP4c3, tlNCbP4c4, tlNCbP4c5,
      tlNCbP4c6, tlNCbP4c7, tlNCbP4c8, tlNCbP4c9, tlNCbP4c10, tlNCbP4c11,
      tlNCbP4c12, tlNCbP4c13, tlNCbP4c14, tlNCbP5c0, tlNCbP5c1, tlNCbP5c2,
      tlNCbP5c3, tlNCbP5c4, tlNCbP5c5, tlNCbP5c6, tlNCbP5c7, tlNCbP5c8, tlNCbP5c9,
      tlNCbP5c10, tlNCbP5c11, tlNCbP5c12, tlNCbP5c13, tlNCbP5c14, tlNCbP6c0,
      tlNCbP6c1, tlNCbP6c2, tlNCbP6c3, tlNCbP6c4, tlNCbP6c5, tlNCbP6c6, tlNCbP6c7,
      tlNCbP6c8, tlNCbP6c9, tlNCbP6c10, tlNCbP6c11, tlNCbP6c12, tlNCbP6c13,
      tlNCbP6c14, tlNCbP7c0, tlNCbP7c1, tlNCbP7c2, tlNCbP7c3, tlNCbP7c4, tlNCbP7c5,
      tlNCbP7c6, tlNCbP7c7, tlNCbP7c8, tlNCbP7c9, tlNCbP7c10, tlNCbP7c11,
      tlNCbP7c12, tlNCbP7c13, tlNCbP7c14, tlNCbP8c0, tlNCbP8c1, tlNCbP8c2,
      tlNCbP8c3, tlNCbP8c4, tlNCbP8c5, tlNCbP8c6, tlNCbP8c7, tlNCbP8c8, tlNCbP8c9,
      tlNCbP8c10, tlNCbP8c11, tlNCbP8c12, tlNCbP8c13, tlNCbP8c14, tlNCbP8c15,
      tlNCbP9c0, tlNCbP9c1, tlNCbP9c2, tlNCbP9c3, tlNCbP9c4, tlNCbP9c5, tlNCbP9c6,
      tlNCbP9c7, tlNCbP9c8, tlNCbP9c9, tlNCbP10c0, tlNCbP10c1, tlNCbP10c2,
      tlNCbP10c3, tlNCbP10c4, tlNCbP10c5, tlNCbP10c6, tlNCbP10c7, tlNCbP10c8,
      tlNCbP10c9, tlNCbP10c10, tlNCbP11c0, tlNCbP11c1, tlNCbP11c2, tlNCbP11c3,
      tlNCbP11c4, tlNCbP11c5, tlNCbP11c6, tlNCbP11c7, tlNCbP11c8, tlNCbP11c9,
      tlNCbP11c10, tlNCbP11c11, tlNCbP11c12, tlNCbP12c0, tlNCbP12c1, tlNCbP12c2,
      tlNCbP12c3, tlNCbP12c4, tlNCbP12c5, tlNCbP12c6, tlNCbP12c7, tlNCbP12c8,
      tlNCbP12c9, tlNCbP12c10, tlNCbP12c11, tlNCbP12c12, tlNCbP12c13, tlNCbP13c0,
      tlNCbP13c1, tlNCbP13c2, tlNCbP13c3, tlNCbP13c4, tlNCbP13c5, tlNCbP13c6,
      tlNCbP13c7, tlNCbP13c8, tlNCbP13c9, tlNCbP13c10, tlNCbP13c11, tlNCbP13c12,
      tlNCbP13c13, tlNCbP13c14, tlNCbP14c0, tlNCbP14c1, tlNCbP14c2, tlNCbP14c3,
      tlNCbP14c4, tlNCbP14c5, tlNCbP14c6, tlNCbP14c7, tlNCbP14c8, tlNCbP14c9,
      tlNCbP14c10, tlNCbP14c11, tlNCbP14c12, tlNCbP14c13, tlNCbP14c14, tlNCbP14c15,
      tlNCbP15c0, tlNCbP15c1, tlNCbP15c2, tlNCbP15c3, tlNCbP15c4, tlNCbP15c5,
      tlNCbP15c6, tlNCbP15c7, tlNCbP15c8, tlNCbP15c9, tlNCbP15c10, tlNCbP15c11,
      tlNCbP15c12, tlNCbP15c13, tlNCbP15c14, tlNCbP15c15, tlNCbP16c0, tlNCbP16c1,
      tlNCbP16c2, tlNCbP16c3, tlNCbP16c4, tlNCbP16c5, tlNCbP16c6, tlNCbP16c7,
      tlNCbP16c8, tlNCbP16c9, tlNCbP16c10, tlNCbP16c11, tlNCbP16c12, tlNCbP16c13,
      tlNCbP16c14, tlNCbP16c15, tlNCbP17c0, tlNCbP17c1, tlNCbP17c2, tlNCbP17c3,
      tlNCbP17c4, tlNCbP17c5, tlNCbP17c6, tlNCbP17c7, tlNCbP17c8, tlNCbP17c9,
      tlNCbP17c10, tlNCbP17c11, tlNCbP17c12, tlNCbP17c13, tlNCbP17c14, tlNCbP17c15,
      tlNCbP18c0, tlNCbP18c1, tlNCbP18c2, tlNCbP18c3, tlNCbP18c4, tlNCbP18c5,
      tlNCbP18c6, tlNCbP18c7, tlNCbP18c8, tlNCbP18c9, tlNCbP18c10, tlNCbP18c11,
      tlNCbP18c12, tlNCbP18c13, tlNCbP18c14, tlNCbP18c15, tlNCbP19c0, tlNCbP19c1,
      tlNCbP19c2, tlNCbP19c3, tlNCbP19c4, tlNCbP19c5, tlNCbP19c6, tlNCbP19c7,
      tlNCbP19c8, tlNCbP19c9, tlNCbP19c10, tlNCbP19c11, tlNCbP19c12, tlNCbP19c13,
      tlNCbP19c14, tlNCbP19c15, tlNCbP20c0, tlNCbP20c1, tlNCbP20c2, tlNCbP20c3,
      tlNCbP20c4, tlNCbP20c5, tlNCbP20c6, tlNCbP20c7, tlNCbP20c8, tlNCbP20c9,
      tlNCbP21c0, tlNCbP21c1, tlNCbP21c2, tlNCbP21c3, tlNCbP21c4, tlNCbP21c5,
      tlNCbP21c6, tlNCbP21c7, tlNCbP21c8, tlNCbP21c9, tlNCbP21c10, tlNCbP22c0,
      tlNCbP22c1, tlNCbP22c2, tlNCbP22c3, tlNCbP22c4, tlNCbP22c5, tlNCbP22c6,
      tlNCbP22c7, tlNCbP22c8, tlNCbP22c9, tlNCbP22c10, tlNCbP22c11, tlNCbP22c12,
      tlNCbP23c0, tlNCbP23c1, tlNCbP23c2, tlNCbP23c3, tlNCbP23c4, tlNCbP23c5,
      tlNCbP23c6, tlNCbP23c7, tlNCbP23c8, tlNCbP23c9, tlNCbP23c10, tlNCbP23c11,
      tlNCbP23c12, tlNCbP23c13, tlNCbP24c0, tlNCbP24c1, tlNCbP24c2, tlNCbP24c3,
      tlNCbP24c4, tlNCbP24c5, tlNCbP24c6, tlNCbP24c7, tlNCbP24c8, tlNCbP24c9,
      tlNCbP24c10, tlNCbP24c11, tlNCbP24c12, tlNCbP24c13, tlNCbP24c14, tlNCbP24c15,
      tlNCbP25c0, tlNCbP25c1, tlNCbP25c2, tlNCbP25c3, tlNCbP25c4, tlNCbP25c5,
      tlNCbP25c6, tlNCbP25c7, tlNCbP25c8, tlNCbP25c9, tlNCbP25c10, tlNCbP25c11,
      tlNCbP25c12, tlNCbP25c13, tlNCbP25c14, tlNCbP25c15, tlNCbP26c0, tlNCbP26c1,
      tlNCbP26c2, tlNCbP26c3, tlNCbP26c4, tlNCbP26c5, tlNCbP26c6, tlNCbP26c7,
      tlNCbP26c8, tlNCbP26c9, tlNCbP26c10, tlNCbP26c11, tlNCbP26c12, tlNCbP26c13,
      tlNCbP26c14, tlNCbP26c15, tlNCbP27c0, tlNCbP27c1, tlNCbP27c2, tlNCbP27c3,
      tlNCbP27c4, tlNCbP27c5, tlNCbP27c6, tlNCbP27c7, tlNCbP27c8, tlNCbP27c9,
      tlNCbP27c10, tlNCbP27c11, tlNCbP27c12, tlNCbP27c13, tlNCbP27c14, tlNCbP27c15,
      tlNCbP27c16, tlNCbP28c0, tlNCbP28c1, tlNCbP28c2, tlNCbP28c3, tlNCbP28c4,
      tlNCbP28c5, tlNCbP28c6, tlNCbP28c7, tlNCbP28c8, tlNCbP28c9, tlNCbP28c10,
      tlNCbP28c11, tlNCbP28c12, tlNCbP28c13, tlNCbP28c14, tlNCbP28c15, tlNCbP28c16,
      tlNCbP29c0, tlNCbP29c1, tlNCbP29c2, tlNCbP29c3, tlNCbP29c4, tlNCbP29c5,
      tlNCbP29c6, tlNCbP29c7, tlNCbP29c8, tlNCbP29c9, tlNCbP29c10, tlNCbP29c11,
      tlNCbP29c12, tlNCbP29c13, tlNCbP29c14, tlNCbP29c15, tlNCbP29c16, tlNCbP30c0,
      tlNCbP30c1, tlNCbP30c2, tlNCbP30c3, tlNCbP30c4, tlNCbP30c5, tlNCbP30c6,
      tlNCbP30c7, tlNCbP30c8, tlNCbP30c9, tlNCbP30c10, tlNCbP30c11, tlNCbP30c12,
      tlNCbP30c13, tlNCbP30c14, tlNCbP30c15, tlNCbP30c16, tlNCbP31c0, tlNCbP31c1,
      tlNCbP31c2, tlNCbP31c3, tlNCbP31c4, tlNCbP31c5, tlNCbP31c6, tlNCbP31c7,
      tlNCbP31c8, tlNCbP31c9, tlNCbP31c10, tlNCbP31c11, tlNCbP31c12, tlNCbP31c13,
      tlNCbP31c14, tlNCbP31c15, tlNCbP31c16, tlNCbP32c0, tlNCbP32c1, tlNCbP32c2,
      tlNCbP32c3, tlNCbP32c4, tlNCbP32c5, tlNCbP32c6, tlNCbP32c7, tlNCbP32c8,
      tlNCbP32c9, tlNCbP33c0, tlNCbP33c1, tlNCbP33c2, tlNCbP33c3, tlNCbP33c4,
      tlNCbP33c5, tlNCbP33c6, tlNCbP33c7, tlNCbP33c8, tlNCbP33c9, tlNCbP33c10,
      tlNCbP34c0, tlNCbP34c1, tlNCbP34c2, tlNCbP34c3, tlNCbP34c4, tlNCbP34c5,
      tlNCbP34c6, tlNCbP34c7, tlNCbP34c8, tlNCbP34c9, tlNCbP34c10, tlNCbP34c11,
      tlNCbP34c12, tlNCbP35c0, tlNCbP35c1, tlNCbP35c2, tlNCbP35c3, tlNCbP35c4,
      tlNCbP35c5, tlNCbP35c6, tlNCbP35c7, tlNCbP35c8, tlNCbP35c9, tlNCbP35c10,
      tlNCbP35c11, tlNCbP35c12, tlNCbP35c13, tlNCbP36c0, tlNCbP36c1, tlNCbP36c2,
      tlNCbP36c3, tlNCbP36c4, tlNCbP36c5, tlNCbP36c6, tlNCbP36c7, tlNCbP36c8,
      tlNCbP36c9, tlNCbP36c10, tlNCbP36c11, tlNCbP36c12, tlNCbP36c13, tlNCbP36c14,
      tlNCbP36c15, tlNCbP37c0, tlNCbP37c1, tlNCbP37c2, tlNCbP37c3, tlNCbP37c4,
      tlNCbP37c5, tlNCbP37c6, tlNCbP37c7, tlNCbP37c8, tlNCbP37c9, tlNCbP37c10,
      tlNCbP37c11, tlNCbP37c12, tlNCbP37c13, tlNCbP37c14, tlNCbP37c15, tlNCbP37c16,
      tlNCbP38c0, tlNCbP38c1, tlNCbP38c2, tlNCbP38c3, tlNCbP38c4, tlNCbP38c5,
      tlNCbP38c6, tlNCbP38c7, tlNCbP38c8, tlNCbP38c9, tlNCbP38c10, tlNCbP38c11,
      tlNCbP38c12, tlNCbP38c13, tlNCbP38c14, tlNCbP38c15, tlNCbP38c16, tlNCbP39c0,
      tlNCbP39c1, tlNCbP39c2, tlNCbP39c3, tlNCbP39c4, tlNCbP39c5, tlNCbP39c6,
      tlNCbP39c7, tlNCbP39c8, tlNCbP39c9, tlNCbP39c10, tlNCbP39c11, tlNCbP39c12,
      tlNCbP39c13, tlNCbP39c14, tlNCbP39c15, tlNCbP39c16, tlNCbP40c0, tlNCbP40c1,
      tlNCbP40c2, tlNCbP40c3, tlNCbP40c4, tlNCbP40c5, tlNCbP40c6, tlNCbP40c7,
      tlNCbP40c8, tlNCbP40c9, tlNCbP40c10, tlNCbP40c11, tlNCbP40c12, tlNCbP40c13,
      tlNCbP40c14, tlNCbP40c15, tlNCbP40c16, tlNCbP41c0, tlNCbP41c1, tlNCbP41c2,
      tlNCbP41c3, tlNCbP41c4, tlNCbP41c5, tlNCbP41c6, tlNCbP41c7, tlNCbP41c8,
      tlNCbP41c9, tlNCbP41c10, tlNCbP41c11, tlNCbP41c12, tlNCbP41c13, tlNCbP41c14,
      tlNCbP41c15, tlNCbP41c16, tlNCbP42c0, tlNCbP42c1, tlNCbP42c2, tlNCbP42c3,
      tlNCbP42c4, tlNCbP42c5, tlNCbP42c6, tlNCbP42c7, tlNCbP42c8, tlNCbP42c9,
      tlNCbP42c10, tlNCbP42c11, tlNCbP42c12, tlNCbP42c13, tlNCbP42c14, tlNCbP42c15,
      tlNCbP42c16, tlNCbP43c0, tlNCbP43c1, tlNCbP43c2, tlNCbP43c3, tlNCbP43c4,
      tlNCbP43c5, tlNCbP43c6, tlNCbP43c7, tlNCbP43c8, tlNCbP43c9, tlNCbP43c10,
      tlNCbP43c11, tlNCbP43c12, tlNCbP43c13, tlNCbP43c14, tlNCbP43c15, tlNCbP43c16,
      tlNCbP44c0, tlNCbP44c1, tlNCbP44c2, tlNCbP44c3, tlNCbP44c4, tlNCbP44c5,
      tlNCbP44c6, tlNCbP44c7, tlNCbP44c8, tlNCbP44c9, tlNCbP44c10, tlNCbP44c11,
      tlNCbP44c12, tlNCbP44c13, tlNCbP44c14, tlNCbP44c15, tlNCbP45c0, tlNCbP45c1,
      tlNCbP45c2, tlNCbP45c3, tlNCbP45c4, tlNCbP45c5, tlNCbP45c6, tlNCbP45c7,
      tlNCbP45c8, tlNCbP45c9, tlNCbP45c10, tlNCbP45c11, tlNCbP45c12, tlNCbP45c13,
      tlNCbP45c14, tlNCbP45c15, tlWTwoXP0c0, tlWTwoXP0c1, tlWTwoXP0c2, tlWTwoXP0c3,
      tlWTwoXP0c4, tlWTwoXP0c5, tlWTwoXP0c6, tlWTwoXP0c7, tlWTwoXP0c8, tlWTwoXP0c9,
      tlWTwoXP0c10, tlWTwoXP0c11, tlWTwoXP0c12, tlWTwoXP0c13, tlWTwoXP0c14,
      tlWTwoXP0c15, tlWTwoXP0c16, tlWTwoXP0c17, tlWTwoXP0c18, tlWTwoXP0c19,
      tlWTwoXP1c0, tlWTwoXP1c1, tlWTwoXP1c2, tlWTwoXP1c3, tlWTwoXP1c4, tlWTwoXP1c5,
      tlWTwoXP1c6, tlWTwoXP1c7, tlWTwoXP1c8, tlWTwoXP1c9, tlWTwoXP1c10,
      tlWTwoXP1c11, tlWTwoXP1c12, tlWTwoXP1c13, tlWTwoXP1c14, tlWTwoXP1c15,
      tlWTwoXP1c16, tlWTwoXP1c17, tlWTwoXP1c18, tlWTwoXP1c19, tlWTwoXP1c20,
      tlWTwoXP1c21, tlWTwoXP1c22, tlWTwoXP2c0, tlWTwoXP2c1, tlWTwoXP2c2,
      tlWTwoXP2c3, tlWTwoXP2c4, tlWTwoXP2c5, tlWTwoXP2c6, tlWTwoXP2c7, tlWTwoXP2c8,
      tlWTwoXP2c9, tlWTwoXP2c10, tlWTwoXP2c11, tlWTwoXP2c12, tlWTwoXP2c13,
      tlWTwoXP2c14, tlWTwoXP2c15, tlWTwoXP2c16, tlWTwoXP2c17, tlWTwoXP2c18,
      tlWTwoXP2c19, tlWTwoXP2c20, tlWTwoXP2c21, tlWTwoXP2c22, tlWTwoXP2c23,
      tlWTwoXP3c0, tlWTwoXP3c1, tlWTwoXP3c2, tlWTwoXP3c3, tlWTwoXP3c4, tlWTwoXP3c5,
      tlWTwoXP3c6, tlWTwoXP3c7, tlWTwoXP3c8, tlWTwoXP3c9, tlWTwoXP3c10,
      tlWTwoXP3c11, tlWTwoXP3c12, tlWTwoXP3c13, tlWTwoXP3c14, tlWTwoXP3c15,
      tlWTwoXP3c16, tlWTwoXP3c17, tlWTwoXP3c18, tlWTwoXP3c19, tlWTwoXP3c20,
      tlWTwoXP3c21, tlWTwoXP3c22, tlWTwoXP3c23, tlWTwoXP3c24, tlWOneXP0c0,
      tlWOneXP0c1, tlWOneXP0c2, tlWOneXP0c3, tlWOneXP0c4, tlWOneXP0c5, tlWOneXP0c6,
      tlWOneXP0c7, tlWOneXP0c8, tlWOneXP0c9, tlWOneXP0c10, tlWOneXP0c11,
      tlWOneXP0c12, tlWOneXP0c13, tlWOneXP1c0, tlWOneXP1c1, tlWOneXP1c2,
      tlWOneXP1c3, tlWOneXP1c4, tlWOneXP1c5, tlWOneXP1c6, tlWOneXP1c7, tlWOneXP1c8,
      tlWOneXP1c9, tlWOneXP1c10, tlWOneXP1c11, tlWOneXP1c12, tlWOneXP1c13,
      tlWOneXP1c14, tlWOneXP1c15, tlWOneXP1c16, tlWOneXP1c17, tlWOneXP2c0,
      tlWOneXP2c1, tlWOneXP2c2, tlWOneXP2c3, tlWOneXP2c4, tlWOneXP2c5, tlWOneXP2c6,
      tlWOneXP2c7, tlWOneXP2c8, tlWOneXP2c9, tlWOneXP2c10, tlWOneXP2c11,
      tlWOneXP2c12, tlWOneXP2c13, tlWOneXP2c14, tlWOneXP2c15, tlWOneXP2c16,
      tlWOneXP2c17, tlWOneXP2c18, tlWOneXP3c0, tlWOneXP3c1, tlWOneXP3c2,
      tlWOneXP3c3, tlWOneXP3c4, tlWOneXP3c5, tlWOneXP3c6, tlWOneXP3c7, tlWOneXP3c8,
      tlWOneXP3c9, tlWOneXP3c10, tlWOneXP3c11, tlWOneXP3c12, tlWOneXP3c13,
      tlWOneXP3c14, tlWOneXP3c15, tlWOneXP3c16, tlWOneXP3c17, tlWOneXP3c18,
      tlWOneXP3c19, tlWOneXP4c0, tlWOneXP4c1, tlWOneXP4c2, tlWOneXP4c3, tlWOneXP4c4,
      tlWOneXP4c5, tlWOneXP4c6, tlWOneXP4c7, tlWOneXP4c8, tlWOneXP4c9, tlWOneXP4c10,
      tlWOneXP4c11, tlWOneXP4c12, tlWOneXP4c13, tlWOneXP4c14, tlWOneXP4c15,
      tlWOneXP4c16, tlWOneXP4c17, tlWOneXP4c18, tlWOneXP4c19, tlWOneXP5c0,
      tlWOneXP5c1, tlWOneXP5c2, tlWOneXP5c3, tlWOneXP5c4, tlWOneXP5c5, tlWOneXP5c6,
      tlWOneXP5c7, tlWOneXP5c8, tlWOneXP5c9, tlWOneXP5c10, tlWOneXP5c11,
      tlWOneXP5c12, tlWOneXP5c13, tlWOneXP5c14, tlWOneXP5c15, tlWOneXP5c16,
      tlWOneXP5c17, tlWOneXP5c18, tlWOneXP5c19, tlWOneXP6c0, tlWOneXP6c1,
      tlWOneXP6c2, tlWOneXP6c3, tlWOneXP6c4, tlWOneXP6c5, tlWOneXP6c6, tlWOneXP6c7,
      tlWOneXP6c8, tlWOneXP6c9, tlWOneXP6c10, tlWOneXP6c11, tlWZeroXP0c0,
      tlWZeroXP0c1, tlWZeroXP0c2, tlWZeroXP0c3, tlWZeroXP0c4, tlWZeroXP0c5,
      tlWZeroXP0c6, tlWZeroXP0c7, tlWZeroXP0c8, tlWZeroXP0c9, tlWZeroXP0c10,
      tlWZeroXP0c11, tlWZeroXP0c12, tlWZeroXP0c13, tlWZeroXP0c14, tlWZeroXP0c15,
      tlWZeroXP0c16, tlWZeroXP0c17, tlWZeroXP1c0, tlWZeroXP1c1, tlWZeroXP1c2,
      tlWZeroXP1c3, tlWZeroXP1c4, tlWZeroXP1c5, tlWZeroXP1c6, tlWZeroXP1c7,
      tlWZeroXP1c8, tlWZeroXP1c9, tlWZeroXP1c10, tlWZeroXP1c11, tlWZeroXP1c12,
      tlWZeroXP1c13, tlWZeroXP1c14, tlWZeroXP1c15, tlWZeroXP1c16, tlWZeroXP1c17,
      tlWZeroXP1c18, tlWZeroXP1c19, tlWZeroXP2c0, tlWZeroXP2c1, tlWZeroXP2c2,
      tlWZeroXP2c3, tlWZeroXP2c4, tlWZeroXP2c5, tlWZeroXP2c6, tlWZeroXP2c7,
      tlWZeroXP2c8, tlWZeroXP2c9, tlWZeroXP2c10, tlWZeroXP2c11, tlWZeroXP2c12,
      tlWZeroXP2c13, tlWZeroXP2c14, tlWZeroXP2c15, tlWZeroXP2c16, tlWZeroXP2c17,
      tlWZeroXP2c18, tlWZeroXP2c19, tlWZeroXP2c20]
  ring1

lemma tl_mnum {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) ^ 3 + -(3 * f * (f - 1) ^ 2 * (f ^ 2 +
      f - 1)) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) ^ 2 * (tlD0 f ξ + tlD1 f ξ)
      + -(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^
      4 - 145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) * (tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ +
      tlN4 f ξ) * (tlD0 f ξ + tlD1 f ξ) ^ 2 + -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13
      + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 * f ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7
      + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 * f ^ 4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) *
      (tlD0 f ξ + tlD1 f ξ) ^ 3 = 0 := by
  linear_combination
    ((tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) + -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f -
      1)) * (tlD0 f ξ + tlD1 f ξ)) * tlNSq_val hT + tlNCb_val hT + -(3 * f * (f - 1) ^ 2 * (f ^ 2
      + f - 1)) * tlTTwo_val hT + (-(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^
      6 - 168 * f ^ 5 + 187 * f ^ 4 - 145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) * (tlN0 f ξ + tlN1 f
      ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) + -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 +
      768 * f ^ 12 - 2105 * f ^ 11 + 4341 * f ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 +
      7985 * f ^ 6 - 5312 * f ^ 5 + 2713 * f ^ 4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) *
      (tlD0 f ξ + tlD1 f ξ)) * tlDSq_val hT + -(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7
      + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4 - 145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) *
      tlTOne_val hT + -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 *
      f ^ 11 + 4341 * f ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 *
      f ^ 5 + 2713 * f ^ 4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) * tlDCb_val hT +
      tlWTwoX_val hT + tlWOneX_val hT + tlWZeroX_val hT - (tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ +
      tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ + tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ + tlTTwoP0c6 f ξ +
      tlTTwoP0c7 f ξ + tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ + tlTTwoP0c10 f ξ + tlTTwoP0c11 f ξ +
      tlTTwoP0c12 f ξ + tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ + tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ +
      tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ + tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ + tlTTwoP1c8 f ξ +
      tlTTwoP1c9 f ξ + tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ + tlTTwoP1c12 f ξ + tlTTwoP1c13 f ξ +
      tlTTwoP1c14 f ξ + tlTTwoP1c15 f ξ + tlTTwoP1c16 f ξ + tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ +
      tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ + tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ + tlTTwoP2c6 f ξ +
      tlTTwoP2c7 f ξ + tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ + tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ +
      tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ + tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ + tlTTwoP2c16 f ξ +
      tlTTwoP2c17 f ξ + tlTTwoP2c18 f ξ + tlTTwoP3c0 f ξ + tlTTwoP3c1 f ξ + tlTTwoP3c2 f ξ +
      tlTTwoP3c3 f ξ + tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ + tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ +
      tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ + tlTTwoP3c10 f ξ + tlTTwoP3c11 f ξ + tlTTwoP3c12 f ξ +
      tlTTwoP3c13 f ξ + tlTTwoP3c14 f ξ + tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ + tlTTwoP4c2 f ξ +
      tlTTwoP4c3 f ξ + tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ + tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ +
      tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ + tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ + tlTTwoP4c12 f ξ +
      tlTTwoP4c13 f ξ + tlTTwoP4c14 f ξ + tlTTwoP4c15 f ξ + tlTTwoP4c16 f ξ + tlTTwoP5c0 f ξ +
      tlTTwoP5c1 f ξ + tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ + tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ +
      tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ + tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ + tlTTwoP5c10 f ξ +
      tlTTwoP5c11 f ξ + tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ + tlTTwoP5c14 f ξ + tlTTwoP5c15 f ξ +
      tlTTwoP5c16 f ξ + tlTTwoP5c17 f ξ + tlTTwoP5c18 f ξ + tlTTwoP5c19 f ξ + tlTTwoP6c0 f ξ +
      tlTTwoP6c1 f ξ + tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ + tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ +
      tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ + tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ + tlTTwoP6c10 f ξ +
      tlTTwoP6c11 f ξ + tlTTwoP6c12 f ξ + tlTTwoP6c13 f ξ + tlTTwoP6c14 f ξ + tlTTwoP7c0 f ξ +
      tlTTwoP7c1 f ξ + tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ + tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ +
      tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ + tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ + tlTTwoP7c10 f ξ +
      tlTTwoP7c11 f ξ + tlTTwoP7c12 f ξ + tlTTwoP7c13 f ξ + tlTTwoP7c14 f ξ + tlTTwoP7c15 f ξ +
      tlTTwoP7c16 f ξ + tlTTwoP7c17 f ξ + tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ + tlTTwoP8c2 f ξ +
      tlTTwoP8c3 f ξ + tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ + tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ +
      tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ + tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ + tlTTwoP8c12 f ξ +
      tlTTwoP8c13 f ξ + tlTTwoP8c14 f ξ + tlTTwoP8c15 f ξ + tlTTwoP8c16 f ξ + tlTTwoP8c17 f ξ +
      tlTTwoP8c18 f ξ + tlTTwoP8c19 f ξ + tlTTwoP8c20 f ξ + tlTTwoP8c21 f ξ + tlTTwoP9c0 f ξ +
      tlTTwoP9c1 f ξ + tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ + tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ +
      tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ + tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ + tlTTwoP9c10 f ξ +
      tlTTwoP9c11 f ξ + tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ + tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ +
      tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ + tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ + tlTTwoP10c6 f ξ +
      tlTTwoP10c7 f ξ + tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ + tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ +
      tlTTwoP10c12 f ξ + tlTTwoP10c13 f ξ + tlTTwoP10c14 f ξ + tlTTwoP10c15 f ξ + tlTTwoP10c16 f ξ
      + tlTTwoP10c17 f ξ + tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ + tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ +
      tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ + tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ + tlTTwoP11c8 f ξ +
      tlTTwoP11c9 f ξ + tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ + tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ
      + tlTTwoP11c14 f ξ + tlTTwoP11c15 f ξ + tlTTwoP11c16 f ξ + tlTTwoP11c17 f ξ + tlTTwoP12c0 f
      ξ + tlTTwoP12c1 f ξ + tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ + tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ
      + tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ + tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ + tlTTwoP12c10 f ξ +
      tlTTwoP12c11 f ξ + tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ) * tl_brM2 f - (tlTOneP0c0 f ξ +
      tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ + tlTOneP0c5 f ξ +
      tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP0c9 f ξ + tlTOneP1c0 f ξ +
      tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ + tlTOneP1c5 f ξ +
      tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ + tlTOneP1c10 f ξ +
      tlTOneP2c0 f ξ + tlTOneP2c1 f ξ + tlTOneP2c2 f ξ + tlTOneP2c3 f ξ + tlTOneP2c4 f ξ +
      tlTOneP2c5 f ξ + tlTOneP2c6 f ξ + tlTOneP2c7 f ξ + tlTOneP2c8 f ξ + tlTOneP2c9 f ξ +
      tlTOneP2c10 f ξ + tlTOneP2c11 f ξ + tlTOneP2c12 f ξ + tlTOneP3c0 f ξ + tlTOneP3c1 f ξ +
      tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ + tlTOneP3c5 f ξ + tlTOneP3c6 f ξ +
      tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ + tlTOneP3c10 f ξ + tlTOneP3c11 f ξ +
      tlTOneP3c12 f ξ + tlTOneP3c13 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ + tlTOneP4c2 f ξ +
      tlTOneP4c3 f ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ + tlTOneP4c7 f ξ +
      tlTOneP4c8 f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ + tlTOneP4c12 f ξ +
      tlTOneP4c13 f ξ + tlTOneP4c14 f ξ + tlTOneP5c0 f ξ + tlTOneP5c1 f ξ + tlTOneP5c2 f ξ +
      tlTOneP5c3 f ξ + tlTOneP5c4 f ξ + tlTOneP5c5 f ξ + tlTOneP5c6 f ξ + tlTOneP5c7 f ξ +
      tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ + tlTOneP5c11 f ξ + tlTOneP5c12 f ξ +
      tlTOneP5c13 f ξ + tlTOneP5c14 f ξ + tlTOneP5c15 f ξ + tlTOneP6c0 f ξ + tlTOneP6c1 f ξ +
      tlTOneP6c2 f ξ + tlTOneP6c3 f ξ + tlTOneP6c4 f ξ + tlTOneP6c5 f ξ + tlTOneP6c6 f ξ +
      tlTOneP6c7 f ξ + tlTOneP6c8 f ξ + tlTOneP6c9 f ξ + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ +
      tlTOneP6c12 f ξ + tlTOneP6c13 f ξ + tlTOneP6c14 f ξ + tlTOneP6c15 f ξ + tlTOneP7c0 f ξ +
      tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ + tlTOneP7c5 f ξ +
      tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ + tlTOneP7c10 f ξ +
      tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP7c13 f ξ + tlTOneP7c14 f ξ + tlTOneP7c15 f ξ +
      tlTOneP8c0 f ξ + tlTOneP8c1 f ξ + tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ +
      tlTOneP8c5 f ξ + tlTOneP8c6 f ξ + tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ +
      tlTOneP8c10 f ξ + tlTOneP8c11 f ξ + tlTOneP8c12 f ξ + tlTOneP8c13 f ξ + tlTOneP8c14 f ξ +
      tlTOneP8c15 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ + tlTOneP9c3 f ξ +
      tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ + tlTOneP9c8 f ξ +
      tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ + tlTOneP9c13 f ξ +
      tlTOneP9c14 f ξ + tlTOneP10c0 f ξ + tlTOneP10c1 f ξ + tlTOneP10c2 f ξ + tlTOneP10c3 f ξ +
      tlTOneP10c4 f ξ + tlTOneP10c5 f ξ + tlTOneP10c6 f ξ + tlTOneP10c7 f ξ + tlTOneP10c8 f ξ +
      tlTOneP10c9 f ξ + tlTOneP10c10 f ξ + tlTOneP10c11 f ξ + tlTOneP10c12 f ξ + tlTOneP10c13 f ξ
      + tlTOneP10c14 f ξ + tlTOneP10c15 f ξ) * tl_brM1 f - (tlDCbP0c0 f ξ + tlDCbP0c1 f ξ +
      tlDCbP0c2 f ξ + tlDCbP0c3 f ξ + tlDCbP0c4 f ξ + tlDCbP0c5 f ξ + tlDCbP0c6 f ξ + tlDCbP0c7 f
      ξ + tlDCbP0c8 f ξ + tlDCbP0c9 f ξ + tlDCbP0c10 f ξ + tlDCbP0c11 f ξ + tlDCbP0c12 f ξ +
      tlDCbP1c0 f ξ + tlDCbP1c1 f ξ + tlDCbP1c2 f ξ + tlDCbP1c3 f ξ + tlDCbP1c4 f ξ + tlDCbP1c5 f
      ξ + tlDCbP1c6 f ξ + tlDCbP1c7 f ξ + tlDCbP1c8 f ξ + tlDCbP1c9 f ξ + tlDCbP1c10 f ξ +
      tlDCbP1c11 f ξ + tlDCbP1c12 f ξ + tlDCbP1c13 f ξ + tlDCbP1c14 f ξ + tlDCbP1c15 f ξ +
      tlDCbP1c16 f ξ + tlDCbP2c0 f ξ + tlDCbP2c1 f ξ + tlDCbP2c2 f ξ + tlDCbP2c3 f ξ + tlDCbP2c4 f
      ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ + tlDCbP2c8 f ξ + tlDCbP2c9 f ξ +
      tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ + tlDCbP2c13 f ξ + tlDCbP2c14 f ξ +
      tlDCbP2c15 f ξ + tlDCbP2c16 f ξ) * tl_brM0 f + tl_zero f ξ

lemma kernel_cubic_at {f ξ : ℚ} (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0)
    (hD : tlD0 f ξ + tlD1 f ξ ≠ 0) :
    kernelCubicM f ((tlN0 f ξ + tlN1 f ξ + tlN2 f ξ + tlN3 f ξ + tlN4 f ξ) / (tlD0 f ξ + tlD1 f
      ξ)) = 0 := by
  have h := tl_mnum hT
  simp only [kernelCubicM]
  field_simp
  linear_combination h

lemma tl_ne_Zero {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    ξ ≠ (0 : ℚ) := by
  intro hz
  subst hz
  have hval : f ^ 14 * (f - 1) ^ 7 * (f ^ 2 - f + 1) ^ 6 = 0 := by
    simp only [tlT0, tlT1, tlT2, tlT3] at hT
    linear_combination hT
  rcases mul_eq_zero.mp hval with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hf0 (pow_eq_zero_iff (by norm_num) |>.mp h')
    · exact hf1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h'))
  · exact quad_ne f (pow_eq_zero_iff (by norm_num) |>.mp h)

lemma tl_ne_C {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    ξ ≠ f ^ 2 * (f - 1) := by
  intro hz
  subst hz
  have hval : f ^ 18 * (f - 1) ^ 18 = 0 := by
    simp only [tlT0, tlT1, tlT2, tlT3] at hT
    linear_combination hT
  rcases mul_eq_zero.mp hval with h | h
  · exact hf0 (pow_eq_zero_iff (by norm_num) |>.mp h)
  · exact hf1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h))

lemma tl_ne_BF {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    ξ ≠ f * (f - 1) * (f ^ 2 - f + 1) := by
  intro hz
  subst hz
  have hval : f ^ 8 * (f - 1) ^ 19 * (f ^ 2 - f + 1) ^ 6 = 0 := by
    simp only [tlT0, tlT1, tlT2, tlT3] at hT
    linear_combination hT
  rcases mul_eq_zero.mp hval with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hf0 (pow_eq_zero_iff (by norm_num) |>.mp h')
    · exact hf1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h'))
  · exact quad_ne f (pow_eq_zero_iff (by norm_num) |>.mp h)

lemma tl_ne_B {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    ξ ≠ f ^ 2 * (f - 1) * (f ^ 2 - f + 1) := by
  intro hz
  subst hz
  have hval : f ^ 20 * (f - 1) ^ 13 * (f ^ 2 - f + 1) ^ 6 = 0 := by
    simp only [tlT0, tlT1, tlT2, tlT3] at hT
    linear_combination hT
  rcases mul_eq_zero.mp hval with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hf0 (pow_eq_zero_iff (by norm_num) |>.mp h')
    · exact hf1 (sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h'))
  · exact quad_ne f (pow_eq_zero_iff (by norm_num) |>.mp h)

lemma tl_d_ne {f ξ : ℚ} (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hT : tlT0 f ξ + tlT1 f ξ + tlT2 f ξ + tlT3 f ξ = 0) :
    (tlD0 f ξ + tlD1 f ξ) ≠ 0 := by
  have h1 := tl_ne_Zero hf0 hf1 hT
  have h2 := tl_ne_C hf0 hf1 hT
  have h3 := tl_ne_BF hf0 hf1 hT
  have h4 := tl_ne_B hf0 hf1 hT
  have hfac : (tlD0 f ξ + tlD1 f ξ) = ξ ^ 2 * (ξ - f ^ 2 * (f - 1)) ^ 2 *
      (ξ - f * (f - 1) * (f ^ 2 - f + 1)) ^ 2 *
      (ξ - f ^ 2 * (f - 1) * (f ^ 2 - f + 1)) ^ 2 := by
    simp only [tlD0, tlD1]
    ring
  rw [hfac]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (pow_ne_zero 2 h1) (pow_ne_zero 2 (sub_ne_zero.mpr h2)))
    (pow_ne_zero 2 (sub_ne_zero.mpr h3))) (pow_ne_zero 2 (sub_ne_zero.mpr h4))

/-- The trisection abscissa produces a third leg completing the
`X₀(9)` chain after the two family legs. -/

end MazurTorsion.Kubert
