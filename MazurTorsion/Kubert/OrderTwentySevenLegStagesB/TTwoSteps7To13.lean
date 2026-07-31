/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Second-power product identities 7 through 13

The remaining independent identities for the second-power product.
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c3 f ξ + tlNSqP2c4 f ξ + tlNSqP2c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ) + (tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ)) +
        ((tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ) + (tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ))) +
        (((tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ) + (tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ)) +
        tlTTwoP7c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ7c0 f ξ) * hT + (tlTTwoQ7c1 f ξ) * hT + (tlTTwoQ7c2 f ξ) * hT + (tlTTwoQ7c3 f ξ) * hT
      + (tlTTwoQ7c4 f ξ) * hT + (tlTTwoQ7c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c3, tlNSqP2c4, tlNSqP2c5, tlT0, tlT1, tlT2, tlT3, tlTTwoP7c0,
      tlTTwoP7c1, tlTTwoP7c10, tlTTwoP7c11, tlTTwoP7c12, tlTTwoP7c2, tlTTwoP7c3,
      tlTTwoP7c4, tlTTwoP7c5, tlTTwoP7c6, tlTTwoP7c7, tlTTwoP7c8, tlTTwoP7c9,
      tlTTwoQ7c0, tlTTwoQ7c1, tlTTwoQ7c2, tlTTwoQ7c3, tlTTwoQ7c4, tlTTwoQ7c5]
  ring1

lemma tlTTwo_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ + tlNSqP2c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ) + (tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ)) +
        ((tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ) + (tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ))) +
        (((tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ) + (tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ)) +
        (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ8c0 f ξ) * hT + (tlTTwoQ8c1 f ξ) * hT + (tlTTwoQ8c2 f ξ) * hT + (tlTTwoQ8c3 f ξ) * hT
      + (tlTTwoQ8c4 f ξ) * hT + (tlTTwoQ8c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c6, tlNSqP2c7, tlNSqP2c8, tlT0, tlT1, tlT2, tlT3, tlTTwoP8c0,
      tlTTwoP8c1, tlTTwoP8c10, tlTTwoP8c11, tlTTwoP8c12, tlTTwoP8c13, tlTTwoP8c2,
      tlTTwoP8c3, tlTTwoP8c4, tlTTwoP8c5, tlTTwoP8c6, tlTTwoP8c7, tlTTwoP8c8,
      tlTTwoP8c9, tlTTwoQ8c0, tlTTwoQ8c1, tlTTwoQ8c2, tlTTwoQ8c3, tlTTwoQ8c4,
      tlTTwoQ8c5]
  ring1

lemma tlTTwo_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c9 f ξ + tlNSqP2c10 f ξ + tlNSqP2c11 f ξ + tlNSqP3c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      ((((tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ)) +
        ((tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ))) +
        (((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) + (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ)) +
        ((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) + (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)))) +
        (tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ9c0 f ξ) * hT + (tlTTwoQ9c1 f ξ) * hT + (tlTTwoQ9c2 f ξ) * hT + (tlTTwoQ9c3 f ξ) * hT
      + (tlTTwoQ9c4 f ξ) * hT + (tlTTwoQ9c5 f ξ) * hT + (tlTTwoQ9c6 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c10, tlNSqP2c11, tlNSqP2c9, tlNSqP3c0, tlT0, tlT1, tlT2,
      tlT3, tlTTwoP9c0, tlTTwoP9c1, tlTTwoP9c10, tlTTwoP9c11, tlTTwoP9c12,
      tlTTwoP9c13, tlTTwoP9c14, tlTTwoP9c15, tlTTwoP9c16, tlTTwoP9c17, tlTTwoP9c2,
      tlTTwoP9c3, tlTTwoP9c4, tlTTwoP9c5, tlTTwoP9c6, tlTTwoP9c7, tlTTwoP9c8,
      tlTTwoP9c9, tlTTwoQ9c0, tlTTwoQ9c1, tlTTwoQ9c2, tlTTwoQ9c3, tlTTwoQ9c4,
      tlTTwoQ9c5, tlTTwoQ9c6]
  ring1

lemma tlTTwo_s10 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c1 f ξ + tlNSqP3c2 f ξ + tlNSqP3c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP10c0 f ξ + tlTTwoP10c1 f ξ) + (tlTTwoP10c2 f ξ + tlTTwoP10c3 f ξ)) +
        ((tlTTwoP10c4 f ξ + tlTTwoP10c5 f ξ) + (tlTTwoP10c6 f ξ + tlTTwoP10c7 f ξ))) +
        ((tlTTwoP10c8 f ξ + tlTTwoP10c9 f ξ) + (tlTTwoP10c10 f ξ + tlTTwoP10c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ10c0 f ξ) * hT + (tlTTwoQ10c1 f ξ) * hT + (tlTTwoQ10c2 f ξ) * hT + (tlTTwoQ10c3 f ξ) *
      hT
  simp only [tlD0, tlD1, tlNSqP3c1, tlNSqP3c2, tlNSqP3c3, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP10c0, tlTTwoP10c1, tlTTwoP10c10, tlTTwoP10c11, tlTTwoP10c2,
      tlTTwoP10c3, tlTTwoP10c4, tlTTwoP10c5, tlTTwoP10c6, tlTTwoP10c7, tlTTwoP10c8,
      tlTTwoP10c9, tlTTwoQ10c0, tlTTwoQ10c1, tlTTwoQ10c2, tlTTwoQ10c3]
  ring1

lemma tlTTwo_s11 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c4 f ξ + tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP11c0 f ξ + tlTTwoP11c1 f ξ) + (tlTTwoP11c2 f ξ + tlTTwoP11c3 f ξ)) +
        ((tlTTwoP11c4 f ξ + tlTTwoP11c5 f ξ) + (tlTTwoP11c6 f ξ + tlTTwoP11c7 f ξ))) +
        (((tlTTwoP11c8 f ξ + tlTTwoP11c9 f ξ) + (tlTTwoP11c10 f ξ + tlTTwoP11c11 f ξ)) +
        (tlTTwoP11c12 f ξ + tlTTwoP11c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ11c0 f ξ) * hT + (tlTTwoQ11c1 f ξ) * hT + (tlTTwoQ11c2 f ξ) * hT + (tlTTwoQ11c3 f ξ) *
      hT + (tlTTwoQ11c4 f ξ) * hT + (tlTTwoQ11c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c4, tlNSqP3c5, tlNSqP3c6, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP11c0, tlTTwoP11c1, tlTTwoP11c10, tlTTwoP11c11, tlTTwoP11c12,
      tlTTwoP11c13, tlTTwoP11c2, tlTTwoP11c3, tlTTwoP11c4, tlTTwoP11c5, tlTTwoP11c6,
      tlTTwoP11c7, tlTTwoP11c8, tlTTwoP11c9, tlTTwoQ11c0, tlTTwoQ11c1, tlTTwoQ11c2,
      tlTTwoQ11c3, tlTTwoQ11c4, tlTTwoQ11c5]
  ring1

lemma tlTTwo_s12 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c7 f ξ + tlNSqP3c8 f ξ + tlNSqP3c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP12c0 f ξ + tlTTwoP12c1 f ξ) + (tlTTwoP12c2 f ξ + tlTTwoP12c3 f ξ)) +
        ((tlTTwoP12c4 f ξ + tlTTwoP12c5 f ξ) + (tlTTwoP12c6 f ξ + tlTTwoP12c7 f ξ))) +
        (((tlTTwoP12c8 f ξ + tlTTwoP12c9 f ξ) + (tlTTwoP12c10 f ξ + tlTTwoP12c11 f ξ)) +
        (tlTTwoP12c12 f ξ + tlTTwoP12c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ12c0 f ξ) * hT + (tlTTwoQ12c1 f ξ) * hT + (tlTTwoQ12c2 f ξ) * hT + (tlTTwoQ12c3 f ξ) *
      hT + (tlTTwoQ12c4 f ξ) * hT + (tlTTwoQ12c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c7, tlNSqP3c8, tlNSqP3c9, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP12c0, tlTTwoP12c1, tlTTwoP12c10, tlTTwoP12c11, tlTTwoP12c12,
      tlTTwoP12c13, tlTTwoP12c2, tlTTwoP12c3, tlTTwoP12c4, tlTTwoP12c5, tlTTwoP12c6,
      tlTTwoP12c7, tlTTwoP12c8, tlTTwoP12c9, tlTTwoQ12c0, tlTTwoQ12c1, tlTTwoQ12c2,
      tlTTwoQ12c3, tlTTwoQ12c4, tlTTwoQ12c5]
  ring1

lemma tlTTwo_s13 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c10 f ξ + tlNSqP3c11 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP13c0 f ξ + tlTTwoP13c1 f ξ) + (tlTTwoP13c2 f ξ + tlTTwoP13c3 f ξ)) +
        ((tlTTwoP13c4 f ξ + tlTTwoP13c5 f ξ) + (tlTTwoP13c6 f ξ + tlTTwoP13c7 f ξ))) +
        (((tlTTwoP13c8 f ξ + tlTTwoP13c9 f ξ) + (tlTTwoP13c10 f ξ + tlTTwoP13c11 f ξ)) +
        tlTTwoP13c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ13c0 f ξ) * hT + (tlTTwoQ13c1 f ξ) * hT + (tlTTwoQ13c2 f ξ) * hT + (tlTTwoQ13c3 f ξ) *
      hT + (tlTTwoQ13c4 f ξ) * hT + (tlTTwoQ13c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP3c10, tlNSqP3c11, tlT0, tlT1, tlT2, tlT3, tlTTwoP13c0,
      tlTTwoP13c1, tlTTwoP13c10, tlTTwoP13c11, tlTTwoP13c12, tlTTwoP13c2,
      tlTTwoP13c3, tlTTwoP13c4, tlTTwoP13c5, tlTTwoP13c6, tlTTwoP13c7, tlTTwoP13c8,
      tlTTwoP13c9, tlTTwoQ13c0, tlTTwoQ13c1, tlTTwoQ13c2, tlTTwoQ13c3, tlTTwoQ13c4,
      tlTTwoQ13c5]
  ring1


end MazurTorsion.Kubert
