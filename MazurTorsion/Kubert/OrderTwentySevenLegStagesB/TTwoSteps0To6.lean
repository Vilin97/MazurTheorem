/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Second-power product identities 0 through 6

The first independent identities for the second-power product.
-/

namespace MazurTorsion.Kubert

lemma tlTTwo_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c0 f ξ + tlNSqP0c1 f ξ + tlNSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP0c0 f ξ + tlTTwoP0c1 f ξ) + (tlTTwoP0c2 f ξ + tlTTwoP0c3 f ξ)) +
        ((tlTTwoP0c4 f ξ + tlTTwoP0c5 f ξ) + (tlTTwoP0c6 f ξ + tlTTwoP0c7 f ξ))) +
        (tlTTwoP0c8 f ξ + tlTTwoP0c9 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ0c0 f ξ) * hT + (tlTTwoQ0c1 f ξ) * hT + (tlTTwoQ0c2 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP0c0, tlNSqP0c1, tlNSqP0c2, tlT0, tlT1, tlT2, tlT3, tlTTwoP0c0,
      tlTTwoP0c1, tlTTwoP0c2, tlTTwoP0c3, tlTTwoP0c4, tlTTwoP0c5, tlTTwoP0c6,
      tlTTwoP0c7, tlTTwoP0c8, tlTTwoP0c9, tlTTwoQ0c0, tlTTwoQ0c1, tlTTwoQ0c2]
  ring1

lemma tlTTwo_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c3 f ξ + tlNSqP0c4 f ξ + tlNSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP1c0 f ξ + tlTTwoP1c1 f ξ) + (tlTTwoP1c2 f ξ + tlTTwoP1c3 f ξ)) +
        ((tlTTwoP1c4 f ξ + tlTTwoP1c5 f ξ) + (tlTTwoP1c6 f ξ + tlTTwoP1c7 f ξ))) +
        (((tlTTwoP1c8 f ξ + tlTTwoP1c9 f ξ) + (tlTTwoP1c10 f ξ + tlTTwoP1c11 f ξ)) +
        tlTTwoP1c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ1c0 f ξ) * hT + (tlTTwoQ1c1 f ξ) * hT + (tlTTwoQ1c2 f ξ) * hT + (tlTTwoQ1c3 f ξ) * hT
      + (tlTTwoQ1c4 f ξ) * hT + (tlTTwoQ1c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP0c3, tlNSqP0c4, tlNSqP0c5, tlT0, tlT1, tlT2, tlT3, tlTTwoP1c0,
      tlTTwoP1c1, tlTTwoP1c10, tlTTwoP1c11, tlTTwoP1c12, tlTTwoP1c2, tlTTwoP1c3,
      tlTTwoP1c4, tlTTwoP1c5, tlTTwoP1c6, tlTTwoP1c7, tlTTwoP1c8, tlTTwoP1c9,
      tlTTwoQ1c0, tlTTwoQ1c1, tlTTwoQ1c2, tlTTwoQ1c3, tlTTwoQ1c4, tlTTwoQ1c5]
  ring1

lemma tlTTwo_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ + tlNSqP0c8 f ξ + tlNSqP1c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP2c0 f ξ + tlTTwoP2c1 f ξ) + (tlTTwoP2c2 f ξ + tlTTwoP2c3 f ξ)) +
        ((tlTTwoP2c4 f ξ + tlTTwoP2c5 f ξ) + (tlTTwoP2c6 f ξ + tlTTwoP2c7 f ξ))) +
        (((tlTTwoP2c8 f ξ + tlTTwoP2c9 f ξ) + (tlTTwoP2c10 f ξ + tlTTwoP2c11 f ξ)) +
        ((tlTTwoP2c12 f ξ + tlTTwoP2c13 f ξ) + (tlTTwoP2c14 f ξ + tlTTwoP2c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlTTwoQ2c0 f ξ) * hT + (tlTTwoQ2c1 f ξ) * hT + (tlTTwoQ2c2 f ξ) * hT + (tlTTwoQ2c3 f ξ) * hT
      + (tlTTwoQ2c4 f ξ) * hT + (tlTTwoQ2c5 f ξ) * hT + (tlTTwoQ2c6 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP0c6, tlNSqP0c7, tlNSqP0c8, tlNSqP1c0, tlT0, tlT1, tlT2, tlT3,
      tlTTwoP2c0, tlTTwoP2c1, tlTTwoP2c10, tlTTwoP2c11, tlTTwoP2c12, tlTTwoP2c13,
      tlTTwoP2c14, tlTTwoP2c15, tlTTwoP2c2, tlTTwoP2c3, tlTTwoP2c4, tlTTwoP2c5,
      tlTTwoP2c6, tlTTwoP2c7, tlTTwoP2c8, tlTTwoP2c9, tlTTwoQ2c0, tlTTwoQ2c1,
      tlTTwoQ2c2, tlTTwoQ2c3, tlTTwoQ2c4, tlTTwoQ2c5, tlTTwoQ2c6]
  ring1

lemma tlTTwo_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c1 f ξ + tlNSqP1c2 f ξ + tlNSqP1c3 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP3c0 f ξ + tlTTwoP3c1 f ξ) + (tlTTwoP3c2 f ξ + tlTTwoP3c3 f ξ)) +
        ((tlTTwoP3c4 f ξ + tlTTwoP3c5 f ξ) + (tlTTwoP3c6 f ξ + tlTTwoP3c7 f ξ))) +
        ((tlTTwoP3c8 f ξ + tlTTwoP3c9 f ξ) + (tlTTwoP3c10 f ξ + tlTTwoP3c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ3c0 f ξ) * hT + (tlTTwoQ3c1 f ξ) * hT + (tlTTwoQ3c2 f ξ) * hT + (tlTTwoQ3c3 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP1c1, tlNSqP1c2, tlNSqP1c3, tlT0, tlT1, tlT2, tlT3, tlTTwoP3c0,
      tlTTwoP3c1, tlTTwoP3c10, tlTTwoP3c11, tlTTwoP3c2, tlTTwoP3c3, tlTTwoP3c4,
      tlTTwoP3c5, tlTTwoP3c6, tlTTwoP3c7, tlTTwoP3c8, tlTTwoP3c9, tlTTwoQ3c0,
      tlTTwoQ3c1, tlTTwoQ3c2, tlTTwoQ3c3]
  ring1

lemma tlTTwo_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c4 f ξ + tlNSqP1c5 f ξ + tlNSqP1c6 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP4c0 f ξ + tlTTwoP4c1 f ξ) + (tlTTwoP4c2 f ξ + tlTTwoP4c3 f ξ)) +
        ((tlTTwoP4c4 f ξ + tlTTwoP4c5 f ξ) + (tlTTwoP4c6 f ξ + tlTTwoP4c7 f ξ))) +
        (((tlTTwoP4c8 f ξ + tlTTwoP4c9 f ξ) + (tlTTwoP4c10 f ξ + tlTTwoP4c11 f ξ)) +
        (tlTTwoP4c12 f ξ + tlTTwoP4c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ4c0 f ξ) * hT + (tlTTwoQ4c1 f ξ) * hT + (tlTTwoQ4c2 f ξ) * hT + (tlTTwoQ4c3 f ξ) * hT
      + (tlTTwoQ4c4 f ξ) * hT + (tlTTwoQ4c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP1c4, tlNSqP1c5, tlNSqP1c6, tlT0, tlT1, tlT2, tlT3, tlTTwoP4c0,
      tlTTwoP4c1, tlTTwoP4c10, tlTTwoP4c11, tlTTwoP4c12, tlTTwoP4c13, tlTTwoP4c2,
      tlTTwoP4c3, tlTTwoP4c4, tlTTwoP4c5, tlTTwoP4c6, tlTTwoP4c7, tlTTwoP4c8,
      tlTTwoP4c9, tlTTwoQ4c0, tlTTwoQ4c1, tlTTwoQ4c2, tlTTwoQ4c3, tlTTwoQ4c4,
      tlTTwoQ4c5]
  ring1

lemma tlTTwo_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c7 f ξ + tlNSqP1c8 f ξ + tlNSqP1c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP5c0 f ξ + tlTTwoP5c1 f ξ) + (tlTTwoP5c2 f ξ + tlTTwoP5c3 f ξ)) +
        ((tlTTwoP5c4 f ξ + tlTTwoP5c5 f ξ) + (tlTTwoP5c6 f ξ + tlTTwoP5c7 f ξ))) +
        (((tlTTwoP5c8 f ξ + tlTTwoP5c9 f ξ) + (tlTTwoP5c10 f ξ + tlTTwoP5c11 f ξ)) +
        (tlTTwoP5c12 f ξ + tlTTwoP5c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ5c0 f ξ) * hT + (tlTTwoQ5c1 f ξ) * hT + (tlTTwoQ5c2 f ξ) * hT + (tlTTwoQ5c3 f ξ) * hT
      + (tlTTwoQ5c4 f ξ) * hT + (tlTTwoQ5c5 f ξ) * hT + (tlTTwoQ5c6 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP1c7, tlNSqP1c8, tlNSqP1c9, tlT0, tlT1, tlT2, tlT3, tlTTwoP5c0,
      tlTTwoP5c1, tlTTwoP5c10, tlTTwoP5c11, tlTTwoP5c12, tlTTwoP5c13, tlTTwoP5c2,
      tlTTwoP5c3, tlTTwoP5c4, tlTTwoP5c5, tlTTwoP5c6, tlTTwoP5c7, tlTTwoP5c8,
      tlTTwoP5c9, tlTTwoQ5c0, tlTTwoQ5c1, tlTTwoQ5c2, tlTTwoQ5c3, tlTTwoQ5c4,
      tlTTwoQ5c5, tlTTwoQ5c6]
  ring1

lemma tlTTwo_s6 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c0 f ξ + tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP6c0 f ξ + tlTTwoP6c1 f ξ) + (tlTTwoP6c2 f ξ + tlTTwoP6c3 f ξ)) +
        ((tlTTwoP6c4 f ξ + tlTTwoP6c5 f ξ) + (tlTTwoP6c6 f ξ + tlTTwoP6c7 f ξ))) +
        (tlTTwoP6c8 f ξ + tlTTwoP6c9 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ6c0 f ξ) * hT + (tlTTwoQ6c1 f ξ) * hT + (tlTTwoQ6c2 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c0, tlNSqP2c1, tlNSqP2c2, tlT0, tlT1, tlT2, tlT3, tlTTwoP6c0,
      tlTTwoP6c1, tlTTwoP6c2, tlTTwoP6c3, tlTTwoP6c4, tlTTwoP6c5, tlTTwoP6c6,
      tlTTwoP6c7, tlTTwoP6c8, tlTTwoP6c9, tlTTwoQ6c0, tlTTwoQ6c1, tlTTwoQ6c2]
  ring1


end MazurTorsion.Kubert
