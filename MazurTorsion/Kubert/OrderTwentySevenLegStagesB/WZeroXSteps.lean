/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Zero-weight coefficient identities

The independent zero-weight coefficient identities.
-/

namespace MazurTorsion.Kubert

lemma tlWZeroX_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP0c0 f ξ + tlDCbP0c1 f ξ + tlDCbP0c2 f ξ + tlDCbP0c3 f ξ + tlDCbP0c4 f ξ + tlDCbP0c5 f ξ
      + tlDCbP0c6 f ξ + tlDCbP0c7 f ξ + tlDCbP0c8 f ξ + tlDCbP0c9 f ξ + tlDCbP1c0 f ξ + tlDCbP1c1
      f ξ + tlDCbP1c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP0c0 f ξ + tlWZeroXP0c1 f ξ) + (tlWZeroXP0c2 f ξ + tlWZeroXP0c3 f ξ)) +
        ((tlWZeroXP0c4 f ξ + tlWZeroXP0c5 f ξ) + (tlWZeroXP0c6 f ξ + tlWZeroXP0c7 f ξ))) +
        (((tlWZeroXP0c8 f ξ + tlWZeroXP0c9 f ξ) + (tlWZeroXP0c10 f ξ + tlWZeroXP0c11 f ξ))
        + ((tlWZeroXP0c12 f ξ + tlWZeroXP0c13 f ξ) + (tlWZeroXP0c14 f ξ + tlWZeroXP0c15 f
        ξ)))) + tlWZeroXP0c16 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP0c0, tlDCbP0c1, tlDCbP0c2, tlDCbP0c3, tlDCbP0c4, tlDCbP0c5, tlDCbP0c6,
      tlDCbP0c7, tlDCbP0c8, tlDCbP0c9, tlDCbP1c0, tlDCbP1c1, tlDCbP1c2, tlMZeroV0,
      tlT0, tlT1, tlT2, tlT3, tlWZeroXP0c0, tlWZeroXP0c1, tlWZeroXP0c10,
      tlWZeroXP0c11, tlWZeroXP0c12, tlWZeroXP0c13, tlWZeroXP0c14, tlWZeroXP0c15,
      tlWZeroXP0c16, tlWZeroXP0c2, tlWZeroXP0c3, tlWZeroXP0c4, tlWZeroXP0c5,
      tlWZeroXP0c6, tlWZeroXP0c7, tlWZeroXP0c8, tlWZeroXP0c9]
  ring1

lemma tlWZeroX_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP1c3 f ξ + tlDCbP1c4 f ξ + tlDCbP1c5 f ξ + tlDCbP1c6 f ξ + tlDCbP1c7 f ξ + tlDCbP1c8 f ξ
      + tlDCbP1c9 f ξ + tlDCbP1c10 f ξ + tlDCbP1c11 f ξ + tlDCbP1c12 f ξ + tlDCbP2c0 f ξ +
      tlDCbP2c1 f ξ + tlDCbP2c2 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP1c0 f ξ + tlWZeroXP1c1 f ξ) + (tlWZeroXP1c2 f ξ + tlWZeroXP1c3 f ξ)) +
        ((tlWZeroXP1c4 f ξ + tlWZeroXP1c5 f ξ) + (tlWZeroXP1c6 f ξ + tlWZeroXP1c7 f ξ))) +
        (((tlWZeroXP1c8 f ξ + tlWZeroXP1c9 f ξ) + (tlWZeroXP1c10 f ξ + tlWZeroXP1c11 f ξ))
        + ((tlWZeroXP1c12 f ξ + tlWZeroXP1c13 f ξ) + (tlWZeroXP1c14 f ξ + tlWZeroXP1c15 f
        ξ)))) + ((tlWZeroXP1c16 f ξ + tlWZeroXP1c17 f ξ) + tlWZeroXP1c18 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP1c10, tlDCbP1c11, tlDCbP1c12, tlDCbP1c3, tlDCbP1c4, tlDCbP1c5, tlDCbP1c6,
      tlDCbP1c7, tlDCbP1c8, tlDCbP1c9, tlDCbP2c0, tlDCbP2c1, tlDCbP2c2, tlMZeroV0,
      tlT0, tlT1, tlT2, tlT3, tlWZeroXP1c0, tlWZeroXP1c1, tlWZeroXP1c10,
      tlWZeroXP1c11, tlWZeroXP1c12, tlWZeroXP1c13, tlWZeroXP1c14, tlWZeroXP1c15,
      tlWZeroXP1c16, tlWZeroXP1c17, tlWZeroXP1c18, tlWZeroXP1c2, tlWZeroXP1c3,
      tlWZeroXP1c4, tlWZeroXP1c5, tlWZeroXP1c6, tlWZeroXP1c7, tlWZeroXP1c8,
      tlWZeroXP1c9]
  ring1

lemma tlWZeroX_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP2c3 f ξ + tlDCbP2c4 f ξ + tlDCbP2c5 f ξ + tlDCbP2c6 f ξ + tlDCbP2c7 f ξ + tlDCbP2c8 f ξ
      + tlDCbP2c9 f ξ + tlDCbP2c10 f ξ + tlDCbP2c11 f ξ + tlDCbP2c12 f ξ + tlDCbP2c13 f ξ +
      tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) * tlMZeroV0 f =
      ((((tlWZeroXP2c0 f ξ + tlWZeroXP2c1 f ξ) + (tlWZeroXP2c2 f ξ + tlWZeroXP2c3 f ξ)) +
        ((tlWZeroXP2c4 f ξ + tlWZeroXP2c5 f ξ) + (tlWZeroXP2c6 f ξ + tlWZeroXP2c7 f ξ))) +
        (((tlWZeroXP2c8 f ξ + tlWZeroXP2c9 f ξ) + (tlWZeroXP2c10 f ξ + tlWZeroXP2c11 f ξ))
        + ((tlWZeroXP2c12 f ξ + tlWZeroXP2c13 f ξ) + (tlWZeroXP2c14 f ξ + tlWZeroXP2c15 f
        ξ)))) + ((tlWZeroXP2c16 f ξ + tlWZeroXP2c17 f ξ) + (tlWZeroXP2c18 f ξ +
        tlWZeroXP2c19 f ξ)) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP2c10, tlDCbP2c11, tlDCbP2c12, tlDCbP2c13, tlDCbP2c3, tlDCbP2c4, tlDCbP2c5,
      tlDCbP2c6, tlDCbP2c7, tlDCbP2c8, tlDCbP2c9, tlDCbP3c0, tlDCbP3c1, tlMZeroV0,
      tlT0, tlT1, tlT2, tlT3, tlWZeroXP2c0, tlWZeroXP2c1, tlWZeroXP2c10,
      tlWZeroXP2c11, tlWZeroXP2c12, tlWZeroXP2c13, tlWZeroXP2c14, tlWZeroXP2c15,
      tlWZeroXP2c16, tlWZeroXP2c17, tlWZeroXP2c18, tlWZeroXP2c19, tlWZeroXP2c2,
      tlWZeroXP2c3, tlWZeroXP2c4, tlWZeroXP2c5, tlWZeroXP2c6, tlWZeroXP2c7,
      tlWZeroXP2c8, tlWZeroXP2c9]
  ring1

lemma tlWZeroX_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDCbP3c2 f ξ + tlDCbP3c3 f ξ + tlDCbP3c4 f ξ + tlDCbP3c5 f ξ + tlDCbP3c6 f ξ + tlDCbP3c7 f ξ
      + tlDCbP3c8 f ξ + tlDCbP3c9 f ξ + tlDCbP3c10 f ξ + tlDCbP3c11 f ξ) * tlMZeroV0 f =
      (((tlWZeroXP3c0 f ξ + tlWZeroXP3c1 f ξ) + (tlWZeroXP3c2 f ξ + tlWZeroXP3c3 f ξ)) +
        ((tlWZeroXP3c4 f ξ + tlWZeroXP3c5 f ξ) + (tlWZeroXP3c6 f ξ + tlWZeroXP3c7 f ξ))) +
        (((tlWZeroXP3c8 f ξ + tlWZeroXP3c9 f ξ) + (tlWZeroXP3c10 f ξ + tlWZeroXP3c11 f ξ))
        + ((tlWZeroXP3c12 f ξ + tlWZeroXP3c13 f ξ) + (tlWZeroXP3c14 f ξ + tlWZeroXP3c15 f
        ξ))) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlDCbP3c10, tlDCbP3c11, tlDCbP3c2, tlDCbP3c3, tlDCbP3c4, tlDCbP3c5, tlDCbP3c6,
      tlDCbP3c7, tlDCbP3c8, tlDCbP3c9, tlMZeroV0, tlT0, tlT1, tlT2, tlT3,
      tlWZeroXP3c0, tlWZeroXP3c1, tlWZeroXP3c10, tlWZeroXP3c11, tlWZeroXP3c12,
      tlWZeroXP3c13, tlWZeroXP3c14, tlWZeroXP3c15, tlWZeroXP3c2, tlWZeroXP3c3,
      tlWZeroXP3c4, tlWZeroXP3c5, tlWZeroXP3c6, tlWZeroXP3c7, tlWZeroXP3c8,
      tlWZeroXP3c9]
  ring1


end MazurTorsion.Kubert
