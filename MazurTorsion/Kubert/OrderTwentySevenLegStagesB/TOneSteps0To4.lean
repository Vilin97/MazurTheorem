/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# First-power product identities 0 through 4

The first independent identities for the first-power product.
-/

namespace MazurTorsion.Kubert

lemma tlTOne_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP0c0 f ξ + tlTOneP0c1 f ξ) + (tlTOneP0c2 f ξ + tlTOneP0c3 f ξ)) +
        ((tlTOneP0c4 f ξ + tlTOneP0c5 f ξ) + (tlTOneP0c6 f ξ + tlTOneP0c7 f ξ))) +
        tlTOneP0c8 f ξ := by
  linear_combination (norm := skip)
    (tlTOneQ0c0 f ξ) * hT + (tlTOneQ0c1 f ξ) * hT
  simp only [tlDSqP0c0, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP0c0,
      tlTOneP0c1, tlTOneP0c2, tlTOneP0c3, tlTOneP0c4, tlTOneP0c5, tlTOneP0c6,
      tlTOneP0c7, tlTOneP0c8, tlTOneQ0c0, tlTOneQ0c1]
  ring1

lemma tlTOne_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP1c0 f ξ + tlTOneP1c1 f ξ) + (tlTOneP1c2 f ξ + tlTOneP1c3 f ξ)) +
        ((tlTOneP1c4 f ξ + tlTOneP1c5 f ξ) + (tlTOneP1c6 f ξ + tlTOneP1c7 f ξ))) +
        (tlTOneP1c8 f ξ + tlTOneP1c9 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ1c0 f ξ) * hT + (tlTOneQ1c1 f ξ) * hT + (tlTOneQ1c2 f ξ) * hT
  simp only [tlDSqP0c1, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP1c0,
      tlTOneP1c1, tlTOneP1c2, tlTOneP1c3, tlTOneP1c4, tlTOneP1c5, tlTOneP1c6,
      tlTOneP1c7, tlTOneP1c8, tlTOneP1c9, tlTOneQ1c0, tlTOneQ1c1, tlTOneQ1c2]
  ring1

lemma tlTOne_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP2c0 f ξ + tlTOneP2c1 f ξ) + (tlTOneP2c2 f ξ + tlTOneP2c3 f ξ)) +
        ((tlTOneP2c4 f ξ + tlTOneP2c5 f ξ) + (tlTOneP2c6 f ξ + tlTOneP2c7 f ξ))) +
        ((tlTOneP2c8 f ξ + tlTOneP2c9 f ξ) + (tlTOneP2c10 f ξ + tlTOneP2c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlTOneQ2c0 f ξ) * hT + (tlTOneQ2c1 f ξ) * hT + (tlTOneQ2c2 f ξ) * hT + (tlTOneQ2c3 f ξ) * hT
  simp only [tlDSqP0c2, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP2c0,
      tlTOneP2c1, tlTOneP2c10, tlTOneP2c11, tlTOneP2c2, tlTOneP2c3, tlTOneP2c4,
      tlTOneP2c5, tlTOneP2c6, tlTOneP2c7, tlTOneP2c8, tlTOneP2c9, tlTOneQ2c0,
      tlTOneQ2c1, tlTOneQ2c2, tlTOneQ2c3]
  ring1

lemma tlTOne_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP3c0 f ξ + tlTOneP3c1 f ξ) + (tlTOneP3c2 f ξ + tlTOneP3c3 f ξ)) +
        ((tlTOneP3c4 f ξ + tlTOneP3c5 f ξ) + (tlTOneP3c6 f ξ + tlTOneP3c7 f ξ))) +
        (((tlTOneP3c8 f ξ + tlTOneP3c9 f ξ) + (tlTOneP3c10 f ξ + tlTOneP3c11 f ξ)) +
        tlTOneP3c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ3c0 f ξ) * hT + (tlTOneQ3c1 f ξ) * hT + (tlTOneQ3c2 f ξ) * hT + (tlTOneQ3c3 f ξ) * hT
      + (tlTOneQ3c4 f ξ) * hT
  simp only [tlDSqP0c3, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP3c0,
      tlTOneP3c1, tlTOneP3c10, tlTOneP3c11, tlTOneP3c12, tlTOneP3c2, tlTOneP3c3,
      tlTOneP3c4, tlTOneP3c5, tlTOneP3c6, tlTOneP3c7, tlTOneP3c8, tlTOneP3c9,
      tlTOneQ3c0, tlTOneQ3c1, tlTOneQ3c2, tlTOneQ3c3, tlTOneQ3c4]
  ring1

lemma tlTOne_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP4c0 f ξ + tlTOneP4c1 f ξ) + (tlTOneP4c2 f ξ + tlTOneP4c3 f ξ)) +
        ((tlTOneP4c4 f ξ + tlTOneP4c5 f ξ) + (tlTOneP4c6 f ξ + tlTOneP4c7 f ξ))) +
        (((tlTOneP4c8 f ξ + tlTOneP4c9 f ξ) + (tlTOneP4c10 f ξ + tlTOneP4c11 f ξ)) +
        tlTOneP4c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ4c0 f ξ) * hT + (tlTOneQ4c1 f ξ) * hT + (tlTOneQ4c2 f ξ) * hT + (tlTOneQ4c3 f ξ) * hT
      + (tlTOneQ4c4 f ξ) * hT + (tlTOneQ4c5 f ξ) * hT
  simp only [tlDSqP0c4, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP4c0,
      tlTOneP4c1, tlTOneP4c10, tlTOneP4c11, tlTOneP4c12, tlTOneP4c2, tlTOneP4c3,
      tlTOneP4c4, tlTOneP4c5, tlTOneP4c6, tlTOneP4c7, tlTOneP4c8, tlTOneP4c9,
      tlTOneQ4c0, tlTOneQ4c1, tlTOneQ4c2, tlTOneQ4c3, tlTOneQ4c4, tlTOneQ4c5]
  ring1


end MazurTorsion.Kubert
