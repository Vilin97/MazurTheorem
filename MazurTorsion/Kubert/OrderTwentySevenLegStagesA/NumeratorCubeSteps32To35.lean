/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Numerator-cube identities 32 through 35

The independent numerator-cube coefficient identities for steps 32 through 35.
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s32 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP32c0 f ξ + tlNCbP32c1 f ξ) + (tlNCbP32c2 f ξ + tlNCbP32c3 f ξ)) +
        ((tlNCbP32c4 f ξ + tlNCbP32c5 f ξ) + (tlNCbP32c6 f ξ + tlNCbP32c7 f ξ))) +
        (((tlNCbP32c8 f ξ + tlNCbP32c9 f ξ) + (tlNCbP32c10 f ξ + tlNCbP32c11 f ξ)) +
        ((tlNCbP32c12 f ξ + tlNCbP32c13 f ξ) + (tlNCbP32c14 f ξ + tlNCbP32c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlNCbQ32c0 f ξ) * hT + (tlNCbQ32c1 f ξ) * hT + (tlNCbQ32c2 f ξ) * hT + (tlNCbQ32c3 f ξ) * hT
      + (tlNCbQ32c4 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP32c0, tlNCbP32c1, tlNCbP32c10, tlNCbP32c11,
      tlNCbP32c12, tlNCbP32c13, tlNCbP32c14, tlNCbP32c15, tlNCbP32c2, tlNCbP32c3,
      tlNCbP32c4, tlNCbP32c5, tlNCbP32c6, tlNCbP32c7, tlNCbP32c8, tlNCbP32c9,
      tlNCbQ32c0, tlNCbQ32c1, tlNCbQ32c2, tlNCbQ32c3, tlNCbQ32c4, tlNSqP3c3, tlT0,
      tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s33 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP33c0 f ξ + tlNCbP33c1 f ξ) + (tlNCbP33c2 f ξ + tlNCbP33c3 f ξ)) +
        ((tlNCbP33c4 f ξ + tlNCbP33c5 f ξ) + (tlNCbP33c6 f ξ + tlNCbP33c7 f ξ))) +
        (((tlNCbP33c8 f ξ + tlNCbP33c9 f ξ) + (tlNCbP33c10 f ξ + tlNCbP33c11 f ξ)) +
        ((tlNCbP33c12 f ξ + tlNCbP33c13 f ξ) + (tlNCbP33c14 f ξ + tlNCbP33c15 f ξ)))) +
        tlNCbP33c16 f ξ := by
  linear_combination (norm := skip)
    (tlNCbQ33c0 f ξ) * hT + (tlNCbQ33c1 f ξ) * hT + (tlNCbQ33c2 f ξ) * hT + (tlNCbQ33c3 f ξ) * hT
      + (tlNCbQ33c4 f ξ) * hT + (tlNCbQ33c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP33c0, tlNCbP33c1, tlNCbP33c10, tlNCbP33c11,
      tlNCbP33c12, tlNCbP33c13, tlNCbP33c14, tlNCbP33c15, tlNCbP33c16, tlNCbP33c2,
      tlNCbP33c3, tlNCbP33c4, tlNCbP33c5, tlNCbP33c6, tlNCbP33c7, tlNCbP33c8,
      tlNCbP33c9, tlNCbQ33c0, tlNCbQ33c1, tlNCbQ33c2, tlNCbQ33c3, tlNCbQ33c4,
      tlNCbQ33c5, tlNSqP3c4, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s34 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP34c0 f ξ + tlNCbP34c1 f ξ) + (tlNCbP34c2 f ξ + tlNCbP34c3 f ξ)) +
        ((tlNCbP34c4 f ξ + tlNCbP34c5 f ξ) + (tlNCbP34c6 f ξ + tlNCbP34c7 f ξ))) +
        (((tlNCbP34c8 f ξ + tlNCbP34c9 f ξ) + (tlNCbP34c10 f ξ + tlNCbP34c11 f ξ)) +
        ((tlNCbP34c12 f ξ + tlNCbP34c13 f ξ) + (tlNCbP34c14 f ξ + tlNCbP34c15 f ξ)))) +
        (tlNCbP34c16 f ξ + tlNCbP34c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ34c0 f ξ) * hT + (tlNCbQ34c1 f ξ) * hT + (tlNCbQ34c2 f ξ) * hT + (tlNCbQ34c3 f ξ) * hT
      + (tlNCbQ34c4 f ξ) * hT + (tlNCbQ34c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP34c0, tlNCbP34c1, tlNCbP34c10, tlNCbP34c11,
      tlNCbP34c12, tlNCbP34c13, tlNCbP34c14, tlNCbP34c15, tlNCbP34c16, tlNCbP34c17,
      tlNCbP34c2, tlNCbP34c3, tlNCbP34c4, tlNCbP34c5, tlNCbP34c6, tlNCbP34c7,
      tlNCbP34c8, tlNCbP34c9, tlNCbQ34c0, tlNCbQ34c1, tlNCbQ34c2, tlNCbQ34c3,
      tlNCbQ34c4, tlNCbQ34c5, tlNSqP3c5, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s35 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP35c0 f ξ + tlNCbP35c1 f ξ) + (tlNCbP35c2 f ξ + tlNCbP35c3 f ξ)) +
        ((tlNCbP35c4 f ξ + tlNCbP35c5 f ξ) + (tlNCbP35c6 f ξ + tlNCbP35c7 f ξ))) +
        (((tlNCbP35c8 f ξ + tlNCbP35c9 f ξ) + (tlNCbP35c10 f ξ + tlNCbP35c11 f ξ)) +
        ((tlNCbP35c12 f ξ + tlNCbP35c13 f ξ) + (tlNCbP35c14 f ξ + tlNCbP35c15 f ξ)))) +
        (tlNCbP35c16 f ξ + tlNCbP35c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ35c0 f ξ) * hT + (tlNCbQ35c1 f ξ) * hT + (tlNCbQ35c2 f ξ) * hT + (tlNCbQ35c3 f ξ) * hT
      + (tlNCbQ35c4 f ξ) * hT + (tlNCbQ35c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP35c0, tlNCbP35c1, tlNCbP35c10, tlNCbP35c11,
      tlNCbP35c12, tlNCbP35c13, tlNCbP35c14, tlNCbP35c15, tlNCbP35c16, tlNCbP35c17,
      tlNCbP35c2, tlNCbP35c3, tlNCbP35c4, tlNCbP35c5, tlNCbP35c6, tlNCbP35c7,
      tlNCbP35c8, tlNCbP35c9, tlNCbQ35c0, tlNCbQ35c1, tlNCbQ35c2, tlNCbQ35c3,
      tlNCbQ35c4, tlNCbQ35c5, tlNSqP3c6, tlT0, tlT1, tlT2, tlT3]
  ring1

end MazurTorsion.Kubert
