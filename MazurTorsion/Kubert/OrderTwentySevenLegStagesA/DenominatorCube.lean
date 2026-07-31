/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Denominator-cube identities for the order-twenty-seven certificate

The denominator-cube coefficient and value identities.
-/

namespace MazurTorsion.Kubert

lemma tlDCb_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c0 f ξ + tlDSqP0c1 f ξ + tlDSqP0c2 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP0c0 f ξ + tlDCbP0c1 f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4 f
        ξ + tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ + tlDCbP0c7 f ξ))) + (tlDCbP0c8 f ξ +
        tlDCbP0c9 f ξ) := by
  linear_combination (norm := skip)
    (tlDCbQ0c0 f ξ) * hT + (tlDCbQ0c1 f ξ) * hT + (tlDCbQ0c2 f ξ) * hT
  simp only [tlD0, tlD1, tlDCbP0c0, tlDCbP0c1, tlDCbP0c2, tlDCbP0c3, tlDCbP0c4, tlDCbP0c5,
      tlDCbP0c6, tlDCbP0c7, tlDCbP0c8, tlDCbP0c9, tlDCbQ0c0, tlDCbQ0c1, tlDCbQ0c2,
      tlDSqP0c0, tlDSqP0c1, tlDSqP0c2, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlDCb_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c3 f ξ + tlDSqP0c4 f ξ + tlDSqP0c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP1c0 f ξ + tlDCbP1c1 f ξ) + (tlDCbP1c2 f ξ + tlDCbP1c3 f ξ)) + ((tlDCbP1c4 f
        ξ + tlDCbP1c5 f ξ) + (tlDCbP1c6 f ξ + tlDCbP1c7 f ξ))) + (((tlDCbP1c8 f ξ +
        tlDCbP1c9 f ξ) + (tlDCbP1c10 f ξ + tlDCbP1c11 f ξ)) + tlDCbP1c12 f ξ) := by
  linear_combination (norm := skip)
    (tlDCbQ1c0 f ξ) * hT + (tlDCbQ1c1 f ξ) * hT + (tlDCbQ1c2 f ξ) * hT + (tlDCbQ1c3 f ξ) * hT +
      (tlDCbQ1c4 f ξ) * hT + (tlDCbQ1c5 f ξ) * hT
  simp only [tlD0, tlD1, tlDCbP1c0, tlDCbP1c1, tlDCbP1c10, tlDCbP1c11, tlDCbP1c12, tlDCbP1c2,
      tlDCbP1c3, tlDCbP1c4, tlDCbP1c5, tlDCbP1c6, tlDCbP1c7, tlDCbP1c8, tlDCbP1c9,
      tlDCbQ1c0, tlDCbQ1c1, tlDCbQ1c2, tlDCbQ1c3, tlDCbQ1c4, tlDCbQ1c5, tlDSqP0c3,
      tlDSqP0c4, tlDSqP0c5, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlDCb_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ + tlDSqP0c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP2c0 f ξ + tlDCbP2c1 f ξ) + (tlDCbP2c2 f ξ + tlDCbP2c3 f ξ)) + ((tlDCbP2c4 f
        ξ + tlDCbP2c5 f ξ) + (tlDCbP2c6 f ξ + tlDCbP2c7 f ξ))) + (((tlDCbP2c8 f ξ +
        tlDCbP2c9 f ξ) + (tlDCbP2c10 f ξ + tlDCbP2c11 f ξ)) + (tlDCbP2c12 f ξ + tlDCbP2c13
        f ξ)) := by
  linear_combination (norm := skip)
    (tlDCbQ2c0 f ξ) * hT + (tlDCbQ2c1 f ξ) * hT + (tlDCbQ2c2 f ξ) * hT + (tlDCbQ2c3 f ξ) * hT +
      (tlDCbQ2c4 f ξ) * hT + (tlDCbQ2c5 f ξ) * hT + (tlDCbQ2c6 f ξ) * hT
  simp only [tlD0, tlD1, tlDCbP2c0, tlDCbP2c1, tlDCbP2c10, tlDCbP2c11, tlDCbP2c12,
      tlDCbP2c13, tlDCbP2c2, tlDCbP2c3, tlDCbP2c4, tlDCbP2c5, tlDCbP2c6, tlDCbP2c7,
      tlDCbP2c8, tlDCbP2c9, tlDCbQ2c0, tlDCbQ2c1, tlDCbQ2c2, tlDCbQ2c3, tlDCbQ2c4,
      tlDCbQ2c5, tlDCbQ2c6, tlDSqP0c6, tlDSqP0c7, tlDSqP0c8, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlDCb_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c9 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDCbP3c0 f ξ + tlDCbP3c1 f ξ) + (tlDCbP3c2 f ξ + tlDCbP3c3 f ξ)) + ((tlDCbP3c4 f
        ξ + tlDCbP3c5 f ξ) + (tlDCbP3c6 f ξ + tlDCbP3c7 f ξ))) + ((tlDCbP3c8 f ξ +
        tlDCbP3c9 f ξ) + (tlDCbP3c10 f ξ + tlDCbP3c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlDCbQ3c0 f ξ) * hT + (tlDCbQ3c1 f ξ) * hT + (tlDCbQ3c2 f ξ) * hT + (tlDCbQ3c3 f ξ) * hT +
      (tlDCbQ3c4 f ξ) * hT
  simp only [tlD0, tlD1, tlDCbP3c0, tlDCbP3c1, tlDCbP3c10, tlDCbP3c11, tlDCbP3c2, tlDCbP3c3,
      tlDCbP3c4, tlDCbP3c5, tlDCbP3c6, tlDCbP3c7, tlDCbP3c8, tlDCbP3c9, tlDCbQ3c0,
      tlDCbQ3c1, tlDCbQ3c2, tlDCbQ3c3, tlDCbQ3c4, tlDSqP0c9, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlDCb_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f ξ +
      tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ + tlDSqP0c9 f ξ)) *
      (tlD0 f ξ + tlD1 f ξ) =
      (((((tlDCbP0c0 f ξ + tlDCbP0c1 f ξ) + (tlDCbP0c2 f ξ + tlDCbP0c3 f ξ)) + ((tlDCbP0c4
        f ξ + tlDCbP0c5 f ξ) + (tlDCbP0c6 f ξ + tlDCbP0c7 f ξ))) + (((tlDCbP0c8 f ξ +
        tlDCbP0c9 f ξ) + (tlDCbP1c0 f ξ + tlDCbP1c1 f ξ)) + ((tlDCbP1c2 f ξ + tlDCbP1c3 f
        ξ) + (tlDCbP1c4 f ξ + tlDCbP1c5 f ξ)))) + ((((tlDCbP1c6 f ξ + tlDCbP1c7 f ξ) +
        (tlDCbP1c8 f ξ + tlDCbP1c9 f ξ)) + ((tlDCbP1c10 f ξ + tlDCbP1c11 f ξ) +
        (tlDCbP1c12 f ξ + tlDCbP2c0 f ξ))) + (((tlDCbP2c1 f ξ + tlDCbP2c2 f ξ) +
        (tlDCbP2c3 f ξ + tlDCbP2c4 f ξ)) + ((tlDCbP2c5 f ξ + tlDCbP2c6 f ξ) + (tlDCbP2c7 f
        ξ + tlDCbP2c8 f ξ))))) + (((((tlDCbP2c9 f ξ + tlDCbP2c10 f ξ) + (tlDCbP2c11 f ξ +
        tlDCbP2c12 f ξ)) + ((tlDCbP2c13 f ξ + tlDCbP3c0 f ξ) + (tlDCbP3c1 f ξ + tlDCbP3c2
        f ξ))) + (((tlDCbP3c3 f ξ + tlDCbP3c4 f ξ) + (tlDCbP3c5 f ξ + tlDCbP3c6 f ξ)) +
        ((tlDCbP3c7 f ξ + tlDCbP3c8 f ξ) + (tlDCbP3c9 f ξ + tlDCbP3c10 f ξ)))) +
        tlDCbP3c11 f ξ) := by
  linear_combination
    ((tlDCb_s0 hT) + (tlDCb_s1 hT)) + ((tlDCb_s2 hT) + (tlDCb_s3 hT))


end MazurTorsion.Kubert
