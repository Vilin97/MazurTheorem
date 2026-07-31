/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Numerator-square identities for the order-twenty-seven certificate

The numerator-square coefficient identities, isolated to bound elaboration memory.
-/

namespace MazurTorsion.Kubert

lemma tlNSq_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4 f
        ξ + tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + tlNSqP0c8 f ξ := by
  linear_combination (norm := skip)
    (tlNSqQ0c0 f ξ) * hT + (tlNSqQ0c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNSqP0c0, tlNSqP0c1, tlNSqP0c2, tlNSqP0c3, tlNSqP0c4,
      tlNSqP0c5, tlNSqP0c6, tlNSqP0c7, tlNSqP0c8, tlNSqQ0c0, tlNSqQ0c1, tlT0, tlT1,
      tlT2, tlT3]
  ring1

lemma tlNSq_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP1c0 f ξ + tlNSqP1c1 f ξ) + (tlNSqP1c2 f ξ + tlNSqP1c3 f ξ)) + ((tlNSqP1c4 f
        ξ + tlNSqP1c5 f ξ) + (tlNSqP1c6 f ξ + tlNSqP1c7 f ξ))) + (tlNSqP1c8 f ξ +
        tlNSqP1c9 f ξ) := by
  linear_combination (norm := skip)
    (tlNSqQ1c0 f ξ) * hT + (tlNSqQ1c1 f ξ) * hT + (tlNSqQ1c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNSqP1c0, tlNSqP1c1, tlNSqP1c2, tlNSqP1c3, tlNSqP1c4,
      tlNSqP1c5, tlNSqP1c6, tlNSqP1c7, tlNSqP1c8, tlNSqP1c9, tlNSqQ1c0, tlNSqQ1c1,
      tlNSqQ1c2, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNSq_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP2c0 f ξ + tlNSqP2c1 f ξ) + (tlNSqP2c2 f ξ + tlNSqP2c3 f ξ)) + ((tlNSqP2c4 f
        ξ + tlNSqP2c5 f ξ) + (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ))) + ((tlNSqP2c8 f ξ +
        tlNSqP2c9 f ξ) + (tlNSqP2c10 f ξ + tlNSqP2c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlNSqQ2c0 f ξ) * hT + (tlNSqQ2c1 f ξ) * hT + (tlNSqQ2c2 f ξ) * hT + (tlNSqQ2c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNSqP2c0, tlNSqP2c1, tlNSqP2c10, tlNSqP2c11, tlNSqP2c2,
      tlNSqP2c3, tlNSqP2c4, tlNSqP2c5, tlNSqP2c6, tlNSqP2c7, tlNSqP2c8, tlNSqP2c9,
      tlNSqQ2c0, tlNSqQ2c1, tlNSqQ2c2, tlNSqQ2c3, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNSq_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlN3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNSqP3c0 f ξ + tlNSqP3c1 f ξ) + (tlNSqP3c2 f ξ + tlNSqP3c3 f ξ)) + ((tlNSqP3c4 f
        ξ + tlNSqP3c5 f ξ) + (tlNSqP3c6 f ξ + tlNSqP3c7 f ξ))) + ((tlNSqP3c8 f ξ +
        tlNSqP3c9 f ξ) + (tlNSqP3c10 f ξ + tlNSqP3c11 f ξ)) := by
  linear_combination (norm := skip)
    (tlNSqQ3c0 f ξ) * hT + (tlNSqQ3c1 f ξ) * hT + (tlNSqQ3c2 f ξ) * hT + (tlNSqQ3c3 f ξ) * hT +
      (tlNSqQ3c4 f ξ) * hT + (tlNSqQ3c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNSqP3c0, tlNSqP3c1, tlNSqP3c10, tlNSqP3c11, tlNSqP3c2,
      tlNSqP3c3, tlNSqP3c4, tlNSqP3c5, tlNSqP3c6, tlNSqP3c7, tlNSqP3c8, tlNSqP3c9,
      tlNSqQ3c0, tlNSqQ3c1, tlNSqQ3c2, tlNSqQ3c3, tlNSqQ3c4, tlNSqQ3c5, tlT0, tlT1,
      tlT2, tlT3]
  ring1

lemma tlNSq_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f
      ξ)) =
      (((((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4
        f ξ + tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + (((tlNSqP0c8 f ξ +
        tlNSqP1c0 f ξ) + (tlNSqP1c1 f ξ + tlNSqP1c2 f ξ)) + ((tlNSqP1c3 f ξ + tlNSqP1c4 f
        ξ) + (tlNSqP1c5 f ξ + tlNSqP1c6 f ξ)))) + ((((tlNSqP1c7 f ξ + tlNSqP1c8 f ξ) +
        (tlNSqP1c9 f ξ + tlNSqP2c0 f ξ)) + ((tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) + (tlNSqP2c3 f
        ξ + tlNSqP2c4 f ξ))) + (((tlNSqP2c5 f ξ + tlNSqP2c6 f ξ) + (tlNSqP2c7 f ξ +
        tlNSqP2c8 f ξ)) + ((tlNSqP2c9 f ξ + tlNSqP2c10 f ξ) + (tlNSqP2c11 f ξ + tlNSqP3c0
        f ξ))))) + ((((tlNSqP3c1 f ξ + tlNSqP3c2 f ξ) + (tlNSqP3c3 f ξ + tlNSqP3c4 f ξ)) +
        ((tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) + (tlNSqP3c7 f ξ + tlNSqP3c8 f ξ))) + ((tlNSqP3c9
        f ξ + tlNSqP3c10 f ξ) + tlNSqP3c11 f ξ)) := by
  linear_combination
    ((tlNSq_s0 hT) + (tlNSq_s1 hT)) + ((tlNSq_s2 hT) + (tlNSq_s3 hT))


end MazurTorsion.Kubert
