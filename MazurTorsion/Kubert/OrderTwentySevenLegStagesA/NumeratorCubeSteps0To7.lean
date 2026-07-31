/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Numerator-cube identities 0 through 7

The first independent numerator-cube coefficient identities.
-/

namespace MazurTorsion.Kubert

lemma tlNCb_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP0c0 f ξ + tlNCbP0c1 f ξ) + (tlNCbP0c2 f ξ + tlNCbP0c3 f ξ)) + ((tlNCbP0c4 f
        ξ + tlNCbP0c5 f ξ) + (tlNCbP0c6 f ξ + tlNCbP0c7 f ξ))) + ((tlNCbP0c8 f ξ +
        tlNCbP0c9 f ξ) + tlNCbP0c10 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ0c0 f ξ) * hT + (tlNCbQ0c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP0c0, tlNCbP0c1, tlNCbP0c10, tlNCbP0c2, tlNCbP0c3,
      tlNCbP0c4, tlNCbP0c5, tlNCbP0c6, tlNCbP0c7, tlNCbP0c8, tlNCbP0c9, tlNCbQ0c0,
      tlNCbQ0c1, tlNSqP0c0, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP1c0 f ξ + tlNCbP1c1 f ξ) + (tlNCbP1c2 f ξ + tlNCbP1c3 f ξ)) + ((tlNCbP1c4 f
        ξ + tlNCbP1c5 f ξ) + (tlNCbP1c6 f ξ + tlNCbP1c7 f ξ))) + (((tlNCbP1c8 f ξ +
        tlNCbP1c9 f ξ) + (tlNCbP1c10 f ξ + tlNCbP1c11 f ξ)) + tlNCbP1c12 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ1c0 f ξ) * hT + (tlNCbQ1c1 f ξ) * hT + (tlNCbQ1c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP1c0, tlNCbP1c1, tlNCbP1c10, tlNCbP1c11,
      tlNCbP1c12, tlNCbP1c2, tlNCbP1c3, tlNCbP1c4, tlNCbP1c5, tlNCbP1c6, tlNCbP1c7,
      tlNCbP1c8, tlNCbP1c9, tlNCbQ1c0, tlNCbQ1c1, tlNCbQ1c2, tlNSqP0c1, tlT0, tlT1,
      tlT2, tlT3]
  ring1

lemma tlNCb_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP2c0 f ξ + tlNCbP2c1 f ξ) + (tlNCbP2c2 f ξ + tlNCbP2c3 f ξ)) + ((tlNCbP2c4 f
        ξ + tlNCbP2c5 f ξ) + (tlNCbP2c6 f ξ + tlNCbP2c7 f ξ))) + (((tlNCbP2c8 f ξ +
        tlNCbP2c9 f ξ) + (tlNCbP2c10 f ξ + tlNCbP2c11 f ξ)) + ((tlNCbP2c12 f ξ +
        tlNCbP2c13 f ξ) + tlNCbP2c14 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ2c0 f ξ) * hT + (tlNCbQ2c1 f ξ) * hT + (tlNCbQ2c2 f ξ) * hT + (tlNCbQ2c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP2c0, tlNCbP2c1, tlNCbP2c10, tlNCbP2c11,
      tlNCbP2c12, tlNCbP2c13, tlNCbP2c14, tlNCbP2c2, tlNCbP2c3, tlNCbP2c4,
      tlNCbP2c5, tlNCbP2c6, tlNCbP2c7, tlNCbP2c8, tlNCbP2c9, tlNCbQ2c0, tlNCbQ2c1,
      tlNCbQ2c2, tlNCbQ2c3, tlNSqP0c2, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP3c0 f ξ + tlNCbP3c1 f ξ) + (tlNCbP3c2 f ξ + tlNCbP3c3 f ξ)) + ((tlNCbP3c4 f
        ξ + tlNCbP3c5 f ξ) + (tlNCbP3c6 f ξ + tlNCbP3c7 f ξ))) + (((tlNCbP3c8 f ξ +
        tlNCbP3c9 f ξ) + (tlNCbP3c10 f ξ + tlNCbP3c11 f ξ)) + ((tlNCbP3c12 f ξ +
        tlNCbP3c13 f ξ) + (tlNCbP3c14 f ξ + tlNCbP3c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlNCbQ3c0 f ξ) * hT + (tlNCbQ3c1 f ξ) * hT + (tlNCbQ3c2 f ξ) * hT + (tlNCbQ3c3 f ξ) * hT +
      (tlNCbQ3c4 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP3c0, tlNCbP3c1, tlNCbP3c10, tlNCbP3c11,
      tlNCbP3c12, tlNCbP3c13, tlNCbP3c14, tlNCbP3c15, tlNCbP3c2, tlNCbP3c3,
      tlNCbP3c4, tlNCbP3c5, tlNCbP3c6, tlNCbP3c7, tlNCbP3c8, tlNCbP3c9, tlNCbQ3c0,
      tlNCbQ3c1, tlNCbQ3c2, tlNCbQ3c3, tlNCbQ3c4, tlNSqP0c3, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP4c0 f ξ + tlNCbP4c1 f ξ) + (tlNCbP4c2 f ξ + tlNCbP4c3 f ξ)) + ((tlNCbP4c4
        f ξ + tlNCbP4c5 f ξ) + (tlNCbP4c6 f ξ + tlNCbP4c7 f ξ))) + (((tlNCbP4c8 f ξ +
        tlNCbP4c9 f ξ) + (tlNCbP4c10 f ξ + tlNCbP4c11 f ξ)) + ((tlNCbP4c12 f ξ +
        tlNCbP4c13 f ξ) + (tlNCbP4c14 f ξ + tlNCbP4c15 f ξ)))) + tlNCbP4c16 f ξ := by
  linear_combination (norm := skip)
    (tlNCbQ4c0 f ξ) * hT + (tlNCbQ4c1 f ξ) * hT + (tlNCbQ4c2 f ξ) * hT + (tlNCbQ4c3 f ξ) * hT +
      (tlNCbQ4c4 f ξ) * hT + (tlNCbQ4c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP4c0, tlNCbP4c1, tlNCbP4c10, tlNCbP4c11,
      tlNCbP4c12, tlNCbP4c13, tlNCbP4c14, tlNCbP4c15, tlNCbP4c16, tlNCbP4c2,
      tlNCbP4c3, tlNCbP4c4, tlNCbP4c5, tlNCbP4c6, tlNCbP4c7, tlNCbP4c8, tlNCbP4c9,
      tlNCbQ4c0, tlNCbQ4c1, tlNCbQ4c2, tlNCbQ4c3, tlNCbQ4c4, tlNCbQ4c5, tlNSqP0c4,
      tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP5c0 f ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f ξ + tlNCbP5c3 f ξ)) + ((tlNCbP5c4
        f ξ + tlNCbP5c5 f ξ) + (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ))) + (((tlNCbP5c8 f ξ +
        tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ + tlNCbP5c11 f ξ)) + ((tlNCbP5c12 f ξ +
        tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f ξ)))) + (tlNCbP5c16 f ξ +
        tlNCbP5c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ5c0 f ξ) * hT + (tlNCbQ5c1 f ξ) * hT + (tlNCbQ5c2 f ξ) * hT + (tlNCbQ5c3 f ξ) * hT +
      (tlNCbQ5c4 f ξ) * hT + (tlNCbQ5c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP5c0, tlNCbP5c1, tlNCbP5c10, tlNCbP5c11,
      tlNCbP5c12, tlNCbP5c13, tlNCbP5c14, tlNCbP5c15, tlNCbP5c16, tlNCbP5c17,
      tlNCbP5c2, tlNCbP5c3, tlNCbP5c4, tlNCbP5c5, tlNCbP5c6, tlNCbP5c7, tlNCbP5c8,
      tlNCbP5c9, tlNCbQ5c0, tlNCbQ5c1, tlNCbQ5c2, tlNCbQ5c3, tlNCbQ5c4, tlNCbQ5c5,
      tlNSqP0c5, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s6 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP6c0 f ξ + tlNCbP6c1 f ξ) + (tlNCbP6c2 f ξ + tlNCbP6c3 f ξ)) + ((tlNCbP6c4
        f ξ + tlNCbP6c5 f ξ) + (tlNCbP6c6 f ξ + tlNCbP6c7 f ξ))) + (((tlNCbP6c8 f ξ +
        tlNCbP6c9 f ξ) + (tlNCbP6c10 f ξ + tlNCbP6c11 f ξ)) + ((tlNCbP6c12 f ξ +
        tlNCbP6c13 f ξ) + (tlNCbP6c14 f ξ + tlNCbP6c15 f ξ)))) + (tlNCbP6c16 f ξ +
        tlNCbP6c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ6c0 f ξ) * hT + (tlNCbQ6c1 f ξ) * hT + (tlNCbQ6c2 f ξ) * hT + (tlNCbQ6c3 f ξ) * hT +
      (tlNCbQ6c4 f ξ) * hT + (tlNCbQ6c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP6c0, tlNCbP6c1, tlNCbP6c10, tlNCbP6c11,
      tlNCbP6c12, tlNCbP6c13, tlNCbP6c14, tlNCbP6c15, tlNCbP6c16, tlNCbP6c17,
      tlNCbP6c2, tlNCbP6c3, tlNCbP6c4, tlNCbP6c5, tlNCbP6c6, tlNCbP6c7, tlNCbP6c8,
      tlNCbP6c9, tlNCbQ6c0, tlNCbQ6c1, tlNCbQ6c2, tlNCbQ6c3, tlNCbQ6c4, tlNCbQ6c5,
      tlNSqP0c6, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP0c7 f ξ + tlNSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ) + (tlNCbP7c2 f ξ + tlNCbP7c3 f ξ)) + ((tlNCbP7c4
        f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ + tlNCbP7c7 f ξ))) + (((tlNCbP7c8 f ξ +
        tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ)) + ((tlNCbP7c12 f ξ +
        tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)))) + ((tlNCbP7c16 f ξ +
        tlNCbP7c17 f ξ) + tlNCbP7c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ7c0 f ξ) * hT + (tlNCbQ7c1 f ξ) * hT + (tlNCbQ7c2 f ξ) * hT + (tlNCbQ7c3 f ξ) * hT +
      (tlNCbQ7c4 f ξ) * hT + (tlNCbQ7c5 f ξ) * hT + (tlNCbQ7c6 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP7c0, tlNCbP7c1, tlNCbP7c10, tlNCbP7c11,
      tlNCbP7c12, tlNCbP7c13, tlNCbP7c14, tlNCbP7c15, tlNCbP7c16, tlNCbP7c17,
      tlNCbP7c18, tlNCbP7c2, tlNCbP7c3, tlNCbP7c4, tlNCbP7c5, tlNCbP7c6, tlNCbP7c7,
      tlNCbP7c8, tlNCbP7c9, tlNCbQ7c0, tlNCbQ7c1, tlNCbQ7c2, tlNCbQ7c3, tlNCbQ7c4,
      tlNCbQ7c5, tlNCbQ7c6, tlNSqP0c7, tlNSqP0c8, tlT0, tlT1, tlT2, tlT3]
  ring1


end MazurTorsion.Kubert
