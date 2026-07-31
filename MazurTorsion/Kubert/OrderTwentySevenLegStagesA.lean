/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Trisection-side staged products

Staged products of the trisection-side certificate chain: powers of the
pushforward numerator and denominator reduced against the trisection
polynomial.
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

lemma tlNCb_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP8c0 f ξ + tlNCbP8c1 f ξ) + (tlNCbP8c2 f ξ + tlNCbP8c3 f ξ)) + ((tlNCbP8c4 f
        ξ + tlNCbP8c5 f ξ) + (tlNCbP8c6 f ξ + tlNCbP8c7 f ξ))) + ((tlNCbP8c8 f ξ +
        tlNCbP8c9 f ξ) + tlNCbP8c10 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ8c0 f ξ) * hT + (tlNCbQ8c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP8c0, tlNCbP8c1, tlNCbP8c10, tlNCbP8c2, tlNCbP8c3,
      tlNCbP8c4, tlNCbP8c5, tlNCbP8c6, tlNCbP8c7, tlNCbP8c8, tlNCbP8c9, tlNCbQ8c0,
      tlNCbQ8c1, tlNSqP1c0, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP9c0 f ξ + tlNCbP9c1 f ξ) + (tlNCbP9c2 f ξ + tlNCbP9c3 f ξ)) + ((tlNCbP9c4 f
        ξ + tlNCbP9c5 f ξ) + (tlNCbP9c6 f ξ + tlNCbP9c7 f ξ))) + (((tlNCbP9c8 f ξ +
        tlNCbP9c9 f ξ) + (tlNCbP9c10 f ξ + tlNCbP9c11 f ξ)) + tlNCbP9c12 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ9c0 f ξ) * hT + (tlNCbQ9c1 f ξ) * hT + (tlNCbQ9c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP9c0, tlNCbP9c1, tlNCbP9c10, tlNCbP9c11,
      tlNCbP9c12, tlNCbP9c2, tlNCbP9c3, tlNCbP9c4, tlNCbP9c5, tlNCbP9c6, tlNCbP9c7,
      tlNCbP9c8, tlNCbP9c9, tlNCbQ9c0, tlNCbQ9c1, tlNCbQ9c2, tlNSqP1c1, tlT0, tlT1,
      tlT2, tlT3]
  ring1

lemma tlNCb_s10 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP10c0 f ξ + tlNCbP10c1 f ξ) + (tlNCbP10c2 f ξ + tlNCbP10c3 f ξ)) +
        ((tlNCbP10c4 f ξ + tlNCbP10c5 f ξ) + (tlNCbP10c6 f ξ + tlNCbP10c7 f ξ))) +
        (((tlNCbP10c8 f ξ + tlNCbP10c9 f ξ) + (tlNCbP10c10 f ξ + tlNCbP10c11 f ξ)) +
        (tlNCbP10c12 f ξ + tlNCbP10c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ10c0 f ξ) * hT + (tlNCbQ10c1 f ξ) * hT + (tlNCbQ10c2 f ξ) * hT + (tlNCbQ10c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP10c0, tlNCbP10c1, tlNCbP10c10, tlNCbP10c11,
      tlNCbP10c12, tlNCbP10c13, tlNCbP10c2, tlNCbP10c3, tlNCbP10c4, tlNCbP10c5,
      tlNCbP10c6, tlNCbP10c7, tlNCbP10c8, tlNCbP10c9, tlNCbQ10c0, tlNCbQ10c1,
      tlNCbQ10c2, tlNCbQ10c3, tlNSqP1c2, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s11 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP11c0 f ξ + tlNCbP11c1 f ξ) + (tlNCbP11c2 f ξ + tlNCbP11c3 f ξ)) +
        ((tlNCbP11c4 f ξ + tlNCbP11c5 f ξ) + (tlNCbP11c6 f ξ + tlNCbP11c7 f ξ))) +
        (((tlNCbP11c8 f ξ + tlNCbP11c9 f ξ) + (tlNCbP11c10 f ξ + tlNCbP11c11 f ξ)) +
        ((tlNCbP11c12 f ξ + tlNCbP11c13 f ξ) + tlNCbP11c14 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ11c0 f ξ) * hT + (tlNCbQ11c1 f ξ) * hT + (tlNCbQ11c2 f ξ) * hT + (tlNCbQ11c3 f ξ) * hT
      + (tlNCbQ11c4 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP11c0, tlNCbP11c1, tlNCbP11c10, tlNCbP11c11,
      tlNCbP11c12, tlNCbP11c13, tlNCbP11c14, tlNCbP11c2, tlNCbP11c3, tlNCbP11c4,
      tlNCbP11c5, tlNCbP11c6, tlNCbP11c7, tlNCbP11c8, tlNCbP11c9, tlNCbQ11c0,
      tlNCbQ11c1, tlNCbQ11c2, tlNCbQ11c3, tlNCbQ11c4, tlNSqP1c3, tlT0, tlT1, tlT2,
      tlT3]
  ring1

lemma tlNCb_s12 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP12c0 f ξ + tlNCbP12c1 f ξ) + (tlNCbP12c2 f ξ + tlNCbP12c3 f ξ)) +
        ((tlNCbP12c4 f ξ + tlNCbP12c5 f ξ) + (tlNCbP12c6 f ξ + tlNCbP12c7 f ξ))) +
        (((tlNCbP12c8 f ξ + tlNCbP12c9 f ξ) + (tlNCbP12c10 f ξ + tlNCbP12c11 f ξ)) +
        ((tlNCbP12c12 f ξ + tlNCbP12c13 f ξ) + (tlNCbP12c14 f ξ + tlNCbP12c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlNCbQ12c0 f ξ) * hT + (tlNCbQ12c1 f ξ) * hT + (tlNCbQ12c2 f ξ) * hT + (tlNCbQ12c3 f ξ) * hT
      + (tlNCbQ12c4 f ξ) * hT + (tlNCbQ12c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP12c0, tlNCbP12c1, tlNCbP12c10, tlNCbP12c11,
      tlNCbP12c12, tlNCbP12c13, tlNCbP12c14, tlNCbP12c15, tlNCbP12c2, tlNCbP12c3,
      tlNCbP12c4, tlNCbP12c5, tlNCbP12c6, tlNCbP12c7, tlNCbP12c8, tlNCbP12c9,
      tlNCbQ12c0, tlNCbQ12c1, tlNCbQ12c2, tlNCbQ12c3, tlNCbQ12c4, tlNCbQ12c5,
      tlNSqP1c4, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s13 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP13c0 f ξ + tlNCbP13c1 f ξ) + (tlNCbP13c2 f ξ + tlNCbP13c3 f ξ)) +
        ((tlNCbP13c4 f ξ + tlNCbP13c5 f ξ) + (tlNCbP13c6 f ξ + tlNCbP13c7 f ξ))) +
        (((tlNCbP13c8 f ξ + tlNCbP13c9 f ξ) + (tlNCbP13c10 f ξ + tlNCbP13c11 f ξ)) +
        ((tlNCbP13c12 f ξ + tlNCbP13c13 f ξ) + (tlNCbP13c14 f ξ + tlNCbP13c15 f ξ)))) +
        (tlNCbP13c16 f ξ + tlNCbP13c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ13c0 f ξ) * hT + (tlNCbQ13c1 f ξ) * hT + (tlNCbQ13c2 f ξ) * hT + (tlNCbQ13c3 f ξ) * hT
      + (tlNCbQ13c4 f ξ) * hT + (tlNCbQ13c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP13c0, tlNCbP13c1, tlNCbP13c10, tlNCbP13c11,
      tlNCbP13c12, tlNCbP13c13, tlNCbP13c14, tlNCbP13c15, tlNCbP13c16, tlNCbP13c17,
      tlNCbP13c2, tlNCbP13c3, tlNCbP13c4, tlNCbP13c5, tlNCbP13c6, tlNCbP13c7,
      tlNCbP13c8, tlNCbP13c9, tlNCbQ13c0, tlNCbQ13c1, tlNCbQ13c2, tlNCbQ13c3,
      tlNCbQ13c4, tlNCbQ13c5, tlNSqP1c5, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s14 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP14c0 f ξ + tlNCbP14c1 f ξ) + (tlNCbP14c2 f ξ + tlNCbP14c3 f ξ)) +
        ((tlNCbP14c4 f ξ + tlNCbP14c5 f ξ) + (tlNCbP14c6 f ξ + tlNCbP14c7 f ξ))) +
        (((tlNCbP14c8 f ξ + tlNCbP14c9 f ξ) + (tlNCbP14c10 f ξ + tlNCbP14c11 f ξ)) +
        ((tlNCbP14c12 f ξ + tlNCbP14c13 f ξ) + (tlNCbP14c14 f ξ + tlNCbP14c15 f ξ)))) +
        (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ14c0 f ξ) * hT + (tlNCbQ14c1 f ξ) * hT + (tlNCbQ14c2 f ξ) * hT + (tlNCbQ14c3 f ξ) * hT
      + (tlNCbQ14c4 f ξ) * hT + (tlNCbQ14c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP14c0, tlNCbP14c1, tlNCbP14c10, tlNCbP14c11,
      tlNCbP14c12, tlNCbP14c13, tlNCbP14c14, tlNCbP14c15, tlNCbP14c16, tlNCbP14c17,
      tlNCbP14c2, tlNCbP14c3, tlNCbP14c4, tlNCbP14c5, tlNCbP14c6, tlNCbP14c7,
      tlNCbP14c8, tlNCbP14c9, tlNCbQ14c0, tlNCbQ14c1, tlNCbQ14c2, tlNCbQ14c3,
      tlNCbQ14c4, tlNCbQ14c5, tlNSqP1c6, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s15 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP15c0 f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) +
        ((tlNCbP15c4 f ξ + tlNCbP15c5 f ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ))) +
        (((tlNCbP15c8 f ξ + tlNCbP15c9 f ξ) + (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) +
        ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) + (tlNCbP15c14 f ξ + tlNCbP15c15 f ξ)))) +
        ((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) + tlNCbP15c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ15c0 f ξ) * hT + (tlNCbQ15c1 f ξ) * hT + (tlNCbQ15c2 f ξ) * hT + (tlNCbQ15c3 f ξ) * hT
      + (tlNCbQ15c4 f ξ) * hT + (tlNCbQ15c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP15c0, tlNCbP15c1, tlNCbP15c10, tlNCbP15c11,
      tlNCbP15c12, tlNCbP15c13, tlNCbP15c14, tlNCbP15c15, tlNCbP15c16, tlNCbP15c17,
      tlNCbP15c18, tlNCbP15c2, tlNCbP15c3, tlNCbP15c4, tlNCbP15c5, tlNCbP15c6,
      tlNCbP15c7, tlNCbP15c8, tlNCbP15c9, tlNCbQ15c0, tlNCbQ15c1, tlNCbQ15c2,
      tlNCbQ15c3, tlNCbQ15c4, tlNCbQ15c5, tlNSqP1c7, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s16 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP16c0 f ξ + tlNCbP16c1 f ξ) + (tlNCbP16c2 f ξ + tlNCbP16c3 f ξ)) +
        ((tlNCbP16c4 f ξ + tlNCbP16c5 f ξ) + (tlNCbP16c6 f ξ + tlNCbP16c7 f ξ))) +
        (((tlNCbP16c8 f ξ + tlNCbP16c9 f ξ) + (tlNCbP16c10 f ξ + tlNCbP16c11 f ξ)) +
        ((tlNCbP16c12 f ξ + tlNCbP16c13 f ξ) + (tlNCbP16c14 f ξ + tlNCbP16c15 f ξ)))) +
        ((tlNCbP16c16 f ξ + tlNCbP16c17 f ξ) + tlNCbP16c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ16c0 f ξ) * hT + (tlNCbQ16c1 f ξ) * hT + (tlNCbQ16c2 f ξ) * hT + (tlNCbQ16c3 f ξ) * hT
      + (tlNCbQ16c4 f ξ) * hT + (tlNCbQ16c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP16c0, tlNCbP16c1, tlNCbP16c10, tlNCbP16c11,
      tlNCbP16c12, tlNCbP16c13, tlNCbP16c14, tlNCbP16c15, tlNCbP16c16, tlNCbP16c17,
      tlNCbP16c18, tlNCbP16c2, tlNCbP16c3, tlNCbP16c4, tlNCbP16c5, tlNCbP16c6,
      tlNCbP16c7, tlNCbP16c8, tlNCbP16c9, tlNCbQ16c0, tlNCbQ16c1, tlNCbQ16c2,
      tlNCbQ16c3, tlNCbQ16c4, tlNCbQ16c5, tlNSqP1c8, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s17 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP1c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP17c0 f ξ + tlNCbP17c1 f ξ) + (tlNCbP17c2 f ξ + tlNCbP17c3 f ξ)) +
        ((tlNCbP17c4 f ξ + tlNCbP17c5 f ξ) + (tlNCbP17c6 f ξ + tlNCbP17c7 f ξ))) +
        (((tlNCbP17c8 f ξ + tlNCbP17c9 f ξ) + (tlNCbP17c10 f ξ + tlNCbP17c11 f ξ)) +
        ((tlNCbP17c12 f ξ + tlNCbP17c13 f ξ) + (tlNCbP17c14 f ξ + tlNCbP17c15 f ξ)))) +
        ((tlNCbP17c16 f ξ + tlNCbP17c17 f ξ) + tlNCbP17c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ17c0 f ξ) * hT + (tlNCbQ17c1 f ξ) * hT + (tlNCbQ17c2 f ξ) * hT + (tlNCbQ17c3 f ξ) * hT
      + (tlNCbQ17c4 f ξ) * hT + (tlNCbQ17c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP17c0, tlNCbP17c1, tlNCbP17c10, tlNCbP17c11,
      tlNCbP17c12, tlNCbP17c13, tlNCbP17c14, tlNCbP17c15, tlNCbP17c16, tlNCbP17c17,
      tlNCbP17c18, tlNCbP17c2, tlNCbP17c3, tlNCbP17c4, tlNCbP17c5, tlNCbP17c6,
      tlNCbP17c7, tlNCbP17c8, tlNCbP17c9, tlNCbQ17c0, tlNCbQ17c1, tlNCbQ17c2,
      tlNCbQ17c3, tlNCbQ17c4, tlNCbQ17c5, tlNSqP1c9, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s18 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP18c0 f ξ + tlNCbP18c1 f ξ) + (tlNCbP18c2 f ξ + tlNCbP18c3 f ξ)) +
        ((tlNCbP18c4 f ξ + tlNCbP18c5 f ξ) + (tlNCbP18c6 f ξ + tlNCbP18c7 f ξ))) +
        ((tlNCbP18c8 f ξ + tlNCbP18c9 f ξ) + tlNCbP18c10 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ18c0 f ξ) * hT + (tlNCbQ18c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP18c0, tlNCbP18c1, tlNCbP18c10, tlNCbP18c2,
      tlNCbP18c3, tlNCbP18c4, tlNCbP18c5, tlNCbP18c6, tlNCbP18c7, tlNCbP18c8,
      tlNCbP18c9, tlNCbQ18c0, tlNCbQ18c1, tlNSqP2c0, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s19 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP19c0 f ξ + tlNCbP19c1 f ξ) + (tlNCbP19c2 f ξ + tlNCbP19c3 f ξ)) +
        ((tlNCbP19c4 f ξ + tlNCbP19c5 f ξ) + (tlNCbP19c6 f ξ + tlNCbP19c7 f ξ))) +
        (((tlNCbP19c8 f ξ + tlNCbP19c9 f ξ) + (tlNCbP19c10 f ξ + tlNCbP19c11 f ξ)) +
        tlNCbP19c12 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ19c0 f ξ) * hT + (tlNCbQ19c1 f ξ) * hT + (tlNCbQ19c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP19c0, tlNCbP19c1, tlNCbP19c10, tlNCbP19c11,
      tlNCbP19c12, tlNCbP19c2, tlNCbP19c3, tlNCbP19c4, tlNCbP19c5, tlNCbP19c6,
      tlNCbP19c7, tlNCbP19c8, tlNCbP19c9, tlNCbQ19c0, tlNCbQ19c1, tlNCbQ19c2,
      tlNSqP2c1, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s20 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP20c0 f ξ + tlNCbP20c1 f ξ) + (tlNCbP20c2 f ξ + tlNCbP20c3 f ξ)) +
        ((tlNCbP20c4 f ξ + tlNCbP20c5 f ξ) + (tlNCbP20c6 f ξ + tlNCbP20c7 f ξ))) +
        (((tlNCbP20c8 f ξ + tlNCbP20c9 f ξ) + (tlNCbP20c10 f ξ + tlNCbP20c11 f ξ)) +
        (tlNCbP20c12 f ξ + tlNCbP20c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ20c0 f ξ) * hT + (tlNCbQ20c1 f ξ) * hT + (tlNCbQ20c2 f ξ) * hT + (tlNCbQ20c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP20c0, tlNCbP20c1, tlNCbP20c10, tlNCbP20c11,
      tlNCbP20c12, tlNCbP20c13, tlNCbP20c2, tlNCbP20c3, tlNCbP20c4, tlNCbP20c5,
      tlNCbP20c6, tlNCbP20c7, tlNCbP20c8, tlNCbP20c9, tlNCbQ20c0, tlNCbQ20c1,
      tlNCbQ20c2, tlNCbQ20c3, tlNSqP2c2, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s21 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c3 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP21c0 f ξ + tlNCbP21c1 f ξ) + (tlNCbP21c2 f ξ + tlNCbP21c3 f ξ)) +
        ((tlNCbP21c4 f ξ + tlNCbP21c5 f ξ) + (tlNCbP21c6 f ξ + tlNCbP21c7 f ξ))) +
        (((tlNCbP21c8 f ξ + tlNCbP21c9 f ξ) + (tlNCbP21c10 f ξ + tlNCbP21c11 f ξ)) +
        ((tlNCbP21c12 f ξ + tlNCbP21c13 f ξ) + tlNCbP21c14 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ21c0 f ξ) * hT + (tlNCbQ21c1 f ξ) * hT + (tlNCbQ21c2 f ξ) * hT + (tlNCbQ21c3 f ξ) * hT
      + (tlNCbQ21c4 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP21c0, tlNCbP21c1, tlNCbP21c10, tlNCbP21c11,
      tlNCbP21c12, tlNCbP21c13, tlNCbP21c14, tlNCbP21c2, tlNCbP21c3, tlNCbP21c4,
      tlNCbP21c5, tlNCbP21c6, tlNCbP21c7, tlNCbP21c8, tlNCbP21c9, tlNCbQ21c0,
      tlNCbQ21c1, tlNCbQ21c2, tlNCbQ21c3, tlNCbQ21c4, tlNSqP2c3, tlT0, tlT1, tlT2,
      tlT3]
  ring1

lemma tlNCb_s22 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c4 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP22c0 f ξ + tlNCbP22c1 f ξ) + (tlNCbP22c2 f ξ + tlNCbP22c3 f ξ)) +
        ((tlNCbP22c4 f ξ + tlNCbP22c5 f ξ) + (tlNCbP22c6 f ξ + tlNCbP22c7 f ξ))) +
        (((tlNCbP22c8 f ξ + tlNCbP22c9 f ξ) + (tlNCbP22c10 f ξ + tlNCbP22c11 f ξ)) +
        ((tlNCbP22c12 f ξ + tlNCbP22c13 f ξ) + (tlNCbP22c14 f ξ + tlNCbP22c15 f ξ))) := by
  linear_combination (norm := skip)
    (tlNCbQ22c0 f ξ) * hT + (tlNCbQ22c1 f ξ) * hT + (tlNCbQ22c2 f ξ) * hT + (tlNCbQ22c3 f ξ) * hT
      + (tlNCbQ22c4 f ξ) * hT + (tlNCbQ22c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP22c0, tlNCbP22c1, tlNCbP22c10, tlNCbP22c11,
      tlNCbP22c12, tlNCbP22c13, tlNCbP22c14, tlNCbP22c15, tlNCbP22c2, tlNCbP22c3,
      tlNCbP22c4, tlNCbP22c5, tlNCbP22c6, tlNCbP22c7, tlNCbP22c8, tlNCbP22c9,
      tlNCbQ22c0, tlNCbQ22c1, tlNCbQ22c2, tlNCbQ22c3, tlNCbQ22c4, tlNCbQ22c5,
      tlNSqP2c4, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s23 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP23c0 f ξ + tlNCbP23c1 f ξ) + (tlNCbP23c2 f ξ + tlNCbP23c3 f ξ)) +
        ((tlNCbP23c4 f ξ + tlNCbP23c5 f ξ) + (tlNCbP23c6 f ξ + tlNCbP23c7 f ξ))) +
        (((tlNCbP23c8 f ξ + tlNCbP23c9 f ξ) + (tlNCbP23c10 f ξ + tlNCbP23c11 f ξ)) +
        ((tlNCbP23c12 f ξ + tlNCbP23c13 f ξ) + (tlNCbP23c14 f ξ + tlNCbP23c15 f ξ)))) +
        tlNCbP23c16 f ξ := by
  linear_combination (norm := skip)
    (tlNCbQ23c0 f ξ) * hT + (tlNCbQ23c1 f ξ) * hT + (tlNCbQ23c2 f ξ) * hT + (tlNCbQ23c3 f ξ) * hT
      + (tlNCbQ23c4 f ξ) * hT + (tlNCbQ23c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP23c0, tlNCbP23c1, tlNCbP23c10, tlNCbP23c11,
      tlNCbP23c12, tlNCbP23c13, tlNCbP23c14, tlNCbP23c15, tlNCbP23c16, tlNCbP23c2,
      tlNCbP23c3, tlNCbP23c4, tlNCbP23c5, tlNCbP23c6, tlNCbP23c7, tlNCbP23c8,
      tlNCbP23c9, tlNCbQ23c0, tlNCbQ23c1, tlNCbQ23c2, tlNCbQ23c3, tlNCbQ23c4,
      tlNCbQ23c5, tlNSqP2c5, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s24 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP24c0 f ξ + tlNCbP24c1 f ξ) + (tlNCbP24c2 f ξ + tlNCbP24c3 f ξ)) +
        ((tlNCbP24c4 f ξ + tlNCbP24c5 f ξ) + (tlNCbP24c6 f ξ + tlNCbP24c7 f ξ))) +
        (((tlNCbP24c8 f ξ + tlNCbP24c9 f ξ) + (tlNCbP24c10 f ξ + tlNCbP24c11 f ξ)) +
        ((tlNCbP24c12 f ξ + tlNCbP24c13 f ξ) + (tlNCbP24c14 f ξ + tlNCbP24c15 f ξ)))) +
        (tlNCbP24c16 f ξ + tlNCbP24c17 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ24c0 f ξ) * hT + (tlNCbQ24c1 f ξ) * hT + (tlNCbQ24c2 f ξ) * hT + (tlNCbQ24c3 f ξ) * hT
      + (tlNCbQ24c4 f ξ) * hT + (tlNCbQ24c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP24c0, tlNCbP24c1, tlNCbP24c10, tlNCbP24c11,
      tlNCbP24c12, tlNCbP24c13, tlNCbP24c14, tlNCbP24c15, tlNCbP24c16, tlNCbP24c17,
      tlNCbP24c2, tlNCbP24c3, tlNCbP24c4, tlNCbP24c5, tlNCbP24c6, tlNCbP24c7,
      tlNCbP24c8, tlNCbP24c9, tlNCbQ24c0, tlNCbQ24c1, tlNCbQ24c2, tlNCbQ24c3,
      tlNCbQ24c4, tlNCbQ24c5, tlNSqP2c6, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s25 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP25c0 f + tlNCbP25c1 f ξ) + (tlNCbP25c2 f ξ + tlNCbP25c3 f ξ)) +
        ((tlNCbP25c4 f ξ + tlNCbP25c5 f ξ) + (tlNCbP25c6 f ξ + tlNCbP25c7 f ξ))) +
        (((tlNCbP25c8 f ξ + tlNCbP25c9 f ξ) + (tlNCbP25c10 f ξ + tlNCbP25c11 f ξ)) +
        ((tlNCbP25c12 f ξ + tlNCbP25c13 f ξ) + (tlNCbP25c14 f ξ + tlNCbP25c15 f ξ)))) +
        ((tlNCbP25c16 f ξ + tlNCbP25c17 f ξ) + tlNCbP25c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ25c0 f ξ) * hT + (tlNCbQ25c1 f ξ) * hT + (tlNCbQ25c2 f ξ) * hT + (tlNCbQ25c3 f ξ) * hT
      + (tlNCbQ25c4 f ξ) * hT + (tlNCbQ25c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP25c0, tlNCbP25c1, tlNCbP25c10, tlNCbP25c11,
      tlNCbP25c12, tlNCbP25c13, tlNCbP25c14, tlNCbP25c15, tlNCbP25c16, tlNCbP25c17,
      tlNCbP25c18, tlNCbP25c2, tlNCbP25c3, tlNCbP25c4, tlNCbP25c5, tlNCbP25c6,
      tlNCbP25c7, tlNCbP25c8, tlNCbP25c9, tlNCbQ25c0, tlNCbQ25c1, tlNCbQ25c2,
      tlNCbQ25c3, tlNCbQ25c4, tlNCbQ25c5, tlNSqP2c7, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s26 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3 f ξ)) +
        ((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ))) +
        (((tlNCbP26c8 f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ)) +
        ((tlNCbP26c12 f ξ + tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)))) +
        ((tlNCbP26c16 f ξ + tlNCbP26c17 f ξ) + tlNCbP26c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ26c0 f ξ) * hT + (tlNCbQ26c1 f ξ) * hT + (tlNCbQ26c2 f ξ) * hT + (tlNCbQ26c3 f ξ) * hT
      + (tlNCbQ26c4 f ξ) * hT + (tlNCbQ26c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP26c0, tlNCbP26c1, tlNCbP26c10, tlNCbP26c11,
      tlNCbP26c12, tlNCbP26c13, tlNCbP26c14, tlNCbP26c15, tlNCbP26c16, tlNCbP26c17,
      tlNCbP26c18, tlNCbP26c2, tlNCbP26c3, tlNCbP26c4, tlNCbP26c5, tlNCbP26c6,
      tlNCbP26c7, tlNCbP26c8, tlNCbP26c9, tlNCbQ26c0, tlNCbQ26c1, tlNCbQ26c2,
      tlNCbQ26c3, tlNCbQ26c4, tlNCbQ26c5, tlNSqP2c8, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s27 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP27c0 f ξ + tlNCbP27c1 f ξ) + (tlNCbP27c2 f ξ + tlNCbP27c3 f ξ)) +
        ((tlNCbP27c4 f ξ + tlNCbP27c5 f ξ) + (tlNCbP27c6 f ξ + tlNCbP27c7 f ξ))) +
        (((tlNCbP27c8 f ξ + tlNCbP27c9 f ξ) + (tlNCbP27c10 f ξ + tlNCbP27c11 f ξ)) +
        ((tlNCbP27c12 f ξ + tlNCbP27c13 f ξ) + (tlNCbP27c14 f ξ + tlNCbP27c15 f ξ)))) +
        ((tlNCbP27c16 f ξ + tlNCbP27c17 f ξ) + tlNCbP27c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ27c0 f ξ) * hT + (tlNCbQ27c1 f ξ) * hT + (tlNCbQ27c2 f ξ) * hT + (tlNCbQ27c3 f ξ) * hT
      + (tlNCbQ27c4 f ξ) * hT + (tlNCbQ27c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP27c0, tlNCbP27c1, tlNCbP27c10, tlNCbP27c11,
      tlNCbP27c12, tlNCbP27c13, tlNCbP27c14, tlNCbP27c15, tlNCbP27c16, tlNCbP27c17,
      tlNCbP27c18, tlNCbP27c2, tlNCbP27c3, tlNCbP27c4, tlNCbP27c5, tlNCbP27c6,
      tlNCbP27c7, tlNCbP27c8, tlNCbP27c9, tlNCbQ27c0, tlNCbQ27c1, tlNCbQ27c2,
      tlNCbQ27c3, tlNCbQ27c4, tlNCbQ27c5, tlNSqP2c9, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s28 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c10 f ξ + tlNSqP2c11 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP28c0 f ξ + tlNCbP28c1 f ξ) + (tlNCbP28c2 f ξ + tlNCbP28c3 f ξ)) +
        ((tlNCbP28c4 f ξ + tlNCbP28c5 f ξ) + (tlNCbP28c6 f ξ + tlNCbP28c7 f ξ))) +
        (((tlNCbP28c8 f ξ + tlNCbP28c9 f ξ) + (tlNCbP28c10 f ξ + tlNCbP28c11 f ξ)) +
        ((tlNCbP28c12 f ξ + tlNCbP28c13 f ξ) + (tlNCbP28c14 f ξ + tlNCbP28c15 f ξ)))) +
        ((tlNCbP28c16 f ξ + tlNCbP28c17 f ξ) + tlNCbP28c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ28c0 f ξ) * hT + (tlNCbQ28c1 f ξ) * hT + (tlNCbQ28c2 f ξ) * hT + (tlNCbQ28c3 f ξ) * hT
      + (tlNCbQ28c4 f ξ) * hT + (tlNCbQ28c5 f ξ) * hT + (tlNCbQ28c6 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP28c0, tlNCbP28c1, tlNCbP28c10, tlNCbP28c11,
      tlNCbP28c12, tlNCbP28c13, tlNCbP28c14, tlNCbP28c15, tlNCbP28c16, tlNCbP28c17,
      tlNCbP28c18, tlNCbP28c2, tlNCbP28c3, tlNCbP28c4, tlNCbP28c5, tlNCbP28c6,
      tlNCbP28c7, tlNCbP28c8, tlNCbP28c9, tlNCbQ28c0, tlNCbQ28c1, tlNCbQ28c2,
      tlNCbQ28c3, tlNCbQ28c4, tlNCbQ28c5, tlNCbQ28c6, tlNSqP2c10, tlNSqP2c11, tlT0,
      tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s29 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c0 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP29c0 f ξ + tlNCbP29c1 f ξ) + (tlNCbP29c2 f ξ + tlNCbP29c3 f ξ)) +
        ((tlNCbP29c4 f ξ + tlNCbP29c5 f ξ) + (tlNCbP29c6 f ξ + tlNCbP29c7 f ξ))) +
        ((tlNCbP29c8 f ξ + tlNCbP29c9 f ξ) + tlNCbP29c10 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ29c0 f ξ) * hT + (tlNCbQ29c1 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP29c0, tlNCbP29c1, tlNCbP29c10, tlNCbP29c2,
      tlNCbP29c3, tlNCbP29c4, tlNCbP29c5, tlNCbP29c6, tlNCbP29c7, tlNCbP29c8,
      tlNCbP29c9, tlNCbQ29c0, tlNCbQ29c1, tlNSqP3c0, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s30 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c1 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ + tlNCbP30c3 f ξ)) +
        ((tlNCbP30c4 f ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f ξ))) +
        (((tlNCbP30c8 f ξ + tlNCbP30c9 f ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) +
        tlNCbP30c12 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ30c0 f ξ) * hT + (tlNCbQ30c1 f ξ) * hT + (tlNCbQ30c2 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP30c0, tlNCbP30c1, tlNCbP30c10, tlNCbP30c11,
      tlNCbP30c12, tlNCbP30c2, tlNCbP30c3, tlNCbP30c4, tlNCbP30c5, tlNCbP30c6,
      tlNCbP30c7, tlNCbP30c8, tlNCbP30c9, tlNCbQ30c0, tlNCbQ30c1, tlNCbQ30c2,
      tlNSqP3c1, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s31 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c2 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlNCbP31c0 f ξ + tlNCbP31c1 f ξ) + (tlNCbP31c2 f ξ + tlNCbP31c3 f ξ)) +
        ((tlNCbP31c4 f ξ + tlNCbP31c5 f ξ) + (tlNCbP31c6 f ξ + tlNCbP31c7 f ξ))) +
        (((tlNCbP31c8 f ξ + tlNCbP31c9 f ξ) + (tlNCbP31c10 f ξ + tlNCbP31c11 f ξ)) +
        (tlNCbP31c12 f ξ + tlNCbP31c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlNCbQ31c0 f ξ) * hT + (tlNCbQ31c1 f ξ) * hT + (tlNCbQ31c2 f ξ) * hT + (tlNCbQ31c3 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP31c0, tlNCbP31c1, tlNCbP31c10, tlNCbP31c11,
      tlNCbP31c12, tlNCbP31c13, tlNCbP31c2, tlNCbP31c3, tlNCbP31c4, tlNCbP31c5,
      tlNCbP31c6, tlNCbP31c7, tlNCbP31c8, tlNCbP31c9, tlNCbQ31c0, tlNCbQ31c1,
      tlNCbQ31c2, tlNCbQ31c3, tlNSqP3c2, tlT0, tlT1, tlT2, tlT3]
  ring1

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

lemma tlNCb_s36 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) +
        ((tlNCbP36c4 f ξ + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) +
        (((tlNCbP36c8 f ξ + tlNCbP36c9 f ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) +
        ((tlNCbP36c12 f ξ + tlNCbP36c13 f ξ) + (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) +
        ((tlNCbP36c16 f ξ + tlNCbP36c17 f ξ) + tlNCbP36c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ36c0 f ξ) * hT + (tlNCbQ36c1 f ξ) * hT + (tlNCbQ36c2 f ξ) * hT + (tlNCbQ36c3 f ξ) * hT
      + (tlNCbQ36c4 f ξ) * hT + (tlNCbQ36c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP36c0, tlNCbP36c1, tlNCbP36c10, tlNCbP36c11,
      tlNCbP36c12, tlNCbP36c13, tlNCbP36c14, tlNCbP36c15, tlNCbP36c16, tlNCbP36c17,
      tlNCbP36c18, tlNCbP36c2, tlNCbP36c3, tlNCbP36c4, tlNCbP36c5, tlNCbP36c6,
      tlNCbP36c7, tlNCbP36c8, tlNCbP36c9, tlNCbQ36c0, tlNCbQ36c1, tlNCbQ36c2,
      tlNCbQ36c3, tlNCbQ36c4, tlNCbQ36c5, tlNSqP3c7, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s37 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP37c0 f + tlNCbP37c1 f ξ) + (tlNCbP37c2 f ξ + tlNCbP37c3 f ξ)) +
        ((tlNCbP37c4 f ξ + tlNCbP37c5 f ξ) + (tlNCbP37c6 f ξ + tlNCbP37c7 f ξ))) +
        (((tlNCbP37c8 f ξ + tlNCbP37c9 f ξ) + (tlNCbP37c10 f ξ + tlNCbP37c11 f ξ)) +
        ((tlNCbP37c12 f ξ + tlNCbP37c13 f ξ) + (tlNCbP37c14 f ξ + tlNCbP37c15 f ξ)))) +
        ((tlNCbP37c16 f ξ + tlNCbP37c17 f ξ) + tlNCbP37c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ37c0 f ξ) * hT + (tlNCbQ37c1 f ξ) * hT + (tlNCbQ37c2 f ξ) * hT + (tlNCbQ37c3 f ξ) * hT
      + (tlNCbQ37c4 f ξ) * hT + (tlNCbQ37c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP37c0, tlNCbP37c1, tlNCbP37c10, tlNCbP37c11,
      tlNCbP37c12, tlNCbP37c13, tlNCbP37c14, tlNCbP37c15, tlNCbP37c16, tlNCbP37c17,
      tlNCbP37c18, tlNCbP37c2, tlNCbP37c3, tlNCbP37c4, tlNCbP37c5, tlNCbP37c6,
      tlNCbP37c7, tlNCbP37c8, tlNCbP37c9, tlNCbQ37c0, tlNCbQ37c1, tlNCbQ37c2,
      tlNCbQ37c3, tlNCbQ37c4, tlNCbQ37c5, tlNSqP3c8, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s38 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP38c0 f + tlNCbP38c1 f ξ) + (tlNCbP38c2 f ξ + tlNCbP38c3 f ξ)) +
        ((tlNCbP38c4 f ξ + tlNCbP38c5 f ξ) + (tlNCbP38c6 f ξ + tlNCbP38c7 f ξ))) +
        (((tlNCbP38c8 f ξ + tlNCbP38c9 f ξ) + (tlNCbP38c10 f ξ + tlNCbP38c11 f ξ)) +
        ((tlNCbP38c12 f ξ + tlNCbP38c13 f ξ) + (tlNCbP38c14 f ξ + tlNCbP38c15 f ξ)))) +
        ((tlNCbP38c16 f ξ + tlNCbP38c17 f ξ) + tlNCbP38c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ38c0 f ξ) * hT + (tlNCbQ38c1 f ξ) * hT + (tlNCbQ38c2 f ξ) * hT + (tlNCbQ38c3 f ξ) * hT
      + (tlNCbQ38c4 f ξ) * hT + (tlNCbQ38c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP38c0, tlNCbP38c1, tlNCbP38c10, tlNCbP38c11,
      tlNCbP38c12, tlNCbP38c13, tlNCbP38c14, tlNCbP38c15, tlNCbP38c16, tlNCbP38c17,
      tlNCbP38c18, tlNCbP38c2, tlNCbP38c3, tlNCbP38c4, tlNCbP38c5, tlNCbP38c6,
      tlNCbP38c7, tlNCbP38c8, tlNCbP38c9, tlNCbQ38c0, tlNCbQ38c1, tlNCbQ38c2,
      tlNCbQ38c3, tlNCbQ38c4, tlNCbQ38c5, tlNSqP3c9, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s39 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c10 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP39c0 f + tlNCbP39c1 f ξ) + (tlNCbP39c2 f ξ + tlNCbP39c3 f ξ)) +
        ((tlNCbP39c4 f ξ + tlNCbP39c5 f ξ) + (tlNCbP39c6 f ξ + tlNCbP39c7 f ξ))) +
        (((tlNCbP39c8 f ξ + tlNCbP39c9 f ξ) + (tlNCbP39c10 f ξ + tlNCbP39c11 f ξ)) +
        ((tlNCbP39c12 f ξ + tlNCbP39c13 f ξ) + (tlNCbP39c14 f ξ + tlNCbP39c15 f ξ)))) +
        ((tlNCbP39c16 f ξ + tlNCbP39c17 f ξ) + tlNCbP39c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ39c0 f ξ) * hT + (tlNCbQ39c1 f ξ) * hT + (tlNCbQ39c2 f ξ) * hT + (tlNCbQ39c3 f ξ) * hT
      + (tlNCbQ39c4 f ξ) * hT + (tlNCbQ39c5 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP39c0, tlNCbP39c1, tlNCbP39c10, tlNCbP39c11,
      tlNCbP39c12, tlNCbP39c13, tlNCbP39c14, tlNCbP39c15, tlNCbP39c16, tlNCbP39c17,
      tlNCbP39c18, tlNCbP39c2, tlNCbP39c3, tlNCbP39c4, tlNCbP39c5, tlNCbP39c6,
      tlNCbP39c7, tlNCbP39c8, tlNCbP39c9, tlNCbQ39c0, tlNCbQ39c1, tlNCbQ39c2,
      tlNCbQ39c3, tlNCbQ39c4, tlNCbQ39c5, tlNSqP3c10, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlNCb_s40 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP3c11 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      ((((tlNCbP40c0 f + tlNCbP40c1 f ξ) + (tlNCbP40c2 f ξ + tlNCbP40c3 f ξ)) +
        ((tlNCbP40c4 f ξ + tlNCbP40c5 f ξ) + (tlNCbP40c6 f ξ + tlNCbP40c7 f ξ))) +
        (((tlNCbP40c8 f ξ + tlNCbP40c9 f ξ) + (tlNCbP40c10 f ξ + tlNCbP40c11 f ξ)) +
        ((tlNCbP40c12 f ξ + tlNCbP40c13 f ξ) + (tlNCbP40c14 f ξ + tlNCbP40c15 f ξ)))) +
        ((tlNCbP40c16 f ξ + tlNCbP40c17 f ξ) + tlNCbP40c18 f ξ) := by
  linear_combination (norm := skip)
    (tlNCbQ40c0 f ξ) * hT + (tlNCbQ40c1 f ξ) * hT + (tlNCbQ40c2 f ξ) * hT + (tlNCbQ40c3 f ξ) * hT
      + (tlNCbQ40c4 f ξ) * hT + (tlNCbQ40c5 f ξ) * hT + (tlNCbQ40c6 f ξ) * hT
  simp only [tlN0, tlN1, tlN2, tlN3, tlNCbP40c0, tlNCbP40c1, tlNCbP40c10, tlNCbP40c11,
      tlNCbP40c12, tlNCbP40c13, tlNCbP40c14, tlNCbP40c15, tlNCbP40c16, tlNCbP40c17,
      tlNCbP40c18, tlNCbP40c2, tlNCbP40c3, tlNCbP40c4, tlNCbP40c5, tlNCbP40c6,
      tlNCbP40c7, tlNCbP40c8, tlNCbP40c9, tlNCbQ40c0, tlNCbQ40c1, tlNCbQ40c2,
      tlNCbQ40c3, tlNCbQ40c4, tlNCbQ40c5, tlNCbQ40c6, tlNSqP3c11, tlT0, tlT1, tlT2,
      tlT3]
  ring1

lemma tlNCb_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((((((tlNSqP0c0 f ξ + tlNSqP0c1 f ξ) + (tlNSqP0c2 f ξ + tlNSqP0c3 f ξ)) + ((tlNSqP0c4 f ξ +
      tlNSqP0c5 f ξ) + (tlNSqP0c6 f ξ + tlNSqP0c7 f ξ))) + (((tlNSqP0c8 f ξ + tlNSqP1c0 f ξ) +
      (tlNSqP1c1 f ξ + tlNSqP1c2 f ξ)) + ((tlNSqP1c3 f ξ + tlNSqP1c4 f ξ) + (tlNSqP1c5 f ξ +
      tlNSqP1c6 f ξ)))) + ((((tlNSqP1c7 f ξ + tlNSqP1c8 f ξ) + (tlNSqP1c9 f ξ + tlNSqP2c0 f ξ)) +
      ((tlNSqP2c1 f ξ + tlNSqP2c2 f ξ) + (tlNSqP2c3 f ξ + tlNSqP2c4 f ξ))) + (((tlNSqP2c5 f ξ +
      tlNSqP2c6 f ξ) + (tlNSqP2c7 f ξ + tlNSqP2c8 f ξ)) + ((tlNSqP2c9 f ξ + tlNSqP2c10 f ξ) +
      (tlNSqP2c11 f ξ + tlNSqP3c0 f ξ))))) + ((((tlNSqP3c1 f ξ + tlNSqP3c2 f ξ) + (tlNSqP3c3 f ξ +
      tlNSqP3c4 f ξ)) + ((tlNSqP3c5 f ξ + tlNSqP3c6 f ξ) + (tlNSqP3c7 f ξ + tlNSqP3c8 f ξ))) +
      ((tlNSqP3c9 f ξ + tlNSqP3c10 f ξ) + tlNSqP3c11 f ξ))) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ +
      tlN3 f ξ)) =
      (((((((((tlNCbP0c0 f ξ + tlNCbP0c1 f ξ) + (tlNCbP0c2 f ξ + tlNCbP0c3 f ξ)) +
        ((tlNCbP0c4 f ξ + tlNCbP0c5 f ξ) + (tlNCbP0c6 f ξ + tlNCbP0c7 f ξ))) +
        (((tlNCbP0c8 f ξ + tlNCbP0c9 f ξ) + (tlNCbP0c10 f ξ + tlNCbP1c0 f ξ)) +
        ((tlNCbP1c1 f ξ + tlNCbP1c2 f ξ) + (tlNCbP1c3 f ξ + tlNCbP1c4 f ξ)))) +
        ((((tlNCbP1c5 f ξ + tlNCbP1c6 f ξ) + (tlNCbP1c7 f ξ + tlNCbP1c8 f ξ)) +
        ((tlNCbP1c9 f ξ + tlNCbP1c10 f ξ) + (tlNCbP1c11 f ξ + tlNCbP1c12 f ξ))) +
        (((tlNCbP2c0 f ξ + tlNCbP2c1 f ξ) + (tlNCbP2c2 f ξ + tlNCbP2c3 f ξ)) + ((tlNCbP2c4
        f ξ + tlNCbP2c5 f ξ) + (tlNCbP2c6 f ξ + tlNCbP2c7 f ξ))))) + (((((tlNCbP2c8 f ξ +
        tlNCbP2c9 f ξ) + (tlNCbP2c10 f ξ + tlNCbP2c11 f ξ)) + ((tlNCbP2c12 f ξ +
        tlNCbP2c13 f ξ) + (tlNCbP2c14 f ξ + tlNCbP3c0 f ξ))) + (((tlNCbP3c1 f ξ +
        tlNCbP3c2 f ξ) + (tlNCbP3c3 f ξ + tlNCbP3c4 f ξ)) + ((tlNCbP3c5 f ξ + tlNCbP3c6 f
        ξ) + (tlNCbP3c7 f ξ + tlNCbP3c8 f ξ)))) + ((((tlNCbP3c9 f ξ + tlNCbP3c10 f ξ) +
        (tlNCbP3c11 f ξ + tlNCbP3c12 f ξ)) + ((tlNCbP3c13 f ξ + tlNCbP3c14 f ξ) +
        (tlNCbP3c15 f ξ + tlNCbP4c0 f ξ))) + (((tlNCbP4c1 f ξ + tlNCbP4c2 f ξ) +
        (tlNCbP4c3 f ξ + tlNCbP4c4 f ξ)) + ((tlNCbP4c5 f ξ + tlNCbP4c6 f ξ) + (tlNCbP4c7 f
        ξ + tlNCbP4c8 f ξ)))))) + ((((((tlNCbP4c9 f ξ + tlNCbP4c10 f ξ) + (tlNCbP4c11 f ξ
        + tlNCbP4c12 f ξ)) + ((tlNCbP4c13 f ξ + tlNCbP4c14 f ξ) + (tlNCbP4c15 f ξ +
        tlNCbP4c16 f ξ))) + (((tlNCbP5c0 f ξ + tlNCbP5c1 f ξ) + (tlNCbP5c2 f ξ + tlNCbP5c3
        f ξ)) + ((tlNCbP5c4 f ξ + tlNCbP5c5 f ξ) + (tlNCbP5c6 f ξ + tlNCbP5c7 f ξ)))) +
        ((((tlNCbP5c8 f ξ + tlNCbP5c9 f ξ) + (tlNCbP5c10 f ξ + tlNCbP5c11 f ξ)) +
        ((tlNCbP5c12 f ξ + tlNCbP5c13 f ξ) + (tlNCbP5c14 f ξ + tlNCbP5c15 f ξ))) +
        (((tlNCbP5c16 f ξ + tlNCbP5c17 f ξ) + (tlNCbP6c0 f ξ + tlNCbP6c1 f ξ)) +
        ((tlNCbP6c2 f ξ + tlNCbP6c3 f ξ) + (tlNCbP6c4 f ξ + tlNCbP6c5 f ξ))))) +
        (((((tlNCbP6c6 f ξ + tlNCbP6c7 f ξ) + (tlNCbP6c8 f ξ + tlNCbP6c9 f ξ)) +
        ((tlNCbP6c10 f ξ + tlNCbP6c11 f ξ) + (tlNCbP6c12 f ξ + tlNCbP6c13 f ξ))) +
        (((tlNCbP6c14 f ξ + tlNCbP6c15 f ξ) + (tlNCbP6c16 f ξ + tlNCbP6c17 f ξ)) +
        ((tlNCbP7c0 f ξ + tlNCbP7c1 f ξ) + (tlNCbP7c2 f ξ + tlNCbP7c3 f ξ)))) +
        ((((tlNCbP7c4 f ξ + tlNCbP7c5 f ξ) + (tlNCbP7c6 f ξ + tlNCbP7c7 f ξ)) +
        ((tlNCbP7c8 f ξ + tlNCbP7c9 f ξ) + (tlNCbP7c10 f ξ + tlNCbP7c11 f ξ))) +
        (((tlNCbP7c12 f ξ + tlNCbP7c13 f ξ) + (tlNCbP7c14 f ξ + tlNCbP7c15 f ξ)) +
        ((tlNCbP7c16 f ξ + tlNCbP7c17 f ξ) + (tlNCbP7c18 f ξ + tlNCbP8c0 f ξ))))))) +
        (((((((tlNCbP8c1 f ξ + tlNCbP8c2 f ξ) + (tlNCbP8c3 f ξ + tlNCbP8c4 f ξ)) +
        ((tlNCbP8c5 f ξ + tlNCbP8c6 f ξ) + (tlNCbP8c7 f ξ + tlNCbP8c8 f ξ))) +
        (((tlNCbP8c9 f ξ + tlNCbP8c10 f ξ) + (tlNCbP9c0 f ξ + tlNCbP9c1 f ξ)) +
        ((tlNCbP9c2 f ξ + tlNCbP9c3 f ξ) + (tlNCbP9c4 f ξ + tlNCbP9c5 f ξ)))) +
        ((((tlNCbP9c6 f ξ + tlNCbP9c7 f ξ) + (tlNCbP9c8 f ξ + tlNCbP9c9 f ξ)) +
        ((tlNCbP9c10 f ξ + tlNCbP9c11 f ξ) + (tlNCbP9c12 f ξ + tlNCbP10c0 f ξ))) +
        (((tlNCbP10c1 f ξ + tlNCbP10c2 f ξ) + (tlNCbP10c3 f ξ + tlNCbP10c4 f ξ)) +
        ((tlNCbP10c5 f ξ + tlNCbP10c6 f ξ) + (tlNCbP10c7 f ξ + tlNCbP10c8 f ξ))))) +
        (((((tlNCbP10c9 f ξ + tlNCbP10c10 f ξ) + (tlNCbP10c11 f ξ + tlNCbP10c12 f ξ)) +
        ((tlNCbP10c13 f ξ + tlNCbP11c0 f ξ) + (tlNCbP11c1 f ξ + tlNCbP11c2 f ξ))) +
        (((tlNCbP11c3 f ξ + tlNCbP11c4 f ξ) + (tlNCbP11c5 f ξ + tlNCbP11c6 f ξ)) +
        ((tlNCbP11c7 f ξ + tlNCbP11c8 f ξ) + (tlNCbP11c9 f ξ + tlNCbP11c10 f ξ)))) +
        ((((tlNCbP11c11 f ξ + tlNCbP11c12 f ξ) + (tlNCbP11c13 f ξ + tlNCbP11c14 f ξ)) +
        ((tlNCbP12c0 f ξ + tlNCbP12c1 f ξ) + (tlNCbP12c2 f ξ + tlNCbP12c3 f ξ))) +
        (((tlNCbP12c4 f ξ + tlNCbP12c5 f ξ) + (tlNCbP12c6 f ξ + tlNCbP12c7 f ξ)) +
        ((tlNCbP12c8 f ξ + tlNCbP12c9 f ξ) + (tlNCbP12c10 f ξ + tlNCbP12c11 f ξ)))))) +
        ((((((tlNCbP12c12 f ξ + tlNCbP12c13 f ξ) + (tlNCbP12c14 f ξ + tlNCbP12c15 f ξ)) +
        ((tlNCbP13c0 f ξ + tlNCbP13c1 f ξ) + (tlNCbP13c2 f ξ + tlNCbP13c3 f ξ))) +
        (((tlNCbP13c4 f ξ + tlNCbP13c5 f ξ) + (tlNCbP13c6 f ξ + tlNCbP13c7 f ξ)) +
        ((tlNCbP13c8 f ξ + tlNCbP13c9 f ξ) + (tlNCbP13c10 f ξ + tlNCbP13c11 f ξ)))) +
        ((((tlNCbP13c12 f ξ + tlNCbP13c13 f ξ) + (tlNCbP13c14 f ξ + tlNCbP13c15 f ξ)) +
        ((tlNCbP13c16 f ξ + tlNCbP13c17 f ξ) + (tlNCbP14c0 f ξ + tlNCbP14c1 f ξ))) +
        (((tlNCbP14c2 f ξ + tlNCbP14c3 f ξ) + (tlNCbP14c4 f ξ + tlNCbP14c5 f ξ)) +
        ((tlNCbP14c6 f ξ + tlNCbP14c7 f ξ) + (tlNCbP14c8 f ξ + tlNCbP14c9 f ξ))))) +
        (((((tlNCbP14c10 f ξ + tlNCbP14c11 f ξ) + (tlNCbP14c12 f ξ + tlNCbP14c13 f ξ)) +
        ((tlNCbP14c14 f ξ + tlNCbP14c15 f ξ) + (tlNCbP14c16 f ξ + tlNCbP14c17 f ξ))) +
        (((tlNCbP15c0 f + tlNCbP15c1 f ξ) + (tlNCbP15c2 f ξ + tlNCbP15c3 f ξ)) +
        ((tlNCbP15c4 f ξ + tlNCbP15c5 f ξ) + (tlNCbP15c6 f ξ + tlNCbP15c7 f ξ)))) +
        ((((tlNCbP15c8 f ξ + tlNCbP15c9 f ξ) + (tlNCbP15c10 f ξ + tlNCbP15c11 f ξ)) +
        ((tlNCbP15c12 f ξ + tlNCbP15c13 f ξ) + (tlNCbP15c14 f ξ + tlNCbP15c15 f ξ))) +
        (((tlNCbP15c16 f ξ + tlNCbP15c17 f ξ) + (tlNCbP15c18 f ξ + tlNCbP16c0 f ξ)) +
        ((tlNCbP16c1 f ξ + tlNCbP16c2 f ξ) + (tlNCbP16c3 f ξ + tlNCbP16c4 f ξ)))))))) +
        ((((((((tlNCbP16c5 f ξ + tlNCbP16c6 f ξ) + (tlNCbP16c7 f ξ + tlNCbP16c8 f ξ)) +
        ((tlNCbP16c9 f ξ + tlNCbP16c10 f ξ) + (tlNCbP16c11 f ξ + tlNCbP16c12 f ξ))) +
        (((tlNCbP16c13 f ξ + tlNCbP16c14 f ξ) + (tlNCbP16c15 f ξ + tlNCbP16c16 f ξ)) +
        ((tlNCbP16c17 f ξ + tlNCbP16c18 f ξ) + (tlNCbP17c0 f ξ + tlNCbP17c1 f ξ)))) +
        ((((tlNCbP17c2 f ξ + tlNCbP17c3 f ξ) + (tlNCbP17c4 f ξ + tlNCbP17c5 f ξ)) +
        ((tlNCbP17c6 f ξ + tlNCbP17c7 f ξ) + (tlNCbP17c8 f ξ + tlNCbP17c9 f ξ))) +
        (((tlNCbP17c10 f ξ + tlNCbP17c11 f ξ) + (tlNCbP17c12 f ξ + tlNCbP17c13 f ξ)) +
        ((tlNCbP17c14 f ξ + tlNCbP17c15 f ξ) + (tlNCbP17c16 f ξ + tlNCbP17c17 f ξ))))) +
        (((((tlNCbP17c18 f ξ + tlNCbP18c0 f ξ) + (tlNCbP18c1 f ξ + tlNCbP18c2 f ξ)) +
        ((tlNCbP18c3 f ξ + tlNCbP18c4 f ξ) + (tlNCbP18c5 f ξ + tlNCbP18c6 f ξ))) +
        (((tlNCbP18c7 f ξ + tlNCbP18c8 f ξ) + (tlNCbP18c9 f ξ + tlNCbP18c10 f ξ)) +
        ((tlNCbP19c0 f ξ + tlNCbP19c1 f ξ) + (tlNCbP19c2 f ξ + tlNCbP19c3 f ξ)))) +
        ((((tlNCbP19c4 f ξ + tlNCbP19c5 f ξ) + (tlNCbP19c6 f ξ + tlNCbP19c7 f ξ)) +
        ((tlNCbP19c8 f ξ + tlNCbP19c9 f ξ) + (tlNCbP19c10 f ξ + tlNCbP19c11 f ξ))) +
        (((tlNCbP19c12 f ξ + tlNCbP20c0 f ξ) + (tlNCbP20c1 f ξ + tlNCbP20c2 f ξ)) +
        ((tlNCbP20c3 f ξ + tlNCbP20c4 f ξ) + (tlNCbP20c5 f ξ + tlNCbP20c6 f ξ)))))) +
        ((((((tlNCbP20c7 f ξ + tlNCbP20c8 f ξ) + (tlNCbP20c9 f ξ + tlNCbP20c10 f ξ)) +
        ((tlNCbP20c11 f ξ + tlNCbP20c12 f ξ) + (tlNCbP20c13 f ξ + tlNCbP21c0 f ξ))) +
        (((tlNCbP21c1 f ξ + tlNCbP21c2 f ξ) + (tlNCbP21c3 f ξ + tlNCbP21c4 f ξ)) +
        ((tlNCbP21c5 f ξ + tlNCbP21c6 f ξ) + (tlNCbP21c7 f ξ + tlNCbP21c8 f ξ)))) +
        ((((tlNCbP21c9 f ξ + tlNCbP21c10 f ξ) + (tlNCbP21c11 f ξ + tlNCbP21c12 f ξ)) +
        ((tlNCbP21c13 f ξ + tlNCbP21c14 f ξ) + (tlNCbP22c0 f ξ + tlNCbP22c1 f ξ))) +
        (((tlNCbP22c2 f ξ + tlNCbP22c3 f ξ) + (tlNCbP22c4 f ξ + tlNCbP22c5 f ξ)) +
        ((tlNCbP22c6 f ξ + tlNCbP22c7 f ξ) + (tlNCbP22c8 f ξ + tlNCbP22c9 f ξ))))) +
        (((((tlNCbP22c10 f ξ + tlNCbP22c11 f ξ) + (tlNCbP22c12 f ξ + tlNCbP22c13 f ξ)) +
        ((tlNCbP22c14 f ξ + tlNCbP22c15 f ξ) + (tlNCbP23c0 f ξ + tlNCbP23c1 f ξ))) +
        (((tlNCbP23c2 f ξ + tlNCbP23c3 f ξ) + (tlNCbP23c4 f ξ + tlNCbP23c5 f ξ)) +
        ((tlNCbP23c6 f ξ + tlNCbP23c7 f ξ) + (tlNCbP23c8 f ξ + tlNCbP23c9 f ξ)))) +
        ((((tlNCbP23c10 f ξ + tlNCbP23c11 f ξ) + (tlNCbP23c12 f ξ + tlNCbP23c13 f ξ)) +
        ((tlNCbP23c14 f ξ + tlNCbP23c15 f ξ) + (tlNCbP23c16 f ξ + tlNCbP24c0 f ξ))) +
        (((tlNCbP24c1 f ξ + tlNCbP24c2 f ξ) + (tlNCbP24c3 f ξ + tlNCbP24c4 f ξ)) +
        ((tlNCbP24c5 f ξ + tlNCbP24c6 f ξ) + (tlNCbP24c7 f ξ + tlNCbP24c8 f ξ))))))) +
        (((((((tlNCbP24c9 f ξ + tlNCbP24c10 f ξ) + (tlNCbP24c11 f ξ + tlNCbP24c12 f ξ)) +
        ((tlNCbP24c13 f ξ + tlNCbP24c14 f ξ) + (tlNCbP24c15 f ξ + tlNCbP24c16 f ξ))) +
        (((tlNCbP24c17 f ξ + tlNCbP25c0 f) + (tlNCbP25c1 f ξ + tlNCbP25c2 f ξ)) +
        ((tlNCbP25c3 f ξ + tlNCbP25c4 f ξ) + (tlNCbP25c5 f ξ + tlNCbP25c6 f ξ)))) +
        ((((tlNCbP25c7 f ξ + tlNCbP25c8 f ξ) + (tlNCbP25c9 f ξ + tlNCbP25c10 f ξ)) +
        ((tlNCbP25c11 f ξ + tlNCbP25c12 f ξ) + (tlNCbP25c13 f ξ + tlNCbP25c14 f ξ))) +
        (((tlNCbP25c15 f ξ + tlNCbP25c16 f ξ) + (tlNCbP25c17 f ξ + tlNCbP25c18 f ξ)) +
        ((tlNCbP26c0 f ξ + tlNCbP26c1 f ξ) + (tlNCbP26c2 f ξ + tlNCbP26c3 f ξ))))) +
        (((((tlNCbP26c4 f ξ + tlNCbP26c5 f ξ) + (tlNCbP26c6 f ξ + tlNCbP26c7 f ξ)) +
        ((tlNCbP26c8 f ξ + tlNCbP26c9 f ξ) + (tlNCbP26c10 f ξ + tlNCbP26c11 f ξ))) +
        (((tlNCbP26c12 f ξ + tlNCbP26c13 f ξ) + (tlNCbP26c14 f ξ + tlNCbP26c15 f ξ)) +
        ((tlNCbP26c16 f ξ + tlNCbP26c17 f ξ) + (tlNCbP26c18 f ξ + tlNCbP27c0 f ξ)))) +
        ((((tlNCbP27c1 f ξ + tlNCbP27c2 f ξ) + (tlNCbP27c3 f ξ + tlNCbP27c4 f ξ)) +
        ((tlNCbP27c5 f ξ + tlNCbP27c6 f ξ) + (tlNCbP27c7 f ξ + tlNCbP27c8 f ξ))) +
        (((tlNCbP27c9 f ξ + tlNCbP27c10 f ξ) + (tlNCbP27c11 f ξ + tlNCbP27c12 f ξ)) +
        ((tlNCbP27c13 f ξ + tlNCbP27c14 f ξ) + (tlNCbP27c15 f ξ + tlNCbP27c16 f ξ)))))) +
        ((((((tlNCbP27c17 f ξ + tlNCbP27c18 f ξ) + (tlNCbP28c0 f ξ + tlNCbP28c1 f ξ)) +
        ((tlNCbP28c2 f ξ + tlNCbP28c3 f ξ) + (tlNCbP28c4 f ξ + tlNCbP28c5 f ξ))) +
        (((tlNCbP28c6 f ξ + tlNCbP28c7 f ξ) + (tlNCbP28c8 f ξ + tlNCbP28c9 f ξ)) +
        ((tlNCbP28c10 f ξ + tlNCbP28c11 f ξ) + (tlNCbP28c12 f ξ + tlNCbP28c13 f ξ)))) +
        ((((tlNCbP28c14 f ξ + tlNCbP28c15 f ξ) + (tlNCbP28c16 f ξ + tlNCbP28c17 f ξ)) +
        ((tlNCbP28c18 f ξ + tlNCbP29c0 f ξ) + (tlNCbP29c1 f ξ + tlNCbP29c2 f ξ))) +
        (((tlNCbP29c3 f ξ + tlNCbP29c4 f ξ) + (tlNCbP29c5 f ξ + tlNCbP29c6 f ξ)) +
        ((tlNCbP29c7 f ξ + tlNCbP29c8 f ξ) + (tlNCbP29c9 f ξ + tlNCbP29c10 f ξ))))) +
        (((((tlNCbP30c0 f ξ + tlNCbP30c1 f ξ) + (tlNCbP30c2 f ξ + tlNCbP30c3 f ξ)) +
        ((tlNCbP30c4 f ξ + tlNCbP30c5 f ξ) + (tlNCbP30c6 f ξ + tlNCbP30c7 f ξ))) +
        (((tlNCbP30c8 f ξ + tlNCbP30c9 f ξ) + (tlNCbP30c10 f ξ + tlNCbP30c11 f ξ)) +
        ((tlNCbP30c12 f ξ + tlNCbP31c0 f ξ) + (tlNCbP31c1 f ξ + tlNCbP31c2 f ξ)))) +
        ((((tlNCbP31c3 f ξ + tlNCbP31c4 f ξ) + (tlNCbP31c5 f ξ + tlNCbP31c6 f ξ)) +
        ((tlNCbP31c7 f ξ + tlNCbP31c8 f ξ) + (tlNCbP31c9 f ξ + tlNCbP31c10 f ξ))) +
        (((tlNCbP31c11 f ξ + tlNCbP31c12 f ξ) + (tlNCbP31c13 f ξ + tlNCbP32c0 f ξ)) +
        ((tlNCbP32c1 f ξ + tlNCbP32c2 f ξ) + (tlNCbP32c3 f ξ + tlNCbP32c4 f ξ))))))))) +
        ((((((((tlNCbP32c5 f ξ + tlNCbP32c6 f ξ) + (tlNCbP32c7 f ξ + tlNCbP32c8 f ξ)) +
        ((tlNCbP32c9 f ξ + tlNCbP32c10 f ξ) + (tlNCbP32c11 f ξ + tlNCbP32c12 f ξ))) +
        (((tlNCbP32c13 f ξ + tlNCbP32c14 f ξ) + (tlNCbP32c15 f ξ + tlNCbP33c0 f ξ)) +
        ((tlNCbP33c1 f ξ + tlNCbP33c2 f ξ) + (tlNCbP33c3 f ξ + tlNCbP33c4 f ξ)))) +
        ((((tlNCbP33c5 f ξ + tlNCbP33c6 f ξ) + (tlNCbP33c7 f ξ + tlNCbP33c8 f ξ)) +
        ((tlNCbP33c9 f ξ + tlNCbP33c10 f ξ) + (tlNCbP33c11 f ξ + tlNCbP33c12 f ξ))) +
        (((tlNCbP33c13 f ξ + tlNCbP33c14 f ξ) + (tlNCbP33c15 f ξ + tlNCbP33c16 f ξ)) +
        ((tlNCbP34c0 f ξ + tlNCbP34c1 f ξ) + (tlNCbP34c2 f ξ + tlNCbP34c3 f ξ))))) +
        (((((tlNCbP34c4 f ξ + tlNCbP34c5 f ξ) + (tlNCbP34c6 f ξ + tlNCbP34c7 f ξ)) +
        ((tlNCbP34c8 f ξ + tlNCbP34c9 f ξ) + (tlNCbP34c10 f ξ + tlNCbP34c11 f ξ))) +
        (((tlNCbP34c12 f ξ + tlNCbP34c13 f ξ) + (tlNCbP34c14 f ξ + tlNCbP34c15 f ξ)) +
        ((tlNCbP34c16 f ξ + tlNCbP34c17 f ξ) + (tlNCbP35c0 f ξ + tlNCbP35c1 f ξ)))) +
        ((((tlNCbP35c2 f ξ + tlNCbP35c3 f ξ) + (tlNCbP35c4 f ξ + tlNCbP35c5 f ξ)) +
        ((tlNCbP35c6 f ξ + tlNCbP35c7 f ξ) + (tlNCbP35c8 f ξ + tlNCbP35c9 f ξ))) +
        (((tlNCbP35c10 f ξ + tlNCbP35c11 f ξ) + (tlNCbP35c12 f ξ + tlNCbP35c13 f ξ)) +
        ((tlNCbP35c14 f ξ + tlNCbP35c15 f ξ) + (tlNCbP35c16 f ξ + tlNCbP35c17 f ξ)))))) +
        ((((((tlNCbP36c0 f + tlNCbP36c1 f ξ) + (tlNCbP36c2 f ξ + tlNCbP36c3 f ξ)) +
        ((tlNCbP36c4 f ξ + tlNCbP36c5 f ξ) + (tlNCbP36c6 f ξ + tlNCbP36c7 f ξ))) +
        (((tlNCbP36c8 f ξ + tlNCbP36c9 f ξ) + (tlNCbP36c10 f ξ + tlNCbP36c11 f ξ)) +
        ((tlNCbP36c12 f ξ + tlNCbP36c13 f ξ) + (tlNCbP36c14 f ξ + tlNCbP36c15 f ξ)))) +
        ((((tlNCbP36c16 f ξ + tlNCbP36c17 f ξ) + (tlNCbP36c18 f ξ + tlNCbP37c0 f)) +
        ((tlNCbP37c1 f ξ + tlNCbP37c2 f ξ) + (tlNCbP37c3 f ξ + tlNCbP37c4 f ξ))) +
        (((tlNCbP37c5 f ξ + tlNCbP37c6 f ξ) + (tlNCbP37c7 f ξ + tlNCbP37c8 f ξ)) +
        ((tlNCbP37c9 f ξ + tlNCbP37c10 f ξ) + (tlNCbP37c11 f ξ + tlNCbP37c12 f ξ))))) +
        (((((tlNCbP37c13 f ξ + tlNCbP37c14 f ξ) + (tlNCbP37c15 f ξ + tlNCbP37c16 f ξ)) +
        ((tlNCbP37c17 f ξ + tlNCbP37c18 f ξ) + (tlNCbP38c0 f + tlNCbP38c1 f ξ))) +
        (((tlNCbP38c2 f ξ + tlNCbP38c3 f ξ) + (tlNCbP38c4 f ξ + tlNCbP38c5 f ξ)) +
        ((tlNCbP38c6 f ξ + tlNCbP38c7 f ξ) + (tlNCbP38c8 f ξ + tlNCbP38c9 f ξ)))) +
        ((((tlNCbP38c10 f ξ + tlNCbP38c11 f ξ) + (tlNCbP38c12 f ξ + tlNCbP38c13 f ξ)) +
        ((tlNCbP38c14 f ξ + tlNCbP38c15 f ξ) + (tlNCbP38c16 f ξ + tlNCbP38c17 f ξ))) +
        (((tlNCbP38c18 f ξ + tlNCbP39c0 f) + (tlNCbP39c1 f ξ + tlNCbP39c2 f ξ)) +
        ((tlNCbP39c3 f ξ + tlNCbP39c4 f ξ) + (tlNCbP39c5 f ξ + tlNCbP39c6 f ξ))))))) +
        (((((tlNCbP39c7 f ξ + tlNCbP39c8 f ξ) + (tlNCbP39c9 f ξ + tlNCbP39c10 f ξ)) +
        ((tlNCbP39c11 f ξ + tlNCbP39c12 f ξ) + (tlNCbP39c13 f ξ + tlNCbP39c14 f ξ))) +
        (((tlNCbP39c15 f ξ + tlNCbP39c16 f ξ) + (tlNCbP39c17 f ξ + tlNCbP39c18 f ξ)) +
        ((tlNCbP40c0 f + tlNCbP40c1 f ξ) + (tlNCbP40c2 f ξ + tlNCbP40c3 f ξ)))) +
        ((((tlNCbP40c4 f ξ + tlNCbP40c5 f ξ) + (tlNCbP40c6 f ξ + tlNCbP40c7 f ξ)) +
        ((tlNCbP40c8 f ξ + tlNCbP40c9 f ξ) + (tlNCbP40c10 f ξ + tlNCbP40c11 f ξ))) +
        (((tlNCbP40c12 f ξ + tlNCbP40c13 f ξ) + (tlNCbP40c14 f ξ + tlNCbP40c15 f ξ)) +
        ((tlNCbP40c16 f ξ + tlNCbP40c17 f ξ) + tlNCbP40c18 f ξ))))) := by
  linear_combination
    ((((((tlNCb_s0 hT) + (tlNCb_s1 hT)) + ((tlNCb_s2 hT) + (tlNCb_s3 hT))) + (((tlNCb_s4 hT) +
      (tlNCb_s5 hT)) + ((tlNCb_s6 hT) + (tlNCb_s7 hT)))) + ((((tlNCb_s8 hT) + (tlNCb_s9 hT)) +
      ((tlNCb_s10 hT) + (tlNCb_s11 hT))) + (((tlNCb_s12 hT) + (tlNCb_s13 hT)) + ((tlNCb_s14 hT) +
      (tlNCb_s15 hT))))) + (((((tlNCb_s16 hT) + (tlNCb_s17 hT)) + ((tlNCb_s18 hT) + (tlNCb_s19
      hT))) + (((tlNCb_s20 hT) + (tlNCb_s21 hT)) + ((tlNCb_s22 hT) + (tlNCb_s23 hT)))) +
      ((((tlNCb_s24 hT) + (tlNCb_s25 hT)) + ((tlNCb_s26 hT) + (tlNCb_s27 hT))) + (((tlNCb_s28 hT)
      + (tlNCb_s29 hT)) + ((tlNCb_s30 hT) + (tlNCb_s31 hT)))))) + (((((tlNCb_s32 hT) + (tlNCb_s33
      hT)) + ((tlNCb_s34 hT) + (tlNCb_s35 hT))) + (((tlNCb_s36 hT) + (tlNCb_s37 hT)) + ((tlNCb_s38
      hT) + (tlNCb_s39 hT)))) + (tlNCb_s40 hT))

lemma tlDSq_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f
        ξ + tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ +
        tlDSqP0c9 f ξ) := by
  linear_combination (norm := skip)
    (tlDSqQ0c0 f ξ) * hT + (tlDSqQ0c1 f ξ) * hT + (tlDSqQ0c2 f ξ) * hT + (tlDSqQ0c3 f ξ) * hT
  simp only [tlD0, tlD1, tlDSqP0c0, tlDSqP0c1, tlDSqP0c2, tlDSqP0c3, tlDSqP0c4, tlDSqP0c5,
      tlDSqP0c6, tlDSqP0c7, tlDSqP0c8, tlDSqP0c9, tlDSqQ0c0, tlDSqQ0c1, tlDSqQ0c2,
      tlDSqQ0c3, tlT0, tlT1, tlT2, tlT3]
  ring1

lemma tlDSq_val {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlD0 f ξ + tlD1 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlDSqP0c0 f ξ + tlDSqP0c1 f ξ) + (tlDSqP0c2 f ξ + tlDSqP0c3 f ξ)) + ((tlDSqP0c4 f
        ξ + tlDSqP0c5 f ξ) + (tlDSqP0c6 f ξ + tlDSqP0c7 f ξ))) + (tlDSqP0c8 f ξ +
        tlDSqP0c9 f ξ) := by
  linear_combination
    (tlDSq_s0 hT)

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
