/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Numerator-cube identities 8 through 15

The second independent numerator-cube coefficient identities.
-/

namespace MazurTorsion.Kubert

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


end MazurTorsion.Kubert
