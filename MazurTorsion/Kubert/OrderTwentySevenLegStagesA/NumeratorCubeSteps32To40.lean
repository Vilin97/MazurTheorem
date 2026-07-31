/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Numerator-cube identities 32 through 40

The final independent numerator-cube coefficient identities.
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


end MazurTorsion.Kubert
