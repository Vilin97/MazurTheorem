/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Numerator-cube identities 24 through 31

The fourth independent numerator-cube coefficient identities.
-/

namespace MazurTorsion.Kubert

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


end MazurTorsion.Kubert
