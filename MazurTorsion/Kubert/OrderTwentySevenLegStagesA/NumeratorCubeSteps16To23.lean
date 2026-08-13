/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part00
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part04
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part05
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part06
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Numerator-cube identities 16 through 23

The third independent numerator-cube coefficient identities.
-/

suppress_compilation

public section

namespace MazurTorsion.Kubert

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


end MazurTorsion.Kubert

end
