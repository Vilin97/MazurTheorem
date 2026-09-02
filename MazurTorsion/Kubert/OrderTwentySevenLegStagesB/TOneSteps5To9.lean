/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part00
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part10
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part16
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part17
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# First-power product identities 5 through 9

The remaining independent identities for the first-power product.
-/

suppress_compilation

public section

namespace MazurTorsion.Kubert

lemma tlTOne_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c5 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP5c0 f ξ + tlTOneP5c1 f ξ) + (tlTOneP5c2 f ξ + tlTOneP5c3 f ξ)) +
        ((tlTOneP5c4 f ξ + tlTOneP5c5 f ξ) + (tlTOneP5c6 f ξ + tlTOneP5c7 f ξ))) +
        (((tlTOneP5c8 f ξ + tlTOneP5c9 f ξ) + (tlTOneP5c10 f ξ + tlTOneP5c11 f ξ)) +
        tlTOneP5c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ5c0 f ξ) * hT + (tlTOneQ5c1 f ξ) * hT + (tlTOneQ5c2 f ξ) * hT + (tlTOneQ5c3 f ξ) * hT
      + (tlTOneQ5c4 f ξ) * hT + (tlTOneQ5c5 f ξ) * hT
  simp only [tlDSqP0c5, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP5c0,
      tlTOneP5c1, tlTOneP5c10, tlTOneP5c11, tlTOneP5c12, tlTOneP5c2, tlTOneP5c3,
      tlTOneP5c4, tlTOneP5c5, tlTOneP5c6, tlTOneP5c7, tlTOneP5c8, tlTOneP5c9,
      tlTOneQ5c0, tlTOneQ5c1, tlTOneQ5c2, tlTOneQ5c3, tlTOneQ5c4, tlTOneQ5c5]
  ring1

lemma tlTOne_s6 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c6 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP6c0 f ξ + tlTOneP6c1 f ξ) + (tlTOneP6c2 f ξ + tlTOneP6c3 f ξ)) +
        ((tlTOneP6c4 f ξ + tlTOneP6c5 f ξ) + (tlTOneP6c6 f ξ + tlTOneP6c7 f ξ))) +
        (((tlTOneP6c8 f ξ + tlTOneP6c9 f ξ) + (tlTOneP6c10 f ξ + tlTOneP6c11 f ξ)) +
        tlTOneP6c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ6c0 f ξ) * hT + (tlTOneQ6c1 f ξ) * hT + (tlTOneQ6c2 f ξ) * hT + (tlTOneQ6c3 f ξ) * hT
      + (tlTOneQ6c4 f ξ) * hT + (tlTOneQ6c5 f ξ) * hT
  simp only [tlDSqP0c6, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP6c0,
      tlTOneP6c1, tlTOneP6c10, tlTOneP6c11, tlTOneP6c12, tlTOneP6c2, tlTOneP6c3,
      tlTOneP6c4, tlTOneP6c5, tlTOneP6c6, tlTOneP6c7, tlTOneP6c8, tlTOneP6c9,
      tlTOneQ6c0, tlTOneQ6c1, tlTOneQ6c2, tlTOneQ6c3, tlTOneQ6c4, tlTOneQ6c5]
  ring1

lemma tlTOne_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c7 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP7c0 f ξ + tlTOneP7c1 f ξ) + (tlTOneP7c2 f ξ + tlTOneP7c3 f ξ)) +
        ((tlTOneP7c4 f ξ + tlTOneP7c5 f ξ) + (tlTOneP7c6 f ξ + tlTOneP7c7 f ξ))) +
        (((tlTOneP7c8 f ξ + tlTOneP7c9 f ξ) + (tlTOneP7c10 f ξ + tlTOneP7c11 f ξ)) +
        tlTOneP7c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ7c0 f ξ) * hT + (tlTOneQ7c1 f ξ) * hT + (tlTOneQ7c2 f ξ) * hT + (tlTOneQ7c3 f ξ) * hT
      + (tlTOneQ7c4 f ξ) * hT + (tlTOneQ7c5 f ξ) * hT
  simp only [tlDSqP0c7, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP7c0,
      tlTOneP7c1, tlTOneP7c10, tlTOneP7c11, tlTOneP7c12, tlTOneP7c2, tlTOneP7c3,
      tlTOneP7c4, tlTOneP7c5, tlTOneP7c6, tlTOneP7c7, tlTOneP7c8, tlTOneP7c9,
      tlTOneQ7c0, tlTOneQ7c1, tlTOneQ7c2, tlTOneQ7c3, tlTOneQ7c4, tlTOneQ7c5]
  ring1

lemma tlTOne_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c8 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP8c0 f ξ + tlTOneP8c1 f ξ) + (tlTOneP8c2 f ξ + tlTOneP8c3 f ξ)) +
        ((tlTOneP8c4 f ξ + tlTOneP8c5 f ξ) + (tlTOneP8c6 f ξ + tlTOneP8c7 f ξ))) +
        (((tlTOneP8c8 f ξ + tlTOneP8c9 f ξ) + (tlTOneP8c10 f ξ + tlTOneP8c11 f ξ)) +
        tlTOneP8c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ8c0 f ξ) * hT + (tlTOneQ8c1 f ξ) * hT + (tlTOneQ8c2 f ξ) * hT + (tlTOneQ8c3 f ξ) * hT
      + (tlTOneQ8c4 f ξ) * hT + (tlTOneQ8c5 f ξ) * hT
  simp only [tlDSqP0c8, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP8c0,
      tlTOneP8c1, tlTOneP8c10, tlTOneP8c11, tlTOneP8c12, tlTOneP8c2, tlTOneP8c3,
      tlTOneP8c4, tlTOneP8c5, tlTOneP8c6, tlTOneP8c7, tlTOneP8c8, tlTOneP8c9,
      tlTOneQ8c0, tlTOneQ8c1, tlTOneQ8c2, tlTOneQ8c3, tlTOneQ8c4, tlTOneQ8c5]
  ring1

lemma tlTOne_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlDSqP0c9 f ξ) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) =
      (((tlTOneP9c0 f ξ + tlTOneP9c1 f ξ) + (tlTOneP9c2 f ξ + tlTOneP9c3 f ξ)) +
        ((tlTOneP9c4 f ξ + tlTOneP9c5 f ξ) + (tlTOneP9c6 f ξ + tlTOneP9c7 f ξ))) +
        (((tlTOneP9c8 f ξ + tlTOneP9c9 f ξ) + (tlTOneP9c10 f ξ + tlTOneP9c11 f ξ)) +
        tlTOneP9c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTOneQ9c0 f ξ) * hT + (tlTOneQ9c1 f ξ) * hT + (tlTOneQ9c2 f ξ) * hT + (tlTOneQ9c3 f ξ) * hT
      + (tlTOneQ9c4 f ξ) * hT + (tlTOneQ9c5 f ξ) * hT
  simp only [tlDSqP0c9, tlN0, tlN1, tlN2, tlN3, tlT0, tlT1, tlT2, tlT3, tlTOneP9c0,
      tlTOneP9c1, tlTOneP9c10, tlTOneP9c11, tlTOneP9c12, tlTOneP9c2, tlTOneP9c3,
      tlTOneP9c4, tlTOneP9c5, tlTOneP9c6, tlTOneP9c7, tlTOneP9c8, tlTOneP9c9,
      tlTOneQ9c0, tlTOneQ9c1, tlTOneQ9c2, tlTOneQ9c3, tlTOneQ9c4, tlTOneQ9c5]
  ring1


end MazurTorsion.Kubert

end
