/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part00
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part13
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part14
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Second-power product identities 7 through 9

The independent second-power product identities for steps 7 through 9.
-/

suppress_compilation

public section

namespace MazurTorsion.Kubert

lemma tlTTwo_s7 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c3 f ξ + tlNSqP2c4 f ξ + tlNSqP2c5 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP7c0 f ξ + tlTTwoP7c1 f ξ) + (tlTTwoP7c2 f ξ + tlTTwoP7c3 f ξ)) +
        ((tlTTwoP7c4 f ξ + tlTTwoP7c5 f ξ) + (tlTTwoP7c6 f ξ + tlTTwoP7c7 f ξ))) +
        (((tlTTwoP7c8 f ξ + tlTTwoP7c9 f ξ) + (tlTTwoP7c10 f ξ + tlTTwoP7c11 f ξ)) +
        tlTTwoP7c12 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ7c0 f ξ) * hT + (tlTTwoQ7c1 f ξ) * hT + (tlTTwoQ7c2 f ξ) * hT + (tlTTwoQ7c3 f ξ) * hT
      + (tlTTwoQ7c4 f ξ) * hT + (tlTTwoQ7c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c3, tlNSqP2c4, tlNSqP2c5, tlT0, tlT1, tlT2, tlT3, tlTTwoP7c0,
      tlTTwoP7c1, tlTTwoP7c10, tlTTwoP7c11, tlTTwoP7c12, tlTTwoP7c2, tlTTwoP7c3,
      tlTTwoP7c4, tlTTwoP7c5, tlTTwoP7c6, tlTTwoP7c7, tlTTwoP7c8, tlTTwoP7c9,
      tlTTwoQ7c0, tlTTwoQ7c1, tlTTwoQ7c2, tlTTwoQ7c3, tlTTwoQ7c4, tlTTwoQ7c5]
  ring1

lemma tlTTwo_s8 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c6 f ξ + tlNSqP2c7 f ξ + tlNSqP2c8 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      (((tlTTwoP8c0 f ξ + tlTTwoP8c1 f ξ) + (tlTTwoP8c2 f ξ + tlTTwoP8c3 f ξ)) +
        ((tlTTwoP8c4 f ξ + tlTTwoP8c5 f ξ) + (tlTTwoP8c6 f ξ + tlTTwoP8c7 f ξ))) +
        (((tlTTwoP8c8 f ξ + tlTTwoP8c9 f ξ) + (tlTTwoP8c10 f ξ + tlTTwoP8c11 f ξ)) +
        (tlTTwoP8c12 f ξ + tlTTwoP8c13 f ξ)) := by
  linear_combination (norm := skip)
    (tlTTwoQ8c0 f ξ) * hT + (tlTTwoQ8c1 f ξ) * hT + (tlTTwoQ8c2 f ξ) * hT + (tlTTwoQ8c3 f ξ) * hT
      + (tlTTwoQ8c4 f ξ) * hT + (tlTTwoQ8c5 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c6, tlNSqP2c7, tlNSqP2c8, tlT0, tlT1, tlT2, tlT3, tlTTwoP8c0,
      tlTTwoP8c1, tlTTwoP8c10, tlTTwoP8c11, tlTTwoP8c12, tlTTwoP8c13, tlTTwoP8c2,
      tlTTwoP8c3, tlTTwoP8c4, tlTTwoP8c5, tlTTwoP8c6, tlTTwoP8c7, tlTTwoP8c8,
      tlTTwoP8c9, tlTTwoQ8c0, tlTTwoQ8c1, tlTTwoQ8c2, tlTTwoQ8c3, tlTTwoQ8c4,
      tlTTwoQ8c5]
  ring1

lemma tlTTwo_s9 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlNSqP2c9 f ξ + tlNSqP2c10 f ξ + tlNSqP2c11 f ξ + tlNSqP3c0 f ξ) * (tlD0 f ξ + tlD1 f ξ) =
      ((((tlTTwoP9c0 f ξ + tlTTwoP9c1 f ξ) + (tlTTwoP9c2 f ξ + tlTTwoP9c3 f ξ)) +
        ((tlTTwoP9c4 f ξ + tlTTwoP9c5 f ξ) + (tlTTwoP9c6 f ξ + tlTTwoP9c7 f ξ))) +
        (((tlTTwoP9c8 f ξ + tlTTwoP9c9 f ξ) + (tlTTwoP9c10 f ξ + tlTTwoP9c11 f ξ)) +
        ((tlTTwoP9c12 f ξ + tlTTwoP9c13 f ξ) + (tlTTwoP9c14 f ξ + tlTTwoP9c15 f ξ)))) +
        (tlTTwoP9c16 f ξ + tlTTwoP9c17 f ξ) := by
  linear_combination (norm := skip)
    (tlTTwoQ9c0 f ξ) * hT + (tlTTwoQ9c1 f ξ) * hT + (tlTTwoQ9c2 f ξ) * hT + (tlTTwoQ9c3 f ξ) * hT
      + (tlTTwoQ9c4 f ξ) * hT + (tlTTwoQ9c5 f ξ) * hT + (tlTTwoQ9c6 f ξ) * hT
  simp only [tlD0, tlD1, tlNSqP2c10, tlNSqP2c11, tlNSqP2c9, tlNSqP3c0, tlT0, tlT1, tlT2,
      tlT3, tlTTwoP9c0, tlTTwoP9c1, tlTTwoP9c10, tlTTwoP9c11, tlTTwoP9c12,
      tlTTwoP9c13, tlTTwoP9c14, tlTTwoP9c15, tlTTwoP9c16, tlTTwoP9c17, tlTTwoP9c2,
      tlTTwoP9c3, tlTTwoP9c4, tlTTwoP9c5, tlTTwoP9c6, tlTTwoP9c7, tlTTwoP9c8,
      tlTTwoP9c9, tlTTwoQ9c0, tlTTwoQ9c1, tlTTwoQ9c2, tlTTwoQ9c3, tlTTwoQ9c4,
      tlTTwoQ9c5, tlTTwoQ9c6]
  ring1

end MazurTorsion.Kubert

end
