/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part00
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part16
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part17
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part19
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part20
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# First-weight identities 3 through 5

The remaining independent first-weight identities.
-/

suppress_compilation

public section

namespace MazurTorsion.Kubert

lemma tlWOneX_s3 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP5c6 f ξ + tlTOneP5c7 f ξ + tlTOneP5c8 f ξ + tlTOneP5c9 f ξ + tlTOneP5c10 f ξ +
      tlTOneP5c11 f ξ + tlTOneP5c12 f ξ + tlTOneP6c0 f ξ + tlTOneP6c1 f ξ + tlTOneP6c2 f ξ +
      tlTOneP6c3 f ξ + tlTOneP6c4 f ξ + tlTOneP6c5 f ξ + tlTOneP6c6 f ξ + tlTOneP6c7 f ξ +
      tlTOneP6c8 f ξ + tlTOneP6c9 f ξ + tlTOneP6c10 f ξ + tlTOneP6c11 f ξ + tlTOneP6c12 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP3c0 f ξ + tlWOneXP3c1 f ξ) + (tlWOneXP3c2 f ξ + tlWOneXP3c3 f ξ)) +
        ((tlWOneXP3c4 f ξ + tlWOneXP3c5 f ξ) + (tlWOneXP3c6 f ξ + tlWOneXP3c7 f ξ))) +
        (((tlWOneXP3c8 f ξ + tlWOneXP3c9 f ξ) + (tlWOneXP3c10 f ξ + tlWOneXP3c11 f ξ)) +
        ((tlWOneXP3c12 f ξ + tlWOneXP3c13 f ξ) + (tlWOneXP3c14 f ξ + tlWOneXP3c15 f ξ))))
        + ((tlWOneXP3c16 f ξ + tlWOneXP3c17 f ξ) + (tlWOneXP3c18 f ξ + tlWOneXP3c19 f ξ))
        := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP5c10, tlTOneP5c11, tlTOneP5c12,
      tlTOneP5c6, tlTOneP5c7, tlTOneP5c8, tlTOneP5c9, tlTOneP6c0, tlTOneP6c1,
      tlTOneP6c10, tlTOneP6c11, tlTOneP6c12, tlTOneP6c2, tlTOneP6c3, tlTOneP6c4,
      tlTOneP6c5, tlTOneP6c6, tlTOneP6c7, tlTOneP6c8, tlTOneP6c9, tlWOneXP3c0,
      tlWOneXP3c1, tlWOneXP3c10, tlWOneXP3c11, tlWOneXP3c12, tlWOneXP3c13,
      tlWOneXP3c14, tlWOneXP3c15, tlWOneXP3c16, tlWOneXP3c17, tlWOneXP3c18,
      tlWOneXP3c19, tlWOneXP3c2, tlWOneXP3c3, tlWOneXP3c4, tlWOneXP3c5, tlWOneXP3c6,
      tlWOneXP3c7, tlWOneXP3c8, tlWOneXP3c9]
  ring1

lemma tlWOneX_s4 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP7c0 f ξ + tlTOneP7c1 f ξ + tlTOneP7c2 f ξ + tlTOneP7c3 f ξ + tlTOneP7c4 f ξ +
      tlTOneP7c5 f ξ + tlTOneP7c6 f ξ + tlTOneP7c7 f ξ + tlTOneP7c8 f ξ + tlTOneP7c9 f ξ +
      tlTOneP7c10 f ξ + tlTOneP7c11 f ξ + tlTOneP7c12 f ξ + tlTOneP8c0 f ξ + tlTOneP8c1 f ξ +
      tlTOneP8c2 f ξ + tlTOneP8c3 f ξ + tlTOneP8c4 f ξ + tlTOneP8c5 f ξ + tlTOneP8c6 f ξ) *
      tlMOneV0 f =
      ((((tlWOneXP4c0 f + tlWOneXP4c1 f ξ) + (tlWOneXP4c2 f ξ + tlWOneXP4c3 f ξ)) +
        ((tlWOneXP4c4 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP4c6 f ξ + tlWOneXP4c7 f ξ))) +
        (((tlWOneXP4c8 f ξ + tlWOneXP4c9 f ξ) + (tlWOneXP4c10 f ξ + tlWOneXP4c11 f ξ)) +
        ((tlWOneXP4c12 f ξ + tlWOneXP4c13 f ξ) + (tlWOneXP4c14 f ξ + tlWOneXP4c15 f ξ))))
        + (((tlWOneXP4c16 f ξ + tlWOneXP4c17 f ξ) + (tlWOneXP4c18 f ξ + tlWOneXP4c19 f ξ))
        + tlWOneXP4c20 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP7c0, tlTOneP7c1, tlTOneP7c10,
      tlTOneP7c11, tlTOneP7c12, tlTOneP7c2, tlTOneP7c3, tlTOneP7c4, tlTOneP7c5,
      tlTOneP7c6, tlTOneP7c7, tlTOneP7c8, tlTOneP7c9, tlTOneP8c0, tlTOneP8c1,
      tlTOneP8c2, tlTOneP8c3, tlTOneP8c4, tlTOneP8c5, tlTOneP8c6, tlWOneXP4c0,
      tlWOneXP4c1, tlWOneXP4c10, tlWOneXP4c11, tlWOneXP4c12, tlWOneXP4c13,
      tlWOneXP4c14, tlWOneXP4c15, tlWOneXP4c16, tlWOneXP4c17, tlWOneXP4c18,
      tlWOneXP4c19, tlWOneXP4c2, tlWOneXP4c20, tlWOneXP4c3, tlWOneXP4c4,
      tlWOneXP4c5, tlWOneXP4c6, tlWOneXP4c7, tlWOneXP4c8, tlWOneXP4c9]
  ring1

lemma tlWOneX_s5 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP8c7 f ξ + tlTOneP8c8 f ξ + tlTOneP8c9 f ξ + tlTOneP8c10 f ξ + tlTOneP8c11 f ξ +
      tlTOneP8c12 f ξ + tlTOneP9c0 f ξ + tlTOneP9c1 f ξ + tlTOneP9c2 f ξ + tlTOneP9c3 f ξ +
      tlTOneP9c4 f ξ + tlTOneP9c5 f ξ + tlTOneP9c6 f ξ + tlTOneP9c7 f ξ + tlTOneP9c8 f ξ +
      tlTOneP9c9 f ξ + tlTOneP9c10 f ξ + tlTOneP9c11 f ξ + tlTOneP9c12 f ξ) * tlMOneV0 f =
      ((((tlWOneXP5c0 f ξ + tlWOneXP5c1 f ξ) + (tlWOneXP5c2 f ξ + tlWOneXP5c3 f ξ)) +
        ((tlWOneXP5c4 f ξ + tlWOneXP5c5 f ξ) + (tlWOneXP5c6 f ξ + tlWOneXP5c7 f ξ))) +
        (((tlWOneXP5c8 f ξ + tlWOneXP5c9 f ξ) + (tlWOneXP5c10 f ξ + tlWOneXP5c11 f ξ)) +
        ((tlWOneXP5c12 f ξ + tlWOneXP5c13 f ξ) + (tlWOneXP5c14 f ξ + tlWOneXP5c15 f ξ))))
        + (((tlWOneXP5c16 f ξ + tlWOneXP5c17 f ξ) + (tlWOneXP5c18 f ξ + tlWOneXP5c19 f ξ))
        + tlWOneXP5c20 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP8c10, tlTOneP8c11, tlTOneP8c12,
      tlTOneP8c7, tlTOneP8c8, tlTOneP8c9, tlTOneP9c0, tlTOneP9c1, tlTOneP9c10,
      tlTOneP9c11, tlTOneP9c12, tlTOneP9c2, tlTOneP9c3, tlTOneP9c4, tlTOneP9c5,
      tlTOneP9c6, tlTOneP9c7, tlTOneP9c8, tlTOneP9c9, tlWOneXP5c0, tlWOneXP5c1,
      tlWOneXP5c10, tlWOneXP5c11, tlWOneXP5c12, tlWOneXP5c13, tlWOneXP5c14,
      tlWOneXP5c15, tlWOneXP5c16, tlWOneXP5c17, tlWOneXP5c18, tlWOneXP5c19,
      tlWOneXP5c2, tlWOneXP5c20, tlWOneXP5c3, tlWOneXP5c4, tlWOneXP5c5, tlWOneXP5c6,
      tlWOneXP5c7, tlWOneXP5c8, tlWOneXP5c9]
  ring1


end MazurTorsion.Kubert

end
