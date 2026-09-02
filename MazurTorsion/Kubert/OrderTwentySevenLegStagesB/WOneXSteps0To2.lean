/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part00
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part15
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part16
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part17
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part19
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# First-weight identities 0 through 2

The first independent first-weight identities.
-/

suppress_compilation

public section

namespace MazurTorsion.Kubert

lemma tlWOneX_s0 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP0c0 f ξ + tlTOneP0c1 f ξ + tlTOneP0c2 f ξ + tlTOneP0c3 f ξ + tlTOneP0c4 f ξ +
      tlTOneP0c5 f ξ + tlTOneP0c6 f ξ + tlTOneP0c7 f ξ + tlTOneP0c8 f ξ + tlTOneP1c0 f ξ +
      tlTOneP1c1 f ξ + tlTOneP1c2 f ξ + tlTOneP1c3 f ξ + tlTOneP1c4 f ξ + tlTOneP1c5 f ξ +
      tlTOneP1c6 f ξ + tlTOneP1c7 f ξ + tlTOneP1c8 f ξ + tlTOneP1c9 f ξ + tlTOneP2c0 f ξ +
      tlTOneP2c1 f ξ) * tlMOneV0 f =
      (((tlWOneXP0c0 f ξ + tlWOneXP0c1 f ξ) + (tlWOneXP0c2 f ξ + tlWOneXP0c3 f ξ)) +
        ((tlWOneXP0c4 f ξ + tlWOneXP0c5 f ξ) + (tlWOneXP0c6 f ξ + tlWOneXP0c7 f ξ))) +
        (((tlWOneXP0c8 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP0c10 f ξ + tlWOneXP0c11 f ξ)) +
        ((tlWOneXP0c12 f ξ + tlWOneXP0c13 f ξ) + tlWOneXP0c14 f ξ)) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP0c0, tlTOneP0c1, tlTOneP0c2,
      tlTOneP0c3, tlTOneP0c4, tlTOneP0c5, tlTOneP0c6, tlTOneP0c7, tlTOneP0c8,
      tlTOneP1c0, tlTOneP1c1, tlTOneP1c2, tlTOneP1c3, tlTOneP1c4, tlTOneP1c5,
      tlTOneP1c6, tlTOneP1c7, tlTOneP1c8, tlTOneP1c9, tlTOneP2c0, tlTOneP2c1,
      tlWOneXP0c0, tlWOneXP0c1, tlWOneXP0c10, tlWOneXP0c11, tlWOneXP0c12,
      tlWOneXP0c13, tlWOneXP0c14, tlWOneXP0c2, tlWOneXP0c3, tlWOneXP0c4,
      tlWOneXP0c5, tlWOneXP0c6, tlWOneXP0c7, tlWOneXP0c8, tlWOneXP0c9]
  ring1

lemma tlWOneX_s1 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP2c2 f ξ + tlTOneP2c3 f ξ + tlTOneP2c4 f ξ + tlTOneP2c5 f ξ + tlTOneP2c6 f ξ +
      tlTOneP2c7 f ξ + tlTOneP2c8 f ξ + tlTOneP2c9 f ξ + tlTOneP2c10 f ξ + tlTOneP2c11 f ξ +
      tlTOneP3c0 f ξ + tlTOneP3c1 f ξ + tlTOneP3c2 f ξ + tlTOneP3c3 f ξ + tlTOneP3c4 f ξ +
      tlTOneP3c5 f ξ + tlTOneP3c6 f ξ + tlTOneP3c7 f ξ + tlTOneP3c8 f ξ + tlTOneP3c9 f ξ +
      tlTOneP3c10 f ξ) * tlMOneV0 f =
      ((((tlWOneXP1c0 f ξ + tlWOneXP1c1 f ξ) + (tlWOneXP1c2 f ξ + tlWOneXP1c3 f ξ)) +
        ((tlWOneXP1c4 f ξ + tlWOneXP1c5 f ξ) + (tlWOneXP1c6 f ξ + tlWOneXP1c7 f ξ))) +
        (((tlWOneXP1c8 f ξ + tlWOneXP1c9 f ξ) + (tlWOneXP1c10 f ξ + tlWOneXP1c11 f ξ)) +
        ((tlWOneXP1c12 f ξ + tlWOneXP1c13 f ξ) + (tlWOneXP1c14 f ξ + tlWOneXP1c15 f ξ))))
        + tlWOneXP1c16 f ξ := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP2c10, tlTOneP2c11, tlTOneP2c2,
      tlTOneP2c3, tlTOneP2c4, tlTOneP2c5, tlTOneP2c6, tlTOneP2c7, tlTOneP2c8,
      tlTOneP2c9, tlTOneP3c0, tlTOneP3c1, tlTOneP3c10, tlTOneP3c2, tlTOneP3c3,
      tlTOneP3c4, tlTOneP3c5, tlTOneP3c6, tlTOneP3c7, tlTOneP3c8, tlTOneP3c9,
      tlWOneXP1c0, tlWOneXP1c1, tlWOneXP1c10, tlWOneXP1c11, tlWOneXP1c12,
      tlWOneXP1c13, tlWOneXP1c14, tlWOneXP1c15, tlWOneXP1c16, tlWOneXP1c2,
      tlWOneXP1c3, tlWOneXP1c4, tlWOneXP1c5, tlWOneXP1c6, tlWOneXP1c7, tlWOneXP1c8,
      tlWOneXP1c9]
  ring1

lemma tlWOneX_s2 {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    (tlTOneP3c11 f ξ + tlTOneP3c12 f ξ + tlTOneP4c0 f ξ + tlTOneP4c1 f ξ + tlTOneP4c2 f ξ +
      tlTOneP4c3 f ξ + tlTOneP4c4 f ξ + tlTOneP4c5 f ξ + tlTOneP4c6 f ξ + tlTOneP4c7 f ξ +
      tlTOneP4c8 f ξ + tlTOneP4c9 f ξ + tlTOneP4c10 f ξ + tlTOneP4c11 f ξ + tlTOneP4c12 f ξ +
      tlTOneP5c0 f ξ + tlTOneP5c1 f ξ + tlTOneP5c2 f ξ + tlTOneP5c3 f ξ + tlTOneP5c4 f ξ +
      tlTOneP5c5 f ξ) * tlMOneV0 f =
      ((((tlWOneXP2c0 f ξ + tlWOneXP2c1 f ξ) + (tlWOneXP2c2 f ξ + tlWOneXP2c3 f ξ)) +
        ((tlWOneXP2c4 f ξ + tlWOneXP2c5 f ξ) + (tlWOneXP2c6 f ξ + tlWOneXP2c7 f ξ))) +
        (((tlWOneXP2c8 f ξ + tlWOneXP2c9 f ξ) + (tlWOneXP2c10 f ξ + tlWOneXP2c11 f ξ)) +
        ((tlWOneXP2c12 f ξ + tlWOneXP2c13 f ξ) + (tlWOneXP2c14 f ξ + tlWOneXP2c15 f ξ))))
        + ((tlWOneXP2c16 f ξ + tlWOneXP2c17 f ξ) + tlWOneXP2c18 f ξ) := by
  linear_combination (norm := skip)
    0 * hT
  simp only [tlMOneV0, tlT0, tlT1, tlT2, tlT3, tlTOneP3c11, tlTOneP3c12, tlTOneP4c0,
      tlTOneP4c1, tlTOneP4c10, tlTOneP4c11, tlTOneP4c12, tlTOneP4c2, tlTOneP4c3,
      tlTOneP4c4, tlTOneP4c5, tlTOneP4c6, tlTOneP4c7, tlTOneP4c8, tlTOneP4c9,
      tlTOneP5c0, tlTOneP5c1, tlTOneP5c2, tlTOneP5c3, tlTOneP5c4, tlTOneP5c5,
      tlWOneXP2c0, tlWOneXP2c1, tlWOneXP2c10, tlWOneXP2c11, tlWOneXP2c12,
      tlWOneXP2c13, tlWOneXP2c14, tlWOneXP2c15, tlWOneXP2c16, tlWOneXP2c17,
      tlWOneXP2c18, tlWOneXP2c2, tlWOneXP2c3, tlWOneXP2c4, tlWOneXP2c5, tlWOneXP2c6,
      tlWOneXP2c7, tlWOneXP2c8, tlWOneXP2c9]
  ring1


end MazurTorsion.Kubert

end
