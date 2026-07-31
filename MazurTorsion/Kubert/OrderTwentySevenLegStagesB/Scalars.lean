/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Trisection and branch scalar identities

The scalar identities used by the order-twenty-seven kernel calculation.
-/

namespace MazurTorsion.Kubert

lemma trisection_chunks {f ξ : ℚ} (hT : trisectionPoly f ξ = 0) :
    (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0 := by
  simp only [trisectionPoly] at hT
  simp only [tlT0, tlT1, tlT2, tlT3]
  linear_combination hT

lemma tl_brM2 (f : ℚ) :
    tlMTwoV0 f = -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1)) := by
  simp only [tlMTwoV0]
  ring1

lemma tl_brM1 (f : ℚ) :
    tlMOneV0 f =
      -(3 * f * (f - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4
        - 145 * f ^ 3 + 76 * f ^ 2 - 26 * f + 3)) := by
  simp only [tlMOneV0]
  ring1

lemma tl_brM0 (f : ℚ) :
    tlMZeroV0 f =
      -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105 * f ^ 11 + 4341 *
        f ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312 * f ^ 5 + 2713 *
        f ^ 4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) := by
  simp only [tlMZeroV0]
  ring1


end MazurTorsion.Kubert
