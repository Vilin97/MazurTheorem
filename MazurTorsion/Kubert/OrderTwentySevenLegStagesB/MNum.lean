/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumOne
import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumTwo
import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumThree
import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.MNumFour
import MazurTorsion.Kubert.OrderTwentySevenLegStagesB.Zero

/-!
# The combined kernel numerator

The four numerator terms combined using the aggregate zero identity.
-/

namespace MazurTorsion.Kubert

lemma tl_mnum {f ξ : ℚ} (hT : (tlT0 f ξ + tlT1 f ξ) + (tlT2 f ξ + tlT3 f ξ) = 0) :
    ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 3 + -(3 * f * (f - 1) ^ 2 * (f ^ 2 + f - 1))
      * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) ^ 2 * (tlD0 f ξ + tlD1 f ξ) + -(3 * f * (f
      - 1) * (3 * f ^ 9 - f ^ 8 - 26 * f ^ 7 + 94 * f ^ 6 - 168 * f ^ 5 + 187 * f ^ 4 - 145 * f ^
      3 + 76 * f ^ 2 - 26 * f + 3)) * ((tlN0 f ξ + tlN1 f ξ) + (tlN2 f ξ + tlN3 f ξ)) * (tlD0 f ξ
      + tlD1 f ξ) ^ 2 + -(f * (f - 1) * (f ^ 15 + 24 * f ^ 14 - 191 * f ^ 13 + 768 * f ^ 12 - 2105
      * f ^ 11 + 4341 * f ^ 10 - 7010 * f ^ 9 + 9075 * f ^ 8 - 9491 * f ^ 7 + 7985 * f ^ 6 - 5312
      * f ^ 5 + 2713 * f ^ 4 - 1020 * f ^ 3 + 259 * f ^ 2 - 39 * f + 1)) * (tlD0 f ξ + tlD1 f ξ) ^
      3 = 0 := by
  rw [tl_mnum₁ hT, tl_mnum₂ hT, tl_mnum₃ hT, tl_mnum₄ hT]
  exact tl_zero f ξ


end MazurTorsion.Kubert
