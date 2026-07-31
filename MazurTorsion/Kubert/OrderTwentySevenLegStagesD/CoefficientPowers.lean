/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegChunks

/-!
# Third-leg coefficient power identities

The four coefficient identities that express the cleared correspondence coefficients
in terms of the family parameter.
-/

namespace MazurTorsion.Kubert

lemma zl_brC3 (f : ℚ) :
    zlCThree0 f =
      ((f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3)) := by
  simp only [zlCThree0]
  ring1

lemma zl_brC2 (f : ℚ) :
    zlCTwo0 f =
      (36 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 729 * (f ^
        3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2) := by
  simp only [zlCTwo0]
  ring1

lemma zl_brC1 (f : ℚ) :
    zlCOne0 f =
      (270 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 6 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) + 26244 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 * (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 2 + 531441 *
        (f * (f - 1) * (f ^ 2 - f + 1) ^ 3) ^ 3) := by
  simp only [zlCOne0]
  ring1

lemma zl_brC0 (f : ℚ) :
    zlCZero0 f =
      (-(f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 9) := by
  simp only [zlCZero0]
  ring1

end MazurTorsion.Kubert
