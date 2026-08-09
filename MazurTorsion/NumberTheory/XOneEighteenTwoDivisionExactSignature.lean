/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSignature
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionDiscriminant

/-!
# The exact signature of the `X₁(18)` two-division compositum

The compositum has degree nine, at most three real places, and an odd
number of complex places.  The signature identity

`r₁ + 2 r₂ = 9`

then forces `(r₁, r₂) = (3, 3)`.
-/

open Module NumberField NumberField.InfinitePlace

namespace MazurTorsion.XOneEighteenTwoDivisionExactSignature

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSignature
open MazurTorsion.XOneEighteenTwoDivisionDiscriminant

private theorem exact_signature :
    nrRealPlaces M = 3 ∧ nrComplexPlaces M = 3 := by
  have hsignature := card_add_two_mul_card_eq_rank (K := M)
  rw [finrank_M_over_rat] at hsignature
  have hreal := nrRealPlaces_le_three
  obtain ⟨k, hk⟩ := nrComplexPlaces_odd
  constructor <;> omega

/-- The degree-nine compositum has exactly three real places. -/
theorem nrRealPlaces_eq_three : nrRealPlaces M = 3 :=
  exact_signature.1

/-- The degree-nine compositum has exactly three pairs of complex places. -/
theorem nrComplexPlaces_eq_three : nrComplexPlaces M = 3 :=
  exact_signature.2

end

end MazurTorsion.XOneEighteenTwoDivisionExactSignature
