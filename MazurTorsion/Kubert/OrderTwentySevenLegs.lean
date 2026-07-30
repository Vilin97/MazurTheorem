/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenReduction

/-!
# The first two hauptmodul legs of the order-twenty-seven tower

On the parametrized `X₁(9)` family the marked subgroup chain produces
`t₃`-hauptmodul values for the curve and its Vélu quotient:

`a₁leg = (f²-f+1)³(f³-6f²+3f+1)/(f³(f-1)³)`,
`a₂leg = (f³-6f²+3f+1)³/(f(f-1)(f²-f+1)³)`.

Both satisfy cleared `j`-identities against their curves, and the pair
satisfies the Fricke-twisted `X₀(9)` fibre relation `G9F`.  Every
identity in this file is a literal polynomial identity, verified by
`ring` after clearing.
-/

namespace MazurTorsion.Kubert

/-- The Fricke-twisted `X₀(9)` correspondence polynomial. -/
def orderNineG9F (s B : ℚ) : ℚ :=
  s ^ 2 * B ^ 3 + 36 * s ^ 2 * B ^ 2 + 270 * s ^ 2 * B - s ^ 3 +
    729 * s * B ^ 2 + 26244 * s * B + 531441 * B

/-- Numerator of the first hauptmodul leg. -/
def a1legN (f : ℚ) : ℚ :=
  (f ^ 2 - f + 1) ^ 3 * (f ^ 3 - 6 * f ^ 2 + 3 * f + 1)

/-- Denominator of the first hauptmodul leg. -/
def a1legD (f : ℚ) : ℚ := f ^ 3 * (f - 1) ^ 3

/-- Numerator of the second hauptmodul leg. -/
def a2legN (f : ℚ) : ℚ := (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3

/-- Denominator of the second hauptmodul leg. -/
def a2legD (f : ℚ) : ℚ := f * (f - 1) * (f ^ 2 - f + 1) ^ 3

/-- The Vélu quotient of the family curve by the marked three-subgroup. -/
def orderNineQuotient (f : ℚ) : WeierstrassCurve ℚ :=
  ⟨1 - nineC f, -nineB f, -nineB f,
    -5 * f ^ 3 * (f - 1) ^ 3 * (f ^ 3 - 3 * f ^ 2 + 1),
    -(f ^ 3 * (f - 1) ^ 3 *
      (f ^ 9 - 9 * f ^ 8 + 27 * f ^ 7 - 22 * f ^ 6 - 19 * f ^ 5 +
        33 * f ^ 4 - 9 * f ^ 3 - 4 * f ^ 2 + 1))⟩

/-- The discriminant of the quotient family. -/
theorem orderNineQuotient_Δ (f : ℚ) :
    (orderNineQuotient f).Δ =
      f ^ 3 * (f - 1) ^ 3 * (f ^ 2 - f + 1) ^ 9 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) ^ 3 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, orderNineQuotient,
    nineB, nineC]
  ring

/-- The invariant `c₄` of the quotient family. -/
theorem orderNineQuotient_c₄ (f : ℚ) :
    (orderNineQuotient f).c₄ =
      (f ^ 3 - 3 * f ^ 2 + 1) * (f ^ 3 + 3 * f ^ 2 - 6 * f + 1) *
        (f ^ 6 - 12 * f ^ 5 + 69 * f ^ 4 - 88 * f ^ 3 +
          24 * f ^ 2 + 6 * f + 1) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    orderNineQuotient, nineB, nineC]
  ring

/-- Cleared `j`-identity of the first leg against the family curve. -/
theorem a1leg_hauptmodul_identity (f : ℚ) :
    (a1legN f + 27 * a1legD f) * (a1legN f + 3 * a1legD f) ^ 3 *
        (tateNormalCurve (nineB f) (nineC f)).Δ =
      (tateNormalCurve (nineB f) (nineC f)).c₄ ^ 3 *
        (a1legN f * a1legD f ^ 3) := by
  rw [orderNine_Δ, orderNine_c₄]
  simp only [a1legN, a1legD]
  ring

/-- Cleared `j`-identity of the second leg against the quotient curve. -/
theorem a2leg_hauptmodul_identity (f : ℚ) :
    (a2legN f + 27 * a2legD f) * (a2legN f + 3 * a2legD f) ^ 3 *
        (orderNineQuotient f).Δ =
      (orderNineQuotient f).c₄ ^ 3 *
        (a2legN f * a2legD f ^ 3) := by
  rw [orderNineQuotient_Δ, orderNineQuotient_c₄]
  simp only [a2legN, a2legD]
  ring

/-- The two legs satisfy the cleared Fricke-twisted `X₀(9)` relation. -/
theorem legs_G9F_relation (f : ℚ) :
    a1legN f ^ 2 * a1legD f * a2legN f ^ 3 +
        36 * a1legN f ^ 2 * a1legD f * a2legN f ^ 2 * a2legD f +
        270 * a1legN f ^ 2 * a1legD f * a2legN f * a2legD f ^ 2 -
        a1legN f ^ 3 * a2legD f ^ 3 +
        729 * a1legN f * a1legD f ^ 2 * a2legN f ^ 2 * a2legD f +
        26244 * a1legN f * a1legD f ^ 2 * a2legN f * a2legD f ^ 2 +
        531441 * a1legD f ^ 3 * a2legN f * a2legD f ^ 2 = 0 := by
  simp only [a1legN, a1legD, a2legN, a2legD]
  ring

end MazurTorsion.Kubert
