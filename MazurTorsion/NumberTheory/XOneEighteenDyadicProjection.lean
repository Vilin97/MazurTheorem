/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.ZMod.Basic

/-!
# A scalar dyadic projection certificate for the `X₁(18)` two-descent

The rational two-division cubic occurring in the elliptic quotient of
`X₁(18)` is

`S³ - 3S - 10`.

Its `2`-adic root is congruent to `74` modulo `128`.  After projecting to
this degree-one factor and putting `X = 4(x₀ - α)`, the completed-square
equation is

`Y² = X (X² + aX + b)`,

where

`a = 9(S² - 2S - 2)` and `b = 81(S² + 2S - 7)`.

This file records the scalar finite, kernel-checked part of the local
calculation.  Modulo `128`, every scalar solution has square `X`-coordinate.
The proof uses ordinary kernel reduction and no external computation.

The dyadic completion of the real cubic field has residue degree three, so
the passage from a local point to this scalar certificate requires additional
work: either a proof that the relevant coordinates lie in the scalar
subfield, or a corresponding certificate in the cubic residue ring.  No such
bridge is postulated here.
-/

namespace MazurTorsion.XOneEighteenDyadicProjection

/-- The degree-one root of `S³ - 3S - 10` modulo `2⁷`. -/
def rootMod128 : ZMod 128 := 74

/-- The first normalized coefficient as a function of a cubic root. -/
def coeffAAt (S : ZMod 128) : ZMod 128 := 9 * (S ^ 2 - 2 * S - 2)

/-- The second normalized coefficient as a function of a cubic root. -/
def coeffBAt (S : ZMod 128) : ZMod 128 := 81 * (S ^ 2 + 2 * S - 7)

/-- The projected coefficient `9(S² - 2S - 2)` modulo `2⁷`. -/
def coeffA : ZMod 128 := coeffAAt rootMod128

/-- The projected coefficient `81(S² + 2S - 7)` modulo `2⁷`. -/
def coeffB : ZMod 128 := coeffBAt rootMod128

/-- The chosen residue is a root of the rational two-division cubic. -/
theorem rootMod128_cubic :
    rootMod128 ^ 3 - 3 * rootMod128 - 10 = 0 := by
  decide

/-- The first normalized coefficient is `62` modulo `128`. -/
theorem coeffA_eq : coeffA = 62 := by
  decide

/-- The second normalized coefficient is `65` modulo `128`. -/
theorem coeffB_eq : coeffB = 65 := by
  decide

/--
Every scalar solution of the normalized curve modulo `2⁷` has square first
coordinate.  Lean's kernel checks the complete finite search.
-/
theorem integral_projection_mod128 :
    ∀ X Y : ZMod 128,
      Y ^ 2 = X * (X ^ 2 + coeffA * X + coeffB) →
        ∃ Z : ZMod 128, Z ^ 2 = X := by
  decide +kernel

end MazurTorsion.XOneEighteenDyadicProjection
