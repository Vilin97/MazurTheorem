/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.Examples.ExceptionalCubicReduction
import MazurTorsion.NumberTheory.ExceptionalCubicDescent

/-!
# Closing the exceptional cubic by reduction modulo five

The elementary two-descent in `ExceptionalCubicDescent` proves that the
rational point group of

`y² = x³ + 2x² - 3x`

is finite.  The exact-pin reduction infrastructure proves that reduction
modulo five is injective on that finite group and that the reduced curve has
eight points.  This file joins those independent results and closes the
exceptional cubic classification used to exclude `ZMod 2 × ZMod 12`.
-/

namespace MazurTorsion.ExceptionalCubic

/-- The exceptional cubic has at most eight rational points. -/
theorem point_card_le_eight :
    Nat.card curve.toAffine.Point ≤ 8 := by
  letI : Finite ExceptionalCubicReduction.curve.Point := by
    change Finite curve.toAffine.Point
    exact point_finite
  change Nat.card ExceptionalCubicReduction.curve.Point ≤ 8
  exact ExceptionalCubicReduction.point_card_le_eight

/-- The exceptional cubic has only the eight explicitly listed rational
points needed by the `ZMod 2 × ZMod 12` obstruction. -/
theorem exceptionalCubicIsTrivial :
    MazurTorsion.ExceptionalCubicIsTrivial := by
  letI : Finite curve.toAffine.Point := point_finite
  exact exceptionalCubicIsTrivial_of_point_card_le_eight point_card_le_eight

end MazurTorsion.ExceptionalCubic
