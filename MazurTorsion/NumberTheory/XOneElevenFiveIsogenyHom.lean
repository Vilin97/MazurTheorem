/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneElevenFiveIsogeny

/-!
# Group-law boundaries for the explicit five-isogenies on `X₁(11)`

This file records the group-law pieces of the explicit Vélu and dual maps
that follow without the full two-point addition calculation.  Both maps
commute with negation.  The dual map has trivial rational kernel, while the
kernel of the Vélu map is exactly the rational subgroup killed by five.

The binary addition laws remain the acceptance boundary before either map
is packaged as an `AddMonoidHom`.
-/

open WeierstrassCurve

namespace MazurTorsion.XOneEleven

open WeierstrassCurve.Affine

/-- The dual ordinate formula commutes with the Weierstrass negations. -/
theorem dualFiveY_neg (X Y : ℚ) :
    dualFiveY X (fiveIsogenousCurve.toAffine.negY X Y) =
      curve.toAffine.negY (dualFiveX X) (dualFiveY X Y) := by
  simp only [dualFiveY, WeierstrassCurve.Affine.negY,
    fiveIsogenousCurve, curve]
  ring

/-- The total dual point map commutes with negation. -/
theorem dualFiveMap_neg (P : fiveIsogenousCurve.toAffine.Point) :
    dualFiveMap (-P) = -dualFiveMap P := by
  cases P with
  | zero => rfl
  | some X Y hP =>
      simp only [Point.neg_some, dualFiveMap, dualFivePoint,
        Point.some.injEq]
      exact ⟨trivial, dualFiveY_neg X Y⟩

/-- No nonidentity rational point lies in the kernel of the dual map. -/
theorem dualFiveMap_eq_zero_iff
    (P : fiveIsogenousCurve.toAffine.Point) :
    dualFiveMap P = 0 ↔ P = 0 := by
  cases P with
  | zero =>
      constructor
      · intro _
        rfl
      · intro _
        exact dualFiveMap_zero
  | some X Y hP =>
      simp only [dualFiveMap, dualFivePoint, Point.some_ne_zero]

/-- The Vélu ordinate formula commutes with the Weierstrass negations away
from its kernel poles. -/
theorem veluFiveY_neg (x y : ℚ) :
    veluFiveY x (curve.toAffine.negY x y) =
      fiveIsogenousCurve.toAffine.negY (veluFiveX x) (veluFiveY x y) := by
  simp only [veluFiveY, WeierstrassCurve.Affine.negY,
    fiveIsogenousCurve, curve]
  ring

/-- The total Vélu point map commutes with negation. -/
theorem veluFiveMap_neg (P : curve.toAffine.Point) :
    veluFiveMap (-P) = -veluFiveMap P := by
  cases P with
  | zero => rfl
  | some x y hP =>
      by_cases hx : x = 0 ∨ x = 1
      · simp [veluFiveMap, hx]
      · simp only [Point.neg_some, veluFiveMap, dif_neg hx,
          veluFivePoint, Point.some.injEq]
        exact ⟨trivial, veluFiveY_neg x y⟩

/-- The kernel of the total Vélu map is exactly the rational subgroup killed
by five.  This uses the checked multiplication-by-five composition and the
trivial rational kernel of the dual map, but not an unproved additivity law. -/
theorem veluFiveMap_eq_zero_iff_five_nsmul
    (P : curve.toAffine.Point) :
    veluFiveMap P = 0 ↔ (5 : ℕ) • P = 0 := by
  constructor
  · intro hP
    rw [← dualFiveMap_veluFiveMap P, hP, dualFiveMap_zero]
  · intro hP
    apply (dualFiveMap_eq_zero_iff (veluFiveMap P)).mp
    rw [dualFiveMap_veluFiveMap, hP]

end MazurTorsion.XOneEleven
