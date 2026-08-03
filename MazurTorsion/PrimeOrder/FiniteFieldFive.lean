/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.Mathlib.EllipticCurvePoint
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import MazurTorsion.EllipticCurve.VariableChange

/-!
# The ten-point bound for short Weierstrass models over F_5

The formal-immersion route reduces the prime-order contradiction to a good
elliptic curve over `ZMod 5`.  After short-Weierstrass normalization, there
are only 25 coefficient pairs.  This file checks those models directly rather
than importing a general Hasse theorem.
-/

namespace MazurTorsion.PrimeOrder

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The short Weierstrass equation `y² = x³ + a*x + b` over `F_5`. -/
def shortCurveFive (a b : ZMod 5) : WeierstrassCurve (ZMod 5) :=
  ⟨0, 0, 0, a, b⟩

/-- Every one of the 25 short Weierstrass models over `F_5` has at most ten
nonsingular projective points.  Singular coefficient pairs are harmless here:
`Affine.Point` retains only nonsingular points. -/
theorem card_shortCurveFive_le_ten (a b : ZMod 5) :
    Fintype.card (shortCurveFive a b).toAffine.Point ≤ 10 := by
  fin_cases a <;> fin_cases b <;> decide

/-- Every elliptic Weierstrass equation over `F_5` is point-group equivalent
to one of the 25 enumerated short models, so it has at most ten points. -/
theorem card_reductionAtFive_le_ten
    (W : WeierstrassCurve (ZMod 5)) [W.IsElliptic] :
    Nat.card W.toAffine.Point ≤ 10 := by
  letI : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide)
  letI : Invertible (3 : ZMod 5) := invertibleOfNonzero (by decide)
  let C : WeierstrassCurve.VariableChange (ZMod 5) := W.toShortNF
  let Wshort : WeierstrassCurve (ZMod 5) := C • W
  haveI : Wshort.IsElliptic := inferInstance
  haveI : Wshort.IsShortNF := by
    dsimp only [Wshort, C]
    infer_instance
  have hshort : Wshort = shortCurveFive Wshort.a₄ Wshort.a₆ := by
    ext <;> simp [shortCurveFive]
  let shortEquiv : Wshort.toAffine.Point ≃+
      (shortCurveFive Wshort.a₄ Wshort.a₆).toAffine.Point :=
    WeierstrassCurve.Affine.Point.congr hshort
  calc
    Nat.card W.toAffine.Point = Nat.card Wshort.toAffine.Point :=
      Nat.card_congr
        (WeierstrassCurve.Affine.Point.equivVariableChange W C).symm.toEquiv
    _ = Nat.card (shortCurveFive Wshort.a₄ Wshort.a₆).toAffine.Point :=
      Nat.card_congr shortEquiv.toEquiv
    _ = Fintype.card (shortCurveFive Wshort.a₄ Wshort.a₆).toAffine.Point :=
      Nat.card_eq_fintype_card
    _ ≤ 10 := card_shortCurveFive_le_ten Wshort.a₄ Wshort.a₆

end MazurTorsion.PrimeOrder
