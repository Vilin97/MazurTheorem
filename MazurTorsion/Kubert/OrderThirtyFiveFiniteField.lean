/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.Mathlib.EllipticCurvePoint
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import MazurTorsion.EllipticCurve.VariableChange

/-!
# The eighteen-point bound over F_11 for the order-35 endpoint

The squarefree-level formal-immersion route at auxiliary prime `11` needs only
the concrete inequality `#E(F_11) ≤ 18`.  Short-Weierstrass normalization
reduces this to 121 coefficient pairs, which are checked exhaustively here
instead of importing a general Hasse theorem.
-/

namespace MazurTorsion.OrderThirtyFive

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The short Weierstrass equation `y² = x³ + a*x + b` over `F_11`. -/
def shortCurveEleven (a b : ZMod 11) : WeierstrassCurve (ZMod 11) :=
  ⟨0, 0, 0, a, b⟩

/-- Every short Weierstrass model over `F_11` has at most eighteen
nonsingular projective points. -/
theorem card_shortCurveEleven_le_eighteen (a b : ZMod 11) :
    Fintype.card (shortCurveEleven a b).toAffine.Point ≤ 18 := by
  fin_cases a <;> fin_cases b <;> decide

/-- Every elliptic Weierstrass equation over `F_11` is point-group equivalent
to an enumerated short model, so its point group has at most eighteen
elements. -/
theorem card_reductionAtEleven_le_eighteen
    (W : WeierstrassCurve (ZMod 11)) [W.IsElliptic] :
    Nat.card W.toAffine.Point ≤ 18 := by
  letI : Invertible (2 : ZMod 11) := invertibleOfNonzero (by decide)
  letI : Invertible (3 : ZMod 11) := invertibleOfNonzero (by decide)
  let C : WeierstrassCurve.VariableChange (ZMod 11) := W.toShortNF
  let Wshort : WeierstrassCurve (ZMod 11) := C • W
  haveI : Wshort.IsElliptic := inferInstance
  haveI : Wshort.IsShortNF := by
    dsimp only [Wshort, C]
    infer_instance
  have hshort : Wshort = shortCurveEleven Wshort.a₄ Wshort.a₆ := by
    ext <;> simp [shortCurveEleven]
  let shortEquiv : Wshort.toAffine.Point ≃+
      (shortCurveEleven Wshort.a₄ Wshort.a₆).toAffine.Point :=
    WeierstrassCurve.Affine.Point.congr hshort
  calc
    Nat.card W.toAffine.Point = Nat.card Wshort.toAffine.Point :=
      Nat.card_congr
        (WeierstrassCurve.Affine.Point.equivVariableChange W C).symm.toEquiv
    _ = Nat.card (shortCurveEleven Wshort.a₄ Wshort.a₆).toAffine.Point :=
      Nat.card_congr shortEquiv.toEquiv
    _ = Fintype.card (shortCurveEleven Wshort.a₄ Wshort.a₆).toAffine.Point :=
      Nat.card_eq_fintype_card
    _ ≤ 18 := card_shortCurveEleven_le_eighteen Wshort.a₄ Wshort.a₆

end MazurTorsion.OrderThirtyFive
