/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFiveFiniteField

/-!
# Point-order consequences of the finite-field-eleven enumeration

This file is the point-level consumer of the exhaustive 121-model
enumeration in `OrderThirtyFiveFiniteField`.  It turns the checked bound
`#E(F_11) ≤ 18` into the exact local obstruction used by the order-35
formal-immersion route.  No modular interpretation of the fixed quotient
model is asserted here.
-/

namespace MazurTorsion.OrderThirtyFive

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Every point on an elliptic short Weierstrass model over `F_11` has
additive order at most eighteen. -/
theorem shortCurveEleven_addOrderOf_le_eighteen (a b : ZMod 11)
    [(shortCurveEleven a b).IsElliptic]
    (P : (shortCurveEleven a b).toAffine.Point) :
    addOrderOf P ≤ 18 := by
  have hdvd : addOrderOf P ∣
      Nat.card (shortCurveEleven a b).toAffine.Point :=
    addOrderOf_dvd_natCard P
  calc
    addOrderOf P ≤ Nat.card (shortCurveEleven a b).toAffine.Point :=
      Nat.le_of_dvd Nat.card_pos hdvd
    _ = Fintype.card (shortCurveEleven a b).toAffine.Point :=
      Nat.card_eq_fintype_card
    _ ≤ 18 := card_shortCurveEleven_le_eighteen a b

/-- An elliptic short model over `F_11` has no point whose exact order is at
least nineteen. -/
theorem shortCurveEleven_addOrderOf_ne_of_nineteen_le (a b : ZMod 11)
    [(shortCurveEleven a b).IsElliptic]
    (P : (shortCurveEleven a b).toAffine.Point)
    (N : ℕ) (hN : 19 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hle := shortCurveEleven_addOrderOf_le_eighteen a b P
  omega

/-- The exhaustive normalization-and-enumeration certificate bounds the
additive order of every point on every elliptic curve over `F_11`. -/
theorem zmod_eleven_addOrderOf_le_eighteen
    (W : WeierstrassCurve (ZMod 11)) [W.IsElliptic]
    (P : W.toAffine.Point) :
    addOrderOf P ≤ 18 := by
  have hdvd : addOrderOf P ∣ Nat.card W.toAffine.Point :=
    addOrderOf_dvd_natCard P
  exact (Nat.le_of_dvd Nat.card_pos hdvd).trans
    (card_reductionAtEleven_le_eighteen W)

/-- No point on an elliptic curve over `F_11` has additive order at least
nineteen. -/
theorem zmod_eleven_addOrderOf_ne_of_nineteen_le
    (W : WeierstrassCurve (ZMod 11)) [W.IsElliptic]
    (P : W.toAffine.Point) (N : ℕ) (hN : 19 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hle := zmod_eleven_addOrderOf_le_eighteen W P
  omega

/-- In particular, the finite-field certificate rules out a specialized
point of exact order 35. -/
theorem zmod_eleven_addOrderOf_ne_thirtyFive
    (W : WeierstrassCurve (ZMod 11)) [W.IsElliptic]
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  zmod_eleven_addOrderOf_ne_of_nineteen_le W P 35 (by omega)

end MazurTorsion.OrderThirtyFive
