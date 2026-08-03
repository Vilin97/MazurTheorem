/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.PrimeOrder.FiniteFieldFive

/-!
# Point-order consequences of the finite-field-five enumeration

This file is the first downstream consumer of
`PrimeOrder.card_reductionAtFive_le_ten`.  It translates the checked finite
enumeration into the point-order contradiction required after prime-to-five
torsion specialization.
-/

namespace MazurTorsion.PrimeOrder

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The finite enumeration bounds the additive order of every point on a
nonsingular short model. -/
theorem shortCurveFive_addOrderOf_le_ten (a b : ZMod 5)
    [(shortCurveFive a b).IsElliptic]
    (P : (shortCurveFive a b).toAffine.Point) :
    addOrderOf P ≤ 10 := by
  have hdvd : addOrderOf P ∣ Nat.card (shortCurveFive a b).toAffine.Point :=
    addOrderOf_dvd_natCard P
  calc
    addOrderOf P ≤ Nat.card (shortCurveFive a b).toAffine.Point :=
      Nat.le_of_dvd Nat.card_pos hdvd
    _ = Fintype.card (shortCurveFive a b).toAffine.Point :=
      Nat.card_eq_fintype_card
    _ ≤ 10 := card_shortCurveFive_le_ten a b

/-- A short elliptic model over `F_5` has no point whose exact order is at
least eleven. -/
theorem shortCurveFive_addOrderOf_ne_of_eleven_le (a b : ZMod 5)
    [(shortCurveFive a b).IsElliptic]
    (P : (shortCurveFive a b).toAffine.Point) (N : ℕ) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hle := shortCurveFive_addOrderOf_le_ten a b P
  omega

/-- No point on an elliptic curve over `F_5` has additive order at least
eleven.  The prime-order callback will obtain precisely such a point from
Néron specialization. -/
theorem zmod_five_addOrderOf_ne_of_eleven_le
    (W : WeierstrassCurve (ZMod 5)) [W.IsElliptic]
    (P : W.toAffine.Point) (N : ℕ) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hdvd : addOrderOf P ∣ Nat.card W.toAffine.Point :=
    addOrderOf_dvd_natCard P
  have hle : addOrderOf P ≤ 10 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans
      (card_reductionAtFive_le_ten W)
  omega

end MazurTorsion.PrimeOrder
