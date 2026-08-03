/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFiveFiniteField

/-!
# Rational points of order thirty-five

This module reserves the permanent library destination for the order-35
challenge. A solution belongs here; the published challenge module can then
become a thin, immutable bridge to that theorem.
-/

namespace MazurTorsion.OrderThirtyFive

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The checked `F_11` enumeration rules out a specialized point of exact
order 35.  The remaining rational theorem must construct this point through
the squarefree-level formal-immersion and Néron-specialization route. -/
theorem reductionAtEleven_addOrderOf_ne_thirtyFive
    (W : WeierstrassCurve (ZMod 11)) [W.IsElliptic]
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  intro hP
  have hdvd : addOrderOf P ∣ Nat.card W.toAffine.Point :=
    addOrderOf_dvd_natCard P
  have hle : addOrderOf P ≤ 18 :=
    (Nat.le_of_dvd Nat.card_pos hdvd).trans
      (card_reductionAtEleven_le_eighteen W)
  omega

end MazurTorsion.OrderThirtyFive
