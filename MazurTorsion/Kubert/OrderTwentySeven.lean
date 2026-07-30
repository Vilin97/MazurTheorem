/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenThirdLeg
import MazurTorsion.Kubert.OrderTwentySevenEndpoint

/-!
# No rational point of order twenty-seven

A point of exact order twenty-seven normalizes into the parametrized
`X₁(9)` Tate family with its triple at the marked origin.  The
trisection certificate places its abscissa on the trisection locus,
which produces a third hauptmodul leg completing the two family legs
to a chain of the Fricke-twisted `X₀(9)` correspondence.  The
classification of that chain leaves only the cusp and the CM point,
and both are impossible for the family legs.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- No rational point of an elliptic curve over `ℚ` has order `27`. -/
theorem no_rational_point_of_order_twentySeven
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P : E.toAffine.Point) :
    addOrderOf P ≠ 27 := by
  intro h27
  obtain ⟨f, u, hf0, hf1, hK, hu, h00, e, heQ, hdisc, hc₄, horder27, h3Q⟩ :=
    orderTwentySeven_family_package E P h27
  cases hEP : e P with
  | zero =>
    rw [hEP] at horder27
    have h1 : addOrderOf (WeierstrassCurve.Affine.Point.zero :
        (tateNormalCurve (nineB f) (nineC f)).toAffine.Point) = 1 :=
      addOrderOf_zero
    rw [h1] at horder27
    exact absurd horder27 (by norm_num)
  | some hQ =>
    rename_i ξ η
    rw [hEP] at horder27 h3Q
    have hT := trisectionPoly_eq_zero_of_three_nsmul f ξ η hQ h00 horder27 h3Q
    obtain ⟨s₃, hG2⟩ := thirdLeg_exists f ξ hf0 hf1 hK hT
    exact legs_chain_impossible f hf0 hf1 hK s₃ hG2

/-- Interface form of the order-27 exclusion on the base-changed model. -/
theorem rationalPoint_addOrderOf_ne_twentySeven
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 27 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  intro hQ
  exact no_rational_point_of_order_twentySeven (E⁄ℚ) Q hQ

end MazurTorsion.Kubert
