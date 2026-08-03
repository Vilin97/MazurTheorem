/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.VariableChange
import Mathlib.Tactic.NormNum

/-!
# The fixed elliptic quotient used at level 35

The squarefree-level formal-immersion argument uses the elliptic quotient

`X₀(35)/w₅ : y² + y = x³ + x² + 9x + 1`.

This file fixes that model and checks its elementary arithmetic data.  The
translation

`x = X + 1`, `y = Y + 2X + 3`

identifies it with the rational-three-torsion normal form

`Y² + 4XY + 7Y = X³`.

The marked point `(X,Y) = (0,0)`, hence `(x,y) = (1,3)` on the selected
quotient, has exact order three.  This is the input for the curve-specific
three-isogeny descent; it also explains why the existing two-isogeny descent
files are not the right API for this quotient.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

/-- The fixed rational model of the optimal quotient `X₀(35)/w₅`. -/
def optimalQuotient : WeierstrassCurve ℚ :=
  ⟨0, 1, 1, 9, 1⟩

/-- The integral model underlying `optimalQuotient`. -/
def optimalQuotientIntegral : WeierstrassCurve ℤ :=
  ⟨0, 1, 1, 9, 1⟩

/-- The discriminant of the selected integral model is `-5³7³`. -/
theorem optimalQuotientIntegral_discriminant :
    optimalQuotientIntegral.Δ = -42875 := by
  norm_num [optimalQuotientIntegral, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The integral and rational definitions are literally compatible. -/
theorem map_optimalQuotientIntegral :
    (optimalQuotientIntegral.map (algebraMap ℤ ℚ)).toAffine =
      optimalQuotient.toAffine := by
  ext <;> simp [optimalQuotientIntegral, optimalQuotient]

instance optimalQuotient_isElliptic : optimalQuotient.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [optimalQuotient, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The order-three Tate normal form of the fixed quotient. -/
def threeTorsionCurve : WeierstrassCurve ℚ :=
  ⟨4, 0, 7, 0, 0⟩

instance threeTorsionCurve_isElliptic : threeTorsionCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [threeTorsionCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The admissible change `x = X+1`, `y = Y+2X+3`. -/
def threeTorsionChange : WeierstrassCurve.VariableChange ℚ :=
  WeierstrassCurve.VariableChange.mk 1 1 2 3

/-- Applying the explicit change to the quotient gives its order-three
normal form. -/
theorem threeTorsionChange_smul :
    threeTorsionChange • optimalQuotient = threeTorsionCurve := by
  ext <;>
    norm_num [WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆,
      threeTorsionChange, optimalQuotient, threeTorsionCurve]

/-- The point-group equivalence furnished by the explicit normalization. -/
noncomputable def threeTorsionEquiv :
    threeTorsionCurve.toAffine.Point ≃+
      optimalQuotient.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivOfEq
      threeTorsionChange_smul.symm).trans
    (WeierstrassCurve.Affine.Point.equivVariableChange
      optimalQuotient threeTorsionChange)

private theorem threeTorsionOrigin_nonsingular :
    threeTorsionCurve.toAffine.Nonsingular 0 0 := by
  apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff,
    threeTorsionCurve]

/-- The marked origin on the order-three normal form. -/
def threeTorsionOrigin : threeTorsionCurve.toAffine.Point :=
  .some 0 0 threeTorsionOrigin_nonsingular

private theorem double_threeTorsionOrigin :
    (2 : ℕ) • threeTorsionOrigin = -threeTorsionOrigin := by
  simp only [two_nsmul, threeTorsionOrigin]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne]
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · norm_num [WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.slope,
        WeierstrassCurve.Affine.negY, threeTorsionCurve]
    · norm_num [WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.slope,
        WeierstrassCurve.Affine.negY, threeTorsionCurve]
  · norm_num [WeierstrassCurve.Affine.negY, threeTorsionCurve]

private theorem three_nsmul_threeTorsionOrigin :
    (3 : ℕ) • threeTorsionOrigin = 0 := by
  calc
    (3 : ℕ) • threeTorsionOrigin =
        threeTorsionOrigin + (2 : ℕ) • threeTorsionOrigin := by abel
    _ = threeTorsionOrigin + -threeTorsionOrigin := by
      rw [double_threeTorsionOrigin]
    _ = 0 := add_neg_cancel _

/-- The marked origin has exact additive order three. -/
theorem addOrderOf_threeTorsionOrigin :
    addOrderOf threeTorsionOrigin = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply addOrderOf_eq_prime three_nsmul_threeTorsionOrigin
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The visible rational point `(1,3)` on the selected quotient. -/
def quotientThreeTorsion : optimalQuotient.toAffine.Point :=
  .some 1 3 (by
    apply optimalQuotient.toAffine.equation_iff_nonsingular.mp
    norm_num [WeierstrassCurve.Affine.equation_iff,
      optimalQuotient])

/-- The normalization sends `(0,0)` to the literal point `(1,3)`. -/
theorem threeTorsionEquiv_origin :
    threeTorsionEquiv threeTorsionOrigin = quotientThreeTorsion := by
  rw [threeTorsionEquiv]
  simp only [AddEquiv.trans_apply]
  rw [threeTorsionOrigin]
  rw [WeierstrassCurve.Affine.Point.equivOfEq_some]
  rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
  apply WeierstrassCurve.Affine.Point.some_eq_some optimalQuotient
  · norm_num [threeTorsionChange]
  · norm_num [threeTorsionChange]

/-- The visible point `(1,3)` has exact rational order three. -/
theorem addOrderOf_quotientThreeTorsion :
    addOrderOf quotientThreeTorsion = 3 := by
  rw [← threeTorsionEquiv_origin,
    AddEquiv.addOrderOf_eq threeTorsionEquiv]
  exact addOrderOf_threeTorsionOrigin

end MazurTorsion.OrderThirtyFive
