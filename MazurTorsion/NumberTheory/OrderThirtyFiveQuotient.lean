/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.VariableChange
import Mathlib.Tactic.NormNum

/-!
# The fixed elliptic model expected at level 35

The literature identifies the elliptic quotient `X₀(35)/w₅` with the model

`X₀(35)/w₅ : y² + y = x³ + x² + 9x + 1`.

This file only fixes that Weierstrass equation and checks its elementary
arithmetic data.  It does **not** construct the modular curve, the quotient
map by `w₅`, or an isomorphism from that quotient to this model; those remain
separate obligations on the order-35 critical path.  The
translation

`x = X + 1`, `y = Y + 2X + 3`

identifies it with the rational-three-torsion normal form

`Y² + 4XY + 7Y = X³`.

The marked point `(X,Y) = (0,0)`, hence `(x,y) = (1,3)` on the fixed model,
has exact order three.  This is arithmetic input for a prospective
curve-specific three-isogeny descent; it also explains why the existing
two-isogeny descent files are not the right API for this model.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

/-- The fixed rational Weierstrass model expected for `X₀(35)/w₅`.

No modular interpretation is part of this definition. -/
def optimalQuotientModel : WeierstrassCurve ℚ :=
  ⟨0, 1, 1, 9, 1⟩

/-- The integral model underlying `optimalQuotientModel`. -/
def optimalQuotientModelIntegral : WeierstrassCurve ℤ :=
  ⟨0, 1, 1, 9, 1⟩

/-- The discriminant of the selected integral model is `-5³7³`. -/
theorem optimalQuotientModelIntegral_discriminant :
    optimalQuotientModelIntegral.Δ = -42875 := by
  norm_num [optimalQuotientModelIntegral, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The integral and rational definitions are literally compatible. -/
theorem map_optimalQuotientModelIntegral :
    (optimalQuotientModelIntegral.map (algebraMap ℤ ℚ)).toAffine =
      optimalQuotientModel.toAffine := by
  ext <;> simp [optimalQuotientModelIntegral, optimalQuotientModel]

instance optimalQuotientModel_isElliptic : optimalQuotientModel.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [optimalQuotientModel, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The order-three Tate normal form of the fixed model. -/
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

/-- Applying the explicit change to the model gives its order-three
normal form. -/
theorem threeTorsionChange_smul :
    threeTorsionChange • optimalQuotientModel = threeTorsionCurve := by
  ext <;>
    norm_num [WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆,
      threeTorsionChange, optimalQuotientModel, threeTorsionCurve]

/-- The point-group equivalence furnished by the explicit normalization. -/
noncomputable def threeTorsionEquiv :
    threeTorsionCurve.toAffine.Point ≃+
      optimalQuotientModel.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivOfEq
      threeTorsionChange_smul.symm).trans
    (WeierstrassCurve.Affine.Point.equivVariableChange
      optimalQuotientModel threeTorsionChange)

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

/-- The visible rational point `(1,3)` on the fixed model. -/
def modelThreeTorsion : optimalQuotientModel.toAffine.Point :=
  .some 1 3 (by
    apply optimalQuotientModel.toAffine.equation_iff_nonsingular.mp
    norm_num [WeierstrassCurve.Affine.equation_iff,
      optimalQuotientModel])

/-- The normalization sends `(0,0)` to the literal point `(1,3)`. -/
theorem threeTorsionEquiv_origin :
    threeTorsionEquiv threeTorsionOrigin = modelThreeTorsion := by
  rw [threeTorsionEquiv]
  simp only [AddEquiv.trans_apply]
  rw [threeTorsionOrigin]
  rw [WeierstrassCurve.Affine.Point.equivOfEq_some]
  rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
  apply WeierstrassCurve.Affine.Point.some_eq_some optimalQuotientModel
  · norm_num [threeTorsionChange]
  · norm_num [threeTorsionChange]

/-- The visible point `(1,3)` has exact rational order three. -/
theorem addOrderOf_modelThreeTorsion :
    addOrderOf modelThreeTorsion = 3 := by
  rw [← threeTorsionEquiv_origin,
    AddEquiv.addOrderOf_eq threeTorsionEquiv]
  exact addOrderOf_threeTorsionOrigin

end MazurTorsion.OrderThirtyFive
