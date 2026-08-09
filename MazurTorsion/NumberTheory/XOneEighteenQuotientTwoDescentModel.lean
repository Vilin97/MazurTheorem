/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.X18WeakMordellWeil
import MazurTorsion.EllipticCurve.VariableChange
import MazurTorsion.NumberTheory.XOneEighteenQuotientSevenTorsion
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionNorms

/-!
# A characteristic-not-two model of the `X₁(18)` elliptic quotient

This file puts the real-cubic elliptic quotient into the form used by the
`x-T` two-descent.  Both coordinate changes are genuine admissible changes
of Weierstrass variables, so the resulting point maps are additive
equivalences rather than equation-only substitutions.

The completed two-division cubic is also identified with the explicit
relative cubic algebra used by the arithmetic certificates.  No
Mordell--Weil or Selmer conclusion is asserted here.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

private theorem tau_pow_five : tau ^ 5 = tau ^ 2 + 9 * tau + 3 := by
  calc
    tau ^ 5 = tau * tau ^ 4 := by ring
    _ = tau * (3 * tau ^ 2 + tau) := by rw [tau_pow_four]
    _ = 3 * tau ^ 3 + tau ^ 2 := by ring
    _ = tau ^ 2 + 9 * tau + 3 := by rw [tau_cubic]; ring

private theorem tau_pow_six : tau ^ 6 = 9 * tau ^ 2 + 6 * tau + 1 := by
  calc
    tau ^ 6 = tau * tau ^ 5 := by ring
    _ = tau * (tau ^ 2 + 9 * tau + 3) := by rw [tau_pow_five]
    _ = tau ^ 3 + 9 * tau ^ 2 + 3 * tau := by ring
    _ = 9 * tau ^ 2 + 6 * tau + 1 := by rw [tau_cubic]; ring

/-! ## Admissible point-group equivalences -/

/-- The change whose coordinate formula is
`(X,Y) ↦ (9X+3τ²+3τ-8, 27Y+9X+12τ²+12τ-10)`. -/
def quotientToRationalChange : VariableChange K :=
  VariableChange.mk (Units.mk0 (3 : K) (by norm_num))
    (3 * tau ^ 2 + 3 * tau - 8) 1
    (12 * tau ^ 2 + 12 * tau - 10)

/-- The displayed quotient-to-rational coordinate change is an identity of
Weierstrass curves. -/
theorem quotientToRationalChange_smul :
    quotientToRationalChange • rationalModel = quotientCurve := by
  ext <;>
    norm_num [quotientToRationalChange, rationalModel, quotientCurve,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;>
    ring_nf <;>
    simp only [tau_pow_six, tau_pow_five, tau_pow_four, tau_cubic] <;>
    ring

/-- The characteristic-not-two model used by the `x-T` descent. -/
def descentCurve : WeierstrassCurve K :=
  rationalModel.toCharNeTwoNF • rationalModel

private instance rationalModel_isElliptic : rationalModel.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [rationalModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The completed-square equation has coefficients
`[0,-3/4,0,51/2,5/4]`. -/
theorem descentCurve_eq :
    descentCurve =
      (⟨0, -(3 : K) / 4, 0, (51 : K) / 2, (5 : K) / 4⟩ :
        WeierstrassCurve K) := by
  ext <;>
    norm_num [descentCurve, rationalModel,
      WeierstrassCurve.toCharNeTwoNF,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]

instance descentCurve_isElliptic : descentCurve.IsElliptic := by
  dsimp only [descentCurve]
  infer_instance

instance descentCurve_isCharNeTwoNF : descentCurve.IsCharNeTwoNF := by
  dsimp only [descentCurve]
  infer_instance

/-- Additive equivalence from the original quotient to its
rational-coefficient model. -/
def quotientToRationalEquiv :
    quotientCurve.toAffine.Point ≃+ rationalModel.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivOfEq
      quotientToRationalChange_smul.symm).trans
    (WeierstrassCurve.Affine.Point.equivVariableChange
      rationalModel quotientToRationalChange)

/-- Additive equivalence from the rational-coefficient model to the
completed-square descent model. -/
def rationalToDescentEquiv :
    rationalModel.toAffine.Point ≃+ descentCurve.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivVariableChange
    rationalModel rationalModel.toCharNeTwoNF).symm

/-- The composite point-group equivalence used by the two-descent. -/
def quotientToDescentEquiv :
    quotientCurve.toAffine.Point ≃+ descentCurve.toAffine.Point :=
  quotientToRationalEquiv.trans rationalToDescentEquiv

/-! ## The completed two-division cubic -/

/-- The monic cubic on the right-hand side of the completed-square model. -/
theorem descentCurve_f :
    descentCurve.toAffine.f =
      X ^ 3 - C ((3 : K) / 4) * X ^ 2 +
        C ((51 : K) / 2) * X + C ((5 : K) / 4) := by
  rw [descentCurve_eq]
  change
    X ^ 3 + C (-(3 : K) / 4) * X ^ 2 + C ((51 : K) / 2) * X +
        C ((5 : K) / 4) =
      X ^ 3 - C ((3 : K) / 4) * X ^ 2 + C ((51 : K) / 2) * X +
        C ((5 : K) / 4)
  have hneg : (-(3 : K) / 4) = -((3 : K) / 4) := by ring
  rw [hneg, map_neg]
  ring

/-- The explicit element of the relative cubic algebra corresponding to a
two-division abscissa. -/
def descentRootInM : M :=
  algebraMap K M (1 / 4 : K) * relativeTwoDivisionZ

/-- The explicit relative element is a root of the completed two-division
cubic. -/
theorem descentRootInM_isRoot :
    Polynomial.IsRoot
      (descentCurve.toAffine.f.map (algebraMap K M)) descentRootInM := by
  rw [Polynomial.IsRoot, descentCurve_f]
  rw [Polynomial.eval_map_algebraMap]
  simp only [aeval_add, aeval_sub, aeval_mul, map_pow, aeval_X,
    aeval_C]
  change
    descentRootInM ^ 3 -
        algebraMap K M ((3 : K) / 4) * descentRootInM ^ 2 +
      algebraMap K M ((51 : K) / 2) * descentRootInM +
        algebraMap K M ((5 : K) / 4) = 0
  have hcube :
      algebraMap K M (1 / 4 : K) ^ 3 =
        algebraMap K M (1 / 64 : K) := by
    rw [← map_pow]
    norm_num
  have hquad :
      algebraMap K M ((3 : K) / 4) *
          algebraMap K M (1 / 4 : K) ^ 2 =
        algebraMap K M (1 / 64 : K) * (3 : M) := by
    calc
      _ = algebraMap K M (((3 : K) / 4) * (1 / 4 : K) ^ 2) := by
        rw [← map_pow, ← map_mul]
      _ = algebraMap K M ((1 / 64 : K) * 3) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (3 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (3 : M) := by
        simp only [map_ofNat]
  have hlinear :
      algebraMap K M ((51 : K) / 2) *
          algebraMap K M (1 / 4 : K) =
        algebraMap K M (1 / 64 : K) * (408 : M) := by
    calc
      _ = algebraMap K M (((51 : K) / 2) * (1 / 4 : K)) := by
        rw [← map_mul]
      _ = algebraMap K M ((1 / 64 : K) * 408) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (408 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (408 : M) := by
        simp only [map_ofNat]
  have hconst :
      algebraMap K M ((5 : K) / 4) =
        algebraMap K M (1 / 64 : K) * (80 : M) := by
    calc
      _ = algebraMap K M ((1 / 64 : K) * 80) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (80 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (80 : M) := by
        simp only [map_ofNat]
  simp only [descentRootInM, mul_pow]
  linear_combination
    relativeTwoDivisionZ ^ 3 * hcube -
      relativeTwoDivisionZ ^ 2 * hquad +
      relativeTwoDivisionZ * hlinear + hconst +
      algebraMap K M (1 / 64 : K) * relativeTwoDivisionZ_cubic

end

end MazurTorsion.XOneEighteenQuotientTwoDescentModel
