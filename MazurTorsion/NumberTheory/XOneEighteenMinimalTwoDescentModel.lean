/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenDescentAlgebraEquiv
import MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes

/-!
# A dyadic-support two-descent model for the `X₁(18)` quotient

The rational-coefficient model used for explicit two-division arithmetic is
obtained from the original real-cubic quotient by a change with scale `3`.
It is consequently nonminimal at the primes above `3`.  For the global
Selmer containment we instead complete the square directly on the original
quotient, whose discriminant is `-2`.

The abscissas on the two completed-square models are related by

`z = 9 w + 3τ² + 3τ - 8`.

Thus the new cubic algebra is the same explicit degree-nine compositum, but
its bad-prime support is genuinely dyadic.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenMinimalTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

/-- The completed-square model of the original discriminant-`-2` quotient. -/
def minimalDescentCurve : WeierstrassCurve K :=
  quotientCurve.toCharNeTwoNF • quotientCurve

/-- Exact coefficients of the minimal completed-square model. -/
theorem minimalDescentCurve_eq :
    minimalDescentCurve =
      (⟨0, tau ^ 2 + tau - (11 : K) / 4, 0,
          (-tau ^ 2 + tau + 7) / 2,
          (2 * tau ^ 2 + tau - 5) / 4⟩ : WeierstrassCurve K) := by
  ext
  all_goals
    norm_num [minimalDescentCurve, quotientCurve,
      WeierstrassCurve.toCharNeTwoNF,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  all_goals ring_nf
  all_goals simp only [tau_pow_four, tau_cubic]
  all_goals ring

instance minimalDescentCurve_isElliptic : minimalDescentCurve.IsElliptic := by
  dsimp only [minimalDescentCurve]
  infer_instance

instance minimalDescentCurve_isCharNeTwoNF :
    minimalDescentCurve.IsCharNeTwoNF := by
  dsimp only [minimalDescentCurve]
  infer_instance

/-- The original quotient and the minimal completed-square model have
additively equivalent affine point groups. -/
def quotientToMinimalDescentEquiv :
    quotientCurve.toAffine.Point ≃+ minimalDescentCurve.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivVariableChange
    quotientCurve quotientCurve.toCharNeTwoNF).symm

/-- The monic cubic for the minimal completed-square model. -/
theorem minimalDescentCurve_f :
    minimalDescentCurve.toAffine.f =
      X ^ 3 + C (tau ^ 2 + tau - (11 : K) / 4) * X ^ 2 +
        C ((-tau ^ 2 + tau + 7) / 2) * X +
          C ((2 * tau ^ 2 + tau - 5) / 4) := by
  rw [minimalDescentCurve_eq]

/-- The minimal cubic has discriminant `-1/8`; in particular its only bad
rational support is dyadic. -/
theorem minimalDescentCurve_discr_f :
    minimalDescentCurve.toAffine.f.discr = -(1 : K) / 8 := by
  have hdelta : minimalDescentCurve.Δ = -2 := by
    rw [minimalDescentCurve, WeierstrassCurve.variableChange_Δ,
      quotientCurve_discriminant]
    norm_num [WeierstrassCurve.toCharNeTwoNF]
  rw [minimalDescentCurve.toAffine.Δ_eq_discr_f] at hdelta
  calc
    minimalDescentCurve.toAffine.f.discr =
        (1 / 16 : K) * (16 * minimalDescentCurve.toAffine.f.discr) := by
          field_simp
    _ = (1 / 16 : K) * (-2) := by rw [hdelta]
    _ = -(1 : K) / 8 := by norm_num

/-- Translation term in the scale-three change from the original quotient
to the rational-coefficient model. -/
def rationalAbscissaTranslation : K :=
  3 * tau ^ 2 + 3 * tau - 8

/-- The root of the minimal cubic in the explicit compositum. -/
def minimalDescentRootInM : M :=
  (descentRootInM - algebraMap K M rationalAbscissaTranslation) / 9

/-- The affine root change is reversible. -/
theorem descentRootInM_eq_minimal :
    descentRootInM =
      9 * minimalDescentRootInM +
        algebraMap K M rationalAbscissaTranslation := by
  simp only [minimalDescentRootInM]
  field_simp
  ring

end

end MazurTorsion.XOneEighteenMinimalTwoDescentModel
