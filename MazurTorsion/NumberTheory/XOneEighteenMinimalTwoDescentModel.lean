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
open MazurTorsion.XOneEighteenDescentAlgebraEquiv

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

/-- The displayed element is a root of the minimal completed-square cubic. -/
theorem minimalDescentRootInM_isRoot :
    Polynomial.IsRoot
      (minimalDescentCurve.toAffine.f.map (algebraMap K M))
        minimalDescentRootInM := by
  have hz :
      4 * descentRootInM ^ 3 - 3 * descentRootInM ^ 2 +
          102 * descentRootInM + 5 = 0 := by
    have h := congrArg descentAlgebraEquiv genericRoot_cubic
    simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat,
      descentAlgebraEquiv_genericRoot, map_zero] using h
  have ht4 : t ^ 4 = 3 * t ^ 2 + t := by
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ = 3 * t ^ 2 + t := by rw [t_cubic]; ring
  have ht5 : t ^ 5 = t ^ 2 + 9 * t + 3 := by
    calc
      t ^ 5 = t * t ^ 4 := by ring
      _ = 3 * t ^ 3 + t ^ 2 := by rw [ht4]; ring
      _ = t ^ 2 + 9 * t + 3 := by rw [t_cubic]; ring
  have ht6 : t ^ 6 = 9 * t ^ 2 + 6 * t + 1 := by
    calc
      t ^ 6 = t * t ^ 5 := by ring
      _ = t ^ 3 + 9 * t ^ 2 + 3 * t := by rw [ht5]; ring
      _ = 9 * t ^ 2 + 6 * t + 1 := by rw [t_cubic]; ring
  rw [Polynomial.IsRoot, minimalDescentCurve_f,
    Polynomial.eval_map_algebraMap]
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
  simp only [minimalDescentRootInM, rationalAbscissaTranslation,
    map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg,
    map_div₀,
    show algebraMap K M tau = t by rfl]
  field_simp
  ring_nf
  rw [ht6, ht5, ht4, t_cubic]
  ring_nf
  ring_nf at hz
  linear_combination 2 * hz

private theorem minimalDescentRootInM_adjoin_eq_top :
    IntermediateField.adjoin K {minimalDescentRootInM} = ⊤ := by
  let L : IntermediateField K M :=
    IntermediateField.adjoin K {minimalDescentRootInM}
  have hw : minimalDescentRootInM ∈ L :=
    IntermediateField.mem_adjoin_simple_self K minimalDescentRootInM
  have hz : descentRootInM ∈ L := by
    rw [descentRootInM_eq_minimal]
    exact L.add_mem
      (L.mul_mem (L.natCast_mem 9) hw)
      (L.algebraMap_mem rationalAbscissaTranslation)
  have hs : s ∈ L := by
    rw [← recover_s_in_compositum]
    exact L.div_mem
      (L.add_mem
        (L.sub_mem
          (L.mul_mem (L.natCast_mem 4) (L.pow_mem hz 2))
          (L.mul_mem (L.natCast_mem 11) hz))
        (L.natCast_mem 70))
      (L.natCast_mem 27)
  apply top_unique
  intro x _hx
  have hadjoin :
      Algebra.adjoin K ({s} : Set M) ≤ L.toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
  have hsTop : Algebra.adjoin K ({s} : Set M) = ⊤ := by
    change Algebra.adjoin K
      ({AdjoinRoot.root relativePolynomial} : Set M) = ⊤
    exact AdjoinRoot.adjoinRoot_eq_top
  rw [hsTop] at hadjoin
  exact hadjoin (show x ∈ (⊤ : Subalgebra K M) from trivial)

/-- The minimal completed-square cubic is irreducible over the real cubic
coefficient field. -/
theorem minimalDescentPolynomial_irreducible :
    Irreducible minimalDescentCurve.toAffine.f := by
  have hroot :
      Polynomial.aeval minimalDescentRootInM
        minimalDescentCurve.toAffine.f = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact minimalDescentRootInM_isRoot
  have hdegree : (minpoly K minimalDescentRootInM).natDegree = 3 := by
    have h :=
      (Field.primitive_element_iff_minpoly_natDegree_eq
        K minimalDescentRootInM).mp minimalDescentRootInM_adjoin_eq_top
    simpa only [finrank_M_over_K] using h
  have hint : IsIntegral K minimalDescentRootInM :=
    IsIntegral.of_finite K minimalDescentRootInM
  have hdvd : minpoly K minimalDescentRootInM ∣
      minimalDescentCurve.toAffine.f :=
    minpoly.dvd K minimalDescentRootInM hroot
  have heq : minimalDescentCurve.toAffine.f =
      minpoly K minimalDescentRootInM :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hint) minimalDescentCurve.toAffine.monic_f hdvd (by
        rw [hdegree, minimalDescentCurve.toAffine.natDegree_f])
  rw [heq]
  exact minpoly.irreducible hint

end

end MazurTorsion.XOneEighteenMinimalTwoDescentModel
