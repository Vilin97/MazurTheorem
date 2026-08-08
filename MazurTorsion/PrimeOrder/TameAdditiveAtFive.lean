/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.NonsingularReductionAdditive
import MazurTorsion.EllipticCurve.CuspidalReduction
import MazurTorsion.EllipticCurve.MinimalModelScaling
import MazurTorsion.EllipticCurve.TateStarDepthFour
import MazurTorsion.EllipticCurve.TateResidueTranslation
import MazurTorsion.EllipticCurve.TameAdditiveFiltration
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Tactic.NormNum

/-!
# The tame additive contradiction at residue characteristic five

This is the prime-route consumer of the algebraic Néron filtration boundary.
It remains conditional on construction of that filtration from the actual
local elliptic curve.
-/

namespace MazurTorsion.PrimeOrder

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum

universe u v

noncomputable local instance : DecidableEq
    (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

section ReductionType

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Named additive-reduction consumer for the tame Tate algorithm.** Additive reduction and
integral `j` give the three valuation inequalities available from the exact-pin reduction API:
positive discriminant valuation, positive `c₄` valuation, and the potentially-good comparison
`v(c₄)³ ≤ v(Δ)`.  This package does not determine a Kodaira symbol or component order. -/
theorem tateAlgorithm_valuationInput_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hA : W.HasAdditiveReduction R)
    (hj : valuation K (maximalIdeal R) W.j ≤ 1) :
    valuation K (maximalIdeal R) W.Δ < 1 ∧
      valuation K (maximalIdeal R) W.c₄ < 1 ∧
      valuation K (maximalIdeal R) W.c₄ ^ 3 ≤
        valuation K (maximalIdeal R) W.Δ :=
  ⟨hA.badReduction, hA.additiveReduction,
    valuation_c₄_pow_three_le_valuation_Δ_of_valuation_j_le_one hj⟩

/-- **Named translation consumer for the tame Tate algorithm.** An integral admissible change
whose scale factor is a valuation unit preserves the additive-reduction branch.  In particular,
the translations used to move a singular point can be composed without losing minimality or the
two strict valuation inequalities.  Constructing those translations and the later blowups remains
separate work. -/
theorem tateAlgorithm_hasAdditiveReduction_variableChange_of_valuation_u_eq_one
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hA : W.HasAdditiveReduction R)
    (C : WeierstrassCurve.VariableChange K)
    (hC : WeierstrassCurve.IsIntegral R (C • W))
    (hu : valuation K (maximalIdeal R) (C.u : K) = 1) :
    (C • W).HasAdditiveReduction R := by
  letI : W.IsMinimal R := hA.toIsMinimal
  have hminimal : (C • W).IsMinimal R :=
    isMinimal_variableChange_of_isIntegral_of_valuation_u_eq_one C hC hu
  letI : (C • W).IsMinimal R := hminimal
  refine ⟨?_, ?_⟩
  · simpa [WeierstrassCurve.variableChange_Δ, map_mul, map_pow,
      Units.val_inv_eq_inv_val, map_inv₀, hu] using hA.badReduction
  · simpa [WeierstrassCurve.variableChange_c₄, map_mul, map_pow,
      Units.val_inv_eq_inv_val, map_inv₀, hu] using hA.additiveReduction

/-- **Named translated-minimality consumer for the tame Tate algorithm.** In the additive branch,
no choice of translation parameters can make all five coefficients integral after a further scale
by `u⁻¹` with `v(u) < 1`.  This supplies the simultaneous coefficient obstruction, but not the
blowup sequence, Kodaira classification, or marked-component incidence theorem. -/
theorem tateAlgorithm_translatedCoefficientObstruction_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hA : W.HasAdditiveReduction R)
    (u : Kˣ) (r s t : K)
    (hu : valuation K (maximalIdeal R) (u : K) < 1) :
    ¬ TranslatedWeightedCoefficientsIntegralAfterScale (R := R) W u r s t := by
  letI : W.IsMinimal R := hA.toIsMinimal
  exact tateAlgorithm_minimalityTranslatedCoefficientObstruction u r s t hu

/-- **First residue-translation step of the tame Tate algorithm.** Given a singular affine point
of the reduced minimal cubic, lift its two coordinates to the valuation ring and translate that
point to the origin.  The resulting generic equation remains in the minimal additive branch, and
the explicit translated integral model has `a₃`, `a₄`, and `a₆` in the maximal ideal.

This constructs the translation rather than taking its parameters as hypotheses.  The later
tangent normalization, blowups, Kodaira case split, and marked-component calculation remain
separate work. -/
theorem tateAlgorithm_residueTranslation_of_singularPoint
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hA : W.HasAdditiveReduction R)
    (x y : IsLocalRing.ResidueField R)
    (hequation : (W.reduction R).toAffine.Equation x y)
    (hsingular : ¬ (W.reduction R).toAffine.Nonsingular x y) :
    let W' := residueTranslatedIntegralModel R K W x 0 y
    (genericResidueTranslation R K x 0 y • W).HasAdditiveReduction R ∧
      W'.a₃ ∈ IsLocalRing.maximalIdeal R ∧
      W'.a₄ ∈ IsLocalRing.maximalIdeal R ∧
      W'.a₆ ∈ IsLocalRing.maximalIdeal R := by
  let C := genericResidueTranslation R K x 0 y
  have hIntegral : WeierstrassCurve.IsIntegral R (C • W) := by
    simpa [C] using isIntegral_genericResidueTranslation R K W x 0 y
  have hAdditive : (C • W).HasAdditiveReduction R :=
    tateAlgorithm_hasAdditiveReduction_variableChange_of_valuation_u_eq_one
      hA C hIntegral (by
        simp [C, genericResidueTranslation, integralResidueTranslation])
  have hcoeff :=
    residueTranslatedIntegralModel_a₃_a₄_a₆_mem_maximalIdeal_of_singular
      R K W x y hequation hsingular
  simpa [C] using And.intro hAdditive hcoeff

/-- **Constructed first Tate step.** In residue characteristic different from two and three,
additive reduction itself supplies the affine singular point used by the preceding translation
theorem.  Thus the caller need not choose residue coordinates: normalization to the standard
cusp produces them, and their integral lifts give an additive translated equation with `a₃`,
`a₄`, and `a₆` in the maximal ideal. -/
theorem tateAlgorithm_exists_residueTranslation_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hA : W.HasAdditiveReduction R)
    (h2 : (2 : IsLocalRing.ResidueField R) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField R) ≠ 0) :
    ∃ x y : IsLocalRing.ResidueField R,
      let W' := residueTranslatedIntegralModel R K W x 0 y
      (genericResidueTranslation R K x 0 y • W).HasAdditiveReduction R ∧
        W'.a₃ ∈ IsLocalRing.maximalIdeal R ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal R ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨x, y, hequation, hsingular⟩ := exists_affine_singular_of_cuspidal
    (W.reduction R) h2 h3
      (reduction_Δ_eq_zero_of_hasAdditiveReduction hA)
      (reduction_c₄_eq_zero_of_hasAdditiveReduction hA)
  exact ⟨x, y,
    tateAlgorithm_residueTranslation_of_singularPoint hA x y hequation hsingular⟩

/-- **Constructed tangent normalization.** In residue characteristic different from two and
three, lift the complete short-normal-form change of the additive special cubic.  Its scale is
one, so the generic equation remains minimal and additive; its special fibre is exactly the
standard cusp `Y² = X³`.  Consequently all five coefficients of the explicit integral model
belong to the maximal ideal.

This is the coordinate-normalization step preceding the blowups in the tame Tate algorithm.  It
does not determine a Kodaira symbol, construct special-fibre components, or bound a component
class. -/
theorem tateAlgorithm_exists_residueShortNormalization_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hA : W.HasAdditiveReduction R)
    (h2 : (2 : IsLocalRing.ResidueField R) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField R) ≠ 0) :
    ∃ r s t : IsLocalRing.ResidueField R,
      let W' := residueTranslatedIntegralModel R K W r s t
      (genericResidueTranslation R K r s t • W).HasAdditiveReduction R ∧
        W'.map (IsLocalRing.residue R) =
          cuspidalShortCurve (IsLocalRing.ResidueField R) ∧
        W'.a₁ ∈ IsLocalRing.maximalIdeal R ∧
        W'.a₂ ∈ IsLocalRing.maximalIdeal R ∧
        W'.a₃ ∈ IsLocalRing.maximalIdeal R ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal R ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal R := by
  letI : Invertible (2 : IsLocalRing.ResidueField R) := invertibleOfNonzero h2
  letI : Invertible (3 : IsLocalRing.ResidueField R) := invertibleOfNonzero h3
  let Wbar : WeierstrassCurve (IsLocalRing.ResidueField R) := W.reduction R
  let C : WeierstrassCurve.VariableChange (IsLocalRing.ResidueField R) := Wbar.toShortNF
  refine ⟨C.r, C.s, C.t, ?_⟩
  let W' := residueTranslatedIntegralModel R K W C.r C.s C.t
  let Cgeneric := genericResidueTranslation R K C.r C.s C.t
  have hIntegral : WeierstrassCurve.IsIntegral R (Cgeneric • W) := by
    simpa [Cgeneric] using
      isIntegral_genericResidueTranslation R K W C.r C.s C.t
  have hAdditive : (Cgeneric • W).HasAdditiveReduction R :=
    tateAlgorithm_hasAdditiveReduction_variableChange_of_valuation_u_eq_one
      hA Cgeneric hIntegral (by
        simp [Cgeneric, genericResidueTranslation, integralResidueTranslation])
  have hchange :
      (⟨1, C.r, C.s, C.t⟩ :
        WeierstrassCurve.VariableChange (IsLocalRing.ResidueField R)) = C := by
    ext <;>
      simp [C, Wbar, WeierstrassCurve.toShortNF,
        WeierstrassCurve.toCharNeTwoNF, WeierstrassCurve.VariableChange.mul_def]
  have hspecial : W'.map (IsLocalRing.residue R) =
      cuspidalShortCurve (IsLocalRing.ResidueField R) := by
    calc
      W'.map (IsLocalRing.residue R) =
          (⟨1, C.r, C.s, C.t⟩ :
            WeierstrassCurve.VariableChange (IsLocalRing.ResidueField R)) •
            (W.integralModel R).map (IsLocalRing.residue R) := by
              simpa [W'] using
                residueTranslatedIntegralModel_map_residue R K W C.r C.s C.t
      _ = C • Wbar := by rw [hchange]; rfl
      _ = cuspidalShortCurve (IsLocalRing.ResidueField R) := by
        apply short_eq_cuspidal_of_invariants
        · rw [WeierstrassCurve.variableChange_Δ,
            reduction_Δ_eq_zero_of_hasAdditiveReduction hA, mul_zero]
        · rw [WeierstrassCurve.variableChange_c₄,
            reduction_c₄_eq_zero_of_hasAdditiveReduction hA, mul_zero]
  have ha₁ : IsLocalRing.residue R W'.a₁ = 0 := by
    simpa [cuspidalShortCurve] using congrArg (fun V ↦ V.a₁) hspecial
  have ha₂ : IsLocalRing.residue R W'.a₂ = 0 := by
    simpa [cuspidalShortCurve] using congrArg (fun V ↦ V.a₂) hspecial
  have ha₃ : IsLocalRing.residue R W'.a₃ = 0 := by
    simpa [cuspidalShortCurve] using congrArg (fun V ↦ V.a₃) hspecial
  have ha₄ : IsLocalRing.residue R W'.a₄ = 0 := by
    simpa [cuspidalShortCurve] using congrArg (fun V ↦ V.a₄) hspecial
  have ha₆ : IsLocalRing.residue R W'.a₆ = 0 := by
    simpa [cuspidalShortCurve] using congrArg (fun V ↦ V.a₆) hspecial
  exact ⟨by simpa [Cgeneric] using hAdditive, hspecial,
    (IsLocalRing.residue_eq_zero_iff W'.a₁).mp ha₁,
    (IsLocalRing.residue_eq_zero_iff W'.a₂).mp ha₂,
    (IsLocalRing.residue_eq_zero_iff W'.a₃).mp ha₃,
    (IsLocalRing.residue_eq_zero_iff W'.a₄).mp ha₄,
    (IsLocalRing.residue_eq_zero_iff W'.a₆).mp ha₆⟩

/-- **Exact integral short normalization.**  If two and three remain nonzero in the residue
field, then they are units in the DVR.  Hence Mathlib's short-normal-form change may be applied
directly to the integral model of a minimal additive equation.  Its scale is one, so the generic
curve remains minimal and additive.  The resulting integral equation has `a₁ = a₂ = a₃ = 0`
exactly, has special fibre `Y² = X³`, and has `a₄` and `a₆` in the maximal ideal.

This improves the preceding residue-only normalization and is the form used by the explicit
first-blowup charts below. -/
theorem tateAlgorithm_exists_integralShortNormalization_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hA : W.HasAdditiveReduction R)
    (h2 : (2 : IsLocalRing.ResidueField R) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField R) ≠ 0) :
    ∃ C : WeierstrassCurve.VariableChange R,
      let W' := C • W.integralModel R
      let CK := C.map (algebraMap R K)
      (CK • W).HasAdditiveReduction R ∧
        W'.map (algebraMap R K) = CK • W ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue R) =
          cuspidalShortCurve (IsLocalRing.ResidueField R) ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal R ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal R := by
  have h2unit : IsUnit (2 : R) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (R := R) (2 : R)).mp
    simpa only [map_ofNat] using h2
  have h3unit : IsUnit (3 : R) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (R := R) (3 : R)).mp
    simpa only [map_ofNat] using h3
  letI : Invertible (2 : R) := h2unit.invertible
  letI : Invertible (3 : R) := h3unit.invertible
  let W₀ : WeierstrassCurve R := W.integralModel R
  let C : WeierstrassCurve.VariableChange R := W₀.toShortNF
  let W' : WeierstrassCurve R := C • W₀
  let CK : WeierstrassCurve.VariableChange K := C.map (algebraMap R K)
  have hbase : W₀.map (algebraMap R K) = W := by
    simpa [W₀, WeierstrassCurve.baseChange] using
      W.baseChange_integralModel_eq R
  have hmap : W'.map (algebraMap R K) = CK • W := by
    calc
      W'.map (algebraMap R K) =
          C.map (algebraMap R K) • W₀.map (algebraMap R K) := by
            simpa [W'] using
              (WeierstrassCurve.map_variableChange
                (W := W₀) (C := C) (φ := algebraMap R K)).symm
      _ = CK • W := by rw [hbase]
  have hIntegral : WeierstrassCurve.IsIntegral R (CK • W) := by
    apply WeierstrassCurve.isIntegral_of_exists_lift R
    · exact ⟨W'.a₁, by
        simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₁) hmap⟩
    · exact ⟨W'.a₂, by
        simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₂) hmap⟩
    · exact ⟨W'.a₃, by
        simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₃) hmap⟩
    · exact ⟨W'.a₄, by
        simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₄) hmap⟩
    · exact ⟨W'.a₆, by
        simpa [WeierstrassCurve.map] using congrArg (fun V ↦ V.a₆) hmap⟩
  have hu : valuation K (maximalIdeal R) (CK.u : K) = 1 := by
    simp [CK, C, W₀, WeierstrassCurve.toShortNF,
      WeierstrassCurve.toCharNeTwoNF,
      WeierstrassCurve.VariableChange.mul_def]
  have hAdditive : (CK • W).HasAdditiveReduction R :=
    tateAlgorithm_hasAdditiveReduction_variableChange_of_valuation_u_eq_one
      hA CK hIntegral hu
  have hshort : W'.IsShortNF := by
    dsimp only [W', C]
    infer_instance
  letI : W'.IsShortNF := hshort
  letI : Invertible (2 : IsLocalRing.ResidueField R) := invertibleOfNonzero h2
  letI : Invertible (3 : IsLocalRing.ResidueField R) := invertibleOfNonzero h3
  letI : (W'.map (IsLocalRing.residue R)).IsShortNF := by
    constructor
    · change IsLocalRing.residue R W'.a₁ = 0
      rw [W'.a₁_of_isShortNF, map_zero]
    · change IsLocalRing.residue R W'.a₂ = 0
      rw [W'.a₂_of_isShortNF, map_zero]
    · change IsLocalRing.residue R W'.a₃ = 0
      rw [W'.a₃_of_isShortNF, map_zero]
  have hΔ : (W'.map (IsLocalRing.residue R)).Δ = 0 := by
    rw [← WeierstrassCurve.map_variableChange,
      WeierstrassCurve.variableChange_Δ]
    change _ * (W.reduction R).Δ = 0
    rw [reduction_Δ_eq_zero_of_hasAdditiveReduction hA, mul_zero]
  have hc₄ : (W'.map (IsLocalRing.residue R)).c₄ = 0 := by
    rw [← WeierstrassCurve.map_variableChange,
      WeierstrassCurve.variableChange_c₄]
    change _ * (W.reduction R).c₄ = 0
    rw [reduction_c₄_eq_zero_of_hasAdditiveReduction hA, mul_zero]
  have hspecial : W'.map (IsLocalRing.residue R) =
      cuspidalShortCurve (IsLocalRing.ResidueField R) :=
    short_eq_cuspidal_of_invariants
      (W'.map (IsLocalRing.residue R)) hΔ hc₄
  have ha₄ : IsLocalRing.residue R W'.a₄ = 0 := by
    simpa [cuspidalShortCurve] using congrArg (fun V ↦ V.a₄) hspecial
  have ha₆ : IsLocalRing.residue R W'.a₆ = 0 := by
    simpa [cuspidalShortCurve] using congrArg (fun V ↦ V.a₆) hspecial
  exact ⟨C, hAdditive, hmap, hshort, hspecial,
    (IsLocalRing.residue_eq_zero_iff W'.a₄).mp ha₄,
    (IsLocalRing.residue_eq_zero_iff W'.a₆).mp ha₆⟩

/-- **Constructed affine first-blowup equation charts.**  After exact integral short
normalization, choose a DVR uniformizer and divide the remaining two coefficients by it.  The
resulting bundled object carries the exact one-exceptional-factor quotients and total-transform
factorizations on the uniformizer, `X`, and `Y` charts of the blowup of the closed cusp.

This is an algebraic chart construction only.  No regularity, Kodaira-symbol, special-component,
strict-transform, or marked-point incidence conclusion is asserted. -/
theorem tateAlgorithm_exists_firstBlowupEquationCharts_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hA : W.HasAdditiveReduction R)
    (h2 : (2 : IsLocalRing.ResidueField R) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField R) ≠ 0) :
    ∃ C : WeierstrassCurve.VariableChange R,
      let W' := C • W.integralModel R
      let CK := C.map (algebraMap R K)
      (CK • W).HasAdditiveReduction R ∧
        W'.map (algebraMap R K) = CK • W ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue R) =
          cuspidalShortCurve (IsLocalRing.ResidueField R) ∧
        Nonempty (FirstBlowupEquationCharts W') := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, ha₄, ha₆⟩ :=
    tateAlgorithm_exists_integralShortNormalization_of_hasAdditiveReduction hA h2 h3
  let W' := C • W.integralModel R
  have ha₁ : W'.a₁ ∈ IsLocalRing.maximalIdeal R := by
    rw [hshort.a₁]
    exact Submodule.zero_mem _
  have ha₂ : W'.a₂ ∈ IsLocalRing.maximalIdeal R := by
    rw [hshort.a₂]
    exact Submodule.zero_mem _
  have ha₃ : W'.a₃ ∈ IsLocalRing.maximalIdeal R := by
    rw [hshort.a₃]
    exact Submodule.zero_mem _
  exact ⟨C, hAdditive, hmap, hshort, hspecial,
    nonempty_firstBlowupEquationCharts_of_coefficients_mem_maximalIdeal
      W' ha₁ ha₂ ha₃ ha₄ ha₆⟩

/-- **Named minimality consumer for the tame Tate algorithm.** In the additive branch, the
minimal equation cannot have all five coefficients remain integral after a further weighted
scaling by `u⁻¹` with `v(u) < 1`.  Completing the marked component theorem still requires the
subsequent translation, blowup, Kodaira classification, and component-incidence steps. -/
theorem tateAlgorithm_coefficientObstruction_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hA : W.HasAdditiveReduction R)
    (u : Kˣ)
    (hu : valuation K (maximalIdeal R) (u : K) < 1) :
    ¬ WeightedCoefficientsIntegralAfterScale (R := R) W u := by
  letI : W.IsMinimal R := hA.toIsMinimal
  exact tateAlgorithm_minimalityCoefficientObstruction u hu

/-- Multiplicative reduction forces the `j`-invariant to have valuation strictly greater than
one.  This is the elementary bridge from the integral-`j` formulation of potentially good
reduction to the reduction-type trichotomy. -/
theorem valuation_j_gt_one_of_hasMultiplicativeReduction
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : W.HasMultiplicativeReduction R) :
    1 < valuation K (maximalIdeal R) W.j := by
  rw [WeierstrassCurve.j]
  simp only [Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_pow,
    WeierstrassCurve.coe_Δ',
    hW.multiplicativeReduction, one_pow, mul_one]
  exact one_lt_inv_iff₀.mpr
    ⟨(valuation K (maximalIdeal R)).pos_iff.mpr (by
        simpa only [WeierstrassCurve.coe_Δ'] using W.Δ'.ne_zero),
      hW.badReduction⟩

/-- An integral `j`-invariant excludes multiplicative reduction of a minimal equation. -/
theorem not_hasMultiplicativeReduction_of_valuation_j_le_one
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1) :
    ¬ W.HasMultiplicativeReduction R := by
  intro hW
  exact (not_lt_of_ge hj) (valuation_j_gt_one_of_hasMultiplicativeReduction hW)

end ReductionType

/-- Integral `j` upgrades a minimal equation to good reduction whenever the
marked point's exact order is impossible in the additive branch.

This is the shared reduction-type engine behind the prime route at five and
the order-35 route at eleven.  It isolates the only residue-characteristic
dependent input as an exact-order obstruction under additive reduction. -/
theorem hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1)
    {G : Type u} [AddCommGroup G]
    (P : G) (N : ℕ)
    (hadditive : W.HasAdditiveReduction R → addOrderOf P ≠ N)
    (horder : addOrderOf P = N) :
    W.HasGoodReduction R := by
  rcases W.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R with
    hgood | hmultiplicative | hA
  · exact hgood
  · exact (not_hasMultiplicativeReduction_of_valuation_j_le_one
      hj hmultiplicative).elim
  · exact (hadditive hA horder).elim

/-- A tame additive filtration with five-element residue group has no point
of prime exact order at least eleven. -/
theorem addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive
    {G : Type u} [AddCommGroup G]
    (F : TameAdditiveFiltrationData.{u, v} G)
    (hresidue : Nat.card F.ResidueAdditive = 5)
    (P : G) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  letI : AddCommGroup F.Component := F.componentAddCommGroup
  letI : Finite F.Component := F.componentFinite
  letI : AddCommGroup F.ResidueAdditive := F.residueAddCommGroup
  letI : Finite F.ResidueAdditive := F.residueFinite
  intro horder
  have hcomponentCoprime : N.Coprime (Nat.card F.Component) :=
    Nat.coprime_of_lt_prime Nat.card_pos.ne'
      (lt_of_le_of_lt F.component_card_le_four (by omega)) hprime
  have hresidueCoprime : N.Coprime (Nat.card F.ResidueAdditive) := by
    rw [hresidue]
    exact Nat.coprime_of_lt_prime (by norm_num) (by omega) hprime
  have hzero := F.point_eq_zero_of_coprime_card hprime.ne_zero
    hcomponentCoprime hresidueCoprime horder
  rw [hzero] at horder
  simp at horder
  omega

/-- The prime-five additive contradiction needs only a component exponent, not a cardinality
bound for a separately constructed component group.  The tame universal exponent `12` is coprime
to every prime order at least eleven, while the identity-component residue group has cardinality
five. -/
theorem addOrderOf_ne_prime_ge_eleven_of_componentExponentTwelveAtFive
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G)
    {ResidueAdditive : Type v} [AddCommGroup ResidueAdditive]
    [Finite ResidueAdditive]
    (identityReduction : identitySubgroup →+ ResidueAdditive)
    (formalKernel : AddSubgroup identitySubgroup)
    (identityReduction_ker : identityReduction.ker = formalKernel)
    (formalKernel_torsionFree :
      ∀ Q : formalKernel, IsOfFinAddOrder Q → Q = 0)
    (hresidue : Nat.card ResidueAdditive = 5)
    (P : G) (hcomponent : 12 • P ∈ identitySubgroup)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hcomponentCoprime : N.Coprime 12 := by
    rw [hprime.coprime_iff_not_dvd]
    intro hdvd
    have hle : N ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : N = 11 ∨ N = 12 := by omega
    rcases hcases with rfl | rfl
    · norm_num at hdvd
    · exact (by decide : ¬ Nat.Prime 12) hprime
  have hresidueCoprime : N.Coprime (Nat.card ResidueAdditive) := by
    rw [hresidue]
    exact Nat.coprime_of_lt_prime (by norm_num) (by omega) hprime
  have hzero := point_eq_zero_of_coprime_component_exponent
    identitySubgroup identityReduction formalKernel identityReduction_ker
    formalKernel_torsionFree hprime.ne_zero hcomponentCoprime
    hresidueCoprime hcomponent horder
  rw [hzero] at horder
  simp at horder
  omega

/-- The canonical five-adic prime-order contradiction through the component-exponent handoff.

Coordinatewise nonsingular reduction fixes the identity subgroup and reduction homomorphism, and
the exact-pinned unramified theorem proves torsion-freeness of the formal kernel.  Consequently the
only component geometry required for the marked point is `12 • P ∈ E₀`; neither finiteness nor a
cardinality bound for the full component quotient appears in this interface. -/
theorem
    addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (P : W.Point)
    (hcomponent : 12 • P ∈
      WeierstrassCurve.Affine.nonsingularReductionSubgroup hW
        (WeierstrassCurve.Affine.nonsingularReduction_isAdditive hW))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  let residueEquivZMod :
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ) ≃ ZMod 5 :=
    ((atFive.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      MazurTorsion.IntegerPrimeSpecialization.residueFiveAlgEquiv.toRingEquiv).toEquiv
  letI : Finite
      (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv (ZMod 5) residueEquivZMod.symm
  let identitySubgroup : AddSubgroup W.Point :=
    WeierstrassCurve.Affine.nonsingularReductionSubgroup hW
      (WeierstrassCurve.Affine.nonsingularReduction_isAdditive hW)
  let identityReduction : identitySubgroup →+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ) :=
    especial.toAddMonoidHom.comp
      (WeierstrassCurve.Affine.nonsingularReductionHom hW
        (WeierstrassCurve.Affine.nonsingularReduction_isAdditive hW))
  let formalKernel : AddSubgroup identitySubgroup :=
    (WeierstrassCurve.Affine.filtration hW 0).comap identitySubgroup.subtype
  apply addOrderOf_ne_prime_ge_eleven_of_componentExponentTwelveAtFive
    identitySubgroup identityReduction formalKernel
  · ext Q
    change especial
      (WeierstrassCurve.Affine.nonsingularReductionHom hW
        (WeierstrassCurve.Affine.nonsingularReduction_isAdditive hW) Q) = 0 ↔ _
    rw [← map_zero especial, especial.injective.eq_iff]
    exact WeierstrassCurve.Affine.nonsingularReduction_eq_zero_iff hW Q Q.property
  · intro Q hQ
    apply Subtype.ext
    apply Subtype.ext
    exact MazurTorsion.IntegerPrimeSpecialization.torsion_eq_zero_of_mem_formalKernel_atFive
      hW Q.property
      (identitySubgroup.subtype.isOfFinAddOrder
        (formalKernel.subtype.isOfFinAddOrder hQ))
  · exact MazurTorsion.EllipticCurve.TameAdditiveReductionDataAtFive.residue_natCard
  · exact hcomponent
  · exact hprime
  · exact hN

/-- In the order-one branch of the normalized tame Tate equation at five, every local point is
already in the canonical nonsingular-reduction subgroup.  The checked component-exponent
consumer therefore excludes every marked prime order at least eleven. -/
theorem addOrderOf_ne_prime_ge_eleven_of_firstBlowup_residue_b₆_ne_zeroAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)))
    (hb₆ : IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)
      B.coefficients.b₆ ≠ 0)
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (P : W.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply
    addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
      hW especial P
  · exact
      twelve_nsmul_mem_nonsingularReductionSubgroup_of_firstBlowup_residue_b₆_ne_zero
        hW B h2 h3 hspecial hb₆ P
  · exact hprime
  · exact hN

/-- In the next coefficient branch at five, the checked tangent calculation puts the double of
every local point in canonical nonsingular reduction.  Hence the same exponent-twelve consumer
excludes every marked prime order at least eleven. -/
theorem addOrderOf_ne_prime_ge_eleven_of_firstBlowup_residue_b₄_ne_zeroAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)))
    (hb₄ : IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)
      B.coefficients.b₄ ≠ 0)
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (P : W.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply
    addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
      hW especial P
  · exact
      twelve_nsmul_mem_nonsingularReductionSubgroup_of_firstBlowup_residue_b₄_ne_zero
        hW B h2 h3 hspecial hb₄ P
  · exact hprime
  · exact hN

/-- In the exact depth-two `a₆` branch at five, the checked tangent--secant calculation puts the
marked triple, and therefore the twelfth multiple, in canonical nonsingular reduction.  The
component-exponent consumer excludes every marked prime order at least eleven. -/
theorem addOrderOf_ne_prime_ge_eleven_of_a₄_sq_a₆_sq_not_cubeAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)))
    (ha₄sq : W₀.a₄ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 2)
    (ha₆sq : W₀.a₆ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 2)
    (ha₆notcube : W₀.a₆ ∉ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 3)
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (P : W.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply
    addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
      hW especial P
  · exact
      twelve_nsmul_mem_nonsingularReductionSubgroup_of_a₄_sq_a₆_sq_not_cube
        hW h2 h3 hspecial ha₄sq ha₆sq ha₆notcube P
  · exact hprime
  · exact hN

/-- A simple marked root of the exceptional cubic at five forces the marked double, hence the
twelfth multiple, into canonical nonsingular reduction.  The component-exponent consumer then
excludes every prime order at least eleven. -/
theorem addOrderOf_ne_prime_ge_eleven_of_markedExceptionalCubic_simpleRootAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hsimple : D.derivativeResidue ≠ 0)
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply
    addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
      hW especial P
  · exact
      twelve_nsmul_mem_nonsingularReductionSubgroup_of_markedExceptionalCubic_simpleRoot
        hW h2 h3 hspecial D hsimple
  · exact hprime
  · exact hN

/-- A nonzero repeated marked root of the exceptional cubic at five forces the marked twelfth
multiple into canonical nonsingular reduction, excluding every prime order at least eleven. -/
theorem
    addOrderOf_ne_prime_ge_eleven_of_markedExceptionalCubic_repeatedNonzeroRootAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hrepeated : D.derivativeResidue = 0)
    (hroot_ne : IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.X ≠ 0)
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply
    addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
      hW especial P
  · exact
      twelve_nsmul_mem_nonsingularReductionSubgroup_of_repeatedExceptionalRoot_ne_zero
        hW h2 h3 hspecial D hrepeated hroot_ne
  · exact hprime
  · exact hN

/-- For a prime-order point on the selected five-adic short equation, a repeated marked
exceptional root must be zero.  The marked abscissa and both coefficients consequently gain one
power of the same bundled uniformizer. -/
theorem markedExceptionalCubic_zeroRoot_and_deeperDepths_of_primeOrderAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hrepeated : D.derivativeResidue = 0)
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.X = 0 ∧
      IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.A = 0 ∧
      IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.B = 0 ∧
      D.x ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
      W₀.a₄ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
      W₀.a₆ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ^ 4 := by
  have hroot : IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.X = 0 := by
    by_contra hroot_ne
    exact
      (addOrderOf_ne_prime_ge_eleven_of_markedExceptionalCubic_repeatedNonzeroRootAtFive
        hW h2 h3 hspecial D hrepeated hroot_ne especial N hprime hN) horder
  have hdepth :=
    markedExceptionalCubic_deeper_depths_of_derivative_eq_zero_of_root_eq_zero
      D hrepeated hroot
  exact ⟨hroot, hdepth⟩

/-- Exact depth four of `a₆` on the selected marked exceptional branch puts `12P` in canonical
nonsingular reduction, contradicting prime order at least eleven over the five-adic field. -/
theorem addOrderOf_ne_prime_ge_eleven_of_marked_depth_fourAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hxsq : D.x ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 2)
    (ha₄cube : W₀.a₄ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 3)
    (ha₆four : W₀.a₆ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 4)
    (ha₆notfive : W₀.a₆ ∉ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 5)
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply
    addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
      hW especial P
  · exact twelve_nsmul_mem_nonsingularReductionSubgroup_of_marked_depth_four
      hW h2 h3 hspecial D hxsq ha₄cube ha₆four ha₆notfive
  · exact hprime
  · exact hN

/-- A marked prime-order point forces `a₆` to gain the fifth power of the maximal ideal on the
same selected five-adic short model. -/
theorem markedExceptionalCubic_a₆_mem_fifth_of_primeOrderAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hxsq : D.x ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 2)
    (ha₄cube : W₀.a₄ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 3)
    (ha₆four : W₀.a₆ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 4)
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    W₀.a₆ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 5 := by
  by_contra ha₆notfive
  exact
    (addOrderOf_ne_prime_ge_eleven_of_marked_depth_fourAtFive
      hW h2 h3 hspecial D hxsq ha₄cube ha₆four ha₆notfive
      especial N hprime hN) horder

/-- Integral `j`, the actual tame additive Néron filtration, and a marked prime-order point
upgrade a minimal equation to good reduction.  The proof uses Mathlib's exhaustive
good/multiplicative/additive trichotomy: integral `j` excludes the multiplicative branch and the
two finite quotients plus torsion-free formal kernel exclude the additive branch.

This is the checked local consumer expected after the formal-immersion argument supplies
potentially good reduction.  Constructing `F` from the genuine Néron model remains the geometric
input; it is not hidden in this statement. -/
theorem hasGoodReduction_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1)
    {G : Type u} [AddCommGroup G]
    (F : W.HasAdditiveReduction R → TameAdditiveFiltrationData.{u, v} G)
    (hresidue : ∀ hW, Nat.card (F hW).ResidueAdditive = 5)
    (P : G) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    W.HasGoodReduction R := by
  exact hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction
    hj P N
      (fun hA ↦ addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive
        (F hA) (hresidue hA) P N hprime hN)
      horder

end MazurTorsion.PrimeOrder
