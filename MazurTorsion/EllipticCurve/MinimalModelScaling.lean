/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Tactic.NormNum

/-!
# Minimal-model scaling inputs for the tame Tate algorithm

Mathlib's minimal-model API states minimality as maximality of the multiplicative discriminant
valuation among integral admissible changes.  This file extracts the forms used at the start of a
Tate-algorithm argument:

* integral `j` gives `v(c₄)³ ≤ v(Δ)`; and
* integral changes whose scale factor has valuation one preserve minimality; and
* no translations followed by a scale of valuation below one can keep all five transformed
  coefficients integral on a minimal equation.

These are valuation and minimality inputs only.  They do not construct a Néron model, determine a
Kodaira symbol, identify the canonical nonsingular-reduction subgroup with the Néron identity
component, or bound the order of a marked component class.
-/

noncomputable section

namespace MazurTorsion.EllipticCurve

open IsDedekindDomain.HeightOneSpectrum
open IsDiscreteValuationRing
open Multiplicative WithZero

/-- Integral `j` is the valuation inequality `v(c₄)³ ≤ v(Δ)`.  This is the
potentially-good valuation input to the tame Kodaira classification. -/
theorem valuation_c₄_pow_three_le_valuation_Δ_of_valuation_j_le_one
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1) :
    valuation K (maximalIdeal R) W.c₄ ^ 3 ≤
      valuation K (maximalIdeal R) W.Δ := by
  have hΔpos : 0 < valuation K (maximalIdeal R) W.Δ :=
    (valuation K (maximalIdeal R)).pos_iff.mpr W.Δ'.ne_zero
  rw [WeierstrassCurve.j] at hj
  simp only [Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_pow,
    WeierstrassCurve.coe_Δ'] at hj
  simpa only [mul_one] using (inv_mul_le_iff₀ hΔpos).mp hj

/-- Minimality forbids an integral admissible change whose discriminant has strictly larger
multiplicative valuation.  This unfolds Mathlib's `MaximalFor` definition and removes the bounded
subtype used internally by `valuation_Δ_aux`. -/
theorem not_valuation_Δ_lt_of_isMinimal_of_isIntegral_variableChange
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsMinimal R]
    (C : WeierstrassCurve.VariableChange K)
    [hC : (C • W).IsIntegral R] :
    ¬ valuation K (maximalIdeal R) W.Δ <
      valuation K (maximalIdeal R) (C • W).Δ := by
  intro hlt
  have hleAux : WeierstrassCurve.valuation_Δ_aux R W ≤
      WeierstrassCurve.valuation_Δ_aux R (C • W) := by
    change (↑(WeierstrassCurve.valuation_Δ_aux R W) : ℤᵐ⁰) ≤
      ↑(WeierstrassCurve.valuation_Δ_aux R (C • W))
    rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
      WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral]
    exact hlt.le
  have hleAux' :
      (fun C : WeierstrassCurve.VariableChange K ↦
        WeierstrassCurve.valuation_Δ_aux R (C • W)) 1 ≤
      WeierstrassCurve.valuation_Δ_aux R (C • W) := by
    simpa only [one_smul] using hleAux
  have hgeAux := WeierstrassCurve.IsMinimal.val_Δ_maximal.2 hC hleAux'
  have hgeAux' : WeierstrassCurve.valuation_Δ_aux R (C • W) ≤
      WeierstrassCurve.valuation_Δ_aux R W := by
    simpa only [one_smul] using hgeAux
  have hge : valuation K (maximalIdeal R) (C • W).Δ ≤
      valuation K (maximalIdeal R) W.Δ := by
    have hgeCoe :
        (↑(WeierstrassCurve.valuation_Δ_aux R (C • W)) : ℤᵐ⁰) ≤
          ↑(WeierstrassCurve.valuation_Δ_aux R W) := hgeAux'
    rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
      WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral] at hgeCoe
    exact hgeCoe
  exact (not_le_of_gt hlt) hge

/-- An integral admissible change whose scale factor has valuation one preserves minimality.
In particular, integral translations used to move a singular point to the origin stay within the
chosen minimal class. -/
theorem isMinimal_variableChange_of_isIntegral_of_valuation_u_eq_one
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsMinimal R]
    (C : WeierstrassCurve.VariableChange K)
    (hC : WeierstrassCurve.IsIntegral R (C • W))
    (hu : valuation K (maximalIdeal R) (C.u : K) = 1) :
    WeierstrassCurve.IsMinimal R (C • W) := by
  letI : WeierstrassCurve.IsIntegral R (C • W) := hC
  refine ⟨⟨?_, ?_⟩⟩
  · simpa only [one_smul] using hC
  · intro D hD hleD
    have hDC : WeierstrassCurve.IsIntegral R ((D * C) • W) := by
      rwa [mul_smul]
    have hbase : WeierstrassCurve.valuation_Δ_aux R (C • W) =
        WeierstrassCurve.valuation_Δ_aux R W := by
      apply Subtype.ext
      rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
        WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral,
        WeierstrassCurve.variableChange_Δ, map_mul, map_pow,
        Units.val_inv_eq_inv_val, map_inv₀, hu]
      simp
    have hleW : WeierstrassCurve.valuation_Δ_aux R W ≤
        WeierstrassCurve.valuation_Δ_aux R ((D * C) • W) := by
      rw [← hbase]
      simpa only [one_smul, mul_smul] using hleD
    have hge := WeierstrassCurve.IsMinimal.val_Δ_maximal.2 hDC (by
      simpa only [one_smul] using hleW)
    have hge' : WeierstrassCurve.valuation_Δ_aux R ((D * C) • W) ≤
        WeierstrassCurve.valuation_Δ_aux R W := by
      simpa only [one_smul] using hge
    rw [← hbase] at hge'
    simpa only [one_smul, mul_smul] using hge'

/-- On a minimal elliptic equation, an admissible change whose scale factor has valuation below
one cannot be integral, regardless of its translation parameters.  The discriminant multiplier
depends only on the scale factor, so such a change would strictly improve the multiplicative
discriminant valuation. -/
theorem not_isIntegral_variableChange_of_isMinimal_of_valuation_u_lt_one
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (C : WeierstrassCurve.VariableChange K)
    (hu : valuation K (maximalIdeal R) (C.u : K) < 1) :
    ¬ WeierstrassCurve.IsIntegral R (C • W) := by
  intro hint
  letI : WeierstrassCurve.IsIntegral R (C • W) := hint
  have huPos : 0 < valuation K (maximalIdeal R) (C.u : K) :=
    (valuation K (maximalIdeal R)).pos_iff.mpr C.u.ne_zero
  have huInv : 1 < (valuation K (maximalIdeal R) (C.u : K))⁻¹ :=
    one_lt_inv_iff₀.mpr ⟨huPos, hu⟩
  have huInvPow : 1 < (valuation K (maximalIdeal R) (C.u : K))⁻¹ ^ 12 :=
    one_lt_pow₀ huInv (by norm_num)
  have hΔPos : 0 < valuation K (maximalIdeal R) W.Δ :=
    (valuation K (maximalIdeal R)).pos_iff.mpr W.Δ'.ne_zero
  have hlt : valuation K (maximalIdeal R) W.Δ <
      valuation K (maximalIdeal R) (C • W).Δ := by
    rw [WeierstrassCurve.variableChange_Δ, map_mul, map_pow,
      Units.val_inv_eq_inv_val, map_inv₀]
    exact lt_mul_of_one_lt_left hΔPos huInvPow
  exact not_valuation_Δ_lt_of_isMinimal_of_isIntegral_variableChange C hlt

/-- A pure change of scale by `u` with `v(u) < 1` cannot remain integral on a minimal elliptic
equation.  Its discriminant is multiplied by `u⁻¹²`, which would strictly improve the
multiplicative discriminant valuation. -/
theorem not_isIntegral_scale_of_isMinimal
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (u : Kˣ)
    (hu : valuation K (maximalIdeal R) (u : K) < 1) :
    ¬ WeierstrassCurve.IsIntegral R
      ((⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) • W) := by
  exact
    not_isIntegral_variableChange_of_isMinimal_of_valuation_u_lt_one
      (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange K) hu

/-- All five coefficients have integral lifts after translating by `r`, `s`, and `t`, then
applying the weighted scale by `u⁻¹`.  These are exactly the five coefficient formulas for the
admissible change `⟨u, r, s, t⟩`. -/
def TranslatedWeightedCoefficientsIntegralAfterScale
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (W : WeierstrassCurve K) (u : Kˣ) (r s t : K) : Prop :=
  (∃ b₁ : R, algebraMap R K b₁ = (↑u⁻¹ : K) * (W.a₁ + 2 * s)) ∧
    (∃ b₂ : R,
      algebraMap R K b₂ = (↑u⁻¹ : K) ^ 2 *
        (W.a₂ - s * W.a₁ + 3 * r - s ^ 2)) ∧
    (∃ b₃ : R,
      algebraMap R K b₃ = (↑u⁻¹ : K) ^ 3 *
        (W.a₃ + r * W.a₁ + 2 * t)) ∧
    (∃ b₄ : R,
      algebraMap R K b₄ = (↑u⁻¹ : K) ^ 4 *
        (W.a₄ - s * W.a₃ + 2 * r * W.a₂ -
          (t + r * s) * W.a₁ + 3 * r ^ 2 - 2 * s * t)) ∧
    (∃ b₆ : R,
      algebraMap R K b₆ = (↑u⁻¹ : K) ^ 6 *
        (W.a₆ + r * W.a₄ + r ^ 2 * W.a₂ + r ^ 3 -
          t * W.a₃ - t ^ 2 - r * t * W.a₁))

/-- **Tate translation-and-scaling input.** On a minimal equation, arbitrary translations cannot
make all five transformed coefficients integral after a scale factor of valuation below one.
This is the simultaneous divisibility obstruction used before the blowup and Kodaira case split. -/
theorem tateAlgorithm_minimalityTranslatedCoefficientObstruction
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (u : Kˣ) (r s t : K)
    (hu : valuation K (maximalIdeal R) (u : K) < 1) :
    ¬ TranslatedWeightedCoefficientsIntegralAfterScale (R := R) W u r s t := by
  rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
  let C : WeierstrassCurve.VariableChange K := ⟨u, r, s, t⟩
  apply
    not_isIntegral_variableChange_of_isMinimal_of_valuation_u_lt_one
      (R := R) (W := W) C hu
  apply WeierstrassCurve.isIntegral_of_exists_lift R
  · simpa [C, WeierstrassCurve.variableChange_a₁] using h₁
  · simpa [C, WeierstrassCurve.variableChange_a₂] using h₂
  · simpa [C, WeierstrassCurve.variableChange_a₃] using h₃
  · simpa [C, WeierstrassCurve.variableChange_a₄] using h₄
  · simpa [C, WeierstrassCurve.variableChange_a₆] using h₆

/-- All five coefficients have integral lifts after the weighted pure scale by `u⁻¹`. -/
def WeightedCoefficientsIntegralAfterScale
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (W : WeierstrassCurve K) (u : Kˣ) : Prop :=
  (∃ r₁ : R, algebraMap R K r₁ = (↑u⁻¹ : K) * W.a₁) ∧
    (∃ r₂ : R, algebraMap R K r₂ = (↑u⁻¹ : K) ^ 2 * W.a₂) ∧
    (∃ r₃ : R, algebraMap R K r₃ = (↑u⁻¹ : K) ^ 3 * W.a₃) ∧
    (∃ r₄ : R, algebraMap R K r₄ = (↑u⁻¹ : K) ^ 4 * W.a₄) ∧
    (∃ r₆ : R, algebraMap R K r₆ = (↑u⁻¹ : K) ^ 6 * W.a₆)

/-- **Named Tate-algorithm consumer.** On a minimal equation, at least one weighted coefficient
fails to remain integral after scaling down by an element of positive additive valuation.  This is
the precise coefficient obstruction used to prevent another global scaling step in Tate's
algorithm.  Further translations, blowups, and component bookkeeping are still required to
deduce a Kodaira symbol or a component-order bound. -/
theorem tateAlgorithm_minimalityCoefficientObstruction
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (u : Kˣ)
    (hu : valuation K (maximalIdeal R) (u : K) < 1) :
    ¬ WeightedCoefficientsIntegralAfterScale (R := R) W u := by
  rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
  apply not_isIntegral_scale_of_isMinimal (R := R) (W := W) u hu
  let C : WeierstrassCurve.VariableChange K := ⟨u, 0, 0, 0⟩
  change WeierstrassCurve.IsIntegral R (C • W)
  apply WeierstrassCurve.isIntegral_of_exists_lift R
  · simpa [C, WeierstrassCurve.variableChange_a₁] using h₁
  · simpa [C, WeierstrassCurve.variableChange_a₂] using h₂
  · simpa [C, WeierstrassCurve.variableChange_a₃] using h₃
  · simpa [C, WeierstrassCurve.variableChange_a₄] using h₄
  · simpa [C, WeierstrassCurve.variableChange_a₆] using h₆

end MazurTorsion.EllipticCurve
