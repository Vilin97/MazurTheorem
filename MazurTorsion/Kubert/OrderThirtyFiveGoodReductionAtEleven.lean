/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFive
import MazurTorsion.PrimeOrder.TameAdditiveAtFive

/-!
# The order-35 good-reduction endpoint at eleven

This file specializes the shared formal-immersion local argument to the
auxiliary prime eleven.  It constructs Mathlib's selected minimal equation
after base change from `ℚ`, transports the marked point through the selected
variable change, excludes multiplicative reduction from integral `j`, and
uses canonical tame-additive reduction data to exclude the additive branch.
Good reduction then preserves exact order, and the checked exhaustive
enumeration over `F_11` rules out order 35.

The modular formal-immersion calculation is deliberately separate: its
output is the eleven-adic valuation bound consumed here.
-/

noncomputable section

open WeierstrassCurve

namespace MazurTorsion.OrderThirtyFive

open IsDedekindDomain.HeightOneSpectrum
open IsDiscreteValuationRing
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.PrimeOrder
open WeierstrassCurve.Affine

local instance : DecidableEq
    (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

private theorem residueAtEleven_natCast_ne_zero
    (n : ℕ) (hn : (n : ZMod 11) ≠ 0) :
    (n : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0 := by
  let e₁₁ : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ) ≃+* ZMod 11 :=
    (atEleven.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueElevenAlgEquiv.toRingEquiv
  intro h
  apply hn
  calc
    (n : ZMod 11) = e₁₁ (n : IsLocalRing.ResidueField
        (atEleven.adicCompletionIntegers ℚ)) := (map_natCast e₁₁ n).symm
    _ = e₁₁ 0 := congrArg e₁₁ h
    _ = 0 := by simp

private theorem residueAtEleven_two_ne_zero :
    (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0 :=
  residueAtEleven_natCast_ne_zero 2 (by decide)

private theorem residueAtEleven_three_ne_zero :
    (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0 :=
  residueAtEleven_natCast_ne_zero 3 (by decide)

/-- Coefficientwise base change of a rational Weierstrass equation to the
eleven-adic completion. -/
noncomputable abbrev completionAtEleven (E : WeierstrassCurve ℚ) :
    WeierstrassCurve (atEleven.adicCompletion ℚ) :=
  E.toAffine ⁄ (atEleven.adicCompletion ℚ)

instance completionAtEleven_isElliptic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (completionAtEleven E).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  dsimp only [completionAtEleven, WeierstrassCurve.Affine.baseChange,
    WeierstrassCurve.baseChange]
  rw [WeierstrassCurve.map_Δ]
  exact E.isUnit_Δ.map _

/-- The variable change selected by Mathlib's minimal-model existence theorem
over the eleven-adic valuation ring. -/
noncomputable def minimalCompletionChangeAtEleven (E : WeierstrassCurve ℚ) :
    WeierstrassCurve.VariableChange (atEleven.adicCompletion ℚ) :=
  ((completionAtEleven E).exists_isMinimal
    (atEleven.adicCompletionIntegers ℚ)).choose

/-- Mathlib's selected minimal eleven-adic equation attached to a rational
Weierstrass equation. -/
noncomputable abbrev minimalCompletionAtEleven (E : WeierstrassCurve ℚ) :
    WeierstrassCurve (atEleven.adicCompletion ℚ) :=
  minimalCompletionChangeAtEleven E • completionAtEleven E

theorem minimalCompletionAtEleven_eq_mathlibMinimal
    (E : WeierstrassCurve ℚ) :
    minimalCompletionAtEleven E =
      (completionAtEleven E).minimal
        (atEleven.adicCompletionIntegers ℚ) :=
  rfl

noncomputable instance minimalCompletionAtEleven_isMinimal
    (E : WeierstrassCurve ℚ) :
    (minimalCompletionAtEleven E).IsMinimal
      (atEleven.adicCompletionIntegers ℚ) := by
  exact ((completionAtEleven E).exists_isMinimal
    (atEleven.adicCompletionIntegers ℚ)).choose_spec

noncomputable instance minimalCompletionAtEleven_isElliptic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (minimalCompletionAtEleven E).IsElliptic := by
  dsimp only [minimalCompletionAtEleven]
  infer_instance

/-- The shared residue-translation construction on the selected eleven-adic minimal equation.
A singular point of its special fibre is moved to the origin by an integral unit-scale change;
the new equation stays additive and has `a₃`, `a₄`, and `a₆` in the maximal ideal. -/
theorem minimalCompletionAtEleven_tateAlgorithm_residueTranslation_of_singularPoint
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ))
    (x y : IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hequation : ((minimalCompletionAtEleven E).reduction
      (atEleven.adicCompletionIntegers ℚ)).toAffine.Equation x y)
    (hsingular : ¬ ((minimalCompletionAtEleven E).reduction
      (atEleven.adicCompletionIntegers ℚ)).toAffine.Nonsingular x y) :
    let W' := residueTranslatedIntegralModel
      (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)
      (minimalCompletionAtEleven E) x 0 y
    (genericResidueTranslation
        (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ) x 0 y •
      minimalCompletionAtEleven E).HasAdditiveReduction
        (atEleven.adicCompletionIntegers ℚ) ∧
      W'.a₃ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
      W'.a₄ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
      W'.a₆ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) := by
  exact tateAlgorithm_residueTranslation_of_singularPoint hA x y hequation hsingular

/-- Additive reduction on the selected eleven-adic minimal equation constructs its affine
singular residue point and the corresponding integral translation, with no coordinate choice
left to the order-35 caller. -/
theorem minimalCompletionAtEleven_tateAlgorithm_exists_residueTranslation
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)) :
    ∃ x y : IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ),
      let W' := residueTranslatedIntegralModel
        (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)
        (minimalCompletionAtEleven E) x 0 y
      (genericResidueTranslation
          (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ) x 0 y •
        minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.a₃ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
      W'.a₆ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) := by
  exact tateAlgorithm_exists_residueTranslation_of_hasAdditiveReduction
    hA residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero

/-- The selected eleven-adic minimal equation admits the full residue short normalization used
before the tame Tate blowups.  The transformed special fibre is literally `Y² = X³`, and every
coefficient of the displayed integral lift lies in the eleven-adic maximal ideal. -/
theorem minimalCompletionAtEleven_tateAlgorithm_exists_residueShortNormalization
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)) :
    ∃ r s t : IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ),
      let W' := residueTranslatedIntegralModel
        (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)
        (minimalCompletionAtEleven E) r s t
      (genericResidueTranslation
          (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ) r s t •
        minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.map (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) ∧
        W'.a₁ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
        W'.a₂ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
        W'.a₃ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) := by
  exact tateAlgorithm_exists_residueShortNormalization_of_hasAdditiveReduction
    hA residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero

/-- The selected eleven-adic minimal equation has an exact integral short model in the additive
branch.  Its generic fibre is explicitly the unit-scale transform of the selected completion,
while its special fibre is the standard cusp and its two remaining coefficients vanish modulo
the eleven-adic maximal ideal. -/
theorem minimalCompletionAtEleven_tateAlgorithm_exists_integralShortNormalization
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)) :
    ∃ C : WeierstrassCurve.VariableChange
        (atEleven.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtEleven E).integralModel
        (atEleven.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ))
      (CK • minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ)) = CK • minimalCompletionAtEleven E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atEleven.adicCompletionIntegers ℚ) := by
  exact tateAlgorithm_exists_integralShortNormalization_of_hasAdditiveReduction
    hA residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero

/-- The exact eleven-adic short model carries the three honest one-exceptional-factor equation
charts for the first blowup at its closed cusp. -/
theorem minimalCompletionAtEleven_tateAlgorithm_exists_firstBlowupEquationCharts
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)) :
    ∃ C : WeierstrassCurve.VariableChange
        (atEleven.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtEleven E).integralModel
        (atEleven.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ))
      (CK • minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ)) = CK • minimalCompletionAtEleven E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) ∧
        Nonempty (FirstBlowupEquationCharts W') := by
  exact tateAlgorithm_exists_firstBlowupEquationCharts_of_hasAdditiveReduction
    hA residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero

/-- A marked point of order 35 eliminates the order-one first-blowup branch.  The selected exact
short model therefore has `a₆` in the square of the eleven-adic maximal ideal, while retaining
the one-factor chart data required by the next valuation branch. -/
theorem
    minimalCompletionAtEleven_tateAlgorithm_exists_firstBlowupEquationCharts_of_orderThirtyFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtEleven E).toAffine.Point)
    (horder : addOrderOf P = 35) :
    ∃ C : WeierstrassCurve.VariableChange
        (atEleven.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtEleven E).integralModel
        (atEleven.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ))
      (CK • minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ)) = CK • minimalCompletionAtEleven E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) ∧
        Nonempty (FirstBlowupEquationCharts W') ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atEleven.adicCompletionIntegers ℚ) ^ 2 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, hcharts⟩ :=
    minimalCompletionAtEleven_tateAlgorithm_exists_firstBlowupEquationCharts E hA
  let W' := C • (minimalCompletionAtEleven E).integralModel
    (atEleven.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
    (atEleven.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  obtain ⟨B⟩ := hcharts
  let P' : (CK • minimalCompletionAtEleven E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P
  have horder' : addOrderOf P' = 35 := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P).trans horder
  have ha₆ : W'.a₆ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 2 := by
    by_contra ha₆
    have hb₆ : IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)
        B.coefficients.b₆ ≠ 0 :=
      B.residue_b₆_ne_zero_iff_a₆_not_mem_maximalIdeal_sq.mpr ha₆
    have hΔ : (adicRedCurve W').Δ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atEleven.adicCompletionIntegers ℚ))).Δ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.Δ,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    have hc₄ : (adicRedCurve W').c₄ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atEleven.adicCompletionIntegers ℚ))).c₄ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    exact
      (addOrderOf_ne_thirtyFive_of_firstBlowup_residue_b₆_ne_zeroAtEleven
        hmap B residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero
        hspecial hb₆
        (specialFiberPointAddEquivAtElevenOfCuspidal W' hΔ hc₄) P') horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆⟩

/-- A marked point of exact order 35 also eliminates the branch in which `a₄/ϖ` has nonzero
residue.  Thus the same normalized eleven-adic model has both remaining short coefficients at
the displayed depths.  The pointwise input is only that the marked double has nonsingular
reduction; no Kodaira-type or component-cardinality conclusion is asserted. -/
theorem
    minimalCompletionAtEleven_tateAlgorithm_exists_secondCoefficientDepth_of_orderThirtyFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtEleven E).toAffine.Point)
    (horder : addOrderOf P = 35) :
    ∃ C : WeierstrassCurve.VariableChange
        (atEleven.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtEleven E).integralModel
        (atEleven.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ))
      (CK • minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ)) = CK • minimalCompletionAtEleven E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) ∧
        Nonempty (FirstBlowupEquationCharts W') ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal
          (atEleven.adicCompletionIntegers ℚ) ^ 2 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆⟩ :=
    minimalCompletionAtEleven_tateAlgorithm_exists_firstBlowupEquationCharts_of_orderThirtyFive
      E hA P horder
  let W' := C • (minimalCompletionAtEleven E).integralModel
    (atEleven.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
    (atEleven.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtEleven E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P
  have horder' : addOrderOf P' = 35 := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P).trans horder
  have ha₄ : W'.a₄ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 2 := by
    by_contra ha₄
    have hb₄ : IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)
        B.coefficients.b₄ ≠ 0 :=
      B.residue_b₄_ne_zero_iff_a₄_not_mem_maximalIdeal_sq.mpr ha₄
    have hΔ : (adicRedCurve W').Δ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atEleven.adicCompletionIntegers ℚ))).Δ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.Δ,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    have hc₄ : (adicRedCurve W').c₄ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atEleven.adicCompletionIntegers ℚ))).c₄ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    exact
      (addOrderOf_ne_thirtyFive_of_firstBlowup_residue_b₄_ne_zeroAtEleven
        hmap B residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero
        hspecial hb₄
        (specialFiberPointAddEquivAtElevenOfCuspidal W' hΔ hc₄) P') horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆, ha₄⟩

/-- A marked point of exact order 35 also eliminates the exact depth-two `a₆` branch.  The same
selected integral short model keeps the checked square-depth properties for `a₄` and `a₆`, while
`a₆` lies in the cube of the eleven-adic maximal ideal.  This uses only the pointwise type-IV
tangent--secant theorem and the established component-exponent consumer. -/
theorem
    minimalCompletionAtEleven_tateAlgorithm_exists_thirdCoefficientDepth_of_orderThirtyFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtEleven E).toAffine.Point)
    (horder : addOrderOf P = 35) :
    ∃ C : WeierstrassCurve.VariableChange
        (atEleven.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtEleven E).integralModel
        (atEleven.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ))
      (CK • minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ)) = CK • minimalCompletionAtEleven E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) ∧
        Nonempty (FirstBlowupEquationCharts W') ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal
          (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atEleven.adicCompletionIntegers ℚ) ^ 3 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆, ha₄⟩ :=
    minimalCompletionAtEleven_tateAlgorithm_exists_secondCoefficientDepth_of_orderThirtyFive
      E hA P horder
  let W' := C • (minimalCompletionAtEleven E).integralModel
    (atEleven.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
    (atEleven.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtEleven E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P
  have horder' : addOrderOf P' = 35 := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P).trans horder
  have ha₆cube : W'.a₆ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 3 := by
    by_contra ha₆notcube
    have hΔ : (adicRedCurve W').Δ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atEleven.adicCompletionIntegers ℚ))).Δ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.Δ,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    have hc₄ : (adicRedCurve W').c₄ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atEleven.adicCompletionIntegers ℚ))).c₄ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    exact
      (addOrderOf_ne_thirtyFive_of_a₄_sq_a₆_sq_not_cubeAtEleven
        hmap residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero hspecial
        ha₄ ha₆ ha₆notcube
        (specialFiberPointAddEquivAtElevenOfCuspidal W' hΔ hc₄) P') horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆, ha₄, ha₆cube⟩

/-- On the selected eleven-adic short model, the marked order-35 point determines an
exceptional-cubic root for the chart uniformizer, and that particular root has zero derivative.
The square and cube coefficient depths remain attached to the same model. -/
theorem
    minimalCompletionAtEleven_exists_markedExceptionalCubic_repeatedRoot_of_orderThirtyFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtEleven E).toAffine.Point)
    (horder : addOrderOf P = 35) :
    ∃ C : WeierstrassCurve.VariableChange
        (atEleven.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtEleven E).integralModel
        (atEleven.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ))
      let P' : (CK • minimalCompletionAtEleven E).toAffine.Point :=
        (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P
      (CK • minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ)) = CK • minimalCompletionAtEleven E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) ∧
        ∃ B : FirstBlowupEquationCharts W',
          W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₄ ∈ IsLocalRing.maximalIdeal
              (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atEleven.adicCompletionIntegers ℚ) ^ 3 ∧
            ∃ D : MarkedExceptionalCubicData W'
                (CK • minimalCompletionAtEleven E).toAffine P',
              D.uniformizer = B.uniformizer ∧ D.derivativeResidue = 0 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆, ha₄, ha₆cube⟩ :=
    minimalCompletionAtEleven_tateAlgorithm_exists_thirdCoefficientDepth_of_orderThirtyFive
      E hA P horder
  let W' := C • (minimalCompletionAtEleven E).integralModel
    (atEleven.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
    (atEleven.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtEleven E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P
  have horder' : addOrderOf P' = 35 := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P).trans horder
  have hΔ : (adicRedCurve W').Δ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atEleven.adicCompletionIntegers ℚ))).Δ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hc₄ : (adicRedCurve W').c₄ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atEleven.adicCompletionIntegers ℚ))).c₄ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  let especial := specialFiberPointAddEquivAtElevenOfCuspidal W' hΔ hc₄
  have hPnot : ¬HasNonsingularReduction hmap P' := by
    intro hP
    have hcomponent := (nonsingularReductionSubgroup hmap
      (nonsingularReduction_isAdditive hmap)).nsmul_mem hP 12
    exact
      (addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
        hmap especial P' hcomponent) horder'
  obtain ⟨D, hDuniformizer⟩ :=
    exists_markedExceptionalCubicData_of_not_hasNonsingularReduction
      hmap residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero hspecial
      B.uniformizer B.uniformizer_irreducible ha₄ ha₆cube P' hPnot
  have hderivative : D.derivativeResidue = 0 := by
    by_contra hsimple
    exact
      (addOrderOf_ne_thirtyFive_of_markedExceptionalCubic_simpleRootAtEleven
        hmap residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero hspecial
        D hsimple especial) horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, B,
    ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative⟩

/-- On the same selected eleven-adic short model and for the same chart uniformizer, the marked
repeated exceptional root is zero.  Its coefficient quotients vanish in the residue field, so
the marked abscissa lies in `𝔪²`, `a₄` lies in `𝔪³`, and `a₆` lies in `𝔪⁴`. -/
theorem
    minimalCompletionAtEleven_exists_zeroExceptionalRoot_and_deeperDepths_of_orderThirtyFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtEleven E).toAffine.Point)
    (horder : addOrderOf P = 35) :
    ∃ C : WeierstrassCurve.VariableChange
        (atEleven.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtEleven E).integralModel
        (atEleven.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ))
      let P' : (CK • minimalCompletionAtEleven E).toAffine.Point :=
        (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P
      (CK • minimalCompletionAtEleven E).HasAdditiveReduction
          (atEleven.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ)) = CK • minimalCompletionAtEleven E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) ∧
        ∃ B : FirstBlowupEquationCharts W',
          W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₄ ∈ IsLocalRing.maximalIdeal
              (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atEleven.adicCompletionIntegers ℚ) ^ 3 ∧
            ∃ D : MarkedExceptionalCubicData W'
                (CK • minimalCompletionAtEleven E).toAffine P',
              D.uniformizer = B.uniformizer ∧
                D.derivativeResidue = 0 ∧
                IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) D.X = 0 ∧
                IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) D.A = 0 ∧
                IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) D.B = 0 ∧
                D.x ∈ IsLocalRing.maximalIdeal
                    (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
                W'.a₄ ∈ IsLocalRing.maximalIdeal
                    (atEleven.adicCompletionIntegers ℚ) ^ 3 ∧
                W'.a₆ ∈ IsLocalRing.maximalIdeal
                    (atEleven.adicCompletionIntegers ℚ) ^ 4 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, B,
      ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative⟩ :=
    minimalCompletionAtEleven_exists_markedExceptionalCubic_repeatedRoot_of_orderThirtyFive
      E hA P horder
  let W' := C • (minimalCompletionAtEleven E).integralModel
    (atEleven.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atEleven.adicCompletionIntegers ℚ)
    (atEleven.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtEleven E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P
  have horder' : addOrderOf P' = 35 := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtEleven E) CK).symm P).trans horder
  have hΔ : (adicRedCurve W').Δ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atEleven.adicCompletionIntegers ℚ))).Δ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hc₄ : (adicRedCurve W').c₄ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atEleven.adicCompletionIntegers ℚ))).c₄ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  let especial := specialFiberPointAddEquivAtElevenOfCuspidal W' hΔ hc₄
  have hdepth :=
    markedExceptionalCubic_zeroRoot_and_deeperDepths_of_orderThirtyFiveAtEleven
      hmap residueAtEleven_two_ne_zero residueAtEleven_three_ne_zero hspecial
      D hderivative especial horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, B,
    ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative, hdepth⟩

/-- The selected minimal equation has the base-changed rational
`j`-invariant. -/
theorem minimalCompletionAtEleven_j
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (minimalCompletionAtEleven E).j =
      algebraMap ℚ (atEleven.adicCompletion ℚ) E.j := by
  simp only [minimalCompletionAtEleven, WeierstrassCurve.variableChange_j,
    completionAtEleven, WeierstrassCurve.Affine.baseChange,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_j]

/-- The local valuation on the selected minimal equation agrees with the
eleven-adic valuation of the original rational `j`-invariant. -/
theorem valuation_minimalCompletionAtEleven_j
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    valuation (atEleven.adicCompletion ℚ)
        (IsDiscreteValuationRing.maximalIdeal
          (atEleven.adicCompletionIntegers ℚ))
        (minimalCompletionAtEleven E).j =
      atEleven.valuation ℚ E.j := by
  rw [minimalCompletionAtEleven_j]
  exact atEleven.valuation_adicCompletion_algebraMap
    (IsDiscreteValuationRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ)) E.j

/-- Transport a rational point to the selected minimal eleven-adic equation. -/
noncomputable def minimalCompletionPointAtEleven
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (P : E.toAffine.Point) :
    (minimalCompletionAtEleven E).toAffine.Point :=
  (Point.equivVariableChange (completionAtEleven E)
    (minimalCompletionChangeAtEleven E)).symm
    (E.toAffine.pointMap (atEleven.adicCompletion ℚ) P)

/-- Completion and the selected variable change preserve the marked point's
exact additive order. -/
theorem minimalCompletionPointAtEleven_addOrderOf
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (P : E.toAffine.Point) :
    addOrderOf (minimalCompletionPointAtEleven E P) = addOrderOf P := by
  rw [minimalCompletionPointAtEleven, AddEquiv.addOrderOf_eq]
  exact addOrderOf_injective _
    (pointMap_injective E.toAffine (atEleven.adicCompletion ℚ)) P

/-- The integral model canonically selected from an eleven-adic minimal
equation. -/
noncomputable abbrev completionIntegralModelAtEleven
    (W : WeierstrassCurve (atEleven.adicCompletion ℚ))
    [W.IsIntegral (atEleven.adicCompletionIntegers ℚ)] :
    WeierstrassCurve (atEleven.adicCompletionIntegers ℚ) :=
  W.integralModel (atEleven.adicCompletionIntegers ℚ)

/-- The selected integral model has generic fibre `W`. -/
theorem completionIntegralModelAtEleven_map
    (W : WeierstrassCurve (atEleven.adicCompletion ℚ))
    [W.IsIntegral (atEleven.adicCompletionIntegers ℚ)] :
    (completionIntegralModelAtEleven W).map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W := by
  simpa only [completionIntegralModelAtEleven,
    WeierstrassCurve.baseChange] using
      W.baseChange_integralModel_eq (atEleven.adicCompletionIntegers ℚ)

/-- Good reduction on a minimal eleven-adic equation contradicts a point of
exact order 35 by specialization to the checked `F_11` enumeration. -/
theorem completionPoint_addOrderOf_ne_thirtyFive_of_hasGoodReductionAtEleven
    {W : WeierstrassCurve (atEleven.adicCompletion ℚ)}
    [W.IsElliptic]
    [W.IsMinimal (atEleven.adicCompletionIntegers ℚ)]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hgood : W.HasGoodReduction (atEleven.adicCompletionIntegers ℚ))
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  classical
  let W₀ := completionIntegralModelAtEleven W
  have hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W :=
    completionIntegralModelAtEleven_map W
  letI : (W.reduction
      (atEleven.adicCompletionIntegers ℚ)).IsElliptic :=
    (W.hasGoodReduction_iff_isElliptic_reduction
      (atEleven.adicCompletionIntegers ℚ)).mp hgood
  letI : W₀.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    apply (IsLocalRing.residue_ne_zero_iff_isUnit W₀.Δ).mp
    have hΔ := (W.reduction
      (atEleven.adicCompletionIntegers ℚ)).isUnit_Δ.ne_zero
    change IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) W₀.Δ ≠ 0
    simpa only [WeierstrassCurve.reduction, WeierstrassCurve.map_Δ,
      W₀, completionIntegralModelAtEleven] using hΔ
  let e₁₁ : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ) ≃+* ZMod 11 :=
    (atEleven.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueElevenAlgEquiv.toRingEquiv
  letI : Algebra (atEleven.adicCompletionIntegers ℚ) (ZMod 11) :=
    (e₁₁.toRingHom.comp
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ))).toAlgebra
  let e₁₁Alg : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ) ≃ₐ[atEleven.adicCompletionIntegers ℚ]
        ZMod 11 :=
    { e₁₁ with
      commutes' := fun _ ↦ rfl }
  let W₁₁ : WeierstrassCurve (ZMod 11) :=
    W₀.map (algebraMap (atEleven.adicCompletionIntegers ℚ) (ZMod 11))
  letI : W₁₁.IsElliptic := by
    dsimp only [W₁₁]
    infer_instance
  let redPointEquiv :
      (adicRedCurve W₀).Point ≃+ W₁₁.toAffine.Point :=
    Point.mapEquiv (W' := W₀.toAffine) e₁₁Alg
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    norm_num)
  have hredOrder : addOrderOf (adicRed hW P) = addOrderOf P :=
    addOrderOf_adicRed hW (by norm_num)
      eleven_mem_completion_maximalIdeal
      eleven_not_mem_completion_maximalIdeal_pow_ten hP
  apply reductionAtEleven_addOrderOf_ne_thirtyFive
    W₁₁ (redPointEquiv (adicRed hW P))
  exact (AddEquiv.addOrderOf_eq redPointEquiv (adicRed hW P)).trans
    (hredOrder.trans horder)

/-- Integral `j` and the actual canonical tame-additive handoff force good
reduction and hence exclude exact order 35 on an eleven-adic minimal
equation. -/
theorem
    completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_tameReductionAtEleven
    {W : WeierstrassCurve (atEleven.adicCompletion ℚ)}
    [W.IsElliptic]
    [W.IsMinimal (atEleven.adicCompletionIntegers ℚ)]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : valuation (atEleven.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal
        (atEleven.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (F : W.HasAdditiveReduction (atEleven.adicCompletionIntegers ℚ) →
      TameAdditiveReductionDataAtEleven
        (completionIntegralModelAtEleven_map W))
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  intro horder
  have hgood : W.HasGoodReduction (atEleven.adicCompletionIntegers ℚ) :=
    hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction
      hj P 35
        (fun hA ↦ addOrderOf_ne_thirtyFive_of_tameAdditiveReductionDataAtEleven
          (completionIntegralModelAtEleven_map W) (F hA) P)
        horder
  exact completionPoint_addOrderOf_ne_thirtyFive_of_hasGoodReductionAtEleven
    hgood P horder

/-- The preceding endpoint with the identity subgroup and reduction map
constructed from canonical coordinatewise nonsingular reduction. -/
theorem
    completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_nonsingularReduction
    {W : WeierstrassCurve (atEleven.adicCompletion ℚ)}
    [W.IsElliptic]
    [W.IsMinimal (atEleven.adicCompletionIntegers ℚ)]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : valuation (atEleven.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal
        (atEleven.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (especial : W.HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (completionIntegralModelAtEleven W)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : ∀ (_hA : W.HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      Nat.card (W.toAffine.Point ⧸
        nonsingularReductionSubgroup
          (completionIntegralModelAtEleven_map W)
          (nonsingularReduction_isAdditive
            (completionIntegralModelAtEleven_map W))) ≤ 4)
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_tameReductionAtEleven
    hj
      (fun hA ↦ TameAdditiveReductionDataAtEleven.ofCanonicalNonsingularReduction
        (especial hA) (hcomponent hA))
      P

/-- The completion-level order-35 endpoint with the component geometry reduced to the marked
point.  In the additive branch the caller proves only that `12 • P` has nonsingular reduction;
the canonical reduction homomorphism and exact formal kernel then give the additive-order
contradiction without constructing the full component quotient. -/
theorem
    completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_componentExponentTwelve
    {W : WeierstrassCurve (atEleven.adicCompletion ℚ)}
    [W.IsElliptic]
    [W.IsMinimal (atEleven.adicCompletionIntegers ℚ)]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : valuation (atEleven.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal
        (atEleven.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (especial : W.HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (completionIntegralModelAtEleven W)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (P : W.toAffine.Point)
    (hcomponent : ∀ (_hA : W.HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      12 • P ∈ nonsingularReductionSubgroup
        (completionIntegralModelAtEleven_map W)
        (nonsingularReduction_isAdditive
          (completionIntegralModelAtEleven_map W))) :
    addOrderOf P ≠ 35 := by
  intro horder
  have hgood : W.HasGoodReduction (atEleven.adicCompletionIntegers ℚ) :=
    hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction
      hj P 35
        (fun hA ↦
          addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
            (completionIntegralModelAtEleven_map W) (especial hA) P (hcomponent hA))
        horder
  exact completionPoint_addOrderOf_ne_thirtyFive_of_hasGoodReductionAtEleven
    hgood P horder

/-- The integral equation on the selected minimal completion used by the
order-35 canonical nonsingular-reduction consumer. -/
noncomputable abbrev minimalCompletionIntegralModelAtEleven
    (E : WeierstrassCurve ℚ) :
    WeierstrassCurve (atEleven.adicCompletionIntegers ℚ) :=
  completionIntegralModelAtEleven (minimalCompletionAtEleven E)

/-- The named integral model has the selected minimal completion as generic
fibre. -/
theorem minimalCompletionIntegralModelAtEleven_map
    (E : WeierstrassCurve ℚ) :
    (minimalCompletionIntegralModelAtEleven E).map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) =
      minimalCompletionAtEleven E :=
  completionIntegralModelAtEleven_map (minimalCompletionAtEleven E)

/-- Rational order 35 is excluded from the eleven-adic valuation bound and
canonical nonsingular-reduction geometry on the selected minimal equation. -/
theorem
    rationalPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_nonsingularReductionAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : atEleven.valuation ℚ E.j ≤ 1)
    (especial : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtEleven E)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : ∀ (_hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      Nat.card ((minimalCompletionAtEleven E).toAffine.Point ⧸
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E))) ≤ 4)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  have hj' : valuation (atEleven.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal
        (atEleven.adicCompletionIntegers ℚ))
      (minimalCompletionAtEleven E).j ≤ 1 := by
    rw [valuation_minimalCompletionAtEleven_j]
    exact hj
  intro horder
  apply
    completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_nonsingularReduction
      hj' especial hcomponent (minimalCompletionPointAtEleven E P)
  exact (minimalCompletionPointAtEleven_addOrderOf E P).trans horder

/-- Rational order 35 is excluded using the eleven-adic valuation bound and only the
marked-point component-exponent statement on the selected minimal equation. -/
theorem
    rationalPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_componentExponentTwelveAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : atEleven.valuation ℚ E.j ≤ 1)
    (especial : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtEleven E)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (P : E.toAffine.Point)
    (hcomponent : ∀ (_hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      12 • minimalCompletionPointAtEleven E P ∈
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E))) :
    addOrderOf P ≠ 35 := by
  have hj' : valuation (atEleven.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal
        (atEleven.adicCompletionIntegers ℚ))
      (minimalCompletionAtEleven E).j ≤ 1 := by
    rw [valuation_minimalCompletionAtEleven_j]
    exact hj
  intro horder
  apply
    completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_componentExponentTwelve
      hj' especial (minimalCompletionPointAtEleven E P) hcomponent
  exact (minimalCompletionPointAtEleven_addOrderOf E P).trans horder

end MazurTorsion.OrderThirtyFive
