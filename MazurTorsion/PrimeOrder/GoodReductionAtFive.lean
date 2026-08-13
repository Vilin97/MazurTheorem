/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.PrimeOrder.FiniteFieldFiveOrder
import MazurTorsion.PrimeOrder.TameAdditiveAtFive
import MazurTorsion.PrimeOrder.TorsionSpecialization
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# The prime-order contradiction after good reduction at five

This module joins the unramified formal-kernel specialization theorem to the
checked enumeration of elliptic curves over `F_5`.  It is the downstream
consumer required by the formal-immersion route once the preceding local
argument has supplied an integral model with good reduction at five.
-/

open WeierstrassCurve

namespace MazurTorsion.PrimeOrder

open WeierstrassCurve.Affine
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum

noncomputable local instance : DecidableEq
    (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

private theorem residueAtFive_natCast_ne_zero
    (n : ℕ) (hn : (n : ZMod 5) ≠ 0) :
    (n : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0 := by
  let e₅ : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ) ≃+* ZMod 5 :=
    (atFive.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueFiveAlgEquiv.toRingEquiv
  intro h
  apply hn
  calc
    (n : ZMod 5) = e₅ (n : IsLocalRing.ResidueField
        (atFive.adicCompletionIntegers ℚ)) := (map_natCast e₅ n).symm
    _ = e₅ 0 := congrArg e₅ h
    _ = 0 := by simp

private theorem residueAtFive_two_ne_zero :
    (2 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0 :=
  residueAtFive_natCast_ne_zero 2 (by decide)

private theorem residueAtFive_three_ne_zero :
    (3 : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ)) ≠ 0 :=
  residueAtFive_natCast_ne_zero 3 (by decide)

/-- If an integral model has good reduction at five, none of its rational
torsion points has exact order at least eleven. -/
theorem rationalPoint_addOrderOf_ne_of_eleven_le_of_goodReductionAtFive
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atFive W₀).IsElliptic]
    {P : E.Point} {N : ℕ} (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    omega)
  letI : (reductionCurveAtFive W₀).IsElliptic := reductionCurveAtFive_isElliptic W₀
  apply zmod_five_addOrderOf_ne_of_eleven_le
    (reductionCurveAtFive W₀) (reductionAtFiveToZMod hE P) N hN
  exact (specializedPointZMod_addOrderOf_eq_atFive_of_goodReduction hE hP).trans horder

/-- Coefficientwise base change of a rational Weierstrass equation to the five-adic
completion. -/
noncomputable abbrev completionAtFive (E : WeierstrassCurve ℚ) :
    WeierstrassCurve (atFive.adicCompletion ℚ) :=
  E.toAffine ⁄ (atFive.adicCompletion ℚ)

instance completionAtFive_isElliptic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (completionAtFive E).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  dsimp only [completionAtFive, WeierstrassCurve.Affine.baseChange,
    WeierstrassCurve.baseChange]
  rw [WeierstrassCurve.map_Δ]
  exact E.isUnit_Δ.map _

/-- The admissible variable change selected by Mathlib's existence proof for a minimal equation
over the five-adic valuation ring. -/
noncomputable def minimalCompletionChangeAtFive (E : WeierstrassCurve ℚ) :
    WeierstrassCurve.VariableChange (atFive.adicCompletion ℚ) :=
  ((completionAtFive E).exists_isMinimal
    (atFive.adicCompletionIntegers ℚ)).choose

/-- The minimal five-adic equation selected by Mathlib after coefficientwise base change from a
rational Weierstrass equation. -/
noncomputable abbrev minimalCompletionAtFive (E : WeierstrassCurve ℚ) :
    WeierstrassCurve (atFive.adicCompletion ℚ) :=
  minimalCompletionChangeAtFive E • completionAtFive E

/-- The named change used here is definitionally the one in Mathlib's `minimal` construction. -/
theorem minimalCompletionAtFive_eq_mathlibMinimal (E : WeierstrassCurve ℚ) :
    minimalCompletionAtFive E =
      (completionAtFive E).minimal (atFive.adicCompletionIntegers ℚ) :=
  rfl

noncomputable instance minimalCompletionAtFive_isMinimal (E : WeierstrassCurve ℚ) :
    (minimalCompletionAtFive E).IsMinimal (atFive.adicCompletionIntegers ℚ) := by
  exact ((completionAtFive E).exists_isMinimal
    (atFive.adicCompletionIntegers ℚ)).choose_spec

noncomputable instance minimalCompletionAtFive_isElliptic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (minimalCompletionAtFive E).IsElliptic := by
  dsimp only [minimalCompletionAtFive]
  infer_instance

/-- On the selected five-adic minimal equation, a singular special-fibre point supplies an actual
integral unit-scale translation to the origin.  The translated equation stays additive and its
explicit integral model has `a₃`, `a₄`, and `a₆` in the five-adic maximal ideal. -/
theorem minimalCompletionAtFive_tateAlgorithm_residueTranslation_of_singularPoint
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ))
    (x y : IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (hequation : ((minimalCompletionAtFive E).reduction
      (atFive.adicCompletionIntegers ℚ)).toAffine.Equation x y)
    (hsingular : ¬ ((minimalCompletionAtFive E).reduction
      (atFive.adicCompletionIntegers ℚ)).toAffine.Nonsingular x y) :
    let W' := residueTranslatedIntegralModel
      (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)
      (minimalCompletionAtFive E) x 0 y
    (genericResidueTranslation
        (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ) x 0 y •
      minimalCompletionAtFive E).HasAdditiveReduction
        (atFive.adicCompletionIntegers ℚ) ∧
      W'.a₃ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
      W'.a₄ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
      W'.a₆ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) := by
  exact tateAlgorithm_residueTranslation_of_singularPoint hA x y hequation hsingular

/-- Additive reduction on the selected five-adic minimal equation constructs the singular
residue coordinates and their integral translation without any coordinate premise from the
caller. -/
theorem minimalCompletionAtFive_tateAlgorithm_exists_residueTranslation
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)) :
    ∃ x y : IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ),
      let W' := residueTranslatedIntegralModel
        (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)
        (minimalCompletionAtFive E) x 0 y
      (genericResidueTranslation
          (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ) x 0 y •
        minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.a₃ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) := by
  exact tateAlgorithm_exists_residueTranslation_of_hasAdditiveReduction
    hA residueAtFive_two_ne_zero residueAtFive_three_ne_zero

/-- The selected five-adic minimal equation admits the full residue short normalization used
before the tame Tate blowups.  The transformed special fibre is literally `Y² = X³`, and every
coefficient of the displayed integral lift lies in the five-adic maximal ideal. -/
theorem minimalCompletionAtFive_tateAlgorithm_exists_residueShortNormalization
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)) :
    ∃ r s t : IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ),
      let W' := residueTranslatedIntegralModel
        (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)
        (minimalCompletionAtFive E) r s t
      (genericResidueTranslation
          (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ) r s t •
        minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        W'.a₁ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
        W'.a₂ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
        W'.a₃ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) := by
  exact tateAlgorithm_exists_residueShortNormalization_of_hasAdditiveReduction
    hA residueAtFive_two_ne_zero residueAtFive_three_ne_zero

/-- The selected five-adic minimal equation has an exact integral short model in the additive
branch.  Its generic fibre is explicitly the unit-scale transform of the selected completion,
while its special fibre is the standard cusp and its two remaining coefficients vanish modulo
the five-adic maximal ideal. -/
theorem minimalCompletionAtFive_tateAlgorithm_exists_integralShortNormalization
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)) :
    ∃ C : WeierstrassCurve.VariableChange (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal (atFive.adicCompletionIntegers ℚ) := by
  exact tateAlgorithm_exists_integralShortNormalization_of_hasAdditiveReduction
    hA residueAtFive_two_ne_zero residueAtFive_three_ne_zero

/-- The exact five-adic short model carries the three honest one-exceptional-factor equation
charts for the first blowup at its closed cusp. -/
theorem minimalCompletionAtFive_tateAlgorithm_exists_firstBlowupEquationCharts
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)) :
    ∃ C : WeierstrassCurve.VariableChange (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        Nonempty (FirstBlowupEquationCharts W') := by
  exact tateAlgorithm_exists_firstBlowupEquationCharts_of_hasAdditiveReduction
    hA residueAtFive_two_ne_zero residueAtFive_three_ne_zero

/-- A marked prime-order point eliminates the order-one first-blowup branch.  The selected exact
short model therefore has `a₆` in the square of the five-adic maximal ideal, while retaining the
honest one-factor chart data needed by the next valuation branch. -/
theorem minimalCompletionAtFive_tateAlgorithm_exists_firstBlowupEquationCharts_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    ∃ C : WeierstrassCurve.VariableChange
        (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        Nonempty (FirstBlowupEquationCharts W') ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atFive.adicCompletionIntegers ℚ) ^ 2 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, hcharts⟩ :=
    minimalCompletionAtFive_tateAlgorithm_exists_firstBlowupEquationCharts E hA
  let W' := C • (minimalCompletionAtFive E).integralModel
    (atFive.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
    (atFive.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  obtain ⟨B⟩ := hcharts
  let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
  have horder' : addOrderOf P' = N := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P).trans horder
  have ha₆ : W'.a₆ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 2 := by
    by_contra ha₆
    have hb₆ : IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)
        B.coefficients.b₆ ≠ 0 :=
      B.residue_b₆_ne_zero_iff_a₆_not_mem_maximalIdeal_sq.mpr ha₆
    have hΔ : (adicRedCurve W').Δ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atFive.adicCompletionIntegers ℚ))).Δ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.Δ,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    have hc₄ : (adicRedCurve W').c₄ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atFive.adicCompletionIntegers ℚ))).c₄ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    exact
      (addOrderOf_ne_prime_ge_eleven_of_firstBlowup_residue_b₆_ne_zeroAtFive
        hmap B residueAtFive_two_ne_zero residueAtFive_three_ne_zero
        hspecial hb₆
        (specialFiberPointAddEquivAtFiveOfCuspidal W' hΔ hc₄)
        P' N hprime hN) horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆⟩

/-- A marked prime-order point also eliminates the branch in which `a₄/ϖ` has nonzero residue.
On the same exact short model, both `a₆` and `a₄` therefore lie in the indicated square of the
maximal ideal.  The proof uses the checked pointwise statement that the double enters canonical
nonsingular reduction; it makes no Kodaira-type assertion. -/
theorem minimalCompletionAtFive_tateAlgorithm_exists_secondCoefficientDepth_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    ∃ C : WeierstrassCurve.VariableChange
        (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        Nonempty (FirstBlowupEquationCharts W') ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal
          (atFive.adicCompletionIntegers ℚ) ^ 2 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆⟩ :=
    minimalCompletionAtFive_tateAlgorithm_exists_firstBlowupEquationCharts_of_primeOrder
      E hA P N hprime hN horder
  let W' := C • (minimalCompletionAtFive E).integralModel
    (atFive.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
    (atFive.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
  have horder' : addOrderOf P' = N := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P).trans horder
  have ha₄ : W'.a₄ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 2 := by
    by_contra ha₄
    have hb₄ : IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)
        B.coefficients.b₄ ≠ 0 :=
      B.residue_b₄_ne_zero_iff_a₄_not_mem_maximalIdeal_sq.mpr ha₄
    have hΔ : (adicRedCurve W').Δ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atFive.adicCompletionIntegers ℚ))).Δ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.Δ,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    have hc₄ : (adicRedCurve W').c₄ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atFive.adicCompletionIntegers ℚ))).c₄ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    exact
      (addOrderOf_ne_prime_ge_eleven_of_firstBlowup_residue_b₄_ne_zeroAtFive
        hmap B residueAtFive_two_ne_zero residueAtFive_three_ne_zero
        hspecial hb₄
        (specialFiberPointAddEquivAtFiveOfCuspidal W' hΔ hc₄)
        P' N hprime hN) horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆, ha₄⟩

/-- The same marked prime-order point eliminates the exact depth-two `a₆` branch.  On one selected
integral short model, `a₄` and `a₆` retain their checked square-depth properties and `a₆` in fact
lies in the cube of the maximal ideal.  The only new geometric input is the pointwise type-IV
tangent--secant theorem; no Kodaira symbol or component-cardinality assertion is used. -/
theorem minimalCompletionAtFive_tateAlgorithm_exists_thirdCoefficientDepth_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    ∃ C : WeierstrassCurve.VariableChange
        (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        Nonempty (FirstBlowupEquationCharts W') ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
        W'.a₄ ∈ IsLocalRing.maximalIdeal
          (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
        W'.a₆ ∈ IsLocalRing.maximalIdeal
          (atFive.adicCompletionIntegers ℚ) ^ 3 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆, ha₄⟩ :=
    minimalCompletionAtFive_tateAlgorithm_exists_secondCoefficientDepth_of_primeOrder
      E hA P N hprime hN horder
  let W' := C • (minimalCompletionAtFive E).integralModel
    (atFive.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
    (atFive.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
  have horder' : addOrderOf P' = N := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P).trans horder
  have ha₆cube : W'.a₆ ∈ IsLocalRing.maximalIdeal
      (atFive.adicCompletionIntegers ℚ) ^ 3 := by
    by_contra ha₆notcube
    have hΔ : (adicRedCurve W').Δ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atFive.adicCompletionIntegers ℚ))).Δ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.Δ,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    have hc₄ : (adicRedCurve W').c₄ = 0 := by
      change (W'.map (IsLocalRing.residue
        (atFive.adicCompletionIntegers ℚ))).c₄ = 0
      rw [hspecial]
      simp [cuspidalShortCurve, WeierstrassCurve.c₄,
        WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    exact
      (addOrderOf_ne_prime_ge_eleven_of_a₄_sq_a₆_sq_not_cubeAtFive
        hmap residueAtFive_two_ne_zero residueAtFive_three_ne_zero hspecial
        ha₄ ha₆ ha₆notcube
        (specialFiberPointAddEquivAtFiveOfCuspidal W' hΔ hc₄)
        P' N hprime hN) horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆, ha₄, ha₆cube⟩

/-- On the selected five-adic short model, the marked point determines an exceptional-cubic root
for the chart uniformizer, and that particular root has zero derivative.  The square and cube
coefficient depths are retained on the same model.  No assertion is made about any other root. -/
theorem
    minimalCompletionAtFive_tateAlgorithm_exists_markedExceptionalCubic_repeatedRoot_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    ∃ C : WeierstrassCurve.VariableChange
        (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
        (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        ∃ B : FirstBlowupEquationCharts W',
          W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₄ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
            ∃ D : MarkedExceptionalCubicData W'
                (CK • minimalCompletionAtFive E).toAffine P',
              D.uniformizer = B.uniformizer ∧ D.derivativeResidue = 0 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, ⟨B⟩, ha₆, ha₄, ha₆cube⟩ :=
    minimalCompletionAtFive_tateAlgorithm_exists_thirdCoefficientDepth_of_primeOrder
      E hA P N hprime hN horder
  let W' := C • (minimalCompletionAtFive E).integralModel
    (atFive.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
    (atFive.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
  have horder' : addOrderOf P' = N := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P).trans horder
  have hΔ : (adicRedCurve W').Δ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atFive.adicCompletionIntegers ℚ))).Δ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hc₄ : (adicRedCurve W').c₄ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atFive.adicCompletionIntegers ℚ))).c₄ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  let especial := specialFiberPointAddEquivAtFiveOfCuspidal W' hΔ hc₄
  have hPnot : ¬HasNonsingularReduction hmap P' := by
    intro hP
    have hcomponent := (nonsingularReductionSubgroup hmap
      (nonsingularReduction_isAdditive hmap)).nsmul_mem hP 12
    exact
      (addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
        hmap especial P' hcomponent N hprime hN) horder'
  obtain ⟨D, hDuniformizer⟩ :=
    exists_markedExceptionalCubicData_of_not_hasNonsingularReduction
      hmap residueAtFive_two_ne_zero residueAtFive_three_ne_zero hspecial
      B.uniformizer B.uniformizer_irreducible ha₄ ha₆cube P' hPnot
  have hderivative : D.derivativeResidue = 0 := by
    by_contra hsimple
    exact
      (addOrderOf_ne_prime_ge_eleven_of_markedExceptionalCubic_simpleRootAtFive
        hmap residueAtFive_two_ne_zero residueAtFive_three_ne_zero hspecial
        D hsimple especial N hprime hN) horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, B,
    ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative⟩

/-- On the same selected five-adic short model and for the same chart uniformizer, the marked
repeated exceptional root is zero.  Its coefficient quotients vanish in the residue field, so
the marked abscissa lies in `𝔪²`, `a₄` lies in `𝔪³`, and `a₆` lies in `𝔪⁴`. -/
theorem
    minimalCompletionAtFive_exists_zeroExceptionalRoot_and_deeperDepths_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    ∃ C : WeierstrassCurve.VariableChange
        (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
        (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        ∃ B : FirstBlowupEquationCharts W',
          W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₄ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
            ∃ D : MarkedExceptionalCubicData W'
                (CK • minimalCompletionAtFive E).toAffine P',
              D.uniformizer = B.uniformizer ∧
                D.derivativeResidue = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.X = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.A = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.B = 0 ∧
                D.x ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
                W'.a₄ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
                W'.a₆ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 4 := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, B,
      ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative⟩ :=
    minimalCompletionAtFive_tateAlgorithm_exists_markedExceptionalCubic_repeatedRoot_of_primeOrder
      E hA P N hprime hN horder
  let W' := C • (minimalCompletionAtFive E).integralModel
    (atFive.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
    (atFive.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
  have horder' : addOrderOf P' = N := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P).trans horder
  have hΔ : (adicRedCurve W').Δ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atFive.adicCompletionIntegers ℚ))).Δ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hc₄ : (adicRedCurve W').c₄ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atFive.adicCompletionIntegers ℚ))).c₄ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  let especial := specialFiberPointAddEquivAtFiveOfCuspidal W' hΔ hc₄
  have hdepth :=
    markedExceptionalCubic_zeroRoot_and_deeperDepths_of_primeOrderAtFive
      hmap residueAtFive_two_ne_zero residueAtFive_three_ne_zero hspecial
      D hderivative especial N hprime hN horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, B,
    ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative, hdepth⟩

private abbrev FifthCoefficientDepthAtFive
    (E : WeierstrassCurve ℚ)
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : (minimalCompletionAtFive E).toAffine.Point) : Prop :=
    ∃ C : WeierstrassCurve.VariableChange
        (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
        (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        ∃ B : FirstBlowupEquationCharts W',
          W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₄ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
            ∃ D : MarkedExceptionalCubicData W'
                (CK • minimalCompletionAtFive E).toAffine P',
              D.uniformizer = B.uniformizer ∧
                D.derivativeResidue = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.X = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.A = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.B = 0 ∧
                D.x ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
                W'.a₄ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
                W'.a₆ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 4 ∧
                W'.a₆ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 5

/-- The selected five-adic model, chart, marked point, and uniformizer from the preceding endpoint
also satisfy `a₆ ∈ 𝔪⁵`.  No coordinate choice is replaced while gaining this depth. -/
theorem minimalCompletionAtFive_exists_fifthCoefficientDepth_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) : FifthCoefficientDepthAtFive E P := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, B,
      ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative,
      hroot, hAres, hBres, hxsq, ha₄cube, ha₆four⟩ :=
    minimalCompletionAtFive_exists_zeroExceptionalRoot_and_deeperDepths_of_primeOrder
      E hA P N hprime hN horder
  let W' := C • (minimalCompletionAtFive E).integralModel
    (atFive.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
    (atFive.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
  have horder' : addOrderOf P' = N := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P).trans horder
  have hΔ : (adicRedCurve W').Δ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atFive.adicCompletionIntegers ℚ))).Δ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hc₄ : (adicRedCurve W').c₄ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atFive.adicCompletionIntegers ℚ))).c₄ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  let especial := specialFiberPointAddEquivAtFiveOfCuspidal W' hΔ hc₄
  have ha₆five :=
    markedExceptionalCubic_a₆_mem_fifth_of_primeOrderAtFive
      hmap residueAtFive_two_ne_zero residueAtFive_three_ne_zero hspecial
      D hxsq ha₄cube especial N hprime hN horder'
  exact ⟨C, hAdditive, hmap, hshort, hspecial, B,
    ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative,
    hroot, hAres, hBres, hxsq, ha₄cube, ha₆four, ha₆five⟩

private abbrev SixthCoefficientDepthAtFive
    (E : WeierstrassCurve ℚ)
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : (minimalCompletionAtFive E).toAffine.Point) : Prop :=
    ∃ C : WeierstrassCurve.VariableChange
        (atFive.adicCompletionIntegers ℚ),
      let W' := C • (minimalCompletionAtFive E).integralModel
        (atFive.adicCompletionIntegers ℚ)
      let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ))
      let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
        (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
      (CK • minimalCompletionAtFive E).HasAdditiveReduction
          (atFive.adicCompletionIntegers ℚ) ∧
        W'.map (algebraMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ)) = CK • minimalCompletionAtFive E ∧
        W'.IsShortNF ∧
        W'.map (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ)) =
          cuspidalShortCurve
            (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) ∧
        ∃ B : FirstBlowupEquationCharts W',
          W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₄ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
            W'.a₆ ∈ IsLocalRing.maximalIdeal
              (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
            ∃ D : MarkedExceptionalCubicData W'
                (CK • minimalCompletionAtFive E).toAffine P',
              D.uniformizer = B.uniformizer ∧
                D.derivativeResidue = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.X = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.A = 0 ∧
                IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) D.B = 0 ∧
                D.x ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 2 ∧
                W'.a₄ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
                W'.a₆ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 4 ∧
                W'.a₆ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 5 ∧
                D.y ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 3 ∧
                W'.a₄ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 4 ∧
                W'.a₆ ∈ IsLocalRing.maximalIdeal
                    (atFive.adicCompletionIntegers ℚ) ^ 6

/-- The same selected five-adic short model reaches the terminal weighted
depths.  In particular the marked ordinate lies in `𝔪³`, `a₄` lies in
`𝔪⁴`, and the equation then puts `a₆` in `𝔪⁶`. -/
theorem minimalCompletionAtFive_exists_sixthCoefficientDepth_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ))
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) : SixthCoefficientDepthAtFive E P := by
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, B,
      ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative,
      hroot, hAres, hBres, hxsq, ha₄cube, ha₆four, ha₆five⟩ :=
    minimalCompletionAtFive_exists_fifthCoefficientDepth_of_primeOrder
      E hA P N hprime hN horder
  let W' := C • (minimalCompletionAtFive E).integralModel
    (atFive.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
    (atFive.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  let P' : (CK • minimalCompletionAtFive E).toAffine.Point :=
    (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P
  have horder' : addOrderOf P' = N := by
    exact (AddEquiv.addOrderOf_eq
      (Point.equivVariableChange (minimalCompletionAtFive E) CK).symm P).trans horder
  have hΔ : (adicRedCurve W').Δ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atFive.adicCompletionIntegers ℚ))).Δ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.Δ,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hc₄ : (adicRedCurve W').c₄ = 0 := by
    change (W'.map (IsLocalRing.residue
      (atFive.adicCompletionIntegers ℚ))).c₄ = 0
    rw [hspecial]
    simp [cuspidalShortCurve, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  let especial := specialFiberPointAddEquivAtFiveOfCuspidal W' hΔ hc₄
  have hycube :=
    markedExceptionalCubic_y_mem_cube_of_coefficient_depths
      hmap D hxsq ha₄cube ha₆five
  have ha₄four := markedExceptionalCubic_a₄_mem_fourth_of_primeOrderAtFive
    hmap residueAtFive_two_ne_zero residueAtFive_three_ne_zero hspecial
      D hxsq ha₄cube ha₆five especial N hprime hN horder'
  have ha₆six := markedExceptionalCubic_a₆_mem_sixth_of_coefficient_depths
    hmap D hxsq ha₄four ha₆five
  exact ⟨C, hAdditive, hmap, hshort, hspecial, B,
    ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative,
    hroot, hAres, hBres, hxsq, ha₄cube, ha₆four, ha₆five,
    hycube, ha₄four, ha₆six⟩

/-- A prime-order point on the selected minimal five-adic equation excludes
the additive branch.  The terminal weighted depths would permit one further
integral pure scaling, contradicting minimality of the unit-change model. -/
theorem minimalCompletionAtFive_not_hasAdditiveReduction_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    ¬(minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) := by
  intro hA
  obtain ⟨C, hAdditive, hmap, hshort, hspecial, B,
      ha₆, ha₄, ha₆cube, D, hDuniformizer, hderivative,
      hroot, hAres, hBres, hxsq, ha₄cube, ha₆four, ha₆five,
      hycube, ha₄four, ha₆six⟩ :=
    minimalCompletionAtFive_exists_sixthCoefficientDepth_of_primeOrder
      E hA P N hprime hN horder
  let W' := C • (minimalCompletionAtFive E).integralModel
    (atFive.adicCompletionIntegers ℚ)
  let CK := C.map (algebraMap (atFive.adicCompletionIntegers ℚ)
    (atFive.adicCompletion ℚ))
  letI : W'.IsShortNF := hshort
  exact
    (not_isMinimal_of_short_model_weighted_coefficient_depths
      hmap D.uniformizer D.uniformizer_irreducible ha₄four ha₆six)
      hAdditive.toIsMinimal

/-- Stable prime-route endpoint: a marked point of exact prime order at least
eleven excludes additive reduction on the selected five-adic minimal model. -/
theorem not_additiveReductionAtFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    ¬(minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) :=
  minimalCompletionAtFive_not_hasAdditiveReduction_of_primeOrder
    E P N hprime hN horder

/-- Integral `j` and a marked prime-order point force good reduction on
Mathlib's selected five-adic minimal equation.  The additive branch is now
closed by the checked marked-point depth and minimality argument. -/
theorem minimalCompletionAtFive_hasGoodReduction_of_valuation_j_le_one_of_primeOrder
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal
        (atFive.adicCompletionIntegers ℚ))
      (minimalCompletionAtFive E).j ≤ 1)
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    (minimalCompletionAtFive E).HasGoodReduction
      (atFive.adicCompletionIntegers ℚ) := by
  exact hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction
    hj P N
      (fun hA horder' ↦
        (not_additiveReductionAtFive E P N hprime hN horder') hA)
      horder

/-- Stable prime-route endpoint: integral `j` and a marked point of exact
prime order at least eleven force good reduction at five. -/
theorem goodReductionAtFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal
        (atFive.adicCompletionIntegers ℚ))
      (minimalCompletionAtFive E).j ≤ 1)
    (P : (minimalCompletionAtFive E).toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    (minimalCompletionAtFive E).HasGoodReduction
      (atFive.adicCompletionIntegers ℚ) :=
  minimalCompletionAtFive_hasGoodReduction_of_valuation_j_le_one_of_primeOrder
    E hj P N hprime hN horder

/-- The `j`-invariant of the selected minimal completion is the image of the original rational
`j`-invariant.  Both coefficient extension and the chosen admissible variable change are made
explicit in the construction above. -/
theorem minimalCompletionAtFive_j
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (minimalCompletionAtFive E).j =
      algebraMap ℚ (atFive.adicCompletion ℚ) E.j := by
  simp only [minimalCompletionAtFive, WeierstrassCurve.variableChange_j,
    completionAtFive, WeierstrassCurve.Affine.baseChange,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_j]

/-- The local valuation of the selected minimal equation's `j`-invariant is exactly the original
five-adic valuation of the rational `j`-invariant. -/
theorem valuation_minimalCompletionAtFive_j
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    valuation (atFive.adicCompletion ℚ)
        (IsDiscreteValuationRing.maximalIdeal (atFive.adicCompletionIntegers ℚ))
        (minimalCompletionAtFive E).j =
      atFive.valuation ℚ E.j := by
  rw [minimalCompletionAtFive_j]
  exact atFive.valuation_adicCompletion_algebraMap
    (IsDiscreteValuationRing.maximalIdeal (atFive.adicCompletionIntegers ℚ)) E.j

/-- Transport a rational point first into the five-adic completion and then through the inverse
of the admissible variable change defining Mathlib's selected minimal equation. -/
noncomputable def minimalCompletionPointAtFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : E.toAffine.Point) :
    (minimalCompletionAtFive E).toAffine.Point :=
  (Point.equivVariableChange (completionAtFive E)
    (minimalCompletionChangeAtFive E)).symm
    (E.toAffine.pointMap (atFive.adicCompletion ℚ) P)

/-- Base change to the five-adic completion and passage to the selected minimal equation preserve
the exact additive order of the marked rational point. -/
theorem minimalCompletionPointAtFive_addOrderOf
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : E.toAffine.Point) :
    addOrderOf (minimalCompletionPointAtFive E P) = addOrderOf P := by
  rw [minimalCompletionPointAtFive, AddEquiv.addOrderOf_eq]
  exact addOrderOf_injective _
    (pointMap_injective E.toAffine (atFive.adicCompletion ℚ)) P

/-- The integral model canonically selected from a five-adic integral equation. -/
noncomputable abbrev completionIntegralModelAtFive
    (W : WeierstrassCurve (atFive.adicCompletion ℚ))
    [W.IsIntegral (atFive.adicCompletionIntegers ℚ)] :
    WeierstrassCurve (atFive.adicCompletionIntegers ℚ) :=
  W.integralModel (atFive.adicCompletionIntegers ℚ)

/-- The selected five-adic integral model has generic fibre `W`. -/
theorem completionIntegralModelAtFive_map
    (W : WeierstrassCurve (atFive.adicCompletion ℚ))
    [W.IsIntegral (atFive.adicCompletionIntegers ℚ)] :
    (completionIntegralModelAtFive W).map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W := by
  simpa only [completionIntegralModelAtFive,
    WeierstrassCurve.baseChange] using
      W.baseChange_integralModel_eq (atFive.adicCompletionIntegers ℚ)

/-- A minimal elliptic curve over the completion of `ℚ` at five with good reduction has no
point of exact order at least eleven.

The integral model is Mathlib's `integralModel` over the completed valuation ring.  Good
reduction makes that integral equation elliptic, so the exact-pinned `adicRed` theorem preserves
the order of torsion.  Finally, the canonical residue-field equivalence
`ResidueField 𝒪₅ ≃+* ZMod 5` transports the reduced point to the checked finite enumeration.

This theorem starts after good reduction has been established.  It does not construct a minimal
model, prove integral `j`, or build the additive Néron filtration used to reach good reduction. -/
theorem completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive
    {W : WeierstrassCurve (atFive.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atFive.adicCompletionIntegers ℚ)]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hgood : W.HasGoodReduction (atFive.adicCompletionIntegers ℚ))
    (P : W.toAffine.Point) (N : ℕ) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  classical
  let W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ) :=
    W.integralModel (atFive.adicCompletionIntegers ℚ)
  have hW : W₀.map (algebraMap (atFive.adicCompletionIntegers ℚ)
      (atFive.adicCompletion ℚ)) = W := by
    simpa only [W₀, WeierstrassCurve.baseChange] using
      W.baseChange_integralModel_eq (atFive.adicCompletionIntegers ℚ)
  letI : (W.reduction (atFive.adicCompletionIntegers ℚ)).IsElliptic :=
    (W.hasGoodReduction_iff_isElliptic_reduction
      (atFive.adicCompletionIntegers ℚ)).mp hgood
  letI : W₀.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    apply (IsLocalRing.residue_ne_zero_iff_isUnit W₀.Δ).mp
    have hΔ := (W.reduction
      (atFive.adicCompletionIntegers ℚ)).isUnit_Δ.ne_zero
    simpa only [WeierstrassCurve.reduction, WeierstrassCurve.map_Δ, W₀] using hΔ
  let e₅ : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ) ≃+* ZMod 5 :=
    (atFive.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueFiveAlgEquiv.toRingEquiv
  letI : Algebra (atFive.adicCompletionIntegers ℚ) (ZMod 5) :=
    (e₅.toRingHom.comp
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ))).toAlgebra
  let e₅Alg : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ) ≃ₐ[atFive.adicCompletionIntegers ℚ]
        ZMod 5 :=
    { e₅ with
      commutes' := fun _ ↦ rfl }
  let W₅ : WeierstrassCurve (ZMod 5) :=
    W₀.map (algebraMap (atFive.adicCompletionIntegers ℚ) (ZMod 5))
  letI : W₅.IsElliptic := by
    dsimp only [W₅]
    infer_instance
  let redPointEquiv :
      (adicRedCurve W₀).Point ≃+ W₅.toAffine.Point :=
    Point.mapEquiv (W' := W₀.toAffine) e₅Alg
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    omega)
  have hredOrder : addOrderOf (adicRed hW P) = addOrderOf P :=
    addOrderOf_adicRed hW (by norm_num)
      five_mem_completion_maximalIdeal
      five_not_mem_completion_maximalIdeal_pow_four hP
  apply zmod_five_addOrderOf_ne_of_eleven_le
    W₅ (redPointEquiv (adicRed hW P)) N hN
  exact (AddEquiv.addOrderOf_eq redPointEquiv (adicRed hW P)).trans
    (hredOrder.trans horder)

/-- The unconditional five-adic arithmetic endpoint for the formal-immersion
route: integral `j` excludes multiplicative reduction, the marked weighted
depth argument excludes additive reduction, and checked enumeration over
`F_5` excludes the surviving good-reduction specialization. -/
theorem rationalPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_oneAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (hj : atFive.valuation ℚ E.j ≤ 1)
    (P : E.toAffine.Point)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  classical
  intro horder
  let P' := minimalCompletionPointAtFive E P
  have horder' : addOrderOf P' = N :=
    (minimalCompletionPointAtFive_addOrderOf E P).trans horder
  have hj' : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal
        (atFive.adicCompletionIntegers ℚ))
      (minimalCompletionAtFive E).j ≤ 1 := by
    rw [valuation_minimalCompletionAtFive_j]
    exact hj
  have hgood :=
    goodReductionAtFive E hj' P' N hprime hN horder'
  exact completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive
    hgood P' N hN horder'

/-- The completion-level prime-order endpoint after the integral-`j` and tame
additive-filtration inputs have been supplied.  The reduction trichotomy first upgrades the
minimal equation to good reduction; the preceding completion theorem then specializes the same
marked point to the checked finite field at five.

The filtration argument remains an explicit input: a later Néron-model consumer must instantiate
`F` with the actual component, smooth-residue, and formal-kernel filtration of `W`. -/
theorem
    completionPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
    {W : WeierstrassCurve (atFive.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atFive.adicCompletionIntegers ℚ)]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (atFive.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (F : W.HasAdditiveReduction (atFive.adicCompletionIntegers ℚ) →
      MazurTorsion.EllipticCurve.TameAdditiveFiltrationData W.toAffine.Point)
    (hresidue : ∀ hW, Nat.card (F hW).ResidueAdditive = 5)
    (P : W.toAffine.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hgood : W.HasGoodReduction (atFive.adicCompletionIntegers ℚ) :=
    hasGoodReduction_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
      hj F hresidue P N hprime hN horder
  exact completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive
    hgood P N hN horder

/-- The completion-level prime-order endpoint with the additive component geometry reduced to
the marked point.  In the additive branch the caller proves only `12 • P ∈ E₀`; canonical
nonsingular reduction and the exact formal kernel supply the rest of the local contradiction. -/
theorem
    completionPoint_addOrderOf_ne_of_eleven_le_of_componentExponentTwelveAtFive
    {W : WeierstrassCurve (atFive.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atFive.adicCompletionIntegers ℚ)]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (atFive.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (especial : W.HasAdditiveReduction (atFive.adicCompletionIntegers ℚ) →
      (adicRedCurve (completionIntegralModelAtFive W)).Point ≃+
        IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (P : W.toAffine.Point)
    (hcomponent : ∀ (_hA : W.HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)),
      12 • P ∈ nonsingularReductionSubgroup
        (completionIntegralModelAtFive_map W)
        (nonsingularReduction_isAdditive (completionIntegralModelAtFive_map W)))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hgood : W.HasGoodReduction (atFive.adicCompletionIntegers ℚ) :=
    hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction
      hj P N
        (fun hA ↦
          addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
            (completionIntegralModelAtFive_map W) (especial hA) P (hcomponent hA)
            N hprime hN)
        horder
  exact completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive
    hgood P N hN horder

/-- The rational-point version of the local completion endpoint.  It transports the marked point
to Mathlib's selected minimal five-adic equation, preserving exact order, before invoking the
integral-`j` and tame-additive-filtration contradiction.

The rational `j`-invariant hypothesis is transported by the checked invariance and completion
valuation lemmas above. The remaining filtration input is stated on the concrete minimal equation
and must ultimately come from the genuine Néron model. -/
theorem rationalPoint_addOrderOf_ne_of_eleven_le_of_minimalCompletionInputsAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : atFive.valuation ℚ E.j ≤ 1)
    (F : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) →
        MazurTorsion.EllipticCurve.TameAdditiveFiltrationData
          (minimalCompletionAtFive E).toAffine.Point)
    (hresidue : ∀ hW, Nat.card (F hW).ResidueAdditive = 5)
    (P : E.toAffine.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hj' : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (atFive.adicCompletionIntegers ℚ))
        (minimalCompletionAtFive E).j ≤ 1 := by
    rw [valuation_minimalCompletionAtFive_j]
    exact hj
  apply
    completionPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
      hj' F hresidue (minimalCompletionPointAtFive E P) N hprime hN
  exact (minimalCompletionPointAtFive_addOrderOf E P).trans horder

/-- The rational prime-order local endpoint requiring only the marked-point component exponent on
Mathlib's selected five-adic minimal equation. -/
theorem
    rationalPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_componentExponentTwelveAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : atFive.valuation ℚ E.j ≤ 1)
    (especial : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) →
        (adicRedCurve (completionIntegralModelAtFive
          (minimalCompletionAtFive E))).Point ≃+
          IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (P : E.toAffine.Point)
    (hcomponent : ∀ (_hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)),
      12 • minimalCompletionPointAtFive E P ∈
        nonsingularReductionSubgroup
          (completionIntegralModelAtFive_map (minimalCompletionAtFive E))
          (nonsingularReduction_isAdditive
            (completionIntegralModelAtFive_map (minimalCompletionAtFive E))))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  have hj' : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (atFive.adicCompletionIntegers ℚ))
        (minimalCompletionAtFive E).j ≤ 1 := by
    rw [valuation_minimalCompletionAtFive_j]
    exact hj
  intro horder
  apply
    completionPoint_addOrderOf_ne_of_eleven_le_of_componentExponentTwelveAtFive
      hj' especial (minimalCompletionPointAtFive E P) hcomponent N hprime hN
  exact (minimalCompletionPointAtFive_addOrderOf E P).trans horder

end MazurTorsion.PrimeOrder
