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
    (hadd : W.HasAdditiveReduction (atEleven.adicCompletionIntegers ℚ) →
      NonsingularReductionIsAdditive
        (completionIntegralModelAtEleven_map W))
    (especial : W.HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (completionIntegralModelAtEleven W)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : ∀ hA,
      Nat.card (W.toAffine.Point ⧸
        nonsingularReductionSubgroup
          (completionIntegralModelAtEleven_map W) (hadd hA)) ≤ 4)
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_tameReductionAtEleven
    hj
      (fun hA ↦ TameAdditiveReductionDataAtEleven.ofNonsingularReduction
        (hadd hA) (especial hA) (hcomponent hA))
      P

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
    (hadd : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        NonsingularReductionIsAdditive
          (minimalCompletionIntegralModelAtEleven_map E))
    (especial : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtEleven E)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : ∀ hA,
      Nat.card ((minimalCompletionAtEleven E).toAffine.Point ⧸
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E) (hadd hA)) ≤ 4)
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
      hj' hadd especial hcomponent (minimalCompletionPointAtEleven E P)
  exact (minimalCompletionPointAtEleven_addOrderOf E P).trans horder

end MazurTorsion.OrderThirtyFive
