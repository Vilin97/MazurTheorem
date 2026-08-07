/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.CuspidalReduction
import MazurTorsion.Kubert.OrderThirtyFiveGoodReductionAtEleven

/-!
# The cuspidal special-fibre consumer for order 35 at eleven

Finite normalization classifies the nonsingular points of the additive special
cubic, so these consumers no longer accept an arbitrary residue-group
equivalence.  Their remaining geometric premise is exactly the marked-point
assertion `12 • P ∈ E₀`; no component quotient or cardinality bound is used.
-/

noncomputable section

open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization

local instance cuspidalConsumerDecidableEqResidueAtEleven : DecidableEq
    (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- Additive reduction at eleven constructs the cuspidal nonsingular-point classification needed
by the order-35 marked component-exponent endpoint. -/
theorem
    completionPoint_orderThirtyFive_ne_of_cuspidalReduction_of_componentExponentTwelveAtEleven
    {W : WeierstrassCurve (atEleven.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atEleven.adicCompletionIntegers ℚ)]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : valuation (atEleven.adicCompletion ℚ)
      (maximalIdeal (atEleven.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (P : W.toAffine.Point)
    (hcomponentExponent : ∀ (_hA : W.HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      12 • P ∈ nonsingularReductionSubgroup
        (completionIntegralModelAtEleven_map W)
        (nonsingularReduction_isAdditive
          (completionIntegralModelAtEleven_map W))) :
    addOrderOf P ≠ 35 := by
  refine
    completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_componentExponentTwelve
      hj ?_ P hcomponentExponent
  intro hA
  apply specialFiberPointAddEquivAtElevenOfCuspidal
  · simpa only [adicRedCurve, completionIntegralModelAtEleven,
      WeierstrassCurve.reduction] using
      reduction_Δ_eq_zero_of_hasAdditiveReduction hA
  · simpa only [adicRedCurve, completionIntegralModelAtEleven,
      WeierstrassCurve.reduction] using
      reduction_c₄_eq_zero_of_hasAdditiveReduction hA

/-- The rational order-35 endpoint with the eleven-adic special-cubic classification discharged.
Only the marked assertion `12 • P ∈ E₀` on the selected minimal equation remains. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_cuspidalReduction_of_componentExponentTwelveAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : atEleven.valuation ℚ E.j ≤ 1)
    (P : E.toAffine.Point)
    (hcomponentExponent : ∀ (_hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      12 • minimalCompletionPointAtEleven E P ∈
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E))) :
    addOrderOf P ≠ 35 := by
  refine
    rationalPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_componentExponentTwelveAtEleven
      hj ?_ P hcomponentExponent
  intro hA
  apply specialFiberPointAddEquivAtElevenOfCuspidal
  · simpa only [adicRedCurve, minimalCompletionIntegralModelAtEleven,
      completionIntegralModelAtEleven, WeierstrassCurve.reduction] using
      reduction_Δ_eq_zero_of_hasAdditiveReduction hA
  · simpa only [adicRedCurve, minimalCompletionIntegralModelAtEleven,
      completionIntegralModelAtEleven, WeierstrassCurve.reduction] using
      reduction_c₄_eq_zero_of_hasAdditiveReduction hA

/-- A finite marked component class of order at most four on Mathlib's selected minimal
eleven-adic equation yields the exact `12 • P ∈ E₀` handoff.  This is the same pointwise
Kodaira intermediate used at five and does not require a bound for the full component quotient. -/
theorem minimalCompletionPointAtEleven_twelve_nsmul_mem_of_markedComponentOrderAtMostFour
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (P : E.toAffine.Point)
    (hcomponentOrder : MarkedComponentOrderAtMost
      (nonsingularReductionSubgroup
        (minimalCompletionIntegralModelAtEleven_map E)
        (nonsingularReduction_isAdditive
          (minimalCompletionIntegralModelAtEleven_map E)))
      4 (minimalCompletionPointAtEleven E P)) :
    12 • minimalCompletionPointAtEleven E P ∈
      nonsingularReductionSubgroup
        (minimalCompletionIntegralModelAtEleven_map E)
        (nonsingularReduction_isAdditive
          (minimalCompletionIntegralModelAtEleven_map E)) :=
  twelve_nsmul_mem_of_markedComponentOrderAtMostFour _ _ hcomponentOrder

/-- The order-35 consumer phrased at the precise remaining Kodaira statement: in the additive
branch, the marked class in the quotient by canonical nonsingular reduction has finite order at
most four. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_cuspidalReduction_of_markedComponentOrderAtMostFourAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : atEleven.valuation ℚ E.j ≤ 1)
    (P : E.toAffine.Point)
    (hcomponentOrder : ∀ (_hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      MarkedComponentOrderAtMost
        (nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E)))
        4 (minimalCompletionPointAtEleven E P)) :
    addOrderOf P ≠ 35 :=
  rationalPoint_orderThirtyFive_ne_of_cuspidalReduction_of_componentExponentTwelveAtEleven
    hj P
      (fun hA ↦
        minimalCompletionPointAtEleven_twelve_nsmul_mem_of_markedComponentOrderAtMostFour
          E P (hcomponentOrder hA))

end MazurTorsion.OrderThirtyFive
