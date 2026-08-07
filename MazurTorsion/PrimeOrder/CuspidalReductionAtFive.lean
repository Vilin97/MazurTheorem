/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.CuspidalReduction
import MazurTorsion.PrimeOrder.GoodReductionAtFive

/-!
# Cuspidal special-fibre consumers at five

Finite normalization classifies the nonsingular points of the additive special
cubic, so these consumers no longer accept an arbitrary residue-group
equivalence.  Their remaining geometric premise is exactly the marked-point
assertion `12 • P ∈ E₀`; no component quotient or cardinality bound is used.
-/

noncomputable section

open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve WeierstrassCurve.Affine

namespace MazurTorsion.PrimeOrder

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization

local instance cuspidalConsumerDecidableEqResidueAtFive : DecidableEq
    (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- At five, additive reduction constructs the cuspidal nonsingular-point classification needed
by the marked component-exponent endpoint. -/
theorem
    completionPoint_primeOrder_ne_of_cuspidalReduction_of_componentExponentTwelveAtFive
    {W : WeierstrassCurve (atFive.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atFive.adicCompletionIntegers ℚ)]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : valuation (atFive.adicCompletion ℚ)
      (maximalIdeal (atFive.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (P : W.toAffine.Point)
    (hcomponentExponent : ∀ (_hA : W.HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)),
      12 • P ∈ nonsingularReductionSubgroup
        (completionIntegralModelAtFive_map W)
        (nonsingularReduction_isAdditive
          (completionIntegralModelAtFive_map W)))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  refine completionPoint_addOrderOf_ne_of_eleven_le_of_componentExponentTwelveAtFive
    hj ?_ P hcomponentExponent N hprime hN
  intro hA
  apply specialFiberPointAddEquivAtFiveOfCuspidal
  · simpa only [adicRedCurve, completionIntegralModelAtFive,
      WeierstrassCurve.reduction] using
      reduction_Δ_eq_zero_of_hasAdditiveReduction hA
  · simpa only [adicRedCurve, completionIntegralModelAtFive,
      WeierstrassCurve.reduction] using
      reduction_c₄_eq_zero_of_hasAdditiveReduction hA

/-- The rational prime-order endpoint with the special-cubic classification discharged.
The only additive-fibre input left is the marked component-exponent statement on Mathlib's
selected minimal five-adic equation. -/
theorem
    rationalPoint_primeOrder_ne_of_cuspidalReduction_of_componentExponentTwelveAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : atFive.valuation ℚ E.j ≤ 1)
    (P : E.toAffine.Point)
    (hcomponentExponent : ∀ (_hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)),
      12 • minimalCompletionPointAtFive E P ∈
        nonsingularReductionSubgroup
          (completionIntegralModelAtFive_map (minimalCompletionAtFive E))
          (nonsingularReduction_isAdditive
            (completionIntegralModelAtFive_map (minimalCompletionAtFive E))))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  refine
    rationalPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_componentExponentTwelveAtFive
      hj ?_ P hcomponentExponent N hprime hN
  intro hA
  apply specialFiberPointAddEquivAtFiveOfCuspidal
  · simpa only [adicRedCurve, completionIntegralModelAtFive,
      WeierstrassCurve.reduction] using
      reduction_Δ_eq_zero_of_hasAdditiveReduction hA
  · simpa only [adicRedCurve, completionIntegralModelAtFive,
      WeierstrassCurve.reduction] using
      reduction_c₄_eq_zero_of_hasAdditiveReduction hA

/-- A finite marked component class of order at most four on Mathlib's selected minimal
five-adic equation yields the exact `12 • P ∈ E₀` handoff.  This is the pointwise Kodaira
intermediate needed by the torsion argument; it neither assumes nor constructs a cardinality
bound for the entire component quotient. -/
theorem minimalCompletionPointAtFive_twelve_nsmul_mem_of_markedComponentOrderAtMostFour
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : E.toAffine.Point)
    (hcomponentOrder : MarkedComponentOrderAtMost
      (nonsingularReductionSubgroup
        (completionIntegralModelAtFive_map (minimalCompletionAtFive E))
        (nonsingularReduction_isAdditive
          (completionIntegralModelAtFive_map (minimalCompletionAtFive E))))
      4 (minimalCompletionPointAtFive E P)) :
    12 • minimalCompletionPointAtFive E P ∈
      nonsingularReductionSubgroup
        (completionIntegralModelAtFive_map (minimalCompletionAtFive E))
        (nonsingularReduction_isAdditive
          (completionIntegralModelAtFive_map (minimalCompletionAtFive E))) :=
  twelve_nsmul_mem_of_markedComponentOrderAtMostFour _ _ hcomponentOrder

/-- The checked prime-order consumer phrased at the precise remaining Kodaira statement: in the
additive branch, the marked class in the quotient by canonical nonsingular reduction has finite
order at most four.  The preceding theorem converts that certificate into the uniform exponent
used by the cuspidal reduction endpoint. -/
theorem
    rationalPoint_primeOrder_ne_of_cuspidalReduction_of_markedComponentOrderAtMostFourAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : atFive.valuation ℚ E.j ≤ 1)
    (P : E.toAffine.Point)
    (hcomponentOrder : ∀ (_hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)),
      MarkedComponentOrderAtMost
        (nonsingularReductionSubgroup
          (completionIntegralModelAtFive_map (minimalCompletionAtFive E))
          (nonsingularReduction_isAdditive
            (completionIntegralModelAtFive_map (minimalCompletionAtFive E))))
        4 (minimalCompletionPointAtFive E P))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N :=
  rationalPoint_primeOrder_ne_of_cuspidalReduction_of_componentExponentTwelveAtFive
    hj P
      (fun hA ↦
        minimalCompletionPointAtFive_twelve_nsmul_mem_of_markedComponentOrderAtMostFour
          E P (hcomponentOrder hA))
    N hprime hN

end MazurTorsion.PrimeOrder
