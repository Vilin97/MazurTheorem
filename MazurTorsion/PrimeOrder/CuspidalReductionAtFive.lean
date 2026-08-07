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

end MazurTorsion.PrimeOrder
