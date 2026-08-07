/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.CuspidalReduction
import MazurTorsion.Kubert.OrderThirtyFiveGoodReductionAtEleven
import MazurTorsion.PrimeOrder.GoodReductionAtFive

/-!
# Cuspidal special-fibre consumers at five and eleven

This file connects the checked finite cuspidal classifications to the marked
component-exponent endpoints.  In an additive branch, Mathlib's selected
integral model has vanishing reduced discriminant and `c₄`; the classification
therefore constructs the nonsingular-point equivalence required by canonical
coordinatewise reduction rather than leaving it as an input.

The remaining geometric premise is exactly the marked-point assertion
`12 • P ∈ E₀`.  No component quotient, component cardinality, or general Hasse
bound is used.
-/

noncomputable section

open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum
open WeierstrassCurve WeierstrassCurve.Affine

namespace MazurTorsion.PrimeOrder

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization

local instance : DecidableEq
    (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- At five, additive reduction itself constructs the cuspidal nonsingular-point
classification needed by the marked component-exponent endpoint. -/
theorem
    completionPoint_primeOrder_ne_of_cuspidalComponentAtFive
    {W : WeierstrassCurve (atFive.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atFive.adicCompletionIntegers ℚ)]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : valuation (atFive.adicCompletion ℚ)
      (maximalIdeal (atFive.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (P : W.toAffine.Point)
    (hcomponent : ∀ (_hA : W.HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)),
      12 • P ∈ nonsingularReductionSubgroup
        (completionIntegralModelAtFive_map W)
        (nonsingularReduction_isAdditive
          (completionIntegralModelAtFive_map W)))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  refine completionPoint_addOrderOf_ne_of_eleven_le_of_componentExponentTwelveAtFive
    hj ?_ P hcomponent N hprime hN
  intro hA
  apply specialFiberPointAddEquivAtFiveOfCuspidal
  · simpa only [adicRedCurve, completionIntegralModelAtFive,
      WeierstrassCurve.reduction] using
      reduction_Δ_eq_zero_of_hasAdditiveReduction hA
  · simpa only [adicRedCurve, completionIntegralModelAtFive,
      WeierstrassCurve.reduction] using
      reduction_c₄_eq_zero_of_hasAdditiveReduction hA

end MazurTorsion.PrimeOrder

namespace MazurTorsion.OrderThirtyFive

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization

local instance : DecidableEq
    (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- The identical checked cuspidal consumer at eleven for the order-35 route. -/
theorem
    completionPoint_orderThirtyFive_ne_of_cuspidalComponentAtEleven
    {W : WeierstrassCurve (atEleven.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atEleven.adicCompletionIntegers ℚ)]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    (hj : valuation (atEleven.adicCompletion ℚ)
      (maximalIdeal (atEleven.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (P : W.toAffine.Point)
    (hcomponent : ∀ (_hA : W.HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      12 • P ∈ nonsingularReductionSubgroup
        (completionIntegralModelAtEleven_map W)
        (nonsingularReduction_isAdditive
          (completionIntegralModelAtEleven_map W))) :
    addOrderOf P ≠ 35 := by
  refine
    completionPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_componentExponentTwelve
      hj ?_ P hcomponent
  intro hA
  apply specialFiberPointAddEquivAtElevenOfCuspidal
  · simpa only [adicRedCurve, completionIntegralModelAtEleven,
      WeierstrassCurve.reduction] using
      reduction_Δ_eq_zero_of_hasAdditiveReduction hA
  · simpa only [adicRedCurve, completionIntegralModelAtEleven,
      WeierstrassCurve.reduction] using
      reduction_c₄_eq_zero_of_hasAdditiveReduction hA

end MazurTorsion.OrderThirtyFive
