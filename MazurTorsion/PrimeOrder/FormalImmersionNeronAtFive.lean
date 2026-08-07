/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.PrimeOrder.CuspidalReductionAtFive
import MazurTorsion.PrimeOrder.FormalImmersionAtFive

/-!
# The canonical Néron-filtration handoff at five

The legacy endpoint in this file accepts the canonical tame-additive handoff:
its component group is the quotient by the chosen identity subgroup, its
identity-component reduction has the exact-pinned formal filtration as kernel,
and that kernel is torsion-free by the unramified formal-group theorem at five.

The stronger endpoints construct the identity subgroup from the actual
predicate of nonsingular coordinate reduction on Mathlib's selected minimal
integral model. Coordinatewise reduction, its exact formal kernel, and its
additivity on the canonical domain are checked. Finite normalization and
enumeration identify the nonsingular points of the singular special cubic with
the additive residue group.  The narrowest endpoint therefore leaves only the
marked component assertion `12 • P ∈ E₀`; no Néron-model geometry is inferred.
-/

noncomputable section

namespace MazurTorsion.PrimeOrder

open CategoryTheory
open WeierstrassCurve WeierstrassCurve.Affine
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open _root_.AlgebraicGeometry

local instance : DecidableEq
    (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- The actual integral equation selected by Mathlib for the minimal five-adic equation used in
the prime route.  Naming this model prevents the nonsingular-reduction consumer from accepting an
unrelated integral equation with the same generic fibre. -/
noncomputable abbrev minimalCompletionIntegralModelAtFive
    (E : WeierstrassCurve ℚ) :
    WeierstrassCurve (atFive.adicCompletionIntegers ℚ) :=
  completionIntegralModelAtFive (minimalCompletionAtFive E)

/-- The named integral equation has the selected minimal completion as its generic fibre. -/
theorem minimalCompletionIntegralModelAtFive_map
    (E : WeierstrassCurve ℚ) :
    (minimalCompletionIntegralModelAtFive E).map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) =
      (minimalCompletionAtFive E).toAffine :=
  completionIntegralModelAtFive_map (minimalCompletionAtFive E)

/-- In the additive branch, the actual special cubic used by canonical nonsingular reduction has
vanishing discriminant and `c₄`.  This specializes the two checked valuation-to-residue lemmas to
the precise minimal equation of the prime route and is the starting point for its cuspidal
additive-group classification. -/
theorem minimalCompletionAtFive_reduction_invariants_of_hasAdditiveReduction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)) :
    ((minimalCompletionAtFive E).reduction
        (atFive.adicCompletionIntegers ℚ)).Δ = 0 ∧
      ((minimalCompletionAtFive E).reduction
        (atFive.adicCompletionIntegers ℚ)).c₄ = 0 :=
  ⟨reduction_Δ_eq_zero_of_hasAdditiveReduction hA,
    reduction_c₄_eq_zero_of_hasAdditiveReduction hA⟩

/-- The rational prime-order contradiction from the formal-immersion collision and canonical
tame-additive reduction data on Mathlib's selected minimal equation.

Compared with `rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive`, this theorem
does not accept an arbitrary component homomorphism or an unrelated formal-kernel torsion
certificate.  Its component is definitionally the quotient by `identitySubgroup`, and the formal
torsion theorem is discharged at five by `toTameAdditiveFiltrationDataAtFive`. -/
theorem
    rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive_of_tameReductionAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    {X Y : Scheme}
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hformal : IsFormalImmersionAt f
      (cuspSection (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))))
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)) =
        cuspSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ))
    (hW₀ : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) =
      (minimalCompletionAtFive E).toAffine)
    (F : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) →
        TameAdditiveReductionDataAtFive hW₀)
    (P : E.toAffine.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive
    f modularSection cuspSection hformal hne hspecializes hquotient
    (fun hW ↦ (F hW).toTameAdditiveFiltrationData)
    (fun _ ↦ TameAdditiveReductionDataAtFive.residue_natCard)
    P N hprime hN

/-- The prime-order formal-immersion endpoint with the identity subgroup and reduction map fixed
to canonical coordinatewise nonsingular reduction.

Unlike the preceding handoff, this theorem does not accept an identity subgroup, a reduction
homomorphism, or a group-law premise for reduction.  The additivity theorem and exact formal
kernel are checked by `nonsingularReduction_isAdditive` and
`nonsingularReduction_eq_zero_iff`; the caller identifies the nonsingular points of the actual
special cubic with the additive residue field and supplies the genuine component bound. -/
theorem
    rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive_of_nonsingularReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    {X Y : Scheme}
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hformal : IsFormalImmersionAt f
      (cuspSection (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))))
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)) =
        cuspSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (especial : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtFive E)).Point ≃+
          IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (hcomponent : ∀ (_hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)),
      Nat.card ((minimalCompletionAtFive E).toAffine.Point ⧸
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtFive_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtFive_map E))) ≤ 4)
    (P : E.toAffine.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply
    rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive_of_tameReductionAtFive
      f modularSection cuspSection hformal hne hspecializes hquotient
      (minimalCompletionIntegralModelAtFive E)
      (minimalCompletionIntegralModelAtFive_map E)
      (fun hA ↦ TameAdditiveReductionDataAtFive.ofCanonicalNonsingularReduction
        (especial hA) (hcomponent hA)) P N hprime hN

/-- The prime-order formal-immersion endpoint after the special cuspidal cubic has been classified.

The formal-immersion collision supplies the five-adic valuation bound, and finite normalization of
the additive special cubic supplies its residue-group equivalence.  Thus the sole additive-fibre
premise is the honest marked-point statement `12 • P ∈ E₀` on the selected minimal equation. -/
theorem
    rationalPoint_primeOrder_ne_of_formalImmersionAtFive_of_componentExponentTwelve
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    {X Y : Scheme}
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hformal : IsFormalImmersionAt f
      (cuspSection (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))))
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)) =
        cuspSection (IsLocalRing.closedPoint
          (atFive.adicCompletionIntegers ℚ)))
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (P : E.toAffine.Point)
    (hcomponentExponent : ∀ (_hA : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ)),
      12 • minimalCompletionPointAtFive E P ∈
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtFive_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtFive_map E)))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N :=
  rationalPoint_primeOrder_ne_of_cuspidalReduction_of_componentExponentTwelveAtFive
    (valuation_j_le_one_of_formalImmersionAtFive f modularSection cuspSection
      hformal hne hspecializes hquotient)
    P hcomponentExponent N hprime hN

end MazurTorsion.PrimeOrder
