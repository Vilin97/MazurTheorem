/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TameAdditiveReductionData
import MazurTorsion.PrimeOrder.FormalImmersionAtFive

/-!
# The canonical Néron-filtration handoff at five

This file replaces the arbitrary tame-additive filtration argument in the prime-route endpoint by
the canonical quotient data expected from a Néron model.  The component group is the actual
quotient by the supplied identity subgroup, identity-component reduction has the exact-pinned
formal filtration as its kernel, and torsion-freeness of that kernel is proved by the unramified
formal-group theorem at five.

The remaining inputs are genuinely geometric: construction of the identity subgroup and its
reduction map into the residue field, the kernel equality, and the order-at-most-four component
theorem.  Component finiteness follows from the checked finite-index theorem for the formal
subgroup, and the five-element cardinality of the fixed target is proved here.  No Néron-model
geometry is inferred.
-/

noncomputable section

namespace MazurTorsion.PrimeOrder

open CategoryTheory
open WeierstrassCurve WeierstrassCurve.Affine
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open _root_.AlgebraicGeometry

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

end MazurTorsion.PrimeOrder
