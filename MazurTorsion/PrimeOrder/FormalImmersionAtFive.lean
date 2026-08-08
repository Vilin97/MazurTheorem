/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionCollision
import MazurTorsion.PrimeOrder.GoodReductionAtFive

/-!
# The formal-immersion boundary at five

Mazur's prime-order argument obtains integrality of the rational `j`-invariant from a collision
on an integral model of `X₀(N)`.  The source point and the cusp meet in the special fibre when
`j` is not integral, while their images in the finite Eisenstein quotient agree.  Formal
immersion at the cusp then forces the two integral sections to agree, contradicting their
distinct generic fibres.

This file isolates that exact logical boundary.  It does not claim a represented modular curve,
an Atkin--Lehner involution, or a Néron model.  Those geometric inputs remain explicit as:

* specialization of the modular section to the cusp when the five-adic valuation bound fails;
* equality of the two quotient sections under the same hypothesis; and
* distinctness of the two integral sections.

The final theorem is a real downstream consumer: it feeds the valuation obtained from the
formal-immersion collision into the already checked minimal-completion and `F₅` contradiction.
-/

namespace MazurTorsion.PrimeOrder

open CategoryTheory
open MazurTorsion.IntegerPrimeSpecialization
open _root_.AlgebraicGeometry

/-- A cusp formal immersion forces the five-adic `j`-valuation bound once the modular point's
specialization and finite-quotient collision have been constructed.

The source is the actual completed integer ring at five.  Thus the Noetherian local-ring
hypothesis needed to descend equality from completed stalks is inferred from its discrete
valuation ring structure, rather than supplied as an unrelated assumption.

The two implications are deliberately separate.  `hspecializes` is the missing integral
`X₀(N)`/Atkin--Lehner geometry, whereas `hquotient` is the missing rank-zero Néron-specialization
consumer.  No representability or modular interpretation is hidden in this theorem. -/
theorem valuation_j_le_one_of_formalImmersionAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
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
      modularSection ≫ f = cuspSection ≫ f) :
    atFive.valuation ℚ E.j ≤ 1 := by
  by_contra hj
  apply hne
  have hpoint := hspecializes hj
  have hformalAtModular : IsFormalImmersionAt f
      (modularSection (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))) := by
    simpa only [hpoint] using hformal
  exact hformalAtModular.spec_ext_of_comp_eq_of_isNoetherian
    modularSection cuspSection hpoint (hquotient hj)

/-- The prime-order contradiction with the five-adic `j` input discharged by the cusp
formal-immersion collision.

This theorem is the checked downstream use of
`valuation_j_le_one_of_formalImmersionAtFive`: after the modular and Néron lanes construct the
three explicit collision inputs, the resulting valuation bound is transported to Mathlib's
selected minimal completion and then to the exhaustive `F₅` point-order bound.  The genuine tame
additive Néron filtration remains explicit and is not inferred from the scheme collision. -/
theorem rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive
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
    (F : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) →
        MazurTorsion.EllipticCurve.TameAdditiveFiltrationData
          (minimalCompletionAtFive E).toAffine.Point)
    (hresidue : ∀ hW, Nat.card (F hW).ResidueAdditive = 5)
    (P : E.toAffine.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  apply rationalPoint_addOrderOf_ne_of_eleven_le_of_minimalCompletionInputsAtFive
    (valuation_j_le_one_of_formalImmersionAtFive f modularSection cuspSection
      hformal hne hspecializes hquotient)
    F hresidue P N hprime hN

/-- The theorem-critical prime-order endpoint of the five-adic
formal-immersion collision.

Unlike the legacy filtration handoff above, this theorem has no additive
reduction premise.  The marked weighted-depth argument on Mathlib's selected
minimal equation rules out that branch, and the checked enumeration over
`F₅` rules out the remaining good-reduction specialization. -/
theorem rationalPoint_primeOrder_ne_of_formalImmersionAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
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
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N :=
  rationalPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_oneAtFive
    (valuation_j_le_one_of_formalImmersionAtFive f modularSection cuspSection
      hformal hne hspecializes hquotient)
    P N hprime hN

end MazurTorsion.PrimeOrder
