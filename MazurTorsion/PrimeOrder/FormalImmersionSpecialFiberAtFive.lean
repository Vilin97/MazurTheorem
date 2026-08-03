/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionSpecialFiber
import MazurTorsion.PrimeOrder.FormalImmersionNeronAtFive

/-!
# The special-fibre formal-immersion consumer at five

This file joins the characteristic-five cotangent calculation to the actual
prime-order contradiction.  The modular input is stated on the two stalks at
the cusp: quotient by the extended special-fibre ideal, prove the resulting
cotangent map surjective, and identify the residue fields.  The checked
quotient-Nakayama lift then supplies formal immersion on the total completed
stalks.

The downstream theorem immediately feeds that formal immersion into the
canonical nonsingular-reduction endpoint.  Thus the interface cannot be
satisfied merely by a calculation on an unrelated pair of quotient rings:
its stalk map is definitionally the map at the same cusp used in the Mazur
collision.
-/

noncomputable section

namespace MazurTorsion.PrimeOrder

open CategoryTheory
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open WeierstrassCurve WeierstrassCurve.Affine
open _root_.AlgebraicGeometry

local instance : DecidableEq
    (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- The closed-fibre point selected by a five-adic integral section. -/
abbrev closedFiberPointAtFive {X : Scheme}
    (s : Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X) : X :=
  s (IsLocalRing.closedPoint (atFive.adicCompletionIntegers ℚ))

/-- A special-fibre cotangent certificate on the actual cusp stalk supplies
the formal immersion used by the prime-order collision.  Local Noetherianity
is the geometric finiteness condition on the integral modular curve and its
quotient; the certificate itself records the compatible fibre ideals and the
computed quotient cotangent surjection. -/
theorem valuation_j_le_one_of_quotientCotangentCertificateAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtFive cuspSection)))
    (data : IsLocalRing.QuotientCotangentCertificate
      (f.stalkMap (closedFiberPointAtFive cuspSection)).hom)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtFive modularSection =
        closedFiberPointAtFive cuspSection)
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f) :
    atFive.valuation ℚ E.j ≤ 1 := by
  have hformal : IsFormalImmersionAt f (closedFiberPointAtFive cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_quotientCotangentCertificate_of_isLocallyNoetherian
      f (closedFiberPointAtFive cuspSection) hresidue data
  exact valuation_j_le_one_of_formalImmersionAtFive
    f modularSection cuspSection hformal hne hspecializes hquotient

/-- The characteristic-five quotient-cotangent certificate reaches the
prime-order exclusion with the canonical nonsingular-reduction domain on
Mathlib's selected minimal equation.

This is the theorem-level consumer of both new interfaces.  Its remaining
inputs are genuine geometry: cusp specialization and quotient equality for
the modular map, additive-group classification of the nonsingular special
cubic, and the component-group bound. -/
theorem
    rationalPoint_addOrderOf_ne_of_quotientCotangentAtFive_of_nonsingularReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtFive cuspSection)))
    (data : IsLocalRing.QuotientCotangentCertificate
      (f.stalkMap (closedFiberPointAtFive cuspSection)).hom)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtFive modularSection =
        closedFiberPointAtFive cuspSection)
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (hadd : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) →
        NonsingularReductionIsAdditive
          (minimalCompletionIntegralModelAtFive_map E))
    (especial : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtFive E)).Point ≃+
          IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (hcomponent : ∀ hA,
      Nat.card ((minimalCompletionAtFive E).toAffine.Point ⧸
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtFive_map E) (hadd hA)) ≤ 4)
    (P : E.toAffine.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  have hformal : IsFormalImmersionAt f (closedFiberPointAtFive cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_quotientCotangentCertificate_of_isLocallyNoetherian
      f (closedFiberPointAtFive cuspSection) hresidue data
  exact
    rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive_of_nonsingularReduction
      f modularSection cuspSection hformal hne hspecializes hquotient
      hadd especial hcomponent P N hprime hN

end MazurTorsion.PrimeOrder
