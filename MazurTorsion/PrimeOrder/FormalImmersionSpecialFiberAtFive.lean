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
collision. The narrowest degree-one consumer also discharges the cuspidal
special-fibre classification and leaves only `12 • P ∈ E₀` from component
geometry.
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

/-- In the standard modular special-fibre situation, the quotient ideal on
the source cusp stalk is the extension of one target-stalk ideal. Local
Noetherianity supplies every finiteness condition, so the characteristic-five
calculation only has to prove the mapped quotient cotangent map surjective. -/
theorem valuation_j_le_one_of_mappedIdealCotangentAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtFive cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hcotangent : IsLocalRing.IsMappedIdealCotangentSurjective
      (f.stalkMap (closedFiberPointAtFive cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtFive modularSection =
        closedFiberPointAtFive cuspSection)
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f) :
    atFive.valuation ℚ E.j ≤ 1 := by
  have hformal : IsFormalImmersionAt f (closedFiberPointAtFive cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_mappedIdealCotangentSurjective_of_isLocallyNoetherian
      f (closedFiberPointAtFive cuspSection) hresidue I hI hcotangent
  exact valuation_j_le_one_of_formalImmersionAtFive
    f modularSection cuspSection hformal hne hspecializes hquotient

/-- The characteristic-five calculation may be supplied in its natural
degree-one form: the actual quotient residue map, the one-dimensional source
cotangent space, and one target vector detected nontrivially by its first
`q`-coefficient. -/
theorem valuation_j_le_one_of_mappedIdealDegreeOneCotangentAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtFive cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hdegreeOne : IsLocalRing.IsMappedIdealDegreeOneCotangent
      (f.stalkMap (closedFiberPointAtFive cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtFive modularSection =
        closedFiberPointAtFive cuspSection)
    (hquotient : ¬ atFive.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f) :
    atFive.valuation ℚ E.j ≤ 1 := by
  have hformal : IsFormalImmersionAt f (closedFiberPointAtFive cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_mappedIdealDegreeOneCotangent_of_isLocallyNoetherian
      f (closedFiberPointAtFive cuspSection) hresidue I hI hdegreeOne
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
  have hformal : IsFormalImmersionAt f (closedFiberPointAtFive cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_quotientCotangentCertificate_of_isLocallyNoetherian
      f (closedFiberPointAtFive cuspSection) hresidue data
  exact
    rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive_of_nonsingularReduction
      f modularSection cuspSection hformal hne hspecializes hquotient
      especial hcomponent P N hprime hN

/-- The mapped characteristic-five cotangent calculation is sufficient for
the final canonical nonsingular-reduction prime-order consumer. -/
theorem
    rationalPoint_addOrderOf_ne_of_mappedCotangentAtFive_of_nonsingularReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtFive cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hcotangent : IsLocalRing.IsMappedIdealCotangentSurjective
      (f.stalkMap (closedFiberPointAtFive cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtFive modularSection =
        closedFiberPointAtFive cuspSection)
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
    addOrderOf P ≠ N :=
  rationalPoint_addOrderOf_ne_of_eleven_le_of_formalImmersionAtFive_of_nonsingularReduction
    f modularSection cuspSection
      (Scheme.Hom.isFormalImmersionAt_of_mappedIdealCotangentSurjective_of_isLocallyNoetherian
        f (closedFiberPointAtFive cuspSection) hresidue I hI hcotangent)
      hne hspecializes hquotient especial hcomponent P N hprime hN

/-- The actual degree-one characteristic-five calculation reaches the
rational prime-order contradiction.  Additivity of canonical nonsingular
reduction is now checked internally, so the remaining local premises are the
special-cubic additive classification and genuine component bound. -/
theorem
    rationalPoint_addOrderOf_ne_of_mappedDegreeOneCotangentAtFive_of_nonsingularReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtFive cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hdegreeOne : IsLocalRing.IsMappedIdealDegreeOneCotangent
      (f.stalkMap (closedFiberPointAtFive cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtFive modularSection =
        closedFiberPointAtFive cuspSection)
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
    addOrderOf P ≠ N :=
  rationalPoint_addOrderOf_ne_of_mappedCotangentAtFive_of_nonsingularReduction
    f modularSection cuspSection hresidue I hI
      (hdegreeOne.isMappedIdealCotangentSurjective
        (f.stalkMap (closedFiberPointAtFive cuspSection)).hom I hI)
      hne hspecializes hquotient especial hcomponent P N hprime hN

/-- The degree-one characteristic-five formal-immersion endpoint with the cuspidal special fibre
classified and the full component-cardinality premise removed.

The sole additive-fibre input is the marked assertion `12 • P ∈ E₀` on Mathlib's selected
minimal five-adic equation. -/
theorem
    rationalPoint_primeOrder_ne_of_mappedDegreeOneCotangentAtFive_of_componentExponentTwelve
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atFive.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtFive cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtFive cuspSection))))
    (hdegreeOne : IsLocalRing.IsMappedIdealDegreeOneCotangent
      (f.stalkMap (closedFiberPointAtFive cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtFive modularSection =
        closedFiberPointAtFive cuspSection)
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
    (valuation_j_le_one_of_mappedIdealDegreeOneCotangentAtFive
      f modularSection cuspSection hresidue I hI hdegreeOne hne
      hspecializes hquotient)
    P hcomponentExponent N hprime hN

end MazurTorsion.PrimeOrder
