/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionSpecialFiber
import MazurTorsion.AlgebraicGeometry.FormalImmersionCollision
import MazurTorsion.Kubert.OrderThirtyFiveCuspidalReductionAtEleven

/-!
# The order-35 formal-immersion collision at eleven

This file is the local theorem-level consumer for the squarefree level-35
route.  A quotient-cotangent calculation on the actual characteristic-eleven
cusp stalk lifts to a formal immersion of total completed stalks.  If the
modular section specializes to that cusp and its image in the finite
rank-zero quotient equals the cusp image, the collision forces the original
rational `j`-invariant to be eleven-adically integral.

The final theorem sends this valuation bound through the selected minimal
eleven-adic equation, canonical nonsingular reduction, good-reduction
specialization, and the checked `F_11` enumeration.  Finite normalization also
classifies the cuspidal special cubic.  The narrowest endpoint leaves the
modular/cusp geometry, quotient specialization, and the marked component
assertion `12 • P ∈ E₀` explicit.
-/

noncomputable section

namespace MazurTorsion.OrderThirtyFive

open CategoryTheory
open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open WeierstrassCurve WeierstrassCurve.Affine
open _root_.AlgebraicGeometry

local instance : DecidableEq
    (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- The closed-fibre point selected by an eleven-adic integral section. -/
abbrev closedFiberPointAtEleven {X : Scheme}
    (s : Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X) : X :=
  s (IsLocalRing.closedPoint (atEleven.adicCompletionIntegers ℚ))

/-- The actual cusp-stalk quotient-cotangent certificate supplies the
eleven-adic `j`-valuation bound through the formal-immersion collision. -/
theorem valuation_j_le_one_of_quotientCotangentCertificateAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (data : IsLocalRing.QuotientCotangentCertificate
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f) :
    atEleven.valuation ℚ E.j ≤ 1 := by
  by_contra hj
  apply hne
  have hpoint := hspecializes hj
  have hformal : IsFormalImmersionAt f
      (closedFiberPointAtEleven cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_quotientCotangentCertificate_of_isLocallyNoetherian
      f (closedFiberPointAtEleven cuspSection) hresidue data
  have hformalAtModular : IsFormalImmersionAt f
      (closedFiberPointAtEleven modularSection) := by
    simpa only [hpoint] using hformal
  exact hformalAtModular.spec_ext_of_comp_eq_of_isNoetherian
    modularSection cuspSection hpoint (hquotient hj)

/-- The standard mapped special-fibre ideal is enough for the eleven-adic
collision; local Noetherianity supplies all three finiteness statements used
by quotient Nakayama and completion surjectivity. -/
theorem valuation_j_le_one_of_mappedIdealCotangentAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hcotangent : IsLocalRing.IsMappedIdealCotangentSurjective
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f) :
    atEleven.valuation ℚ E.j ≤ 1 := by
  by_contra hj
  apply hne
  have hpoint := hspecializes hj
  have hformal : IsFormalImmersionAt f
      (closedFiberPointAtEleven cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_mappedIdealCotangentSurjective_of_isLocallyNoetherian
      f (closedFiberPointAtEleven cuspSection) hresidue I hI hcotangent
  have hformalAtModular : IsFormalImmersionAt f
      (closedFiberPointAtEleven modularSection) := by
    simpa only [hpoint] using hformal
  exact hformalAtModular.spec_ext_of_comp_eq_of_isNoetherian
    modularSection cuspSection hpoint (hquotient hj)

/-- The squarefree level-35 calculation may be supplied directly as the
degree-one quotient-fibre data detected by the characteristic-eleven
`q`-expansion. -/
theorem valuation_j_le_one_of_mappedIdealDegreeOneCotangentAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hdegreeOne : IsLocalRing.IsMappedIdealDegreeOneCotangent
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f) :
    atEleven.valuation ℚ E.j ≤ 1 := by
  by_contra hj
  apply hne
  have hpoint := hspecializes hj
  have hformal : IsFormalImmersionAt f
      (closedFiberPointAtEleven cuspSection) :=
    Scheme.Hom.isFormalImmersionAt_of_mappedIdealDegreeOneCotangent_of_isLocallyNoetherian
      f (closedFiberPointAtEleven cuspSection) hresidue I hI hdegreeOne
  have hformalAtModular : IsFormalImmersionAt f
      (closedFiberPointAtEleven modularSection) := by
    simpa only [hpoint] using hformal
  exact hformalAtModular.spec_ext_of_comp_eq_of_isNoetherian
    modularSection cuspSection hpoint (hquotient hj)

/-- The level-35 special-fibre cotangent calculation reaches the rational
order-35 exclusion through the canonical nonsingular-reduction endpoint at
eleven. -/
theorem
    rationalPoint_addOrderOf_ne_thirtyFive_of_quotientCotangentAtEleven_of_nonsingularReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (data : IsLocalRing.QuotientCotangentCertificate
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (especial : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtEleven E)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : ∀ (_hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      Nat.card ((minimalCompletionAtEleven E).toAffine.Point ⧸
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E))) ≤ 4)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  rationalPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_nonsingularReductionAtEleven
    (valuation_j_le_one_of_quotientCotangentCertificateAtEleven
      f modularSection cuspSection hresidue data hne hspecializes hquotient)
    especial hcomponent P

/-- The actual mapped characteristic-eleven cotangent calculation reaches the
canonical local order-35 contradiction without separately packaging a
quotient certificate. -/
theorem
    rationalPoint_addOrderOf_ne_thirtyFive_of_mappedCotangentAtEleven_of_nonsingularReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hcotangent : IsLocalRing.IsMappedIdealCotangentSurjective
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (especial : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtEleven E)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : ∀ (_hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      Nat.card ((minimalCompletionAtEleven E).toAffine.Point ⧸
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E))) ≤ 4)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  rationalPoint_addOrderOf_ne_thirtyFive_of_valuation_j_le_one_of_nonsingularReductionAtEleven
    (valuation_j_le_one_of_mappedIdealCotangentAtEleven
      f modularSection cuspSection hresidue I hI hcotangent hne
      hspecializes hquotient)
    especial hcomponent P

/-- The actual degree-one characteristic-eleven quotient-fibre calculation
reaches the rational order-35 contradiction with canonical reduction
additivity already discharged. -/
theorem
    rationalPoint_addOrderOf_ne_thirtyFive_of_degreeOneCotangentAtEleven_of_nonsingularReduction
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hdegreeOne : IsLocalRing.IsMappedIdealDegreeOneCotangent
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (especial : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ) →
        (adicRedCurve (minimalCompletionIntegralModelAtEleven E)).Point ≃+
          IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : ∀ (_hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      Nat.card ((minimalCompletionAtEleven E).toAffine.Point ⧸
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E))) ≤ 4)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  rationalPoint_addOrderOf_ne_thirtyFive_of_mappedCotangentAtEleven_of_nonsingularReduction
    f modularSection cuspSection hresidue I hI
      (hdegreeOne.isMappedIdealCotangentSurjective
        (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom I hI)
      hne hspecializes hquotient especial hcomponent P

/-- The degree-one squarefree-level formal-immersion endpoint with the cuspidal special fibre
classified and the full component-cardinality premise removed.

The only remaining additive-fibre input is the marked assertion `12 • P ∈ E₀` on the selected
minimal eleven-adic equation. -/
theorem
    rationalPoint_orderThirtyFive_ne_of_degreeOneCotangentAtEleven_of_componentExponentTwelve
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atEleven.adicCompletion ℚ)]
    {X Y : Scheme} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (modularSection cuspSection :
      Spec (.of (atEleven.adicCompletionIntegers ℚ)) ⟶ X)
    (hresidue : IsIso
      (f.residueFieldMap (closedFiberPointAtEleven cuspSection)))
    (I : Ideal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hI : I ≤ IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (closedFiberPointAtEleven cuspSection))))
    (hdegreeOne : IsLocalRing.IsMappedIdealDegreeOneCotangent
      (f.stalkMap (closedFiberPointAtEleven cuspSection)).hom I hI)
    (hne : modularSection ≠ cuspSection)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      closedFiberPointAtEleven modularSection =
        closedFiberPointAtEleven cuspSection)
    (hquotient : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      modularSection ≫ f = cuspSection ≫ f)
    (P : E.toAffine.Point)
    (hcomponentExponent : ∀ (_hA : (minimalCompletionAtEleven E).HasAdditiveReduction
      (atEleven.adicCompletionIntegers ℚ)),
      12 • minimalCompletionPointAtEleven E P ∈
        nonsingularReductionSubgroup
          (minimalCompletionIntegralModelAtEleven_map E)
          (nonsingularReduction_isAdditive
            (minimalCompletionIntegralModelAtEleven_map E))) :
    addOrderOf P ≠ 35 :=
  rationalPoint_orderThirtyFive_ne_of_cuspidalReduction_of_componentExponentTwelveAtEleven
    (valuation_j_le_one_of_mappedIdealDegreeOneCotangentAtEleven
      f modularSection cuspSection hresidue I hI hdegreeOne hne
      hspecializes hquotient)
    P hcomponentExponent

end MazurTorsion.OrderThirtyFive
