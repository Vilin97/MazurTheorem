/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.NeronModel.Specialization
import MazurTorsion.Kubert.OrderThirtyFiveFormalImmersionAtEleven
import MazurTorsion.PrimeOrder.FormalImmersionAtFive

/-!
# Specializing quotient sections through proper and Néron models

This file supplies arithmetic consumers of the proper-model and Neron specialization APIs at the
actual auxiliary primes.
They derive distinctness from the generic fibres and derive the previously explicit
whole-section quotient collision from source specialization, generic torsion, and
the Néron torsion-specialization kernel.  The formal-immersion input itself is kept
agnostic to the construction of the cusp cotangent map, so it can be supplied by the
q-coordinate/eigen-differential calculation.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace MazurTorsion

open _root_.AlgebraicGeometry
open MazurTorsion.IntegerPrimeSpecialization

namespace PrimeOrder

/-- The prime-order endpoint using only an actual proper group model at five.  Properness supplies
the extension of rational points; no Neron mapping property for general smooth test schemes is
assumed. -/
theorem rationalPoint_primeOrder_ne_of_properModelSpecializationAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : CommGroupScheme (Spec (.of (atFive.adicCompletion ℚ)))}
    (G : CommGroupScheme (Spec (.of (atFive.adicCompletionIntegers ℚ))))
    [IsProper G.X.hom]
    (e : genericFiber (atFive.adicCompletionIntegers ℚ)
      (atFive.adicCompletion ℚ) G ≅ A)
    (X : Over (Spec (.of (atFive.adicCompletionIntegers ℚ))))
    (quotientMap : X ⟶ G.X)
    (modularSection cuspSection :
      Over.mk (𝟙 (Spec (.of (atFive.adicCompletionIntegers ℚ)))) ⟶ X)
    (hformal : IsFormalImmersionAt quotientMap.left
      (cuspSection.left (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))))
    (hgeneric_ne :
      fractionSpecMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ) ≫ modularSection.left ≠
        fractionSpecMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ) ≫ cuspSection.left)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      restrictBaseSection
          (residueSpecMap (atFive.adicCompletionIntegers ℚ)) X modularSection =
        restrictBaseSection
          (residueSpecMap (atFive.adicCompletionIntegers ℚ)) X cuspSection)
    (htorsion : IsOfFinOrder
      (ProperModelBasePoint.restriction G e (modularSection ≫ quotientMap) /
        ProperModelBasePoint.restriction G e (cuspSection ≫ quotientMap)))
    (hinjective : ∀ z :
        Over.mk (𝟙 (Spec (.of (atFive.adicCompletion ℚ)))) ⟶ A.X,
      IsOfFinOrder z →
        ProperModelBasePoint.basePointSpecialization G e
          (residueSpecMap (atFive.adicCompletionIntegers ℚ)) z = 1 →
        z = 1)
    (P : E.toAffine.Point)
    (order : ℕ) (hprime : order.Prime) (horder : 11 ≤ order) :
    addOrderOf P ≠ order := by
  have hne : modularSection.left ≠ cuspSection.left := by
    intro h
    apply hgeneric_ne
    rw [h]
  apply rationalPoint_primeOrder_ne_of_formalImmersionAtFive
    quotientMap.left modularSection.left cuspSection.left hformal hne
  · intro hj
    exact closedPoint_eq_of_restrictBaseSection_residue_eq
      modularSection cuspSection (hspecializes hj)
  · intro hj
    have hover : modularSection ≫ quotientMap = cuspSection ≫ quotientMap :=
      ProperModelBasePoint.basePoint_eq_of_restrict_eq_of_generic_torsion
        G e (residueSpecMap (atFive.adicCompletionIntegers ℚ)) hinjective
        (modularSection ≫ quotientMap) (cuspSection ≫ quotientMap)
        htorsion (by
          simpa only [ProperModelBasePoint.restrictBasePoint_apply,
            restrictBaseSection_comp] using
            congrArg (fun s ↦ s ≫ quotientMap) (hspecializes hj))
    simpa only [Over.comp_left] using congrArg Over.Hom.left hover
  · exact hprime
  · exact horder

/-- The theorem-critical prime-order endpoint with the quotient collision
deduced from actual Néron specialization data. -/
theorem rationalPoint_primeOrder_ne_of_neronSpecializationAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : CommGroupScheme
      (Spec (.of (atFive.adicCompletion ℚ)))}
    (Ner : NeronModel
      (atFive.adicCompletionIntegers ℚ)
      (atFive.adicCompletion ℚ) A)
    (X : Over (Spec (.of (atFive.adicCompletionIntegers ℚ))))
    (quotientMap : X ⟶ Ner.model.X)
    (modularSection cuspSection :
      Over.mk (𝟙 (Spec (.of (atFive.adicCompletionIntegers ℚ)))) ⟶ X)
    (hformal : IsFormalImmersionAt quotientMap.left
      (cuspSection.left (IsLocalRing.closedPoint
        (atFive.adicCompletionIntegers ℚ))))
    (hgeneric_ne :
      fractionSpecMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ) ≫ modularSection.left ≠
        fractionSpecMap (atFive.adicCompletionIntegers ℚ)
          (atFive.adicCompletion ℚ) ≫ cuspSection.left)
    (hspecializes : ¬ atFive.valuation ℚ E.j ≤ 1 →
      restrictBaseSection
          (residueSpecMap (atFive.adicCompletionIntegers ℚ)) X modularSection =
        restrictBaseSection
          (residueSpecMap (atFive.adicCompletionIntegers ℚ)) X cuspSection)
    (htorsion : IsOfFinOrder
      (Ner.basePointRestriction (modularSection ≫ quotientMap) /
        Ner.basePointRestriction (cuspSection ≫ quotientMap)))
    (hinjective : ∀ z :
        Over.mk (𝟙 (Spec (.of (atFive.adicCompletion ℚ)))) ⟶ A.X,
      IsOfFinOrder z →
        Ner.basePointSpecialization
          (residueSpecMap (atFive.adicCompletionIntegers ℚ)) z = 1 →
        z = 1)
    (P : E.toAffine.Point)
    (order : ℕ) (hprime : order.Prime) (horder : 11 ≤ order) :
    addOrderOf P ≠ order := by
  have hne : modularSection.left ≠ cuspSection.left := by
    intro h
    apply hgeneric_ne
    rw [h]
  apply rationalPoint_primeOrder_ne_of_formalImmersionAtFive
    quotientMap.left modularSection.left cuspSection.left hformal hne
  · intro hj
    exact closedPoint_eq_of_restrictBaseSection_residue_eq
      modularSection cuspSection (hspecializes hj)
  · intro hj
    have hover : modularSection ≫ quotientMap = cuspSection ≫ quotientMap :=
      Ner.basePoint_eq_of_restrict_eq_of_generic_torsion
        (residueSpecMap (atFive.adicCompletionIntegers ℚ)) hinjective
        (modularSection ≫ quotientMap) (cuspSection ≫ quotientMap)
        htorsion (by
          simpa only [NeronModel.restrictBasePoint_apply,
            restrictBaseSection_comp] using
            congrArg (fun s ↦ s ≫ quotientMap) (hspecializes hj))
    simpa only [Over.comp_left] using congrArg Over.Hom.left hover
  · exact hprime
  · exact horder

end PrimeOrder

namespace OrderThirtyFive

/-- The theorem-critical order-35 endpoint at the valid auxiliary prime eleven,
with the quotient collision deduced from actual Néron specialization data. -/
theorem rationalPoint_orderThirtyFive_ne_of_neronSpecializationAtEleven
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : CommGroupScheme
      (Spec (.of (atEleven.adicCompletion ℚ)))}
    (Ner : NeronModel
      (atEleven.adicCompletionIntegers ℚ)
      (atEleven.adicCompletion ℚ) A)
    (X : Over (Spec (.of (atEleven.adicCompletionIntegers ℚ))))
    (quotientMap : X ⟶ Ner.model.X)
    (modularSection cuspSection :
      Over.mk (𝟙 (Spec (.of (atEleven.adicCompletionIntegers ℚ)))) ⟶ X)
    (hformal : IsFormalImmersionAt quotientMap.left
      (closedFiberPointAtEleven cuspSection.left))
    (hgeneric_ne :
      fractionSpecMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ) ≫ modularSection.left ≠
        fractionSpecMap (atEleven.adicCompletionIntegers ℚ)
          (atEleven.adicCompletion ℚ) ≫ cuspSection.left)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      restrictBaseSection
          (residueSpecMap (atEleven.adicCompletionIntegers ℚ)) X modularSection =
        restrictBaseSection
          (residueSpecMap (atEleven.adicCompletionIntegers ℚ)) X cuspSection)
    (htorsion : IsOfFinOrder
      (Ner.basePointRestriction (modularSection ≫ quotientMap) /
        Ner.basePointRestriction (cuspSection ≫ quotientMap)))
    (hinjective : ∀ z :
        Over.mk (𝟙 (Spec (.of (atEleven.adicCompletion ℚ)))) ⟶ A.X,
      IsOfFinOrder z →
        Ner.basePointSpecialization
          (residueSpecMap (atEleven.adicCompletionIntegers ℚ)) z = 1 →
        z = 1)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  have hne : modularSection.left ≠ cuspSection.left := by
    intro h
    apply hgeneric_ne
    rw [h]
  apply rationalPoint_orderThirtyFive_ne_of_formalImmersionAtEleven
    quotientMap.left modularSection.left cuspSection.left hformal hne
  · intro hj
    exact closedPoint_eq_of_restrictBaseSection_residue_eq
      modularSection cuspSection (hspecializes hj)
  · intro hj
    have hover : modularSection ≫ quotientMap = cuspSection ≫ quotientMap :=
      Ner.basePoint_eq_of_restrict_eq_of_generic_torsion
        (residueSpecMap (atEleven.adicCompletionIntegers ℚ)) hinjective
        (modularSection ≫ quotientMap) (cuspSection ≫ quotientMap)
        htorsion (by
          simpa only [NeronModel.restrictBasePoint_apply,
            restrictBaseSection_comp] using
            congrArg (fun s ↦ s ≫ quotientMap) (hspecializes hj))
    simpa only [Over.comp_left] using congrArg Over.Hom.left hover

end OrderThirtyFive

end MazurTorsion
