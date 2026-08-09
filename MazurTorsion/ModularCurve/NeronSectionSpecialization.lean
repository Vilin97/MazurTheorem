/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.NeronModel.Basic
import MazurTorsion.Kubert.OrderThirtyFiveFormalImmersionAtEleven
import MazurTorsion.PrimeOrder.FormalImmersionAtFive

/-!
# Specializing quotient sections through a Néron model

This file supplies the section-specialization step used in Mazur's formal-immersion
argument.  A generic point of the quotient is first extended across the discrete
valuation ring by the checked Néron mapping property and is then restricted to a
test scheme over the closed fibre.  Injectivity of that specialization on torsion
turns equality after reduction into equality of the two integral quotient sections.

The final two theorems are arithmetic consumers at the actual auxiliary primes.
They derive distinctness from the generic fibres and derive the previously explicit
whole-section quotient collision from source specialization, generic torsion, and
the Néron torsion-specialization kernel.  The formal-immersion input itself is kept
agnostic to the construction of the cusp cotangent map, so it can be supplied by the
q-coordinate/eigen-differential calculation.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- The morphism from the spectrum of a local ring's residue field to the spectrum
of the local ring. -/
def residueSpecMap (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- Regard a scheme over `S` as a test scheme over `S` and map it to the terminal
test scheme. -/
def toBasePointSource {S T : Scheme.{u}} (t : T ⟶ S) :
    Over.mk t ⟶ Over.mk (𝟙 S) :=
  Over.homMk t (by simp)

/-- Restrict a section over the base to any test scheme mapping to the base. -/
def restrictBaseSection {S T : Scheme.{u}} (t : T ⟶ S) (X : Over S)
    (x : Over.mk (𝟙 S) ⟶ X) : Over.mk t ⟶ X :=
  toBasePointSource t ≫ x

@[simp]
theorem restrictBaseSection_comp {S T : Scheme.{u}} (t : T ⟶ S)
    {X Y : Over S} (x : Over.mk (𝟙 S) ⟶ X) (f : X ⟶ Y) :
    restrictBaseSection t Y (x ≫ f) = restrictBaseSection t X x ≫ f := by
  simp only [restrictBaseSection, Category.assoc]

/-- Equality of residue-field restrictions implies equality of the closed-fibre
points selected by the original sections. -/
theorem closedPoint_eq_of_restrictBaseSection_residue_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (.of R))}
    (x y : Over.mk (𝟙 (Spec (.of R))) ⟶ X)
    (h : restrictBaseSection (residueSpecMap R) X x =
      restrictBaseSection (residueSpecMap R) X y) :
    x.left (IsLocalRing.closedPoint R) =
      y.left (IsLocalRing.closedPoint R) := by
  have hleft := congrArg Over.Hom.left h
  change residueSpecMap R ≫ x.left = residueSpecMap R ≫ y.left at hleft
  have hpoint := congrArg
    (fun f : Spec (.of (IsLocalRing.ResidueField R)) ⟶ X.left ↦
      f (default : Spec (.of (IsLocalRing.ResidueField R)))) hleft
  have hclosed : residueSpecMap R
      (default : Spec (.of (IsLocalRing.ResidueField R))) =
      IsLocalRing.closedPoint R := by
    change PrimeSpectrum.comap (IsLocalRing.residue R) _ = _
    exact IsLocalRing.PrimeSpectrum.comap_residue R _
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hclosed] at hpoint
  exact hpoint

namespace NeronModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {A : CommGroupScheme (Spec (.of K))}

/-- Restriction of integral model points along a test scheme over the base, as a
group homomorphism. -/
def restrictBasePoint (N : NeronModel R K A) {T : Scheme.{u}}
    (t : T ⟶ Spec (.of R)) :
    (Over.mk (𝟙 (Spec (.of R))) ⟶ N.model.X) →*
      (Over.mk t ⟶ N.model.X) where
  toFun := restrictBaseSection t N.model.X
  map_one' := MonObj.comp_one (toBasePointSource t)
  map_mul' x y := MonObj.comp_mul (toBasePointSource t) x y

@[simp]
theorem restrictBasePoint_apply (N : NeronModel R K A)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    (x : Over.mk (𝟙 (Spec (.of R))) ⟶ N.model.X) :
    N.restrictBasePoint t x = restrictBaseSection t N.model.X x :=
  rfl

/-- Specialize a generic rational point by first taking its unique Néron extension
and then restricting that extension along a test scheme over the base. -/
def basePointSpecialization (N : NeronModel R K A) {T : Scheme.{u}}
    (t : T ⟶ Spec (.of R)) :
    (Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) →*
      (Over.mk t ⟶ N.model.X) :=
  (N.restrictBasePoint t).comp N.basePointExtension

@[simp]
theorem basePointSpecialization_apply (N : NeronModel R K A)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    N.basePointSpecialization t x =
      restrictBaseSection t N.model.X (N.basePointExtension x) :=
  rfl

/-- If specialization is injective on generic torsion, two integral model
points with equal specialization and torsion generic difference are equal. -/
theorem basePoint_eq_of_restrict_eq_of_generic_torsion
    (N : NeronModel R K A) {T : Scheme.{u}}
    (t : T ⟶ Spec (.of R))
    (hinjective : ∀ z : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X,
      IsOfFinOrder z → N.basePointSpecialization t z = 1 → z = 1)
    (x y : Over.mk (𝟙 (Spec (.of R))) ⟶ N.model.X)
    (htorsion : IsOfFinOrder
      (N.basePointRestriction x / N.basePointRestriction y))
    (hspecial : N.restrictBasePoint t x = N.restrictBasePoint t y) :
    x = y := by
  let z := N.basePointRestriction x / N.basePointRestriction y
  have hext : N.basePointExtension z = x / y := by
    simp only [z, map_div, basePointExtension_restriction]
  have hspecialDiff : N.restrictBasePoint t (x / y) = 1 := by
    rw [map_div, hspecial]
    exact div_self' (N.restrictBasePoint t y)
  have hspecialZ : N.basePointSpecialization t z = 1 := by
    change N.restrictBasePoint t (N.basePointExtension z) = 1
    rw [hext]
    exact hspecialDiff
  have hz : z = 1 := hinjective z htorsion hspecialZ
  have hdiff : x / y = 1 := by
    rw [← hext, hz, map_one]
  exact div_eq_one.mp hdiff

end NeronModel

end AlgebraicGeometry

namespace MazurTorsion

open _root_.AlgebraicGeometry
open MazurTorsion.IntegerPrimeSpecialization

namespace PrimeOrder

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
