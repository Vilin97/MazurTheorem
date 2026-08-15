/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.NeronModel.Basic

/-!
# Specialization through a Néron model

This file supplies the generic section-specialization API for a Neron model over a
discrete valuation ring. A generic point is first extended across the valuation ring
by the checked Néron mapping property and is then restricted to a test scheme over the
closed fibre. Injectivity of this specialization on torsion turns equality after
restriction into equality of the two integral model points.
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
