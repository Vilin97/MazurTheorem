/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Neron models and extension of generic-fibre points

This file records the geometric data and mapping property of a Neron model over a discrete
valuation ring.  The model is a smooth separated commutative group scheme, together with an
actual isomorphism from its generic fibre to the prescribed generic-fibre group scheme.  Its
mapping property quantifies over every smooth test scheme over the valuation ring and asserts
that restriction to the generic fibre is bijective.

The resulting equivalence on sections is specialized to the terminal test scheme to identify
integral sections of the model with rational points of the generic fibre.  No existence theorem,
finite-generation statement, rank assertion, finite-field input, or component-group calculation
is bundled into the structure.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- The morphism from the spectrum of the fraction field of `R` to the spectrum of `R`. -/
def fractionSpecMap (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The generic fibre of a commutative group scheme over `Spec R`, formed by actual base
change along `Spec K ⟶ Spec R`. -/
abbrev genericFiber (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (G : CommGroupScheme (Spec (.of R))) : CommGroupScheme (Spec (.of K)) :=
  (Over.pullback (fractionSpecMap R K)).mapCommGrp.obj G

/-- Restrict a section over a test scheme to the generic fibre and then use the supplied
generic-fibre isomorphism. -/
def genericFiberRestriction (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (G : CommGroupScheme (Spec (.of R)))
    (A : CommGroupScheme (Spec (.of K)))
    (e : genericFiber R K G ≅ A)
    (X : Over (Spec (.of R))) :
    (X ⟶ G.X) →* ((Over.pullback (fractionSpecMap R K)).obj X ⟶ A.X) :=
  (IsMonHom.monoidHom e.hom.hom.hom.hom
      ((Over.pullback (fractionSpecMap R K)).obj X)).comp
    ((Over.pullback (fractionSpecMap R K)).homMonoidHom)

@[simp]
theorem genericFiberRestriction_apply (R K : Type u)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (G : CommGroupScheme (Spec (.of R)))
    (A : CommGroupScheme (Spec (.of K)))
    (e : genericFiber R K G ≅ A)
    (X : Over (Spec (.of R))) (x : X ⟶ G.X) :
    genericFiberRestriction R K G A e X x =
      (Over.pullback (fractionSpecMap R K)).map x ≫ e.hom.hom.hom.hom :=
  rfl

/-- A Neron model over a discrete valuation ring.  The mapping property is stated on every
smooth test scheme over the base, not merely on the terminal object. -/
structure NeronModel
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (A : CommGroupScheme (Spec (.of K))) where
  /-- The smooth separated commutative group scheme over the valuation ring. -/
  model : CommGroupScheme (Spec (.of R))
  /-- Smoothness of the model over the valuation ring. -/
  smooth : Smooth model.X.hom
  /-- Separatedness of the model over the valuation ring. -/
  separated : IsSeparated model.X.hom
  /-- The chosen identification of the actual generic fibre with `A`. -/
  genericFiberIso : genericFiber R K model ≅ A
  /-- Restriction to the generic fibre is bijective for every smooth test scheme. -/
  mappingProperty : ∀ (X : Over (Spec (.of R))), Smooth X.hom →
    Function.Bijective
      (genericFiberRestriction R K model A genericFiberIso X)

namespace NeronModel

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {A : CommGroupScheme (Spec (.of K))}

/-- The Neron mapping property as a multiplicative equivalence on sections of a smooth test
scheme. -/
noncomputable def sectionMulEquiv (N : NeronModel R K A)
    (X : Over (Spec (.of R))) (hX : Smooth X.hom) :
    (X ⟶ N.model.X) ≃*
      ((Over.pullback (fractionSpecMap R K)).obj X ⟶ A.X) :=
  MulEquiv.ofBijective
    (genericFiberRestriction R K N.model A N.genericFiberIso X)
    (N.mappingProperty X hX)

@[simp]
theorem sectionMulEquiv_apply (N : NeronModel R K A)
    (X : Over (Spec (.of R))) (hX : Smooth X.hom) (x : X ⟶ N.model.X) :
    N.sectionMulEquiv X hX x =
      genericFiberRestriction R K N.model A N.genericFiberIso X x :=
  rfl

/-- Extend a generic-fibre section uniquely across a smooth test scheme. -/
noncomputable def sectionExtension (N : NeronModel R K A)
    (X : Over (Spec (.of R))) (hX : Smooth X.hom) :
    (((Over.pullback (fractionSpecMap R K)).obj X ⟶ A.X) →*
      (X ⟶ N.model.X)) :=
  (N.sectionMulEquiv X hX).symm.toMonoidHom

@[simp]
theorem restrict_sectionExtension (N : NeronModel R K A)
    (X : Over (Spec (.of R))) (hX : Smooth X.hom)
    (x : (Over.pullback (fractionSpecMap R K)).obj X ⟶ A.X) :
    genericFiberRestriction R K N.model A N.genericFiberIso X
        (N.sectionExtension X hX x) = x :=
  (N.sectionMulEquiv X hX).apply_symm_apply x

@[simp]
theorem sectionExtension_restrict (N : NeronModel R K A)
    (X : Over (Spec (.of R))) (hX : Smooth X.hom)
    (x : X ⟶ N.model.X) :
    N.sectionExtension X hX
        (genericFiberRestriction R K N.model A N.genericFiberIso X x) = x :=
  (N.sectionMulEquiv X hX).symm_apply_apply x

/-- The extension supplied by the Neron mapping property is the unique section with the
prescribed generic-fibre restriction. -/
theorem sectionExtension_unique (N : NeronModel R K A)
    (X : Over (Spec (.of R))) (hX : Smooth X.hom)
    (x : (Over.pullback (fractionSpecMap R K)).obj X ⟶ A.X)
    (y : X ⟶ N.model.X)
    (hy : genericFiberRestriction R K N.model A N.genericFiberIso X y = x) :
    y = N.sectionExtension X hX x := by
  apply (N.mappingProperty X hX).1
  rw [hy, N.restrict_sectionExtension X hX x]

/-- Pullback along an isomorphism of test schemes induces an equivalence on points of a
commutative group scheme. -/
private def pointMulEquivOfOverIso {S : Scheme.{u}} (G : CommGroupScheme S)
    {X Y : Over S} (e : X ≅ Y) : (X ⟶ G.X) ≃* (Y ⟶ G.X) where
  toFun x := e.inv ≫ x
  invFun y := e.hom ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul e.inv x y

/-- Integral sections of a Neron model are multiplicatively equivalent to rational points of
its prescribed generic fibre.  This is the terminal-object specialization of
`sectionMulEquiv`, composed with the canonical terminal-object pullback isomorphism. -/
noncomputable def basePointMulEquiv (N : NeronModel R K A) :
    (Over.mk (𝟙 (Spec (.of R))) ⟶ N.model.X) ≃*
      (Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :=
  let hbase : Smooth (Over.mk (𝟙 (Spec (.of R)))).hom := by
    change Smooth (𝟙 (Spec (.of R)))
    infer_instance
  (N.sectionMulEquiv (Over.mk (𝟙 (Spec (.of R)))) hbase).trans
    (pointMulEquivOfOverIso A (CartesianMonoidalCategory.preservesTerminalIso
      (Over.pullback (fractionSpecMap R K))))

/-- Restriction of integral model points to generic rational points. -/
noncomputable def basePointRestriction (N : NeronModel R K A) :
    (Over.mk (𝟙 (Spec (.of R))) ⟶ N.model.X) →*
      (Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :=
  N.basePointMulEquiv.toMonoidHom

/-- Extension of generic rational points to integral model points. -/
noncomputable def basePointExtension (N : NeronModel R K A) :
    (Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) →*
      (Over.mk (𝟙 (Spec (.of R))) ⟶ N.model.X) :=
  N.basePointMulEquiv.symm.toMonoidHom

@[simp]
theorem basePointRestriction_extension (N : NeronModel R K A)
    (x : Over.mk (𝟙 (Spec (.of K))) ⟶ A.X) :
    N.basePointRestriction (N.basePointExtension x) = x :=
  N.basePointMulEquiv.apply_symm_apply x

@[simp]
theorem basePointExtension_restriction (N : NeronModel R K A)
    (x : Over.mk (𝟙 (Spec (.of R))) ⟶ N.model.X) :
    N.basePointExtension (N.basePointRestriction x) = x :=
  N.basePointMulEquiv.symm_apply_apply x

end NeronModel

end AlgebraicGeometry
