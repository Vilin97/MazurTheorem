/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneFunctoriality

/-!
# Quasi-finite flat commutative group schemes and their fppf cohomology

Mazur's pre-admissible group schemes over `Spec ℤ` are flat, quasi-finite, separated, and of
finite presentation; they are only required to become finite after removing the level prime.
This file packages the common structural part without prematurely adding a level, a power that
kills the group, an open-base finiteness witness, or an admissible filtration.

Here `quasi-finite` is represented by Mathlib's `LocallyQuasiFinite` together with
`QuasiCompact`, and `finite presentation` by `LocallyOfFinitePresentation` together with the
same quasi-compactness condition.  Morphisms act functorially on represented points and fppf
`H¹`.  Finite-flat group schemes and their morphisms embed in this category and provide
compiled compatibility consumers for both the coefficient and map-level ambient APIs.

No extension-by-zero construction or claim about the four elementary admissible factors is made
in this file.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe v u

/-- The structural property of a flat, quasi-finite, separated commutative group scheme of
finite presentation over `S`. -/
def quasiFiniteFlatCommGroupSchemeProperty (S : Scheme.{u}) :
    ObjectProperty (CommGroupScheme S) :=
  fun G ↦ Flat G.X.hom ∧ LocallyQuasiFinite G.X.hom ∧ QuasiCompact G.X.hom ∧
    IsSeparated G.X.hom ∧ LocallyOfFinitePresentation G.X.hom

/-- Flat, quasi-finite, separated commutative group schemes of finite presentation over `S`.
This is the ambient category in which Mazur's integral pre-admissible groups live. -/
abbrev QuasiFiniteFlatCommGroupScheme (S : Scheme.{u}) :=
  (quasiFiniteFlatCommGroupSchemeProperty S).FullSubcategory

namespace QuasiFiniteFlatCommGroupScheme

variable {S : Scheme.{u}}

/-- The underlying ambient commutative group scheme. -/
abbrev toCommGroupScheme (G : QuasiFiniteFlatCommGroupScheme S) : CommGroupScheme S := G.obj

/-- The underlying scheme. -/
abbrev scheme (G : QuasiFiniteFlatCommGroupScheme S) : Scheme.{u} := G.obj.X.left

/-- The flat, quasi-finite, separated, finite-presentation structure morphism. -/
abbrev structureMap (G : QuasiFiniteFlatCommGroupScheme S) : G.scheme ⟶ S := G.obj.X.hom

instance (G : QuasiFiniteFlatCommGroupScheme S) : Flat G.structureMap := G.property.1

instance (G : QuasiFiniteFlatCommGroupScheme S) : LocallyQuasiFinite G.structureMap :=
  G.property.2.1

instance (G : QuasiFiniteFlatCommGroupScheme S) : QuasiCompact G.structureMap :=
  G.property.2.2.1

instance (G : QuasiFiniteFlatCommGroupScheme S) : IsSeparated G.structureMap :=
  G.property.2.2.2.1

instance (G : QuasiFiniteFlatCommGroupScheme S) : LocallyOfFinitePresentation G.structureMap :=
  G.property.2.2.2.2

/-- Global fppf `H¹` of a quasi-finite flat commutative group scheme, through the ambient
represented-point wrapper. -/
abbrev FppfHOne (G : QuasiFiniteFlatCommGroupScheme S) : Type _ :=
  CommGroupScheme.FppfHOne.{v} G.obj

noncomputable instance fppfHOneCommGroup (G : QuasiFiniteFlatCommGroupScheme S) :
    CommGroup G.FppfHOne.{v} :=
  CommGroupScheme.fppfHOneCommGroup G.obj

/-- A morphism of quasi-finite flat commutative group schemes acts on test-scheme points through
its underlying ambient group-scheme morphism. -/
def mapPoint {G H : QuasiFiniteFlatCommGroupScheme S} (f : G ⟶ H) (T : Over S) :
    CommGroupScheme.Point G.obj T →* CommGroupScheme.Point H.obj T :=
  CommGroupScheme.mapPoint f.hom T

@[simp]
theorem mapPoint_apply {G H : QuasiFiniteFlatCommGroupScheme S}
    (f : G ⟶ H) (T : Over S) (x : CommGroupScheme.Point G.obj T) :
    mapPoint f T x = x ≫ f.hom.hom.hom.hom :=
  rfl

/-- A quasi-finite flat group-scheme morphism induces the canonical map on global fppf
`H¹`. -/
def fppfHOneMap {G H : QuasiFiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    G.FppfHOne.{v} →* H.FppfHOne.{v} :=
  CommGroupScheme.fppfHOneMap f.hom

@[simp]
theorem fppfHOneMap_id (G : QuasiFiniteFlatCommGroupScheme S) :
    fppfHOneMap (CategoryStruct.id G) = MonoidHom.id G.FppfHOne.{v} := by
  exact CommGroupScheme.fppfHOneMap_id G.obj

theorem fppfHOneMap_comp
    {G H K : QuasiFiniteFlatCommGroupScheme S} (f : G ⟶ H) (g : H ⟶ K) :
    fppfHOneMap (f ≫ g) = (fppfHOneMap g).comp (fppfHOneMap f) := by
  exact CommGroupScheme.fppfHOneMap_comp f.hom g.hom

/-- A finite-flat commutative group scheme whose structure map is locally of finite presentation
satisfies the broader quasi-finite, separated, finite-presentation property.  The hypothesis is
explicit because the legacy finite-flat wrapper does not store finite-presentation data. -/
def ofFiniteFlat (G : FiniteFlatCommGroupScheme S)
    [LocallyOfFinitePresentation G.obj.X.hom] :
    QuasiFiniteFlatCommGroupScheme S where
  obj := G.obj
  property := by
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The new quasi-finite wrapper is definitionally compatible with the existing finite-flat
global fppf `H¹`; this is the first downstream consumer of the broader interface. -/
noncomputable def fppfHOneMulEquivOfFiniteFlat (G : FiniteFlatCommGroupScheme S)
    [LocallyOfFinitePresentation G.obj.X.hom] :
    (ofFiniteFlat G).FppfHOne.{v} ≃* G.FppfHOne.{v} :=
  MulEquiv.refl _

/-- A finite-flat morphism gives the same morphism after both endpoints are regarded as
quasi-finite flat group schemes. -/
def ofFiniteFlatMap {G H : FiniteFlatCommGroupScheme S}
    (f : G ⟶ H) [LocallyOfFinitePresentation G.obj.X.hom]
    [LocallyOfFinitePresentation H.obj.X.hom] :
    ofFiniteFlat G ⟶ ofFiniteFlat H :=
  ObjectProperty.homMk f.hom

/-- The quasi-finite and finite-flat maps on fppf `H¹` agree under the definitional
compatibility equivalences.  This is a morphism-level downstream consumer, needed before
transporting exact quotient sequences to Mazur's four integral elementary factors. -/
theorem fppfHOneMap_ofFiniteFlat_eq
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [LocallyOfFinitePresentation G.obj.X.hom]
    [LocallyOfFinitePresentation H.obj.X.hom] :
    fppfHOneMap.{v} (ofFiniteFlatMap f) =
      FiniteFlatCommGroupScheme.fppfHOneMap f :=
  rfl

end QuasiFiniteFlatCommGroupScheme

end AlgebraicGeometry
