/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfHOne

/-!
# Quasi-finite flat commutative group schemes and their fppf cohomology

Mazur's pre-admissible group schemes over `Spec ℤ` are flat, quasi-finite, separated, and of
finite presentation; they are only required to become finite after removing the level prime.
This file packages the common structural part without prematurely adding a level, a power that
kills the group, an open-base finiteness witness, or an admissible filtration.

Here `quasi-finite` is represented by Mathlib's `LocallyQuasiFinite` together with
`QuasiCompact`, and `finite presentation` by `LocallyOfFinitePresentation` together with the
same quasi-compactness condition.  Finite-flat group schemes embed in this category and provide
a compiled compatibility consumer for the ambient fppf-`H¹` wrapper.

No extension-by-zero construction or claim about the four elementary admissible factors is made
in this file.
-/

noncomputable section

open CategoryTheory

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

end QuasiFiniteFlatCommGroupScheme

end AlgebraicGeometry
