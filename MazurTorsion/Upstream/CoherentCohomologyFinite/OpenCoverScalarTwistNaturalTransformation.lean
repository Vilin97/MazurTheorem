/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedNaturalTransformation
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistEquivalence

/-!
# Natural maps into open-cover scalar twists

A compatible family of chart functions gives chartwise multiplication
maps into a scalar twist.  Effective descent globalizes those maps on the
scheme glued from the cover, and transport across the canonical
open-cover equivalence gives the corresponding natural transformation
on the original scheme.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData

section OpenCover

variable {X : Scheme.{0}} (𝒰 : X.OpenCover)
variable
    (a : ∀ i j,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition 𝒰.gluedCover a)
    (b : ∀ i, Γ(𝒰.gluedCover.U i, ⊤))
    (hb : CoverScalarSectionCompatibility a b)

/--
Apply the inverse module-category equivalence to the globalized scalar
map on the glued cover.
-/
noncomputable def transportedGluedScalarTwistMap
    (M : X.Modules) :
    (modulesToGluedEquivalence 𝒰).inverse.obj
        ((modulesToGluedEquivalence 𝒰).functor.obj M) ⟶
      (modulesToGluedEquivalence 𝒰).inverse.obj
        ((scalarTwistGluedEquivalence
          a hself hcocycle).functor.obj
            ((modulesToGluedEquivalence
              𝒰).functor.obj M)) :=
  (modulesToGluedEquivalence 𝒰).inverse.map
    ((scalarTwistGluedNatTrans
      a hself hcocycle b hb).app
        ((modulesToGluedEquivalence 𝒰).functor.obj M))

/--
Transporting the globalized scalar maps through the inverse equivalence
gives a natural transformation between the two reconstructed functors
on the original scheme.
-/
noncomputable def transportedGluedScalarTwistNatTrans :
    (modulesToGluedEquivalence 𝒰).functor ⋙
        (modulesToGluedEquivalence 𝒰).inverse ⟶
      (modulesToGluedEquivalence 𝒰).functor ⋙
        (scalarTwistGluedEquivalence
          a hself hcocycle).functor ⋙
        (modulesToGluedEquivalence 𝒰).inverse where
  app M :=
    transportedGluedScalarTwistMap
      𝒰 a hself hcocycle b hb M
  naturality {M N} φ := by
    change
      (modulesToGluedEquivalence 𝒰).inverse.map
            ((modulesToGluedEquivalence
              𝒰).functor.map φ) ≫
          (modulesToGluedEquivalence 𝒰).inverse.map
            ((scalarTwistGluedNatTrans
              a hself hcocycle b hb).app
                ((modulesToGluedEquivalence
                  𝒰).functor.obj N)) =
        (modulesToGluedEquivalence 𝒰).inverse.map
              ((scalarTwistGluedNatTrans
                a hself hcocycle b hb).app
                  ((modulesToGluedEquivalence
                    𝒰).functor.obj M)) ≫
            (modulesToGluedEquivalence 𝒰).inverse.map
              ((scalarTwistGluedEquivalence
                a hself hcocycle).functor.map
                  ((modulesToGluedEquivalence
                    𝒰).functor.map φ))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simpa only [Functor.id_obj, Functor.id_map] using
      (scalarTwistGluedNatTrans
        a hself hcocycle b hb).naturality
          ((modulesToGluedEquivalence
            𝒰).functor.map φ)

/--
The scalar-twist morphism on the original scheme, obtained by
transporting the globalized glued-cover morphism through the canonical
module-category equivalence.
-/
noncomputable def openCoverScalarTwistHom
    (M : X.Modules) :
    M ⟶
      (openCoverScalarTwistEquivalence
        𝒰 a hself hcocycle).functor.obj M :=
  (modulesToGluedEquivalence 𝒰).unitIso.hom.app M ≫
    transportedGluedScalarTwistMap
      𝒰 a hself hcocycle b hb M

/--
The compatible chart-function family defines a natural transformation
from the identity to the transported open-cover scalar twist.
-/
noncomputable def openCoverScalarTwistNatTrans :
    𝟭 X.Modules ⟶
      (openCoverScalarTwistEquivalence
        𝒰 a hself hcocycle).functor :=
  (modulesToGluedEquivalence 𝒰).unitIso.hom ≫
    transportedGluedScalarTwistNatTrans
      𝒰 a hself hcocycle b hb

/-- A component of the transported natural transformation is its named
open-cover scalar-twist morphism. -/
@[simp]
theorem openCoverScalarTwistNatTrans_app
    (M : X.Modules) :
    (openCoverScalarTwistNatTrans
        𝒰 a hself hcocycle b hb).app M =
      openCoverScalarTwistHom
        𝒰 a hself hcocycle b hb M :=
  rfl

/-- Expansion of the named transported open-cover scalar morphism. -/
@[simp]
theorem openCoverScalarTwistHom_eq
    (M : X.Modules) :
    openCoverScalarTwistHom
        𝒰 a hself hcocycle b hb M =
      (modulesToGluedEquivalence 𝒰).unitIso.hom.app M ≫
        transportedGluedScalarTwistMap
          𝒰 a hself hcocycle b hb M :=
  rfl

/--
The transported component is an isomorphism when multiplication by
each chart function is an isomorphism after restricting the transported
module to the cover.
-/
theorem isIso_openCoverScalarTwistNatTrans_app
    (M : X.Modules)
    (hiso : ∀ i,
      IsIso
        (scalarEndomorphism
          (((restrictionFunctor
              (D := 𝒰.gluedCover)).obj
            ((modulesToGluedEquivalence
              𝒰).functor.obj M)).chart i)
          (b i))) :
    IsIso
      ((openCoverScalarTwistNatTrans
        𝒰 a hself hcocycle b hb).app M) := by
  letI : IsIso
      ((transportedGluedScalarTwistNatTrans
        𝒰 a hself hcocycle b hb).app M) := by
    change IsIso
      ((modulesToGluedEquivalence 𝒰).inverse.map
        ((scalarTwistGluedNatTrans
          a hself hcocycle b hb).app
            ((modulesToGluedEquivalence
              𝒰).functor.obj M)))
    letI : IsIso
        ((scalarTwistGluedNatTrans
          a hself hcocycle b hb).app
            ((modulesToGluedEquivalence
              𝒰).functor.obj M)) :=
      isIso_scalarTwistGluedNatTrans_app
        a hself hcocycle b hb
        ((modulesToGluedEquivalence 𝒰).functor.obj M)
        hiso
    infer_instance
  change IsIso
    ((modulesToGluedEquivalence
        𝒰).unitIso.hom.app M ≫
      (transportedGluedScalarTwistNatTrans
        𝒰 a hself hcocycle b hb).app M)
  infer_instance

end OpenCover

end AlgebraicGeometry.Scheme.Modules
