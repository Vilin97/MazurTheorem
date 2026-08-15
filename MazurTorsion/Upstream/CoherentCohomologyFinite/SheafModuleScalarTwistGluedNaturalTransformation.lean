/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistNaturalTransformation

/-!
# Natural maps into global scalar twists

A compatible family of chart functions gives a morphism into the
scalar twist of every cover-descent datum.  This file globalizes that
natural transformation through effective descent on the scheme
associated to a glue datum.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData

variable (D : Scheme.GlueData.{0})

namespace CoverDescentData

variable {D}
variable
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (b : ∀ i, Γ(D.U i, ⊤))
    (hb : CoverScalarSectionCompatibility a b)

/--
Gluing the chartwise scalar morphism associated to the canonical
descent datum of a global module.
-/
noncomputable def glueScalarTwistMap
    (W : D.glued.Modules) :
    (glueFunctor (D := D)).obj
        ((restrictionFunctor (D := D)).obj W) ⟶
      (glueFunctor (D := D)).obj
        ((scalarTwistFunctor
          a hself hcocycle).obj
            ((restrictionFunctor (D := D)).obj W)) :=
  (glueFunctor (D := D)).map
    ((scalarTwistHom
      a hself hcocycle b hb)
        ((restrictionFunctor (D := D)).obj W))

/-- The glued chartwise scalar maps commute with global morphisms. -/
theorem glueScalarTwistMap_naturality
    {W Z : D.glued.Modules} (φ : W ⟶ Z) :
    (glueFunctor (D := D)).map
          ((restrictionFunctor (D := D)).map φ) ≫
        glueScalarTwistMap
          a hself hcocycle b hb Z =
      glueScalarTwistMap
          a hself hcocycle b hb W ≫
        (scalarTwistGluedEquivalence
          a hself hcocycle).functor.map φ := by
  change
    (glueFunctor (D := D)).map
          ((restrictionFunctor (D := D)).map φ) ≫
        (glueFunctor (D := D)).map
          ((scalarTwistNatTrans
            a hself hcocycle b hb).app
              ((restrictionFunctor (D := D)).obj Z)) =
      (glueFunctor (D := D)).map
          ((scalarTwistNatTrans
            a hself hcocycle b hb).app
              ((restrictionFunctor (D := D)).obj W)) ≫
        (glueFunctor (D := D)).map
          ((scalarTwistFunctor
            a hself hcocycle).map
              ((restrictionFunctor (D := D)).map φ))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simpa only [Functor.id_obj, Functor.id_map] using
    (scalarTwistNatTrans
      a hself hcocycle b hb).naturality
        ((restrictionFunctor (D := D)).map φ)

/--
The glued chartwise scalar maps form a natural transformation from
cover reconstruction to scalar-twisted cover reconstruction.
-/
noncomputable def glueScalarTwistNatTrans :
    restrictionFunctor (D := D) ⋙
        glueFunctor (D := D) ⟶
      restrictionFunctor (D := D) ⋙
        scalarTwistFunctor a hself hcocycle ⋙
        glueFunctor (D := D) where
  app W :=
    glueScalarTwistMap
      a hself hcocycle b hb W
  naturality {W Z} φ := by
    exact glueScalarTwistMap_naturality
      a hself hcocycle b hb φ

/--
The global morphism obtained by reconstructing a module from its cover
restrictions and then gluing the compatible chartwise scalar maps.
-/
noncomputable def scalarTwistGluedHom
    (W : D.glued.Modules) :
    W ⟶
      (scalarTwistGluedEquivalence
        a hself hcocycle).functor.obj W :=
  coverRestrictionGlueUnit D W ≫
    glueScalarTwistMap
      a hself hcocycle b hb W

/--
Compatible chartwise multiplication globalizes naturally on the scheme
obtained from the glue datum.
-/
noncomputable def scalarTwistGluedNatTrans :
    𝟭 D.glued.Modules ⟶
      (scalarTwistGluedEquivalence
        a hself hcocycle).functor :=
  (restrictionGlueIso (D := D)).hom ≫
    glueScalarTwistNatTrans
      a hself hcocycle b hb

/-- A component of the global natural transformation is its named
globalized scalar-twist morphism. -/
@[simp]
theorem scalarTwistGluedNatTrans_app
    (W : D.glued.Modules) :
    (scalarTwistGluedNatTrans
        a hself hcocycle b hb).app W =
      scalarTwistGluedHom
        a hself hcocycle b hb W :=
  rfl

/-- Expansion of the named globalized scalar-twist morphism. -/
@[simp]
theorem scalarTwistGluedHom_eq
    (W : D.glued.Modules) :
    scalarTwistGluedHom
        a hself hcocycle b hb W =
      coverRestrictionGlueUnit D W ≫
        glueScalarTwistMap
          a hself hcocycle b hb W :=
  rfl

/--
The descent scalar morphism is an isomorphism when each chart scalar
endomorphism is an isomorphism.
-/
theorem isIso_scalarTwistHom
    (A : CoverDescentData D)
    (hiso : ∀ i,
      IsIso
        (scalarEndomorphism
          (A.chart i)
          (b i))) :
    IsIso
      (scalarTwistHom
        a hself hcocycle b hb A) := by
  let s :=
    scalarTwistHom
      a hself hcocycle b hb A
  letI : ∀ i, IsIso (s.app i) := fun i => by
    change IsIso
      (scalarEndomorphism
        (A.chart i)
        (b i))
    exact hiso i
  exact (s.isoOfComponents).isIso_hom

/-- Gluing preserves the isomorphism criterion for chartwise scalar
endomorphisms. -/
theorem isIso_glueScalarTwistMap
    (W : D.glued.Modules)
    (hiso : ∀ i,
      IsIso
        (scalarEndomorphism
          (((restrictionFunctor (D := D)).obj W).chart i)
          (b i))) :
    IsIso
      (glueScalarTwistMap
        a hself hcocycle b hb W) := by
  unfold glueScalarTwistMap
  letI :=
    isIso_scalarTwistHom
      a hself hcocycle b hb
      ((restrictionFunctor (D := D)).obj W)
      hiso
  infer_instance

/--
The globalized component is an isomorphism whenever all of its
chartwise scalar endomorphisms are isomorphisms.
-/
theorem isIso_scalarTwistGluedNatTrans_app
    (W : D.glued.Modules)
    (hiso : ∀ i,
      IsIso
        (scalarEndomorphism
          (((restrictionFunctor (D := D)).obj W).chart i)
          (b i))) :
    IsIso
      ((scalarTwistGluedNatTrans
        a hself hcocycle b hb).app W) := by
  letI : IsIso
      ((glueScalarTwistNatTrans
        a hself hcocycle b hb).app W) := by
    change IsIso
      (glueScalarTwistMap
        a hself hcocycle b hb W)
    exact
    isIso_glueScalarTwistMap
      a hself hcocycle b hb W hiso
  change IsIso
    ((restrictionGlueIso
        (D := D)).hom.app W ≫
      (glueScalarTwistNatTrans
        a hself hcocycle b hb).app W)
  infer_instance

end CoverDescentData

end AlgebraicGeometry.Scheme.Modules
