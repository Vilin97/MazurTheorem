/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistDescentEquivalence

/-!
# Scalar twisting as an equivalence of global module sheaves

Effective cover descent transports the scalar-twist equivalence on cover
descent data to an autoequivalence of module sheaves on the glued scheme.
The construction is the composite

`restriction ≌ scalar twist ≌ gluing`.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{0})

namespace CoverDescentData

variable {D}

section

variable
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)

/-- Scalar twisting transported through effective cover descent, as an
autoequivalence of global module sheaves on the glued scheme. -/
noncomputable def scalarTwistGluedEquivalence :
    D.glued.Modules ≌ D.glued.Modules :=
  (restrictionEquivalence (D := D)).trans
    ((scalarTwistEquivalence a hself hcocycle).trans
      (restrictionEquivalence (D := D)).symm)

/-- The forward global scalar-twist functor is restriction, scalar twisting
of descent data, and gluing. -/
@[simp]
theorem scalarTwistGluedEquivalence_functor :
    (scalarTwistGluedEquivalence a hself hcocycle).functor =
      restrictionFunctor (D := D) ⋙
        scalarTwistFunctor a hself hcocycle ⋙
        glueFunctor (D := D) :=
  rfl

/-- The inverse global functor restricts, twists by the pointwise inverse
cocycle, and glues. -/
@[simp]
theorem scalarTwistGluedEquivalence_inverse :
    (scalarTwistGluedEquivalence a hself hcocycle).inverse =
      (restrictionFunctor (D := D) ⋙
        scalarTwistFunctor
          (inverseCoverUnit a)
          (inverseCoverUnit_self a hself)
          (inverseCoverUnit_cocycle a hcocycle)) ⋙
        glueFunctor (D := D) :=
  rfl

/-- Object-level expansion of the global scalar-twist functor. -/
@[simp]
theorem scalarTwistGluedEquivalence_functor_obj
    (W : D.glued.Modules) :
    (scalarTwistGluedEquivalence
        a hself hcocycle).functor.obj W =
      (glueFunctor (D := D)).obj
        ((scalarTwistFunctor
          a hself hcocycle).obj
            ((restrictionFunctor (D := D)).obj W)) :=
  rfl

/-- Morphism-level expansion of the global scalar-twist functor. -/
@[simp]
theorem scalarTwistGluedEquivalence_functor_map
    {W Z : D.glued.Modules} (φ : W ⟶ Z) :
    (scalarTwistGluedEquivalence
        a hself hcocycle).functor.map φ =
      (glueFunctor (D := D)).map
        ((scalarTwistFunctor
          a hself hcocycle).map
            ((restrictionFunctor (D := D)).map φ)) :=
  rfl

/-- Restricting the globally glued scalar twist recovers its
scalar-twisted descent datum. -/
noncomputable def scalarTwistGluedRestrictionIso
    (W : D.glued.Modules) :
    (restrictionFunctor (D := D)).obj
        ((scalarTwistGluedEquivalence
          a hself hcocycle).functor.obj W) ≅
      (scalarTwistFunctor a hself hcocycle).obj
        ((restrictionFunctor (D := D)).obj W) :=
  descentGlueRestrictionIso
    (D := D)
    ((scalarTwistFunctor a hself hcocycle).obj
      ((restrictionFunctor (D := D)).obj W))

/-- Naturality of the restriction comparison for the global scalar twist. -/
theorem scalarTwistGluedRestrictionIso_naturality
    {W Z : D.glued.Modules} (φ : W ⟶ Z) :
    (restrictionFunctor (D := D)).map
          ((scalarTwistGluedEquivalence
            a hself hcocycle).functor.map φ) ≫
        (scalarTwistGluedRestrictionIso
          a hself hcocycle Z).hom =
      (scalarTwistGluedRestrictionIso
          a hself hcocycle W).hom ≫
        (scalarTwistFunctor a hself hcocycle).map
          ((restrictionFunctor (D := D)).map φ) := by
  exact descentGlueRestrictionIso_naturality
    (D := D)
    ((scalarTwistFunctor a hself hcocycle).map
      ((restrictionFunctor (D := D)).map φ))

/-- Restriction of the global scalar-twist functor is naturally isomorphic
to scalar twisting after restriction. -/
noncomputable def scalarTwistGluedRestrictionNatIso :
    (scalarTwistGluedEquivalence
        a hself hcocycle).functor ⋙
        restrictionFunctor (D := D) ≅
      restrictionFunctor (D := D) ⋙
        scalarTwistFunctor a hself hcocycle :=
  NatIso.ofComponents
    (scalarTwistGluedRestrictionIso
      a hself hcocycle)
    (fun φ =>
      scalarTwistGluedRestrictionIso_naturality
        a hself hcocycle φ)

end

end CoverDescentData

end AlgebraicGeometry.Scheme.Modules
