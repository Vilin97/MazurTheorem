/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedNaturalTransformation
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentIso

/-!
# Restricting the global scalar-twist natural map

After restricting the globalized chartwise scalar map back to the cover
and applying effective descent, one recovers the original chartwise
scalar morphism.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable {D : Scheme.GlueData.{0}}
variable
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (b : ∀ i, Γ(D.U i, ⊤))
    (hb : CoverScalarSectionCompatibility a b)

/--
Restricting a reconstruction unit followed by a glued descent morphism,
then applying the effective-descent counit, recovers that morphism.
-/
theorem restrictionEquivalence_unit_glueMap
    (W : D.glued.Modules)
    {A : CoverDescentData D}
    (φ :
      (restrictionEquivalence
        (D := D)).functor.obj W ⟶ A) :
    (restrictionEquivalence (D := D)).functor.map
          ((restrictionEquivalence
              (D := D)).unitIso.hom.app W ≫
            (restrictionEquivalence
              (D := D)).inverse.map φ) ≫
        (restrictionEquivalence
          (D := D)).counitIso.hom.app A =
      φ := by
  have hnat :
      (restrictionEquivalence
            (D := D)).functor.map
          ((restrictionEquivalence
            (D := D)).inverse.map φ) ≫
        (restrictionEquivalence
          (D := D)).counitIso.hom.app A =
      (restrictionEquivalence
          (D := D)).counitIso.hom.app
            ((restrictionEquivalence
              (D := D)).functor.obj W) ≫ φ := by
    simpa only [Functor.comp_map, Functor.id_map,
      Functor.id_obj] using
      (restrictionEquivalence
        (D := D)).counitIso.hom.naturality φ
  have htriangle :
      (restrictionEquivalence
            (D := D)).functor.map
          ((restrictionEquivalence
            (D := D)).unitIso.hom.app W) ≫
        (restrictionEquivalence
          (D := D)).counitIso.hom.app
            ((restrictionEquivalence
              (D := D)).functor.obj W) =
      𝟙 ((restrictionEquivalence
        (D := D)).functor.obj W) :=
    (restrictionEquivalence
      (D := D)).functor_unitIso_comp W
  calc
    _ =
        (restrictionEquivalence
            (D := D)).functor.map
              ((restrictionEquivalence
                (D := D)).unitIso.hom.app W) ≫
          ((restrictionEquivalence
              (D := D)).functor.map
                ((restrictionEquivalence
                  (D := D)).inverse.map φ) ≫
            (restrictionEquivalence
              (D := D)).counitIso.hom.app A) := by
      rw [Functor.map_comp, Category.assoc]
    _ =
        (restrictionEquivalence
            (D := D)).functor.map
              ((restrictionEquivalence
                (D := D)).unitIso.hom.app W) ≫
          ((restrictionEquivalence
              (D := D)).counitIso.hom.app
                ((restrictionEquivalence
                  (D := D)).functor.obj W) ≫ φ) := by
      exact congrArg
        (fun q =>
          (restrictionEquivalence
              (D := D)).functor.map
                ((restrictionEquivalence
                  (D := D)).unitIso.hom.app W) ≫ q)
        hnat
    _ =
        ((restrictionEquivalence
            (D := D)).functor.map
              ((restrictionEquivalence
                (D := D)).unitIso.hom.app W) ≫
            (restrictionEquivalence
              (D := D)).counitIso.hom.app
                ((restrictionEquivalence
                  (D := D)).functor.obj W)) ≫ φ :=
      (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ φ := by
      exact congrArg (fun q => q ≫ φ) htriangle
    _ = φ := Category.id_comp _

/--
The restricted global scalar-twist map, followed by the canonical
restriction comparison, is the original descent scalar morphism.
-/
theorem scalarTwistGluedNatTrans_restriction
    (W : D.glued.Modules) :
    (restrictionFunctor (D := D)).map
          ((scalarTwistGluedNatTrans
            a hself hcocycle b hb).app W) ≫
        (scalarTwistGluedRestrictionIso
          a hself hcocycle W).hom =
      scalarTwistHom
        a hself hcocycle b hb
        ((restrictionFunctor (D := D)).obj W) := by
  rw [scalarTwistGluedNatTrans_app,
    scalarTwistGluedHom_eq]
  unfold glueScalarTwistMap
  unfold scalarTwistGluedRestrictionIso
  exact
    restrictionEquivalence_unit_glueMap
      W
      (scalarTwistHom
        a hself hcocycle b hb
        ((restrictionFunctor (D := D)).obj W))

/-- Componentwise form of
`scalarTwistGluedNatTrans_restriction`. -/
theorem scalarTwistGluedNatTrans_restriction_app
    (W : D.glued.Modules) (i : D.J) :
    ((restrictionFunctor (D := D)).map
          ((scalarTwistGluedNatTrans
            a hself hcocycle b hb).app W)).app i ≫
        (scalarTwistGluedRestrictionIso
          a hself hcocycle W).hom.app i =
      scalarEndomorphism
        (((restrictionFunctor (D := D)).obj W).chart i)
        (b i) := by
  have h :=
    congrArg
      (fun φ => φ.app i)
      (scalarTwistGluedNatTrans_restriction
        a hself hcocycle b hb W)
  simpa only [comp_app, scalarTwistHom_app,
    Functor.id_obj] using h

/--
If one selected chart function is one, then the global scalar-twist
natural map becomes an isomorphism after restriction to that chart.
-/
theorem isIso_scalarTwistGluedNatTrans_restrict_of_eq_one
    (W : D.glued.Modules) (i : D.J)
    (hi : b i = 1) :
    IsIso
      ((pullback (D.ι i)).map
        ((scalarTwistGluedNatTrans
          a hself hcocycle b hb).app W)) := by
  let q :
      (pullback (D.ι i)).obj
          ((scalarTwistGluedEquivalence
            a hself hcocycle).functor.obj W) ⟶
        (pullback (D.ι i)).obj W :=
    (scalarTwistGluedRestrictionIso
      a hself hcocycle W).hom.app i
  letI : IsIso q := by
    exact
      (isoApp
        (scalarTwistGluedRestrictionIso
          a hself hcocycle W) i).isIso_hom
  have hcomp :
      (pullback (D.ι i)).map
            ((scalarTwistGluedNatTrans
              a hself hcocycle b hb).app W) ≫ q =
        𝟙 ((pullback (D.ι i)).obj W) := by
    change
      ((restrictionFunctor (D := D)).map
            ((scalarTwistGluedNatTrans
              a hself hcocycle b hb).app W)).app i ≫
          (scalarTwistGluedRestrictionIso
            a hself hcocycle W).hom.app i =
        𝟙 (((restrictionFunctor
          (D := D)).obj W).chart i)
    rw [scalarTwistGluedNatTrans_restriction_app,
      hi, scalarEndomorphism_one]
  haveI :
      IsIso
        ((pullback (D.ι i)).map
              ((scalarTwistGluedNatTrans
                a hself hcocycle b hb).app W) ≫ q) := by
    rw [hcomp]
    exact (Iso.refl _).isIso_hom
  exact IsIso.of_isIso_comp_right _ q

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
