/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCategory
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentReconstruction

/-!
# Effective cover descent as an equivalence of categories

Restriction sends a module on a glued scheme to its canonical chartwise
descent datum, and gluing sends a descent datum back to a global module.
The reconstruction morphism and the effective-descent restriction
isomorphisms form the unit and counit of an equivalence.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{0})

namespace CoverDescentData

variable {D}

/-- A morphism of descent data with invertible chart components has a
compatible chartwise inverse. -/
noncomputable def Hom.inverseOfComponents
    {A B : CoverDescentData D} (f : A ⟶ B)
    [∀ i, IsIso (f.app i)] :
    B ⟶ A where
  app i := inv (f.app i)
  compatible := by
    intro i j
    apply
      (cancel_epi
        ((pullback (D.f i j)).map (f.app i))).1
    rw [← Category.assoc,
      ← (pullback (D.f i j)).map_comp,
      IsIso.hom_inv_id,
      (pullback (D.f i j)).map_id,
      Category.id_comp]
    rw [← Category.assoc, f.compatible i j,
      Category.assoc,
      ← (pullback
        (D.t i j ≫ D.f j i)).map_comp,
      IsIso.hom_inv_id,
      (pullback
        (D.t i j ≫ D.f j i)).map_id,
      Category.comp_id]

/-- A morphism of descent data is an isomorphism when all of its chart
components are isomorphisms. -/
noncomputable def Hom.isoOfComponents
    {A B : CoverDescentData D} (f : A ⟶ B)
    [∀ i, IsIso (f.app i)] :
    A ≅ B where
  hom := f
  inv := f.inverseOfComponents
  hom_inv_id := by
    apply Hom.ext
    intro i
    exact IsIso.hom_inv_id (f.app i)
  inv_hom_id := by
    apply Hom.ext
    intro i
    exact IsIso.inv_hom_id_assoc (f.app i) (𝟙 _)

/-- Glue the canonical chart restrictions of a global morphism.  Naming
this map keeps the dependent descent parameters out of later naturality
statements. -/
noncomputable def coverRestrictionGlueMap
    {W Z : D.glued.Modules} (φ : W ⟶ Z) :
    glue D
        (coverRestriction D W)
        (coverRestrictionTransition D W)
        (coverRestrictionTransition_self D W)
        (coverRestrictionTransition_cocycle D W) ⟶
      glue D
        (coverRestriction D Z)
        (coverRestrictionTransition D Z)
        (coverRestrictionTransition_self D Z)
        (coverRestrictionTransition_cocycle D Z) :=
  DescentMorphism.glueMap
    D
    (coverRestriction D W)
    (coverRestriction D Z)
    (coverRestrictionTransition D W)
    (coverRestrictionTransition D Z)
    (coverRestrictionTransition_self D W)
    (coverRestrictionTransition_self D Z)
    (coverRestrictionTransition_cocycle D W)
    (coverRestrictionTransition_cocycle D Z)
    (fun i => (pullback (D.ι i)).map φ)
    (fun i j =>
      coverRestrictionTransition_naturality
        D φ i j)

/-- On every chart, the glued restriction of a global morphism is the
original pullback morphism. -/
theorem pullback_map_coverRestrictionGlueMap
    {W Z : D.glued.Modules} (φ : W ⟶ Z) (i : D.J) :
    (pullback (D.ι i)).map
          (coverRestrictionGlueMap (D := D) φ) ≫
        glueRestrictionHom D
          (coverRestriction D Z)
          (coverRestrictionTransition D Z)
          (coverRestrictionTransition_self D Z)
          (coverRestrictionTransition_cocycle D Z) i =
      glueRestrictionHom D
          (coverRestriction D W)
          (coverRestrictionTransition D W)
          (coverRestrictionTransition_self D W)
          (coverRestrictionTransition_cocycle D W) i ≫
        (pullback (D.ι i)).map φ := by
  unfold coverRestrictionGlueMap
  exact DescentMorphism.pullback_map_glueMap
    D
    (coverRestriction D W)
    (coverRestriction D Z)
    (coverRestrictionTransition D W)
    (coverRestrictionTransition D Z)
    (coverRestrictionTransition_self D W)
    (coverRestrictionTransition_self D Z)
    (coverRestrictionTransition_cocycle D W)
    (coverRestrictionTransition_cocycle D Z)
    (fun i => (pullback (D.ι i)).map φ)
    (fun i j => coverRestrictionTransition_naturality D φ i j)
    i

/-- The canonical reconstruction morphism is natural in the global
module. -/
theorem coverRestrictionGlueUnit_naturality
    {W Z : D.glued.Modules} (φ : W ⟶ Z) :
    φ ≫ coverRestrictionGlueUnit D Z =
      coverRestrictionGlueUnit D W ≫
        coverRestrictionGlueMap (D := D) φ := by
  apply pullback_map_jointly_faithful D
  intro i
  let rW :=
    glueRestrictionHom D
      (coverRestriction D W)
      (coverRestrictionTransition D W)
      (coverRestrictionTransition_self D W)
      (coverRestrictionTransition_cocycle D W) i
  let rZ :=
    glueRestrictionHom D
      (coverRestriction D Z)
      (coverRestrictionTransition D Z)
      (coverRestrictionTransition_self D Z)
      (coverRestrictionTransition_cocycle D Z) i
  letI : IsIso rZ :=
    isIso_glueRestrictionHom D
      (coverRestriction D Z)
      (coverRestrictionTransition D Z)
      (coverRestrictionTransition_self D Z)
      (coverRestrictionTransition_cocycle D Z) i
  apply (cancel_mono rZ).1
  calc
    (pullback (D.ι i)).map
          (φ ≫ coverRestrictionGlueUnit D Z) ≫ rZ =
        (pullback (D.ι i)).map φ ≫
          ((pullback (D.ι i)).map
              (coverRestrictionGlueUnit D Z) ≫ rZ) := by
      rw [(pullback (D.ι i)).map_comp]
      exact Category.assoc _ _ _
    _ = (pullback (D.ι i)).map φ := by
      rw [pullback_map_coverRestrictionGlueUnit]
      exact Category.comp_id _
    _ =
        ((pullback (D.ι i)).map
              (coverRestrictionGlueUnit D W) ≫ rW) ≫
          (pullback (D.ι i)).map φ := by
      rw [pullback_map_coverRestrictionGlueUnit]
      exact (Category.id_comp _).symm
    _ =
        (pullback (D.ι i)).map
            (coverRestrictionGlueUnit D W) ≫
          (rW ≫ (pullback (D.ι i)).map φ) :=
      Category.assoc _ _ _
    _ =
        (pullback (D.ι i)).map
              (coverRestrictionGlueUnit D W) ≫
          ((pullback (D.ι i)).map
              (coverRestrictionGlueMap
                (D := D) φ) ≫ rZ) := by
      rw [pullback_map_coverRestrictionGlueMap]
    _ =
        (pullback (D.ι i)).map
            (coverRestrictionGlueUnit D W) ≫
          (pullback (D.ι i)).map
              (coverRestrictionGlueMap
                (D := D) φ) ≫ rZ :=
      (Category.assoc _ _ _).symm
    _ =
        (pullback (D.ι i)).map
            (coverRestrictionGlueUnit D W ≫
              coverRestrictionGlueMap
                (D := D) φ) ≫ rZ := by
      rw [(pullback (D.ι i)).map_comp]
      exact (Category.assoc _ _ _).symm

/-- Restriction followed by gluing is naturally isomorphic to the
identity on global modules. -/
noncomputable def restrictionGlueIso :
    𝟭 D.glued.Modules ≅
      restrictionFunctor (D := D) ⋙
        glueFunctor (D := D) :=
  NatIso.ofComponents
    (fun W => coverRestrictionGlueIso D W)
    (fun {W Z} φ => by
      change
        φ ≫ coverRestrictionGlueUnit D Z =
          coverRestrictionGlueUnit D W ≫
            coverRestrictionGlueMap
              (D := D) φ
      exact
        coverRestrictionGlueUnit_naturality
          (D := D) φ)

/-- The effective-descent restriction maps form a morphism from the
canonical descent datum of the glued module to the original datum. -/
noncomputable def glueRestrictionDescentHom
    (A : CoverDescentData D) :
    (glueFunctor (D := D) ⋙
      restrictionFunctor (D := D)).obj A ⟶ A where
  app i :=
    glueRestrictionHom D
      A.chart A.transition A.identity A.cocycle i
  compatible := by
    intro i j
    change
      (pullback (D.f i j)).map
            (glueRestrictionHom D
              A.chart A.transition A.identity A.cocycle i) ≫
          (A.transition i j).hom =
        (coverRestrictionTransition D
              ((glueFunctor (D := D)).obj A) i j).hom ≫
          (pullback
            (D.t i j ≫ D.f j i)).map
              (glueRestrictionHom D
                A.chart A.transition A.identity A.cocycle j)
    let P :=
      (pullbackComp (D.f i j) (D.ι i)).app
        ((glueFunctor (D := D)).obj A)
    let Q :=
      (pullbackComp
        (D.t i j ≫ D.f j i) (D.ι j)).app
          ((glueFunctor (D := D)).obj A)
    let C :=
      (pullbackCongr
        (show
          (D.t i j ≫ D.f j i) ≫ D.ι j =
            D.f i j ≫ D.ι i by
          rw [Category.assoc]
          exact D.glue_condition i j)).app
            ((glueFunctor (D := D)).obj A)
    have hc :=
      glueRestriction_overlap_compat D
        A.chart A.transition A.identity A.cocycle i j
    have hleft :
        (pullback (D.f i j)).map
            (glueRestrictionHom D
              A.chart A.transition A.identity A.cocycle i) =
          P.hom ≫ C.inv ≫ Q.inv ≫
            (pullback
              (D.t i j ≫ D.f j i)).map
                (glueRestrictionHom D
                  A.chart A.transition A.identity A.cocycle j) ≫
            (A.transition i j).inv := by
      exact (Iso.inv_comp_eq P).mp hc
    have hcanonical :
        coverRestrictionTransition D
            ((glueFunctor (D := D)).obj A) i j =
          P ≪≫ C.symm ≪≫ Q.symm := by
      rfl
    rw [hleft, hcanonical]
    have hcancel :
        ∀ {X₀ X₁ X₂ X₃ X₄ X₅ :
              (D.V (i, j)).Modules}
          (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
          (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
          (e : X₅ ≅ X₄),
          (a ≫ b ≫ c ≫ d ≫ e.inv) ≫ e.hom =
            (a ≫ b ≫ c) ≫ d := by
      intros
      simp
    exact
      hcancel P.hom C.inv Q.inv
        ((pullback
          (D.t i j ≫ D.f j i)).map
            (glueRestrictionHom D
              A.chart A.transition
              A.identity A.cocycle j))
        (A.transition i j)

/-- Gluing followed by restriction is naturally isomorphic to the
identity on cover descent data. -/
noncomputable def descentGlueRestrictionIso
    (A : CoverDescentData D) :
    (glueFunctor (D := D) ⋙
      restrictionFunctor (D := D)).obj A ≅ A := by
  let h :=
    glueRestrictionDescentHom (D := D) A
  letI : ∀ i, IsIso (h.app i) :=
    fun i =>
      isIso_glueRestrictionHom D
        A.chart A.transition A.identity A.cocycle i
  exact h.isoOfComponents

/-- Naturality of the effective-descent counit. -/
theorem descentGlueRestrictionIso_naturality
    {A B : CoverDescentData D} (φ : A ⟶ B) :
    (glueFunctor (D := D) ⋙
        restrictionFunctor (D := D)).map φ ≫
        (descentGlueRestrictionIso (D := D) B).hom =
      (descentGlueRestrictionIso (D := D) A).hom ≫ φ := by
  apply Hom.ext
  intro i
  exact
    DescentMorphism.pullback_map_glueMap
      D A.chart B.chart A.transition B.transition
      A.identity B.identity A.cocycle B.cocycle
      φ.app φ.compatible i

/-- The effective-descent counit as a natural isomorphism. -/
noncomputable def glueRestrictionNatIso :
    glueFunctor (D := D) ⋙
        restrictionFunctor (D := D) ≅
      𝟭 (CoverDescentData D) :=
  NatIso.ofComponents
    (descentGlueRestrictionIso (D := D))
    (fun φ =>
      descentGlueRestrictionIso_naturality
        (D := D) φ)

/-- Effective module descent along a scheme glue datum. -/
noncomputable def restrictionEquivalence :
    D.glued.Modules ≌ CoverDescentData D where
  functor := restrictionFunctor (D := D)
  inverse := glueFunctor (D := D)
  unitIso := restrictionGlueIso (D := D)
  counitIso := glueRestrictionNatIso (D := D)
  functor_unitIso_comp W := by
    apply Hom.ext
    intro i
    exact
      pullback_map_coverRestrictionGlueUnit D W i

end CoverDescentData

end AlgebraicGeometry.Scheme.Modules
