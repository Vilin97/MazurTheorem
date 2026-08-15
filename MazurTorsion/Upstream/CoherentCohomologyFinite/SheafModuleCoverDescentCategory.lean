/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCocycle
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentMorphism

/-!
# The category of module descent data on a scheme cover

An object consists of a module on every chart, transition isomorphisms on
pairwise overlaps, and the identity and cocycle laws.  Morphisms are
chartwise maps commuting with the transitions.  Effective descent then
defines a functor from this category to modules on the glued scheme.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{0})

/-- A family of overlap transitions for chartwise modules. -/
abbrev CoverTransition
    (M : ∀ i, (D.U i).Modules) :=
  ∀ i j,
    (pullback (D.f i j)).obj (M i) ≅
      (pullback (D.t i j ≫ D.f j i)).obj (M j)

/-- The diagonal identity law for a family of cover transitions. -/
abbrev CoverTransition.IsIdentity
    {M : ∀ i, (D.U i).Modules}
    (g : CoverTransition D M) : Prop :=
  ∀ i, g i i =
    eqToIso (congrArg
      (fun f => (pullback f).obj (M i))
      (show D.f i i = D.t i i ≫ D.f i i by
        rw [D.t_id i, Category.id_comp]))

/-- The triple-overlap cocycle law for a family of cover transitions. -/
abbrev CoverTransition.IsCocycle
    {M : ∀ i, (D.U i).Modules}
    (g : CoverTransition D M) : Prop :=
  ∀ i j k,
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
      (pullbackCongr
        (glueData_bridge_mid D i j k)).app (M j) ≪≫
      pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
      (pullbackCongr
        (glueData_bridge_tgt D i j k)).app (M k) =
    (pullbackCongr
      (glueData_bridge_src D i j k)).app (M i) ≪≫
      pullbackBaseChangeTransport
        (pullback.snd (D.f i j) (D.f i k))
        (D.f i k) (D.t i k ≫ D.f k i) (g i k)

/-- Module descent data on the charts of a scheme glue datum. -/
structure CoverDescentData where
  /-- The module on each chart. -/
  chart : ∀ i, (D.U i).Modules
  /-- The transition isomorphisms on pairwise overlaps. -/
  transition : CoverTransition D chart
  /-- The diagonal transitions are identities. -/
  identity : transition.IsIdentity D
  /-- The transitions satisfy the triple-overlap cocycle. -/
  cocycle : transition.IsCocycle D

namespace CoverDescentData

variable {D}

/-- A morphism of cover descent data is a compatible family of chart maps. -/
structure Hom (A B : CoverDescentData D) where
  /-- The map on each chart. -/
  app : ∀ i, A.chart i ⟶ B.chart i
  /-- The chart maps commute with every overlap transition. -/
  compatible :
    DescentMorphismCompatible
      D A.chart B.chart A.transition B.transition app

@[ext]
lemma Hom.ext {A B : CoverDescentData D}
    {f g : Hom A B} (h : ∀ i, f.app i = g.app i) :
    f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      subst g
      rfl

/-- Identity morphism of cover descent data. -/
def id (A : CoverDescentData D) : Hom A A where
  app i := 𝟙 (A.chart i)
  compatible :=
    descentMorphismCompatible_id
      D A.chart A.transition

/-- Composition of morphisms of cover descent data. -/
def comp {A B C : CoverDescentData D}
    (f : Hom A B) (g : Hom B C) : Hom A C where
  app i := f.app i ≫ g.app i
  compatible :=
    DescentMorphismCompatible.comp
      D A.chart B.chart A.transition B.transition
      f.compatible g.compatible

instance : Category (CoverDescentData D) where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := by
    apply Hom.ext
    intro i
    exact Category.id_comp (f.app i)
  comp_id f := by
    apply Hom.ext
    intro i
    exact Category.comp_id (f.app i)
  assoc f g h := by
    apply Hom.ext
    intro i
    exact Category.assoc (f.app i) (g.app i) (h.app i)

@[simp]
lemma id_app (A : CoverDescentData D) (i : D.J) :
    (𝟙 A : A ⟶ A).app i = 𝟙 (A.chart i) :=
  rfl

@[simp]
lemma comp_app {A B C : CoverDescentData D}
    (f : A ⟶ B) (g : B ⟶ C) (i : D.J) :
    (f ≫ g).app i = f.app i ≫ g.app i :=
  rfl

/-- Glue a cover descent datum to a module on the glued scheme. -/
noncomputable def glueFunctor :
    CoverDescentData D ⥤ D.glued.Modules where
  obj A :=
    glue D A.chart A.transition A.identity A.cocycle
  map {A B} f :=
    DescentMorphism.glueMap
      D A.chart B.chart A.transition B.transition
      A.identity B.identity A.cocycle B.cocycle
      f.app f.compatible
  map_id A :=
    DescentMorphism.glueMap_id
      D A.chart A.transition A.identity A.cocycle
      (descentMorphismCompatible_id
        D A.chart A.transition)
  map_comp {A B C} f g :=
    (DescentMorphism.glueMap_comp
      D A.chart B.chart A.transition B.transition
      A.identity B.identity A.cocycle B.cocycle
      f.app f.compatible
      C.transition C.identity C.cocycle
      g.app g.compatible).symm

/-- Restrict a global module to its canonical cover descent datum. -/
noncomputable def restrictionFunctor :
    D.glued.Modules ⥤ CoverDescentData D where
  obj W :=
    { chart := coverRestriction D W
      transition := coverRestrictionTransition D W
      identity := coverRestrictionTransition_self D W
      cocycle := coverRestrictionTransition_cocycle D W }
  map {W Z} φ :=
    { app := fun i => (pullback (D.ι i)).map φ
      compatible := fun i j =>
        coverRestrictionTransition_naturality D φ i j }
  map_id W := by
    apply Hom.ext
    intro i
    exact (pullback (D.ι i)).map_id W
  map_comp {W Z T} φ ψ := by
    apply Hom.ext
    intro i
    exact (pullback (D.ι i)).map_comp φ ψ

end CoverDescentData

end AlgebraicGeometry.Scheme.Modules
