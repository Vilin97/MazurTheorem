/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafResolution
import Mathlib.Topology.Sheaves.Abelian

/-!
# Exact pullback for sheaves of modules on topological spaces

For a continuous map, inverse image of sheaves of modules is exact.
The key point is the canonical identification of the stalk of a
pullback with the stalk at the image point.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

variable {R : Type u} [CommRing R]
variable {X Y : TopCat.{u}}

namespace Presheaf

/-- The map from the stalk of a direct image to the original stalk is
natural in the presheaf. -/
lemma stalkPushforward_naturality
    (f : X ⟶ Y)
    {F G : X.Presheaf (ModuleCat.{u} R)}
    (α : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) (f x)).map
          ((TopCat.Presheaf.pushforward
            (ModuleCat.{u} R) f).map α) ≫
      TopCat.Presheaf.stalkPushforward
        (ModuleCat.{u} R) f G x =
    TopCat.Presheaf.stalkPushforward
        (ModuleCat.{u} R) f F x ≫
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map α := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  erw [← Category.assoc]
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  erw [Category.assoc]
  erw [TopCat.Presheaf.stalkPushforward_germ]
  erw [TopCat.Presheaf.stalkPushforward_germ_assoc]
  erw [TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- Naturality of the presheaf-level stalk pullback isomorphism. -/
@[reassoc]
lemma presheafStalkPullbackIso_hom_naturality
    (f : X ⟶ Y)
    {F G : Y.Presheaf (ModuleCat.{u} R)}
    (α : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkPullbackIso
        (ModuleCat.{u} R) f F x).hom ≫
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
        ((TopCat.Presheaf.pullback
          (ModuleCat.{u} R) f).map α) =
    (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) (f x)).map α ≫
      (TopCat.Presheaf.stalkPullbackIso
        (ModuleCat.{u} R) f G x).hom := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  erw [Category.assoc,
    TopCat.Presheaf.germ_stalkPullbackHom_assoc]
  erw [TopCat.Presheaf.stalkFunctor_map_germ]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
  change _ =
    α.app (Opposite.op U) ≫
      (G.germ U (f x) hxU ≫
        TopCat.Presheaf.stalkPullbackHom
          (ModuleCat.{u} R) f G x)
  rw [TopCat.Presheaf.germ_stalkPullbackHom]
  change
    (((TopCat.Presheaf.pullbackPushforwardAdjunction
        (ModuleCat.{u} R) f).unit.app F).app
          (Opposite.op U) ≫
        ((TopCat.Presheaf.pullback
          (ModuleCat.{u} R) f).map α).app
            (Opposite.op ((Opens.map f).obj U))) ≫
      ((TopCat.Presheaf.pullback
        (ModuleCat.{u} R) f).obj G).germ
          ((Opens.map f).obj U) x hxU =
    (α.app (Opposite.op U) ≫
        ((TopCat.Presheaf.pullbackPushforwardAdjunction
          (ModuleCat.{u} R) f).unit.app G).app
            (Opposite.op U)) ≫
      ((TopCat.Presheaf.pullback
        (ModuleCat.{u} R) f).obj G).germ
          ((Opens.map f).obj U) x hxU
  exact congrArg
    (fun t =>
      t ≫
        ((TopCat.Presheaf.pullback
          (ModuleCat.{u} R) f).obj G).germ
            ((Opens.map f).obj U) x hxU)
    (congrArg
      (fun t => t.app (Opposite.op U))
      ((TopCat.Presheaf.pullbackPushforwardAdjunction
        (ModuleCat.{u} R) f).unit.naturality α)).symm

/-- Sheafification does not change the stalk of the presheaf pullback. -/
noncomputable def pullbackSheafificationStalkIso
    (f : X ⟶ Y) (F : Y.Sheaf (ModuleCat.{u} R)) (x : X) :
    ((TopCat.Presheaf.pullback
      (ModuleCat.{u} R) f).obj F.presheaf).stalk x ≅
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).obj
          (CategoryTheory.sheafify
            (_root_.Opens.grothendieckTopology X)
            ((TopCat.Presheaf.pullback
              (ModuleCat.{u} R) f).obj F.presheaf)) := by
  let P :=
    (TopCat.Presheaf.pullback
      (ModuleCat.{u} R) f).obj F.presheaf
  let ηP :=
    CategoryTheory.toSheafify
      (_root_.Opens.grothendieckTopology X) P
  let hη :
      IsIso
        ((TopCat.Presheaf.stalkFunctor
          (ModuleCat.{u} R) x).map ηP) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x (ModuleCat.{u} R) P
  exact
    @asIso _ _ _ _
      ((TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map ηP) hη

/-- The chosen sheaf-pullback construction is identified with the
sheafification of the presheaf pullback on stalks. -/
noncomputable def pullbackConstructionStalkIso
    (f : X ⟶ Y) (F : Y.Sheaf (ModuleCat.{u} R)) (x : X) :
    (TopCat.Presheaf.stalkFunctor
      (ModuleCat.{u} R) x).obj
        (CategoryTheory.sheafify
          (_root_.Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback
            (ModuleCat.{u} R) f).obj F.presheaf)) ≅
      ((TopCat.Sheaf.pullback
        (ModuleCat.{u} R) f).obj F).presheaf.stalk x := by
  let e :=
    (TopCat.Sheaf.pullbackIso
      (ModuleCat.{u} R) f).inv.app F
  letI : IsIso e := inferInstance
  let heHom : IsIso e.hom :=
    Functor.map_isIso
      (TopCat.Sheaf.forget (ModuleCat.{u} R) X) e
  let he :
      IsIso
        ((TopCat.Presheaf.stalkFunctor
          (ModuleCat.{u} R) x).map e.hom) :=
    letI : IsIso e.hom := heHom
    Functor.map_isIso
        (TopCat.Presheaf.stalkFunctor
          (ModuleCat.{u} R) x) e.hom
  exact
    @asIso _ _ _ _
      ((TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map e.hom) he

/-- The stalk of a sheaf pullback is canonically the stalk at the
image point. -/
noncomputable def sheafStalkPullbackIso
    (f : X ⟶ Y) (F : Y.Sheaf (ModuleCat.{u} R)) (x : X) :
    F.presheaf.stalk (f x) ≅
      ((TopCat.Sheaf.pullback
        (ModuleCat.{u} R) f).obj F).presheaf.stalk x :=
  TopCat.Presheaf.stalkPullbackIso
      (ModuleCat.{u} R) f F.presheaf x ≪≫
    pullbackSheafificationStalkIso f F x ≪≫
    pullbackConstructionStalkIso f F x

/-- Naturality of the sheafification part of the pullback stalk
isomorphism. -/
@[reassoc]
lemma pullbackSheafificationStalkIso_hom_naturality
    (f : X ⟶ Y)
    {F G : Y.Sheaf (ModuleCat.{u} R)}
    (α : F ⟶ G) (x : X) :
    (pullbackSheafificationStalkIso f F x).hom ≫
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
        (CategoryTheory.sheafifyMap
          (_root_.Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback
            (ModuleCat.{u} R) f).map α.hom)) =
    (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
        ((TopCat.Presheaf.pullback
          (ModuleCat.{u} R) f).map α.hom) ≫
      (pullbackSheafificationStalkIso f G x).hom := by
  change
    (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
          (CategoryTheory.toSheafify
            (_root_.Opens.grothendieckTopology X)
            ((TopCat.Presheaf.pullback
              (ModuleCat.{u} R) f).obj F.presheaf)) ≫
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
          (CategoryTheory.sheafifyMap
            (_root_.Opens.grothendieckTopology X)
            ((TopCat.Presheaf.pullback
              (ModuleCat.{u} R) f).map α.hom)) =
    (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
          ((TopCat.Presheaf.pullback
            (ModuleCat.{u} R) f).map α.hom) ≫
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
          (CategoryTheory.toSheafify
            (_root_.Opens.grothendieckTopology X)
            ((TopCat.Presheaf.pullback
              (ModuleCat.{u} R) f).obj G.presheaf))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (TopCat.Presheaf.stalkFunctor
      (ModuleCat.{u} R) x).map
    (CategoryTheory.toSheafify_naturality
      (_root_.Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback
        (ModuleCat.{u} R) f).map α.hom)).symm

/-- Naturality of the comparison between the two constructions of
sheaf pullback. -/
@[reassoc]
lemma pullbackConstructionStalkIso_hom_naturality
    (f : X ⟶ Y)
    {F G : Y.Sheaf (ModuleCat.{u} R)}
    (α : F ⟶ G) (x : X) :
    (pullbackConstructionStalkIso f F x).hom ≫
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
        ((TopCat.Sheaf.pullback
          (ModuleCat.{u} R) f).map α).hom =
    (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
        (CategoryTheory.sheafifyMap
          (_root_.Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback
            (ModuleCat.{u} R) f).map α.hom)) ≫
      (pullbackConstructionStalkIso f G x).hom := by
  let St := TopCat.Presheaf.stalkFunctor
    (ModuleCat.{u} R) x
  let PF := CategoryTheory.sheafify
    (_root_.Opens.grothendieckTopology X)
    ((TopCat.Presheaf.pullback
      (ModuleCat.{u} R) f).obj F.presheaf)
  let PG := CategoryTheory.sheafify
    (_root_.Opens.grothendieckTopology X)
    ((TopCat.Presheaf.pullback
      (ModuleCat.{u} R) f).obj G.presheaf)
  let QF := ((TopCat.Sheaf.pullback
    (ModuleCat.{u} R) f).obj F).presheaf
  let QG := ((TopCat.Sheaf.pullback
    (ModuleCat.{u} R) f).obj G).presheaf
  let eF : PF ⟶ QF :=
    ((TopCat.Sheaf.pullbackIso
      (ModuleCat.{u} R) f).inv.app F).hom
  let eG : PG ⟶ QG :=
    ((TopCat.Sheaf.pullbackIso
      (ModuleCat.{u} R) f).inv.app G).hom
  let β : PF ⟶ PG :=
    CategoryTheory.sheafifyMap
      (_root_.Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback
        (ModuleCat.{u} R) f).map α.hom)
  let γ : QF ⟶ QG :=
    ((TopCat.Sheaf.pullback
      (ModuleCat.{u} R) f).map α).hom
  have hnat : eF ≫ γ = β ≫ eG :=
    congrArg (fun t => t.hom)
      ((TopCat.Sheaf.pullbackIso
        (ModuleCat.{u} R) f).inv.naturality α).symm
  change St.map eF ≫ St.map γ =
    St.map β ≫ St.map eG
  calc
    St.map eF ≫ St.map γ = St.map (eF ≫ γ) :=
      (St.map_comp eF γ).symm
    _ = St.map (β ≫ eG) := congrArg St.map hnat
    _ = St.map β ≫ St.map eG := St.map_comp β eG

/-- Naturality of the canonical stalk isomorphism for pullback. -/
lemma stalkPullbackIso_hom_naturality
    (f : X ⟶ Y)
    {F G : Y.Sheaf (ModuleCat.{u} R)}
    (α : F ⟶ G) (x : X) :
    (sheafStalkPullbackIso f F x).hom ≫
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) x).map
        ((TopCat.Sheaf.pullback (ModuleCat.{u} R) f).map α).hom =
      (TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) (f x)).map α.hom ≫
        (sheafStalkPullbackIso f G x).hom := by
  let pF := (TopCat.Presheaf.stalkPullbackIso
    (ModuleCat.{u} R) f F.presheaf x).hom
  let pG := (TopCat.Presheaf.stalkPullbackIso
    (ModuleCat.{u} R) f G.presheaf x).hom
  let sF := (pullbackSheafificationStalkIso f F x).hom
  let sG := (pullbackSheafificationStalkIso f G x).hom
  let cF := (pullbackConstructionStalkIso f F x).hom
  let cG := (pullbackConstructionStalkIso f G x).hom
  let a := (TopCat.Presheaf.stalkFunctor
    (ModuleCat.{u} R) (f x)).map α.hom
  let b := (TopCat.Presheaf.stalkFunctor
    (ModuleCat.{u} R) x).map
      ((TopCat.Sheaf.pullback (ModuleCat.{u} R) f).map α).hom
  let δ := (TopCat.Presheaf.stalkFunctor
    (ModuleCat.{u} R) x).map
      ((TopCat.Presheaf.pullback
        (ModuleCat.{u} R) f).map α.hom)
  let γ := (TopCat.Presheaf.stalkFunctor
    (ModuleCat.{u} R) x).map
      (CategoryTheory.sheafifyMap
        (_root_.Opens.grothendieckTopology X)
        ((TopCat.Presheaf.pullback
          (ModuleCat.{u} R) f).map α.hom))
  have hc : cF ≫ b = γ ≫ cG :=
    pullbackConstructionStalkIso_hom_naturality f α x
  have hs : sF ≫ γ = δ ≫ sG :=
    pullbackSheafificationStalkIso_hom_naturality f α x
  have hp : pF ≫ δ = a ≫ pG :=
    presheafStalkPullbackIso_hom_naturality f α.hom x
  change (pF ≫ sF ≫ cF) ≫ b =
    a ≫ (pG ≫ sG ≫ cG)
  have h₁ : (pF ≫ sF ≫ cF) ≫ b =
      (pF ≫ sF) ≫ (cF ≫ b) :=
    Category.assoc _ _ _
  have h₂ : (pF ≫ sF) ≫ (cF ≫ b) =
      (pF ≫ sF) ≫ (γ ≫ cG) :=
    congrArg (fun z => (pF ≫ sF) ≫ z) hc
  have h₃ : (pF ≫ sF) ≫ (γ ≫ cG) =
      ((pF ≫ sF) ≫ γ) ≫ cG :=
    (Category.assoc _ _ _).symm
  have h₄ : ((pF ≫ sF) ≫ γ) ≫ cG =
      (pF ≫ (sF ≫ γ)) ≫ cG :=
    congrArg (fun z => z ≫ cG) (Category.assoc _ _ _)
  have h₅ : (pF ≫ (sF ≫ γ)) ≫ cG =
      (pF ≫ (δ ≫ sG)) ≫ cG :=
    congrArg (fun z => (pF ≫ z) ≫ cG) hs
  have h₆ : (pF ≫ (δ ≫ sG)) ≫ cG =
      ((pF ≫ δ) ≫ sG) ≫ cG :=
    congrArg (fun z => z ≫ cG) (Category.assoc _ _ _).symm
  have h₇ : ((pF ≫ δ) ≫ sG) ≫ cG =
      ((a ≫ pG) ≫ sG) ≫ cG :=
    congrArg (fun z => (z ≫ sG) ≫ cG) hp
  have h₈ : ((a ≫ pG) ≫ sG) ≫ cG =
      (a ≫ (pG ≫ sG)) ≫ cG :=
    congrArg (fun z => z ≫ cG) (Category.assoc _ _ _)
  have h₉ : (a ≫ (pG ≫ sG)) ≫ cG =
      a ≫ (pG ≫ sG ≫ cG) :=
    Category.assoc _ _ _
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans
    (h₅.trans (h₆.trans (h₇.trans (h₈.trans h₉)))))))

end Presheaf

/-- Pullback of sheaves of modules preserves monomorphisms. -/
noncomputable instance pullback_preservesMonomorphisms
    (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback
      (ModuleCat.{u} R) f).PreservesMonomorphisms where
  preserves {F G} α hα := by
    letI : Mono α := hα
    letI :
        ∀ x : X,
          Mono
            ((TopCat.Presheaf.stalkFunctor
              (ModuleCat.{u} R) x).map
                ((TopCat.Sheaf.pullback
                  (ModuleCat.{u} R) f).map α).hom) :=
      fun x => by
        haveI :
            Mono
              ((TopCat.Presheaf.stalkFunctor
                (ModuleCat.{u} R) (f x)).map α.hom) := by
          exact Functor.map_mono
            (TopCat.Sheaf.forget (ModuleCat.{u} R) Y ⋙
              TopCat.Presheaf.stalkFunctor
                (ModuleCat.{u} R) (f x)) α
        let eF :=
          (Presheaf.sheafStalkPullbackIso f F x).hom
        let eG :=
          (Presheaf.sheafStalkPullbackIso f G x).hom
        let a :=
          (TopCat.Presheaf.stalkFunctor
            (ModuleCat.{u} R) (f x)).map α.hom
        let b :=
          (TopCat.Presheaf.stalkFunctor
            (ModuleCat.{u} R) x).map
              ((TopCat.Sheaf.pullback
                (ModuleCat.{u} R) f).map α).hom
        have hnat : eF ≫ b = a ≫ eG :=
          Presheaf.stalkPullbackIso_hom_naturality
            f α x
        haveI : IsIso eF := by
          dsimp only [eF]
          infer_instance
        haveI : IsIso eG := by
          dsimp only [eG]
          infer_instance
        have monoEG : Mono eG := by
          dsimp only [eG]
          infer_instance
        have monoA : Mono a := by
          dsimp only [a]
          infer_instance
        have monoAEG : Mono (a ≫ eG) :=
          mono_comp' monoA monoEG
        have hcomp : Mono (eF ≫ b) :=
          hnat.symm ▸
            monoAEG
        exact
          (mono_comp_iff_of_isIso eF b).mp hcomp
    exact
      TopCat.Presheaf.mono_of_stalk_mono
        ((TopCat.Sheaf.pullback
          (ModuleCat.{u} R) f).map α)

/-- Pullback of sheaves of modules preserves injectivity-detecting
monomorphisms, hence its right adjoint preserves injective objects. -/
noncomputable instance pushforward_preservesInjectiveObjects
    (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward
      (ModuleCat.{u} R) f).PreservesInjectiveObjects := by
  exact
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (TopCat.Sheaf.pullbackPushforwardAdjunction
        (ModuleCat.{u} R) f)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat
