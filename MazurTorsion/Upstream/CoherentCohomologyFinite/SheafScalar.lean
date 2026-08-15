/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentObject

/-!
# Scalar automorphisms of the structure sheaf

A global function acts on the structure sheaf by multiplication.  This file
packages that action, its multiplicativity, and its compatibility with
pullback.  These lemmas are the rank-one algebra needed for transition maps
of a line bundle.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

open _root_.AlgebraicGeometry

local instance presheafPushforwardIsRightAdjoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (PresheafOfModules.pushforward.{u}
      f.toRingCatSheafHom.hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward.{u} _

local instance sheafPushforwardIsRightAdjoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (SheafOfModules.pushforward.{u}
      f.toRingCatSheafHom).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    f.toRingCatSheafHom).isRightAdjoint

/-- The global section of the unit module obtained by restricting a global
function to every open set. -/
noncomputable def globalUnitSection {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk
    (fun U => X.ringCatSheaf.obj.map (homOfLE le_top).op a)
    (by
      intro U V f
      change
        X.ringCatSheaf.obj.map f
            (X.ringCatSheaf.obj.map (homOfLE le_top).op a) =
          X.ringCatSheaf.obj.map (homOfLE le_top).op a
      have hm :
          X.ringCatSheaf.obj.map
                (homOfLE (le_top : U.unop ≤ ⊤)).op ≫
              X.ringCatSheaf.obj.map f =
            X.ringCatSheaf.obj.map
              (homOfLE (le_top : V.unop ≤ ⊤)).op := by
        rw [← X.ringCatSheaf.obj.map_comp]
        congr 1
      exact ConcreteCategory.congr_hom hm a)

/-- Multiplication by a global function as an endomorphism of the structure
sheaf, viewed as its own unit module. -/
noncomputable def endomorphism {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm
    (globalUnitSection a)

/-- Evaluation of scalar multiplication on a section. -/
lemma endomorphism_app {X : Scheme.{u}} (a : Γ(X, ⊤))
    (U : X.Opensᵒᵖ) (x : X.ringCatSheaf.obj.obj U) :
    (endomorphism a).val.app U x =
      x * X.ringCatSheaf.obj.map (homOfLE le_top).op a := by
  rfl

/-- Evaluation on the unit section. -/
lemma endomorphism_app_one {X : Scheme.{u}} (a : Γ(X, ⊤))
    (U : X.Opensᵒᵖ) :
    (endomorphism a).val.app U
        (1 : X.ringCatSheaf.obj.obj U) =
      X.ringCatSheaf.obj.map (homOfLE le_top).op a := by
  exact one_smul _ _

/-- The scalar endomorphism corresponds to its defining global section. -/
lemma unitHomEquiv_endomorphism {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
        (endomorphism a) =
      globalUnitSection a := by
  rw [endomorphism, Equiv.apply_symm_apply]

/-- Multiplication by one is the identity. -/
lemma endomorphism_one {X : Scheme.{u}} :
    endomorphism (1 : Γ(X, ⊤)) =
      𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  rw [endomorphism, Equiv.symm_apply_eq]
  ext U
  change X.ringCatSheaf.obj.map (homOfLE le_top).op (1 : Γ(X, ⊤)) =
    (SheafOfModules.Hom.val
      (𝟙 (SheafOfModules.unit X.ringCatSheaf))).app U
        (1 : X.ringCatSheaf.obj.obj U)
  rw [SheafOfModules.id_val, PresheafOfModules.id_app]
  exact map_one _

/-- Composition of scalar endomorphisms is multiplication of functions. -/
lemma endomorphism_comp {X : Scheme.{u}} (a b : Γ(X, ⊤)) :
    endomorphism a ≫ endomorphism b = endomorphism (a * b) := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  change
    SheafOfModules.sectionsMap (endomorphism b)
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
          (endomorphism a)) =
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
        (endomorphism (a * b))
  rw [unitHomEquiv_endomorphism, unitHomEquiv_endomorphism]
  refine PresheafOfModules.sections_ext _ _ (fun U => ?_)
  change
    (endomorphism b).val.app U
        (X.ringCatSheaf.obj.map (homOfLE le_top).op a) =
      X.ringCatSheaf.obj.map (homOfLE le_top).op (a * b)
  rw [endomorphism_app]
  exact
    (RingHom.map_mul
      (X.ringCatSheaf.obj.map (homOfLE le_top).op).hom a b).symm

private lemma pullbackObjUnitToUnit_isIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) [(TopologicalSpace.Opens.map f.base).Final] :
    IsIso (SheafOfModules.pullbackObjUnitToUnit
      f.toRingCatSheafHom) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      f.toRingCatSheafHom).homEquiv _ _).bijective.of_comp_iff',
    ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert!
    (SheafOfModules.bijective_pushforwardSections
      f.toRingCatSheafHom M).comp
      (SheafOfModules.unitHomEquiv _).bijective
  ext g : 1
  dsimp
  erw [SheafOfModules.pushforwardSections_unitHomEquiv,
    EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

private noncomputable def pullbackObjUnitToUnitIso
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [(TopologicalSpace.Opens.map f.base).Final] :
    (Scheme.Modules.pullback f).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  @asIso _ _ _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (pullbackObjUnitToUnit_isIso f)

/-- The canonical comparison between the pullback of the structure sheaf and
the structure sheaf of the source. -/
noncomputable def pullbackUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).obj
        (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  haveI : (TopologicalSpace.Opens.map f.base).Final :=
    final_of_representablyFlat _
  pullbackObjUnitToUnitIso f

@[simp]
lemma pullbackUnitIso_hom {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (pullbackUnitIso f).hom =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  rfl

/-- A unit acts by an automorphism of the structure sheaf. -/
noncomputable def unitIso {X : Scheme.{u}} (a : Γ(X, ⊤)ˣ) :
    SheafOfModules.unit X.ringCatSheaf ≅
      SheafOfModules.unit X.ringCatSheaf where
  hom := endomorphism a.val
  inv := endomorphism a.inv
  hom_inv_id := by
    rw [endomorphism_comp, a.val_inv, endomorphism_one]
  inv_hom_id := by
    rw [endomorphism_comp, a.inv_val, endomorphism_one]

@[simp]
lemma unitIso_hom {X : Scheme.{u}} (a : Γ(X, ⊤)ˣ) :
    (unitIso a).hom = endomorphism a.val := rfl

@[simp]
lemma unitIso_one {X : Scheme.{u}} :
    unitIso (1 : Γ(X, ⊤)ˣ) = Iso.refl _ :=
  Iso.ext (by
    rw [Iso.refl_hom]
    exact (congrArg endomorphism Units.val_one).trans endomorphism_one)

/-- The transposed form of pullback naturality for multiplication by a
global function. -/
private lemma unitToPushforward_endomorphism {T S : Scheme.{0}}
    (f : T ⟶ S) (a : Γ(S, ⊤)) :
    endomorphism a ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (endomorphism (f.appTop a)) := by
  apply ((Scheme.Modules.pushforward f).obj
    (SheafOfModules.unit T.ringCatSheaf)).unitHomEquiv.injective
  refine PresheafOfModules.sections_ext _ _ (fun U => ?_)
  change
    (SheafOfModules.unitToPushforwardObjUnit
      f.toRingCatSheafHom).val.app U
        ((endomorphism a).val.app U
          (1 : S.ringCatSheaf.obj.obj U)) =
      ((Scheme.Modules.pushforward f).map
        (endomorphism (f.appTop a))).val.app U
          ((SheafOfModules.unitToPushforwardObjUnit
            f.toRingCatSheafHom).val.app U
              (1 : S.ringCatSheaf.obj.obj U))
  rw [endomorphism_app_one]
  change
    f.toRingCatSheafHom.hom.app U
        (S.ringCatSheaf.obj.map (homOfLE le_top).op a) =
      (endomorphism (f.appTop a)).val.app
        (Opposite.op
          ((TopologicalSpace.Opens.map f.base).obj U.unop))
        (f.toRingCatSheafHom.hom.app U 1)
  rw [map_one]
  erw [endomorphism_app_one]
  have h := ConcreteCategory.congr_hom
    (f.toRingCatSheafHom.hom.naturality
      (homOfLE (le_top : U.unop ≤ ⊤)).op) a
  exact h

/-- Pullback carries multiplication by `a` to multiplication by the pulled
back function. -/
lemma pullback_endomorphism {T S : Scheme.{0}} (f : T ⟶ S)
    (a : Γ(S, ⊤)) :
    (Scheme.Modules.pullback f).map (endomorphism a) ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom =
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
        endomorphism (f.appTop a) := by
  apply (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
    (SheafOfModules.unit S.ringCatSheaf)
    (SheafOfModules.unit T.ringCatSheaf) |>.injective
  have hq :
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
          (SheafOfModules.unit S.ringCatSheaf)
          (SheafOfModules.unit T.ringCatSheaf)
          (SheafOfModules.pullbackObjUnitToUnit
            f.toRingCatSheafHom) =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  erw [Adjunction.homEquiv_naturality_left, hq]
  refine (unitToPushforward_endomorphism f a).trans ?_
  exact
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
      (endomorphism (f.appTop a))).trans
        (congrArg
          (· ≫ (Scheme.Modules.pushforward f).map
            (endomorphism (f.appTop a))) hq)).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar
