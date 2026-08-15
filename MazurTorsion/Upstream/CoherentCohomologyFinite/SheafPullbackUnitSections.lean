/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerOverlapSections

/-!
# Sections of pullbacks of the structure sheaf

This file compares the abstract restriction/pullback equivalence for an
open immersion with the concrete map on regular functions.  The pointwise
formula is useful whenever a sheaf-of-modules calculation is transported
back to ordinary scheme sections.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

/-- The structure sheaf, named as an object of the scheme's module
category so its site is retained during elaboration. -/
def schemeUnitModule (X : Scheme) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- The restriction adjunction specialized to the two typed structure
sheaf modules. -/
noncomputable def restrictUnitHomEquiv
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :=
  (Scheme.Modules.restrictAdjunction f).homEquiv
    (schemeUnitModule Y) (schemeUnitModule X)

/-- The canonical structure-sheaf map, with its source and target fixed in
the scheme-module categories. -/
def schemeUnitToPushforward
    {X Y : Scheme} (f : X ⟶ Y) :
    schemeUnitModule Y ⟶
      (Scheme.Modules.pushforward f).obj (schemeUnitModule X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

lemma restrictUnitHomEquiv_comparison
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictUnitHomEquiv f)
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app
            (schemeUnitModule Y) ≫
          (pullbackUnitIso f).hom) =
      schemeUnitToPushforward f := by
  have hraw :
      ((Scheme.Modules.restrictAdjunction f).homEquiv
          (SheafOfModules.unit Y.ringCatSheaf)
          (SheafOfModules.unit X.ringCatSheaf))
          ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app
              (SheafOfModules.unit Y.ringCatSheaf) ≫
            (pullbackUnitIso f).hom) =
        schemeUnitToPushforward f := by
    let A : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let B : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let α : (Scheme.Modules.restrictFunctor f).obj A ⟶
        (Scheme.Modules.pullback f).obj A :=
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app A
    let β : (Scheme.Modules.pullback f).obj A ⟶ B :=
      (pullbackUnitIso f).hom
    letI :
        (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
      { exists_leftAdjoint :=
          ⟨Scheme.Modules.pullback f,
            ⟨by
              change Scheme.Modules.pullback f ⊣
                Scheme.Modules.pushforward f
              exact Scheme.Modules.pullbackPushforwardAdjunction f⟩⟩ }
    have hcanonical :
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
            A B) β = schemeUnitToPushforward f :=
      SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
        f.toRingCatSheafHom
    have hcomparison :
        ((Scheme.Modules.restrictAdjunction f).homEquiv A B) (α ≫ β) =
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv A B) β := by
      calc
      _ = (Scheme.Modules.restrictAdjunction f).unit.app A ≫
          (Scheme.Modules.pushforward f).map (α ≫ β) :=
        Adjunction.homEquiv_unit
          (Scheme.Modules.restrictAdjunction f) A B (α ≫ β)
      _ = (Scheme.Modules.restrictAdjunction f).unit.app A ≫
          ((Scheme.Modules.pushforward f).map α ≫
            (Scheme.Modules.pushforward f).map β) := by
        exact congrArg
          ((Scheme.Modules.restrictAdjunction f).unit.app A ≫ ·)
          ((Scheme.Modules.pushforward f).map_comp α β)
      _ = ((Scheme.Modules.restrictAdjunction f).unit.app A ≫
            (Scheme.Modules.pushforward f).map α) ≫
          (Scheme.Modules.pushforward f).map β :=
        (Category.assoc _ _ _).symm
      _ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A ≫
          (Scheme.Modules.pushforward f).map β := by
        exact congrArg
          (· ≫ (Scheme.Modules.pushforward f).map β)
          (Scheme.Modules.restrictAdjunction_unit_app_iso f A)
      _ = ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
          A B) β :=
        (Adjunction.homEquiv_unit
          (Scheme.Modules.pullbackPushforwardAdjunction f) A B β).symm
    exact hcomparison.trans hcanonical
  exact hraw

lemma restrictUnitHomEquiv_symm_unit_app
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (W : X.Opens) (y : Γ(Y, f ''ᵁ W)) :
    ((restrictUnitHomEquiv f).symm
        (schemeUnitToPushforward f)).app W y =
      (f.appIso W).hom y := by
  let A : Y.Modules := schemeUnitModule Y
  let B : X.Modules := schemeUnitModule X
  let adj := Scheme.Modules.restrictAdjunction f
  let u : A ⟶ (Scheme.Modules.pushforward f).obj B :=
    schemeUnitToPushforward f
  change ((adj.homEquiv A B).symm u).app W y = _
  have hc := Adjunction.homEquiv_counit adj A B u
  refine (congrArg (fun q => q.app W y) hc).trans ?_
  change
    X.presheaf.map
        (eqToHom (f.preimage_image_eq W).symm).op
        (f.app (f ''ᵁ W) y) =
      (f.appIso W).hom y
  rw [← ConcreteCategory.comp_apply, ← f.appIso_hom]

/-- The restriction-to-structure-sheaf morphism adjoint to the canonical
map from the structure sheaf to its pushforward. -/
def restrictUnitToUnit
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).obj
        (schemeUnitModule Y) ⟶
      schemeUnitModule X :=
  (restrictUnitHomEquiv f).symm
    (schemeUnitToPushforward f)

/-- Restriction/pullback followed by the canonical pullback
trivialization is the adjoint restriction map. -/
lemma restrictFunctorIsoPullback_unit
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          (schemeUnitModule Y) ≫
        (pullbackUnitIso f).hom =
      restrictUnitToUnit f := by
  let e := restrictUnitHomEquiv f
  let u := schemeUnitToPushforward f
  apply e.injective
  change e _ = e (e.symm u)
  rw [e.apply_symm_apply]
  exact restrictUnitHomEquiv_comparison f

/-- Pointwise, the restriction/pullback comparison for the structure
sheaf is exactly the usual open-immersion map on sections. -/
lemma restrictFunctorIsoPullback_unit_app
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (W : X.Opens)
    (y : Γ(Y, f ''ᵁ W)) :
    (pullbackUnitIso f).hom.app W
        (((Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          (schemeUnitModule Y)).app W y) =
      (f.appIso W).hom y := by
  change
    ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          (schemeUnitModule Y) ≫
        (pullbackUnitIso f).hom).app W y =
      (f.appIso W).hom y
  rw [restrictFunctorIsoPullback_unit]
  let e := restrictUnitHomEquiv f
  let u := schemeUnitToPushforward f
  change (e.symm u).app W y = _
  exact restrictUnitHomEquiv_symm_unit_app f W y

/-- Naturality of the restriction/pullback comparison, evaluated on a
single open and section. -/
lemma restrictFunctorIsoPullback_hom_app_naturality
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : SheafOfModules Y.ringCatSheaf} (e : M ⟶ N)
    (W : X.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor f).obj M, W)) :
    ((Scheme.Modules.pullback f).map e).app W
        (((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M).app W x) =
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N).app W
        (((Scheme.Modules.restrictFunctor f).map e).app W x) := by
  simpa only [Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply] using
    congrArg (fun q => q.app W x)
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality e).symm

/-- Conjugating a sheaf morphism by the maps induced by an equality of
opens leaves its application unchanged. -/
lemma moduleHom_mapIso_inv_hom_app_mapIso_hom
    {X : Scheme} {M N : X.Modules}
    (e : M ⟶ N) {U V : X.Opens} (h : U = V)
    (x : Γ(M, V)) :
    (N.presheaf.mapIso (eqToIso h).op).inv.hom
        (e.app U
          ((M.presheaf.mapIso (eqToIso h).op).hom.hom x)) =
      e.app V x := by
  subst V
  simp

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar
