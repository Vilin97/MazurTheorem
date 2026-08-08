/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.ModuleCat.Products
import MazurTorsion.Upstream.CurveLineBundleDescent

/-!
# The equalizer candidate for effective module descent

This file constructs the canonical compatible-family object attached to module descent data on
one scheme open cover.  The construction is an equalizer of the two overlap-restriction maps.
It is only a candidate until its restriction to every member of the cover is identified with the
specified local module.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

universe u

/-- For a cartesian square whose vertical maps are open immersions, taking the image along the
left projection after pulling an open set back agrees with pulling back its image along the right
vertical map.  This is the site-level comparison underlying open base change for module sheaves.
-/
noncomputable def openPullbackOpensIso
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) :
    f₁.opensFunctor ⋙ TopologicalSpace.Opens.map f₂.base ≅
      TopologicalSpace.Opens.map p₁.base ⋙ p₂.opensFunctor :=
  NatIso.ofComponents
    (fun W ↦ eqToIso
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W).symm)
    (fun _ ↦ Subsingleton.elim _ _)

/-- Restriction of a direct image around a cartesian square of open immersions is the direct
image of the corresponding restriction. -/
noncomputable def openPullbackRestrictPushforwardIso
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) :
    Scheme.Modules.pushforward f₂ ⋙ Scheme.Modules.restrictFunctor f₁ ≅
      Scheme.Modules.restrictFunctor p₂ ⋙ Scheme.Modules.pushforward p₁ := by
  let e := openPullbackOpensIso p₁ p₂ f₁ f₂ H
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  exact SheafOfModules.pushforwardCongr₂ _ e.symm (by
    ext W x
    let hW := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W.unop
    change ((f₁.appIso W.unop).inv ≫ f₂.app (f₁ ''ᵁ W.unop) ≫
      X₂.presheaf.map (eqToHom hW).op) x =
        (p₁.app W.unop ≫ (p₂.appIso (p₁ ⁻¹ᵁ W.unop)).inv) x
    suffices (f₁.appIso W.unop).inv ≫ f₂.app (f₁ ''ᵁ W.unop) ≫
        X₂.presheaf.map (eqToHom hW).op =
      p₁.app W.unop ≫ (p₂.appIso (p₁ ⁻¹ᵁ W.unop)).inv by
      exact congr($this x)
    rw [← cancel_mono (p₂.appIso (p₁ ⁻¹ᵁ W.unop)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [p₂.appIso_hom, p₂.naturality_assoc]
    rw [IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq
      p₁ f₁ (p₂ ≫ f₂) H.w.symm W.unop]
    simp only [Scheme.Hom.comp_app]
    rw [← Functor.map_comp, ← op_comp]
    rfl)

/-- The descent transition on a chosen pairwise overlap. -/
noncomputable def compatibleFamilyOverlapPullbackIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    (Scheme.Modules.pullback (overlap cov i j).p₁).obj (D.obj i) ≅
      (Scheme.Modules.pullback (overlap cov i j).p₂).obj (D.obj j) :=
  let P := overlap cov i j
  D.iso (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm

/-- The `j`-th component of the compatible family induced by the local object on chart `i`.
It first transposes the overlap transition across restriction/direct-image adjunction, then uses
open base change to land in the restriction to chart `i` of the direct image from chart `j`.
These maps are the components required to construct an inverse to
`compatibleFamilyRestrictionHom`. -/
noncomputable def compatibleFamilyChartComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    D.obj i ⟶
      (Scheme.Modules.restrictFunctor (cov.f i)).obj
        ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) :=
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  let transition :=
    (Scheme.Modules.restrictFunctorIsoPullback P.p₁).app (D.obj i) ≪≫
      compatibleFamilyOverlapPullbackIso D i j ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback P.p₂).app (D.obj j)).symm
  ((Scheme.Modules.restrictAdjunction P.p₁).homEquiv
      (D.obj i)
      ((Scheme.Modules.restrictFunctor P.p₂).obj (D.obj j)))
      transition.hom ≫
    (openPullbackRestrictPushforwardIso
      P.p₁ P.p₂ (cov.f i) (cov.f j) P.isPullback).inv.app (D.obj j)

/-- The product of the direct images of all local modules in a descent datum. -/
noncomputable def compatibleFamilyAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  ∏ᶜ fun i ↦ (Scheme.Modules.pushforward (cov.f i)).obj (D.obj i)

/-- The product of the direct images of the second local module restricted to every chosen
pairwise overlap. -/
noncomputable def compatibleFamilyOverlapAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  ∏ᶜ fun ij : cov.I₀ × cov.I₀ ↦
    let P := overlap cov ij.1 ij.2
    (Scheme.Modules.pushforward (P.p₁ ≫ cov.f ij.1)).obj
      ((Scheme.Modules.pullback P.p₂).obj (D.obj ij.2))

/-- Restrict the first member of a local family to an overlap and transport it through the
descent isomorphism. -/
noncomputable def compatibleFamilyFirstComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbient D ⟶
      (Scheme.Modules.pushforward
        ((overlap cov i j).p₁ ≫ cov.f i)).obj
        ((Scheme.Modules.pullback (overlap cov i j).p₂).obj (D.obj j)) :=
  let P := overlap cov i j
  Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) i ≫
    (Scheme.Modules.pushforward (cov.f i)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction P.p₁).unit.app (D.obj i)) ≫
    (Scheme.Modules.pushforwardComp P.p₁ (cov.f i)).hom.app
      ((Scheme.Modules.pullback P.p₁).obj (D.obj i)) ≫
    (Scheme.Modules.pushforward (P.p₁ ≫ cov.f i)).map
      (D.hom (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm)

/-- Restrict the second member of a local family to an overlap, then identify the two equal
structural maps to the base. -/
noncomputable def compatibleFamilySecondComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbient D ⟶
      (Scheme.Modules.pushforward
        ((overlap cov i j).p₁ ≫ cov.f i)).obj
        ((Scheme.Modules.pullback (overlap cov i j).p₂).obj (D.obj j)) :=
  let P := overlap cov i j
  Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j ≫
    (Scheme.Modules.pushforward (cov.f j)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction P.p₂).unit.app (D.obj j)) ≫
    (Scheme.Modules.pushforwardComp P.p₂ (cov.f j)).hom.app
      ((Scheme.Modules.pullback P.p₂).obj (D.obj j)) ≫
    (Scheme.Modules.pushforwardCongr P.condition.symm).hom.app
      ((Scheme.Modules.pullback P.p₂).obj (D.obj j))

/-- The first overlap-restriction map from all local families. -/
noncomputable def compatibleFamilyFirst
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) :
    compatibleFamilyAmbient D ⟶ compatibleFamilyOverlapAmbient D :=
  Pi.lift fun ij ↦ compatibleFamilyFirstComponent D ij.1 ij.2

/-- The second overlap-restriction map from all local families. -/
noncomputable def compatibleFamilySecond
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) :
    compatibleFamilyAmbient D ⟶ compatibleFamilyOverlapAmbient D :=
  Pi.lift fun ij ↦ compatibleFamilySecondComponent D ij.1 ij.2

/-- The global module candidate consisting of compatible local families. -/
noncomputable def compatibleFamilyModule
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  equalizer (compatibleFamilyFirst D) (compatibleFamilySecond D)

/-- The candidate's universal inclusion satisfies the required compatibility equation. -/
theorem compatibleFamilyModule_condition
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) :
    equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
        compatibleFamilyFirst D =
      equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
        compatibleFamilySecond D :=
  equalizer.condition _ _

/-- The compatible-family module projects to each pushed-forward local module. -/
noncomputable def compatibleFamilyProjection
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyModule D ⟶
      (Scheme.Modules.pushforward (cov.f i)).obj (D.obj i) :=
  equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
    Pi.π (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) i

/-- The adjoint transpose of the chart projection, stated with the genuine module pullback
functor used by `EffectiveModule`.  Proving that this morphism is an isomorphism is the remaining
effective-descent theorem for the equalizer candidate. -/
noncomputable def compatibleFamilyRestrictionHom
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).obj (compatibleFamilyModule D) ⟶ D.obj i :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
    (compatibleFamilyModule D) (D.obj i)).symm (compatibleFamilyProjection D i)

/-- The chart restriction map is definitionally adjoint to the corresponding projection of
compatible families.  This is the comparison equation used when constructing its inverse. -/
theorem compatibleFamilyRestrictionHom_adjunct
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
        (compatibleFamilyModule D) (D.obj i) (compatibleFamilyRestrictionHom D i) =
      compatibleFamilyProjection D i := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
    (compatibleFamilyModule D) (D.obj i)).apply_symm_apply _

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
