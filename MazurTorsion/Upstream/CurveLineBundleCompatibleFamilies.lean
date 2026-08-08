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

@[simp]
private theorem openPullbackRestrictPushforwardIso_hom_app_apply
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor f₁).obj
      ((Scheme.Modules.pushforward f₂).obj M), W)) :
    (((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).hom.app M).app W) x =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op x := by
  rfl

@[simp]
private theorem openPullbackRestrictPushforwardIso_hom_app
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens) :
    ((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).hom.app M).app W =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op := by
  rfl

@[simp]
private theorem openPullbackRestrictPushforwardIso_app_hom_app
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens) :
    ((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).app M).hom.app W =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op := by
  rfl

@[simp]
private theorem openPullbackRestrictPushforwardIso_inv_app_apply
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor p₂).obj M, p₁ ⁻¹ᵁ W)) :
    (((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).inv.app M).app W) x =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W).symm).op x := by
  rfl

@[simp]
private theorem openPullbackRestrictPushforwardIso_inv_app
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens) :
    ((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).inv.app M).app W =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W).symm).op := by
  rfl

@[simp]
private theorem openPullbackRestrictPushforwardIso_app_inv_app
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens) :
    ((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).app M).inv.app W =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W).symm).op := by
  rfl

@[simp]
private theorem restrictFunctor_map_app_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (phi : M ⟶ N) (U : X.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor f).obj M, U)) :
    (((Scheme.Modules.restrictFunctor f).map phi).app U) x =
      phi.app (f ''ᵁ U) x := by
  rfl

@[simp]
private theorem restrictFunctor_map_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (phi : M ⟶ N) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctor f).map phi).app U = phi.app (f ''ᵁ U) := by
  rfl

@[simp]
private theorem modules_comp_app
    {X : Scheme.{u}} {M N K : X.Modules} (phi : M ⟶ N) (psi : N ⟶ K)
    (U : X.Opens) :
    (phi ≫ psi).app U = phi.app U ≫ psi.app U := by
  rfl

private theorem conjugateEquiv_restrictFunctorComp_hom
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    CategoryTheory.conjugateEquiv
      ((Scheme.Modules.restrictAdjunction g).comp
        (Scheme.Modules.restrictAdjunction f))
      (Scheme.Modules.restrictAdjunction (f ≫ g))
      (Scheme.Modules.restrictFunctorComp f g).hom =
        (Scheme.Modules.pushforwardComp f g).hom := by
  ext M U x
  simp only [Scheme.Modules.pushforward_obj_obj, Scheme.Hom.comp_base,
    TopologicalSpace.Opens.map_comp_obj, Functor.comp_obj,
    CategoryTheory.conjugateEquiv_apply_app, Adjunction.comp_counit_app,
    Functor.map_comp, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, homOfLE_leOfHom,
    Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, Functor.op_obj, eqToHom_op,
    restrictFunctor_map_app, Scheme.Modules.restrictAdjunction_counit_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app, AddCommGrpCat.hom_id]
  let A := M.presheaf.obj (Opposite.op (f ⁻¹ᵁ (g ⁻¹ᵁ U)))
  change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫
    M.presheaf.map _) x = (𝟙 A) x
  congr 1
  simp only [← Functor.map_comp]
  rw [← M.presheaf.map_id]
  congr 1

private theorem restrictFunctorIsoPullback_comp
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M =
      (Scheme.Modules.restrictFunctorComp f g).hom.app M ≫
        (Scheme.Modules.restrictFunctor f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app M := by
  let ARf := Scheme.Modules.restrictAdjunction f
  let ARg := Scheme.Modules.restrictAdjunction g
  let ARfg := Scheme.Modules.restrictAdjunction (f ≫ g)
  let APf := Scheme.Modules.pullbackPushforwardAdjunction f
  let APg := Scheme.Modules.pullbackPushforwardAdjunction g
  let APfg := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let ef := Scheme.Modules.restrictFunctorIsoPullback f
  let eg := Scheme.Modules.restrictFunctorIsoPullback g
  let efg := Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)
  let er := Scheme.Modules.restrictFunctorComp f g
  let ep := Scheme.Modules.pullbackComp f g
  let en : Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.restrictFunctor f ⟶
      Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f :=
    Functor.whiskerRight eg.hom (Scheme.Modules.restrictFunctor f) ≫
      Functor.whiskerLeft (Scheme.Modules.pullback g) ef.hom
  have hen : CategoryTheory.conjugateEquiv (APg.comp APf) (ARg.comp ARf) en = 𝟙 _ := by
    dsimp only [en]
    rw [← CategoryTheory.conjugateEquiv_comp
      (APg.comp APf) (APg.comp ARf) (ARg.comp ARf)]
    rw [CategoryTheory.conjugateEquiv_whiskerLeft,
      CategoryTheory.conjugateEquiv_whiskerRight]
    dsimp only [ef, eg, Scheme.Modules.restrictFunctorIsoPullback]
    dsimp only [APf, ARf, APg, ARg]
    simp [Adjunction.leftAdjointUniq]
  let egp := Scheme.Modules.pushforwardComp f g
  have hefg : CategoryTheory.conjugateEquiv APfg ARfg efg.hom = 𝟙 _ := by
    dsimp only [efg, Scheme.Modules.restrictFunctorIsoPullback, APfg, ARfg]
    simp [Adjunction.leftAdjointUniq]
  have her : CategoryTheory.conjugateEquiv (ARg.comp ARf) ARfg er.hom = egp.hom := by
    dsimp only [er, egp, ARf, ARg, ARfg]
    exact conjugateEquiv_restrictFunctorComp_hom f g
  have hp : CategoryTheory.conjugateEquiv (APg.comp APf) APfg ep.inv = egp.hom := by
    dsimp only [ep, egp, APf, APg, APfg]
    exact Scheme.Modules.conjugateEquiv_pullbackComp_inv f g
  letI : IsIso egp.hom := egp.isIso_hom
  have hep : CategoryTheory.conjugateEquiv APfg (APg.comp APf) ep.hom = egp.inv := by
    apply (cancel_mono egp.hom).1
    calc
      _ = CategoryTheory.conjugateEquiv APfg (APg.comp APf) ep.hom ≫
          CategoryTheory.conjugateEquiv (APg.comp APf) APfg ep.inv := by rw [hp]
      _ = CategoryTheory.conjugateEquiv APfg APfg (ep.inv ≫ ep.hom) := by
        rw [CategoryTheory.conjugateEquiv_comp]
      _ = 𝟙 _ := by simp
      _ = egp.inv ≫ egp.hom := egp.inv_hom_id.symm
  have hchain : CategoryTheory.conjugateEquiv APfg ARfg
      (er.hom ≫ en ≫ ep.hom) = 𝟙 _ := by
    calc
      _ = CategoryTheory.conjugateEquiv APfg (APg.comp APf) ep.hom ≫
          CategoryTheory.conjugateEquiv (APg.comp APf) ARfg
            (er.hom ≫ en) :=
        (CategoryTheory.conjugateEquiv_comp APfg (APg.comp APf) ARfg
          ep.hom (er.hom ≫ en)).symm
      _ = CategoryTheory.conjugateEquiv APfg (APg.comp APf) ep.hom ≫
          (CategoryTheory.conjugateEquiv (APg.comp APf) (ARg.comp ARf) en ≫
            CategoryTheory.conjugateEquiv (ARg.comp ARf) ARfg er.hom) := by
        exact congrArg (fun z :
          Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g ⟶
            Scheme.Modules.pushforward (f ≫ g) ↦
          CategoryTheory.conjugateEquiv APfg (APg.comp APf) ep.hom ≫ z)
          (CategoryTheory.conjugateEquiv_comp
            (APg.comp APf) (ARg.comp ARf) ARfg en er.hom).symm
      _ = egp.inv ≫ 𝟙 _ ≫ egp.hom := by rw [hep, hen, her]
      _ = 𝟙 _ := by simp
  have hnat : efg.hom = er.hom ≫ en ≫ ep.hom := by
    apply (CategoryTheory.conjugateEquiv APfg ARfg).injective
    exact hefg.trans hchain.symm
  exact congr_app hnat M

private noncomputable def restrictionTransition
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f)
    {Y : Scheme} (q : Y ⟶ X) {i j : cov.I₀}
    (a : Y ⟶ cov.X i) (b : Y ⟶ cov.X j)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ cov.f i = q) (hb : b ≫ cov.f j = q) :
    (Scheme.Modules.restrictFunctor a).obj (D.obj i) ⟶
      (Scheme.Modules.restrictFunctor b).obj (D.obj j) :=
  (Scheme.Modules.restrictFunctorIsoPullback a).hom.app (D.obj i) ≫
    D.hom q a b ha hb ≫
    (Scheme.Modules.restrictFunctorIsoPullback b).inv.app (D.obj j)

private theorem restrictionTransition_map
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f)
    {Y Y' : Scheme} (g : Y' ⟶ Y) [IsOpenImmersion g]
    (q : Y ⟶ X) {i j : cov.I₀}
    (a : Y ⟶ cov.X i) (b : Y ⟶ cov.X j)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ cov.f i = q) (hb : b ≫ cov.f j = q) :
    (Scheme.Modules.restrictFunctor g).map
        (restrictionTransition D q a b ha hb) ≫
      (Scheme.Modules.restrictFunctorComp g b).inv.app (D.obj j) =
    (Scheme.Modules.restrictFunctorComp g a).inv.app (D.obj i) ≫
      restrictionTransition D (g ≫ q) (g ≫ a) (g ≫ b)
        (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) := by
  let Rg := Scheme.Modules.restrictFunctor g
  let ea := Scheme.Modules.restrictFunctorIsoPullback a
  let eb := Scheme.Modules.restrictFunctorIsoPullback b
  let eg := Scheme.Modules.restrictFunctorIsoPullback g
  let ega := Scheme.Modules.restrictFunctorIsoPullback (g ≫ a)
  let egb := Scheme.Modules.restrictFunctorIsoPullback (g ≫ b)
  let ca := Scheme.Modules.restrictFunctorComp g a
  let cb := Scheme.Modules.restrictFunctorComp g b
  let pa := Scheme.Modules.pullbackComp g a
  let pb := Scheme.Modules.pullbackComp g b
  let h : (Scheme.Modules.pullback a).obj (D.obj i) ⟶
      (Scheme.Modules.pullback b).obj (D.obj j) := D.hom q a b ha hb
  let h' : (Scheme.Modules.pullback (g ≫ a)).obj (D.obj i) ⟶
      (Scheme.Modules.pullback (g ≫ b)).obj (D.obj j) :=
    D.hom (g ≫ q) (g ≫ a) (g ≫ b)
      (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb])
  have hca : ca.inv.app (D.obj i) ≫ ega.hom.app (D.obj i) =
      Rg.map (ea.hom.app (D.obj i)) ≫
        eg.hom.app ((Scheme.Modules.pullback a).obj (D.obj i)) ≫
        pa.hom.app (D.obj i) := by
    have hc : ega.hom.app (D.obj i) = ca.hom.app (D.obj i) ≫
        Rg.map (ea.hom.app (D.obj i)) ≫
        eg.hom.app ((Scheme.Modules.pullback a).obj (D.obj i)) ≫
        pa.hom.app (D.obj i) := restrictFunctorIsoPullback_comp g a (D.obj i)
    calc
      _ = ca.inv.app (D.obj i) ≫ (ca.hom.app (D.obj i) ≫
          Rg.map (ea.hom.app (D.obj i)) ≫
          eg.hom.app ((Scheme.Modules.pullback a).obj (D.obj i)) ≫
          pa.hom.app (D.obj i)) := congrArg (fun z ↦ ca.inv.app (D.obj i) ≫ z) hc
      _ = _ := ca.inv_hom_id_app_assoc (D.obj i) _
  have hcb : cb.inv.app (D.obj j) ≫ egb.hom.app (D.obj j) =
      Rg.map (eb.hom.app (D.obj j)) ≫
        eg.hom.app ((Scheme.Modules.pullback b).obj (D.obj j)) ≫
        pb.hom.app (D.obj j) := by
    have hc : egb.hom.app (D.obj j) = cb.hom.app (D.obj j) ≫
        Rg.map (eb.hom.app (D.obj j)) ≫
        eg.hom.app ((Scheme.Modules.pullback b).obj (D.obj j)) ≫
        pb.hom.app (D.obj j) := restrictFunctorIsoPullback_comp g b (D.obj j)
    calc
      _ = cb.inv.app (D.obj j) ≫ (cb.hom.app (D.obj j) ≫
          Rg.map (eb.hom.app (D.obj j)) ≫
          eg.hom.app ((Scheme.Modules.pullback b).obj (D.obj j)) ≫
          pb.hom.app (D.obj j)) := congrArg (fun z ↦ cb.inv.app (D.obj j) ≫ z) hc
      _ = _ := cb.inv_hom_id_app_assoc (D.obj j) _
  have hpull := D.pullHom_hom g q (g ≫ q) rfl a b ha hb
    (g ≫ a) (g ≫ b) rfl rfl
  have hmap := CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
    (F := modulesPseudofunctor) h g (g ≫ a) (g ≫ b) rfl rfl
  rw [hpull] at hmap
  change (Scheme.Modules.pullback g).map h =
    pa.hom.app (D.obj i) ≫ h' ≫ pb.inv.app (D.obj j) at hmap
  letI : IsIso (egb.hom.app (D.obj j)) := (egb.app (D.obj j)).isIso_hom
  have hpb : pb.inv.app (D.obj j) ≫ pb.hom.app (D.obj j) = 𝟙 _ :=
    pb.inv_hom_id_app (D.obj j)
  have hegb : egb.inv.app (D.obj j) ≫ egb.hom.app (D.obj j) = 𝟙 _ :=
    egb.inv_hom_id_app (D.obj j)
  rw [← cancel_mono (egb.hom.app (D.obj j))]
  simp only [Category.assoc]
  rw [hcb]
  dsimp only [restrictionTransition]
  change Rg.map (ea.hom.app (D.obj i) ≫ h ≫ eb.inv.app (D.obj j)) ≫
      (Rg.map (eb.hom.app (D.obj j)) ≫
        eg.hom.app ((Scheme.Modules.pullback b).obj (D.obj j)) ≫
        pb.hom.app (D.obj j)) = _
  simp only [Functor.map_comp, Category.assoc]
  have heb : eb.inv.app (D.obj j) ≫ eb.hom.app (D.obj j) = 𝟙 _ :=
    eb.inv_hom_id_app (D.obj j)
  have hRgEb : Rg.map (eb.inv.app (D.obj j) ≫ eb.hom.app (D.obj j)) = 𝟙 _ := by
    rw [heb]
    exact Rg.map_id _
  slice_lhs 3 4 =>
    rw [← Rg.map_comp, hRgEb]
  simp only [Category.id_comp]
  rw [eg.hom.naturality_assoc h]
  rw [hmap]
  slice_lhs 5 6 => rw [hpb]
  have hegb' : (h' ≫ egb.inv.app (D.obj j)) ≫ egb.hom.app (D.obj j) = h' := by
    calc
      _ = h' ≫ (egb.inv.app (D.obj j) ≫ egb.hom.app (D.obj j)) :=
        Category.assoc _ _ _
      _ = h' ≫ 𝟙 _ := congrArg (fun z ↦ h' ≫ z) hegb
      _ = h' := Category.comp_id _
  slice_rhs 3 4 => exact hegb'
  simp only [Category.comp_id]
  simpa only [Category.assoc] using
    (congrArg (fun z ↦ z ≫ h') hca).symm

private theorem restrictionTransition_comp
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f)
    {Y : Scheme} (q : Y ⟶ X) {i j k : cov.I₀}
    (a : Y ⟶ cov.X i) (b : Y ⟶ cov.X j) (c : Y ⟶ cov.X k)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    (ha : a ≫ cov.f i = q) (hb : b ≫ cov.f j = q)
    (hc : c ≫ cov.f k = q) :
    restrictionTransition D q a b ha hb ≫
        restrictionTransition D q b c hb hc =
      restrictionTransition D q a c ha hc := by
  dsimp only [restrictionTransition]
  let ea := Scheme.Modules.restrictFunctorIsoPullback a
  let eb := Scheme.Modules.restrictFunctorIsoPullback b
  let ec := Scheme.Modules.restrictFunctorIsoPullback c
  let hab : (Scheme.Modules.pullback a).obj (D.obj i) ⟶
      (Scheme.Modules.pullback b).obj (D.obj j) := D.hom q a b ha hb
  let hbc : (Scheme.Modules.pullback b).obj (D.obj j) ⟶
      (Scheme.Modules.pullback c).obj (D.obj k) := D.hom q b c hb hc
  let hac : (Scheme.Modules.pullback a).obj (D.obj i) ⟶
      (Scheme.Modules.pullback c).obj (D.obj k) := D.hom q a c ha hc
  change ea.hom.app (D.obj i) ≫ hab ≫ eb.inv.app (D.obj j) ≫
      eb.hom.app (D.obj j) ≫ hbc ≫ ec.inv.app (D.obj k) =
    ea.hom.app (D.obj i) ≫ hac ≫ ec.inv.app (D.obj k)
  have heb : eb.inv.app (D.obj j) ≫ eb.hom.app (D.obj j) = 𝟙 _ :=
    eb.inv_hom_id_app (D.obj j)
  slice_lhs 3 4 => rw [heb]
  simp only [Category.id_comp]
  have hcomp : hab ≫ hbc = hac := D.hom_comp q a b c ha hb hc
  slice_lhs 2 3 => rw [hcomp]

private theorem restrictFunctorCongr_refl_hom
    {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  ext U x
  change M.presheaf.obj (Opposite.op (f ''ᵁ U)) at x
  simp only [Scheme.Modules.restrictFunctorCongr_hom_app_app]
  change M.presheaf.map _ x = x
  calc
    M.presheaf.map _ x = M.presheaf.map (𝟙 _) x :=
      M.val.congr_map_apply (Subsingleton.elim _ _) x
    _ = x := by simp

private theorem restrictFunctorCongr_hom_comp
    {X Y : Scheme} {f g h : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    (hfg : f = g) (hgh : g = h) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr hfg).hom.app M ≫
        (Scheme.Modules.restrictFunctorCongr hgh).hom.app M =
      (Scheme.Modules.restrictFunctorCongr (hfg.trans hgh)).hom.app M := by
  ext U x
  simp only [Scheme.Modules.restrictFunctorCongr_hom_app_app]
  change (M.presheaf.map _ ≫ M.presheaf.map _) x = M.presheaf.map _ x
  simp only [← Functor.map_comp]
  exact M.val.congr_map_apply (Subsingleton.elim _ _) x

private theorem restrictionTransition_congr_all
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f)
    {Y : Scheme} (q q' : Y ⟶ X) {i j : cov.I₀}
    (a a' : Y ⟶ cov.X i) (b b' : Y ⟶ cov.X j)
    [ia : IsOpenImmersion a] [ia' : IsOpenImmersion a']
    [ib : IsOpenImmersion b] [ib' : IsOpenImmersion b']
    (hq : q = q') (ha : a = a') (hb : b = b')
    (hqa : a ≫ cov.f i = q) (hqb : b ≫ cov.f j = q)
    (hqa' : a' ≫ cov.f i = q') (hqb' : b' ≫ cov.f j = q') :
    (Scheme.Modules.restrictFunctorCongr ha).hom.app (D.obj i) ≫
        restrictionTransition D q' a' b' hqa' hqb' ≫
        (Scheme.Modules.restrictFunctorCongr hb.symm).hom.app (D.obj j) =
      restrictionTransition D q a b hqa hqb := by
  cases hq
  cases ha
  cases hb
  cases Subsingleton.elim ia ia'
  cases Subsingleton.elim ib ib'
  cases Subsingleton.elim hqa hqa'
  cases Subsingleton.elim hqb hqb'
  have hi := restrictFunctorCongr_refl_hom a (D.obj i)
  have hj := restrictFunctorCongr_refl_hom b (D.obj j)
  rw [hi, hj]
  exact (Category.id_comp _).trans (Category.comp_id _)

private theorem openPullback_chart_mate
    {X₁ X₂ Y P Z Q : Scheme}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    (HP : IsPullback p₁ p₂ f₁ f₂)
    (a : Z ⟶ X₁) (q : Z ⟶ Y) (ha : a ≫ f₁ = q)
    (s : Q ⟶ Z) (r : Q ⟶ X₂) (HQ : IsPullback s r q f₂)
    (l : Q ⟶ P) (hl₁ : l ≫ p₁ = s ≫ a) (hl₂ : l ≫ p₂ = r)
    (HL : IsPullback l s p₁ a)
    [IsOpenImmersion p₁] [IsOpenImmersion p₂]
    [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    [IsOpenImmersion a] [IsOpenImmersion q]
    [IsOpenImmersion s] [IsOpenImmersion r] [IsOpenImmersion l]
    (A : X₁.Modules) (B : X₂.Modules)
    (τ : (Scheme.Modules.restrictFunctor p₁).obj A ⟶
      (Scheme.Modules.restrictFunctor p₂).obj B) :
    let c : A ⟶ (Scheme.Modules.restrictFunctor f₁).obj
        ((Scheme.Modules.pushforward f₂).obj B) :=
      ((Scheme.Modules.restrictAdjunction p₁).homEquiv A
          ((Scheme.Modules.restrictFunctor p₂).obj B)) τ ≫
        (openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ HP).inv.app B
    ((Scheme.Modules.restrictAdjunction s).homEquiv
      ((Scheme.Modules.restrictFunctor a).obj A)
      ((Scheme.Modules.restrictFunctor r).obj B)).symm
        ((Scheme.Modules.restrictFunctor a).map c ≫
          (Scheme.Modules.restrictFunctorComp a f₁).inv.app
            ((Scheme.Modules.pushforward f₂).obj B) ≫
          (Scheme.Modules.restrictFunctorCongr ha).hom.app
            ((Scheme.Modules.pushforward f₂).obj B) ≫
          (openPullbackRestrictPushforwardIso s r q f₂ HQ).hom.app B) =
      (Scheme.Modules.restrictFunctorComp s a).inv.app A ≫
        (Scheme.Modules.restrictFunctorCongr hl₁.symm).hom.app A ≫
        (Scheme.Modules.restrictFunctorComp l p₁).hom.app A ≫
      (Scheme.Modules.restrictFunctor l).map τ ≫
        (Scheme.Modules.restrictFunctorComp l p₂).inv.app B ≫
        (Scheme.Modules.restrictFunctorCongr hl₂).hom.app B := by
  let c : A ⟶ (Scheme.Modules.restrictFunctor f₁).obj
      ((Scheme.Modules.pushforward f₂).obj B) :=
    ((Scheme.Modules.restrictAdjunction p₁).homEquiv A
        ((Scheme.Modules.restrictFunctor p₂).obj B)) τ ≫
      (openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ HP).inv.app B
  change ((Scheme.Modules.restrictAdjunction s).homEquiv
      ((Scheme.Modules.restrictFunctor a).obj A)
      ((Scheme.Modules.restrictFunctor r).obj B)).symm
        ((Scheme.Modules.restrictFunctor a).map c ≫
          (Scheme.Modules.restrictFunctorComp a f₁).inv.app
            ((Scheme.Modules.pushforward f₂).obj B) ≫
          (Scheme.Modules.restrictFunctorCongr ha).hom.app
            ((Scheme.Modules.pushforward f₂).obj B) ≫
          (openPullbackRestrictPushforwardIso s r q f₂ HQ).hom.app B) = _
  ext U x
  change A.presheaf.obj (Opposite.op (a ''ᵁ (s ''ᵁ U))) at x
  simp only [c, Adjunction.homEquiv_apply, Adjunction.homEquiv_symm_apply,
    modules_comp_app, restrictFunctor_map_app,
    Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforward_obj_presheaf_map,
    Scheme.Modules.restrict_map,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    openPullbackRestrictPushforwardIso_hom_app,
    openPullbackRestrictPushforwardIso_inv_app,
    Scheme.Modules.restrict_map]
  have hV : p₁ ⁻¹ᵁ (a ''ᵁ (s ''ᵁ U)) = l ''ᵁ U := by
    have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      HL.flip (s ''ᵁ U)
    rw [s.preimage_image_eq] at h
    exact h.symm
  have hτ := τ.val.naturality (eqToHom hV).op
  change B.presheaf.map _
      (B.presheaf.map _
        (B.presheaf.map _
          (B.presheaf.map _
            (B.presheaf.map _
              ((Scheme.Modules.Hom.app τ (p₁ ⁻¹ᵁ (a ''ᵁ (s ''ᵁ U))))
                (A.presheaf.map _ x)))))) =
    B.presheaf.map _
      (B.presheaf.map _
        ((Scheme.Modules.Hom.app τ (l ''ᵁ U))
          (A.presheaf.map _ (A.presheaf.map _ (A.presheaf.map _ x)))))
  let x₁ : A.presheaf.obj (Opposite.op ((s ≫ a) ''ᵁ U)) :=
    A.presheaf.map (eqToHom (by simp)).op x
  let x₂ : A.presheaf.obj (Opposite.op ((l ≫ p₁) ''ᵁ U)) :=
    A.presheaf.map (eqToHom (by simp only [hl₁])).op x₁
  let x₃ : A.presheaf.obj (Opposite.op (p₁ ''ᵁ (l ''ᵁ U))) :=
    A.presheaf.map (eqToHom (by simp)).op x₂
  let yL : A.presheaf.obj
      (Opposite.op (p₁ ''ᵁ (p₁ ⁻¹ᵁ (a ''ᵁ (s ''ᵁ U))))) :=
    A.presheaf.map (homOfLE (p₁.image_preimage_le _)).op x
  have hAx : ((Scheme.Modules.restrictFunctor p₁).obj A).val.map
      (eqToHom hV).op x₃ = yL := by
    dsimp only [x₃, x₂, x₁, yL]
    change A.presheaf.map _
        (A.presheaf.map _ (A.presheaf.map _ (A.presheaf.map _ x))) =
      A.presheaf.map _ x
    rw [← A.presheaf.map_comp_apply]
    rw [← A.presheaf.map_comp_apply]
    rw [← A.presheaf.map_comp_apply]
    exact A.val.congr_map_apply (Subsingleton.elim _ _) x
  have hτx := PresheafOfModules.naturality_apply τ.val (eqToHom hV).op x₃
  change (Scheme.Modules.Hom.app τ (p₁ ⁻¹ᵁ (a ''ᵁ (s ''ᵁ U))))
      (((Scheme.Modules.restrictFunctor p₁).obj A).val.map
        (eqToHom hV).op x₃) =
    ((Scheme.Modules.restrictFunctor p₂).obj B).val.map
      (eqToHom hV).op ((Scheme.Modules.Hom.app τ (l ''ᵁ U)) x₃) at hτx
  change B.presheaf.map _
      (B.presheaf.map _
        (B.presheaf.map _
          (B.presheaf.map _
            (B.presheaf.map _
              ((Scheme.Modules.Hom.app τ (p₁ ⁻¹ᵁ (a ''ᵁ (s ''ᵁ U)))) yL))))) =
    B.presheaf.map _
      (B.presheaf.map _
        ((Scheme.Modules.Hom.app τ (l ''ᵁ U)) x₃))
  rw [← hAx, hτx]
  let z : B.presheaf.obj (Opposite.op (p₂ ''ᵁ (l ''ᵁ U))) :=
    (Scheme.Modules.Hom.app τ (l ''ᵁ U)) x₃
  change B.presheaf.map _
      (B.presheaf.map _
        (B.presheaf.map _
          (B.presheaf.map _
            (B.presheaf.map _ (B.presheaf.map _ z))))) =
    B.presheaf.map _ (B.presheaf.map _ z)
  rw [← B.presheaf.map_comp_apply]
  rw [← B.presheaf.map_comp_apply]
  rw [← B.presheaf.map_comp_apply]
  rw [← B.presheaf.map_comp_apply]
  rw [← B.presheaf.map_comp_apply]
  rw [← B.presheaf.map_comp_apply]
  exact B.val.congr_map_apply (Subsingleton.elim _ _) z

private theorem openPullback_unit_mate
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₁] [IsOpenImmersion p₂]
    [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : Y.Modules) :
    ((Scheme.Modules.restrictAdjunction p₁).homEquiv
      ((Scheme.Modules.restrictFunctor f₁).obj M)
      ((Scheme.Modules.restrictFunctor p₂).obj
        ((Scheme.Modules.restrictFunctor f₂).obj M))).symm
        ((Scheme.Modules.restrictFunctor f₁).map
            ((Scheme.Modules.restrictAdjunction f₂).unit.app M) ≫
          (openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).hom.app
            ((Scheme.Modules.restrictFunctor f₂).obj M)) =
      (Scheme.Modules.restrictFunctorComp p₁ f₁).inv.app M ≫
        (Scheme.Modules.restrictFunctorCongr H.w).hom.app M ≫
          (Scheme.Modules.restrictFunctorComp p₂ f₂).hom.app M := by
  ext U x
  simp only [Adjunction.homEquiv_symm_apply, modules_comp_app,
    restrictFunctor_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    openPullbackRestrictPushforwardIso_hom_app,
    Scheme.Modules.restrict_map]
  change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _) x =
    (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _) x
  congr 1
  simp only [← Functor.map_comp]
  congr 1

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
      D.iso (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback P.p₂).app (D.obj j)).symm
  ((Scheme.Modules.restrictAdjunction P.p₁).homEquiv
      (D.obj i)
      ((Scheme.Modules.restrictFunctor P.p₂).obj (D.obj j)))
      transition.hom ≫
    (openPullbackRestrictPushforwardIso
      P.p₁ P.p₂ (cov.f i) (cov.f j) P.isPullback).inv.app (D.obj j)

/-- Untransposing a chart component across open base change recovers the specified overlap
transition. -/
private theorem compatibleFamilyChartComponent_adjunct
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    let P := overlap cov i j
    letI : IsOpenImmersion P.p₁ :=
      MorphismProperty.of_isPullback P.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f j))
    letI : IsOpenImmersion P.p₂ :=
      MorphismProperty.of_isPullback P.isPullback
        (inferInstance : IsOpenImmersion (cov.f i))
    ((Scheme.Modules.restrictAdjunction P.p₁).homEquiv
      (D.obj i) ((Scheme.Modules.restrictFunctor P.p₂).obj (D.obj j))).symm
        (compatibleFamilyChartComponent D i j ≫
          (openPullbackRestrictPushforwardIso
            P.p₁ P.p₂ (cov.f i) (cov.f j) P.isPullback).hom.app (D.obj j)) =
      ((Scheme.Modules.restrictFunctorIsoPullback P.p₁).app (D.obj i)).hom ≫
        (D.iso (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm ≪≫
          ((Scheme.Modules.restrictFunctorIsoPullback P.p₂).app (D.obj j)).symm).hom := by
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  let A := (Scheme.Modules.restrictAdjunction P.p₁).homEquiv
    (D.obj i) ((Scheme.Modules.restrictFunctor P.p₂).obj (D.obj j))
  let e := openPullbackRestrictPushforwardIso
    P.p₁ P.p₂ (cov.f i) (cov.f j) P.isPullback
  let d := ((Scheme.Modules.restrictFunctorIsoPullback P.p₁).app (D.obj i)).hom ≫
    (D.iso (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback P.p₂).app (D.obj j)).symm).hom
  change A.symm ((A d ≫ e.inv.app (D.obj j)) ≫ e.hom.app (D.obj j)) = d
  apply A.injective
  rw [Equiv.apply_symm_apply]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ A d ≫ z) (e.app (D.obj j)).inv_hom_id).trans
      (Category.comp_id _))

private theorem compatibleFamilyChartComponent_eq_transition
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    let P := overlap cov i j
    letI : IsOpenImmersion P.p₁ :=
      MorphismProperty.of_isPullback P.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f j))
    letI : IsOpenImmersion P.p₂ :=
      MorphismProperty.of_isPullback P.isPullback
        (inferInstance : IsOpenImmersion (cov.f i))
    compatibleFamilyChartComponent D i j =
      ((Scheme.Modules.restrictAdjunction P.p₁).homEquiv
        (D.obj i) ((Scheme.Modules.restrictFunctor P.p₂).obj (D.obj j)))
          (restrictionTransition D P.p P.p₁ P.p₂ P.hp₁ P.hp₂) ≫
        (openPullbackRestrictPushforwardIso
          P.p₁ P.p₂ (cov.f i) (cov.f j) P.isPullback).inv.app (D.obj j) := by
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  dsimp only [compatibleFamilyChartComponent, restrictionTransition]
  congr 2

private theorem compatibleFamilyChartComponent_mate
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀)
    {Z Q : Scheme} (a : Z ⟶ cov.X i) (q : Z ⟶ X)
    (ha : a ≫ cov.f i = q)
    (s : Q ⟶ Z) (r : Q ⟶ cov.X j)
    (HQ : IsPullback s r q (cov.f j))
    (l : Q ⟶ (overlap cov i j).pullback)
    (hl₁ : l ≫ (overlap cov i j).p₁ = s ≫ a)
    (hl₂ : l ≫ (overlap cov i j).p₂ = r)
    (HL : IsPullback l s (overlap cov i j).p₁ a)
    [IsOpenImmersion a] [IsOpenImmersion q]
    [IsOpenImmersion s] [IsOpenImmersion r] [IsOpenImmersion l] :
    let P := overlap cov i j
    letI : IsOpenImmersion P.p₁ :=
      MorphismProperty.of_isPullback P.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f j))
    letI : IsOpenImmersion P.p₂ :=
      MorphismProperty.of_isPullback P.isPullback
        (inferInstance : IsOpenImmersion (cov.f i))
    ((Scheme.Modules.restrictAdjunction s).homEquiv
      ((Scheme.Modules.restrictFunctor a).obj (D.obj i))
      ((Scheme.Modules.restrictFunctor r).obj (D.obj j))).symm
        ((Scheme.Modules.restrictFunctor a).map
            (compatibleFamilyChartComponent D i j) ≫
          (Scheme.Modules.restrictFunctorComp a (cov.f i)).inv.app
            ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) ≫
          (Scheme.Modules.restrictFunctorCongr ha).hom.app
            ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) ≫
          (openPullbackRestrictPushforwardIso
            s r q (cov.f j) HQ).hom.app (D.obj j)) =
      (Scheme.Modules.restrictFunctorComp s a).inv.app (D.obj i) ≫
        (Scheme.Modules.restrictFunctorCongr hl₁.symm).hom.app (D.obj i) ≫
        (Scheme.Modules.restrictFunctorComp l P.p₁).hom.app (D.obj i) ≫
        (Scheme.Modules.restrictFunctor l).map
          (restrictionTransition D P.p P.p₁ P.p₂ P.hp₁ P.hp₂) ≫
        (Scheme.Modules.restrictFunctorComp l P.p₂).inv.app (D.obj j) ≫
        (Scheme.Modules.restrictFunctorCongr hl₂).hom.app (D.obj j) := by
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  rw [compatibleFamilyChartComponent_eq_transition D i j]
  exact openPullback_chart_mate P.p₁ P.p₂ (cov.f i) (cov.f j)
    P.isPullback a q ha s r HQ l hl₁ hl₂ HL (D.obj i) (D.obj j)
    (restrictionTransition D P.p P.p₁ P.p₂ P.hp₁ P.hp₂)

private theorem compatibleFamilyChartComponent_mate_transition
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀)
    {Z Q : Scheme} (a : Z ⟶ cov.X i) (q : Z ⟶ X)
    (ha : a ≫ cov.f i = q)
    (s : Q ⟶ Z) (r : Q ⟶ cov.X j)
    (HQ : IsPullback s r q (cov.f j))
    (l : Q ⟶ (overlap cov i j).pullback)
    (hl₁ : l ≫ (overlap cov i j).p₁ = s ≫ a)
    (hl₂ : l ≫ (overlap cov i j).p₂ = r)
    (HL : IsPullback l s (overlap cov i j).p₁ a)
    [IsOpenImmersion a] [IsOpenImmersion q]
    [IsOpenImmersion s] [IsOpenImmersion r] [IsOpenImmersion l] :
    let P := overlap cov i j
    letI : IsOpenImmersion P.p₁ :=
      MorphismProperty.of_isPullback P.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f j))
    letI : IsOpenImmersion P.p₂ :=
      MorphismProperty.of_isPullback P.isPullback
        (inferInstance : IsOpenImmersion (cov.f i))
    ((Scheme.Modules.restrictAdjunction s).homEquiv
      ((Scheme.Modules.restrictFunctor a).obj (D.obj i))
      ((Scheme.Modules.restrictFunctor r).obj (D.obj j))).symm
        ((Scheme.Modules.restrictFunctor a).map
            (compatibleFamilyChartComponent D i j) ≫
          (Scheme.Modules.restrictFunctorComp a (cov.f i)).inv.app
            ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) ≫
          (Scheme.Modules.restrictFunctorCongr ha).hom.app
            ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) ≫
          (openPullbackRestrictPushforwardIso
            s r q (cov.f j) HQ).hom.app (D.obj j)) =
      (Scheme.Modules.restrictFunctorComp s a).inv.app (D.obj i) ≫
        restrictionTransition D (s ≫ q) (s ≫ a) r
          (by rw [Category.assoc, ha]) HQ.w.symm := by
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  rw [compatibleFamilyChartComponent_mate D i j a q ha s r HQ l hl₁ hl₂ HL]
  have hm := restrictionTransition_map D l P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  have hq : s ≫ q = l ≫ P.p := by
    calc
      s ≫ q = (s ≫ a) ≫ cov.f i := by rw [Category.assoc, ha]
      _ = (l ≫ P.p₁) ≫ cov.f i := by rw [hl₁]
      _ = l ≫ (P.p₁ ≫ cov.f i) := Category.assoc _ _ _
      _ = l ≫ P.p := by rw [P.hp₁]
  have ht := restrictionTransition_congr_all D (s ≫ q) (l ≫ P.p)
    (s ≫ a) (l ≫ P.p₁) r (l ≫ P.p₂) hq hl₁.symm hl₂.symm
    (by rw [Category.assoc, ha]) HQ.w.symm
    (by simp) (by simp)
  dsimp only [P] at hm ht ⊢
  slice_lhs 4 5 => rw [hm]
  let ci := Scheme.Modules.restrictFunctorComp l (overlap cov i j).p₁
  have hci : ci.hom.app (D.obj i) ≫ ci.inv.app (D.obj i) = 𝟙 _ :=
    ci.hom_inv_id_app (D.obj i)
  slice_lhs 3 4 => exact hci
  simp only [Category.id_comp]
  slice_lhs 2 4 => rw [ht]

private theorem compatibleFamilyChartComponent_cocycle
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j k : cov.I₀) :
    compatibleFamilyChartComponent D i j ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          ((Scheme.Modules.pushforward (cov.f j)).map
            (compatibleFamilyChartComponent D j k)) =
      compatibleFamilyChartComponent D i k ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          ((Scheme.Modules.restrictAdjunction (cov.f j)).unit.app
            ((Scheme.Modules.pushforward (cov.f k)).obj (D.obj k))) := by
  let Pij := overlap cov i j
  letI : IsOpenImmersion Pij.p₁ :=
    MorphismProperty.of_isPullback Pij.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion Pij.p₂ :=
    MorphismProperty.of_isPullback Pij.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let Mk : X.Modules := (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)
  let N : (cov.X j).Modules :=
    (Scheme.Modules.restrictFunctor (cov.f j)).obj Mk
  let BC := openPullbackRestrictPushforwardIso
    Pij.p₁ Pij.p₂ (cov.f i) (cov.f j) Pij.isPullback
  let BN : F.obj ((Scheme.Modules.pushforward (cov.f j)).obj N) ≅
      (Scheme.Modules.pushforward Pij.p₁).obj
        ((Scheme.Modules.restrictFunctor Pij.p₂).obj N) := BC.app N
  let Bj : F.obj ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) ≅
      (Scheme.Modules.pushforward Pij.p₁).obj
        ((Scheme.Modules.restrictFunctor Pij.p₂).obj (D.obj j)) :=
    BC.app (D.obj j)
  let A := (Scheme.Modules.restrictAdjunction Pij.p₁).homEquiv
    (D.obj i) ((Scheme.Modules.restrictFunctor Pij.p₂).obj N)
  let Aij := (Scheme.Modules.restrictAdjunction Pij.p₁).homEquiv
    (D.obj i) ((Scheme.Modules.restrictFunctor Pij.p₂).obj (D.obj j))
  let Au := (Scheme.Modules.restrictAdjunction Pij.p₁).homEquiv
    ((Scheme.Modules.restrictFunctor (cov.f i)).obj Mk)
    ((Scheme.Modules.restrictFunctor Pij.p₂).obj N)
  let τij := restrictionTransition D Pij.p Pij.p₁ Pij.p₂ Pij.hp₁ Pij.hp₂
  let K : (Scheme.Modules.restrictFunctor Pij.p₁).obj
        ((Scheme.Modules.restrictFunctor (cov.f i)).obj Mk) ⟶
      (Scheme.Modules.restrictFunctor Pij.p₂).obj N :=
    (Scheme.Modules.restrictFunctorComp Pij.p₁ (cov.f i)).inv.app Mk ≫
      (Scheme.Modules.restrictFunctorCongr Pij.condition).hom.app Mk ≫
      (Scheme.Modules.restrictFunctorComp Pij.p₂ (cov.f j)).hom.app Mk
  have hBCnat : F.map ((Scheme.Modules.pushforward (cov.f j)).map
        (compatibleFamilyChartComponent D j k)) ≫ BN.hom =
      Bj.hom ≫ (Scheme.Modules.pushforward Pij.p₁).map
        ((Scheme.Modules.restrictFunctor Pij.p₂).map
          (compatibleFamilyChartComponent D j k)) := by
    exact BC.hom.naturality (compatibleFamilyChartComponent D j k)
  have hAdjij : ((Scheme.Modules.restrictAdjunction Pij.p₁).homEquiv
      (D.obj i) ((Scheme.Modules.restrictFunctor Pij.p₂).obj (D.obj j))).symm
        (compatibleFamilyChartComponent D i j ≫ Bj.hom) = τij := by
    rw [compatibleFamilyChartComponent_eq_transition D i j]
    change Aij.symm ((Aij τij ≫ Bj.inv) ≫ Bj.hom) = τij
    calc
      _ = Aij.symm (Aij τij ≫ (Bj.inv ≫ Bj.hom)) :=
        congrArg Aij.symm (Category.assoc _ _ _)
      _ = Aij.symm (Aij τij ≫ 𝟙 _) := by rw [Bj.inv_hom_id]
      _ = Aij.symm (Aij τij) := congrArg Aij.symm (Category.comp_id _)
      _ = τij := Aij.symm_apply_apply τij
  have hL : A.symm
      ((compatibleFamilyChartComponent D i j ≫
        F.map ((Scheme.Modules.pushforward (cov.f j)).map
          (compatibleFamilyChartComponent D j k))) ≫ BN.hom) =
      τij ≫ (Scheme.Modules.restrictFunctor Pij.p₂).map
        (compatibleFamilyChartComponent D j k) := by
    let cjk := compatibleFamilyChartComponent D j k
    calc
      _ = A.symm (compatibleFamilyChartComponent D i j ≫
          (F.map ((Scheme.Modules.pushforward (cov.f j)).map cjk) ≫ BN.hom)) :=
        congrArg A.symm (Category.assoc _ _ _)
      _ = A.symm (compatibleFamilyChartComponent D i j ≫
          (Bj.hom ≫ (Scheme.Modules.pushforward Pij.p₁).map
            ((Scheme.Modules.restrictFunctor Pij.p₂).map cjk))) := by
        rw [hBCnat]
      _ = A.symm ((compatibleFamilyChartComponent D i j ≫ Bj.hom) ≫
          (Scheme.Modules.pushforward Pij.p₁).map
            ((Scheme.Modules.restrictFunctor Pij.p₂).map cjk)) :=
        congrArg A.symm (Category.assoc _ _ _).symm
      _ = Aij.symm (compatibleFamilyChartComponent D i j ≫ Bj.hom) ≫
          (Scheme.Modules.restrictFunctor Pij.p₂).map cjk :=
        (Scheme.Modules.restrictAdjunction Pij.p₁).homEquiv_naturality_right_symm
          (compatibleFamilyChartComponent D i j ≫ Bj.hom)
          ((Scheme.Modules.restrictFunctor Pij.p₂).map cjk)
      _ = _ := by rw [hAdjij]
  have hR : A.symm
      ((compatibleFamilyChartComponent D i k ≫
        F.map ((Scheme.Modules.restrictAdjunction (cov.f j)).unit.app Mk)) ≫
          BN.hom) =
      (Scheme.Modules.restrictFunctor Pij.p₁).map
          (compatibleFamilyChartComponent D i k) ≫ K := by
    have hunit : Au.symm
        (F.map ((Scheme.Modules.restrictAdjunction (cov.f j)).unit.app Mk) ≫
          BN.hom) = K := by
      exact openPullback_unit_mate Pij.p₁ Pij.p₂
        (cov.f i) (cov.f j) Pij.isPullback Mk
    let u := (Scheme.Modules.restrictAdjunction (cov.f j)).unit.app Mk
    calc
      _ = A.symm (compatibleFamilyChartComponent D i k ≫
          (F.map u ≫ BN.hom)) := congrArg A.symm (Category.assoc _ _ _)
      _ = (Scheme.Modules.restrictFunctor Pij.p₁).map
            (compatibleFamilyChartComponent D i k) ≫
          Au.symm (F.map u ≫ BN.hom) :=
        (Scheme.Modules.restrictAdjunction Pij.p₁).homEquiv_naturality_left_symm
          (compatibleFamilyChartComponent D i k) (F.map u ≫ BN.hom)
      _ = _ := by rw [hunit]
  have hcore : τij ≫ (Scheme.Modules.restrictFunctor Pij.p₂).map
        (compatibleFamilyChartComponent D j k) =
      (Scheme.Modules.restrictFunctor Pij.p₁).map
          (compatibleFamilyChartComponent D i k) ≫ K := by
    let Pjk := overlap cov j k
    let Pik := overlap cov i k
    let T := tripleOverlap cov i j k
    letI : IsOpenImmersion Pjk.p₁ :=
      MorphismProperty.of_isPullback Pjk.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f k))
    letI : IsOpenImmersion Pjk.p₂ :=
      MorphismProperty.of_isPullback Pjk.isPullback
        (inferInstance : IsOpenImmersion (cov.f j))
    letI : IsOpenImmersion Pik.p₁ :=
      MorphismProperty.of_isPullback Pik.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f k))
    letI : IsOpenImmersion Pik.p₂ :=
      MorphismProperty.of_isPullback Pik.isPullback
        (inferInstance : IsOpenImmersion (cov.f i))
    letI : IsOpenImmersion Pij.p := by
      rw [← Pij.hp₁]
      infer_instance
    letI : IsOpenImmersion T.p₁₂ :=
      MorphismProperty.of_isPullback T.isPullback₂.flip
        (inferInstance : IsOpenImmersion Pjk.p₁)
    letI : IsOpenImmersion T.p₂₃ :=
      MorphismProperty.of_isPullback T.isPullback₂
        (inferInstance : IsOpenImmersion Pij.p₂)
    letI : IsOpenImmersion T.p₁₃ :=
      MorphismProperty.of_isPullback T.isPullback₁
        (inferInstance : IsOpenImmersion Pij.p₁)
    letI : IsOpenImmersion T.p₃ := by
      rw [← T.p₂₃_p₃]
      infer_instance
    have HQ : IsPullback T.p₁₂ T.p₃ Pij.p (cov.f k) := by
      have h := T.isPullback₂.flip.paste_horiz Pjk.isPullback.flip
      simpa [T, Pjk, Pij] using h.flip
    let Rk : T.pullback.Modules :=
      (Scheme.Modules.restrictFunctor T.p₃).obj (D.obj k)
    let E : (Scheme.Modules.restrictFunctor Pij.p₂).obj N ≅
        (Scheme.Modules.pushforward T.p₁₂).obj Rk :=
      (Scheme.Modules.restrictFunctorComp Pij.p₂ (cov.f j)).symm.app Mk ≪≫
        (Scheme.Modules.restrictFunctorCongr Pij.hp₂).app Mk ≪≫
        (openPullbackRestrictPushforwardIso
          T.p₁₂ T.p₃ Pij.p (cov.f k) HQ).app (D.obj k)
    have hKE : K ≫ E.hom =
        (Scheme.Modules.restrictFunctorComp Pij.p₁ (cov.f i)).inv.app Mk ≫
          (Scheme.Modules.restrictFunctorCongr Pij.hp₁).hom.app Mk ≫
          (openPullbackRestrictPushforwardIso
            T.p₁₂ T.p₃ Pij.p (cov.f k) HQ).hom.app (D.obj k) := by
      change K ≫
          (Scheme.Modules.restrictFunctorComp Pij.p₂ (cov.f j)).inv.app Mk ≫
          (Scheme.Modules.restrictFunctorCongr Pij.hp₂).hom.app Mk ≫
          (openPullbackRestrictPushforwardIso
            T.p₁₂ T.p₃ Pij.p (cov.f k) HQ).hom.app (D.obj k) = _
      dsimp only [K]
      simp only [Category.assoc]
      slice_lhs 3 4 => rw [Iso.hom_inv_id_app]
      simp only [Category.id_comp]
      have hc := restrictFunctorCongr_hom_comp
        Pij.condition Pij.hp₂ Mk
      have hp : Pij.condition.trans Pij.hp₂ = Pij.hp₁ := Subsingleton.elim _ _
      rw [hp] at hc
      slice_lhs 2 3 => rw [hc]
    rw [← cancel_mono E.hom]
    let AS := (Scheme.Modules.restrictAdjunction T.p₁₂).homEquiv
      ((Scheme.Modules.restrictFunctor Pij.p₁).obj (D.obj i)) Rk
    have hjk := compatibleFamilyChartComponent_mate_transition D j k
      Pij.p₂ Pij.p Pij.hp₂ T.p₁₂ T.p₃ HQ T.p₂₃
      (T.p₂₃_p₂.trans T.p₁₂_p₂.symm) T.p₂₃_p₃ T.isPullback₂.flip
    have hmij := restrictionTransition_map D T.p₁₂
      Pij.p Pij.p₁ Pij.p₂ Pij.hp₁ Pij.hp₂
    have hcomp := restrictionTransition_comp D (T.p₁₂ ≫ Pij.p)
      (T.p₁₂ ≫ Pij.p₁) (T.p₁₂ ≫ Pij.p₂) T.p₃
      (by rw [Category.assoc, Pij.hp₁])
      (by rw [Category.assoc, Pij.hp₂]) HQ.w.symm
    have hleft : AS.symm
        ((τij ≫ (Scheme.Modules.restrictFunctor Pij.p₂).map
          (compatibleFamilyChartComponent D j k)) ≫ E.hom) =
        (Scheme.Modules.restrictFunctorComp T.p₁₂ Pij.p₁).inv.app (D.obj i) ≫
          restrictionTransition D (T.p₁₂ ≫ Pij.p)
            (T.p₁₂ ≫ Pij.p₁) T.p₃
              (by rw [Category.assoc, Pij.hp₁]) HQ.w.symm := by
      change AS.symm (τij ≫
        ((Scheme.Modules.restrictFunctor Pij.p₂).map
          (compatibleFamilyChartComponent D j k) ≫ E.hom)) = _
      rw [(Scheme.Modules.restrictAdjunction T.p₁₂).homEquiv_naturality_left_symm]
      change (Scheme.Modules.restrictFunctor T.p₁₂).map τij ≫
        ((Scheme.Modules.restrictAdjunction T.p₁₂).homEquiv
          ((Scheme.Modules.restrictFunctor Pij.p₂).obj (D.obj j)) Rk).symm
            ((Scheme.Modules.restrictFunctor Pij.p₂).map
                (compatibleFamilyChartComponent D j k) ≫
              (Scheme.Modules.restrictFunctorComp Pij.p₂ (cov.f j)).inv.app Mk ≫
              (Scheme.Modules.restrictFunctorCongr Pij.hp₂).hom.app Mk ≫
              (openPullbackRestrictPushforwardIso
                T.p₁₂ T.p₃ Pij.p (cov.f k) HQ).hom.app (D.obj k)) = _
      rw [hjk]
      slice_lhs 1 2 => rw [hmij]
      slice_lhs 2 3 => rw [hcomp]
    have hik := compatibleFamilyChartComponent_mate_transition D i k
      Pij.p₁ Pij.p Pij.hp₁ T.p₁₂ T.p₃ HQ T.p₁₃
      (T.p₁₃_p₁.trans T.p₁₂_p₁.symm) T.p₁₃_p₃ T.isPullback₁.flip
    have hright : AS.symm
        (((Scheme.Modules.restrictFunctor Pij.p₁).map
          (compatibleFamilyChartComponent D i k) ≫ K) ≫ E.hom) =
        (Scheme.Modules.restrictFunctorComp T.p₁₂ Pij.p₁).inv.app (D.obj i) ≫
          restrictionTransition D (T.p₁₂ ≫ Pij.p)
            (T.p₁₂ ≫ Pij.p₁) T.p₃
              (by rw [Category.assoc, Pij.hp₁]) HQ.w.symm := by
      rw [Category.assoc, hKE]
      simpa only [Category.assoc] using hik
    apply AS.symm.injective
    exact hleft.trans hright.symm
  have hpost :
      (compatibleFamilyChartComponent D i j ≫
        F.map ((Scheme.Modules.pushforward (cov.f j)).map
          (compatibleFamilyChartComponent D j k))) ≫ BN.hom =
      (compatibleFamilyChartComponent D i k ≫
        F.map ((Scheme.Modules.restrictAdjunction (cov.f j)).unit.app Mk)) ≫
          BN.hom := by
    apply A.symm.injective
    exact hL.trans (hcore.trans hR.symm)
  exact (cancel_mono BN.hom).mp hpost

private theorem restrictFunctorPreservesLimit
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {J : Type} [Category J] (K : J ⥤ X.Modules) :
    PreservesLimit K (Scheme.Modules.restrictFunctor f) := by
  constructor
  intro c hc
  constructor
  let hCreates : CreatesLimit (K ⋙ Scheme.Modules.restrictFunctor f)
      (SheafOfModules.forget.{u} Y.ringCatSheaf) :=
    SheafOfModules.createsLimit _
  let hRefl := hCreates.toReflectsLimit
  have hforget : IsLimit ((SheafOfModules.forget.{u} Y.ringCatSheaf).mapCone
      ((Scheme.Modules.restrictFunctor f).mapCone c)) := by
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    let KU := (K ⋙ Scheme.Modules.restrictFunctor f ⋙
      SheafOfModules.forget.{u} Y.ringCatSheaf) ⋙
        PresheafOfModules.evaluation _ U
    let hModRefl := ModuleCat.forget₂AddCommGroup_reflectsLimit KU
    apply Nonempty.some
    apply hModRefl.reflects
    let E := SheafOfModules.evaluation X.ringCatSheaf
      (Opposite.op (f ''ᵁ U.unop))
    let hPres : PreservesLimit K E := by
      apply SheafOfModules.evaluationPreservesLimit
    have hEval : IsLimit (E.mapCone c) := (hPres.preserves hc).some
    change IsLimit ((forget₂ (ModuleCat.{u} _) AddCommGrpCat).mapCone (E.mapCone c))
    let hGroupPres := ModuleCat.forget₂AddCommGroup_preservesLimit (K ⋙ E)
    exact (hGroupPres.preserves hEval).some
  exact (hRefl.reflects hforget).some

/-- The product of the direct images of all local modules in a descent datum. -/
noncomputable def compatibleFamilyAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  ∏ᶜ fun i ↦ (Scheme.Modules.pushforward (cov.f i)).obj (D.obj i)

/-- The local object on chart `i`, viewed as a compatible family in the restriction of the
ambient product to that chart. -/
noncomputable def compatibleFamilyChartAmbientHom
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    D.obj i ⟶
      (Scheme.Modules.restrictFunctor (cov.f i)).obj (compatibleFamilyAmbient D) := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let M : cov.I₀ → X.Modules := fun j ↦
    (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)
  let FM : cov.I₀ → (cov.X i).Modules := fun j ↦ F.obj (M j)
  let hM : HasProduct M := hasLimitOfHasLimitsOfShape _
  let hFM : HasProduct FM := hasLimitOfHasLimitsOfShape _
  let hPres : PreservesLimit (Discrete.functor M) F :=
    restrictFunctorPreservesLimit (cov.f i) (Discrete.functor M)
  let P := @piObj cov.I₀ X.Modules inferInstance M hM
  let FP := @piObj cov.I₀ (cov.X i).Modules inferInstance FM hFM
  let l : D.obj i ⟶ FP :=
    @Pi.lift cov.I₀ (cov.X i).Modules inferInstance FM hFM (D.obj i)
      (fun j ↦ compatibleFamilyChartComponent D i j)
  let e : F.obj P ≅ FP :=
    @PreservesProduct.iso X.Modules inferInstance (cov.X i).Modules inferInstance F cov.I₀ M
      hM hFM hPres
  change D.obj i ⟶ F.obj P
  exact l ≫ e.inv

/-- The `j`-th projection of the fixed-chart ambient family is the overlap component used to
construct it. -/
theorem compatibleFamilyChartAmbientHom_component
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyChartAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j) =
      compatibleFamilyChartComponent D i j := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let M : cov.I₀ → X.Modules := fun k ↦
    (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)
  let FM : cov.I₀ → (cov.X i).Modules := fun k ↦ F.obj (M k)
  let Di : (cov.X i).Modules := D.obj i
  let hM : HasProduct M := hasLimitOfHasLimitsOfShape _
  let hFM : HasProduct FM := hasLimitOfHasLimitsOfShape _
  let hPres : PreservesLimit (Discrete.functor M) F :=
    restrictFunctorPreservesLimit (cov.f i) (Discrete.functor M)
  let e : F.obj (@piObj cov.I₀ X.Modules inferInstance M hM) ≅
      @piObj cov.I₀ (cov.X i).Modules inferInstance FM hFM :=
    @PreservesProduct.iso X.Modules inferInstance (cov.X i).Modules inferInstance F cov.I₀ M
      hM hFM hPres
  let c : (k : cov.I₀) → Di ⟶ FM k := fun k ↦ compatibleFamilyChartComponent D i k
  let l : Di ⟶ @piObj cov.I₀ (cov.X i).Modules inferInstance FM hFM :=
    @Pi.lift cov.I₀ (cov.X i).Modules inferInstance FM hFM Di c
  have he : e.inv ≫ F.map (@Pi.π cov.I₀ X.Modules inferInstance M hM j) =
      @Pi.π cov.I₀ (cov.X i).Modules inferInstance FM hFM j := by
    rw [Iso.inv_comp_eq, PreservesProduct.iso_hom]
    exact (piComparison_comp_π F M j).symm
  change (l ≫ e.inv) ≫ F.map (@Pi.π cov.I₀ X.Modules inferInstance M hM j) = c j
  calc
    _ = l ≫ (e.inv ≫ F.map (@Pi.π cov.I₀ X.Modules inferInstance M hM j)) :=
      Category.assoc _ _ _
    _ = l ≫ @Pi.π cov.I₀ (cov.X i).Modules inferInstance FM hFM j := by
      simpa only [Category.assoc] using congrArg (fun q ↦ l ≫ q) he
    _ = c j := @Pi.lift_π (cov.X i).Modules inferInstance cov.I₀ FM hFM Di c j

/-- The product of the direct images of the restriction targets recording every ordered
pairwise compatibility equation. -/
noncomputable def compatibleFamilyOverlapAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  ∏ᶜ fun ij : cov.I₀ × cov.I₀ ↦
    (Scheme.Modules.pushforward (cov.f ij.1)).obj
      ((Scheme.Modules.restrictFunctor (cov.f ij.1)).obj
        ((Scheme.Modules.pushforward (cov.f ij.2)).obj (D.obj ij.2)))

/-- Restrict the first member of a local family to an overlap and transport it through the
descent isomorphism. -/
noncomputable def compatibleFamilyFirstComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbient D ⟶
      (Scheme.Modules.pushforward (cov.f i)).obj
        ((Scheme.Modules.restrictFunctor (cov.f i)).obj
          ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j))) :=
  Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) i ≫
    (Scheme.Modules.pushforward (cov.f i)).map
      (compatibleFamilyChartComponent D i j)

/-- Restrict the second member of a local family to an overlap, then identify the two equal
structural maps to the base. -/
noncomputable def compatibleFamilySecondComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbient D ⟶
      (Scheme.Modules.pushforward (cov.f i)).obj
        ((Scheme.Modules.restrictFunctor (cov.f i)).obj
          ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j))) :=
  Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j ≫
    (Scheme.Modules.restrictAdjunction (cov.f i)).unit.app
      ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j))

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

/-- The fixed-chart family satisfies the pairwise compatibility equations after restriction to
that chart. -/
theorem compatibleFamilyChartAmbientHom_condition
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyChartAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilyFirst D) =
      compatibleFamilyChartAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilySecond D) := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let N : cov.I₀ × cov.I₀ → X.Modules := fun jk ↦
    (Scheme.Modules.pushforward (cov.f jk.1)).obj
      ((Scheme.Modules.restrictFunctor (cov.f jk.1)).obj
        ((Scheme.Modules.pushforward (cov.f jk.2)).obj (D.obj jk.2)))
  let FN : cov.I₀ × cov.I₀ → (cov.X i).Modules := fun jk ↦ F.obj (N jk)
  let O : X.Modules := compatibleFamilyOverlapAmbient D
  let hN : HasProduct N := hasLimitOfHasLimitsOfShape _
  let hFN : HasProduct FN := hasLimitOfHasLimitsOfShape _
  let hPres : PreservesLimit (Discrete.functor N) F :=
    restrictFunctorPreservesLimit (cov.f i) (Discrete.functor N)
  let Di : (cov.X i).Modules := D.obj i
  let c : Di ⟶ F.obj (compatibleFamilyAmbient D) := compatibleFamilyChartAmbientHom D i
  let a : Di ⟶ F.obj O :=
    c ≫ F.map (compatibleFamilyFirst D)
  let b : Di ⟶ F.obj O :=
    c ≫ F.map (compatibleFamilySecond D)
  let p : (jk : cov.I₀ × cov.I₀) → O ⟶ N jk := fun jk ↦
    @Pi.π (cov.I₀ × cov.I₀) X.Modules inferInstance N hN jk
  let e : F.obj O ≅
      @piObj (cov.I₀ × cov.I₀) (cov.X i).Modules inferInstance FN hFN :=
    @PreservesProduct.iso X.Modules inferInstance (cov.X i).Modules inferInstance F
      (cov.I₀ × cov.I₀) N hN hFN hPres
  change a = b
  rw [← cancel_mono e.hom]
  apply Pi.hom_ext
  intro jk
  have hproj : e.hom ≫ @Pi.π (cov.I₀ × cov.I₀) (cov.X i).Modules inferInstance
      FN hFN jk = F.map (p jk) := by
    rw [PreservesProduct.iso_hom]
    exact piComparison_comp_π F N jk
  simp only [Category.assoc, hproj]
  dsimp only [a, b]
  simp only [Category.assoc]
  rw [← F.map_comp, ← F.map_comp]
  have hfirst : compatibleFamilyFirst D ≫ p jk =
      compatibleFamilyFirstComponent D jk.1 jk.2 := by
    exact Pi.lift_π _ jk
  have hsecond : compatibleFamilySecond D ≫ p jk =
      compatibleFamilySecondComponent D jk.1 jk.2 := by
    exact Pi.lift_π _ jk
  rw [hfirst, hsecond]
  let Mj : X.Modules := (Scheme.Modules.pushforward (cov.f jk.1)).obj (D.obj jk.1)
  let Mk : X.Modules := (Scheme.Modules.pushforward (cov.f jk.2)).obj (D.obj jk.2)
  let T : X.Modules := (Scheme.Modules.pushforward (cov.f jk.1)).obj
    ((Scheme.Modules.restrictFunctor (cov.f jk.1)).obj Mk)
  let qj : compatibleFamilyAmbient D ⟶ Mj :=
    Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) jk.1
  let qk : compatibleFamilyAmbient D ⟶ Mk :=
    Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) jk.2
  let t₁ : Mj ⟶ T :=
    (Scheme.Modules.pushforward (cov.f jk.1)).map
      (compatibleFamilyChartComponent D jk.1 jk.2)
  let t₂ : Mk ⟶ T :=
    (Scheme.Modules.restrictAdjunction (cov.f jk.1)).unit.app Mk
  have hfirstDef : compatibleFamilyFirstComponent D jk.1 jk.2 = qj ≫ t₁ := rfl
  have hsecondDef : compatibleFamilySecondComponent D jk.1 jk.2 = qk ≫ t₂ := rfl
  let dij : Di ⟶ F.obj Mj := compatibleFamilyChartComponent D i jk.1
  let dik : Di ⟶ F.obj Mk := compatibleFamilyChartComponent D i jk.2
  have hcj : c ≫ F.map qj = dij := by
    exact compatibleFamilyChartAmbientHom_component D i jk.1
  have hck : c ≫ F.map qk = dik := by
    exact compatibleFamilyChartAmbientHom_component D i jk.2
  rw [hfirstDef, hsecondDef]
  conv_lhs => rw [F.map_comp, ← Category.assoc, hcj]
  conv_rhs => rw [F.map_comp, ← Category.assoc, hck]
  exact compatibleFamilyChartComponent_cocycle D i jk.1 jk.2

private instance compatibleFamilyChartHasEqualizer
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    HasEqualizer
      ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilyFirst D))
      ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilySecond D)) :=
  hasLimitOfHasLimitsOfShape _

/-- The equalizer of the two compatibility maps after restricting them to one fixed chart. -/
noncomputable def compatibleFamilyChartObject
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (cov.X i).Modules :=
  equalizer
    ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilyFirst D))
    ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilySecond D))

/-- The fixed-chart compatible family, factored through the actual restricted equalizer. -/
noncomputable def compatibleFamilyChartObjectHom
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    D.obj i ⟶ compatibleFamilyChartObject D i := by
  letI := compatibleFamilyChartHasEqualizer D i
  dsimp only [compatibleFamilyChartObject]
  exact @equalizer.lift _ _ _ _ _ _
    (compatibleFamilyChartHasEqualizer D i) _
    (compatibleFamilyChartAmbientHom D i)
    (compatibleFamilyChartAmbientHom_condition D i)

/-- The chart-object factorization has the constructed ambient family as its equalizer
projection. -/
theorem compatibleFamilyChartObjectHom_comp_ι
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyChartObjectHom D i ≫
        equalizer.ι
          ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilyFirst D))
          ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilySecond D)) =
      compatibleFamilyChartAmbientHom D i := by
  letI := compatibleFamilyChartHasEqualizer D i
  dsimp only [compatibleFamilyChartObjectHom, compatibleFamilyChartObject]
  exact @equalizer.lift_ι _ _ _ _ _ _
    (compatibleFamilyChartHasEqualizer D i) _
    (compatibleFamilyChartAmbientHom D i)
    (compatibleFamilyChartAmbientHom_condition D i)

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
