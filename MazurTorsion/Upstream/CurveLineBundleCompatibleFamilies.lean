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
Its restriction to every member of the cover is identified with the specified local module, and
the resulting isomorphisms are proved to commute with the descent maps after arbitrary base
change.  This packages the equalizer as an `EffectiveModule` for every descent datum on an
`OpenCover.{0}`.
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

-- Pointwise form; the function-level lemma below is the canonical simp rule.
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

-- This alias is intentionally omitted from the simp set as redundant.
private theorem openPullbackRestrictPushforwardIso_app_hom_app
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens) :
    ((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).app M).hom.app W =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op := by
  rfl

-- Pointwise form; the function-level lemma below is the canonical simp rule.
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

-- This alias is intentionally omitted from the simp set as redundant.
private theorem openPullbackRestrictPushforwardIso_app_inv_app
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion p₂] [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens) :
    ((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).app M).inv.app W =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W).symm).op := by
  rfl

-- Pointwise form; the function-level lemma below is the canonical simp rule.
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

private theorem restrictionTransition_self
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f)
    {Y : Scheme} (q : Y ⟶ X) {i : cov.I₀}
    (a : Y ⟶ cov.X i) [IsOpenImmersion a]
    (ha : a ≫ cov.f i = q) :
    restrictionTransition D q a a ha ha = 𝟙 _ := by
  let e := Scheme.Modules.restrictFunctorIsoPullback a
  letI : IsIso ((Scheme.Modules.restrictFunctorIsoPullback a).hom.app (D.obj i)) :=
    ((Scheme.Modules.restrictFunctorIsoPullback a).app (D.obj i)).isIso_hom
  rw [← cancel_mono
    ((Scheme.Modules.restrictFunctorIsoPullback a).hom.app (D.obj i))]
  dsimp only [restrictionTransition]
  simp only [Category.assoc, Category.id_comp]
  rw [D.hom_self q a ha]
  change e.hom.app (D.obj i) ≫
      (𝟙 ((Scheme.Modules.pullback a).obj (D.obj i)) ≫ e.inv.app (D.obj i)) ≫
        e.hom.app (D.obj i) = e.hom.app (D.obj i)
  rw [Category.id_comp]
  exact e.hom_inv_id_app_assoc (D.obj i) _

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

private theorem compatibleFamilyChartComponent_self_counit
    {X : Scheme} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyChartComponent D i i ≫
        (Scheme.Modules.restrictAdjunction (cov.f i)).counit.app (D.obj i) =
      𝟙 _ := by
  let P := overlap cov i i
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f i))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  have hp : P.p₁ = P.p₂ := by
    rw [← cancel_mono (cov.f i)]
    exact P.condition
  have ht : restrictionTransition D P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
      (Scheme.Modules.restrictFunctorCongr hp).hom.app (D.obj i) := by
    have h := restrictionTransition_congr_all D P.p P.p
      P.p₁ P.p₁ P.p₂ P.p₁ rfl rfl hp.symm
      P.hp₁ P.hp₂ P.hp₁ P.hp₁
    have hr := restrictFunctorCongr_refl_hom P.p₁ (D.obj i)
    have hs := restrictionTransition_self D P.p P.p₁ P.hp₁
    rw [hr, hs] at h
    simpa only [Category.id_comp] using h.symm
  rw [compatibleFamilyChartComponent_eq_transition D i i, ht]
  let Di : (cov.X i).Modules := D.obj i
  change ((((Scheme.Modules.restrictAdjunction P.p₁).homEquiv
      Di ((Scheme.Modules.restrictFunctor P.p₂).obj Di))
        ((Scheme.Modules.restrictFunctorCongr hp).hom.app Di) ≫
      (openPullbackRestrictPushforwardIso
        P.p₁ P.p₂ (cov.f i) (cov.f i) P.isPullback).inv.app Di) ≫
      (Scheme.Modules.restrictAdjunction (cov.f i)).counit.app Di) = 𝟙 Di
  apply @Scheme.Modules.hom_ext (cov.X i) Di Di
  intro U
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.Hom.id_app, Adjunction.homEquiv_apply,
    Scheme.Modules.Hom.comp_app]
  ext x
  change Di.presheaf.obj (Opposite.op U) at x
  simp only [Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    openPullbackRestrictPushforwardIso_inv_app,
    Scheme.Modules.restrictAdjunction_counit_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    AddCommGrpCat.hom_id]
  change Di.presheaf.map _ (Di.presheaf.map _
    (Di.presheaf.map _ (Di.presheaf.map _ x))) = x
  rw [← Di.presheaf.map_comp_apply]
  rw [← Di.presheaf.map_comp_apply]
  rw [← Di.presheaf.map_comp_apply]
  calc
    _ = Di.presheaf.map (𝟙 _) x :=
      Di.val.congr_map_apply (Subsingleton.elim _ _) x
    _ = x := by simp

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

private theorem compatibleFamilyModule_component_condition
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
        compatibleFamilyFirstComponent D i j =
      equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
        compatibleFamilySecondComponent D i j := by
  let N : cov.I₀ × cov.I₀ → X.Modules := fun ij ↦
    (Scheme.Modules.pushforward (cov.f ij.1)).obj
      ((Scheme.Modules.restrictFunctor (cov.f ij.1)).obj
        ((Scheme.Modules.pushforward (cov.f ij.2)).obj (D.obj ij.2)))
  let q : compatibleFamilyOverlapAmbient D ⟶ N (i, j) :=
    Pi.π N (i, j)
  have h := congrArg (fun z ↦ z ≫ q) (compatibleFamilyModule_condition D)
  have hfirst : compatibleFamilyFirst D ≫ q =
      compatibleFamilyFirstComponent D i j := by
    exact Pi.lift_π _ (i, j)
  have hsecond : compatibleFamilySecond D ≫ q =
      compatibleFamilySecondComponent D i j := by
    exact Pi.lift_π _ (i, j)
  simpa only [Category.assoc, hfirst, hsecond] using h

/-- Restriction to one chart commutes with the compatible-family equalizer. -/
noncomputable def compatibleFamilyRestrictionEqualizerIso
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.restrictFunctor (cov.f i)).obj (compatibleFamilyModule D) ≅
      compatibleFamilyChartObject D i := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let a := compatibleFamilyFirst D
  let b := compatibleFamilySecond D
  letI : PreservesLimit (parallelPair a b) F :=
    restrictFunctorPreservesLimit (cov.f i) (parallelPair a b)
  change F.obj (equalizer a b) ≅ equalizer (F.map a) (F.map b)
  exact PreservesEqualizer.iso F a b

/-- The inverse equalizer comparison followed by the restricted global equalizer inclusion is the
local equalizer inclusion. -/
theorem compatibleFamilyRestrictionEqualizerIso_inv_comp_ι
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (compatibleFamilyRestrictionEqualizerIso D i).inv ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D)) =
      equalizer.ι
        ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilyFirst D))
        ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilySecond D)) := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let a := compatibleFamilyFirst D
  let b := compatibleFamilySecond D
  letI : PreservesLimit (parallelPair a b) F :=
    restrictFunctorPreservesLimit (cov.f i) (parallelPair a b)
  change (PreservesEqualizer.iso F a b).inv ≫ F.map (equalizer.ι a b) =
    equalizer.ι (F.map a) (F.map b)
  exact PreservesEqualizer.iso_inv_ι F a b

/-- The fixed-chart compatible family, regarded as a morphism into the restriction of the actual
global compatible-family equalizer. -/
noncomputable def compatibleFamilyChartToRestrictedModule
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    D.obj i ⟶
      (Scheme.Modules.restrictFunctor (cov.f i)).obj (compatibleFamilyModule D) :=
  compatibleFamilyChartObjectHom D i ≫
    (compatibleFamilyRestrictionEqualizerIso D i).inv

/-- The chart-to-global-restriction morphism has the originally constructed ambient family as its
image under the restricted global equalizer inclusion. -/
theorem compatibleFamilyChartToRestrictedModule_comp_ι
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyChartToRestrictedModule D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D)) =
      compatibleFamilyChartAmbientHom D i := by
  change (compatibleFamilyChartObjectHom D i ≫
      (compatibleFamilyRestrictionEqualizerIso D i).inv) ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D)) =
    compatibleFamilyChartAmbientHom D i
  calc
    _ = compatibleFamilyChartObjectHom D i ≫
        ((compatibleFamilyRestrictionEqualizerIso D i).inv ≫
          (Scheme.Modules.restrictFunctor (cov.f i)).map
            (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D))) :=
      Category.assoc _ _ _
    _ = compatibleFamilyChartObjectHom D i ≫
        equalizer.ι
          ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilyFirst D))
          ((Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilySecond D)) := by
      exact congrArg
        (fun z ↦ compatibleFamilyChartObjectHom D i ≫ z)
        (compatibleFamilyRestrictionEqualizerIso_inv_comp_ι D i)
    _ = compatibleFamilyChartAmbientHom D i :=
      compatibleFamilyChartObjectHom_comp_ι D i

/-- The compatible-family module projects to each pushed-forward local module. -/
noncomputable def compatibleFamilyProjection
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyModule D ⟶
      (Scheme.Modules.pushforward (cov.f i)).obj (D.obj i) :=
  equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
    Pi.π (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) i

/-- The adjoint transpose of the chart projection, stated with the genuine module pullback
functor used by `EffectiveModule`. -/
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

/-- The fixed-chart compatible family, transported from restriction to the genuine module
pullback. -/
noncomputable def compatibleFamilyRestrictionInverse
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    D.obj i ⟶
      (Scheme.Modules.pullback (cov.f i)).obj (compatibleFamilyModule D) :=
  compatibleFamilyChartToRestrictedModule D i ≫
    (Scheme.Modules.restrictFunctorIsoPullback (cov.f i)).hom.app
      (compatibleFamilyModule D)

private theorem compatibleFamilyRestrictedProjection_comp_component
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    ((Scheme.Modules.restrictFunctor (cov.f i)).map
        (compatibleFamilyProjection D i) ≫
      (Scheme.Modules.restrictAdjunction (cov.f i)).counit.app (D.obj i)) ≫
        compatibleFamilyChartComponent D i j =
      (Scheme.Modules.restrictFunctor (cov.f i)).map
        (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
          Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j) := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let R := Scheme.Modules.pushforward (cov.f i)
  let AR := Scheme.Modules.restrictAdjunction (cov.f i)
  let M : X.Modules := compatibleFamilyModule D
  let Di : (cov.X i).Modules := D.obj i
  let N : X.Modules := (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)
  let cij : Di ⟶ F.obj N := compatibleFamilyChartComponent D i j
  let pi : M ⟶ R.obj Di := compatibleFamilyProjection D i
  let pj : M ⟶ N :=
    equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
      Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j
  have hglobal : pi ≫ R.map cij = pj ≫ AR.unit.app N := by
    have h := compatibleFamilyModule_component_condition D i j
    dsimp only [compatibleFamilyFirstComponent,
      compatibleFamilySecondComponent] at h
    change pi ≫ R.map cij = pj ≫ AR.unit.app N at h
    exact h
  have hmap : F.map pi ≫ F.map (R.map cij) =
      F.map pj ≫ F.map (AR.unit.app N) := by
    simpa only [Functor.map_comp] using congrArg F.map hglobal
  have hcounit : F.map (R.map cij) ≫ AR.counit.app (F.obj N) =
      AR.counit.app Di ≫ cij := AR.counit.naturality cij
  have htriangle : F.map (AR.unit.app N) ≫ AR.counit.app (F.obj N) =
      𝟙 (F.obj N) := by
    simpa only [Functor.id_obj] using AR.left_triangle_components N
  change (F.map pi ≫ AR.counit.app Di) ≫ cij = F.map pj
  calc
    _ = F.map pi ≫ (AR.counit.app Di ≫ cij) := Category.assoc _ _ _
    _ = F.map pi ≫
        (F.map (R.map cij) ≫ AR.counit.app (F.obj N)) := by rw [hcounit]
    _ = (F.map pi ≫ F.map (R.map cij)) ≫ AR.counit.app (F.obj N) := by
      rw [Category.assoc]
    _ = (F.map pj ≫ F.map (AR.unit.app N)) ≫ AR.counit.app (F.obj N) := by
      rw [hmap]
    _ = F.map pj ≫
        (F.map (AR.unit.app N) ≫ AR.counit.app (F.obj N)) := Category.assoc _ _ _
    _ = F.map pj ≫ 𝟙 _ := by rw [htriangle]
    _ = F.map pj := Category.comp_id _

/-- Reconstructing a compatible family from its `i`-th component and then projecting back to that
component is the identity. -/
theorem compatibleFamilyRestrictionInverse_comp_hom
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyRestrictionInverse D i ≫
        compatibleFamilyRestrictionHom D i =
      𝟙 _ := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let P := Scheme.Modules.pullback (cov.f i)
  let R := Scheme.Modules.pushforward (cov.f i)
  let AR := Scheme.Modules.restrictAdjunction (cov.f i)
  let AP := Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)
  let e := Scheme.Modules.restrictFunctorIsoPullback (cov.f i)
  let M : X.Modules := compatibleFamilyModule D
  let Di : (cov.X i).Modules := D.obj i
  let p : M ⟶ R.obj Di := compatibleFamilyProjection D i
  let c : Di ⟶ F.obj M := compatibleFamilyChartToRestrictedModule D i
  have hnat : e.hom.app M ≫ P.map p = F.map p ≫ e.hom.app (R.obj Di) :=
    (e.hom.naturality p).symm
  have hcou : e.hom.app (R.obj Di) ≫ AP.counit.app Di = AR.counit.app Di := by
    dsimp only [e, AR, AP]
    exact Adjunction.leftAdjointUniq_hom_app_counit
      (Scheme.Modules.restrictAdjunction (cov.f i))
      (Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)) Di
  have hι : c ≫ F.map
        (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D)) =
      compatibleFamilyChartAmbientHom D i :=
    compatibleFamilyChartToRestrictedModule_comp_ι D i
  let π : compatibleFamilyAmbient D ⟶ R.obj Di :=
    Pi.π (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) i
  have hπ : compatibleFamilyChartAmbientHom D i ≫ F.map π =
      compatibleFamilyChartComponent D i i :=
    compatibleFamilyChartAmbientHom_component D i i
  have hproj : c ≫ F.map p = compatibleFamilyChartComponent D i i := by
    have hdecomp : c ≫ F.map p =
        (c ≫ F.map
          (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D))) ≫
            F.map π := by
      dsimp only [p, compatibleFamilyProjection, π]
      exact congrArg (fun z ↦ c ≫ z) (F.map_comp
        (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D))
        (Pi.π (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) i))
    have hlift :
        (c ≫ F.map
          (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D))) ≫
            F.map π =
          compatibleFamilyChartAmbientHom D i ≫ F.map π :=
      congrArg (fun z ↦ z ≫ F.map π) hι
    exact hdecomp.trans (hlift.trans hπ)
  have hproj_counit : (c ≫ F.map p) ≫ AR.counit.app Di =
      compatibleFamilyChartComponent D i i ≫ AR.counit.app Di :=
    congrArg (fun z ↦ z ≫ AR.counit.app Di) hproj
  have hself : compatibleFamilyChartComponent D i i ≫ AR.counit.app Di =
      𝟙 Di := compatibleFamilyChartComponent_self_counit D i
  change (c ≫ e.hom.app M) ≫
      (P.map p ≫ AP.counit.app Di) = 𝟙 Di
  calc
    _ = c ≫ (e.hom.app M ≫ P.map p) ≫ AP.counit.app Di := by
      simp only [Category.assoc]
    _ = c ≫ (F.map p ≫ e.hom.app (R.obj Di)) ≫ AP.counit.app Di := by
      rw [hnat]
    _ = c ≫ F.map p ≫ (e.hom.app (R.obj Di) ≫ AP.counit.app Di) := by
      simp only [Category.assoc]
    _ = (c ≫ F.map p) ≫ AR.counit.app Di := by
      rw [hcou, Category.assoc]
    _ = 𝟙 Di := hproj_counit.trans hself

/-- Projecting a restricted compatible family to its `i`-th component and reconstructing all
components gives the original restricted family. -/
theorem compatibleFamilyRestrictionHom_comp_inverse
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyRestrictionHom D i ≫
        compatibleFamilyRestrictionInverse D i =
      𝟙 _ := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let P := Scheme.Modules.pullback (cov.f i)
  let R := Scheme.Modules.pushforward (cov.f i)
  let AR := Scheme.Modules.restrictAdjunction (cov.f i)
  let AP := Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)
  let e := Scheme.Modules.restrictFunctorIsoPullback (cov.f i)
  let M : X.Modules := compatibleFamilyModule D
  let Di : (cov.X i).Modules := D.obj i
  let p : M ⟶ R.obj Di := compatibleFamilyProjection D i
  let r : P.obj M ⟶ Di := compatibleFamilyRestrictionHom D i
  let c : Di ⟶ F.obj M := compatibleFamilyChartToRestrictedModule D i
  let q : M ⟶ compatibleFamilyAmbient D :=
    equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D)
  let a : Di ⟶ F.obj (compatibleFamilyAmbient D) :=
    compatibleFamilyChartAmbientHom D i
  have hnat : e.hom.app M ≫ P.map p = F.map p ≫ e.hom.app (R.obj Di) :=
    (e.hom.naturality p).symm
  have hcou : e.hom.app (R.obj Di) ≫ AP.counit.app Di = AR.counit.app Di := by
    dsimp only [e, AR, AP]
    exact Adjunction.leftAdjointUniq_hom_app_counit
      (Scheme.Modules.restrictAdjunction (cov.f i))
      (Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)) Di
  have hr : e.hom.app M ≫ r = F.map p ≫ AR.counit.app Di := by
    change e.hom.app M ≫ (P.map p ≫ AP.counit.app Di) =
      F.map p ≫ AR.counit.app Di
    calc
      _ = (e.hom.app M ≫ P.map p) ≫ AP.counit.app Di := by
        rw [Category.assoc]
      _ = (F.map p ≫ e.hom.app (R.obj Di)) ≫ AP.counit.app Di := by
        rw [hnat]
      _ = F.map p ≫ (e.hom.app (R.obj Di) ≫ AP.counit.app Di) :=
        Category.assoc _ _ _
      _ = F.map p ≫ AR.counit.app Di := by rw [hcou]
  have hambient : (e.hom.app M ≫ r) ≫ a = F.map q := by
    letI : PreservesLimit
        (Discrete.functor
          (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j))) F :=
      restrictFunctorPreservesLimit (cov.f i)
        (Discrete.functor
          (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)))
    let prodIso : F.obj (compatibleFamilyAmbient D) ≅
        ∏ᶜ fun j ↦ F.obj
          ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) := by
      change F.obj
          (∏ᶜ fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j)) ≅
        ∏ᶜ fun j ↦ F.obj
          ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j))
      exact PreservesProduct.iso F
        (fun j ↦ (Scheme.Modules.pushforward (cov.f j)).obj (D.obj j))
    apply (cancel_mono prodIso.hom).mp
    apply Pi.hom_ext
    intro j
    have hprod : prodIso.hom ≫
        Pi.π (fun j ↦ F.obj
          ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j))) j =
      F.map (Pi.π
        (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j) := by
      change (PreservesProduct.iso F
          (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k))).hom ≫
          Pi.π (fun j ↦ F.obj
            ((Scheme.Modules.pushforward (cov.f j)).obj (D.obj j))) j =
        F.map (Pi.π
          (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j)
      rw [PreservesProduct.iso_hom]
      exact piComparison_comp_π F
        (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j
    simp only [Category.assoc, hprod]
    have hc := compatibleFamilyChartAmbientHom_component D i j
    have hrec := compatibleFamilyRestrictedProjection_comp_component D i j
    change (e.hom.app M ≫ r) ≫
        (a ≫ F.map (Pi.π
          (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j)) =
      F.map q ≫ F.map (Pi.π
        (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j)
    have hc' : a ≫ F.map (Pi.π
          (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j) =
        compatibleFamilyChartComponent D i j := by
      change compatibleFamilyChartAmbientHom D i ≫
          (Scheme.Modules.restrictFunctor (cov.f i)).map
            (Pi.π (fun k ↦
              (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j) =
        compatibleFamilyChartComponent D i j
      exact hc
    have hrec' : (F.map p ≫ AR.counit.app Di) ≫
          compatibleFamilyChartComponent D i j =
        F.map (q ≫ Pi.π
          (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j) := by
      simpa only [q, F, p, AR, Di, M, compatibleFamilyModule] using hrec
    rw [hc', hr, hrec']
    exact F.map_comp q
      (Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j)
  have hmono : Mono (F.map q) := by
    letI : PreservesLimit
        (parallelPair (compatibleFamilyFirst D) (compatibleFamilySecond D)) F :=
      restrictFunctorPreservesLimit (cov.f i)
        (parallelPair (compatibleFamilyFirst D) (compatibleFamilySecond D))
    dsimp only [q, M, compatibleFamilyModule]
    rw [← equalizerComparison_comp_π
      (compatibleFamilyFirst D) (compatibleFamilySecond D) F]
    infer_instance
  letI : Mono (F.map q) := hmono
  have hcι : c ≫ F.map q = a := by
    dsimp only [c, q, a, F, Di, M]
    exact compatibleFamilyChartToRestrictedModule_comp_ι D i
  have hF : (e.hom.app M ≫ r) ≫ c = 𝟙 (F.obj M) := by
    apply (cancel_mono (F.map q)).mp
    calc
      _ = (e.hom.app M ≫ r) ≫ (c ≫ F.map q) := by
        rw [Category.assoc]
      _ = (e.hom.app M ≫ r) ≫ a := by
        rw [hcι]
      _ = F.map q := hambient
      _ = 𝟙 (F.obj M) ≫ F.map q :=
        (Category.id_comp _).symm
  letI : IsIso (e.hom.app M) := (e.app M).isIso_hom
  rw [← cancel_epi (e.hom.app M)]
  change e.hom.app M ≫ (r ≫ (c ≫ e.hom.app M)) =
    e.hom.app M ≫ 𝟙 (P.obj M)
  calc
    _ = ((e.hom.app M ≫ r) ≫ c) ≫ e.hom.app M := by
      simp only [Category.assoc]
    _ = 𝟙 (F.obj M) ≫ e.hom.app M := by rw [hF]
    _ = e.hom.app M := Category.id_comp _
    _ = e.hom.app M ≫ 𝟙 (P.obj M) := (Category.comp_id _).symm

/-- The compatible-family equalizer restricts to the prescribed module on each chart.

This is the pointwise restriction isomorphism used below to construct the full descent-data
isomorphism.  Its compatibility with `DescentData.hom` after arbitrary base change is supplied by
`compatibleFamilyDescentIso`. -/
noncomputable def compatibleFamilyRestrictionIso
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).obj (compatibleFamilyModule D) ≅ D.obj i where
  hom := compatibleFamilyRestrictionHom D i
  inv := compatibleFamilyRestrictionInverse D i
  hom_inv_id := compatibleFamilyRestrictionHom_comp_inverse D i
  inv_hom_id := compatibleFamilyRestrictionInverse_comp_hom D i

@[simp]
theorem compatibleFamilyRestrictionIso_hom
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (compatibleFamilyRestrictionIso D i).hom = compatibleFamilyRestrictionHom D i :=
  rfl

@[simp]
theorem compatibleFamilyRestrictionIso_inv
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (compatibleFamilyRestrictionIso D i).inv = compatibleFamilyRestrictionInverse D i :=
  rfl

private theorem modulesPseudofunctor_mapComp'_inv_app
    {X Y Z : Scheme.{u}} (b : X ⟶ Y) (a : Y ⟶ Z)
    (c : X ⟶ Z) (h : b ≫ a = c) (M : Z.Modules) :
    (modulesPseudofunctor.mapComp'
      a.op.toLoc b.op.toLoc c.op.toLoc (by cases h; rfl)).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackComp b a).hom.app M ≫
        (Scheme.Modules.pullbackCongr h).hom.app M := by
  subst c
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom]
  change (modulesPseudofunctor.mapComp'
      a.op.toLoc b.op.toLoc (a.op.toLoc ≫ b.op.toLoc) _).inv.toNatTrans.app M = _
  calc
    _ = (modulesPseudofunctor.mapComp a.op.toLoc b.op.toLoc).inv.toNatTrans.app M := by
      simpa only [] using congrArg (fun e ↦ e.inv.toNatTrans.app M)
        (modulesPseudofunctor.mapComp'_eq_mapComp a.op.toLoc b.op.toLoc)
    _ = _ := by
      unfold modulesPseudofunctor
      rw [Pseudofunctor.comp_mapComp]
      dsimp
      exact congrArg (fun k ↦ k.toNatTrans.app M)
        (Scheme.Modules.pseudofunctor_mapComp_inv_τl a.op.toLoc b.op.toLoc)

private theorem modulesPseudofunctor_mapComp'_hom_app
    {X Y Z : Scheme.{u}} (b : X ⟶ Y) (a : Y ⟶ Z)
    (c : X ⟶ Z) (h : b ≫ a = c) (M : Z.Modules) :
    (modulesPseudofunctor.mapComp'
      a.op.toLoc b.op.toLoc c.op.toLoc (by cases h; rfl)).hom.toNatTrans.app M =
      (Scheme.Modules.pullbackCongr h).inv.app M ≫
        (Scheme.Modules.pullbackComp b a).inv.app M := by
  subst c
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv]
  change (modulesPseudofunctor.mapComp'
      a.op.toLoc b.op.toLoc (a.op.toLoc ≫ b.op.toLoc) _).hom.toNatTrans.app M = _
  calc
    _ = (modulesPseudofunctor.mapComp a.op.toLoc b.op.toLoc).hom.toNatTrans.app M := by
      simpa only [] using congrArg (fun e ↦ e.hom.toNatTrans.app M)
        (modulesPseudofunctor.mapComp'_eq_mapComp a.op.toLoc b.op.toLoc)
    _ = _ := by
      unfold modulesPseudofunctor
      rw [Pseudofunctor.comp_mapComp]
      dsimp
      exact congrArg (fun k ↦ k.toNatTrans.app M)
        (Scheme.Modules.pseudofunctor_mapComp_hom_τl a.op.toLoc b.op.toLoc)

private theorem pullbackCongr_refl_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (h : f = f) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ := by
  cases Subsingleton.elim h rfl
  rfl

private theorem restrictFunctorIsoPullback_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [hf : IsOpenImmersion f] [hg : IsOpenImmersion g] (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback g).hom.app M =
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫
        (Scheme.Modules.pullbackCongr h).hom.app M := by
  subst g
  cases Subsingleton.elim hf hg
  rw [restrictFunctorCongr_refl_hom]
  rw [pullbackCongr_refl_hom]
  simp

private theorem pullbackCongr_symm_inv
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h.symm).inv.app M =
      (Scheme.Modules.pullbackCongr h).hom.app M := by
  subst g
  rfl

private theorem compatibleFamilyRestrictionHom_from_restriction
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.restrictFunctorIsoPullback (cov.f i)).hom.app
          (compatibleFamilyModule D) ≫
        compatibleFamilyRestrictionHom D i =
      (Scheme.Modules.restrictFunctor (cov.f i)).map
          (compatibleFamilyProjection D i) ≫
        (Scheme.Modules.restrictAdjunction (cov.f i)).counit.app (D.obj i) := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  let P := Scheme.Modules.pullback (cov.f i)
  let AR := Scheme.Modules.restrictAdjunction (cov.f i)
  let AP := Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)
  let e := Scheme.Modules.restrictFunctorIsoPullback (cov.f i)
  let M : X.Modules := compatibleFamilyModule D
  let Di : (cov.X i).Modules := D.obj i
  let p : M ⟶ (Scheme.Modules.pushforward (cov.f i)).obj Di :=
    compatibleFamilyProjection D i
  have hnat : e.hom.app M ≫ P.map p =
      F.map p ≫ e.hom.app ((Scheme.Modules.pushforward (cov.f i)).obj Di) :=
    (e.hom.naturality p).symm
  have hcou : e.hom.app ((Scheme.Modules.pushforward (cov.f i)).obj Di) ≫
      AP.counit.app Di = AR.counit.app Di := by
    dsimp only [e, AR, AP]
    exact Adjunction.leftAdjointUniq_hom_app_counit
      (Scheme.Modules.restrictAdjunction (cov.f i))
      (Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)) Di
  change e.hom.app M ≫ (P.map p ≫ AP.counit.app Di) =
    F.map p ≫ AR.counit.app Di
  rw [← Category.assoc, hnat, Category.assoc, hcou]

private theorem compatibleFamilyRestrictionHom_comp_chartComponent
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    ((Scheme.Modules.restrictFunctorIsoPullback (cov.f i)).hom.app
          (compatibleFamilyModule D) ≫
        compatibleFamilyRestrictionHom D i) ≫
      compatibleFamilyChartComponent D i j =
    (Scheme.Modules.restrictFunctor (cov.f i)).map
      (compatibleFamilyProjection D j) := by
  rw [compatibleFamilyRestrictionHom_from_restriction D i]
  change (((Scheme.Modules.restrictFunctor (cov.f i)).map
          (compatibleFamilyProjection D i) ≫
        (Scheme.Modules.restrictAdjunction (cov.f i)).counit.app (D.obj i)) ≫
      compatibleFamilyChartComponent D i j) =
    (Scheme.Modules.restrictFunctor (cov.f i)).map
      (equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
        Pi.π (fun k ↦ (Scheme.Modules.pushforward (cov.f k)).obj (D.obj k)) j)
  exact compatibleFamilyRestrictedProjection_comp_component D i j

/-
This is the central overlap-coherence calculation for the compatible-family
construction.  The local notation separates the restrictions, pushforwards,
adjunctions, and base-change comparison that occur in the square.

The proof reduces the comparison to three naturality statements:

* `hAdj` identifies the chart transition with the adjoint of its component;
* `hBC` moves the restricted projection through open base change;
* `hunit` identifies the adjoint of the unit with the restriction comparison.

The two projection equations connect those statements to the compatible-family
equalizer.  Naturality of the adjunction equivalence then transports the left
projection into the overlap and the right projection back out of it.

Once these ingredients are in place, the desired equality is only reassociation
and rewriting.  Keeping that final argument as directed rewrites shares the
large categorical expressions instead of restating every intermediate morphism
as a separate equality in a calculation chain.

This formulation is also easier to audit: every rewrite below corresponds to
one of the named coherence facts above, and no additional categorical identity
is hidden in broad simplification.
-/
private theorem compatibleFamilyRestrictionHom_comm_restriction
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    let P := overlap cov i j
    letI : IsOpenImmersion P.p₁ :=
      MorphismProperty.of_isPullback P.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f j))
    letI : IsOpenImmersion P.p₂ :=
      MorphismProperty.of_isPullback P.isPullback
        (inferInstance : IsOpenImmersion (cov.f i))
    (Scheme.Modules.restrictFunctor P.p₁).map
        ((Scheme.Modules.restrictFunctorIsoPullback (cov.f i)).hom.app
            (compatibleFamilyModule D) ≫
          compatibleFamilyRestrictionHom D i) ≫
      restrictionTransition D (P.p₁ ≫ cov.f i) P.p₁ P.p₂
        rfl P.condition.symm =
    ((Scheme.Modules.restrictFunctorComp P.p₁ (cov.f i)).inv.app
          (compatibleFamilyModule D) ≫
        (Scheme.Modules.restrictFunctorCongr P.condition).hom.app
          (compatibleFamilyModule D) ≫
        (Scheme.Modules.restrictFunctorComp P.p₂ (cov.f j)).hom.app
          (compatibleFamilyModule D)) ≫
      (Scheme.Modules.restrictFunctor P.p₂).map
        ((Scheme.Modules.restrictFunctorIsoPullback (cov.f j)).hom.app
            (compatibleFamilyModule D) ≫
          compatibleFamilyRestrictionHom D j) := by
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  let Ri := Scheme.Modules.restrictFunctor (cov.f i)
  let Rj := Scheme.Modules.restrictFunctor (cov.f j)
  let R₁ := Scheme.Modules.restrictFunctor P.p₁
  let R₂ := Scheme.Modules.restrictFunctor P.p₂
  let Sj := Scheme.Modules.pushforward (cov.f j)
  let S₁ := Scheme.Modules.pushforward P.p₁
  let Aj := Scheme.Modules.restrictAdjunction (cov.f j)
  let A₁ := Scheme.Modules.restrictAdjunction P.p₁
  let M : X.Modules := compatibleFamilyModule D
  let Di : (cov.X i).Modules := D.obj i
  let Dj : (cov.X j).Modules := D.obj j
  let hi : Ri.obj M ⟶ Di :=
    (Scheme.Modules.restrictFunctorIsoPullback (cov.f i)).hom.app M ≫
      compatibleFamilyRestrictionHom D i
  let hj : Rj.obj M ⟶ Dj :=
    (Scheme.Modules.restrictFunctorIsoPullback (cov.f j)).hom.app M ≫
      compatibleFamilyRestrictionHom D j
  let cij : Di ⟶ Ri.obj (Sj.obj Dj) := compatibleFamilyChartComponent D i j
  let B := openPullbackRestrictPushforwardIso
    P.p₁ P.p₂ (cov.f i) (cov.f j) P.isPullback
  let K : R₁.obj (Ri.obj M) ⟶ R₂.obj (Rj.obj M) :=
    (Scheme.Modules.restrictFunctorComp P.p₁ (cov.f i)).inv.app M ≫
      (Scheme.Modules.restrictFunctorCongr P.condition).hom.app M ≫
      (Scheme.Modules.restrictFunctorComp P.p₂ (cov.f j)).hom.app M
  let T : R₁.obj Di ⟶ R₂.obj Dj :=
    restrictionTransition D (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm
  let A := A₁.homEquiv Di (R₂.obj Dj)
  let Ah := A₁.homEquiv (Ri.obj M) (R₂.obj Dj)
  let Au := A₁.homEquiv (Ri.obj M) (R₂.obj (Rj.obj M))
  have hAdj : A.symm (cij ≫ B.hom.app Dj) = T := by
    have h := compatibleFamilyChartComponent_adjunct D i j
    change ((Scheme.Modules.restrictAdjunction P.p₁).homEquiv
        (D.obj i) ((Scheme.Modules.restrictFunctor P.p₂).obj (D.obj j))).symm
          (compatibleFamilyChartComponent D i j ≫ B.hom.app (D.obj j)) =
      (Scheme.Modules.restrictFunctorIsoPullback P.p₁).hom.app (D.obj i) ≫
        D.hom (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm ≫
        (Scheme.Modules.restrictFunctorIsoPullback P.p₂).inv.app (D.obj j) at h
    simpa only [A, A₁, cij, B, T, restrictionTransition,
      Category.assoc] using h
  have hunit : Au.symm (Ri.map (Aj.unit.app M) ≫ B.hom.app (Rj.obj M)) = K := by
    simpa only [Au, A₁, Ri, Rj, Aj, B, K, Category.assoc] using
      openPullback_unit_mate P.p₁ P.p₂
        (cov.f i) (cov.f j) P.isPullback M
  have hhi : hi ≫ cij = Ri.map (compatibleFamilyProjection D j) := by
    simpa only [hi, cij, Ri, Di, Dj, M] using
      compatibleFamilyRestrictionHom_comp_chartComponent D i j
  have hhj : Aj.homEquiv M Dj hj = compatibleFamilyProjection D j := by
    dsimp only [hj, Aj, M, Dj, Rj]
    rw [compatibleFamilyRestrictionHom_from_restriction D j]
    exact ((Scheme.Modules.restrictAdjunction (cov.f j)).homEquiv
      (compatibleFamilyModule D) (D.obj j)).apply_symm_apply
        (compatibleFamilyProjection D j)
  have hBC := (B.hom.naturality hj).symm
  change B.hom.app (Rj.obj M) ≫ S₁.map (R₂.map hj) =
    Ri.map (Sj.map hj) ≫ B.hom.app Dj at hBC
  change R₁.map hi ≫ T = K ≫ R₂.map hj
  rw [← hAdj]
  rw [(A₁.homEquiv_naturality_left_symm hi
    (cij ≫ B.hom.app Dj)).symm]
  rw [← Category.assoc, hhi, ← hhj, Adjunction.homEquiv_apply,
    Ri.map_comp, Category.assoc, ← hBC, ← Category.assoc]
  rw [A₁.homEquiv_naturality_right_symm, hunit]

private theorem compatibleFamilyOfObjTransition_from_restriction
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    let P := overlap cov i j
    letI : IsOpenImmersion P.p₁ :=
      MorphismProperty.of_isPullback P.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f j))
    letI : IsOpenImmersion P.p₂ :=
      MorphismProperty.of_isPullback P.isPullback
        (inferInstance : IsOpenImmersion (cov.f i))
    ((Scheme.Modules.restrictFunctor P.p₁).map
          ((Scheme.Modules.restrictFunctorIsoPullback (cov.f i)).hom.app
            (compatibleFamilyModule D)) ≫
        (Scheme.Modules.restrictFunctorIsoPullback P.p₁).hom.app
          ((Scheme.Modules.pullback (cov.f i)).obj (compatibleFamilyModule D))) ≫
      ((modulesPseudofunctor.toDescentData cov.f).obj
          (compatibleFamilyModule D)).hom
        (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm =
    ((Scheme.Modules.restrictFunctorComp P.p₁ (cov.f i)).inv.app
          (compatibleFamilyModule D) ≫
        (Scheme.Modules.restrictFunctorCongr P.condition).hom.app
          (compatibleFamilyModule D) ≫
        (Scheme.Modules.restrictFunctorComp P.p₂ (cov.f j)).hom.app
          (compatibleFamilyModule D)) ≫
      ((Scheme.Modules.restrictFunctor P.p₂).map
          ((Scheme.Modules.restrictFunctorIsoPullback (cov.f j)).hom.app
            (compatibleFamilyModule D)) ≫
        (Scheme.Modules.restrictFunctorIsoPullback P.p₂).hom.app
          ((Scheme.Modules.pullback (cov.f j)).obj (compatibleFamilyModule D))) := by
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  let M : X.Modules := compatibleFamilyModule D
  let ei := Scheme.Modules.restrictFunctorIsoPullback (cov.f i)
  let ej := Scheme.Modules.restrictFunctorIsoPullback (cov.f j)
  let e₁ := Scheme.Modules.restrictFunctorIsoPullback P.p₁
  let e₂ := Scheme.Modules.restrictFunctorIsoPullback P.p₂
  let ci := Scheme.Modules.restrictFunctorComp P.p₁ (cov.f i)
  let cj := Scheme.Modules.restrictFunctorComp P.p₂ (cov.f j)
  let pi := Scheme.Modules.pullbackComp P.p₁ (cov.f i)
  let pj := Scheme.Modules.pullbackComp P.p₂ (cov.f j)
  let er := Scheme.Modules.restrictFunctorCongr P.condition
  let ep := Scheme.Modules.pullbackCongr P.condition
  let L := (Scheme.Modules.restrictFunctor P.p₁).map (ei.hom.app M) ≫
    e₁.hom.app ((Scheme.Modules.pullback (cov.f i)).obj M)
  let R := (Scheme.Modules.restrictFunctor P.p₂).map (ej.hom.app M) ≫
    e₂.hom.app ((Scheme.Modules.pullback (cov.f j)).obj M)
  let K := ci.inv.app M ≫ er.hom.app M ≫ cj.hom.app M
  have hs : ((modulesPseudofunctor.toDescentData cov.f).obj M).hom
        (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm =
      pi.hom.app M ≫ ep.hom.app M ≫ pj.inv.app M := by
    change (modulesPseudofunctor.mapComp'
          (cov.f i).op.toLoc P.p₁.op.toLoc
          (P.p₁ ≫ cov.f i).op.toLoc _).inv.toNatTrans.app M ≫
        (modulesPseudofunctor.mapComp'
          (cov.f j).op.toLoc P.p₂.op.toLoc
          (P.p₁ ≫ cov.f i).op.toLoc _).hom.toNatTrans.app M = _
    rw [modulesPseudofunctor_mapComp'_inv_app
      P.p₁ (cov.f i) (P.p₁ ≫ cov.f i) rfl M]
    rw [modulesPseudofunctor_mapComp'_hom_app
      P.p₂ (cov.f j) (P.p₁ ≫ cov.f i) P.condition.symm M]
    rw [pullbackCongr_symm_inv P.condition M]
    rfl
  have hci := restrictFunctorIsoPullback_comp P.p₁ (cov.f i) M
  have hcj := restrictFunctorIsoPullback_comp P.p₂ (cov.f j) M
  have hcongr := restrictFunctorIsoPullback_congr P.condition M
  change L ≫
      ((modulesPseudofunctor.toDescentData cov.f).obj M).hom
        (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm = K ≫ R
  rw [hs]
  have hleft : L ≫ pi.hom.app M = ci.inv.app M ≫
      (Scheme.Modules.restrictFunctorIsoPullback
        (P.p₁ ≫ cov.f i)).hom.app M := by
    rw [← cancel_epi (ci.hom.app M)]
    simpa only [L, ci, ei, e₁, pi, Category.assoc,
      Iso.hom_inv_id_app_assoc] using hci.symm
  have hright :
      (Scheme.Modules.restrictFunctorIsoPullback
          (P.p₂ ≫ cov.f j)).hom.app M ≫ pj.inv.app M =
        cj.hom.app M ≫ R := by
    rw [hcj]
    simp only [R, cj, ej, e₂, pj, Category.assoc]
    slice_lhs 4 5 => rw [Iso.hom_inv_id_app]
    simp
  calc
    L ≫ (pi.hom.app M ≫ ep.hom.app M ≫ pj.inv.app M) =
        (L ≫ pi.hom.app M) ≫ ep.hom.app M ≫ pj.inv.app M := by
      simp only [Category.assoc]
    _ = (ci.inv.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback
            (P.p₁ ≫ cov.f i)).hom.app M) ≫
        ep.hom.app M ≫ pj.inv.app M := by rw [hleft]
    _ = ci.inv.app M ≫
        ((Scheme.Modules.restrictFunctorIsoPullback
            (P.p₁ ≫ cov.f i)).hom.app M ≫ ep.hom.app M) ≫
          pj.inv.app M := by simp only [Category.assoc]
    _ = ci.inv.app M ≫
        (er.hom.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback
            (P.p₂ ≫ cov.f j)).hom.app M) ≫ pj.inv.app M := by
      rw [hcongr]
    _ = ci.inv.app M ≫ er.hom.app M ≫
        ((Scheme.Modules.restrictFunctorIsoPullback
            (P.p₂ ≫ cov.f j)).hom.app M ≫ pj.inv.app M) := by
      simp only [Category.assoc]
    _ = ci.inv.app M ≫ er.hom.app M ≫ (cj.hom.app M ≫ R) := by
      rw [hright]
    _ = K ≫ R := by simp only [K, Category.assoc]

private theorem compatibleFamilyRestrictionHom_comm_overlap
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    let P := overlap cov i j
    (Scheme.Modules.pullback P.p₁).map
          (compatibleFamilyRestrictionHom D i) ≫
        D.hom (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm =
      ((modulesPseudofunctor.toDescentData cov.f).obj
          (compatibleFamilyModule D)).hom
          (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm ≫
        (Scheme.Modules.pullback P.p₂).map
          (compatibleFamilyRestrictionHom D j) := by
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  let M : X.Modules := compatibleFamilyModule D
  let Di : (cov.X i).Modules := D.obj i
  let Dj : (cov.X j).Modules := D.obj j
  let Ri := Scheme.Modules.restrictFunctor (cov.f i)
  let Rj := Scheme.Modules.restrictFunctor (cov.f j)
  let R₁ := Scheme.Modules.restrictFunctor P.p₁
  let R₂ := Scheme.Modules.restrictFunctor P.p₂
  let Q₁ := Scheme.Modules.pullback P.p₁
  let Q₂ := Scheme.Modules.pullback P.p₂
  let ei := Scheme.Modules.restrictFunctorIsoPullback (cov.f i)
  let ej := Scheme.Modules.restrictFunctorIsoPullback (cov.f j)
  let e₁ := Scheme.Modules.restrictFunctorIsoPullback P.p₁
  let e₂ := Scheme.Modules.restrictFunctorIsoPullback P.p₂
  let ri : (Scheme.Modules.pullback (cov.f i)).obj M ⟶ Di :=
    compatibleFamilyRestrictionHom D i
  let rj : (Scheme.Modules.pullback (cov.f j)).obj M ⟶ Dj :=
    compatibleFamilyRestrictionHom D j
  let A := R₁.map (ei.hom.app M) ≫
    e₁.hom.app ((Scheme.Modules.pullback (cov.f i)).obj M)
  let B := R₂.map (ej.hom.app M) ≫
    e₂.hom.app ((Scheme.Modules.pullback (cov.f j)).obj M)
  let K := (Scheme.Modules.restrictFunctorComp P.p₁ (cov.f i)).inv.app M ≫
    (Scheme.Modules.restrictFunctorCongr P.condition).hom.app M ≫
    (Scheme.Modules.restrictFunctorComp P.p₂ (cov.f j)).hom.app M
  let T := restrictionTransition D
    (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm
  let d : Q₁.obj Di ⟶ Q₂.obj Dj := D.hom
    (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm
  let s := ((modulesPseudofunctor.toDescentData cov.f).obj M).hom
    (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm
  have hA : A ≫ Q₁.map ri = R₁.map (ei.hom.app M ≫ ri) ≫
      e₁.hom.app Di := by
    calc
      A ≫ Q₁.map ri = R₁.map (ei.hom.app M) ≫
          (e₁.hom.app ((Scheme.Modules.pullback (cov.f i)).obj M) ≫
            Q₁.map ri) := by simp only [A, Category.assoc]
      _ = R₁.map (ei.hom.app M) ≫
          (R₁.map ri ≫ e₁.hom.app Di) := by
        rw [e₁.hom.naturality ri]
      _ = (R₁.map (ei.hom.app M) ≫ R₁.map ri) ≫
          e₁.hom.app Di := by simp only [Category.assoc]
      _ = R₁.map (ei.hom.app M ≫ ri) ≫ e₁.hom.app Di := by
        rw [R₁.map_comp]
  have hB : R₂.map (ej.hom.app M ≫ rj) ≫ e₂.hom.app Dj =
      B ≫ Q₂.map rj := by
    calc
      R₂.map (ej.hom.app M ≫ rj) ≫ e₂.hom.app Dj =
          (R₂.map (ej.hom.app M) ≫ R₂.map rj) ≫
            e₂.hom.app Dj := by rw [R₂.map_comp]
      _ = R₂.map (ej.hom.app M) ≫
          (R₂.map rj ≫ e₂.hom.app Dj) := by simp only [Category.assoc]
      _ = R₂.map (ej.hom.app M) ≫
          (e₂.hom.app ((Scheme.Modules.pullback (cov.f j)).obj M) ≫
            Q₂.map rj) := by rw [e₂.hom.naturality rj]
      _ = B ≫ Q₂.map rj := by simp only [B, Category.assoc]
  have hrestriction : R₁.map (ei.hom.app M ≫ ri) ≫ T =
      K ≫ R₂.map (ej.hom.app M ≫ rj) := by
    simpa only [P, Ri, Rj, R₁, R₂, ei, ej, ri, rj, K, T, M] using
      compatibleFamilyRestrictionHom_comm_restriction D i j
  have hsource : A ≫ s = K ≫ B := by
    simpa only [P, A, B, K, s, M, R₁, R₂, ei, ej, e₁, e₂] using
      compatibleFamilyOfObjTransition_from_restriction D i j
  have hinner : (d ≫ e₂.inv.app Dj) ≫ e₂.hom.app Dj = d := by
    calc
      _ = d ≫ (e₂.inv.app Dj ≫ e₂.hom.app Dj) := Category.assoc _ _ _
      _ = d ≫ 𝟙 _ := congrArg (fun z ↦ d ≫ z) (e₂.inv_hom_id_app Dj)
      _ = d := Category.comp_id _
  have hT : e₁.hom.app Di ≫ d = T ≫ e₂.hom.app Dj := by
    calc
      _ = e₁.hom.app Di ≫ ((d ≫ e₂.inv.app Dj) ≫ e₂.hom.app Dj) :=
        congrArg (fun z ↦ e₁.hom.app Di ≫ z) hinner.symm
      _ = (e₁.hom.app Di ≫ (d ≫ e₂.inv.app Dj)) ≫ e₂.hom.app Dj :=
        (Category.assoc _ _ _).symm
      _ = T ≫ e₂.hom.app Dj := by rfl
  change Q₁.map ri ≫ d = s ≫ Q₂.map rj
  apply (cancel_epi A).mp
  calc
    A ≫ (Q₁.map ri ≫ d) =
        (R₁.map (ei.hom.app M ≫ ri) ≫ e₁.hom.app Di) ≫ d := by
      rw [← Category.assoc, hA]
    _ = R₁.map (ei.hom.app M ≫ ri) ≫
        (T ≫ e₂.hom.app Dj) := by
      simp only [Category.assoc, hT]
    _ = (R₁.map (ei.hom.app M ≫ ri) ≫ T) ≫
        e₂.hom.app Dj := by simp only [Category.assoc]
    _ = (K ≫ R₂.map (ej.hom.app M ≫ rj)) ≫
        e₂.hom.app Dj := by rw [hrestriction]
    _ = K ≫ (R₂.map (ej.hom.app M ≫ rj) ≫
        e₂.hom.app Dj) := by simp only [Category.assoc]
    _ = K ≫ (B ≫ Q₂.map rj) := by rw [hB]
    _ = (K ≫ B) ≫ Q₂.map rj := by simp only [Category.assoc]
    _ = (A ≫ s) ≫ Q₂.map rj :=
      congrArg (fun z ↦ z ≫ Q₂.map rj) hsource.symm
    _ = A ≫ (s ≫ Q₂.map rj) := Category.assoc A s (Q₂.map rj)

private theorem compatibleFamilyRestrictionHom_comm_chosenOverlap
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    let P := overlap cov i j
    (modulesPseudofunctor.map P.p₁.op.toLoc).toFunctor.map
          (compatibleFamilyRestrictionHom D i) ≫
        D.hom P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
      ((modulesPseudofunctor.toDescentData cov.f).obj
          (compatibleFamilyModule D)).hom P.p P.p₁ P.p₂ P.hp₁ P.hp₂ ≫
        (modulesPseudofunctor.map P.p₂.op.toLoc).toFunctor.map
          (compatibleFamilyRestrictionHom D j) := by
  let P := overlap cov i j
  change (Scheme.Modules.pullback P.p₁).map
        (compatibleFamilyRestrictionHom D i) ≫
      D.hom P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
    ((modulesPseudofunctor.toDescentData cov.f).obj
        (compatibleFamilyModule D)).hom P.p P.p₁ P.p₂ P.hp₁ P.hp₂ ≫
      (Scheme.Modules.pullback P.p₂).map
        (compatibleFamilyRestrictionHom D j)
  cases P.hp₁
  exact compatibleFamilyRestrictionHom_comm_overlap D i j

private noncomputable def compatibleFamilyDescentDataPrimeIso
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) :
    Pseudofunctor.DescentData'.ofDescentData
          (overlap cov) (tripleOverlap cov)
          ((modulesPseudofunctor.toDescentData cov.f).obj
            (compatibleFamilyModule D)) ≅
      Pseudofunctor.DescentData'.ofDescentData
        (overlap cov) (tripleOverlap cov) D :=
  Pseudofunctor.DescentData'.isoMk
    (compatibleFamilyRestrictionIso D)
    (compatibleFamilyRestrictionHom_comm_chosenOverlap D)

/-- The equalizer of a compatible family induces the original full descent datum.

The commutativity field of this isomorphism is the full `DescentData.Hom.comm`: it holds after
pullback along every common base change, not only on the chosen pairwise overlaps.  The current
construction retains the honest `OpenCover.{0}` restriction needed by the product-preservation
argument used to build `compatibleFamilyModule`. -/
noncomputable def compatibleFamilyDescentIso
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) :
    (modulesPseudofunctor.toDescentData cov.f).obj
        (compatibleFamilyModule D) ≅ D := by
  let prime := compatibleFamilyDescentDataPrimeIso D
  exact Pseudofunctor.DescentData.isoMk
    (compatibleFamilyRestrictionIso D)
    (fun {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ ↦ by
      have h := Pseudofunctor.DescentData'.comm
        prime.hom q f₁ f₂ hf₁ hf₂
      have hprime (k : cov.I₀) : prime.hom.hom k =
          (compatibleFamilyRestrictionIso D k).hom := by
        rfl
      rw [hprime i₁, hprime i₂] at h
      rw [Pseudofunctor.DescentData'.pullHom'_ofDescentData_hom,
        Pseudofunctor.DescentData'.pullHom'_ofDescentData_hom] at h
      change (modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map
            (compatibleFamilyRestrictionIso D i₁).hom ≫
          D.hom q f₁ f₂ hf₁ hf₂ =
        ((modulesPseudofunctor.toDescentData cov.f).obj
            (compatibleFamilyModule D)).hom q f₁ f₂ hf₁ hf₂ ≫
          (modulesPseudofunctor.map f₂.op.toLoc).toFunctor.map
            (compatibleFamilyRestrictionIso D i₂).hom at h
      exact h)

@[simp]
theorem compatibleFamilyDescentIso_hom_hom
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (compatibleFamilyDescentIso D).hom.hom i =
      compatibleFamilyRestrictionHom D i := by
  rfl

/-- The compatible-family equalizer is an object-specific effective module for the original
descent datum. -/
theorem compatibleFamilyEffectiveModule
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (D : modulesPseudofunctor.DescentData cov.f) : EffectiveModule cov D :=
  ⟨compatibleFamilyModule D, ⟨compatibleFamilyDescentIso D⟩⟩

/-- Module descent data on a universe-zero-indexed scheme open cover are effective. -/
theorem moduleEffectiveDescentForOpenCover
    {X : Scheme.{u}} (cov : X.OpenCover.{0}) : ModuleEffectiveDescentFor cov :=
  fun D ↦ compatibleFamilyEffectiveModule D

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
