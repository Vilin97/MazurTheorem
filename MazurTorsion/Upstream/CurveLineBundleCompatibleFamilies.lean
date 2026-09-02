/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Adjunction.Limits
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

/-- Restriction of scheme modules along an open immersion is a right adjoint.  This is kept as a
named, explicitly installed fact rather than a global instance, so consumers can request exactly
the limit-preservation scope they need without introducing an instance diamond. -/
theorem restrictFunctorIsRightAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).IsRightAdjoint := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  let φ : X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  letI : (PresheafOfModules.pushforward φ.hom).IsRightAdjoint :=
    PresheafOfModules.instIsRightAdjointPushforward φ.hom
  change (SheafOfModules.pushforward φ).IsRightAdjoint
  exact SheafOfModules.instIsRightAdjointPushforward φ

/-- The local module in a descent datum, with its ambient scheme-module category made explicit.
This reducible spelling avoids exposing the implementation category of `modulesPseudofunctor` to
downstream categorical rewriting. -/
abbrev descentLocalModule
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) : (cov.X i).Modules :=
  D.obj i

/-- A transition of the descent datum with its source and target exposed as scheme-module
pullbacks. -/
abbrev descentPullbackHom
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f)
    {Y : Scheme.{u}} (q : Y ⟶ X) {i j : cov.I₀}
    (fᵢ : Y ⟶ cov.X i) (fⱼ : Y ⟶ cov.X j)
    (hᵢ : fᵢ ≫ cov.f i = q) (hⱼ : fⱼ ≫ cov.f j = q) :
    (Scheme.Modules.pullback fᵢ).obj (descentLocalModule D i) ⟶
      (Scheme.Modules.pullback fⱼ).obj (descentLocalModule D j) :=
  D.hom q fᵢ fⱼ hᵢ hⱼ

/-- The scheme-module spelling of the raw descent cocycle. -/
theorem descentPullbackHom_comp
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f)
    {Y : Scheme.{u}} (q : Y ⟶ X) {i j k : cov.I₀}
    (fᵢ : Y ⟶ cov.X i) (fⱼ : Y ⟶ cov.X j) (fₖ : Y ⟶ cov.X k)
    (hᵢ : fᵢ ≫ cov.f i = q) (hⱼ : fⱼ ≫ cov.f j = q)
    (hₖ : fₖ ≫ cov.f k = q) :
    descentPullbackHom D q fᵢ fⱼ hᵢ hⱼ ≫
        descentPullbackHom D q fⱼ fₖ hⱼ hₖ =
      descentPullbackHom D q fᵢ fₖ hᵢ hₖ := by
  exact D.hom_comp q fᵢ fⱼ fₖ hᵢ hⱼ hₖ

/-- Conjugating a restricted morphism by the restriction-pullback comparison recovers its
genuine pullback. -/
@[reassoc]
theorem restrictFunctorIsoPullback_inv_map_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (g : M ⟶ N) :
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app M ≫
        (Scheme.Modules.restrictFunctor f).map g ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app N =
      (Scheme.Modules.pullback f).map g := by
  change (((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M ≫
    (Scheme.Modules.restrictFunctor f).map g) ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app N) = _
  rw [← (Scheme.Modules.restrictFunctorIsoPullback f).inv.naturality]
  simp

@[simp]
theorem restrictFunctor_map_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (g : M ⟶ N) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctor f).map g).app U = g.app (f ''ᵁ U) :=
  rfl

/-- The restriction-composition comparison is the mate of direct-image composition. -/
theorem conjugateEquiv_restrictFunctorComp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv
        ((Scheme.Modules.restrictAdjunction g).comp
          (Scheme.Modules.restrictAdjunction f))
        (Scheme.Modules.restrictAdjunction (f ≫ g))
        (Scheme.Modules.restrictFunctorComp f g).hom =
      (Scheme.Modules.pushforwardComp f g).hom := by
  ext M U x
  simp [conjugateEquiv_apply_app]
  change (AddCommGrpCat.Hom.hom
    (M.presheaf.map _ ≫ M.presheaf.map _ ≫
      M.presheaf.map _ ≫ M.presheaf.map _)) x = x
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  change ↑Γ(M, f ⁻¹ᵁ g ⁻¹ᵁ U) at x
  change (M.presheaf.map
      (_ : Opposite.op (f ⁻¹ᵁ g ⁻¹ᵁ U) ⟶ Opposite.op (f ⁻¹ᵁ g ⁻¹ᵁ U))).hom x =
    (AddCommGrpCat.Hom.hom
      (𝟙 Γ(M, f ⁻¹ᵁ g ⁻¹ᵁ U))) x
  congr 2
  rw [← M.presheaf.map_id]
  congr 1

/-- The restriction--pullback comparison has the identity direct-image mate. -/
theorem conjugateEquiv_restrictFunctorIsoPullback_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.restrictAdjunction f)
        (Scheme.Modules.restrictFunctorIsoPullback f).hom =
      𝟙 (Scheme.Modules.pushforward f) := by
  simp [Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.leftAdjointUniq]

/-- The canonical restriction--pullback comparison is compatible with composition of open
immersions, as an equality of natural transformations. -/
theorem restrictFunctorIsoPullback_comp_hom_natTrans
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (Scheme.Modules.restrictFunctorComp f g).hom ≫
        Functor.whiskerRight
          (Scheme.Modules.restrictFunctorIsoPullback g).hom
          (Scheme.Modules.restrictFunctor f) ≫
        Functor.whiskerLeft (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictFunctorIsoPullback f).hom ≫
        (Scheme.Modules.pullbackComp f g).hom =
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom := by
  let A := Scheme.Modules.restrictAdjunction (f ≫ g)
  let B := (Scheme.Modules.restrictAdjunction g).comp
    (Scheme.Modules.restrictAdjunction f)
  let C := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.restrictAdjunction f)
  let D := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let E := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let a := (Scheme.Modules.restrictFunctorComp f g).hom
  let b := Functor.whiskerRight
    (Scheme.Modules.restrictFunctorIsoPullback g).hom
    (Scheme.Modules.restrictFunctor f)
  let c := Functor.whiskerLeft (Scheme.Modules.pullback g)
    (Scheme.Modules.restrictFunctorIsoPullback f).hom
  let d := (Scheme.Modules.pullbackComp f g).hom
  have ha : conjugateEquiv B A a =
      (Scheme.Modules.pushforwardComp f g).hom := by
    exact conjugateEquiv_restrictFunctorComp_hom f g
  have hb : conjugateEquiv C B b =
      𝟙 (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g) := by
    dsimp only [B, C, b]
    rw [conjugateEquiv_whiskerRight,
      conjugateEquiv_restrictFunctorIsoPullback_hom]
    simp
  have hc : conjugateEquiv D C c =
      𝟙 (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g) := by
    dsimp only [C, D, c]
    rw [conjugateEquiv_whiskerLeft,
      conjugateEquiv_restrictFunctorIsoPullback_hom]
    simp
  have hd : conjugateEquiv E D d =
      (Scheme.Modules.pushforwardComp f g).inv := by
    rw [← cancel_mono (Scheme.Modules.pushforwardComp f g).hom]
    rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv f g]
    dsimp only [D, E, d]
    rw [conjugateEquiv_comp]
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv]
    simp
  apply (conjugateEquiv E A).injective
  rw [conjugateEquiv_restrictFunctorIsoPullback_hom]
  change conjugateEquiv E A (a ≫ b ≫ c ≫ d) = _
  calc
    _ = conjugateEquiv E D d ≫ conjugateEquiv D C c ≫
        conjugateEquiv C B b ≫ conjugateEquiv B A a := by
      symm
      rw [conjugateEquiv_comp, conjugateEquiv_comp,
        conjugateEquiv_comp]
      simp only [Category.assoc]
    _ = _ := by rw [hd, hc, hb, ha]; simp

/-- Component form of `restrictFunctorIsoPullback_comp_hom_natTrans`. -/
theorem restrictFunctorIsoPullback_comp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (Scheme.Modules.restrictFunctorComp f g).hom.app M ≫
        (Scheme.Modules.restrictFunctor f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app M =
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M := by
  exact congr_app (restrictFunctorIsoPullback_comp_hom_natTrans f g) M

@[simp]
theorem restrictFunctorCongr_refl_hom_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  ext U x
  simp
  rfl

@[simp]
theorem restrictFunctorCongr_refl_inv_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).inv.app M = 𝟙 _ := by
  ext U x
  simp
  rfl

/-- The restriction--pullback comparison respects replacement of an open immersion by an equal
morphism. -/
theorem restrictFunctorIsoPullback_congr_hom
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback g).hom.app M =
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫
        (Scheme.Modules.pullbackCongr h).hom.app M := by
  subst g
  simp
  change _ = _ ≫ 𝟙 _
  simp

theorem restrictFunctorIsoPullback_congr_inv
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback g).inv.app M ≫
        (Scheme.Modules.restrictFunctorCongr h).inv.app M =
      (Scheme.Modules.pullbackCongr h).inv.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app M := by
  subst g
  rw [restrictFunctorCongr_refl_inv_app]
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp

/-- Cancellation form of restriction--pullback compatibility with composition. -/
theorem restrictFunctorIsoPullback_comp_inv_hom_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).inv.app M ≫
        (Scheme.Modules.restrictFunctorComp f g).hom.app M ≫
        (Scheme.Modules.restrictFunctor f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) =
      (Scheme.Modules.pullbackComp f g).inv.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
          ((Scheme.Modules.pullback g).obj M) := by
  rw [← cancel_mono
    (((Scheme.Modules.restrictFunctorIsoPullback f).hom.app
      ((Scheme.Modules.pullback g).obj M)) ≫
      (Scheme.Modules.pullbackComp f g).hom.app M)]
  simp only [Category.assoc]
  rw [restrictFunctorIsoPullback_comp_hom f g]
  simp

/-- Inverse cancellation form of restriction--pullback compatibility with composition. -/
@[reassoc]
theorem restrictFunctorIsoPullback_map_inv_comp_inv_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules) :
    (Scheme.Modules.restrictFunctor f).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) ≫
        (Scheme.Modules.restrictFunctorComp f g).inv.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M =
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app
          ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app M := by
  let A :
      (Scheme.Modules.restrictFunctor (f ≫ g)).obj M ≅
        (Scheme.Modules.restrictFunctor f).obj
          ((Scheme.Modules.pullback g).obj M) :=
    (Scheme.Modules.restrictFunctorComp f g).app M ≪≫
      (Scheme.Modules.restrictFunctor f).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback g).app M)
  let B :
      (Scheme.Modules.restrictFunctor f).obj
          ((Scheme.Modules.pullback g).obj M) ≅
        (Scheme.Modules.pullback (f ≫ g)).obj M :=
    (Scheme.Modules.restrictFunctorIsoPullback f).app
        ((Scheme.Modules.pullback g).obj M) ≪≫
      (Scheme.Modules.pullbackComp f g).app M
  have hIso : A ≪≫ B =
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).app M := by
    apply Iso.ext
    exact restrictFunctorIsoPullback_comp_hom f g M
  have hhom : A.hom ≫ B.hom =
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M := by
    exact congrArg Iso.hom hIso
  change A.inv ≫
      (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M = B.hom
  rw [← hhom]
  simp

@[reassoc]
private theorem restrictOverlapTransition_source
    {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y) (gf : W ⟶ X)
    (hgf : g ≫ f = gf)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion gf]
    (M : X.Modules) :
    (Scheme.Modules.restrictFunctorCongr hgf).inv.app M ≫
        (Scheme.Modules.restrictFunctorComp g f).hom.app M ≫
        (Scheme.Modules.restrictFunctor g).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
      (Scheme.Modules.restrictFunctorIsoPullback gf).hom.app M ≫
        (Scheme.Modules.pullbackCongr hgf).inv.app M ≫
        (Scheme.Modules.pullbackComp g f).inv.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback g).inv.app
          ((Scheme.Modules.pullback f).obj M) := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback gf).app M
  have hi_assoc {Z : W.Modules}
      (q : (Scheme.Modules.pullback gf).obj M ⟶ Z) :
      e.inv ≫ (Scheme.Modules.restrictFunctorIsoPullback gf).hom.app M ≫ q = q := by
    change e.inv ≫ e.hom ≫ q = q
    exact e.inv_hom_id_assoc q
  have hc : e.inv ≫
      (Scheme.Modules.restrictFunctorCongr hgf).inv.app M =
        (Scheme.Modules.pullbackCongr hgf).inv.app M ≫
          (Scheme.Modules.restrictFunctorIsoPullback (g ≫ f)).inv.app M := by
    exact restrictFunctorIsoPullback_congr_inv hgf M
  rw [← cancel_epi e.inv]
  calc
    _ = (Scheme.Modules.pullbackCongr hgf).inv.app M ≫
        (Scheme.Modules.pullbackComp g f).inv.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback g).inv.app
          ((Scheme.Modules.pullback f).obj M) := by
      rw [← Category.assoc, hc]
      simp only [Category.assoc]
      rw [restrictFunctorIsoPullback_comp_inv_hom_hom]
    _ = _ := by rw [hi_assoc]

@[reassoc]
private theorem restrictOverlapTransition_target
    {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y) (gf : W ⟶ X)
    (hgf : g ≫ f = gf)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion gf]
    (M : X.Modules) :
    (Scheme.Modules.restrictFunctor g).map
          ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M) ≫
        (Scheme.Modules.restrictFunctorComp g f).inv.app M ≫
        (Scheme.Modules.restrictFunctorCongr hgf).hom.app M =
      (Scheme.Modules.restrictFunctorIsoPullback g).hom.app
          ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackComp g f).hom.app M ≫
        (Scheme.Modules.pullbackCongr hgf).hom.app M ≫
        (Scheme.Modules.restrictFunctorIsoPullback gf).inv.app M := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback gf).app M
  have hi : (Scheme.Modules.restrictFunctorIsoPullback gf).inv.app M ≫
      e.hom = 𝟙 _ := by
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id
  have hc : (Scheme.Modules.restrictFunctorCongr hgf).hom.app M ≫
      e.hom =
        (Scheme.Modules.restrictFunctorIsoPullback (g ≫ f)).hom.app M ≫
          (Scheme.Modules.pullbackCongr hgf).hom.app M := by
    exact restrictFunctorIsoPullback_congr_hom hgf M
  rw [← cancel_mono e.hom]
  calc
    _ = (Scheme.Modules.restrictFunctorIsoPullback g).hom.app
          ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackComp g f).hom.app M ≫
        (Scheme.Modules.pullbackCongr hgf).hom.app M := by
      simp only [Category.assoc]
      rw [hc]
      rw [restrictFunctorIsoPullback_map_inv_comp_inv_hom_assoc]
    _ = _ := by
      simp only [Category.assoc, hi, Category.comp_id]

private theorem modulesPseudofunctor_mapComp'_hom_app
    {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y) (gf : W ⟶ X)
    (hgf : g ≫ f = gf) (M : X.Modules) :
    (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by aesop)).hom.toNatTrans.app M =
      (Scheme.Modules.pullbackCongr hgf).inv.app M ≫
        (Scheme.Modules.pullbackComp g f).inv.app M := by
  subst gf
  rfl

private theorem modulesPseudofunctor_mapComp'_inv_app
    {X Y W : Scheme.{u}} (f : Y ⟶ X) (g : W ⟶ Y) (gf : W ⟶ X)
    (hgf : g ≫ f = gf) (M : X.Modules) :
    (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by aesop)).inv.toNatTrans.app M =
      (Scheme.Modules.pullbackComp g f).hom.app M ≫
        (Scheme.Modules.pullbackCongr hgf).hom.app M := by
  subst gf
  rfl

private theorem modulesPseudofunctor_map_map
    {X Y : Scheme.{u}} (f : Y ⟶ X) {M N : X.Modules} (phi : M ⟶ N) :
    (modulesPseudofunctor.map f.op.toLoc).toFunctor.map phi =
      (Scheme.Modules.pullback f).map phi := by
  rfl

/-- Restricting a pullback-valued transition along a further open immersion gives the
`Pseudofunctor.pullHom` transition, after the canonical restriction--pullback comparisons. -/
theorem restrictOverlapTransition_eq_pullHom
    {X₁ X₂ Y W : Scheme.{u}}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (g : W ⟶ Y)
    (gf₁ : W ⟶ X₁) (gf₂ : W ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] [IsOpenImmersion g]
    [IsOpenImmersion gf₁] [IsOpenImmersion gf₂]
    {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    (phi : (Scheme.Modules.pullback f₁).obj M₁ ⟶
      (Scheme.Modules.pullback f₂).obj M₂) :
    (Scheme.Modules.restrictFunctorCongr hgf₁).inv.app M₁ ≫
        (Scheme.Modules.restrictFunctorComp g f₁).hom.app M₁ ≫
        (Scheme.Modules.restrictFunctor g).map
          ((Scheme.Modules.restrictFunctorIsoPullback f₁).hom.app M₁ ≫
            phi ≫
            (Scheme.Modules.restrictFunctorIsoPullback f₂).inv.app M₂) ≫
        (Scheme.Modules.restrictFunctorComp g f₂).inv.app M₂ ≫
        (Scheme.Modules.restrictFunctorCongr hgf₂).hom.app M₂ =
      (Scheme.Modules.restrictFunctorIsoPullback gf₁).hom.app M₁ ≫
        CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := modulesPseudofunctor) phi g gf₁ gf₂ hgf₁ hgf₂ ≫
        (Scheme.Modules.restrictFunctorIsoPullback gf₂).inv.app M₂ := by
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [restrictOverlapTransition_source_assoc f₁ g gf₁ hgf₁ M₁]
  rw [restrictOverlapTransition_target f₂ g gf₂ hgf₂ M₂]
  rw [restrictFunctorIsoPullback_inv_map_hom_assoc]
  rw [cancel_epi
    ((Scheme.Modules.restrictFunctorIsoPullback gf₁).hom.app M₁)]
  simp only [← Category.assoc]
  apply (cancel_mono
    ((Scheme.Modules.restrictFunctorIsoPullback gf₂).inv.app M₂)).mpr
  unfold CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  rw [modulesPseudofunctor_mapComp'_hom_app f₁ g gf₁ hgf₁ M₁,
    modulesPseudofunctor_mapComp'_inv_app f₂ g gf₂ hgf₂ M₂]
  calc
    _ = ((Scheme.Modules.pullbackCongr hgf₁).inv.app M₁ ≫
          (Scheme.Modules.pullbackComp g f₁).inv.app M₁) ≫
        (Scheme.Modules.pullback g).map phi ≫
        (Scheme.Modules.pullbackComp g f₂).hom.app M₂ ≫
        (Scheme.Modules.pullbackCongr hgf₂).hom.app M₂ := by
      simp only [Category.assoc]
    _ = _ := congrArg
      (fun m ↦
        ((Scheme.Modules.pullbackCongr hgf₁).inv.app M₁ ≫
            (Scheme.Modules.pullbackComp g f₁).inv.app M₁) ≫
          m ≫
          (Scheme.Modules.pullbackComp g f₂).hom.app M₂ ≫
          (Scheme.Modules.pullbackCongr hgf₂).hom.app M₂)
      (modulesPseudofunctor_map_map g phi).symm

/-- For a cartesian square whose vertical maps are open immersions, taking the image along the
left projection after pulling an open set back agrees with pulling back its image along the right
vertical map.  This is the site-level comparison underlying open base change for module sheaves.
-/
noncomputable def openPullbackOpensIso
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) :
    letI : IsOpenImmersion p₂ :=
      MorphismProperty.of_isPullback H
        (inferInstance : IsOpenImmersion f₁)
    f₁.opensFunctor ⋙ TopologicalSpace.Opens.map f₂.base ≅
      TopologicalSpace.Opens.map p₁.base ⋙ p₂.opensFunctor := by
  letI : IsOpenImmersion p₂ :=
    MorphismProperty.of_isPullback H
      (inferInstance : IsOpenImmersion f₁)
  exact NatIso.ofComponents
    (fun W ↦ eqToIso
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W).symm)
    (fun _ ↦ Subsingleton.elim _ _)

/-- Restriction of a direct image around a cartesian square of open immersions is the direct
image of the corresponding restriction. -/
noncomputable def openPullbackRestrictPushforwardIso
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) :
    letI : IsOpenImmersion p₂ :=
      MorphismProperty.of_isPullback H
        (inferInstance : IsOpenImmersion f₁)
    Scheme.Modules.pushforward f₂ ⋙ Scheme.Modules.restrictFunctor f₁ ≅
      Scheme.Modules.restrictFunctor p₂ ⋙ Scheme.Modules.pushforward p₁ := by
  letI : IsOpenImmersion p₂ :=
    MorphismProperty.of_isPullback H
      (inferInstance : IsOpenImmersion f₁)
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
theorem openPullbackRestrictPushforwardIso_hom_app
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens) :
    letI : IsOpenImmersion p₂ :=
      MorphismProperty.of_isPullback H
        (inferInstance : IsOpenImmersion f₁)
    ((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).hom.app M).app W =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op := by
  letI : IsOpenImmersion p₂ :=
    MorphismProperty.of_isPullback H
      (inferInstance : IsOpenImmersion f₁)
  rfl

@[simp]
theorem openPullbackRestrictPushforwardIso_inv_app
    {X₁ X₂ Y P : Scheme.{u}}
    (p₁ : P ⟶ X₁) (p₂ : P ⟶ X₂) (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y)
    [IsOpenImmersion f₁]
    (H : IsPullback p₁ p₂ f₁ f₂) (M : X₂.Modules) (W : X₁.Opens) :
    letI : IsOpenImmersion p₂ :=
      MorphismProperty.of_isPullback H
        (inferInstance : IsOpenImmersion f₁)
    ((openPullbackRestrictPushforwardIso p₁ p₂ f₁ f₂ H).inv.app M).app W =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W).symm).op := by
  letI : IsOpenImmersion p₂ :=
    MorphismProperty.of_isPullback H
      (inferInstance : IsOpenImmersion f₁)
  rfl

/-- The descent transition on a chosen pairwise overlap. -/
noncomputable def compatibleFamilyOverlapPullbackIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    (Scheme.Modules.pullback (overlap cov i j).p₁).obj (descentLocalModule D i) ≅
      (Scheme.Modules.pullback (overlap cov i j).p₂).obj (descentLocalModule D j) :=
  let P := overlap cov i j
  D.iso (P.p₁ ≫ cov.f i) P.p₁ P.p₂ rfl P.condition.symm

/-- The same overlap transition written between the concrete restriction functors. -/
noncomputable def compatibleFamilyOverlapRestrictIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    let P := overlap cov i j
    letI : IsOpenImmersion P.p₁ :=
      MorphismProperty.of_isPullback P.isPullback.flip
        (inferInstance : IsOpenImmersion (cov.f j))
    letI : IsOpenImmersion P.p₂ :=
      MorphismProperty.of_isPullback P.isPullback
        (inferInstance : IsOpenImmersion (cov.f i))
    (Scheme.Modules.restrictFunctor P.p₁).obj (descentLocalModule D i) ≅
      (Scheme.Modules.restrictFunctor P.p₂).obj (descentLocalModule D j) := by
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ := MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  exact (Scheme.Modules.restrictFunctorIsoPullback P.p₁).app (descentLocalModule D i) ≪≫
    compatibleFamilyOverlapPullbackIso D i j ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback P.p₂).app
      (descentLocalModule D j)).symm

/-- The chosen triple overlap is also the pullback of chart `i` and the `(j,k)` overlap over
the base. -/
theorem tripleOverlapIsPullbackFirstOverlap
    {X : Scheme.{u}} (cov : X.OpenCover) (i j k : cov.I₀) :
    IsPullback (tripleOverlap cov i j k).p₁ (tripleOverlap cov i j k).p₂₃
      (cov.f i) ((overlap cov j k).p₁ ≫ cov.f j) := by
  simpa only [ChosenPullback₃.p₁₂_p₁] using
    (tripleOverlap cov i j k).isPullback₂.paste_horiz (overlap cov i j).isPullback

/-- The `j`-th component of the compatible family induced by the local object on chart `i`.
It first transposes the overlap transition across restriction/direct-image adjunction, then uses
open base change to land in the restriction to chart `i` of the direct image from chart `j`.
These maps are the components required to construct an inverse to
`compatibleFamilyRestrictionHom`. -/
noncomputable def compatibleFamilyChartComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    descentLocalModule D i ⟶
      (Scheme.Modules.restrictFunctor (cov.f i)).obj
        ((Scheme.Modules.pushforward (cov.f j)).obj (descentLocalModule D j)) :=
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  (Scheme.Modules.restrictAdjunction P.p₁).homEquiv
      (descentLocalModule D i)
      ((Scheme.Modules.restrictFunctor P.p₂).obj (descentLocalModule D j))
      (compatibleFamilyOverlapRestrictIso D i j).hom ≫
    (openPullbackRestrictPushforwardIso
      P.p₁ P.p₂ (cov.f i) (cov.f j) P.isPullback).inv.app
        (descentLocalModule D j)

/-- The product of the direct images of all local modules in a descent datum. -/
abbrev compatibleFamilyAmbientObject
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) : X.Modules :=
  (Scheme.Modules.pushforward (cov.f i)).obj (descentLocalModule D i)

/-- The direct-image object associated to one ordered pairwise overlap. -/
abbrev compatibleFamilyOverlapObject
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (ij : cov.I₀ × cov.I₀) : X.Modules :=
  let P := overlap cov ij.1 ij.2
  (Scheme.Modules.pushforward (P.p₁ ≫ cov.f ij.1)).obj
    ((Scheme.Modules.pullback P.p₂).obj (descentLocalModule D ij.2))

/-- The product of the direct images of all local modules in a descent datum. -/
noncomputable abbrev compatibleFamilyAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  ∏ᶜ compatibleFamilyAmbientObject D

/-- The product of the direct images of the second local module restricted to every chosen
pairwise overlap. -/
noncomputable abbrev compatibleFamilyOverlapAmbient
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) : X.Modules :=
  ∏ᶜ compatibleFamilyOverlapObject D

/-- The first-chart contribution to one overlap equation, after projecting from the ambient
product. -/
noncomputable def compatibleFamilyFirstTail
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbientObject D i ⟶ compatibleFamilyOverlapObject D (i, j) :=
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  (Scheme.Modules.pushforward (cov.f i)).map
      ((Scheme.Modules.restrictAdjunction P.p₁).unit.app
        (descentLocalModule D i)) ≫
    (Scheme.Modules.pushforwardComp P.p₁ (cov.f i)).hom.app
      ((Scheme.Modules.restrictFunctor P.p₁).obj (descentLocalModule D i)) ≫
    (Scheme.Modules.pushforward (P.p₁ ≫ cov.f i)).map
      ((compatibleFamilyOverlapRestrictIso D i j).hom ≫
        ((Scheme.Modules.restrictFunctorIsoPullback P.p₂).app
          (descentLocalModule D j)).hom)

/-- The second-chart contribution to one overlap equation, after projecting from the ambient
product. -/
noncomputable def compatibleFamilySecondTail
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbientObject D j ⟶ compatibleFamilyOverlapObject D (i, j) :=
  let P := overlap cov i j
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  (Scheme.Modules.pushforward (cov.f j)).map
      ((Scheme.Modules.restrictAdjunction P.p₂).unit.app
        (descentLocalModule D j)) ≫
    (Scheme.Modules.pushforwardComp P.p₂ (cov.f j)).hom.app
      ((Scheme.Modules.restrictFunctor P.p₂).obj (descentLocalModule D j)) ≫
    (Scheme.Modules.pushforwardCongr P.condition.symm).hom.app
      ((Scheme.Modules.restrictFunctor P.p₂).obj (descentLocalModule D j)) ≫
    (Scheme.Modules.pushforward (P.p₁ ≫ cov.f i)).map
      ((Scheme.Modules.restrictFunctorIsoPullback P.p₂).app
        (descentLocalModule D j)).hom

/-- Restrict the first member of a local family to an overlap and transport it through the
descent isomorphism. -/
noncomputable def compatibleFamilyFirstComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbient D ⟶
      (Scheme.Modules.pushforward
        ((overlap cov i j).p₁ ≫ cov.f i)).obj
        ((Scheme.Modules.pullback (overlap cov i j).p₂).obj
          (descentLocalModule D j)) :=
  Pi.π (compatibleFamilyAmbientObject D) i ≫ compatibleFamilyFirstTail D i j

/-- Restrict the second member of a local family to an overlap, then identify the two equal
structural maps to the base. -/
noncomputable def compatibleFamilySecondComponent
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyAmbient D ⟶
      (Scheme.Modules.pushforward
        ((overlap cov i j).p₁ ≫ cov.f i)).obj
        ((Scheme.Modules.pullback (overlap cov i j).p₂).obj
          (descentLocalModule D j)) :=
  Pi.π (compatibleFamilyAmbientObject D) j ≫ compatibleFamilySecondTail D i j

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

/-- The chartwise compatible family regarded as a map into the restriction of the global
ambient product.  The right-adjoint fact is installed only in this consumer. -/
noncomputable def compatibleFamilyRestrictedAmbientHom
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    descentLocalModule D i ⟶
      (Scheme.Modules.restrictFunctor (cov.f i)).obj (compatibleFamilyAmbient D) := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  letI : F.IsRightAdjoint := restrictFunctorIsRightAdjoint (cov.f i)
  exact (isLimitOfHasProductOfPreservesLimit F (compatibleFamilyAmbientObject D)).lift
    (Fan.mk (descentLocalModule D i) fun j ↦ compatibleFamilyChartComponent D i j)

/-- Projection of the restricted ambient family recovers the chosen chart component. -/
@[reassoc]
theorem compatibleFamilyRestrictedAmbientHom_map_π
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j : cov.I₀) :
    compatibleFamilyRestrictedAmbientHom D i ≫
          (Scheme.Modules.restrictFunctor (cov.f i)).map
          (Pi.π (compatibleFamilyAmbientObject D) j) =
      compatibleFamilyChartComponent D i j := by
  let F := Scheme.Modules.restrictFunctor (cov.f i)
  letI : F.IsRightAdjoint := restrictFunctorIsRightAdjoint (cov.f i)
  exact (isLimitOfHasProductOfPreservesLimit F (compatibleFamilyAmbientObject D)).fac
    (Fan.mk (descentLocalModule D i) fun k ↦ compatibleFamilyChartComponent D i k) ⟨j⟩

/-- On a third chart, composing the transition from `i` to `j` with the overlap transition from
`j` to `k` agrees with the direct transition from `i` to `k`.  This is the componentwise cocycle
equation used by the restricted equalizer lift. -/
theorem compatibleFamilyChartComponent_condition
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i j k : cov.I₀) :
    compatibleFamilyChartComponent D i j ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (compatibleFamilyFirstTail D j k) =
      compatibleFamilyChartComponent D i k ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (compatibleFamilySecondTail D j k) := by
  let P := overlap cov j k
  let T := tripleOverlap cov i j k
  let H := tripleOverlapIsPullbackFirstOverlap cov i j k
  letI : IsOpenImmersion P.p₁ :=
    MorphismProperty.of_isPullback P.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f k))
  letI : IsOpenImmersion P.p₂ :=
    MorphismProperty.of_isPullback P.isPullback
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion T.p₂₃ :=
    MorphismProperty.of_isPullback H
      (inferInstance : IsOpenImmersion (cov.f i))
  letI : IsOpenImmersion T.p₁ :=
    MorphismProperty.of_isPullback H.flip
      (inferInstance : IsOpenImmersion (P.p₁ ≫ cov.f j))
  letI : IsOpenImmersion T.p₂ := by
    rw [← T.p₂₃_p₂]
    infer_instance
  letI : IsOpenImmersion T.p₃ := by
    rw [← T.p₂₃_p₃]
    infer_instance
  rw [← cancel_mono ((openPullbackRestrictPushforwardIso
    T.p₁ T.p₂₃ (cov.f i) (P.p₁ ≫ cov.f j) H).hom.app
      ((Scheme.Modules.pullback P.p₂).obj (descentLocalModule D k)))]
  simp only [Category.assoc]
  apply ((Scheme.Modules.restrictAdjunction T.p₁).homEquiv
    (descentLocalModule D i)
    ((Scheme.Modules.restrictFunctor T.p₂₃).obj
      ((Scheme.Modules.pullback P.p₂).obj (descentLocalModule D k)))).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  simp only [compatibleFamilyChartComponent, compatibleFamilyFirstTail,
    compatibleFamilySecondTail, Functor.map_comp, Category.assoc]
  let eTarget :
      (Scheme.Modules.restrictFunctor T.p₂₃).obj
          ((Scheme.Modules.pullback P.p₂).obj (descentLocalModule D k)) ≅
        (Scheme.Modules.restrictFunctor T.p₃).obj (descentLocalModule D k) :=
    (Scheme.Modules.restrictFunctor T.p₂₃).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback P.p₂).app
          (descentLocalModule D k)).symm ≪≫
      (Scheme.Modules.restrictFunctorComp T.p₂₃ P.p₂).symm.app
        (descentLocalModule D k) ≪≫
      (Scheme.Modules.restrictFunctorCongr T.p₂₃_p₃).app
        (descentLocalModule D k)
  rw [← cancel_mono eTarget.hom]
  simp only [Category.assoc]
  let r₁₂ :
      (Scheme.Modules.restrictFunctor T.p₁).obj (descentLocalModule D i) ⟶
        (Scheme.Modules.restrictFunctor T.p₂).obj (descentLocalModule D j) :=
    ((Scheme.Modules.restrictFunctorIsoPullback T.p₁).app
        (descentLocalModule D i)).hom ≫
      descentPullbackHom D T.p T.p₁ T.p₂ T.w₁ T.w₂ ≫
      ((Scheme.Modules.restrictFunctorIsoPullback T.p₂).app
        (descentLocalModule D j)).inv
  let r₂₃ :
      (Scheme.Modules.restrictFunctor T.p₂).obj (descentLocalModule D j) ⟶
        (Scheme.Modules.restrictFunctor T.p₃).obj (descentLocalModule D k) :=
    ((Scheme.Modules.restrictFunctorIsoPullback T.p₂).app
        (descentLocalModule D j)).hom ≫
      descentPullbackHom D T.p T.p₂ T.p₃ T.w₂ T.w₃ ≫
      ((Scheme.Modules.restrictFunctorIsoPullback T.p₃).app
        (descentLocalModule D k)).inv
  let r₁₃ :
      (Scheme.Modules.restrictFunctor T.p₁).obj (descentLocalModule D i) ⟶
        (Scheme.Modules.restrictFunctor T.p₃).obj (descentLocalModule D k) :=
    ((Scheme.Modules.restrictFunctorIsoPullback T.p₁).app
        (descentLocalModule D i)).hom ≫
      descentPullbackHom D T.p T.p₁ T.p₃ T.w₁ T.w₃ ≫
      ((Scheme.Modules.restrictFunctorIsoPullback T.p₃).app
        (descentLocalModule D k)).inv
  let P₁₂ := overlap cov i j
  let P₁₃ := overlap cov i k
  letI : IsOpenImmersion P₁₂.p₁ :=
    MorphismProperty.of_isPullback P₁₂.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f j))
  letI : IsOpenImmersion P₁₂.p₂ :=
    MorphismProperty.of_isPullback P₁₂.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  letI : IsOpenImmersion P₁₃.p₁ :=
    MorphismProperty.of_isPullback P₁₃.isPullback.flip
      (inferInstance : IsOpenImmersion (cov.f k))
  letI : IsOpenImmersion P₁₃.p₂ :=
    MorphismProperty.of_isPullback P₁₃.isPullback
      (inferInstance : IsOpenImmersion (cov.f i))
  letI : IsOpenImmersion T.p₁₂ :=
    MorphismProperty.of_isPullback T.isPullback₁.flip
      (inferInstance : IsOpenImmersion P₁₃.p₁)
  letI : IsOpenImmersion T.p₁₃ :=
    MorphismProperty.of_isPullback T.isPullback₁
      (inferInstance : IsOpenImmersion P₁₂.p₁)
  have hFace₁₂ :
      (Scheme.Modules.restrictFunctorCongr T.p₁₂_p₁).inv.app
          (descentLocalModule D i) ≫
        (Scheme.Modules.restrictFunctorComp T.p₁₂ P₁₂.p₁).hom.app
          (descentLocalModule D i) ≫
        (Scheme.Modules.restrictFunctor T.p₁₂).map
          (compatibleFamilyOverlapRestrictIso D i j).hom ≫
        (Scheme.Modules.restrictFunctorComp T.p₁₂ P₁₂.p₂).inv.app
          (descentLocalModule D j) ≫
        (Scheme.Modules.restrictFunctorCongr T.p₁₂_p₂).hom.app
          (descentLocalModule D j) = r₁₂ := by
    dsimp only [compatibleFamilyOverlapRestrictIso]
    change _ ≫ _ ≫
      (Scheme.Modules.restrictFunctor T.p₁₂).map
        ((Scheme.Modules.restrictFunctorIsoPullback P₁₂.p₁).hom.app
            (descentLocalModule D i) ≫
          (compatibleFamilyOverlapPullbackIso D i j).hom ≫
          (Scheme.Modules.restrictFunctorIsoPullback P₁₂.p₂).inv.app
            (descentLocalModule D j)) ≫
      _ ≫ _ = r₁₂
    rw [restrictOverlapTransition_eq_pullHom P₁₂.p₁ P₁₂.p₂ T.p₁₂
      T.p₁ T.p₂ T.p₁₂_p₁ T.p₁₂_p₂]
    dsimp only [compatibleFamilyOverlapPullbackIso,
      CategoryTheory.Pseudofunctor.DescentData.iso]
    change _ ≫
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (D.hom P₁₂.p P₁₂.p₁ P₁₂.p₂ P₁₂.hp₁ P₁₂.hp₂)
        T.p₁₂ T.p₁ T.p₂ T.p₁₂_p₁ T.p₁₂_p₂ ≫ _ = r₁₂
    rw [D.pullHom_hom T.p₁₂ P₁₂.p T.p T.p₁₂_p
      P₁₂.p₁ P₁₂.p₂ P₁₂.hp₁ P₁₂.hp₂
      T.p₁ T.p₂ T.p₁₂_p₁ T.p₁₂_p₂]
    rfl
  have hFace₂₃ :
      (Scheme.Modules.restrictFunctorCongr T.p₂₃_p₂).inv.app
          (descentLocalModule D j) ≫
        (Scheme.Modules.restrictFunctorComp T.p₂₃ P.p₁).hom.app
          (descentLocalModule D j) ≫
        (Scheme.Modules.restrictFunctor T.p₂₃).map
          (compatibleFamilyOverlapRestrictIso D j k).hom ≫
        (Scheme.Modules.restrictFunctorComp T.p₂₃ P.p₂).inv.app
          (descentLocalModule D k) ≫
        (Scheme.Modules.restrictFunctorCongr T.p₂₃_p₃).hom.app
          (descentLocalModule D k) = r₂₃ := by
    dsimp only [compatibleFamilyOverlapRestrictIso]
    change _ ≫ _ ≫
      (Scheme.Modules.restrictFunctor T.p₂₃).map
        ((Scheme.Modules.restrictFunctorIsoPullback P.p₁).hom.app
            (descentLocalModule D j) ≫
          (compatibleFamilyOverlapPullbackIso D j k).hom ≫
          (Scheme.Modules.restrictFunctorIsoPullback P.p₂).inv.app
            (descentLocalModule D k)) ≫
      _ ≫ _ = r₂₃
    rw [restrictOverlapTransition_eq_pullHom P.p₁ P.p₂ T.p₂₃
      T.p₂ T.p₃ T.p₂₃_p₂ T.p₂₃_p₃]
    dsimp only [compatibleFamilyOverlapPullbackIso,
      CategoryTheory.Pseudofunctor.DescentData.iso]
    change _ ≫
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (D.hom P.p P.p₁ P.p₂ P.hp₁ P.hp₂)
        T.p₂₃ T.p₂ T.p₃ T.p₂₃_p₂ T.p₂₃_p₃ ≫ _ = r₂₃
    rw [D.pullHom_hom T.p₂₃ P.p T.p T.p₂₃_p
      P.p₁ P.p₂ P.hp₁ P.hp₂
      T.p₂ T.p₃ T.p₂₃_p₂ T.p₂₃_p₃]
    rfl
  have hFace₁₃ :
      (Scheme.Modules.restrictFunctorCongr T.p₁₃_p₁).inv.app
          (descentLocalModule D i) ≫
        (Scheme.Modules.restrictFunctorComp T.p₁₃ P₁₃.p₁).hom.app
          (descentLocalModule D i) ≫
        (Scheme.Modules.restrictFunctor T.p₁₃).map
          (compatibleFamilyOverlapRestrictIso D i k).hom ≫
        (Scheme.Modules.restrictFunctorComp T.p₁₃ P₁₃.p₂).inv.app
          (descentLocalModule D k) ≫
        (Scheme.Modules.restrictFunctorCongr T.p₁₃_p₃).hom.app
          (descentLocalModule D k) = r₁₃ := by
    dsimp only [compatibleFamilyOverlapRestrictIso]
    change _ ≫ _ ≫
      (Scheme.Modules.restrictFunctor T.p₁₃).map
        ((Scheme.Modules.restrictFunctorIsoPullback P₁₃.p₁).hom.app
            (descentLocalModule D i) ≫
          (compatibleFamilyOverlapPullbackIso D i k).hom ≫
          (Scheme.Modules.restrictFunctorIsoPullback P₁₃.p₂).inv.app
            (descentLocalModule D k)) ≫
      _ ≫ _ = r₁₃
    rw [restrictOverlapTransition_eq_pullHom P₁₃.p₁ P₁₃.p₂ T.p₁₃
      T.p₁ T.p₃ T.p₁₃_p₁ T.p₁₃_p₃]
    dsimp only [compatibleFamilyOverlapPullbackIso,
      CategoryTheory.Pseudofunctor.DescentData.iso]
    change _ ≫
      CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (D.hom P₁₃.p P₁₃.p₁ P₁₃.p₂ P₁₃.hp₁ P₁₃.hp₂)
        T.p₁₃ T.p₁ T.p₃ T.p₁₃_p₁ T.p₁₃_p₃ ≫ _ = r₁₃
    rw [D.pullHom_hom T.p₁₃ P₁₃.p T.p T.p₁₃_p
      P₁₃.p₁ P₁₃.p₂ P₁₃.hp₁ P₁₃.hp₂
      T.p₁ T.p₃ T.p₁₃_p₁ T.p₁₃_p₃]
    rfl
  calc
    _ = r₁₂ ≫ r₂₃ := by
      simp only [compatibleFamilyOverlapRestrictIso, Adjunction.homEquiv_unit,
        eTarget, r₁₂, r₂₃]
      trace_state
    _ = r₁₃ := by
      dsimp only [r₁₂, r₂₃, r₁₃]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simpa only [Category.assoc] using congrArg
        (fun h ↦
          ((Scheme.Modules.restrictFunctorIsoPullback T.p₁).app
              (descentLocalModule D i)).hom ≫ h ≫
            ((Scheme.Modules.restrictFunctorIsoPullback T.p₃).app
              (descentLocalModule D k)).inv)
        (descentPullbackHom_comp D T.p T.p₁ T.p₂ T.p₃
          T.w₁ T.w₂ T.w₃)
    _ = _ := by
      symm
      ext U x
      simp [compatibleFamilyOverlapRestrictIso, Adjunction.homEquiv_unit,
        eTarget, r₁₃]

/-- The chartwise family satisfies the two overlap equations after restricting the ambient
equalizer diagram to the chosen chart. -/
theorem compatibleFamilyRestrictedAmbientHom_condition
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    compatibleFamilyRestrictedAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilyFirst D) =
      compatibleFamilyRestrictedAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilySecond D) := by
  letI : (Scheme.Modules.restrictFunctor (cov.f i)).IsRightAdjoint :=
    restrictFunctorIsRightAdjoint (cov.f i)
  let B := compatibleFamilyOverlapObject D
  apply (isLimitOfHasProductOfPreservesLimit
    (Scheme.Modules.restrictFunctor (cov.f i)) B).hom_ext
  rintro ⟨⟨j, k⟩⟩
  simp only [Fan.mk_π_app]
  have hfirst : compatibleFamilyFirst D ≫ Pi.π B (j, k) =
      compatibleFamilyFirstComponent D j k := by
    dsimp only [B]
    unfold compatibleFamilyFirst compatibleFamilyOverlapAmbient
    exact Pi.lift_π _ _
  have hsecond : compatibleFamilySecond D ≫ Pi.π B (j, k) =
      compatibleFamilySecondComponent D j k := by
    dsimp only [B]
    unfold compatibleFamilySecond compatibleFamilyOverlapAmbient
    exact Pi.lift_π _ _
  calc
    (compatibleFamilyRestrictedAmbientHom D i ≫
          (Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilyFirst D)) ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map (Pi.π B (j, k)) =
      compatibleFamilyRestrictedAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (compatibleFamilyFirst D ≫ Pi.π B (j, k)) := by
            rw [Category.assoc, ← Functor.map_comp]
    _ = compatibleFamilyRestrictedAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (compatibleFamilyFirstComponent D j k) := by rw [hfirst]
    _ = compatibleFamilyRestrictedAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (compatibleFamilySecondComponent D j k) := by
            simp only [compatibleFamilyFirstComponent, compatibleFamilySecondComponent]
            simp only [Functor.map_comp, Category.assoc]
            rw [compatibleFamilyRestrictedAmbientHom_map_π_assoc D i j,
              compatibleFamilyRestrictedAmbientHom_map_π_assoc D i k]
            exact compatibleFamilyChartComponent_condition D i j k
    _ = compatibleFamilyRestrictedAmbientHom D i ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map
          (compatibleFamilySecond D ≫ Pi.π B (j, k)) := by rw [hsecond]
    _ = (compatibleFamilyRestrictedAmbientHom D i ≫
          (Scheme.Modules.restrictFunctor (cov.f i)).map (compatibleFamilySecond D)) ≫
        (Scheme.Modules.restrictFunctor (cov.f i)).map (Pi.π B (j, k)) := by
            rw [Category.assoc, ← Functor.map_comp]

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
      (Scheme.Modules.pushforward (cov.f i)).obj (descentLocalModule D i) :=
  equalizer.ι (compatibleFamilyFirst D) (compatibleFamilySecond D) ≫
    Pi.π (compatibleFamilyAmbientObject D) i

/-- The adjoint transpose of the chart projection, stated with the genuine module pullback
functor used by `EffectiveModule`.  Proving that this morphism is an isomorphism is the remaining
effective-descent theorem for the equalizer candidate. -/
noncomputable def compatibleFamilyRestrictionHom
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).obj (compatibleFamilyModule D) ⟶
      descentLocalModule D i :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
    (compatibleFamilyModule D) (descentLocalModule D i)).symm
      (compatibleFamilyProjection D i)

/-- The chart restriction map is definitionally adjoint to the corresponding projection of
compatible families.  This is the comparison equation used when constructing its inverse. -/
theorem compatibleFamilyRestrictionHom_adjunct
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : modulesPseudofunctor.DescentData cov.f) (i : cov.I₀) :
    (Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
        (compatibleFamilyModule D) (descentLocalModule D i)
          (compatibleFamilyRestrictionHom D i) =
      compatibleFamilyProjection D i := by
  exact ((Scheme.Modules.pullbackPushforwardAdjunction (cov.f i)).homEquiv
    (compatibleFamilyModule D) (descentLocalModule D i)).apply_symm_apply _

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
