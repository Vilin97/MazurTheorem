/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentPresentation

/-!
# Global sections of an equalizer descent object

Evaluation at the terminal open preserves limits.  Consequently, global
sections of `glueObject` are exactly compatible families of chart sections.
This is the section-level interface needed for computations with a descended
line bundle.
-/

open CategoryTheory Limits Opposite

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent

open _root_.AlgebraicGeometry

/-- Global sections at the terminal open as a functor. -/
abbrev gammaTop (X : Scheme.{0}) :
    X.Modules ⥤ ModuleCat.{0}
      (X.ringCatSheaf.obj.obj (op ⊤)) :=
  SheafOfModules.evaluation _ (op ⊤)

instance gammaTop_preservesLimits (X : Scheme.{0}) :
    PreservesLimitsOfSize.{0, 0} (gammaTop X) :=
  inferInstanceAs
    (PreservesLimitsOfSize.{0, 0}
      (SheafOfModules.evaluation
        (R := X.ringCatSheaf) (op ⊤)))

/-- Comparison from sections of a product to the product of sections. -/
def gammaProductHom {X : Scheme.{0}} {ι : Type}
    (N : ι → X.Modules) :
    (gammaTop X).obj (∏ᶜ N) ⟶
      ModuleCat.of _
        (∀ i, ((gammaTop X).obj (N i) : Type)) :=
  piComparison (gammaTop X) N ≫
    (ModuleCat.piIsoPi
      (fun i => (gammaTop X).obj (N i))).hom

instance gammaProductHom_isIso
    {X : Scheme.{0}} {ι : Type} (N : ι → X.Modules) :
    IsIso (gammaProductHom N) := by
  dsimp only [gammaProductHom]
  infer_instance

lemma gammaProductHom_apply
    {X : Scheme.{0}} {ι : Type} (N : ι → X.Modules)
    (x : Γ(∏ᶜ N, ⊤)) (i : ι) :
    gammaProductHom N x i = (Pi.π N i).app ⊤ x :=
  show gammaProductHom N x i =
      (gammaTop X).map (Pi.π N i) x from
  calc
    gammaProductHom N x i =
        ((ModuleCat.piIsoPi
          (fun i => (gammaTop X).obj (N i))).hom
            (piComparison (gammaTop X) N x)) i := rfl
    _ = Pi.π (fun i => (gammaTop X).obj (N i)) i
          (piComparison (gammaTop X) N x) :=
      congr(($(ModuleCat.piIsoPi_hom_ker_subtype
        (fun i => (gammaTop X).obj (N i)) i))
          (piComparison (gammaTop X) N x))
    _ = (gammaTop X).map (Pi.π N i) x :=
      congr(($(piComparison_comp_π (gammaTop X) N i)) x)

lemma gamma_product_ext
    {X : Scheme.{0}} {ι : Type} (N : ι → X.Modules)
    {x y : Γ(∏ᶜ N, ⊤)}
    (h : ∀ i,
      (Pi.π N i).app ⊤ x = (Pi.π N i).app ⊤ y) :
    x = y := by
  have hinjective :
      Function.Injective (gammaProductHom N) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hinjective
  funext i
  rw [gammaProductHom_apply, gammaProductHom_apply]
  exact h i

lemma gamma_product_surjective
    {X : Scheme.{0}} {ι : Type} (N : ι → X.Modules)
    (s : ∀ i, Γ(N i, ⊤)) :
    ∃ x : Γ(∏ᶜ N, ⊤),
      ∀ i, (Pi.π N i).app ⊤ x = s i := by
  refine ⟨inv (gammaProductHom N) s, fun i => ?_⟩
  have h :
      gammaProductHom N (inv (gammaProductHom N) s) = s :=
    congr(($(IsIso.inv_hom_id (gammaProductHom N))) s)
  exact (gammaProductHom_apply N _ i).symm.trans (congrFun h i)

private lemma moduleCat_equalizer_element_lift
    {R : RingCat.{0}} {A B : ModuleCat.{0} R}
    (f g : A ⟶ B) (x : A) (h : f x = g x) :
    ∃ z : (equalizer f g : ModuleCat.{0} R),
      equalizer.ι f g z = x := by
  have hcondition :
      ModuleCat.ofHom (LinearMap.toSpanSingleton R A x) ≫ f =
        ModuleCat.ofHom (LinearMap.toSpanSingleton R A x) ≫ g := by
    ext : 1
    apply LinearMap.ext_ring
    change
      f (LinearMap.toSpanSingleton
        (R : Type) (A : Type) x (1 : R)) =
      g (LinearMap.toSpanSingleton
        (R : Type) (A : Type) x (1 : R))
    have h1 :
        LinearMap.toSpanSingleton
          (R : Type) (A : Type) x (1 : R) = x :=
      one_smul _ x
    rw [h1]
    exact h
  refine
    ⟨equalizer.lift
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R A x))
      hcondition (1 : R), ?_⟩
  have hlift := congr(
    ($(equalizer.lift_ι
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R A x))
      hcondition)) (1 : R))
  exact hlift.trans (one_smul _ x)

variable (D : Scheme.GlueData.{0})
  (M : ∀ i, (D.U i).Modules)
  (e : ∀ i j,
    (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
      (Scheme.Modules.pullback
        (D.t i j ≫ D.f j i)).obj (M j))

/-- Compatible families of chart sections. -/
def CompatibleSections :
    Submodule Γ(D.glued, ⊤)
      (∀ i,
        Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤)) where
  carrier := {s | ∀ p : D.J × D.J,
    (firstComponent D M p).app ⊤ (s p.1) =
      (secondComponent D M e p).app ⊤ (s p.2)}
  add_mem' := by
    intro s t hs ht p
    simp only [Pi.add_apply, map_add]
    rw [hs p, ht p]
  zero_mem' := by
    intro p
    simp only [Pi.zero_apply, map_zero]
  smul_mem' := by
    intro r s hs p
    simp only [Pi.smul_apply,
      AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
    rw [hs p]

variable
  (hIdentity : ∀ i, e i i =
    eqToIso (congrArg
      (fun f => (Scheme.Modules.pullback f).obj (M i))
      (show D.f i i = D.t i i ≫ D.f i i by
        rw [D.t_id i, Category.id_comp])))
  (hCocycle : ∀ i j k,
    pullbackTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i) (e i j) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeMiddle D i j k)).app (M j) ≪≫
      pullbackTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j) (e j k) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeTarget D i j k)).app (M k) =
    (Scheme.Modules.pullbackCongr
      (bridgeSource D i j k)).app (M i) ≪≫
      pullbackTransport
        (pullback.snd (D.f i j) (D.f i k))
        (D.f i k) (D.t i k ≫ D.f k i) (e i k))

lemma projection_app_compatible
    (w : Γ(glueObject D M e hIdentity hCocycle, ⊤)) :
    (fun i =>
      (projection D M e hIdentity hCocycle i).app ⊤ w) ∈
      CompatibleSections D M e := by
  intro p
  have h := congrArg
    (fun f => f.app ⊤ w)
    (projection_compatibility
      D M e hIdentity hCocycle p)
  exact h

/-- Map a global section to its family of chart projections. -/
def sectionsToFamily :
    Γ(glueObject D M e hIdentity hCocycle, ⊤) →ₗ[Γ(D.glued, ⊤)]
      ∀ i,
        Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤) where
  toFun w i :=
    (projection D M e hIdentity hCocycle i).app ⊤ w
  map_add' x y := by
    funext i
    simp only [map_add, Pi.add_apply]
  map_smul' r x := by
    funext i
    simp only [
      AlgebraicGeometry.Scheme.Modules.Hom.app_smul,
      RingHom.id_apply, Pi.smul_apply]

lemma projection_app_factor
    (w : Γ(glueObject D M e hIdentity hCocycle, ⊤))
    (i : D.J) :
    (projection D M e hIdentity hCocycle i).app ⊤ w =
      (Pi.π (fun i =>
        (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤
        (((glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          equalizer.ι (firstLeg D M) (secondLeg D M e)).app ⊤ w) := by
  have h :
      projection D M e hIdentity hCocycle i =
        ((glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          equalizer.ι (firstLeg D M) (secondLeg D M e)) ≫
          Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i := by
    dsimp only [projection]
    exact (Category.assoc _ _ _).symm
  exact congrArg (fun f => f.app ⊤ w) h

lemma sections_ext
    {w w' : Γ(glueObject D M e hIdentity hCocycle, ⊤)}
    (h : ∀ i,
      (projection D M e hIdentity hCocycle i).app ⊤ w =
        (projection D M e hIdentity hCocycle i).app ⊤ w') :
    w = w' := by
  have hmono :
      Mono ((gammaTop D.glued).map
        ((glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          equalizer.ι (firstLeg D M) (secondLeg D M e))) := by
    rw [Functor.map_comp]
    have :
        Mono ((gammaTop D.glued).map
          (equalizer.ι (firstLeg D M) (secondLeg D M e))) := by
      rw [← equalizerComparison_comp_π]
      exact mono_comp _ _
    exact mono_comp _ _
  have hinjective :
      Function.Injective ((gammaTop D.glued).map
        ((glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          equalizer.ι (firstLeg D M) (secondLeg D M e))) :=
    (ModuleCat.mono_iff_injective _).mp hmono
  apply hinjective
  apply gamma_product_ext
  intro i
  exact
    (projection_app_factor
      D M e hIdentity hCocycle w i).symm.trans
      ((h i).trans
        (projection_app_factor
          D M e hIdentity hCocycle w' i))

private lemma sections_surjective_on_compatible
    (s : ∀ i,
      Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤))
    (hs : s ∈ CompatibleSections D M e) :
    ∃ w : Γ(glueObject D M e hIdentity hCocycle, ⊤),
      ∀ i,
        (projection D M e hIdentity hCocycle i).app ⊤ w =
          s i := by
  obtain ⟨x, hx⟩ :=
    gamma_product_surjective
      (fun i =>
        (Scheme.Modules.pushforward (D.ι i)).obj (M i)) s
  have hequal :
      (firstLeg D M).app ⊤ x =
        (secondLeg D M e).app ⊤ x := by
    apply gamma_product_ext
    intro p
    calc
      (Pi.π (fun q : D.J × D.J =>
          (Scheme.Modules.pushforward
            (D.f q.1 q.2 ≫ D.ι q.1)).obj
              ((Scheme.Modules.pullback
                (D.f q.1 q.2)).obj (M q.1))) p).app ⊤
          ((firstLeg D M).app ⊤ x) =
        (firstLeg D M ≫
          Pi.π (fun q : D.J × D.J =>
            (Scheme.Modules.pushforward
              (D.f q.1 q.2 ≫ D.ι q.1)).obj
                ((Scheme.Modules.pullback
                  (D.f q.1 q.2)).obj (M q.1))) p).app ⊤ x := rfl
      _ = (Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i))
              p.1 ≫ firstComponent D M p).app ⊤ x :=
        congrArg (fun f => f.app ⊤ x)
          (firstLeg_projection D M p)
      _ = (firstComponent D M p).app ⊤
          ((Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i))
              p.1).app ⊤ x) := rfl
      _ = (firstComponent D M p).app ⊤ (s p.1) :=
        congrArg (fun z => (firstComponent D M p).app ⊤ z)
          (hx p.1)
      _ = (secondComponent D M e p).app ⊤ (s p.2) :=
        hs p
      _ = (secondComponent D M e p).app ⊤
          ((Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i))
              p.2).app ⊤ x) :=
        congrArg (fun z => (secondComponent D M e p).app ⊤ z)
          (hx p.2).symm
      _ = (Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i))
              p.2 ≫ secondComponent D M e p).app ⊤ x := rfl
      _ = (secondLeg D M e ≫
          Pi.π (fun q : D.J × D.J =>
            (Scheme.Modules.pushforward
              (D.f q.1 q.2 ≫ D.ι q.1)).obj
                ((Scheme.Modules.pullback
                  (D.f q.1 q.2)).obj (M q.1))) p).app ⊤ x :=
        congrArg (fun f => f.app ⊤ x)
          (secondLeg_projection D M e p).symm
      _ = (Pi.π (fun q : D.J × D.J =>
          (Scheme.Modules.pushforward
            (D.f q.1 q.2 ≫ D.ι q.1)).obj
              ((Scheme.Modules.pullback
                (D.f q.1 q.2)).obj (M q.1))) p).app ⊤
          ((secondLeg D M e).app ⊤ x) := rfl
  obtain ⟨z, hz⟩ :=
    moduleCat_equalizer_element_lift
      ((gammaTop D.glued).map (firstLeg D M))
      ((gammaTop D.glued).map (secondLeg D M e))
      x hequal
  let comparison :=
    equalizerComparison
      (firstLeg D M) (secondLeg D M e) (gammaTop D.glued)
  refine
    ⟨(glueIsoEqualizer D M e hIdentity hCocycle).inv.app ⊤
      (inv comparison z), fun i => ?_⟩
  have hinclusion :
      (equalizer.ι (firstLeg D M) (secondLeg D M e)).app ⊤
          (inv comparison z) =
        x := by
    have h :
        inv comparison ≫
            (gammaTop D.glued).map
              (equalizer.ι (firstLeg D M) (secondLeg D M e)) =
          equalizer.ι
            ((gammaTop D.glued).map (firstLeg D M))
            ((gammaTop D.glued).map (secondLeg D M e)) := by
      rw [IsIso.inv_comp_eq]
      exact
        (equalizerComparison_comp_π _ _ _).symm
    exact (congr(($(h)) z)).trans hz
  have hfactor :
      (glueIsoEqualizer D M e hIdentity hCocycle).inv ≫
          projection D M e hIdentity hCocycle i =
        equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
          Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i := by
    rw [projection, Iso.inv_hom_id_assoc]
  calc
    (projection D M e hIdentity hCocycle i).app ⊤
        ((glueIsoEqualizer D M e hIdentity hCocycle).inv.app ⊤
          (inv comparison z)) =
      ((glueIsoEqualizer D M e hIdentity hCocycle).inv ≫
        projection D M e hIdentity hCocycle i).app ⊤
          (inv comparison z) := rfl
    _ = (equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
          Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤
          (inv comparison z) :=
      congrArg (fun f => f.app ⊤ (inv comparison z)) hfactor
    _ = (Pi.π (fun i =>
          (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤
        ((equalizer.ι (firstLeg D M) (secondLeg D M e)).app ⊤
          (inv comparison z)) := rfl
    _ = (Pi.π (fun i =>
          (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤ x :=
      congrArg
        (fun y =>
          (Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i)) i).app ⊤ y)
        hinclusion
    _ = s i := hx i

/-- Global sections of the descended object are linearly equivalent to
compatible families of chart sections. -/
def sectionsEquiv :
    Γ(glueObject D M e hIdentity hCocycle, ⊤) ≃ₗ[Γ(D.glued, ⊤)]
      CompatibleSections D M e :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (CompatibleSections D M e)
      (sectionsToFamily D M e hIdentity hCocycle)
      (projection_app_compatible D M e hIdentity hCocycle))
    ⟨fun x y h =>
      sections_ext D M e hIdentity hCocycle
        (fun i => congrFun (congrArg Subtype.val h) i),
      fun s => by
        obtain ⟨w, hw⟩ :=
          sections_surjective_on_compatible
            D M e hIdentity hCocycle s.val s.property
        exact ⟨w, Subtype.ext (funext hw)⟩⟩

@[simp]
lemma sectionsEquiv_apply
    (w : Γ(glueObject D M e hIdentity hCocycle, ⊤))
    (i : D.J) :
    (sectionsEquiv D M e hIdentity hCocycle w :
      ∀ i,
        Γ((Scheme.Modules.pushforward (D.ι i)).obj (M i), ⊤)) i =
      (projection D M e hIdentity hCocycle i).app ⊤ w :=
  rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
