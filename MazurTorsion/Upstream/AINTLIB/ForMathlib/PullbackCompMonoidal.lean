/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.PresheafPullbackCompMonoidal
import MazurTorsion.Upstream.AINTLIB.Picard.Pullback

/-!
# Monoidality of pullback composition for sheaves of modules

The canonical comparison from iterated pullback to pullback along a composite morphism
of schemes is monoidal. The proof identifies its pullback along module sheafification
with the corresponding presheaf comparison, proves that comparison monoidal, and then
descends through the monoidal localization.

This is an exact-pin port of AINTLIB's `ForMathlib/PullbackCompMonoidal.lean` at
commit `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`. Imports are redirected to the
retained local pullback foundation, two local monoidal instances make that foundation
elaborate at the immutable pin, and one private mate calculation is inlined to avoid
the unrelated dual-pullback dependency cone. Public statements are unchanged.
-/

open AlgebraicGeometry CategoryTheory MonoidalCategory Functor.LaxMonoidal

universe u
universe u₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃

namespace CategoryTheory

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  {L₁ L₂ : Functor C₀ C₁} {R : Functor C₁ C₀}
  {L : Functor C₁ C₂} {S : Functor C₂ C₁}

private theorem conjugateEquiv_leftAdjointUniq_hom'
    (a : L₁ ⊣ R) (b : L₂ ⊣ R) :
    conjugateEquiv b a (Adjunction.leftAdjointUniq a b).hom = 𝟙 R := by
  simp [Adjunction.leftAdjointUniq]

private theorem conjugateEquiv_leftAdjointUniq_inv'
    (a : L₁ ⊣ R) (b : L₂ ⊣ R) :
    conjugateEquiv a b (Adjunction.leftAdjointUniq a b).inv = 𝟙 R := by
  simp [Adjunction.leftAdjointUniq]

private theorem conjugateEquiv_whiskerRight_leftAdjointUniq_hom'
    (a : L₁ ⊣ R) (b : L₂ ⊣ R) (c : L ⊣ S) :
    conjugateEquiv (b.comp c) (a.comp c)
        (Functor.whiskerRight (Adjunction.leftAdjointUniq a b).hom L) =
      Functor.whiskerLeft S (𝟙 R) := by
  rw [conjugateEquiv_whiskerRight]
  rw [conjugateEquiv_leftAdjointUniq_hom']

variable {L' : Functor C₂ C₀} {S' : Functor C₀ C₂}

private theorem conjugateEquiv_whiskerLeft_leftAdjointUniq_hom'
    (a : L₁ ⊣ R) (b : L₂ ⊣ R) (c : L' ⊣ S') :
    conjugateEquiv (c.comp b) (c.comp a)
        (Functor.whiskerLeft L' (Adjunction.leftAdjointUniq a b).hom) =
      Functor.whiskerRight (𝟙 R) S' := by
  rw [conjugateEquiv_whiskerLeft]
  rw [conjugateEquiv_leftAdjointUniq_hom']

variable {C₃ : Type u₀} [Category.{v₀} C₃]
  {F₀₁ : Functor C₀ C₁} {R₁₀ : Functor C₁ C₀}
  {F₁₂ : Functor C₁ C₂} {R₂₁ : Functor C₂ C₁}
  {F₂₃ : Functor C₂ C₃} {R₃₂ : Functor C₃ C₂}

private theorem conjugateEquiv_associator_inv'
    (a : F₀₁ ⊣ R₁₀) (b : F₁₂ ⊣ R₂₁)
    (c : F₂₃ ⊣ R₃₂) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
        (Functor.associator F₀₁ F₁₂ F₂₃).inv =
      (Functor.associator R₃₂ R₂₁ R₁₀).inv := by
  let eL := Functor.associator F₀₁ F₁₂ F₂₃
  let eR := Functor.associator R₃₂ R₂₁ R₁₀
  have hhom := conjugateEquiv_associator_hom a b c
  have h := conjugateEquiv_comm (a.comp (b.comp c)) ((a.comp b).comp c)
    (α := eL.hom) (β := eL.inv) eL.inv_hom_id
  rw [hhom] at h
  change eR.hom ≫
      conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c)) eL.inv = 𝟙 _ at h
  apply (cancel_epi eR.hom).1
  exact h.trans eR.hom_inv_id.symm

variable {C D : Type u₀} [Category.{v₀} C] [Category.{v₁} D]
  {F₀ F₁ F₂ F₃ F₄ F₅ : Functor C D}
  {R₀ R₁ R₂ R₃ R₄ R₅ : Functor D C}

private theorem conjugateEquiv_comp_five'
    (a₀ : F₀ ⊣ R₀) (a₁ : F₁ ⊣ R₁) (a₂ : F₂ ⊣ R₂)
    (a₃ : F₃ ⊣ R₃) (a₄ : F₄ ⊣ R₄) (a₅ : F₅ ⊣ R₅)
    (t₁ : F₀ ⟶ F₁) (t₂ : F₁ ⟶ F₂) (t₃ : F₂ ⟶ F₃)
    (t₄ : F₃ ⟶ F₄) (t₅ : F₄ ⟶ F₅) :
    conjugateEquiv a₅ a₀ (t₁ ≫ t₂ ≫ t₃ ≫ t₄ ≫ t₅) =
      conjugateEquiv a₅ a₄ t₅ ≫ conjugateEquiv a₄ a₃ t₄ ≫
        conjugateEquiv a₃ a₂ t₃ ≫ conjugateEquiv a₂ a₁ t₂ ≫
          conjugateEquiv a₁ a₀ t₁ := by
  have h₄₅ := conjugateEquiv_comp a₅ a₄ a₃ t₅ t₄
  have h₃₄₅ := conjugateEquiv_comp a₅ a₃ a₂ (t₄ ≫ t₅) t₃
  have h₂₃₄₅ := conjugateEquiv_comp a₅ a₂ a₁
    (t₃ ≫ t₄ ≫ t₅) t₂
  have h₁₂₃₄₅ := conjugateEquiv_comp a₅ a₁ a₀
    (t₂ ≫ t₃ ≫ t₄ ≫ t₅) t₁
  calc
    _ = conjugateEquiv a₅ a₁ (t₂ ≫ t₃ ≫ t₄ ≫ t₅) ≫
        conjugateEquiv a₁ a₀ t₁ := h₁₂₃₄₅.symm
    _ = (conjugateEquiv a₅ a₂ (t₃ ≫ t₄ ≫ t₅) ≫
          conjugateEquiv a₂ a₁ t₂) ≫ conjugateEquiv a₁ a₀ t₁ :=
      congrArg (fun k => k ≫ conjugateEquiv a₁ a₀ t₁) h₂₃₄₅.symm
    _ = ((conjugateEquiv a₅ a₃ (t₄ ≫ t₅) ≫
            conjugateEquiv a₃ a₂ t₃) ≫ conjugateEquiv a₂ a₁ t₂) ≫
          conjugateEquiv a₁ a₀ t₁ :=
      congrArg (fun k => (k ≫ conjugateEquiv a₂ a₁ t₂) ≫
        conjugateEquiv a₁ a₀ t₁) h₃₄₅.symm
    _ = (((conjugateEquiv a₅ a₄ t₅ ≫ conjugateEquiv a₄ a₃ t₄) ≫
            conjugateEquiv a₃ a₂ t₃) ≫ conjugateEquiv a₂ a₁ t₂) ≫
          conjugateEquiv a₁ a₀ t₁ :=
      congrArg (fun k => ((k ≫ conjugateEquiv a₃ a₂ t₃) ≫
        conjugateEquiv a₂ a₁ t₂) ≫ conjugateEquiv a₁ a₀ t₁) h₄₅.symm
    _ = _ := by simp only [Category.assoc]

@[implicit_reducible]
private def laxComp'
    {C : Type u₀} {D : Type u₁} {E : Type u₂}
    [Category.{v₀} C] [Category.{v₁} D] [Category.{v₂} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E)
    (hF : F.LaxMonoidal) (hG : G.LaxMonoidal) : (F ⋙ G).LaxMonoidal :=
  @Functor.LaxMonoidal.comp _ _ _ _ _ _ _ _ _ F G hF hG

private theorem associatorHomExplicit
    {C : Type u₀} {D : Type u₁} {E : Type u₂} {K : Type u₃}
    [Category.{v₀} C] [Category.{v₁} D]
    [Category.{v₂} E] [Category.{v₃} K]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory E] [MonoidalCategory K]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)
    (hF : F.LaxMonoidal) (hG : G.LaxMonoidal) (hH : H.LaxMonoidal) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (Functor.associator F G H).hom
      (laxComp' (F ⋙ G) H (laxComp' F G hF hG) hH)
      (laxComp' F (G ⋙ H) hF (laxComp' G H hG hH)) := by
  letI := hF
  letI := hG
  letI := hH
  infer_instance

private theorem associatorInvExplicit
    {C : Type u₀} {D : Type u₁} {E : Type u₂} {K : Type u₃}
    [Category.{v₀} C] [Category.{v₁} D]
    [Category.{v₂} E] [Category.{v₃} K]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory E] [MonoidalCategory K]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)
    (hF : F.LaxMonoidal) (hG : G.LaxMonoidal) (hH : H.LaxMonoidal) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (Functor.associator F G H).inv
      (laxComp' F (G ⋙ H) hF (laxComp' G H hG hH))
      (laxComp' (F ⋙ G) H (laxComp' F G hF hG) hH) := by
  letI := hF
  letI := hG
  letI := hH
  infer_instance

private theorem whiskerRightExplicit
    {C : Type u₀} {D : Type u₁} {E : Type u₂}
    [Category.{v₀} C] [Category.{v₁} D] [Category.{v₂} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    {F₁ F₂ : C ⥤ D} (G : D ⥤ E) (t : F₁ ⟶ F₂)
    (hF₁ : F₁.LaxMonoidal) (hF₂ : F₂.LaxMonoidal)
    (hG : G.LaxMonoidal)
    (ht : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t hF₁ hF₂) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (Functor.whiskerRight t G)
      (laxComp' F₁ G hF₁ hG) (laxComp' F₂ G hF₂ hG) := by
  letI := hF₁
  letI := hF₂
  letI := hG
  letI := ht
  infer_instance

private theorem whiskerLeftExplicit
    {C : Type u₀} {D : Type u₁} {E : Type u₂}
    [Category.{v₀} C] [Category.{v₁} D] [Category.{v₂} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : C ⥤ D) {G₁ G₂ : D ⥤ E} (t : G₁ ⟶ G₂)
    (hF : F.LaxMonoidal) (hG₁ : G₁.LaxMonoidal)
    (hG₂ : G₂.LaxMonoidal)
    (ht : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t hG₁ hG₂) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (Functor.whiskerLeft F t)
      (laxComp' F G₁ hF hG₁) (laxComp' F G₂ hF hG₂) := by
  letI := hF
  letI := hG₁
  letI := hG₂
  letI := ht
  infer_instance

private theorem compExplicit
    {C : Type u₀} {D : Type u₁}
    [Category.{v₀} C] [Category.{v₁} D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F₁ F₂ F₃ : C ⥤ D} (t₁ : F₁ ⟶ F₂) (t₂ : F₂ ⟶ F₃)
    (hF₁ : F₁.LaxMonoidal) (hF₂ : F₂.LaxMonoidal)
    (hF₃ : F₃.LaxMonoidal)
    (ht₁ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₁ hF₁ hF₂)
    (ht₂ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₂ hF₂ hF₃) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (t₁ ≫ t₂) hF₁ hF₃ := by
  letI := hF₁
  letI := hF₂
  letI := hF₃
  letI := ht₁
  letI := ht₂
  infer_instance

private theorem isoInvExplicit
    {C : Type u₀} {D : Type u₁}
    [Category.{v₀} C] [Category.{v₁} D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂)
    (hF₁ : F₁.LaxMonoidal) (hF₂ : F₂.LaxMonoidal)
    (h : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ e.hom hF₁ hF₂) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ e.inv hF₂ hF₁ := by
  letI := hF₁
  letI := hF₂
  letI := h
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

noncomputable local instance presheafModulesMonoidalOfRingSheaf
    (X : Scheme.{u}) : MonoidalCategory
    (_root_.PresheafOfModules.{u}
      ((sheafToPresheaf (Opens.grothendieckTopology ↥X)
        RingCat).obj X.ringCatSheaf)) :=
  inferInstanceAs (MonoidalCategory
    (_root_.PresheafOfModules.{u}
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

noncomputable local instance presheafModulesMonoidalRingCatObj
    (X : Scheme.{u}) :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) := by
  change MonoidalCategory (_root_.PresheafOfModules.{u}
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

private abbrev moduleSheafification (X : Scheme.{u}) :=
  PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)

private abbrev moduleSheafificationRight (X : Scheme.{u}) :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)

private abbrev presheafModulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  PresheafOfModules.pullback.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private abbrev presheafModulePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  PresheafOfModules.pushforward.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

noncomputable local instance compPresheafPushforwardIsRightAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom).IsRightAdjoint := by
  change (PresheafOfModules.pushforward.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom f)).IsRightAdjoint
  exact PresheafOfModules.instIsRightAdjointPushforward
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private abbrev moduleSheafificationAdjunction (X : Scheme.{u}) :=
  PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)

private abbrev presheafModulePullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private abbrev presheafModulePullbackComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  PresheafOfModules.pullbackComp.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom g)
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private abbrev presheafModulePushforwardComp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  PresheafOfModules.pushforwardComp.{u}
    (_root_.PresheafOfModules.schemeRingPresheafHom g)
    (_root_.PresheafOfModules.schemeRingPresheafHom f)

private abbrev modulePullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Scheme.Modules.pullbackPushforwardAdjunction f

private def sheafificationPullbackCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleSheafification Z ⋙
        (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f) ≅
      (presheafModulePullback g ⋙ presheafModulePullback f) ⋙
        moduleSheafification X :=
  (Functor.associator (moduleSheafification Z)
      (Scheme.Modules.pullback g) (Scheme.Modules.pullback f)).symm ≪≫
    Functor.isoWhiskerRight
      (SheafOfModules.sheafificationCompPullback g.toRingCatSheafHom)
      (Scheme.Modules.pullback f) ≪≫
    Functor.associator (presheafModulePullback g)
      (moduleSheafification Y) (Scheme.Modules.pullback f) ≪≫
    Functor.isoWhiskerLeft (presheafModulePullback g)
      (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom) ≪≫
    (Functor.associator (presheafModulePullback g)
      (presheafModulePullback f) (moduleSheafification X)).symm

private theorem sheafificationCompPullback_whiskerRight_mate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    let LZ := moduleSheafification Z
    let LY := moduleSheafification Y
    let preG := presheafModulePullback g
    let shG := Scheme.Modules.pullback g
    let shF := Scheme.Modules.pullback f
    let RY := SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)
    let aZ := moduleSheafificationAdjunction Z
    let ag := Scheme.Modules.pullbackPushforwardAdjunction g
    let af := Scheme.Modules.pullbackPushforwardAdjunction f
    let aY := moduleSheafificationAdjunction Y
    let pg := presheafModulePullbackAdjunction g
    let eG : LZ ⋙ shG ≅ preG ⋙ LY :=
      SheafOfModules.sheafificationCompPullback g.toRingCatSheafHom
    (conjugateEquiv ((pg.comp aY).comp af) ((aZ.comp ag).comp af))
        (Functor.whiskerRight eG.hom shF) =
      Functor.whiskerLeft (Scheme.Modules.pushforward f)
        (𝟙 (RY ⋙ presheafModulePushforward g)) := by
  dsimp only
  exact CategoryTheory.conjugateEquiv_whiskerRight_leftAdjointUniq_hom'
    ((moduleSheafificationAdjunction Z).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g))
    ((presheafModulePullbackAdjunction g).comp
      (moduleSheafificationAdjunction Y))
    (Scheme.Modules.pullbackPushforwardAdjunction f)

private theorem sheafificationCompPullback_whiskerLeft_mate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    let LX := moduleSheafification X
    let LY := moduleSheafification Y
    let preG := presheafModulePullback g
    let preF := presheafModulePullback f
    let RX := SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
    let af := Scheme.Modules.pullbackPushforwardAdjunction f
    let aX := moduleSheafificationAdjunction X
    let aY := moduleSheafificationAdjunction Y
    let pg := presheafModulePullbackAdjunction g
    let pf := presheafModulePullbackAdjunction f
    let eF : LY ⋙ Scheme.Modules.pullback f ≅ preF ⋙ LX :=
      SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom
    (conjugateEquiv (pg.comp (pf.comp aX)) (pg.comp (aY.comp af)))
        (Functor.whiskerLeft preG eF.hom) =
      Functor.whiskerRight
        (𝟙 (RX ⋙ presheafModulePushforward f))
        (presheafModulePushforward g) := by
  dsimp only
  exact CategoryTheory.conjugateEquiv_whiskerLeft_leftAdjointUniq_hom'
    ((moduleSheafificationAdjunction Y).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
    ((presheafModulePullbackAdjunction f).comp
      (moduleSheafificationAdjunction X))
    (presheafModulePullbackAdjunction g)

private theorem pushforwardComp_forget_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerRight (Scheme.Modules.pushforwardComp f g).inv
        (moduleSheafificationRight Z) =
      Functor.whiskerLeft (moduleSheafificationRight X)
        (presheafModulePushforwardComp f g).inv := by
  ext M U x
  rfl

private def pullbackCompLift
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleSheafification Z ⋙
        (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f) ⟶
      moduleSheafification Z ⋙ Scheme.Modules.pullback (f ≫ g) :=
  (sheafificationPullbackCompIso f g).hom ≫
    Functor.whiskerRight
      (presheafModulePullbackComp f g).hom
      (moduleSheafification X) ≫
    (SheafOfModules.sheafificationCompPullback
      (f ≫ g).toRingCatSheafHom).inv

private abbrev moduleDirectPullbackAdjunction
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (moduleSheafificationAdjunction Z).comp (modulePullbackAdjunction (f ≫ g))

private abbrev moduleCompositePullbackAdjunction
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (moduleSheafificationAdjunction Z).comp
    ((modulePullbackAdjunction g).comp (modulePullbackAdjunction f))

private abbrev presheafDirectPullbackAdjunction
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (presheafModulePullbackAdjunction (f ≫ g)).comp
    (moduleSheafificationAdjunction X)

private abbrev presheafCompositePullbackAdjunction
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  ((presheafModulePullbackAdjunction g).comp
    (presheafModulePullbackAdjunction f)).comp
      (moduleSheafificationAdjunction X)

private def pullbackCompLiftMate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (conjugateEquiv (moduleDirectPullbackAdjunction f g)
    (moduleCompositePullbackAdjunction f g)) (pullbackCompLift f g)

private def directSheafificationInvMate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (conjugateEquiv (moduleDirectPullbackAdjunction f g)
    (presheafDirectPullbackAdjunction f g))
      (SheafOfModules.sheafificationCompPullback
        (f ≫ g).toRingCatSheafHom).inv

private def presheafPullbackCompMate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (conjugateEquiv (presheafDirectPullbackAdjunction f g)
    (presheafCompositePullbackAdjunction f g))
      (Functor.whiskerRight
        (presheafModulePullbackComp f g).hom
        (moduleSheafification X))

private def compositeSheafificationMate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (conjugateEquiv (presheafCompositePullbackAdjunction f g)
    (moduleCompositePullbackAdjunction f g))
      (sheafificationPullbackCompIso f g).hom

private def directPresheafCompositeMate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (conjugateEquiv (moduleDirectPullbackAdjunction f g)
    (presheafCompositePullbackAdjunction f g))
      (Functor.whiskerRight
          (presheafModulePullbackComp f g).hom
          (moduleSheafification X) ≫
        (SheafOfModules.sheafificationCompPullback
          (f ≫ g).toRingCatSheafHom).inv)

private theorem pullbackCompLiftMate_decomp_outer
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCompLiftMate f g = directPresheafCompositeMate f g ≫
      compositeSheafificationMate f g := by
  let a := moduleDirectPullbackAdjunction f g
  let c := presheafCompositePullbackAdjunction f g
  let d := moduleCompositePullbackAdjunction f g
  let eComp := sheafificationPullbackCompIso f g
  let σ := Functor.whiskerRight
    (presheafModulePullbackComp f g).hom
    (moduleSheafification X)
  let eFG := SheafOfModules.sheafificationCompPullback
    (f ≫ g).toRingCatSheafHom
  have h₁ := conjugateEquiv_comp a c d (σ ≫ eFG.inv) eComp.hom
  dsimp only [pullbackCompLiftMate, pullbackCompLift,
    directPresheafCompositeMate, compositeSheafificationMate]
  exact h₁.symm

private theorem directPresheafCompositeMate_decomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    directPresheafCompositeMate f g =
      directSheafificationInvMate f g ≫ presheafPullbackCompMate f g := by
  let a := moduleDirectPullbackAdjunction f g
  let b := presheafDirectPullbackAdjunction f g
  let c := presheafCompositePullbackAdjunction f g
  let σ := Functor.whiskerRight
    (presheafModulePullbackComp f g).hom
    (moduleSheafification X)
  let eFG := SheafOfModules.sheafificationCompPullback
    (f ≫ g).toRingCatSheafHom
  have h₂ := conjugateEquiv_comp a b c eFG.inv σ
  dsimp only [directPresheafCompositeMate,
    directSheafificationInvMate, presheafPullbackCompMate]
  exact h₂.symm

private theorem sheafificationCompPullback_inv_mate
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (conjugateEquiv
      ((moduleSheafificationAdjunction Y).comp (modulePullbackAdjunction f))
      ((presheafModulePullbackAdjunction f).comp
        (moduleSheafificationAdjunction X)))
      (SheafOfModules.sheafificationCompPullback
        f.toRingCatSheafHom).inv =
      𝟙 (Scheme.Modules.pushforward f ⋙ moduleSheafificationRight Y) := by
  exact CategoryTheory.conjugateEquiv_leftAdjointUniq_inv'
    ((moduleSheafificationAdjunction Y).comp (modulePullbackAdjunction f))
    ((presheafModulePullbackAdjunction f).comp
      (moduleSheafificationAdjunction X))

private theorem presheafPullbackComp_whisker_mate
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (conjugateEquiv
      ((presheafModulePullbackAdjunction (f ≫ g)).comp
        (moduleSheafificationAdjunction X))
      (((presheafModulePullbackAdjunction g).comp
        (presheafModulePullbackAdjunction f)).comp
          (moduleSheafificationAdjunction X)))
      (Functor.whiskerRight
        (presheafModulePullbackComp f g).hom
        (moduleSheafification X)) =
      Functor.whiskerLeft (moduleSheafificationRight X)
        (presheafModulePushforwardComp f g).inv := by
  let pfg := presheafModulePullbackAdjunction (f ≫ g)
  let pg := presheafModulePullbackAdjunction g
  let pf := presheafModulePullbackAdjunction f
  let aX := moduleSheafificationAdjunction X
  let preComp := presheafModulePullbackComp f g
  have hpre : (conjugateEquiv pfg (pg.comp pf)) preComp.hom =
      (presheafModulePushforwardComp f g).inv := by
    change (conjugateEquiv pfg (pg.comp pf))
      ((conjugateEquiv pfg (pg.comp pf)).symm
        (presheafModulePushforwardComp f g).inv) =
      (presheafModulePushforwardComp f g).inv
    exact (conjugateEquiv pfg (pg.comp pf)).apply_symm_apply _
  have hw := conjugateEquiv_whiskerRight pfg (pg.comp pf) aX preComp.hom
  change (conjugateEquiv (pfg.comp aX) ((pg.comp pf).comp aX))
      (Functor.whiskerRight preComp.hom (moduleSheafification X)) =
    Functor.whiskerLeft (moduleSheafificationRight X)
      ((conjugateEquiv pfg (pg.comp pf)) preComp.hom) at hw
  exact hw.trans (congrArg (Functor.whiskerLeft
    (moduleSheafificationRight X)) hpre)

private theorem directPresheafCompositeMate_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (directPresheafCompositeMate f g).app M =
      (Functor.whiskerLeft (moduleSheafificationRight X)
        (presheafModulePushforwardComp f g).inv).app M := by
  have hinner := NatTrans.congr_app (directPresheafCompositeMate_decomp f g) M
  have heFG : directSheafificationInvMate f g =
      𝟙 (Scheme.Modules.pushforward (f ≫ g) ⋙
        moduleSheafificationRight Z) :=
    sheafificationCompPullback_inv_mate (f ≫ g)
  have hσ : presheafPullbackCompMate f g =
      Functor.whiskerLeft (moduleSheafificationRight X)
        (presheafModulePushforwardComp f g).inv :=
    presheafPullbackComp_whisker_mate f g
  have heFGM := NatTrans.congr_app heFG M
  have hσM := NatTrans.congr_app hσ M
  refine hinner.trans ?_
  change (directSheafificationInvMate f g).app M ≫
    (presheafPullbackCompMate f g).app M = _
  let iFG := 𝟙 (Scheme.Modules.pushforward (f ≫ g) ⋙
    moduleSheafificationRight Z)
  let iM := iFG.app M
  have heFGM' : (directSheafificationInvMate f g).app M = iM := heFGM
  let t := (Functor.whiskerLeft (moduleSheafificationRight X)
    (presheafModulePushforwardComp f g).inv).app M
  have hleft := congrArg
    (fun k => k ≫ (presheafPullbackCompMate f g).app M) heFGM'
  have hright := congrArg (fun k => iM ≫ k) hσM
  have hiM : iM = 𝟙 _ := rfl
  have hunit : iM ≫ t = t :=
    (congrArg (fun k => k ≫ t) hiM).trans (Category.id_comp t)
  exact hleft.trans (hright.trans hunit)

private theorem sheafificationMate_r₁
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (Functor.associator (Scheme.Modules.pushforward f)
      (Scheme.Modules.pushforward g) (moduleSheafificationRight Z)).inv.app M = 𝟙 _ := by
  rfl

private theorem sheafificationMate_r₂
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (Functor.whiskerLeft (Scheme.Modules.pushforward f)
      (𝟙 (moduleSheafificationRight Y ⋙ presheafModulePushforward g))).app M = 𝟙 _ := by
  rfl

private theorem sheafificationMate_r₃
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (Functor.associator (Scheme.Modules.pushforward f)
      (moduleSheafificationRight Y) (presheafModulePushforward g)).hom.app M = 𝟙 _ := by
  rfl

private theorem sheafificationMate_r₄
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (Functor.whiskerRight
      (𝟙 (moduleSheafificationRight X ⋙ presheafModulePushforward f))
      (presheafModulePushforward g)).app M = 𝟙 _ := by
  rfl

private theorem sheafificationMate_r₅
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (Functor.associator (moduleSheafificationRight X)
      (presheafModulePushforward f) (presheafModulePushforward g)).inv.app M = 𝟙 _ := by
  rfl

private theorem sheafificationPullbackCompIso_mate_coherence
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (Functor.associator (moduleSheafificationRight X)
          (presheafModulePushforward f) (presheafModulePushforward g)).inv.app M ≫
      (Functor.whiskerRight
          (𝟙 (moduleSheafificationRight X ⋙ presheafModulePushforward f))
          (presheafModulePushforward g)).app M ≫
      (Functor.associator (Scheme.Modules.pushforward f)
          (moduleSheafificationRight Y) (presheafModulePushforward g)).hom.app M ≫
      (Functor.whiskerLeft (Scheme.Modules.pushforward f)
          (𝟙 (moduleSheafificationRight Y ⋙ presheafModulePushforward g))).app M ≫
      (Functor.associator (Scheme.Modules.pushforward f)
          (Scheme.Modules.pushforward g) (moduleSheafificationRight Z)).inv.app M = 𝟙 _ := by
  rw [sheafificationMate_r₅ f g M, sheafificationMate_r₄ f g M,
    sheafificationMate_r₃ f g M, sheafificationMate_r₂ f g M,
    sheafificationMate_r₁ f g M]
  rfl

private abbrev mateA₀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (moduleSheafificationAdjunction Z).comp
    ((modulePullbackAdjunction g).comp (modulePullbackAdjunction f))

private abbrev mateA₁ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  ((moduleSheafificationAdjunction Z).comp (modulePullbackAdjunction g)).comp
    (modulePullbackAdjunction f)

private abbrev mateA₂ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  ((presheafModulePullbackAdjunction g).comp
    (moduleSheafificationAdjunction Y)).comp (modulePullbackAdjunction f)

private abbrev mateA₃ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (presheafModulePullbackAdjunction g).comp
    ((moduleSheafificationAdjunction Y).comp (modulePullbackAdjunction f))

private abbrev mateA₄ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (presheafModulePullbackAdjunction g).comp
    ((presheafModulePullbackAdjunction f).comp (moduleSheafificationAdjunction X))

private abbrev mateA₅ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  ((presheafModulePullbackAdjunction g).comp
    (presheafModulePullbackAdjunction f)).comp (moduleSheafificationAdjunction X)

private abbrev mateT₁ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (Functor.associator (moduleSheafification Z)
    (Scheme.Modules.pullback g) (Scheme.Modules.pullback f)).inv

private abbrev mateT₂ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Functor.whiskerRight
    (SheafOfModules.sheafificationCompPullback g.toRingCatSheafHom).hom
    (Scheme.Modules.pullback f)

private abbrev mateT₃ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (Functor.associator (presheafModulePullback g)
    (moduleSheafification Y) (Scheme.Modules.pullback f)).hom

private abbrev mateT₄ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  Functor.whiskerLeft (presheafModulePullback g)
    (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom

private abbrev mateT₅ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (Functor.associator (presheafModulePullback g)
    (presheafModulePullback f) (moduleSheafification X)).inv

private theorem sheafificationMate_decomp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (conjugateEquiv (mateA₅ f g) (mateA₀ f g))
        (sheafificationPullbackCompIso f g).hom =
      conjugateEquiv (mateA₅ f g) (mateA₄ f g) (mateT₅ f g) ≫
        conjugateEquiv (mateA₄ f g) (mateA₃ f g) (mateT₄ f g) ≫
          conjugateEquiv (mateA₃ f g) (mateA₂ f g) (mateT₃ f g) ≫
            conjugateEquiv (mateA₂ f g) (mateA₁ f g) (mateT₂ f g) ≫
              conjugateEquiv (mateA₁ f g) (mateA₀ f g) (mateT₁ f g) := by
  exact CategoryTheory.conjugateEquiv_comp_five'
    (mateA₀ f g) (mateA₁ f g) (mateA₂ f g)
    (mateA₃ f g) (mateA₄ f g) (mateA₅ f g)
    (mateT₁ f g) (mateT₂ f g) (mateT₃ f g) (mateT₄ f g) (mateT₅ f g)

private theorem sheafificationMate_component₁
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (mateA₁ f g) (mateA₀ f g) (mateT₁ f g) =
      (Functor.associator (Scheme.Modules.pushforward f)
        (Scheme.Modules.pushforward g) (moduleSheafificationRight Z)).inv :=
  CategoryTheory.conjugateEquiv_associator_inv'
    (moduleSheafificationAdjunction Z) (modulePullbackAdjunction g)
      (modulePullbackAdjunction f)

private theorem sheafificationMate_component₂
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (mateA₂ f g) (mateA₁ f g) (mateT₂ f g) =
      Functor.whiskerLeft (Scheme.Modules.pushforward f)
        (𝟙 (moduleSheafificationRight Y ⋙ presheafModulePushforward g)) := by
  exact sheafificationCompPullback_whiskerRight_mate f g

private theorem sheafificationMate_component₃
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (mateA₃ f g) (mateA₂ f g) (mateT₃ f g) =
      (Functor.associator (Scheme.Modules.pushforward f)
        (moduleSheafificationRight Y) (presheafModulePushforward g)).hom :=
  CategoryTheory.conjugateEquiv_associator_hom
    (presheafModulePullbackAdjunction g) (moduleSheafificationAdjunction Y)
      (modulePullbackAdjunction f)

private theorem sheafificationMate_component₄
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (mateA₄ f g) (mateA₃ f g) (mateT₄ f g) =
      Functor.whiskerRight
        (𝟙 (moduleSheafificationRight X ⋙ presheafModulePushforward f))
        (presheafModulePushforward g) := by
  exact sheafificationCompPullback_whiskerLeft_mate f g

private theorem sheafificationMate_component₅
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (mateA₅ f g) (mateA₄ f g) (mateT₅ f g) =
      (Functor.associator (moduleSheafificationRight X)
        (presheafModulePushforward f) (presheafModulePushforward g)).inv :=
  CategoryTheory.conjugateEquiv_associator_inv'
    (presheafModulePullbackAdjunction g) (presheafModulePullbackAdjunction f)
      (moduleSheafificationAdjunction X)

private abbrev mateQ₁ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (conjugateEquiv (mateA₁ f g) (mateA₀ f g) (mateT₁ f g)).app M

private abbrev mateQ₂ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (conjugateEquiv (mateA₂ f g) (mateA₁ f g) (mateT₂ f g)).app M

private abbrev mateQ₃ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (conjugateEquiv (mateA₃ f g) (mateA₂ f g) (mateT₃ f g)).app M

private abbrev mateQ₄ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (conjugateEquiv (mateA₄ f g) (mateA₃ f g) (mateT₄ f g)).app M

private abbrev mateQ₅ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (conjugateEquiv (mateA₅ f g) (mateA₄ f g) (mateT₅ f g)).app M

private abbrev mateR₁ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (Functor.associator (Scheme.Modules.pushforward f)
    (Scheme.Modules.pushforward g) (moduleSheafificationRight Z)).inv.app M

private abbrev mateR₂ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (Functor.whiskerLeft (Scheme.Modules.pushforward f)
    (𝟙 (moduleSheafificationRight Y ⋙ presheafModulePushforward g))).app M

private abbrev mateR₃ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (Functor.associator (Scheme.Modules.pushforward f)
    (moduleSheafificationRight Y) (presheafModulePushforward g)).hom.app M

private abbrev mateR₄ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (Functor.whiskerRight
    (𝟙 (moduleSheafificationRight X ⋙ presheafModulePushforward f))
    (presheafModulePushforward g)).app M

private abbrev mateR₅ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :=
  (Functor.associator (moduleSheafificationRight X)
    (presheafModulePushforward f) (presheafModulePushforward g)).inv.app M

private theorem sheafificationMate_decomp_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    ((conjugateEquiv (mateA₅ f g) (mateA₀ f g))
        (sheafificationPullbackCompIso f g).hom).app M =
      mateQ₅ f g M ≫ mateQ₄ f g M ≫ mateQ₃ f g M ≫
        mateQ₂ f g M ≫ mateQ₁ f g M :=
  NatTrans.congr_app (sheafificationMate_decomp f g) M

private theorem sheafificationMate_components_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    mateQ₅ f g M ≫ mateQ₄ f g M ≫ mateQ₃ f g M ≫
        mateQ₂ f g M ≫ mateQ₁ f g M =
      mateR₅ f g M ≫ mateR₄ f g M ≫ mateR₃ f g M ≫
        mateR₂ f g M ≫ mateR₁ f g M := by
  have h₁ := NatTrans.congr_app (sheafificationMate_component₁ f g) M
  have h₂ := NatTrans.congr_app (sheafificationMate_component₂ f g) M
  have h₃ := NatTrans.congr_app (sheafificationMate_component₃ f g) M
  have h₄ := NatTrans.congr_app (sheafificationMate_component₄ f g) M
  have h₅ := NatTrans.congr_app (sheafificationMate_component₅ f g) M
  calc
    _ = mateR₅ f g M ≫ mateQ₄ f g M ≫ mateQ₃ f g M ≫
          mateQ₂ f g M ≫ mateQ₁ f g M :=
      congrArg (fun k => k ≫ mateQ₄ f g M ≫ mateQ₃ f g M ≫
        mateQ₂ f g M ≫ mateQ₁ f g M) h₅
    _ = mateR₅ f g M ≫ mateR₄ f g M ≫ mateQ₃ f g M ≫
          mateQ₂ f g M ≫ mateQ₁ f g M :=
      congrArg (fun k => mateR₅ f g M ≫ k ≫ mateQ₃ f g M ≫
        mateQ₂ f g M ≫ mateQ₁ f g M) h₄
    _ = mateR₅ f g M ≫ mateR₄ f g M ≫ mateR₃ f g M ≫
          mateQ₂ f g M ≫ mateQ₁ f g M :=
      congrArg (fun k => mateR₅ f g M ≫ mateR₄ f g M ≫ k ≫
        mateQ₂ f g M ≫ mateQ₁ f g M) h₃
    _ = mateR₅ f g M ≫ mateR₄ f g M ≫ mateR₃ f g M ≫
          mateR₂ f g M ≫ mateQ₁ f g M :=
      congrArg (fun k => mateR₅ f g M ≫ mateR₄ f g M ≫
        mateR₃ f g M ≫ k ≫ mateQ₁ f g M) h₂
    _ = _ := congrArg (fun k => mateR₅ f g M ≫ mateR₄ f g M ≫
      mateR₃ f g M ≫ mateR₂ f g M ≫ k) h₁

private theorem sheafificationMate_coherence_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    mateR₅ f g M ≫ mateR₄ f g M ≫ mateR₃ f g M ≫
      mateR₂ f g M ≫ mateR₁ f g M = 𝟙 _ :=
  sheafificationPullbackCompIso_mate_coherence f g M

private theorem sheafificationPullbackCompIso_mate_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    ((conjugateEquiv
      (((presheafModulePullbackAdjunction g).comp
        (presheafModulePullbackAdjunction f)).comp
          (moduleSheafificationAdjunction X))
      ((moduleSheafificationAdjunction Z).comp
        ((modulePullbackAdjunction g).comp (modulePullbackAdjunction f))))
      (sheafificationPullbackCompIso f g).hom).app M = 𝟙 _ := by
  exact (sheafificationMate_decomp_app f g M).trans
    ((sheafificationMate_components_app f g M).trans
      (sheafificationMate_coherence_app f g M))

private theorem pullbackCompLift_mate_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : X.Modules) :
    (pullbackCompLiftMate f g).app M =
    (Functor.whiskerRight (Scheme.Modules.pushforwardComp f g).inv
      (moduleSheafificationRight Z)).app M := by
  have houter := NatTrans.congr_app (pullbackCompLiftMate_decomp_outer f g) M
  have hdirect := directPresheafCompositeMate_app f g M
  have hcomp := sheafificationPullbackCompIso_mate_app f g M
  have hcomp' : (compositeSheafificationMate f g).app M = 𝟙 _ := hcomp
  have hpush := NatTrans.congr_app (pushforwardComp_forget_eq f g) M
  refine houter.trans (Eq.trans ?_ hpush.symm)
  change (directPresheafCompositeMate f g).app M ≫
    (compositeSheafificationMate f g).app M =
      (Functor.whiskerLeft (moduleSheafificationRight X)
        (presheafModulePushforwardComp f g).inv).app M
  let t := (Functor.whiskerLeft (moduleSheafificationRight X)
    (presheafModulePushforwardComp f g).inv).app M
  have hleft := congrArg
    (fun k => k ≫ (compositeSheafificationMate f g).app M) hdirect
  have hunit : t ≫ (compositeSheafificationMate f g).app M = t :=
    (congrArg (fun k => t ≫ k) hcomp').trans (Category.comp_id t)
  exact hleft.trans hunit

private theorem whiskerLeft_pullbackComp_hom_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerLeft (moduleSheafification Z)
        (Scheme.Modules.pullbackComp f g).hom =
      pullbackCompLift f g := by
  apply (conjugateEquiv (moduleDirectPullbackAdjunction f g)
    (moduleCompositePullbackAdjunction f g)).injective
  have hwhisker := conjugateEquiv_whiskerLeft
    (modulePullbackAdjunction (f ≫ g))
    ((modulePullbackAdjunction g).comp (modulePullbackAdjunction f))
    (moduleSheafificationAdjunction Z)
    (Scheme.Modules.pullbackComp f g).hom
  refine hwhisker.trans ?_
  -- From AINTLIB `Picard/DualPullback/RestrictComp.lean`,
  -- blob `a32b6e89c0bb810b29c5c9bd68f8205f2c7347ca`.
  have hpull :
      conjugateEquiv
          (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
          ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
            (Scheme.Modules.pullbackPushforwardAdjunction f))
          (Scheme.Modules.pullbackComp f g).hom =
        (Scheme.Modules.pushforwardComp f g).inv := by
    let eL := Scheme.Modules.pullbackComp f g
    let eR := Scheme.Modules.pushforwardComp f g
    have h := conjugateEquiv_comm
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      (α := eL.inv) (β := eL.hom) eL.hom_inv_id
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
    apply (cancel_epi eR.hom).1
    exact h.trans eR.hom_inv_id.symm
  change (conjugateEquiv (modulePullbackAdjunction (f ≫ g))
    ((modulePullbackAdjunction g).comp (modulePullbackAdjunction f)))
      (Scheme.Modules.pullbackComp f g).hom = _ at hpull
  refine (congrArg (fun k => Functor.whiskerRight k
    (moduleSheafificationRight Z)) hpull).trans ?_
  apply NatTrans.ext
  funext M
  exact (pullbackCompLift_mate_app f g M).symm

private local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (PresheafOfModules.sheafificationW.{u} (𝟙 X.ringCatSheaf.obj)) := by
  change (PresheafOfModules.sheafification.{u}
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsLocalization
    (PresheafOfModules.sheafificationW.{u}
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj))
  exact PresheafOfModules.sheafificationW_isLocalization
    (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X)

private local instance (X : Scheme.{u}) :
    (PresheafOfModules.sheafificationW.{u}
      (𝟙 X.ringCatSheaf.obj)).IsMonoidal := by
  change (PresheafOfModules.sheafificationW.{u}
    (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsMonoidal
  infer_instance

@[implicit_reducible]
noncomputable local instance moduleMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

@[implicit_reducible]
noncomputable local instance exactModuleMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory
      (SheafOfModules (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : Sheaf _ RingCat.{u})) := by
  change MonoidalCategory X.Modules
  exact moduleMonoidalCategory X

noncomputable local instance {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MonoidalCategory (_root_.PresheafOfModules
      ((TopologicalSpace.Opens.map f.base).op ⋙
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) := by
  rw [show (TopologicalSpace.Opens.map f.base).op ⋙
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) =
      ((TopologicalSpace.Opens.map f.base).op ⋙ X.sheaf.obj) ⋙
        forget₂ CommRingCat RingCat by rfl]
  exact _root_.PresheafOfModules.monoidalCategory

private abbrev exactRingSheaf (X : Scheme.{u}) :=
  (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
    X.ringCatSheaf.property⟩ : Sheaf _ RingCat.{u})

private abbrev exactSheafificationUnit (X : Scheme.{u}) :=
  𝟙 (exactRingSheaf X).obj

private abbrev exactSheafification (X : Scheme.{u}) :=
  PresheafOfModules.sheafification.{u} (exactSheafificationUnit X)

private abbrev exactSheafificationW (X : Scheme.{u}) :=
  PresheafOfModules.sheafificationW.{u} (exactSheafificationUnit X)

private local instance exactSheafificationLocalization (X : Scheme.{u}) :
    (exactSheafification X).IsLocalization (exactSheafificationW X) :=
  PresheafOfModules.sheafificationW_isLocalization (exactRingSheaf X)

private local instance exactSheafificationWMonoidal (X : Scheme.{u}) :
    (exactSheafificationW X).IsMonoidal :=
  PresheafOfModules.sheafificationW_isMonoidal _

private abbrev exactLocalizedSheafification (X : Scheme.{u}) :=
  Localization.Monoidal.toMonoidalCategory
    (L := exactSheafification X) (W := exactSheafificationW X) (Iso.refl _)

private abbrev exactPresheafPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  PresheafOfModules.pullback.{u} (PresheafOfModules.schemeRingPresheafHom f)

private abbrev exactSheafHom {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (⟨PresheafOfModules.schemeRingPresheafHom f⟩ : exactRingSheaf Y ⟶
    ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj (exactRingSheaf X))

private abbrev exactSheafPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pullback.{u} (exactSheafHom f)

@[implicit_reducible]
private noncomputable def exactSheafPullbackMonoidal
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (exactSheafPullback f).Monoidal :=
  PresheafOfModules.sheafPullbackMonoidal
    Y.sheaf.obj Y.ringCatSheaf.property
    X.sheaf.obj X.ringCatSheaf.property
    (PresheafOfModules.schemeRingPresheafHom f)
    (PresheafOfModules.pullbackMonoidal f)

@[implicit_reducible]
private noncomputable def exactSheafPullbackLifting
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Localization.Lifting (exactLocalizedSheafification Y)
      (exactSheafificationW Y)
      (exactPresheafPullback f ⋙ exactLocalizedSheafification X)
      (exactSheafPullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback (exactSheafHom f)⟩

@[implicit_reducible]
private noncomputable def exactLocalizedLax (X : Scheme.{u}) :
    (exactLocalizedSheafification X).LaxMonoidal :=
  (inferInstance : (exactLocalizedSheafification X).Monoidal).toLaxMonoidal

@[implicit_reducible]
private noncomputable def exactPresheafPullbackLax
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exactPresheafPullback f).LaxMonoidal :=
  (PresheafOfModules.pullbackMonoidal f).toLaxMonoidal

@[implicit_reducible]
private noncomputable def exactSheafPullbackLax
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exactSheafPullback f).LaxMonoidal :=
  (exactSheafPullbackMonoidal f).toLaxMonoidal

private def exactSheafificationPullbackCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    exactLocalizedSheafification Z ⋙
        (exactSheafPullback g ⋙ exactSheafPullback f) ≅
      (exactPresheafPullback g ⋙ exactPresheafPullback f) ⋙
        exactLocalizedSheafification X :=
  (Functor.associator (exactLocalizedSheafification Z)
      (exactSheafPullback g) (exactSheafPullback f)).symm ≪≫
    Functor.isoWhiskerRight
      (SheafOfModules.sheafificationCompPullback (exactSheafHom g))
      (exactSheafPullback f) ≪≫
    Functor.associator (exactPresheafPullback g)
      (exactLocalizedSheafification Y) (exactSheafPullback f) ≪≫
    Functor.isoWhiskerLeft (exactPresheafPullback g)
      (SheafOfModules.sheafificationCompPullback (exactSheafHom f)) ≪≫
    (Functor.associator (exactPresheafPullback g)
      (exactPresheafPullback f) (exactLocalizedSheafification X)).symm

@[implicit_reducible]
private noncomputable def exactSheafificationPullbackCompSourceLax
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  CategoryTheory.laxComp' (exactLocalizedSheafification Z)
    (exactSheafPullback g ⋙ exactSheafPullback f) (exactLocalizedLax Z)
    (CategoryTheory.laxComp' (exactSheafPullback g) (exactSheafPullback f)
      (exactSheafPullbackLax g) (exactSheafPullbackLax f))

@[implicit_reducible]
private noncomputable def exactSheafificationPullbackCompTargetLax
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  CategoryTheory.laxComp'
    (exactPresheafPullback g ⋙ exactPresheafPullback f)
    (exactLocalizedSheafification X)
    (CategoryTheory.laxComp' (exactPresheafPullback g)
      (exactPresheafPullback f) (exactPresheafPullbackLax g)
      (exactPresheafPullbackLax f))
    (exactLocalizedLax X)

private theorem exactSheafificationPullbackCompIso_hom_isMonoidal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (exactSheafificationPullbackCompIso f g).hom
      (exactSheafificationPullbackCompSourceLax f g)
      (exactSheafificationPullbackCompTargetLax f g) := by
  letI lX : (exactLocalizedSheafification X).Monoidal := inferInstance
  letI lY : (exactLocalizedSheafification Y).Monoidal := inferInstance
  letI lZ : (exactLocalizedSheafification Z).Monoidal := inferInstance
  letI pF : (exactPresheafPullback f).Monoidal :=
    PresheafOfModules.pullbackMonoidal f
  letI pG : (exactPresheafPullback g).Monoidal :=
    PresheafOfModules.pullbackMonoidal g
  letI pgF : (exactPresheafPullback f ⋙
      exactLocalizedSheafification X).Monoidal := inferInstance
  letI pgG : (exactPresheafPullback g ⋙
      exactLocalizedSheafification Y).Monoidal := inferInstance
  letI liftF : Localization.Lifting (exactLocalizedSheafification Y)
      (exactSheafificationW Y)
      (exactPresheafPullback f ⋙ exactLocalizedSheafification X)
      (exactSheafPullback f) := exactSheafPullbackLifting f
  letI liftG : Localization.Lifting (exactLocalizedSheafification Z)
      (exactSheafificationW Z)
      (exactPresheafPullback g ⋙ exactLocalizedSheafification Y)
      (exactSheafPullback g) := exactSheafPullbackLifting g
  letI fM : (exactSheafPullback f).Monoidal :=
    @Localization.Monoidal.functorMonoidalOfComp
      _ _ _ _ _ _ _ _ _ (exactLocalizedSheafification Y)
      (exactSheafificationW Y) _ _ (exactSheafPullback f)
      (exactPresheafPullback f ⋙ exactLocalizedSheafification X) pgF _ liftF
  letI gM : (exactSheafPullback g).Monoidal :=
    @Localization.Monoidal.functorMonoidalOfComp
      _ _ _ _ _ _ _ _ _ (exactLocalizedSheafification Z)
      (exactSheafificationW Z) _ _ (exactSheafPullback g)
      (exactPresheafPullback g ⋙ exactLocalizedSheafification Y) pgG _ liftG
  letI fLax : (exactSheafPullback f).LaxMonoidal := fM.toLaxMonoidal
  letI gLax : (exactSheafPullback g).LaxMonoidal := gM.toLaxMonoidal
  letI xLax : (exactLocalizedSheafification X).LaxMonoidal :=
    lX.toLaxMonoidal
  letI yLax : (exactLocalizedSheafification Y).LaxMonoidal :=
    lY.toLaxMonoidal
  letI zLax : (exactLocalizedSheafification Z).LaxMonoidal :=
    lZ.toLaxMonoidal
  letI pFLax : (exactPresheafPullback f).LaxMonoidal := pF.toLaxMonoidal
  letI pGLax : (exactPresheafPullback g).LaxMonoidal := pG.toLaxMonoidal
  letI hF := @Localization.Monoidal.lifting_isMonoidal
    _ _ _ _ _ _ _ _ _ (exactLocalizedSheafification Y)
    (exactSheafificationW Y) _ lY (exactSheafPullback f)
    (exactPresheafPullback f ⋙ exactLocalizedSheafification X) pgF _ liftF
  letI hG := @Localization.Monoidal.lifting_isMonoidal
    _ _ _ _ _ _ _ _ _ (exactLocalizedSheafification Z)
    (exactSheafificationW Z) _ lZ (exactSheafPullback g)
    (exactPresheafPullback g ⋙ exactLocalizedSheafification Y) pgG _ liftG
  let eF := Localization.Lifting.iso (exactLocalizedSheafification Y)
    (exactSheafificationW Y)
    (exactPresheafPullback f ⋙ exactLocalizedSheafification X)
    (exactSheafPullback f)
  let eG := Localization.Lifting.iso (exactLocalizedSheafification Z)
    (exactSheafificationW Z)
    (exactPresheafPullback g ⋙ exactLocalizedSheafification Y)
    (exactSheafPullback g)
  let yF := CategoryTheory.laxComp' (exactLocalizedSheafification Y)
    (exactSheafPullback f) yLax fLax
  let zG := CategoryTheory.laxComp' (exactLocalizedSheafification Z)
    (exactSheafPullback g) zLax gLax
  let pFX := CategoryTheory.laxComp' (exactPresheafPullback f)
    (exactLocalizedSheafification X) pFLax xLax
  let pGY := CategoryTheory.laxComp' (exactPresheafPullback g)
    (exactLocalizedSheafification Y) pGLax yLax
  let gF := CategoryTheory.laxComp' (exactSheafPullback g)
    (exactSheafPullback f) gLax fLax
  let source := CategoryTheory.laxComp' (exactLocalizedSheafification Z)
    (exactSheafPullback g ⋙ exactSheafPullback f) zLax gF
  let zGF := CategoryTheory.laxComp'
    (exactLocalizedSheafification Z ⋙ exactSheafPullback g)
    (exactSheafPullback f) zG fLax
  let pGYF := CategoryTheory.laxComp'
    (exactPresheafPullback g ⋙ exactLocalizedSheafification Y)
    (exactSheafPullback f) pGY fLax
  let pGyF := CategoryTheory.laxComp' (exactPresheafPullback g)
    (exactLocalizedSheafification Y ⋙ exactSheafPullback f) pGLax yF
  let pGpFX := CategoryTheory.laxComp' (exactPresheafPullback g)
    (exactPresheafPullback f ⋙ exactLocalizedSheafification X) pGLax pFX
  let pGpF := CategoryTheory.laxComp' (exactPresheafPullback g)
    (exactPresheafPullback f) pGLax pFLax
  let target := CategoryTheory.laxComp'
    (exactPresheafPullback g ⋙ exactPresheafPullback f)
    (exactLocalizedSheafification X) pGpF xLax
  have hF' : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ eF.hom yF pFX := hF
  have hG' : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ eG.hom zG pGY := hG
  let eComp :=
    (Functor.associator (exactLocalizedSheafification Z)
      (exactSheafPullback g) (exactSheafPullback f)).symm ≪≫
    Functor.isoWhiskerRight eG (exactSheafPullback f) ≪≫
    Functor.associator (exactPresheafPullback g)
      (exactLocalizedSheafification Y) (exactSheafPullback f) ≪≫
    Functor.isoWhiskerLeft (exactPresheafPullback g) eF ≪≫
    (Functor.associator (exactPresheafPullback g)
      (exactPresheafPullback f) (exactLocalizedSheafification X)).symm
  let t₁ := (Functor.associator (exactLocalizedSheafification Z)
    (exactSheafPullback g) (exactSheafPullback f)).inv
  let t₂ := Functor.whiskerRight eG.hom (exactSheafPullback f)
  let t₃ := (Functor.associator (exactPresheafPullback g)
    (exactLocalizedSheafification Y) (exactSheafPullback f)).hom
  let t₄ := Functor.whiskerLeft (exactPresheafPullback g) eF.hom
  let t₅ := (Functor.associator (exactPresheafPullback g)
    (exactPresheafPullback f) (exactLocalizedSheafification X)).inv
  have ht₁ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₁ source zGF :=
    CategoryTheory.associatorInvExplicit _ _ _ zLax gLax fLax
  have ht₂ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₂ zGF pGYF :=
    CategoryTheory.whiskerRightExplicit _ eG.hom zG pGY fLax hG'
  have ht₃ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₃ pGYF pGyF :=
    CategoryTheory.associatorHomExplicit _ _ _ pGLax yLax fLax
  have ht₄ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₄ pGyF pGpFX :=
    CategoryTheory.whiskerLeftExplicit _ eF.hom pGLax yF pFX hF'
  have ht₅ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₅ pGpFX target :=
    CategoryTheory.associatorInvExplicit _ _ _ pGLax pFLax xLax
  have ht₁₂ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (t₁ ≫ t₂)
      source pGYF :=
    CategoryTheory.compExplicit t₁ t₂ source zGF pGYF ht₁ ht₂
  have ht₁₂₃ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (t₁ ≫ t₂ ≫ t₃)
      source pGyF :=
    CategoryTheory.compExplicit (t₁ ≫ t₂) t₃ source pGYF pGyF ht₁₂ ht₃
  have ht₁₂₃₄ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (t₁ ≫ t₂ ≫ t₃ ≫ t₄) source pGpFX :=
    CategoryTheory.compExplicit (t₁ ≫ t₂ ≫ t₃) t₄
      source pGyF pGpFX ht₁₂₃ ht₄
  have ht₁₂₃₄₅ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (t₁ ≫ t₂ ≫ t₃ ≫ t₄ ≫ t₅) source target :=
    CategoryTheory.compExplicit (t₁ ≫ t₂ ≫ t₃ ≫ t₄) t₅
      source pGpFX target ht₁₂₃₄ ht₅
  have hEComp : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ eComp.hom
      source target := by
    change @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (t₁ ≫ t₂ ≫ t₃ ≫ t₄ ≫ t₅) source target
    exact ht₁₂₃₄₅
  exact hEComp

private abbrev exactPresheafPullbackCompIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  PresheafOfModules.pullbackComp
    (PresheafOfModules.schemeRingPresheafHom g)
    (PresheafOfModules.schemeRingPresheafHom f)

@[implicit_reducible]
private noncomputable def exactDirectPresheafPullbackLax
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  CategoryTheory.laxComp' (exactPresheafPullback (f ≫ g))
    (exactLocalizedSheafification X) (exactPresheafPullbackLax (f ≫ g))
    (exactLocalizedLax X)

private theorem exactPresheafPullbackComp_whisker_isMonoidal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (Functor.whiskerRight (exactPresheafPullbackCompIso f g).hom
        (exactLocalizedSheafification X))
      (exactSheafificationPullbackCompTargetLax f g)
      (exactDirectPresheafPullbackLax f g) := by
  letI pF : (exactPresheafPullback f).Monoidal :=
    PresheafOfModules.pullbackMonoidal f
  letI pG : (exactPresheafPullback g).Monoidal :=
    PresheafOfModules.pullbackMonoidal g
  letI pFG : (exactPresheafPullback (f ≫ g)).Monoidal :=
    PresheafOfModules.pullbackMonoidal (f ≫ g)
  let pFLax := pF.toLaxMonoidal
  let pGLax := pG.toLaxMonoidal
  let pFGLax := pFG.toLaxMonoidal
  let xLax := exactLocalizedLax X
  let pGpF := CategoryTheory.laxComp' (exactPresheafPullback g)
    (exactPresheafPullback f) pGLax pFLax
  have hPre := PresheafOfModules.pullbackComp_hom_isMonoidal f g
  have hPre' : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (exactPresheafPullbackCompIso f g).hom pGpF pFGLax := hPre
  exact CategoryTheory.whiskerRightExplicit _
    (exactPresheafPullbackCompIso f g).hom pGpF pFGLax xLax hPre'

private abbrev exactDirectSheafificationPullbackIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  SheafOfModules.sheafificationCompPullback (exactSheafHom (f ≫ g))

@[implicit_reducible]
private noncomputable def exactDirectSheafPullbackLax
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  CategoryTheory.laxComp' (exactLocalizedSheafification Z)
    (exactSheafPullback (f ≫ g)) (exactLocalizedLax Z)
    (exactSheafPullbackLax (f ≫ g))

private theorem exactDirectSheafificationPullbackIso_inv_isMonoidal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (exactDirectSheafificationPullbackIso f g).inv
      (exactDirectPresheafPullbackLax f g)
      (exactDirectSheafPullbackLax f g) := by
  letI lX : (exactLocalizedSheafification X).Monoidal := inferInstance
  letI lZ : (exactLocalizedSheafification Z).Monoidal := inferInstance
  letI pFG : (exactPresheafPullback (f ≫ g)).Monoidal :=
    PresheafOfModules.pullbackMonoidal (f ≫ g)
  letI pgFG : (exactPresheafPullback (f ≫ g) ⋙
      exactLocalizedSheafification X).Monoidal := inferInstance
  letI liftFG : Localization.Lifting (exactLocalizedSheafification Z)
      (exactSheafificationW Z)
      (exactPresheafPullback (f ≫ g) ⋙ exactLocalizedSheafification X)
      (exactSheafPullback (f ≫ g)) := exactSheafPullbackLifting (f ≫ g)
  letI fgM : (exactSheafPullback (f ≫ g)).Monoidal :=
    @Localization.Monoidal.functorMonoidalOfComp
      _ _ _ _ _ _ _ _ _ (exactLocalizedSheafification Z)
      (exactSheafificationW Z) _ _ (exactSheafPullback (f ≫ g))
      (exactPresheafPullback (f ≫ g) ⋙
        exactLocalizedSheafification X) pgFG _ liftFG
  let zLax := lZ.toLaxMonoidal
  let xLax := lX.toLaxMonoidal
  let pFGLax := pFG.toLaxMonoidal
  let fgLax := fgM.toLaxMonoidal
  let source := CategoryTheory.laxComp' (exactLocalizedSheafification Z)
    (exactSheafPullback (f ≫ g)) zLax fgLax
  let target := CategoryTheory.laxComp' (exactPresheafPullback (f ≫ g))
    (exactLocalizedSheafification X) pFGLax xLax
  letI hFG := @Localization.Monoidal.lifting_isMonoidal
    _ _ _ _ _ _ _ _ _ (exactLocalizedSheafification Z)
    (exactSheafificationW Z) _ lZ (exactSheafPullback (f ≫ g))
    (exactPresheafPullback (f ≫ g) ⋙ exactLocalizedSheafification X)
    pgFG _ liftFG
  let eFG := Localization.Lifting.iso (exactLocalizedSheafification Z)
    (exactSheafificationW Z)
    (exactPresheafPullback (f ≫ g) ⋙ exactLocalizedSheafification X)
    (exactSheafPullback (f ≫ g))
  have hFG' : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ eFG.hom
      source target := hFG
  exact CategoryTheory.isoInvExplicit eFG source target hFG'

private theorem pullbackCompLift_isMonoidal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (pullbackCompLift f g)
      (exactSheafificationPullbackCompSourceLax f g)
      (exactDirectSheafPullbackLax f g) := by
  let t₁ := (exactSheafificationPullbackCompIso f g).hom
  let t₂ := Functor.whiskerRight (exactPresheafPullbackCompIso f g).hom
    (exactLocalizedSheafification X)
  let t₃ := (exactDirectSheafificationPullbackIso f g).inv
  have ht₁ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₁
      (exactSheafificationPullbackCompSourceLax f g)
      (exactSheafificationPullbackCompTargetLax f g) :=
    exactSheafificationPullbackCompIso_hom_isMonoidal f g
  have ht₂ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₂
      (exactSheafificationPullbackCompTargetLax f g)
      (exactDirectPresheafPullbackLax f g) :=
    exactPresheafPullbackComp_whisker_isMonoidal f g
  have ht₃ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ t₃
      (exactDirectPresheafPullbackLax f g)
      (exactDirectSheafPullbackLax f g) :=
    exactDirectSheafificationPullbackIso_inv_isMonoidal f g
  have ht₁₂ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (t₁ ≫ t₂)
      (exactSheafificationPullbackCompSourceLax f g)
      (exactDirectPresheafPullbackLax f g) :=
    CategoryTheory.compExplicit t₁ t₂
      (exactSheafificationPullbackCompSourceLax f g)
      (exactSheafificationPullbackCompTargetLax f g)
      (exactDirectPresheafPullbackLax f g) ht₁ ht₂
  have ht₁₂₃ : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (t₁ ≫ t₂ ≫ t₃)
      (exactSheafificationPullbackCompSourceLax f g)
      (exactDirectSheafPullbackLax f g) :=
    CategoryTheory.compExplicit (t₁ ≫ t₂) t₃
      (exactSheafificationPullbackCompSourceLax f g)
      (exactDirectPresheafPullbackLax f g)
      (exactDirectSheafPullbackLax f g) ht₁₂ ht₃
  change @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (t₁ ≫ t₂ ≫ t₃)
    (exactSheafificationPullbackCompSourceLax f g)
    (exactDirectSheafPullbackLax f g)
  exact ht₁₂₃

/-- The canonical comparison between a composite pullback of sheaves of modules and
the iterated pullback is monoidal. -/
theorem pullbackComp_hom_isMonoidal
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    letI : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
    letI : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
    letI : MonoidalCategory Z.Modules := Scheme.Modules.monoidalCategory Z
    letI : (Scheme.Modules.pullback f).Monoidal :=
      Scheme.Modules.pullbackMonoidal f
    letI : (Scheme.Modules.pullback g).Monoidal :=
      Scheme.Modules.pullbackMonoidal g
    letI : (Scheme.Modules.pullback (f ≫ g)).Monoidal :=
      Scheme.Modules.pullbackMonoidal (f ≫ g)
    (Scheme.Modules.pullbackComp f g).hom.IsMonoidal := by
  letI : MonoidalCategory X.Modules := Scheme.Modules.monoidalCategory X
  letI : MonoidalCategory Y.Modules := Scheme.Modules.monoidalCategory Y
  letI : MonoidalCategory Z.Modules := Scheme.Modules.monoidalCategory Z
  letI : MonoidalCategory (SheafOfModules Z.ringCatSheaf) :=
    Scheme.Modules.monoidalCategory Z
  letI fM : (Scheme.Modules.pullback f).Monoidal :=
    Scheme.Modules.pullbackMonoidal f
  letI gM : (Scheme.Modules.pullback g).Monoidal :=
    Scheme.Modules.pullbackMonoidal g
  letI fgM : (Scheme.Modules.pullback (f ≫ g)).Monoidal :=
    Scheme.Modules.pullbackMonoidal (f ≫ g)
  letI gfM : (Scheme.Modules.pullback g ⋙
      Scheme.Modules.pullback f).Monoidal :=
    @Functor.Monoidal.instComp _ _ _ _ _ _ _ _ _
      (Scheme.Modules.pullback g) (Scheme.Modules.pullback f) gM fM
  letI lZ : (moduleSheafification Z).Monoidal := by
    change (exactLocalizedSheafification Z).Monoidal
    infer_instance
  let zLax := lZ.toLaxMonoidal
  let fgLax := fgM.toLaxMonoidal
  let gfLax := gfM.toLaxMonoidal
  let source := CategoryTheory.laxComp' (moduleSheafification Z)
    (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f) zLax gfLax
  let target := CategoryTheory.laxComp' (moduleSheafification Z)
    (Scheme.Modules.pullback (f ≫ g)) zLax fgLax
  have hLift : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (pullbackCompLift f g) source target := by
    exact pullbackCompLift_isMonoidal f g
  have hWhisker : @NatTrans.IsMonoidal _ _ _ _ _ _ _ _
      (Functor.whiskerLeft (moduleSheafification Z)
        (Scheme.Modules.pullbackComp f g).hom) source target := by
    rw [whiskerLeft_pullbackComp_hom_eq f g]
    exact hLift
  exact @NatTrans.IsMonoidal.of_whiskerLeft_localization
    _ _ _ _ _ _ _ _ _ (moduleSheafification Z)
    (PresheafOfModules.sheafificationW (𝟙 Z.ringCatSheaf.obj))
    _ _ lZ (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f)
    (Scheme.Modules.pullback (f ≫ g)) gfM fgM
    (Scheme.Modules.pullbackComp f g).hom hWhisker

end

end AlgebraicGeometry.Scheme.Modules
