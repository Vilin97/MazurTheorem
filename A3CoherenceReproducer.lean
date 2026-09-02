import MazurTorsion.Upstream.AffineDivisorLocalization
import Mathlib.CategoryTheory.Adjunction.CompositionIso

open CategoryTheory
open _root_.AlgebraicGeometry

namespace A3CoherenceReproducer

universe u

private noncomputable abbrev evalTop
    (A : CommRingCat.{u}) :
    TopCat.Sheaf (ModuleCat A) (Spec A) ⥤ ModuleCat A :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤)

private noncomputable abbrev sectionsPreimage
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    (Spec B).Modules ⥤ ModuleCat A :=
  modulesSpecToSheaf (R := B) ⋙
    TopCat.Sheaf.forget _ _ ⋙
    (evaluation _ _).obj (.op ((Spec.map f) ⁻¹ᵁ (⊤ : (Spec A).Opens))) ⋙
    ModuleCat.restrictScalars f.hom

private noncomputable abbrev sectionsTop
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    (Spec B).Modules ⥤ ModuleCat A :=
  moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars f.hom

private noncomputable def sectionsPreimageIsoTop
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    sectionsPreimage A B f ≅ sectionsTop A B f := by
  let h : (Spec.map f) ⁻¹ᵁ (⊤ : (Spec A).Opens) = (⊤ : (Spec B).Opens) :=
    Scheme.Hom.preimage_top (Spec.map f)
  let eEval := (evaluation ((Spec B).Opens)ᵒᵖ (ModuleCat B)).mapIso
    ((eqToIso h).op.symm)
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (modulesSpecToSheaf (R := B))
      (Functor.isoWhiskerLeft (TopCat.Sheaf.forget _ _) eEval))
    (ModuleCat.restrictScalars f.hom)

private noncomputable def gammaPushforwardIsoRestrictScalars
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars f.hom := by
  refine (Functor.isoWhiskerRight
    (pushforwardCompModulesSpecToSheafIso f) (evalTop A)) ≪≫ ?_
  exact sectionsPreimageIsoTop A B f

private noncomputable def extendTildeAdjunction
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    ModuleCat.extendScalars f.hom ⋙ tilde.functor B ⊣
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars f.hom :=
  (ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := B))

private noncomputable def tildePullbackAdjunction
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map f) ⊣
      Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor (R := A) :=
  (tilde.adjunction (R := A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))

private noncomputable def extendScalarsTildeIsoPullback
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    ModuleCat.extendScalars f.hom ⋙ tilde.functor B ≅
      tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map f) :=
  (conjugateIsoEquiv (tildePullbackAdjunction A B f)
    (extendTildeAdjunction A B f)).symm
      (gammaPushforwardIsoRestrictScalars A B f)

private lemma conjugateEquiv_extendScalarsTildeIsoPullback_hom
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    conjugateEquiv (tildePullbackAdjunction A B f)
        (extendTildeAdjunction A B f)
        (extendScalarsTildeIsoPullback A B f).hom =
      (gammaPushforwardIsoRestrictScalars A B f).hom := by
  rw [← conjugateIsoEquiv_apply_hom]
  exact congrArg Iso.hom <|
    (conjugateIsoEquiv (tildePullbackAdjunction A B f)
      (extendTildeAdjunction A B f)).apply_symm_apply _

private lemma conjugateEquiv_pullbackCongr_hom
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction g)
        (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackCongr h).hom =
      (Scheme.Modules.pushforwardCongr h).inv := by
  cases h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    conjugateEquiv_id]
  ext M U x
  rw [Scheme.Modules.pushforwardCongr_inv_app_app]
  simp

private lemma pushforwardCongr_symm_hom
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pushforwardCongr h.symm).hom =
      (Scheme.Modules.pushforwardCongr h).inv := by
  cases h
  ext M U x
  rw [Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app]

private noncomputable def gammaPushforwardIsoRestrictScalarsCompPath
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    Scheme.Modules.pushforward (Spec.map g ≫ Spec.map f) ⋙
        moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := C) ⋙
        ModuleCat.restrictScalars (f ≫ g).hom :=
  Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).symm
      (moduleSpecΓFunctor (R := A)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward (Spec.map g))
      (gammaPushforwardIsoRestrictScalars A B f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (gammaPushforwardIsoRestrictScalars B C g)
      (ModuleCat.restrictScalars f.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := C))
      (ModuleCat.restrictScalarsComp f.hom g.hom).symm

private theorem gammaPushforwardIsoRestrictScalars_comp
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    gammaPushforwardIsoRestrictScalarsCompPath A B C f g =
      Functor.isoWhiskerRight
          (Scheme.Modules.pushforwardCongr
            (show Spec.map g ≫ Spec.map f = Spec.map (f ≫ g) from
              (@Spec.map_comp A B C f g).symm))
          (moduleSpecΓFunctor (R := A)) ≪≫
        gammaPushforwardIsoRestrictScalars A C (f ≫ g) := by
  apply Iso.ext
  ext M x
  rfl

section DefinitionalChecks

variable (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C)

example : extendScalarsTildeIsoPullback B C g =
    (ModuleCat.extendRestrictScalarsAdj g.hom).leftAdjointCompIso
      (tilde.adjunction (R := C)) (tildePullbackAdjunction B C g)
      (gammaPushforwardIsoRestrictScalars B C g).symm := by
  rfl

example : ModuleCat.extendScalarsComp f.hom g.hom =
    ((ModuleCat.extendRestrictScalarsAdj f.hom).leftAdjointCompIso
      (ModuleCat.extendRestrictScalarsAdj g.hom)
      (ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom)
      (ModuleCat.restrictScalarsComp f.hom g.hom)).symm := by
  rfl

example : Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) =
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).leftAdjointCompIso
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g ≫ Spec.map f))
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)) := by
  rfl

end DefinitionalChecks

section RightAdjointCoherence

variable (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C)

private noncomputable def pushGammaRestrictCompIso :
    (Scheme.Modules.pushforward (Spec.map g) ⋙ moduleSpecΓFunctor (R := B)) ⋙
        ModuleCat.restrictScalars f.hom ≅
      Scheme.Modules.pushforward (Spec.map g ≫ Spec.map f) ⋙
        moduleSpecΓFunctor (R := A) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward (Spec.map g))
      (gammaPushforwardIsoRestrictScalars A B f).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f))
      (moduleSpecΓFunctor (R := A))

private noncomputable def directGammaCompIso :
    Scheme.Modules.pushforward (Spec.map g ≫ Spec.map f) ⋙
        moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := C) ⋙
        ModuleCat.restrictScalars (f ≫ g).hom :=
  Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardCongr
        (show Spec.map g ≫ Spec.map f = Spec.map (f ≫ g) from
          (@Spec.map_comp A B C f g).symm))
      (moduleSpecΓFunctor (R := A)) ≪≫
    gammaPushforwardIsoRestrictScalars A C (f ≫ g)

private theorem gammaRightAssociativity :
    Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := C))
          (ModuleCat.restrictScalarsComp f.hom g.hom).symm ≪≫
        (directGammaCompIso A B C f g).symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (gammaPushforwardIsoRestrictScalars B C g).symm
          (ModuleCat.restrictScalars f.hom) ≪≫
        pushGammaRestrictCompIso A B C f g := by
  apply Iso.ext
  ext M x
  rfl

end RightAdjointCoherence

section LeftAdjointCoherence

variable (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C)

private noncomputable def tildeCompositePullbackAdjunction :
    tilde.functor A ⋙
        Scheme.Modules.pullback (Spec.map g ≫ Spec.map f) ⊣
      Scheme.Modules.pushforward (Spec.map g ≫ Spec.map f) ⋙
        moduleSpecΓFunctor (R := A) :=
  (tilde.adjunction (R := A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map g ≫ Spec.map f))

private noncomputable def outerTailIso :
    ModuleCat.extendScalars f.hom ⋙
        (tilde.functor B ⋙ Scheme.Modules.pullback (Spec.map g)) ≅
      tilde.functor A ⋙
        Scheme.Modules.pullback (Spec.map g ≫ Spec.map f) :=
  (ModuleCat.extendRestrictScalarsAdj f.hom).leftAdjointCompIso
    (tildePullbackAdjunction B C g)
    (tildeCompositePullbackAdjunction A B C f g)
    (pushGammaRestrictCompIso A B C f g)

private noncomputable def outerDirectIso :
    ModuleCat.extendScalars (f ≫ g).hom ⋙ tilde.functor C ≅
      tilde.functor A ⋙
        Scheme.Modules.pullback (Spec.map g ≫ Spec.map f) :=
  (ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).leftAdjointCompIso
    (tilde.adjunction (R := C))
    (tildeCompositePullbackAdjunction A B C f g)
    (directGammaCompIso A B C f g).symm

private theorem outer_leftAdjointAssociativity :
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom)
          (extendScalarsTildeIsoPullback B C g) ≪≫
        outerTailIso A B C f g =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (ModuleCat.extendScalarsComp f.hom g.hom).symm
          (tilde.functor C) ≪≫
        outerDirectIso A B C f g := by
  exact Adjunction.leftAdjointCompIso_assoc
    (ModuleCat.extendRestrictScalarsAdj f.hom)
    (ModuleCat.extendRestrictScalarsAdj g.hom)
    (tilde.adjunction (R := C))
    (ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom)
    (tildePullbackAdjunction B C g)
    (tildeCompositePullbackAdjunction A B C f g)
    (ModuleCat.restrictScalarsComp f.hom g.hom).symm
    (gammaPushforwardIsoRestrictScalars B C g).symm
    (pushGammaRestrictCompIso A B C f g)
    (directGammaCompIso A B C f g).symm
    (gammaRightAssociativity A B C f g)

private theorem leftAdjointCompIso_refl
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) :
    adj₀₁.leftAdjointCompIso adj₁₂ (adj₀₁.comp adj₁₂)
        (Iso.refl _) = Iso.refl _ := by
  apply Iso.ext
  simp [Adjunction.leftAdjointCompIso_hom,
    Adjunction.leftAdjointCompNatTrans]

private noncomputable def pushforwardCompGammaIso :
    Scheme.Modules.pushforward (Spec.map g) ⋙
        (Scheme.Modules.pushforward (Spec.map f) ⋙
          moduleSpecΓFunctor (R := A)) ≅
      Scheme.Modules.pushforward (Spec.map g ≫ Spec.map f) ⋙
        moduleSpecΓFunctor (R := A) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f))
      (moduleSpecΓFunctor (R := A))

private theorem innerGammaRightAssociativity :
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward (Spec.map g))
          (gammaPushforwardIsoRestrictScalars A B f).symm ≪≫
        pushforwardCompGammaIso A B C f g =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Iso.refl (Scheme.Modules.pushforward (Spec.map g) ⋙
            moduleSpecΓFunctor (R := B)))
          (ModuleCat.restrictScalars f.hom) ≪≫
        pushGammaRestrictCompIso A B C f g := by
  apply Iso.ext
  ext M x
  rfl

private noncomputable def innerTerminalIso :
    (tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map f)) ⋙
        Scheme.Modules.pullback (Spec.map g) ≅
      tilde.functor A ⋙
        Scheme.Modules.pullback (Spec.map g ≫ Spec.map f) :=
  (tildePullbackAdjunction A B f).leftAdjointCompIso
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    (tildeCompositePullbackAdjunction A B C f g)
    (pushforwardCompGammaIso A B C f g)

private theorem inner_leftAdjointAssociativity :
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom)
          ((tilde.adjunction (R := B)).leftAdjointCompIso
            (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
            (tildePullbackAdjunction B C g) (Iso.refl _)) ≪≫
        outerTailIso A B C f g =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (extendScalarsTildeIsoPullback A B f)
          (Scheme.Modules.pullback (Spec.map g)) ≪≫
        innerTerminalIso A B C f g := by
  exact Adjunction.leftAdjointCompIso_assoc
    (ModuleCat.extendRestrictScalarsAdj f.hom)
    (tilde.adjunction (R := B))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    (tildePullbackAdjunction A B f)
    (tildePullbackAdjunction B C g)
    (tildeCompositePullbackAdjunction A B C f g)
    (gammaPushforwardIsoRestrictScalars A B f).symm
    (Iso.refl _)
    (pushGammaRestrictCompIso A B C f g)
    (pushforwardCompGammaIso A B C f g)
    (innerGammaRightAssociativity A B C f g)

private lemma conjugateEquiv_associator_inv
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {L₀₁ : C₀ ⥤ C₁} {R₁₀ : C₁ ⥤ C₀}
    {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁}
    {L₂₃ : C₂ ⥤ C₃} {R₃₂ : C₃ ⥤ C₂}
    (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃)
        (adj₀₁.comp (adj₁₂.comp adj₂₃))
        (Functor.associator L₀₁ L₁₂ L₂₃).inv =
      (Functor.associator R₃₂ R₂₁ R₁₀).inv := by
  apply (cancel_mono (Functor.associator R₃₂ R₂₁ R₁₀).hom).1
  rw [← CategoryTheory.conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃,
    CategoryTheory.conjugateEquiv_comp, Iso.hom_inv_id,
    CategoryTheory.conjugateEquiv_id,
    CategoryTheory.conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃,
    Iso.inv_hom_id]

private lemma conjugateEquiv_comp_two
    {C D : Type*} [Category C] [Category D]
    {L₀ L₁ L₂ : C ⥤ D} {R₀ R₁ R₂ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (s₀ : L₀ ⟶ L₁) (s₁ : L₁ ⟶ L₂) :
    conjugateEquiv a₂ a₀ (s₀ ≫ s₁) =
      conjugateEquiv a₂ a₁ s₁ ≫ conjugateEquiv a₁ a₀ s₀ := by
  exact (conjugateEquiv_comp a₂ a₁ a₀ s₁ s₀).symm

private theorem innerTerminalIso_eq : innerTerminalIso A B C f g =
    Functor.associator (tilde.functor A)
        (Scheme.Modules.pullback (Spec.map f))
        (Scheme.Modules.pullback (Spec.map g)) ≪≫
      Functor.isoWhiskerLeft (tilde.functor A)
        (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)) := by
  apply Iso.ext
  apply (Iso.inv_eq_inv _ _).mp
  apply (conjugateEquiv
    ((tildePullbackAdjunction A B f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
    (tildeCompositePullbackAdjunction A B C f g)).injective
  unfold innerTerminalIso
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv]
  rw [conjugateEquiv_comp_two
      (tildeCompositePullbackAdjunction A B C f g)
      ((tilde.adjunction (R := A)).comp
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))))
      ((tildePullbackAdjunction A B f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))]
  unfold tildePullbackAdjunction tildeCompositePullbackAdjunction
  rw [
    conjugateEquiv_associator_inv,
    CategoryTheory.conjugateEquiv_whiskerLeft,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  rfl

private theorem outerTailIso_eq : outerTailIso A B C f g =
    (Functor.associator (ModuleCat.extendScalars f.hom)
        (tilde.functor B) (Scheme.Modules.pullback (Spec.map g))).symm ≪≫
      Functor.isoWhiskerRight (extendScalarsTildeIsoPullback A B f)
        (Scheme.Modules.pullback (Spec.map g)) ≪≫
      Functor.associator (tilde.functor A)
        (Scheme.Modules.pullback (Spec.map f))
        (Scheme.Modules.pullback (Spec.map g)) ≪≫
      Functor.isoWhiskerLeft (tilde.functor A)
        (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)) := by
  have h := inner_leftAdjointAssociativity A B C f g
  unfold tildePullbackAdjunction at h
  rw [leftAdjointCompIso_refl, innerTerminalIso_eq] at h
  simpa using h

private theorem outerDirectIso_eq : outerDirectIso A B C f g =
    extendScalarsTildeIsoPullback A C (f ≫ g) ≪≫
      Functor.isoWhiskerLeft (tilde.functor A)
        (Scheme.Modules.pullbackCongr
          (show Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f from
            @Spec.map_comp A B C f g)) := by
  let sourceAdj := extendTildeAdjunction A C (f ≫ g)
  let directAdj := tildePullbackAdjunction A C (f ≫ g)
  let compositeAdj := tildeCompositePullbackAdjunction A B C f g
  apply Iso.ext
  apply (conjugateEquiv compositeAdj sourceAdj).injective
  have hOuter : conjugateEquiv compositeAdj sourceAdj
      (outerDirectIso A B C f g).hom =
        (directGammaCompIso A B C f g).hom := by
    unfold outerDirectIso Adjunction.leftAdjointCompIso
    rw [← conjugateIsoEquiv_apply_hom]
    exact congrArg Iso.hom <|
      (conjugateIsoEquiv compositeAdj sourceAdj).apply_symm_apply _
  rw [hOuter]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  rw [conjugateEquiv_comp_two sourceAdj directAdj compositeAdj]
  dsimp only [compositeAdj, directAdj, sourceAdj]
  unfold tildeCompositePullbackAdjunction tildePullbackAdjunction
  rw [CategoryTheory.conjugateEquiv_whiskerLeft,
    conjugateEquiv_pullbackCongr_hom]
  have hE := conjugateEquiv_extendScalarsTildeIsoPullback_hom A C (f ≫ g)
  unfold tildePullbackAdjunction at hE
  rw [hE]
  unfold directGammaCompIso
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom]
  rw [pushforwardCongr_symm_hom]

private noncomputable def extendScalarsTildeIsoPullbackCompPath
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    ModuleCat.extendScalars (f ≫ g).hom ⋙ tilde.functor C ≅
      tilde.functor A ⋙
        Scheme.Modules.pullback (Spec.map g ≫ Spec.map f) :=
  Functor.isoWhiskerRight (ModuleCat.extendScalarsComp f.hom g.hom)
      (tilde.functor C) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom)
      (extendScalarsTildeIsoPullback B C g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extendScalarsTildeIsoPullback A B f)
      (Scheme.Modules.pullback (Spec.map g)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tilde.functor A)
      (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f))

private theorem extendScalarsTildeIsoPullback_comp
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    extendScalarsTildeIsoPullbackCompPath A B C f g =
      extendScalarsTildeIsoPullback A C (f ≫ g) ≪≫
        Functor.isoWhiskerLeft (tilde.functor A)
          (Scheme.Modules.pullbackCongr
            (show Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f from
              @Spec.map_comp A B C f g)) := by
  unfold extendScalarsTildeIsoPullbackCompPath
  rw [← outerTailIso_eq A B C f g]
  rw [outer_leftAdjointAssociativity A B C f g]
  rw [outerDirectIso_eq A B C f g]
  rw [← Functor.isoWhiskerRight_symm]
  simp

end LeftAdjointCoherence

end A3CoherenceReproducer
