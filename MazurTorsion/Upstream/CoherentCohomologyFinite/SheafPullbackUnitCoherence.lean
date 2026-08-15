/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafScalar

/-!
# Coherence for pulling back the structure sheaf

The canonical comparison `f⁎𝒪 ≅ 𝒪` is compatible with composition of
scheme morphisms.  Keeping this proof in its own file prevents the
pseudofunctor bookkeeping from being unfolded in the geometric files that
consume it.
-/

open CategoryTheory

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

open _root_.AlgebraicGeometry

local instance coherencePresheafPushforwardIsRightAdjoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (PresheafOfModules.pushforward.{u}
      f.toRingCatSheafHom.hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward.{u} _

local instance coherenceSheafPushforwardIsRightAdjoint
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (SheafOfModules.pushforward.{u}
      f.toRingCatSheafHom).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    f.toRingCatSheafHom).isRightAdjoint

private lemma homEquiv_conjugate_app
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {c : C} {d : D}
    (f : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ f) =
      adj₁.homEquiv c d f ≫
        (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d := by
  have hunit :=
    CategoryTheory.unit_conjugateEquiv adj₁ adj₂ α c
  have h₁ :
      adj₂.homEquiv c d (α.app c ≫ f) =
        (adj₂.unit.app c ≫ R₂.map (α.app c)) ≫ R₂.map f :=
    (Adjunction.homEquiv_unit adj₂ c d (α.app c ≫ f)).trans <|
      (CategoryTheory.whisker_eq (adj₂.unit.app c)
        (R₂.map_comp (α.app c) f)).trans
          (Category.assoc _ _ _).symm
  have h₂ :
      adj₁.homEquiv c d f ≫
          (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d =
        (adj₁.unit.app c ≫
          (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app
            (L₁.obj c)) ≫ R₂.map f :=
    (CategoryTheory.eq_whisker
      (Adjunction.homEquiv_unit adj₁ c d f)
      ((CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d)).trans <|
        (Category.assoc _ _ _).trans <|
          (CategoryTheory.whisker_eq (adj₁.unit.app c)
            ((CategoryTheory.conjugateEquiv adj₁ adj₂ α).naturality f)).trans
              (Category.assoc _ _ _).symm
  exact h₁.trans
    ((CategoryTheory.eq_whisker hunit.symm (R₂.map f)).trans h₂.symm)

private lemma pullbackCongr_hom_app_eqToHom
    {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (M : X.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M =
      eqToHom (congrArg
        (fun q => (Scheme.Modules.pullback q).obj M) h) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- The canonical unit comparison for a composite pullback factors through
the two individual unit comparisons. -/
lemma pullbackObjUnitToUnit_comp
    {X Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        SheafOfModules.pullbackObjUnitToUnit
          (g ≫ f).toRingCatSheafHom =
      (Scheme.Modules.pullback g).map
          (SheafOfModules.pullbackObjUnitToUnit
            f.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit
          g.toRingCatSheafHom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.pullbackPushforwardAdjunction g)).homEquiv _ _ |>.injective
  set adjF := Scheme.Modules.pullbackPushforwardAdjunction f
  set adjG := Scheme.Modules.pullbackPushforwardAdjunction g
  set adjGF := Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)
  have hleft := homEquiv_conjugate_app adjGF (adjF.comp adjG)
    (Scheme.Modules.pullbackComp g f).hom
    (f := SheafOfModules.pullbackObjUnitToUnit
      (g ≫ f).toRingCatSheafHom)
  have hGF :
      adjGF.homEquiv _ _
          (SheafOfModules.pullbackObjUnitToUnit
            (g ≫ f).toRingCatSheafHom) =
        SheafOfModules.unitToPushforwardObjUnit
          (g ≫ f).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hF :
      adjF.homEquiv _ _
          (SheafOfModules.pullbackObjUnitToUnit
            f.toRingCatSheafHom) =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hG :
      adjG.homEquiv _ _
          (SheafOfModules.pullbackObjUnitToUnit
            g.toRingCatSheafHom) =
        SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hcomm := CategoryTheory.conjugateEquiv_comm
    (adj₁ := adjF.comp adjG) (adj₂ := adjGF)
    (show
      (Scheme.Modules.pullbackComp g f).hom ≫
          (Scheme.Modules.pullbackComp g f).inv = 𝟙 _
      from (Scheme.Modules.pullbackComp g f).hom_inv_id)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hcomm
  have hconjugate :
      CategoryTheory.conjugateEquiv adjGF (adjF.comp adjG)
          (Scheme.Modules.pullbackComp g f).hom =
        (Scheme.Modules.pushforwardComp g f).inv :=
    (CategoryTheory.Iso.hom_comp_eq_id _).mp hcomm
  have hright :
      (adjF.comp adjG).homEquiv _ _
          ((Scheme.Modules.pullback g).map
              (SheafOfModules.pullbackObjUnitToUnit
                f.toRingCatSheafHom) ≫
            SheafOfModules.pullbackObjUnitToUnit
              g.toRingCatSheafHom) =
        SheafOfModules.unitToPushforwardObjUnit
            f.toRingCatSheafHom ≫
          (Scheme.Modules.pushforward f).map
            (SheafOfModules.unitToPushforwardObjUnit
              g.toRingCatSheafHom) := by
    rw [Adjunction.comp_homEquiv]
    change adjF.homEquiv _ _
      (adjG.homEquiv _ _ (_ ≫ _)) = _
    let u := SheafOfModules.pullbackObjUnitToUnit
      f.toRingCatSheafHom
    let v := SheafOfModules.pullbackObjUnitToUnit
      g.toRingCatSheafHom
    have hGnat := adjG.homEquiv_naturality_left u v
    have hFnat := adjF.homEquiv_naturality_right u
      (adjG.homEquiv _ _ v)
    have hmapG := congrArg (Scheme.Modules.pushforward f).map hG
    exact (congrArg (adjF.homEquiv _ _) hGnat).trans
      (hFnat.trans (congrArg₂ (fun a b => a ≫ b) hF hmapG))
  have hsections :
      SheafOfModules.unitToPushforwardObjUnit
            (g ≫ f).toRingCatSheafHom ≫
          (Scheme.Modules.pushforwardComp g f).inv.app
            (SheafOfModules.unit Z.ringCatSheaf) =
        SheafOfModules.unitToPushforwardObjUnit
            f.toRingCatSheafHom ≫
          (Scheme.Modules.pushforward f).map
            (SheafOfModules.unitToPushforwardObjUnit
              g.toRingCatSheafHom) := by
    rfl
  have h₁ := hleft.trans (congrArg
    (· ≫
      (CategoryTheory.conjugateEquiv adjGF (adjF.comp adjG)
        (Scheme.Modules.pullbackComp g f).hom).app
          (SheafOfModules.unit Z.ringCatSheaf)) hGF)
  have h₂ := congrArg
    (SheafOfModules.unitToPushforwardObjUnit
        (g ≫ f).toRingCatSheafHom ≫
      NatTrans.app · (SheafOfModules.unit Z.ringCatSheaf))
    hconjugate
  exact h₁.trans (h₂.trans (hsections.trans hright.symm))

/-- Iso-level form of `pullbackObjUnitToUnit_comp`. -/
lemma pullbackUnitIso_comp
    {X Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (Scheme.Modules.pullbackComp g f).hom.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (pullbackUnitIso (g ≫ f)).hom =
      (Scheme.Modules.pullback g).map
          (pullbackUnitIso f).hom ≫
        (pullbackUnitIso g).hom :=
  pullbackObjUnitToUnit_comp f g

/-- Unit comparisons along equal base morphisms cancel at the isomorphism
level, leaving precisely the equality transport of their sources. -/
lemma pullbackUnitIso_trans_symm_eqToIso
    {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    pullbackUnitIso f ≪≫ (pullbackUnitIso g).symm =
      eqToIso (congrArg
        (fun q => (Scheme.Modules.pullback q).obj
          (SheafOfModules.unit X.ringCatSheaf)) h) := by
  subst h
  apply Iso.ext
  change (pullbackUnitIso f).hom ≫ (pullbackUnitIso f).inv = 𝟙 _
  exact (pullbackUnitIso f).hom_inv_id

/-- Equal base morphisms cancel between the inverse and direct unit
comparisons. -/
@[reassoc]
lemma pullbackUnitIso_inv_congr_hom
    {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    (pullbackUnitIso f).inv ≫
        ((Scheme.Modules.pullbackCongr h).app
          (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        (pullbackUnitIso g).hom =
      𝟙 _ := by
  subst h
  change (pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackUnitIso f).hom = 𝟙 _
  have hc := pullbackCongr_hom_app_eqToHom
    (rfl : f = f) (SheafOfModules.unit X.ringCatSheaf)
  rw [hc, eqToHom_refl]
  exact (CategoryTheory.whisker_eq
    (pullbackUnitIso f).inv
    (Category.id_comp (pullbackUnitIso f).hom)).trans
      (pullbackUnitIso f).inv_hom_id

/-- Absorb equality transport on the left of a unit comparison. -/
@[reassoc]
lemma pullbackCongr_hom_unit
    {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    ((Scheme.Modules.pullbackCongr h).app
        (SheafOfModules.unit X.ringCatSheaf)).hom ≫
      (pullbackUnitIso g).hom =
    (pullbackUnitIso f).hom := by
  subst h
  change
    (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (pullbackUnitIso f).hom = (pullbackUnitIso f).hom
  have hc := pullbackCongr_hom_app_eqToHom
    (rfl : f = f) (SheafOfModules.unit X.ringCatSheaf)
  rw [hc, eqToHom_refl]
  exact Category.id_comp (pullbackUnitIso f).hom

/-- Absorb equality transport on the right of an inverse unit comparison. -/
@[reassoc]
lemma pullbackUnitIso_inv_congr
    {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g) :
    (pullbackUnitIso f).inv ≫
        ((Scheme.Modules.pullbackCongr h).app
          (SheafOfModules.unit X.ringCatSheaf)).hom =
      (pullbackUnitIso g).inv := by
  subst h
  change (pullbackUnitIso f).inv ≫
      (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app
        (SheafOfModules.unit X.ringCatSheaf) =
      (pullbackUnitIso f).inv
  have hc := pullbackCongr_hom_app_eqToHom
    (rfl : f = f) (SheafOfModules.unit X.ringCatSheaf)
  rw [hc, eqToHom_refl]
  exact Category.comp_id (pullbackUnitIso f).inv

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar
