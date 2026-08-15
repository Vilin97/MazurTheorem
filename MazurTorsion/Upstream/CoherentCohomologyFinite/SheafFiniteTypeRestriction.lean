/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafQuasicoherentRestriction

/-!
# Finite-type module sheaves and open restriction

Restriction to an open subscheme preserves local finite generation.  The
exact benchmark pin does not yet contain this functoriality result, so this
file proves it from local generating sections.
-/

open CategoryTheory TopologicalSpace

universe u

namespace SheafOfModules

open CategoryTheory.Functor CategoryTheory.Limits

section SameUniverseSites

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  [hSheafC : ∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [hSheafD : ∀ X : D, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [hWEC : ∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hWED : ∀ X : D, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (φ : S ⟶
    (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/--
Push local generating sections along a continuous, cocontinuous functor of
sites.  The indexing set of generators is unchanged on every member of the
induced cover.
-/
@[simps I X]
noncomputable def LocalGeneratorsData.pushforwardOnSameUniverseSites
    (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ X : C, (Over.post F).IsContinuous (J.over X) (K.over _)]
    (h : ∀ (X : C) (Y : D) (f : F.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
        pushforward.{u} (R := R.over Y)
          (F := Over.post (X := X) F ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u}
            (J.over X) J).map φ))
    {M : SheafOfModules.{u} R}
    (P : LocalGeneratorsData.{u, u, u, u} M) :
    LocalGeneratorsData.{u, u, u, u} ((pushforward φ).obj M) where
  I := Σ (X : C) (i : P.I), F.obj X ⟶ P.X i
  X i := i.1
  coversTop Y := by
    refine J.superset_covering ?_ <|
      F.cover_lift J _ (P.coversTop (F.obj Y))
    intro Z g ⟨i, ⟨v⟩⟩
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
  generators i := by
    letI overS : SheafOfModules.{u} S ⥤
        SheafOfModules.{u} (S.over i.1) :=
      pushforward (𝟙 _)
    letI F' := Over.post (X := i.1) F ⋙ Over.map i.2.2
    letI ψ : S.over i.1 ⟶
        (F'.sheafPushforwardContinuous RingCat.{u}
          (J.over i.1) (K.over (P.X i.2.1))).obj
          (R.over (P.X i.2.1)) :=
      ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u}
        (J.over i.1) J).map φ
    letI e : (pushforward ψ).obj
        (unit (R.over (P.X i.snd.fst))) ≅
        unit (S.over i.fst) :=
      overS.mapIso η
    haveI : PreservesColimitsOfSize.{u, u, _} (pushforward ψ) :=
      h _ _ _
    exact (P.generators i.2.1).map (pushforward ψ) e.symm

instance LocalGeneratorsData.pushforwardOnSameUniverseSites_isFiniteType
    (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ X : C, (Over.post F).IsContinuous (J.over X) (K.over _)]
    (h : ∀ (X : C) (Y : D) (f : F.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
        pushforward.{u} (R := R.over Y)
          (F := Over.post (X := X) F ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u}
            (J.over X) J).map φ))
    {M : SheafOfModules.{u} R}
    (P : LocalGeneratorsData.{u, u, u, u} M) [P.IsFiniteType] :
    (P.pushforwardOnSameUniverseSites φ η h).IsFiniteType where
  isFiniteType i := by
    letI : (J.over i.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
      hWEC i.1
    letI : (P.generators i.2.1).IsFiniteType :=
      LocalGeneratorsData.IsFiniteType.isFiniteType _
    dsimp [LocalGeneratorsData.pushforwardOnSameUniverseSites]
    exact @GeneratingSections.IsFiniteType.mk.{u, u, u}
      (C := Over i.1) (J := J.over i.1) (R := S.over i.1)
      (M := _) (σ := _)
      (finite := GeneratingSections.IsFiniteType.finite
        (σ := P.generators i.2.1))

/--
Finite type is preserved by the site pushforward when the underlying site
functor and the induced module pushforwards are left adjoints.
-/
lemma isFiniteType_pushforwardOnSameUniverseSites_of_isLeftAdjoint
    (η : (pushforward φ).obj (unit R) ≅ unit S)
    [F.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post (X := X) F).IsContinuous (J.over _) (K.over _)]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [IsFiniteType.{u, u, u} M] :
    IsFiniteType.{u, u, u} ((pushforward φ).obj M) := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  letI : P.IsFiniteType := hP
  let P' := P.pushforwardOnSameUniverseSites φ η (fun X Y f ↦ by
    let F' := Over.post (X := X) F ⋙ Over.map f
    have : F'.IsContinuous (J.over X) (K.over Y) :=
      Functor.isContinuous_comp _ _ _ (K.over _) _
    have : F'.IsCocontinuous (J.over X) (K.over Y) :=
      isCocontinuous_comp _ _ _ (K.over _)
    haveI : (Over.map f).IsLeftAdjoint :=
      (Over.mapPullbackAdj f).isLeftAdjoint
    let a : S.over X ⟶
        (F'.sheafPushforwardContinuous RingCat.{u}
          (J.over X) (K.over Y)).obj (R.over Y) :=
      ((Over.forget X).sheafPushforwardContinuous RingCat.{u}
        (J.over X) J).map φ
    haveI : IsIso a := by
      erw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
      rw [NatTrans.isIso_iff_isIso_app]
      intro Z
      change IsIso (φ.hom.app _)
      infer_instance
    have : (pushforward.{u} a).IsLeftAdjoint :=
      isLeftAdjoint_pushforward_of_isIso a
    infer_instance)
  refine ⟨?_⟩
  exact ⟨P', inferInstance⟩

end SameUniverseSites

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Restriction along an open immersion preserves finite type. -/
instance isFiniteType_restrictFunctor
    (M : Y.Modules) [SheafOfModules.IsFiniteType.{u, u, u} M] :
    SheafOfModules.IsFiniteType.{u, u, u} (M.restrict f) := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  haveI hα : IsIso α := NatIso.isIso_of_isIso_app _
  let φ : X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  letI hφ : IsIso φ := by
    erw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    change IsIso ((forget₂ CommRingCat RingCat).map (α.app U))
    infer_instance
  letI : f.opensFunctor.IsLeftAdjoint :=
    (f.isOpenEmbedding.isOpenMap.adjunction).isLeftAdjoint
  change SheafOfModules.IsFiniteType
    ((SheafOfModules.pushforward φ).obj M)
  exact
    @SheafOfModules.isFiniteType_pushforwardOnSameUniverseSites_of_isLeftAdjoint
      _ _ _ _ _ _ f.opensFunctor X.ringCatSheaf Y.ringCatSheaf
      _ _ _ _ _ _ φ (restrictUnitIso f) inferInstance hφ
      inferInstance inferInstance inferInstance M inferInstance

end AlgebraicGeometry.Scheme.Modules
