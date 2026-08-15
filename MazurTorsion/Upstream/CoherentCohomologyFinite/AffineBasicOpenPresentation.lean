/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineBasicOpenRestriction

/-!
# Presentations on affine basic opens

An over-site presentation near `D(g)` is transported first to the open
subscheme and then across `D(g) ≅ Spec R_g`.  Colimit preservation is
provided directly by the restriction adjunction, avoiding expensive
instance search.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

local instance restrictBasicOpenPresheafPushforwardIsRightAdjoint (g : R) :
    (PresheafOfModules.pushforward.{u}
      ((basicOpenIsoSpecAway g).inv).toRingCatSheafHom.hom).IsRightAdjoint :=
  PresheafOfModules.instIsRightAdjointPushforward.{u} _

local instance restrictBasicOpenPushforwardIsRightAdjoint (g : R) :
    (SheafOfModules.pushforward.{u}
      ((basicOpenIsoSpecAway g).inv).toRingCatSheafHom).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    ((basicOpenIsoSpecAway g).inv).toRingCatSheafHom).isRightAdjoint

/-- The unit comparison for restriction across the affine identification
`D(g) ≅ Spec R_g` is an isomorphism. -/
instance pullbackObjUnitToUnitIsIsoBasicOpen (g : R) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u}
      ((basicOpenIsoSpecAway g).inv).toRingCatSheafHom) := by
  haveI : IsIso (((basicOpenIsoSpecAway g).inv).base) :=
    inferInstance
  haveI :
      (TopologicalSpace.Opens.map
        ((basicOpenIsoSpecAway g).inv).base).Final := by
    haveI :
        (TopologicalSpace.Opens.map
          ((basicOpenIsoSpecAway g).inv).base).IsEquivalence :=
      (TopologicalSpace.Opens.mapMapIso
        (asIso ((basicOpenIsoSpecAway g).inv).base)).isEquivalence_functor
    infer_instance
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      ((basicOpenIsoSpecAway g).inv).toRingCatSheafHom).homEquiv _ _).bijective.of_comp_iff',
    ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert!
    (SheafOfModules.bijective_pushforwardSections
      ((basicOpenIsoSpecAway g).inv).toRingCatSheafHom M).comp
      (SheafOfModules.unitHomEquiv _).bijective
  ext f : 1
  dsimp
  erw [SheafOfModules.pushforwardSections_unitHomEquiv,
    EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

/-- Restriction across `D(g) ≅ Spec R_g` sends the structure sheaf to
the structure sheaf. -/
noncomputable def restrictBasicOpenUnitIso (g : R) :
    (Scheme.Modules.restrictFunctor.{u}
      (basicOpenIsoSpecAway g).inv).obj
        (SheafOfModules.unit
          (specBasicOpen g).toScheme.ringCatSheaf) ≅
      SheafOfModules.unit
        (Spec (CommRingCat.of
          (Localization.Away g))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback
    (basicOpenIsoSpecAway g).inv).app _ ≪≫
      @asIso _ _ _ _ _
        (pullbackObjUnitToUnitIsIsoBasicOpen g)

/-- Restriction across the affine identification preserves colimits.
This witness is obtained directly from the explicit adjunction. -/
theorem restrictBasicOpenPreservesColimits (g : R) :
    Limits.PreservesColimitsOfSize.{u, u}
      (Scheme.Modules.restrictFunctor.{u}
        (basicOpenIsoSpecAway g).inv) :=
  (Scheme.Modules.restrictAdjunction
    (basicOpenIsoSpecAway g).inv).leftAdjoint_preservesColimits

open SheafOfModules in
/-- A presentation over a neighborhood of `D(g)` induces a global
presentation after identifying `D(g)` with `Spec R_g`. -/
noncomputable def presentationModulesRestrictBasicOpen
    (M : (Spec R).Modules) (U : (Spec R).Opens)
    (P : (M.over U).Presentation) (g : R)
    (hg : specBasicOpen g ≤ U) :
    (modulesRestrictBasicOpen g M).Presentation := by
  let P₂ : (M.over (specBasicOpen g)).Presentation :=
    presentationOverBasicOpen M U P g hg
  let hE : Limits.PreservesColimitsOfSize.{u, u}
      (modulesOverBasicOpenEquivalence g).inverse :=
    (modulesOverBasicOpenEquivalence g).symm.toAdjunction.leftAdjoint_preservesColimits
  let P₃ :
      ((modulesOverBasicOpenEquivalence g).inverse.obj
        (M.over (specBasicOpen g))).Presentation :=
    @SheafOfModules.Presentation.map
      _ _ _ _ _ _ _ _ _ _ _ _ _ P₂
      (modulesOverBasicOpenEquivalence g).inverse hE (.refl _)
  let P₄ : (M.restrict (specBasicOpen g).ι).Presentation :=
    @Presentation.ofIsIso.{u, u, u}
      _ _ _ _ _ _ _ _ (overBasicOpenIsoRestrict g M).hom
      (overBasicOpenIsoRestrict g M).isIso_hom P₃
  exact @SheafOfModules.Presentation.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ P₄
    (Scheme.Modules.restrictFunctor.{u}
      (basicOpenIsoSpecAway g).inv)
    (restrictBasicOpenPreservesColimits g)
    (restrictBasicOpenUnitIso g).symm

end AlgebraicGeometry
