/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffinePullbackPushforwardUnit
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuotientModulePushforward
import MazurTorsion.Upstream.CoherentCohomologyFinite.SurjectiveRestrictionScalars

/-!
# The pullback--pushforward unit for an affine quotient

If an ideal annihilates a module, the module is in the essential image
of restriction of scalars from the quotient ring.  The affine
pullback--tilde comparison therefore identifies the canonical
scheme-theoretic unit with an isomorphism.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/--
The canonical pullback--pushforward unit on the tilde of an annihilated
module is an isomorphism along the corresponding quotient-spectrum map.
-/
theorem isIso_pullbackPushforward_unit_tilde_idealQuotient
    (M : ModuleCat R) (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (idealQuotientSpecMap I)).unit.app (tilde M)) := by
  let q : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  let φ : R ⟶ CommRingCat.of (R ⧸ I) :=
    CommRingCat.ofHom q
  let N : ModuleCat (R ⧸ I) := quotientModule I h
  let e :
      M ≅ (ModuleCat.restrictScalars q).obj N :=
    quotientModuleRestrictionIso I h
  letI hFull : (ModuleCat.restrictScalars q).Full :=
    (ModuleCat.restrictScalarsFullyFaithfulOfSurjective
      q Ideal.Quotient.mk_surjective).full
  haveI hAlgebraUnit :
      IsIso ((ModuleCat.extendRestrictScalarsAdj q).unit.app M) :=
    (ModuleCat.extendRestrictScalarsAdj q).isIso_unit_app_of_iso e
  change
    IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (Spec.map φ)).unit.app (tilde M))
  exact
    isIso_pullbackPushforward_unit_tilde_of_isIso_extendScalars_unit
      φ M

namespace Scheme.Modules

/--
Affine quasicoherent form: if the global-sections module is annihilated
by an ideal, the canonical pullback--pushforward unit along the quotient
closed immersion is an isomorphism.
-/
theorem isIso_pullbackPushforward_unit_affine_idealQuotient
    (F : (Spec R).Modules) [F.IsQuasicoherent]
    (I : Ideal R)
    (h : Module.IsTorsionBySet R
      (moduleSpecΓFunctor.obj F) (I : Set R)) :
    IsIso
      ((pullbackPushforwardAdjunction
        (idealQuotientSpecMap I)).unit.app F) := by
  haveI hTildeUnit :
      IsIso
        ((pullbackPushforwardAdjunction
          (idealQuotientSpecMap I)).unit.app
            (tilde (moduleSpecΓFunctor.obj F))) :=
    isIso_pullbackPushforward_unit_tilde_idealQuotient
      (moduleSpecΓFunctor.obj F) I h
  haveI hReconstruction : IsIso F.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent F
  haveI hMappedReconstruction :
      IsIso
        ((pullback (idealQuotientSpecMap I) ⋙
          pushforward (idealQuotientSpecMap I)).map
            F.fromTildeΓ) :=
    inferInstance
  haveI hRight :
      IsIso
        ((pullbackPushforwardAdjunction
            (idealQuotientSpecMap I)).unit.app
              (tilde (moduleSpecΓFunctor.obj F)) ≫
          (pullback (idealQuotientSpecMap I) ⋙
            pushforward (idealQuotientSpecMap I)).map
              F.fromTildeΓ) :=
    IsIso.comp_isIso' hTildeUnit hMappedReconstruction
  exact
    @IsIso.of_isIso_fac_left _ _ _ _ _
      F.fromTildeΓ
      ((pullbackPushforwardAdjunction
        (idealQuotientSpecMap I)).unit.app F)
      (((pullbackPushforwardAdjunction
          (idealQuotientSpecMap I)).unit.app
            (tilde (moduleSpecΓFunctor.obj F))) ≫
        (pullback (idealQuotientSpecMap I) ⋙
          pushforward (idealQuotientSpecMap I)).map F.fromTildeΓ)
      hReconstruction hRight
      ((pullbackPushforwardAdjunction
        (idealQuotientSpecMap I)).unit.naturality F.fromTildeΓ)

end Scheme.Modules

end AlgebraicGeometry
