/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Module.Torsion.Basic

import MazurTorsion.Upstream.AINTLIB.ForMathlib.AffineModuleBaseChange
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SurjectiveRestrictionScalars

/-!
# Pullback--pushforward units for affine ideal quotients

An ideal-annihilated module descends to the quotient ring. This identifies the
pullback--pushforward unit along the quotient-spectrum map as an isomorphism.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The morphism of affine spectra induced by an ideal quotient. -/
def idealQuotientSpecMap (I : Ideal R) :
    Spec (.of (R ⧸ I)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The quotient-ring module induced by annihilation by an ideal. -/
noncomputable def quotientModule (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    ModuleCat (R ⧸ I) :=
  letI := h.module
  ModuleCat.of (R ⧸ I) M

/-- Restricting the quotient-ring module recovers the original module. -/
noncomputable def quotientModuleRestrictionIso (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    ModuleCat.of R M ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (quotientModule I h) := by
  let f :
      ModuleCat.of R M ⟶
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (quotientModule I h) :=
    ModuleCat.ofHom
      (X := ModuleCat.of R M)
      (Y :=
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (quotientModule I h))
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun r m => (h.mk_smul r m).symm }
  let g :
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (quotientModule I h) ⟶
        ModuleCat.of R M :=
    ModuleCat.ofHom
      (X :=
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
          (quotientModule I h))
      (Y := ModuleCat.of R M)
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun r m => h.mk_smul r m }
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        ext x
        change id (id x) = x
        rfl
      inv_hom_id := by
        ext x
        change id (id x) = x
        rfl }

variable {R : CommRingCat.{u}}

/-- The pullback--pushforward unit on an ideal-annihilated tilde sheaf is invertible. -/
theorem isIso_pullbackPushforward_unit_tilde_idealQuotient
    (M : ModuleCat R) (I : Ideal R)
    (h : Module.IsTorsionBySet R M (I : Set R)) :
    IsIso
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (idealQuotientSpecMap I)).unit.app (tilde M)) := by
  let q : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  let φ : R ⟶ CommRingCat.of (R ⧸ I) := CommRingCat.ofHom q
  let N : ModuleCat (R ⧸ I) := quotientModule I h
  let e : M ≅ (ModuleCat.restrictScalars q).obj N :=
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
    Scheme.Modules.isIso_pullbackPushforward_unit_tilde_of_isIso_extendScalars_unit
      φ M

namespace Scheme.Modules

/-- The pullback--pushforward unit on an affine quasicoherent module annihilated by
an ideal is invertible along the quotient-spectrum map. -/
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
