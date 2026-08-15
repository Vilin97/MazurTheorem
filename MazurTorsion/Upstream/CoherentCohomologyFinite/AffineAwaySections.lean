/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteGenerators
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineSectionLocalization

/-!
# Sections after restriction to an away localization

Restriction along `Spec R_g ⟶ Spec R` identifies top sections with sections
on `D(g)`.  This file records that identification linearly over `R` and
packages the resulting localization map.
-/

open CategoryTheory

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- The canonical base-ring action on sections of a module on an affine
scheme, named locally so elaboration does not have to unfold `Γ`. -/
@[instance_reducible]
private noncomputable def affineSectionModule
    (F : (Spec R).Modules) (U : (Spec R).Opens) :
    Module R Γ(F, U) :=
  inferInstanceAs
    (Module R
      ((modulesSpecToSheaf.obj F).presheaf.obj (Opposite.op U)))

attribute [local instance] affineSectionModule

/-- The natural `R_g`-module structure on top sections after restriction to
`Spec R_g`.  Naming this instance keeps downstream statements from having to
unfold the restricted sheaf merely to find its scalar action. -/
instance (priority := 900) restrictAwaySectionsLocalizedModule
    (F : (Spec R).Modules) (g : R) :
    Module (CommRingCat.of (Localization.Away g))
      Γ(F.restrict
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (Localization.Away g)))),
        ⊤) :=
  inferInstanceAs
    (Module (CommRingCat.of (Localization.Away g))
      ((modulesSpecToSheaf.obj
        (F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away g)))))).presheaf.obj
        (Opposite.op ⊤)))

/-- The `R`-module structure on sections after restriction to `Spec R_g`,
obtained by restricting scalars from `R_g`. -/
instance (priority := 900) restrictAwaySectionsModule
    (F : (Spec R).Modules) (g : R) :
    Module R
      Γ(F.restrict
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (Localization.Away g)))),
        ⊤) :=
  let Faway :
      (Spec (CommRingCat.of
        (Localization.Away g))).Modules :=
    F.restrict
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (Localization.Away g))))
  letI :
      Module (CommRingCat.of (Localization.Away g))
        Γ(Faway, ⊤) :=
    inferInstanceAs
      (Module (CommRingCat.of (Localization.Away g))
        ((modulesSpecToSheaf.obj Faway).presheaf.obj
          (Opposite.op ⊤)))
  Module.compHom _ (algebraMap R (Localization.Away g))

/-- Top sections after direct restriction to `Spec R_g` are linearly
equivalent over `R` to sections on `D(g)`. -/
def restrictAwaySectionsLinearEquiv
    (F : (Spec R).Modules) (g : R) :
    letI : Module R
        Γ(F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away g)))),
          ⊤) :=
      restrictAwaySectionsModule F g
    Γ(F.restrict
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (Localization.Away g)))),
        ⊤) ≃ₗ[R]
      ((modulesSpecToSheaf.obj F).presheaf.obj
        (Opposite.op (PrimeSpectrum.basicOpen g))) := by
  let a : R ⟶ CommRingCat.of (Localization.Away g) :=
    CommRingCat.ofHom (algebraMap R _)
  let ψ : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec R :=
    Spec.map a
  let Faway :
      (Spec (CommRingCat.of
        (Localization.Away g))).Modules :=
    F.restrict ψ
  letI :
      Module (CommRingCat.of (Localization.Away g))
        Γ(Faway, ⊤) :=
    inferInstanceAs
      (Module (CommRingCat.of (Localization.Away g))
        ((modulesSpecToSheaf.obj Faway).presheaf.obj
          (Opposite.op ⊤)))
  have hRange :
      ψ.opensRange = PrimeSpectrum.basicOpen g := by
    dsimp [ψ, a]
    apply TopologicalSpace.Opens.ext
    exact
      PrimeSpectrum.localization_away_comap_range
        (Localization.Away g) g
  have hImageTop :
      ψ ''ᵁ (⊤ : (Spec (CommRingCat.of
        (Localization.Away g))).Opens) =
        PrimeSpectrum.basicOpen g :=
    ψ.image_top_eq_opensRange.trans hRange
  let e :
      Γ(F.restrict ψ, ⊤) ≅
        Γ(F, PrimeSpectrum.basicOpen g) :=
    F.restrictAppIso ψ ⊤ ≪≫
      F.presheaf.mapIso (eqToIso hImageTop.symm).op
  letI : Module R Γ(F, PrimeSpectrum.basicOpen g) :=
    affineSectionModule F (PrimeSpectrum.basicOpen g)
  exact
    { toFun := e.hom
      invFun := e.inv
      left_inv := e.hom_inv_id_apply
      right_inv := e.inv_hom_id_apply
      map_add' := e.hom.hom.map_add
      map_smul' := by
        intro r x
        let q :
            Opposite.op (ψ ''ᵁ
              (⊤ : (Spec (CommRingCat.of
                (Localization.Away g))).Opens)) ⟶
              Opposite.op (PrimeSpectrum.basicOpen g) :=
          (eqToIso hImageTop.symm).op.hom
        let y := (F.restrictAppIso ψ ⊤).hom x
        have hy :
            (F.restrictAppIso ψ ⊤).hom (r • x) =
              r • y := by
          change
            (F.restrictAppIso ψ ⊤).hom
                (a r • x) =
              r • (F.restrictAppIso ψ ⊤).hom x
          exact restrictAppIso_smul_Spec a r x
        calc
          e.hom (r • x) =
              (F.presheaf.map q).hom
                ((F.restrictAppIso ψ ⊤).hom (r • x)) := rfl
          _ = (F.presheaf.map q).hom (r • y) :=
            congrArg (F.presheaf.map q) hy
          _ = r • (F.presheaf.map q).hom y :=
            ((modulesSpecToSheaf.obj F).presheaf.map q).hom.map_smul r y
          _ = r • e.hom x := rfl }

/-- Restriction of top sections to the away-restricted sheaf. -/
def restrictAwaySectionsLinearMap
    (F : (Spec R).Modules) (g : R) :
    letI : Module R
        Γ(F.restrict
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap R (Localization.Away g)))),
          ⊤) :=
      restrictAwaySectionsModule F g
    Γ(F, ⊤) →ₗ[R]
      Γ(F.restrict
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (Localization.Away g)))),
        ⊤) :=
  (restrictAwaySectionsLinearEquiv F g).symm.toLinearMap.comp
    ((modulesSpecToSheaf.obj F).presheaf.map
      (homOfLE
        (le_top : PrimeSpectrum.basicOpen g ≤
          (⊤ : (Spec R).Opens))).op).hom

/-- Restriction to `Spec R_g` realizes its top sections as the localization
of the original top-section module at `g`. -/
theorem restrictAwaySections_isLocalizedModule
    (F : (Spec R).Modules) [IsIso F.fromTildeΓ] (g : R) :
    IsLocalizedModule (Submonoid.powers g)
      (restrictAwaySectionsLinearMap F g) := by
  let φ : Γ(F, ⊤) →ₗ[R]
      ((modulesSpecToSheaf.obj F).presheaf.obj
        (Opposite.op (PrimeSpectrum.basicOpen g))) :=
    ((modulesSpecToSheaf.obj F).presheaf.map
      (homOfLE
        (le_top : PrimeSpectrum.basicOpen g ≤
          (⊤ : (Spec R).Opens))).op).hom
  haveI : IsLocalizedModule (Submonoid.powers g) φ :=
    section_isLocalizedModule_of_isIso_fromTildeΓ F g
  exact IsLocalizedModule.of_linearEquiv
    (Submonoid.powers g)
    φ
    (restrictAwaySectionsLinearEquiv F g).symm

end AlgebraicGeometry.Scheme.Modules
