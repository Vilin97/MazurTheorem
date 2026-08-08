/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineExact

/-!
# Finite affine-cover modules on an affine spectrum

This file constructs the finite product of restriction-pushforwards attached
to affine opens of `Spec R`.  It proves that this cover module, and the
cokernel of the adjunction-unit map into it, are quasicoherent.  The cokernel
result is a concrete downstream consumer of affine quasicoherent cokernel
closure from `SchemeModuleCohomologyAffineExact`.

These are structural inputs to the Kempf dimension-shifting proof of affine
acyclicity.  This file does not assert that the cover map is a monomorphism,
that a cohomology class is locally killed, or that positive cohomology
vanishes.

The construction was cross-checked against AINTLIB's
`ForMathlib/AffineVanishing.lean` and
`SchemeModuleQuasicoherent.lean` at commit
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`.  The implementation here is an
independent derivation against this repository's exact Mathlib pin.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- A finite product of quasicoherent modules on an affine spectrum is
quasicoherent. -/
theorem moduleSpec_isQuasicoherent_pi {R : CommRingCat.{u}}
    {I : Type u} [Finite I] (F : I → (Spec R).Modules)
    [∀ i, (F i).IsQuasicoherent] :
    (∏ᶜ F).IsQuasicoherent := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  letI : P.IsClosedUnderLimitsOfShape (Discrete I) := by
    change (SheafOfModules.isQuasicoherent
      (Spec R).ringCatSheaf).IsClosedUnderLimitsOfShape (Discrete I)
    rw [← AlgebraicGeometry.essImage_tilde]
    haveI : HasLimitsOfShape (Discrete I) (ModuleCat R) := inferInstance
    haveI : PreservesLimitsOfShape (Discrete I) (tilde.functor R) :=
      inferInstance
    exact
    instIsClosedUnderLimitsOfShapeEssImageOfHasLimitsOfShapeOfPreservesLimitsOfShapeOfFullOfFaithful
      (tilde.functor R)
  exact P.prop_limit (Discrete.functor F) (fun i ↦
    inferInstanceAs ((F i.as).IsQuasicoherent))

/-- Restriction along an isomorphism and its inverse cancel on scheme
modules. -/
noncomputable def restrictFunctor_inv_restrictFunctor_hom_id
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    Scheme.Modules.restrictFunctor e.inv ⋙
        Scheme.Modules.restrictFunctor e.hom ≅ Functor.id X.Modules :=
  (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
    Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId

/-- Quasicoherence is reflected as well as preserved by restriction along a
scheme isomorphism. -/
theorem isQuasicoherent_restrictFunctor_iso_iff
    {X Y : Scheme.{u}} (e : X ≅ Y) {M : Y.Modules} :
    (M.restrict e.hom).IsQuasicoherent ↔ M.IsQuasicoherent := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  apply (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((restrictFunctor_inv_restrictFunctor_hom_id e.symm).app M)
  simp only [Iso.symm_inv, Iso.symm_hom, Functor.comp_obj]
  infer_instance

/-- Pushforward along a scheme isomorphism preserves quasicoherence. -/
theorem isQuasicoherent_pushforward_iso
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f]
    {M : X.Modules} [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  apply (isQuasicoherent_restrictFunctor_iso_iff (asIso f)).mp
  apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorAdjCounitIso f).app M).symm
  change M.IsQuasicoherent
  infer_instance

/-- Pushforward along a morphism of affine spectra preserves
quasicoherence. -/
theorem isQuasicoherent_pushforward_specMap
    {S T : CommRingCat.{u}} (f : S ⟶ T) {M : (Spec T).Modules}
    [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map f)).obj M).IsQuasicoherent := by
  rw [AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ]
  exact AlgebraicGeometry.isIso_fromTildeΓ_pushforward f M

/-- Pushforward between affine schemes preserves quasicoherence. -/
theorem isQuasicoherent_pushforward_of_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) {M : X.Modules} [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  rw [show f = (X.isoSpec.hom ≫ Spec.map (Scheme.Hom.appTop f)) ≫
      Y.isoSpec.inv by simp [Scheme.isoSpec_hom_naturality f]]
  let e := (Scheme.Modules.pushforward X.isoSpec.hom).isoWhiskerLeft
      (Scheme.Modules.pushforwardComp (Spec.map (Scheme.Hom.appTop f))
        Y.isoSpec.inv) ≪≫
    Scheme.Modules.pushforwardComp X.isoSpec.hom
      (Spec.map (Scheme.Hom.appTop f) ≫ Y.isoSpec.inv)
  have hsource :
      ((Scheme.Modules.pushforward X.isoSpec.hom ⋙
        Scheme.Modules.pushforward (Spec.map (Scheme.Hom.appTop f)) ⋙
        Scheme.Modules.pushforward Y.isoSpec.inv).obj M).IsQuasicoherent := by
    simp only [Functor.comp_obj]
    let M₁ := (Scheme.Modules.pushforward X.isoSpec.hom).obj M
    haveI h₁ : M₁.IsQuasicoherent := isQuasicoherent_pushforward_iso
    let M₂ := (Scheme.Modules.pushforward
      (Spec.map (Scheme.Hom.appTop f))).obj M₁
    haveI h₂ : M₂.IsQuasicoherent :=
      isQuasicoherent_pushforward_specMap (Scheme.Hom.appTop f)
    exact isQuasicoherent_pushforward_iso
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (e.app M) hsource

/-- The finite-cover module formed from restriction-pushforwards. -/
noncomputable def affineCoverModule {R : CommRingCat.{u}} {I : Type u}
    (M : (Spec R).Modules) (U : I → (Spec R).Opens) :
    (Spec R).Modules :=
  ∏ᶜ fun i ↦
    (Scheme.Modules.restrictFunctor (U i).ι ⋙
      Scheme.Modules.pushforward (U i).ι).obj M

/-- The adjunction units map a module into its finite-cover module. -/
noncomputable def toAffineCoverModule {R : CommRingCat.{u}} {I : Type u}
    (M : (Spec R).Modules) (U : I → (Spec R).Opens) :
    M ⟶ affineCoverModule M U :=
  Pi.lift fun i ↦ (Scheme.Modules.restrictAdjunction (U i).ι).unit.app M

@[simp]
theorem toAffineCoverModule_comp_pi {R : CommRingCat.{u}} {I : Type u}
    (M : (Spec R).Modules) (U : I → (Spec R).Opens) (i : I) :
    toAffineCoverModule M U ≫
      Pi.π (fun i ↦
        (Scheme.Modules.restrictFunctor (U i).ι ⋙
          Scheme.Modules.pushforward (U i).ι).obj M) i =
      (Scheme.Modules.restrictAdjunction (U i).ι).unit.app M := by
  simp [toAffineCoverModule, affineCoverModule]

/-- A finite affine restriction-pushforward cover module on an affine
spectrum is quasicoherent. -/
theorem affineCoverModule_isQuasicoherent {R : CommRingCat.{u}}
    {I : Type u} [Finite I] (M : (Spec R).Modules)
    [M.IsQuasicoherent] (U : I → (Spec R).Opens)
    [∀ i, IsAffine (U i)] :
    (affineCoverModule M U).IsQuasicoherent := by
  letI (i : I) :
      ((Scheme.Modules.restrictFunctor (U i).ι).obj M).IsQuasicoherent :=
    inferInstance
  letI (i : I) :
      ((Scheme.Modules.restrictFunctor (U i).ι ⋙
        Scheme.Modules.pushforward (U i).ι).obj M).IsQuasicoherent := by
    change ((Scheme.Modules.pushforward (U i).ι).obj
      ((Scheme.Modules.restrictFunctor (U i).ι).obj M)).IsQuasicoherent
    exact isQuasicoherent_pushforward_of_affine (U i).ι
  exact moduleSpec_isQuasicoherent_pi _

/-- The ambient cokernel of the finite-cover map is quasicoherent.  This is
the finite-cover downstream consumer of affine cokernel closure. -/
theorem affineCoverCokernel_isQuasicoherent {R : CommRingCat.{u}}
    {I : Type u} [Finite I] (M : (Spec R).Modules)
    [M.IsQuasicoherent] (U : I → (Spec R).Opens)
    [∀ i, IsAffine (U i)] :
    (cokernel (toAffineCoverModule M U)).IsQuasicoherent := by
  letI : (affineCoverModule M U).IsQuasicoherent :=
    affineCoverModule_isQuasicoherent M U
  exact moduleSpec_isQuasicoherent_cokernel (toAffineCoverModule M U)

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
