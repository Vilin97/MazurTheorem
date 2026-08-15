/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalkwise exactness of the affine tilde functor

For a commutative ring `R`, the map on stalks induced by
`M ⟶ N` under `M ↦ M̃` is the usual localization of that module map.
Consequently, an injective module map induces injective maps on every
stalk.

The public `ModuleCat R`-valued stalk comparison maps in Mathlib are
deliberately minimal.  We therefore package the underlying
abelian-group stalk map as an `R`-linear map and identify it using the
universal property of localization.  This follows the clean portion of
the Algebraic Jacobian Challenge's `TildeExactness` development.
-/


universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

local instance primeSpectrumTop_isPrime
    (x : PrimeSpectrum.Top R) : x.asIdeal.IsPrime :=
  x.isPrime

/-- Localization preserves injectivity of a module map. -/
theorem tildeToStalkMap_injective {M N : ModuleCat R}
    (f : M ⟶ N) (hf : Function.Injective f.hom)
    (x : PrimeSpectrum.Top R) :
    Function.Injective
      (IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk M x).hom (tilde.toStalk N x).hom f.hom) :=
  IsLocalizedModule.map_injective _ _ _ _ hf

/--
Naturality of the localization map from a module to the stalk of its
associated sheaf.
-/
theorem tildeStalkFunctorMap_toStalk {M N : ModuleCat R}
    (f : M ⟶ N) (x : PrimeSpectrum.Top R) (m : M) :
    (TopCat.Presheaf.stalkFunctor _ x).map
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map
          (tilde.map f))
        ((tilde.toStalk M x).hom m) =
      (tilde.toStalk N x).hom (f.hom m) := by
  change
    (TopCat.Presheaf.stalkFunctor _ x).map
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map
          (tilde.map f))
        (TopCat.Presheaf.germ
          (moduleStructurePresheaf R M).presheaf
          ⊤ x (by trivial)
          (StructureSheaf.toOpenₗ R M ⊤ m)) =
      TopCat.Presheaf.germ
        (moduleStructurePresheaf R N).presheaf
        ⊤ x (by trivial)
        (StructureSheaf.toOpenₗ R N ⊤ (f.hom m))
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply
    ⊤ x True.intro
    ((Scheme.Modules.toPresheaf (Spec (.of R))).map
      (tilde.map f))
    (StructureSheaf.toOpenₗ R M ⊤ m)]
  congr 1
  simp only [Scheme.Modules.toPresheaf_map]
  rw [StructureSheaf.toOpenₗ_eq_const,
    StructureSheaf.toOpenₗ_eq_const]
  simp only [tilde.map, SpecModulesToSheafFullyFaithful,
    tilde.modulesSpecToSheafIso]
  erw [StructureSheaf.comapₗ_const
    (hb := le_of_eq PrimeSpectrum.basicOpen_one.symm)]
  rfl

/--
Germs commute with scalar multiplication by a constant section.
-/
theorem tildeGerm_algebraMap_smul {M : ModuleCat R}
    (U : (Spec (.of R)).Opens)
    (x : PrimeSpectrum.Top R) (hxU : x ∈ U)
    (r : R) (s : Γ(tilde M, U)) :
    (ConcreteCategory.hom
      ((tilde M).presheaf.germ U x hxU))
        ((algebraMap R Γ(Spec (.of R), U) r) • s) =
      r •
        (ConcreteCategory.hom
          ((tilde M).presheaf.germ U x hxU)) s := by
  erw [PresheafOfModules.germ_smul,
    StructureSheaf.algebraMap_germ_apply]
  rfl

/--
The underlying abelian-group stalk map of `tilde.map f`, packaged as an
`R`-linear map.
-/
noncomputable def tildeStalkMapₗ {M N : ModuleCat R}
    (f : M ⟶ N) (x : PrimeSpectrum.Top R) :
    (tilde M).presheaf.stalk x →ₗ[R]
      (tilde N).presheaf.stalk x where
  toFun :=
    (TopCat.Presheaf.stalkFunctor _ x).map
      ((Scheme.Modules.toPresheaf (Spec (.of R))).map
        (tilde.map f))
  map_add' a b := map_add _ a b
  map_smul' r z := by
    dsimp only [RingHom.id_apply]
    obtain ⟨U, hxU, s, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq
        (tilde M).presheaf z
    rw [← tildeGerm_algebraMap_smul U x hxU r s]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply
        U x hxU
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map
          (tilde.map f)),
      TopCat.Presheaf.stalkFunctor_map_germ_apply
        U x hxU
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map
          (tilde.map f))]
    rw [Scheme.Modules.toPresheaf_map,
      Scheme.Modules.mapPresheaf_app]
    simp only [Opposite.unop_op]
    erw [Scheme.Modules.Hom.app_smul,
      tildeGerm_algebraMap_smul U x hxU r]
    rfl

/--
The stalk map of `tilde.map f` is the localization of `f`.
-/
theorem tildeStalkMapₗ_eq {M N : ModuleCat R}
    (f : M ⟶ N) (x : PrimeSpectrum.Top R) :
    tildeStalkMapₗ f x =
      IsLocalizedModule.map x.asIdeal.primeCompl
        (tilde.toStalk M x).hom
        (tilde.toStalk N x).hom f.hom := by
  apply IsLocalizedModule.ext x.asIdeal.primeCompl
    (tilde.toStalk M x).hom
    (fun s =>
      IsLocalizedModule.map_units
        (tilde.toStalk N x).hom s)
  ext m
  change
    tildeStalkMapₗ f x
        ((tilde.toStalk M x).hom m) = _
  rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
  exact tildeStalkFunctorMap_toStalk f x m

/--
An injective module map induces an injective map on every tilde stalk.
-/
theorem tildeStalkMapₗ_injective {M N : ModuleCat R}
    (f : M ⟶ N) (hf : Function.Injective f.hom)
    (x : PrimeSpectrum.Top R) :
    Function.Injective (tildeStalkMapₗ f x) := by
  rw [tildeStalkMapₗ_eq]
  exact tildeToStalkMap_injective f hf x

end AlgebraicGeometry
