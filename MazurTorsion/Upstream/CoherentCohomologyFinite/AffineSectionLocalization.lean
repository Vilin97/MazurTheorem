/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib

/-!
# Localization of sections for globally presented affine sheaves

The associated sheaf of a module has the expected localization formula on
distinguished opens.  The formula transports across the affine tilde
counit, and hence applies to every sheaf admitting a global presentation.
-/

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/--
Restriction of sections of `tilde M` from `Spec R` to `D(f)` is
localization at `f`.
-/
theorem tilde_section_isLocalizedModule
    (M : ModuleCat.{u} R) (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE
          (le_top : PrimeSpectrum.basicOpen f ≤
            (⊤ : (Spec R).Opens))).op).hom := by
  have hres := tilde.toOpen_res M ⊤
    (PrimeSpectrum.basicOpen f) (homOfLE le_top)
  let eTop : M ≃ₗ[R] _ :=
    (asIso (tilde.toOpen M ⊤)).toLinearEquiv
  have hmap :
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE
          (le_top : PrimeSpectrum.basicOpen f ≤
            (⊤ : (Spec R).Opens))).op).hom =
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom ∘ₗ
          eTop.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    have hx := congrArg
      (fun (m : M ⟶ _) => m.hom (eTop.symm x)) hres
    simp only [ModuleCat.hom_comp] at hx
    have htop :
        (tilde.toOpen M ⊤).hom (eTop.symm x) = x := by
      exact eTop.apply_symm_apply x
    conv_lhs => rw [← htop]
    exact hx
  rw [hmap]
  exact IsLocalizedModule.of_linearEquiv_right
    (Submonoid.powers f)
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom eTop.symm

/--
If the tilde--global-sections counit of `F` is an isomorphism, restriction
of its sections to `D(f)` is localization at `f`.
-/
theorem section_isLocalizedModule_of_isIso_fromTildeΓ
    (F : (Spec R).Modules) [IsIso F.fromTildeΓ] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE
          (le_top : PrimeSpectrum.basicOpen f ≤
            (⊤ : (Spec R).Opens))).op).hom := by
  let M := moduleSpecΓFunctor.obj F
  let α : F ≅ tilde M := (asIso F.fromTildeΓ).symm
  let β :=
    (TopCat.Sheaf.forget (ModuleCat R) (Spec R)).map
      (modulesSpecToSheaf.map α.hom)
  haveI : IsIso (modulesSpecToSheaf.map α.hom) := inferInstance
  haveI : IsIso β := inferInstance
  haveI : IsIso (β.app (op (⊤ : (Spec R).Opens))) :=
    CategoryTheory.NatIso.isIso_app_of_isIso β _
  haveI : IsIso
      (β.app (op (PrimeSpectrum.basicOpen f))) :=
    CategoryTheory.NatIso.isIso_app_of_isIso β _
  let eTop : _ ≃ₗ[R] _ :=
    (asIso (β.app
      (op (⊤ : (Spec R).Opens)))).toLinearEquiv
  let eDf : _ ≃ₗ[R] _ :=
    (asIso (β.app
      (op (PrimeSpectrum.basicOpen f)))).toLinearEquiv
  haveI htilde := tilde_section_isLocalizedModule M f
  let φ : _ →ₗ[R] _ :=
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
      (homOfLE
        (le_top : PrimeSpectrum.basicOpen f ≤
          (⊤ : (Spec R).Opens))).op).hom ∘ₗ
      eTop.toLinearMap
  haveI hφ : IsLocalizedModule (Submonoid.powers f) φ := by
    dsimp only [φ]
    exact IsLocalizedModule.of_linearEquiv_right
      (Submonoid.powers f)
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
        (homOfLE
          (le_top : PrimeSpectrum.basicOpen f ≤
            (⊤ : (Spec R).Opens))).op).hom eTop
  have hnat := β.naturality
    (homOfLE
      (le_top : PrimeSpectrum.basicOpen f ≤
        (⊤ : (Spec R).Opens))).op
  have hnat' : ∀ x,
      eDf (((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE
          (le_top : PrimeSpectrum.basicOpen f ≤
            (⊤ : (Spec R).Opens))).op).hom x) = φ x := by
    intro x
    have hx :=
      LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom hnat) x
    simp only [ModuleCat.hom_comp] at hx
    exact hx
  have hF :
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE
          (le_top : PrimeSpectrum.basicOpen f ≤
            (⊤ : (Spec R).Opens))).op).hom =
        eDf.symm.toLinearMap ∘ₗ φ := by
    apply LinearMap.ext
    intro x
    change _ = eDf.symm (φ x)
    rw [← hnat' x]
    exact (eDf.symm_apply_apply _).symm
  rw [hF]
  exact IsLocalizedModule.of_linearEquiv
    (Submonoid.powers f) φ eDf.symm

/--
A globally presented module sheaf on `Spec R` has localized sections on
all distinguished opens.
-/
theorem section_isLocalizedModule_of_presentation
    (F : (Spec R).Modules) (P : F.Presentation) (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj F).presheaf.map
        (homOfLE
          (le_top : PrimeSpectrum.basicOpen f ≤
            (⊤ : (Spec R).Opens))).op).hom := by
  letI := isIso_fromTildeΓ_of_presentation F P
  exact section_isLocalizedModule_of_isIso_fromTildeΓ F f

end AlgebraicGeometry.Scheme.Modules
