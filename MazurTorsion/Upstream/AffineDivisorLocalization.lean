/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.LinearAlgebra.Span.TensorProduct
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# Localization boundary for affine divisor line bundles

The affine divisor line bundle in `DivisorLineBundle` uses a chosen `CommRing.Pic`
representative. This file proves that representative is linearly equivalent to the explicit
inverse fractional ideal attached to the divisor. Thus the choice made by `PicardGroup.Shrink`
is not an obstruction to comparing restrictions.

For a principal open, equality of the localized explicit ideals is then carried through chosen
module representatives, module localization, tilde, and restriction to an actual sheaf
isomorphism. The stronger common-extension comparison is now proved on nonempty principal opens:
the actual chosen restriction is tilde of the inverse ideal extended inside the common fraction
field. In the same-chart case, abstract localized-ideal equality is converted to equality of
those common-field extensions and hence directly to an isomorphism of the chosen restrictions;
conversely, the two equalities are equivalent on a compatible nonempty principal open. Equality
of divisor coefficients on `D(f)` now proves both equalities, including abstract localization at
`f = 0`, and directly constructs the actual chosen restriction isomorphism.
For two coordinate rings mapping compatibly through a common affine overlap, equality of their
extended ideals is isolated separately and identifies the two extended ideal modules and their
tilde sheaves. The cross-chart extension equality is now proved outright for two principal
divisors cut out by the same rational function. For arbitrary divisors, an affine open immersion
is a flat ring epimorphism, so every overlap ideal is extended from its contraction. In particular,
each overlap height-one prime contracts to a height-one chart prime and extends back exactly. The
resulting count formula turns
contracted coefficient equality into equality of the two extended inverse ideals without a
classical localization presentation. General affine tilde base change is derived from the affine
adjunctions: open immersion makes the coordinate-ring map an algebra epimorphism, and flat
tensor/span comparison identifies restriction with the extended inverse ideal. Thus contracted
coefficient equality constructs the actual restricted-bundle isomorphism on every common
Dedekind affine overlap satisfying the standing torsion-free, common-fraction-field, and
scalar-tower hypotheses. The companion curve module proves that coefficient equality
automatically when the two overlap maps compose to one ambient map, and constructs all of that
data canonically from a chosen common Dedekind affine subopen. Passing from these local
isomorphisms to the chosen descent pullbacks, normalizing them, proving the triple cocycle, and
proving module effectivity remain open in the current Mathlib and Tau Ceti dependency graph.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization

open CategoryTheory
open _root_.AlgebraicGeometry
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors TensorProduct

universe u

namespace ExplicitIdeal

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The canonical invertible fractional ideal whose divisor is `D`. -/
noncomputable def divisorFractionalIdeal
    (D : WeilDivisor (HeightOneSpectrum R)) : (FractionalIdeal R⁰ K)ˣ :=
  Additive.toMul ((fractionalIdealDivisorAddEquiv R K).symm D)

/-- The inverse divisor ideal, transported to Mathlib's canonical fraction field and regarded
as an `R`-module. -/
noncomputable abbrev inverseIdeal
    (D : WeilDivisor (HeightOneSpectrum R)) : Submodule R (FractionRing R) :=
  FractionalIdeal.unitsMulEquivSubmodule
    (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)).toMonoidHom
      (divisorFractionalIdeal R K D)⁻¹)

private lemma equivPic_mk_fractionalIdeal (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.equivPic R (ClassGroup.mk K I) =
      CommRing.Pic.mk R (FractionalIdeal.unitsMulEquivSubmodule
        (Units.map (FractionalIdeal.canonicalEquiv R⁰ K
          (FractionRing R)).toMonoidHom I)) := by
  rw [ClassGroup.mk_def]
  rfl

/-- The affine line-bundle class is represented by the explicit inverse fractional ideal. -/
lemma lineBundleClass_eq_mk_inverseIdeal
    (D : WeilDivisor (HeightOneSpectrum R)) :
    AffineDedekind.lineBundleClass R K D = CommRing.Pic.mk R (inverseIdeal R K D) := by
  let I := divisorFractionalIdeal R K D
  have hD : fractionalIdealDivisor R K (Additive.ofMul I) = D := by
    change fractionalIdealDivisor R K
      ((fractionalIdealDivisorAddEquiv R K).symm D) = D
    rw [← fractionalIdealDivisorAddEquiv_apply, AddEquiv.apply_symm_apply]
  calc
    AffineDedekind.lineBundleClass R K D =
        AffineDedekind.lineBundleClass R K
          (fractionalIdealDivisor R K (Additive.ofMul I)) :=
      congrArg (AffineDedekind.lineBundleClass R K) hD.symm
    _ = (ClassGroup.equivPic R (ClassGroup.mk K I))⁻¹ :=
      AffineDedekind.lineBundleClass_fractionalIdealDivisor R K I
    _ = ClassGroup.equivPic R (ClassGroup.mk K I⁻¹) := by
      rw [← map_inv, ← map_inv]
    _ = CommRing.Pic.mk R (FractionalIdeal.unitsMulEquivSubmodule
        (Units.map (FractionalIdeal.canonicalEquiv R⁰ K
          (FractionRing R)).toMonoidHom I⁻¹)) :=
      equivPic_mk_fractionalIdeal R K I⁻¹
    _ = CommRing.Pic.mk R (inverseIdeal R K D) := rfl

/-- The chosen Picard representative is linearly equivalent to the explicit inverse divisor
ideal. -/
noncomputable def lineBundleModuleEquivInverseIdeal
    (D : WeilDivisor (HeightOneSpectrum R)) :
    AffineDedekind.lineBundleModule R K D ≃ₗ[R] inverseIdeal R K D :=
  (by
    rw [← CommRing.Pic.mk_eq_mk_iff,
      AffineDedekind.lineBundleModule_picClass,
      lineBundleClass_eq_mk_inverseIdeal] :
    Nonempty (AffineDedekind.lineBundleModule R K D ≃ₗ[R]
      inverseIdeal R K D)).some

end ExplicitIdeal

namespace Boundary

/-- The exact same-chart principal-open equality consumed by the checked restriction chain. -/
def InverseIdealLocalizationEq
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D E : WeilDivisor (HeightOneSpectrum R)) (f : R) : Prop :=
  (ExplicitIdeal.inverseIdeal R K D).localized (.powers f) =
    (ExplicitIdeal.inverseIdeal R K E).localized (.powers f)

/-- The exact cross-chart condition: after choosing two coordinate rings mapping through a
common affine overlap ring `B` into a common function field `K`, the maps form scalar towers and
the inverse divisor ideals extend to the same fractional ideal of `B`. The principal-divisor
case and the arbitrary-divisor localization/coefficient-compatibility case are discharged
below. -/
noncomputable def OverlapInverseIdealExtensionEq
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂)) : Prop :=
  IsScalarTower R₁ B K ∧ IsScalarTower R₂ B K ∧
    Units.map (FractionalIdeal.extendedHom K B).toMonoidHom
        (ExplicitIdeal.divisorFractionalIdeal R₁ K D₁)⁻¹ =
      Units.map (FractionalIdeal.extendedHom K B).toMonoidHom
        (ExplicitIdeal.divisorFractionalIdeal R₂ K D₂)⁻¹

end Boundary

namespace CommonExtension

/-- The extended inverse divisor ideal, regarded as a `B`-submodule of the common fraction
field `K`. -/
noncomputable abbrev extendedInverseIdeal
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    (D : WeilDivisor (HeightOneSpectrum R)) : Submodule B K :=
  Units.map (FractionalIdeal.extendedHom K B).toMonoidHom
    (ExplicitIdeal.divisorFractionalIdeal R K D)⁻¹

/-- Cross-chart extension equality identifies the two explicit overlap modules. -/
noncomputable def extendedInverseIdealEquiv
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    extendedInverseIdeal R₁ B K D₁ ≃ₗ[B]
      extendedInverseIdeal R₂ B K D₂ :=
  LinearEquiv.ofEq _ _ (congrArg
    (fun I : (FractionalIdeal B⁰ K)ˣ ↦ (I : Submodule B K)) h.2.2)

/-- Consequently the explicit extended ideals give isomorphic tilde sheaves on the common
affine overlap. -/
noncomputable def extendedInverseIdealTildeIso
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
        (ModuleCat.of B (extendedInverseIdeal R₁ B K D₁)) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
        (ModuleCat.of B (extendedInverseIdeal R₂ B K D₂)) :=
  (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).mapIso
    (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ h).toModuleIso

/-- The scheme morphism induced by an affine-overlap algebra. -/
noncomputable abbrev extensionMap
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    _root_.AlgebraicGeometry.Spec (.of B) ⟶
      _root_.AlgebraicGeometry.Spec (.of R) :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap R B))

/-- The second exact cross-chart input: restriction of the chosen affine divisor line bundle to
the common affine overlap agrees with tilde of the extended inverse divisor ideal. Flat
epimorphic base change below discharges this input on every affine open immersion; it is also
identified with the corresponding linear equivalence on affine global sections. -/
noncomputable def RestrictionIdentifiesExtendedInverseIdeal
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) : Prop :=
  IsScalarTower R B K ∧
    Nonempty
      ((AffineDedekind.lineBundle R K D).obj.restrict (extensionMap R B) ≅
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K D)))

/-- Global sections of the chosen divisor line bundle after restriction to a common affine
overlap. This is the module-level source of the arbitrary-overlap base-change comparison. -/
noncomputable abbrev restrictedLineBundleGlobalSections
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) : ModuleCat.{u} B :=
  (_root_.AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of B)).obj
    ((AffineDedekind.lineBundle R K D).obj.restrict (extensionMap R B))

/-- The module-level arbitrary-overlap comparison: global sections of the restricted chosen
line bundle agree with the inverse divisor ideal extended to the overlap ring. -/
noncomputable def RestrictionGlobalSectionsEquivExtendedInverseIdeal
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) : Prop :=
  IsScalarTower R B K ∧
    Nonempty (restrictedLineBundleGlobalSections R B K D ≃ₗ[B]
      extendedInverseIdeal R B K D)

/-- On an affine overlap, identifying global sections with the extended inverse ideal suffices:
affine quasicoherent reconstruction supplies the sheaf-level restriction isomorphism. -/
theorem restrictionIdentifiesExtendedInverseIdeal_of_globalSectionsEquiv
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R))
    (h : RestrictionGlobalSectionsEquivExtendedInverseIdeal R B K D) :
    RestrictionIdentifiesExtendedInverseIdeal R B K D := by
  letI : IsScalarTower R B K := h.1
  refine ⟨h.1, ?_⟩
  let P := (AffineDedekind.lineBundle R K D).obj.restrict (extensionMap R B)
  letI : (AffineDedekind.lineBundle R K D).obj.IsQuasicoherent := by
    change (_root_.AlgebraicGeometry.tilde (R := CommRingCat.of R)
      (ModuleCat.of R (AffineDedekind.lineBundleModule R K D))).IsQuasicoherent
    infer_instance
  letI : P.IsQuasicoherent :=
    _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor
      (extensionMap R B) (AffineDedekind.lineBundle R K D).obj
  haveI : IsIso (_root_.AlgebraicGeometry.Scheme.Modules.fromTildeΓ
      (R := CommRingCat.of B) P) :=
    _root_.AlgebraicGeometry.Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent P
  exact ⟨(@asIso _ _ _ _
      (_root_.AlgebraicGeometry.Scheme.Modules.fromTildeΓ
        (R := CommRingCat.of B) P) inferInstance).symm ≪≫
    (_root_.AlgebraicGeometry.tilde.functor (CommRingCat.of B)).mapIso
      h.2.some.toModuleIso⟩

/-- Conversely, a sheaf-level restriction identification induces the corresponding
module-level identification on affine global sections. -/
theorem restrictionGlobalSectionsEquivExtendedInverseIdeal_of_identifies
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R))
    (h : RestrictionIdentifiesExtendedInverseIdeal R B K D) :
    RestrictionGlobalSectionsEquivExtendedInverseIdeal R B K D := by
  letI : IsScalarTower R B K := h.1
  refine ⟨h.1, ?_⟩
  let e₁ := (_root_.AlgebraicGeometry.moduleSpecΓFunctor
    (R := CommRingCat.of B)).mapIso h.2.some
  let e₂ := (_root_.AlgebraicGeometry.tilde.isoTop (R := CommRingCat.of B)
    (ModuleCat.of B (extendedInverseIdeal R B K D))).symm
  exact ⟨e₁.toLinearEquiv.trans e₂.toLinearEquiv⟩

/-- Affine quasicoherent reconstruction makes the sheaf-level and module-level arbitrary
overlap restriction boundaries equivalent. -/
theorem restrictionIdentifiesExtendedInverseIdeal_iff_globalSectionsEquiv
    (R B K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    RestrictionIdentifiesExtendedInverseIdeal R B K D ↔
      RestrictionGlobalSectionsEquivExtendedInverseIdeal R B K D :=
  ⟨restrictionGlobalSectionsEquivExtendedInverseIdeal_of_identifies R B K D,
    restrictionIdentifiesExtendedInverseIdeal_of_globalSectionsEquiv R B K D⟩

/-- The two exact cross-chart inputs produce an actual isomorphism between the restrictions of
the chosen affine divisor line bundles to the common affine overlap. -/
noncomputable def chosenLineBundleRestrictionIso
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₁ B)]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₂ B)]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h₁ : RestrictionIdentifiesExtendedInverseIdeal R₁ B K D₁)
    (h₂ : RestrictionIdentifiesExtendedInverseIdeal R₂ B K D₂)
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    (AffineDedekind.lineBundle R₁ K D₁).obj.restrict (extensionMap R₁ B) ≅
      (AffineDedekind.lineBundle R₂ K D₂).obj.restrict (extensionMap R₂ B) :=
  h₁.2.some ≪≫ extendedInverseIdealTildeIso R₁ R₂ B K D₁ D₂ h ≪≫ h₂.2.some.symm

/-- Module-level global-sections comparisons on both charts, together with equality of the
extended ideals, construct an isomorphism of the actual chosen restrictions. -/
noncomputable def chosenLineBundleRestrictionIsoOfGlobalSectionsEquiv
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₁ B)]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₂ B)]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h₁ : RestrictionGlobalSectionsEquivExtendedInverseIdeal R₁ B K D₁)
    (h₂ : RestrictionGlobalSectionsEquivExtendedInverseIdeal R₂ B K D₂)
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    (AffineDedekind.lineBundle R₁ K D₁).obj.restrict (extensionMap R₁ B) ≅
      (AffineDedekind.lineBundle R₂ K D₂).obj.restrict (extensionMap R₂ B) :=
  chosenLineBundleRestrictionIso R₁ R₂ B K D₁ D₂
    (restrictionIdentifiesExtendedInverseIdeal_of_globalSectionsEquiv R₁ B K D₁ h₁)
    (restrictionIdentifiesExtendedInverseIdeal_of_globalSectionsEquiv R₂ B K D₂ h₂) h

end CommonExtension

namespace LocalizedModule

variable {R : Type u} [CommRing R]

private noncomputable abbrev awayRing (f : R) := Localization.Away f

/-- A linear equivalence localizes functorially. -/
noncomputable def mapLinearEquiv
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : R) (e : M ≃ₗ[R] N) :
    _root_.LocalizedModule.Away f M ≃ₗ[awayRing f]
      _root_.LocalizedModule.Away f N := by
  let l : _root_.LocalizedModule.Away f M →ₗ[R]
      _root_.LocalizedModule.Away f N :=
    IsLocalizedModule.map (.powers f)
      (_root_.LocalizedModule.mkLinearMap (.powers f) M)
      (_root_.LocalizedModule.mkLinearMap (.powers f) N) e.toLinearMap
  let l' : _root_.LocalizedModule.Away f M →ₗ[awayRing f]
      _root_.LocalizedModule.Away f N :=
    l.extendScalarsOfIsLocalization (.powers f) (awayRing f)
  exact LinearEquiv.ofBijective l' ⟨
    IsLocalizedModule.map_injective _ _ _ e.toLinearMap e.injective,
    IsLocalizedModule.map_surjective _ _ _ e.toLinearMap e.surjective⟩

/-- Equality of realized localized submodules gives an equivalence of module localizations. -/
noncomputable def submoduleEquivOfEq
    {M : Type u} [AddCommGroup M] [Module R M]
    (f : R) (P Q : Submodule R M)
    (h : P.localized (.powers f) = Q.localized (.powers f)) :
    _root_.LocalizedModule.Away f P ≃ₗ[awayRing f]
      _root_.LocalizedModule.Away f Q :=
  (P.localizedEquiv (.powers f)).symm |>.trans <|
    (LinearEquiv.ofEq _ _ h).trans (Q.localizedEquiv (.powers f))

end LocalizedModule

namespace PrincipalRestriction

variable {A : CommRingCat.{u}} (M N : ModuleCat.{u} A) (f : A)

private noncomputable abbrev awayRing := Localization.Away f

private noncomputable abbrev awayMap :
    _root_.AlgebraicGeometry.Spec (CommRingCat.of (awayRing f)) ⟶
      _root_.AlgebraicGeometry.Spec A :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap A (awayRing f)))

/-- An equivalence of localized modules gives an actual isomorphism of their tilde restrictions
to the corresponding principal open. -/
noncomputable def isoOfLocalizedLinearEquiv
    (e : _root_.LocalizedModule.Away f M ≃ₗ[awayRing f]
      _root_.LocalizedModule.Away f N) :
    (_root_.AlgebraicGeometry.tilde M).restrict (awayMap f) ≅
      (_root_.AlgebraicGeometry.tilde N).restrict (awayMap f) :=
  (AffineTilde.localizedTildeRestrictIso M f).symm ≪≫
    (_root_.AlgebraicGeometry.tilde.functor
      (CommRingCat.of (awayRing f))).mapIso e.toModuleIso ≪≫
    AffineTilde.localizedTildeRestrictIso N f

end PrincipalRestriction

namespace Chain

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private noncomputable abbrev chosenModule
    (D : WeilDivisor (HeightOneSpectrum R)) : ModuleCat.{u} (CommRingCat.of R) :=
  ModuleCat.of R (AffineDedekind.lineBundleModule R K D)

private noncomputable abbrev awayRing (f : R) := Localization.Away f

private noncomputable abbrev awayMap (f : R) :
    _root_.AlgebraicGeometry.Spec (CommRingCat.of (awayRing R f)) ⟶
      _root_.AlgebraicGeometry.Spec (CommRingCat.of R) :=
  _root_.AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap R (awayRing R f)))

private noncomputable abbrev chosenRestriction
    (D : WeilDivisor (HeightOneSpectrum R)) (f : R) :=
  (_root_.AlgebraicGeometry.tilde
    (chosenModule (R := R) (K := K) D)).restrict (awayMap R f)

/-- The chosen line-bundle representatives localize compatibly once their explicit inverse
ideals do. -/
noncomputable def localizedLineBundleModuleEquivOfInverseIdealEq
    (D E : WeilDivisor (HeightOneSpectrum R)) (f : R)
    (h : Boundary.InverseIdealLocalizationEq R K D E f) :
    _root_.LocalizedModule.Away f (chosenModule (R := R) (K := K) D) ≃ₗ[awayRing R f]
      _root_.LocalizedModule.Away f (chosenModule (R := R) (K := K) E) :=
  (LocalizedModule.mapLinearEquiv f
    (ExplicitIdeal.lineBundleModuleEquivInverseIdeal R K D)).trans <|
    (LocalizedModule.submoduleEquivOfEq f
      (ExplicitIdeal.inverseIdeal R K D)
      (ExplicitIdeal.inverseIdeal R K E) h).trans <|
      (LocalizedModule.mapLinearEquiv f
        (ExplicitIdeal.lineBundleModuleEquivInverseIdeal R K E)).symm

/-- Full checked chain from equality of explicit localized ideals to an isomorphism of the
chosen affine divisor line bundles restricted to a principal open. -/
noncomputable def chosenTildeRestrictIsoOfInverseIdealEq
    (D E : WeilDivisor (HeightOneSpectrum R)) (f : R)
    (h : Boundary.InverseIdealLocalizationEq R K D E f) :
    chosenRestriction (R := R) (K := K) D f ≅
      chosenRestriction (R := R) (K := K) E f :=
  PrincipalRestriction.isoOfLocalizedLinearEquiv
    (chosenModule (R := R) (K := K) D)
    (chosenModule (R := R) (K := K) E) f
    (localizedLineBundleModuleEquivOfInverseIdealEq R K D E f h)

end Chain

namespace CommonExtension

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

private noncomputable def extendScalarsTildeIsoRestrict
    (A B : CommRingCat.{u}) (f : A ⟶ B)
    [IsOpenImmersion (Spec.map f)] :
    ModuleCat.extendScalars f.hom ⋙ tilde.functor B ≅
      tilde.functor A ⋙ Scheme.Modules.restrictFunctor (Spec.map f) :=
  extendScalarsTildeIsoPullback A B f ≪≫
    Functor.isoWhiskerLeft (tilde.functor A)
      (Scheme.Modules.restrictFunctorIsoPullback (Spec.map f)).symm

private noncomputable abbrev originalInverseIdeal
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D : WeilDivisor (HeightOneSpectrum R)) : Submodule R K :=
  ((ExplicitIdeal.divisorFractionalIdeal R K D)⁻¹).1.1

private noncomputable abbrev chosenModule
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
      ModuleCat.{u} (CommRingCat.of R) :=
  ModuleCat.of R (AffineDedekind.lineBundleModule R K D)

private noncomputable abbrev fractionEquiv
    (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    FractionRing R ≃ₐ[R] K :=
  IsLocalization.algEquiv R⁰ (FractionRing R) K

private lemma fractionMap_eq_id
    (R B K : Type u) [CommRing R] [IsDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K] :
    IsLocalization.map (S := K) K (algebraMap R B)
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (FaithfulSMul.algebraMap_injective R B)) = RingHom.id K := by
  apply IsLocalization.map_unique _ (RingHom.id K)
  intro r
  rw [RingHom.id_apply, IsScalarTower.algebraMap_apply R B K]

private lemma extendedInverseIdeal_eq_span
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    extendedInverseIdeal R B K D =
      Submodule.span B
        ((fun x : K ↦ x) '' (originalInverseIdeal R K D : Set K)) := by
  let hf : R⁰ ≤ B⁰.comap (algebraMap R B) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective R B)
  unfold extendedInverseIdeal
  change
    ((FractionalIdeal.extended K hf
      ((ExplicitIdeal.divisorFractionalIdeal R K D)⁻¹).1 :
        FractionalIdeal B⁰ K) : Submodule B K) = _
  rw [FractionalIdeal.coe_extended_eq_span, show IsLocalization.map K (algebraMap R B) hf =
    RingHom.id K from fractionMap_eq_id R B K]
  rfl

private lemma inverseIdeal_map_fractionEquiv
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (ExplicitIdeal.inverseIdeal R K D).map (fractionEquiv R K).toLinearMap =
      originalInverseIdeal R K D := by
  ext x
  rw [Submodule.mem_map_equiv]
  change (fractionEquiv R K).symm x ∈
      FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)
        ((ExplicitIdeal.divisorFractionalIdeal R K D)⁻¹).1 ↔
    x ∈ ((ExplicitIdeal.divisorFractionalIdeal R K D)⁻¹).1
  rw [FractionalIdeal.mem_canonicalEquiv_apply]
  have hmap :
      IsLocalization.map (S := K) (T := R⁰) (FractionRing R) (RingHom.id R)
          (fun y (hy : y ∈ R⁰) => show RingHom.id R y ∈ R⁰ from hy) =
        (fractionEquiv R K).symm.toRingHom := by
    apply IsLocalization.map_unique _ _
    intro r
    simp [fractionEquiv]
  rw [hmap]
  constructor
  · rintro ⟨y, hy, he⟩
    simpa only [(fractionEquiv R K).symm.injective he] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private noncomputable def inverseIdealEquivChosenFraction
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    ExplicitIdeal.inverseIdeal R K D ≃ₗ[R] originalInverseIdeal R K D :=
  (fractionEquiv R K).toLinearEquiv.ofSubmodules _ _
    (inverseIdeal_map_fractionEquiv R K D)

private noncomputable def chosenModuleEquivOriginalInverseIdeal
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    AffineDedekind.lineBundleModule R K D ≃ₗ[R] originalInverseIdeal R K D :=
  (ExplicitIdeal.lineBundleModuleEquivInverseIdeal R K D).trans
    (inverseIdealEquivChosenFraction R K D)

private noncomputable def originalInverseIdealBaseChangeEquivExtended
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    (S : Submonoid R) [IsLocalization S B]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    B ⊗[R] originalInverseIdeal R K D ≃ₗ[B]
      extendedInverseIdeal R B K D := by
  letI : IsLocalizedModule S (LinearMap.id : K →ₗ[R] K) :=
    isLocalizedModule_id S K B
  let P : Submodule R K := originalInverseIdeal R K D
  have hP : P.localized' B S (LinearMap.id : K →ₗ[R] K) =
      extendedInverseIdeal R B K D := by
    rw [Submodule.localized'_eq_span, extendedInverseIdeal_eq_span R B K D]
    rfl
  exact (IsLocalizedModule.isBaseChange S B
    (P.toLocalized' B S (LinearMap.id : K →ₗ[R] K))).equiv |>.trans
      (LinearEquiv.ofEq _ _ hP)

private noncomputable def originalInverseIdealBaseChangeEquivExtended_of_flat_epi
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    B ⊗[R] originalInverseIdeal R K D ≃ₗ[B]
      extendedInverseIdeal R B K D := by
  let P : Submodule R K := originalInverseIdeal R K D
  have hP : Submodule.span B (P : Set K) = extendedInverseIdeal R B K D := by
    simpa [P] using (extendedInverseIdeal_eq_span R B K D).symm
  exact (P.tensorEquivSpan B).trans (LinearEquiv.ofEq _ _ hP)

private noncomputable def originalInverseIdealBaseChangeEquivExtended_of_isOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    B ⊗[R] originalInverseIdeal R K D ≃ₗ[B]
      extendedInverseIdeal R B K D := by
  let f : CommRingCat.of R ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (algebraMap R B)
  letI : Mono (Scheme.Spec.map f.op) := by
    change Mono (Spec.map f)
    infer_instance
  letI : Mono f.op := Scheme.Spec.mono_of_mono_map inferInstance
  letI : Epi f := by
    change Epi f.op.unop
    infer_instance
  letI : Algebra.IsEpi R B :=
    CommRingCat.epi_iff_epi.mp (inferInstanceAs (Epi f))
  letI : Module.Flat R B := inferInstance
  exact originalInverseIdealBaseChangeEquivExtended_of_flat_epi R B K D

private noncomputable def extendScalarsCarrierEquiv
    (R B M N : Type u) [CommRing R] [CommRing B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N]
    [Algebra R B]
    (e : B ⊗[R] M ≃ₗ[B] N) :
    (ModuleCat.extendScalars (algebraMap R B)).obj
        (ModuleCat.of R M) ≃ₗ[B] N := by
  dsimp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
  letI : IsScalarTower R B
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eB : ((ModuleCat.restrictScalars (algebraMap R B)).obj
      (ModuleCat.of B B)) ≃ₗ[B] B := LinearEquiv.refl B B
  let eM : ModuleCat.of R M ≃ₗ[R] M := LinearEquiv.refl R M
  exact (TensorProduct.AlgebraTensorModule.congr eB eM).trans e

private noncomputable def chosenModuleBaseChangeEquivExtended
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    (S : Submonoid R) [IsLocalization S B]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (ModuleCat.extendScalars (algebraMap R B)).obj (chosenModule R K D) ≃ₗ[B]
      extendedInverseIdeal R B K D := by
  exact extendScalarsCarrierEquiv R B
    (AffineDedekind.lineBundleModule R K D)
    (extendedInverseIdeal R B K D) <|
      ((chosenModuleEquivOriginalInverseIdeal R K D).baseChange R B).trans
        (originalInverseIdealBaseChangeEquivExtended R B K S D)

private noncomputable def chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (ModuleCat.extendScalars (algebraMap R B)).obj (chosenModule R K D) ≃ₗ[B]
      extendedInverseIdeal R B K D := by
  exact extendScalarsCarrierEquiv R B
    (AffineDedekind.lineBundleModule R K D)
    (extendedInverseIdeal R B K D) <|
      ((chosenModuleEquivOriginalInverseIdeal R K D).baseChange R B).trans
        (originalInverseIdealBaseChangeEquivExtended_of_isOpenImmersion R B K D)

/-- On every affine open immersion between the chart spectrum and a common overlap spectrum,
restriction of the chosen affine divisor line bundle is tilde of the extended inverse divisor
ideal. No classical localization presentation is required. -/
theorem restrictionIdentifiesExtendedInverseIdeal_of_isOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    RestrictionIdentifiesExtendedInverseIdeal R B K D := by
  refine ⟨inferInstance, ?_⟩
  let M := chosenModule R K D
  exact ⟨((extendScalarsTildeIsoRestrict
      (CommRingCat.of R) (CommRingCat.of B)
      (CommRingCat.ofHom (algebraMap R B))).app M).symm ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D).toModuleIso⟩

/-- On every affine open immersion, affine global sections of the restricted chosen line bundle
identify with the extended inverse divisor ideal. -/
theorem restrictionGlobalSectionsEquivExtendedInverseIdeal_of_isOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    RestrictionGlobalSectionsEquivExtendedInverseIdeal R B K D :=
  restrictionGlobalSectionsEquivExtendedInverseIdeal_of_identifies R B K D
    (restrictionIdentifiesExtendedInverseIdeal_of_isOpenImmersion R B K D)

/-- The packaged `Boundary.OverlapInverseIdealExtensionEq` condition now suffices to identify the
actual chosen line-bundle restrictions on an affine overlap. Besides ideal equality, that
condition records the two scalar towers; affine-open flat epimorphic base change supplies both
restriction comparisons. -/
noncomputable def chosenLineBundleRestrictionIsoOfOverlapExtensionEq
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [IsOpenImmersion (extensionMap R₁ B)]
    [IsOpenImmersion (extensionMap R₂ B)]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    (AffineDedekind.lineBundle R₁ K D₁).obj.restrict (extensionMap R₁ B) ≅
      (AffineDedekind.lineBundle R₂ K D₂).obj.restrict (extensionMap R₂ B) := by
  letI : IsScalarTower R₁ B K := h.1
  letI : IsScalarTower R₂ B K := h.2.1
  exact chosenLineBundleRestrictionIso R₁ R₂ B K D₁ D₂
    (restrictionIdentifiesExtendedInverseIdeal_of_isOpenImmersion R₁ B K D₁)
    (restrictionIdentifiesExtendedInverseIdeal_of_isOpenImmersion R₂ B K D₂) h

/-- If the induced spectrum map is an open immersion and the overlap ring is a localization of
the chart ring, restriction of the chosen affine divisor line bundle is tilde of the extended
inverse divisor ideal. -/
theorem restrictionIdentifiesExtendedInverseIdeal_of_isLocalization
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (S : Submonoid R) [IsLocalization S B]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    RestrictionIdentifiesExtendedInverseIdeal R B K D := by
  refine ⟨inferInstance, ?_⟩
  let M := chosenModule R K D
  exact ⟨((extendScalarsTildeIsoRestrict
      (CommRingCat.of R) (CommRingCat.of B)
      (CommRingCat.ofHom (algebraMap R B))).app M).symm ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (chosenModuleBaseChangeEquivExtended R B K S D).toModuleIso⟩

/-- Under an open-immersion localization presentation, affine global sections of the restricted
chosen line bundle identify with the extended inverse divisor ideal. -/
theorem restrictionGlobalSectionsEquivExtendedInverseIdeal_of_isLocalization
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (S : Submonoid R) [IsLocalization S B]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    RestrictionGlobalSectionsEquivExtendedInverseIdeal R B K D :=
  restrictionGlobalSectionsEquivExtendedInverseIdeal_of_identifies R B K D
    (restrictionIdentifiesExtendedInverseIdeal_of_isLocalization R B K S D)

section PrincipalOpen

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable (f : R) [IsDomain (Localization.Away f)]
variable [Algebra (Localization.Away f) K]
variable [IsFractionRing (Localization.Away f) K]
variable [IsScalarTower R (Localization.Away f) K]

private noncomputable def localizedOriginalInverseIdealEquivExtended
    (D : WeilDivisor (HeightOneSpectrum R)) :
    _root_.LocalizedModule.Away f (originalInverseIdeal R K D) ≃ₗ[Localization.Away f]
      extendedInverseIdeal R (Localization.Away f) K D := by
  letI : IsLocalizedModule (.powers f) (LinearMap.id : K →ₗ[R] K) :=
    isLocalizedModule_id (.powers f) K (Localization.Away f)
  let P : Submodule R K := originalInverseIdeal R K D
  let J : Submodule (Localization.Away f) K :=
    extendedInverseIdeal R (Localization.Away f) K D
  have hJ : J = P.localized' (Localization.Away f) (.powers f)
      (LinearMap.id : K →ₗ[R] K) := by
    rw [Submodule.localized'_eq_span]
    exact extendedInverseIdeal_eq_span R (Localization.Away f) K D
  let eR : P.localized' (Localization.Away f) (.powers f)
        (LinearMap.id : K →ₗ[R] K) ≃ₗ[R]
      _root_.LocalizedModule.Away f P :=
    IsLocalizedModule.linearEquiv (.powers f)
      (P.toLocalized' (Localization.Away f) (.powers f)
        (LinearMap.id : K →ₗ[R] K))
      (_root_.LocalizedModule.mkLinearMap (.powers f) P)
  let e : P.localized' (Localization.Away f) (.powers f)
        (LinearMap.id : K →ₗ[R] K) ≃ₗ[Localization.Away f]
      _root_.LocalizedModule.Away f P :=
    eR.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
  exact e.symm.trans (LinearEquiv.ofEq _ _ hJ.symm)

private noncomputable def localizedChosenModuleEquivExtended
    (D : WeilDivisor (HeightOneSpectrum R)) :
    _root_.LocalizedModule.Away f (chosenModule R K D) ≃ₗ[
        Localization.Away f] extendedInverseIdeal R (Localization.Away f) K D :=
  (LocalizedModule.mapLinearEquiv f
      (chosenModuleEquivOriginalInverseIdeal R K D)).trans
    (localizedOriginalInverseIdealEquivExtended R K f D)

private noncomputable def chosenTildeRestrictionIsoExtended
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (_root_.AlgebraicGeometry.tilde (chosenModule R K D)).restrict
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of (Localization.Away f))
        (ModuleCat.of (Localization.Away f)
          (extendedInverseIdeal R (Localization.Away f) K D)) :=
  CategoryTheory.Iso.trans
    (Y := _root_.AlgebraicGeometry.tilde
      (R := CommRingCat.of (Localization.Away f))
      (ModuleCat.of (Localization.Away f)
        (_root_.LocalizedModule.Away f (chosenModule R K D))))
    (AffineTilde.localizedTildeRestrictIso (chosenModule R K D) f).symm
    ((_root_.AlgebraicGeometry.tilde.functor
      (CommRingCat.of (Localization.Away f))).mapIso
        (localizedChosenModuleEquivExtended R K f D).toModuleIso)

/-- On a nonempty principal open, restriction of the chosen affine divisor line bundle is tilde
of the inverse divisor ideal extended to the localized coordinate ring. -/
theorem restrictionIdentifiesExtendedInverseIdeal_away
    (D : WeilDivisor (HeightOneSpectrum R)) :
    RestrictionIdentifiesExtendedInverseIdeal R (Localization.Away f) K D := by
  refine ⟨inferInstance, ?_⟩
  change Nonempty
    ((_root_.AlgebraicGeometry.tilde (chosenModule R K D)).restrict
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of (Localization.Away f))
        (ModuleCat.of (Localization.Away f)
          (extendedInverseIdeal R (Localization.Away f) K D)))
  exact ⟨chosenTildeRestrictionIsoExtended R K f D⟩

/-- The principal-open restriction theorem supplies both base-change inputs required to turn
equality of the extended inverse ideals into an isomorphism of the chosen restricted bundles. -/
noncomputable def chosenLineBundleRestrictionIsoAway
    (D E : WeilDivisor (HeightOneSpectrum R))
    (h : Boundary.OverlapInverseIdealExtensionEq
      R R (Localization.Away f) K D E) :
    (AffineDedekind.lineBundle R K D).obj.restrict
        (extensionMap R (Localization.Away f)) ≅
      (AffineDedekind.lineBundle R K E).obj.restrict
        (extensionMap R (Localization.Away f)) :=
  chosenLineBundleRestrictionIso R R (Localization.Away f) K D E
    (restrictionIdentifiesExtendedInverseIdeal_away R K f D)
    (restrictionIdentifiesExtendedInverseIdeal_away R K f E) h

end PrincipalOpen

end CommonExtension

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization

open CategoryTheory
open _root_.AlgebraicGeometry
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors TensorProduct

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension

private noncomputable def localizedFractionEquiv
    (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K] :
    _root_.LocalizedModule.Away f (FractionRing R) ≃ₗ[Localization.Away f] K := by
  let e := fractionEquiv R K
  letI : IsLocalizedModule (.powers f) (LinearMap.id : K →ₗ[R] K) :=
    isLocalizedModule_id (.powers f) K (Localization.Away f)
  have hlocal : IsLocalizedModule (.powers f)
      ((LinearMap.id : K →ₗ[R] K) ∘ₗ e.toLinearMap) := inferInstance
  have hcomp : (LinearMap.id : K →ₗ[R] K) ∘ₗ e.toLinearMap = e.toLinearMap := by
    ext x
    rfl
  rw [hcomp] at hlocal
  letI : IsLocalizedModule (.powers f) e.toLinearMap := hlocal
  exact (IsLocalizedModule.linearEquiv (.powers f)
    (_root_.LocalizedModule.mkLinearMap (.powers f) (FractionRing R))
    e.toLinearMap).extendScalarsOfIsLocalization (.powers f) (Localization.Away f)

private lemma localizedFractionEquiv_mk
    (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K]
    (x : FractionRing R) :
    localizedFractionEquiv R K f
        (_root_.LocalizedModule.mkLinearMap (.powers f) (FractionRing R) x) =
      fractionEquiv R K x := by
  simp only [localizedFractionEquiv,
    LinearEquiv.extendScalarsOfIsLocalization_apply]
  rw [IsLocalizedModule.linearEquiv_apply]
  rfl

private lemma map_localized_inverseIdeal_eq_span
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    ((ExplicitIdeal.inverseIdeal R K D).localized (.powers f)).map
        (localizedFractionEquiv R K f).toLinearMap =
      Submodule.span (Localization.Away f)
        (fractionEquiv R K ''
          (ExplicitIdeal.inverseIdeal R K D : Set (FractionRing R))) := by
  change ((ExplicitIdeal.inverseIdeal R K D).localized'
      (Localization.Away f) (.powers f)
      (_root_.LocalizedModule.mkLinearMap (.powers f) (FractionRing R))).map
        (localizedFractionEquiv R K f).toLinearMap = _
  rw [Submodule.localized'_eq_span, Submodule.map_span]
  congr 1
  rw [Set.image_image]
  apply Set.image_congr
  intro x hx
  exact localizedFractionEquiv_mk R K f x

private lemma map_localized_inverseIdeal_eq_extended
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    ((ExplicitIdeal.inverseIdeal R K D).localized (.powers f)).map
        (localizedFractionEquiv R K f).toLinearMap =
      extendedInverseIdeal R (Localization.Away f) K D := by
  rw [map_localized_inverseIdeal_eq_span]
  have himage :
      fractionEquiv R K ''
          (ExplicitIdeal.inverseIdeal R K D : Set (FractionRing R)) =
        (originalInverseIdeal R K D : Set K) := by
    change (fractionEquiv R K).toLinearMap ''
        (ExplicitIdeal.inverseIdeal R K D : Set (FractionRing R)) = _
    rw [← Submodule.map_coe, inverseIdeal_map_fractionEquiv R K D]
  rw [himage]
  symm
  simpa using extendedInverseIdeal_eq_span R (Localization.Away f) K D

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.ExplicitIdeal

variable (R K : Type u) [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The explicit fractional ideal of a principal divisor is the corresponding principal
fractional ideal. -/
lemma divisorFractionalIdeal_principalDivisor (g : Additive Kˣ) :
    divisorFractionalIdeal R K
        ((OrderSystem.ofDedekindDomain R K).principalDivisor g) =
      toPrincipalIdeal R K (Additive.toMul g) := by
  unfold divisorFractionalIdeal
  have h :
      (fractionalIdealDivisorAddEquiv R K).symm
          ((OrderSystem.ofDedekindDomain R K).principalDivisor g) =
        Additive.ofMul (toPrincipalIdeal R K (Additive.toMul g)) := by
    apply (fractionalIdealDivisorAddEquiv R K).injective
    rw [AddEquiv.apply_symm_apply]
    exact (fractionalIdealDivisorAddEquiv_toPrincipalIdeal (Additive.toMul g)).symm
  exact congrArg Additive.toMul h

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.ExplicitIdeal

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary

/-- Principal divisors defined by the same rational function have equal inverse fractional
ideals after extension from two distinct Dedekind chart rings to a common overlap ring. -/
theorem overlapInverseIdealExtensionEq_principal
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    (h₁ : IsScalarTower R₁ B K) (h₂ : IsScalarTower R₂ B K)
    (g : Additive Kˣ) :
    OverlapInverseIdealExtensionEq R₁ R₂ B K
      ((OrderSystem.ofDedekindDomain R₁ K).principalDivisor g)
      ((OrderSystem.ofDedekindDomain R₂ K).principalDivisor g) := by
  letI : IsScalarTower R₁ B K := h₁
  letI : IsScalarTower R₂ B K := h₂
  refine ⟨h₁, h₂, ?_⟩
  rw [ExplicitIdeal.divisorFractionalIdeal_principalDivisor,
    ExplicitIdeal.divisorFractionalIdeal_principalDivisor]
  apply Units.ext
  simp only [Units.coe_map, Units.val_inv_eq_inv_val,
    coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_inv]
  have hmap₁ :
      IsFractionRing.map (FaithfulSMul.algebraMap_injective R₁ B) =
        RingHom.id K := by
    apply IsLocalization.map_unique _ (RingHom.id K)
    intro r
    rw [RingHom.id_apply, IsScalarTower.algebraMap_apply R₁ B K]
  have hmap₂ :
      IsFractionRing.map (FaithfulSMul.algebraMap_injective R₂ B) =
        RingHom.id K := by
    apply IsLocalization.map_unique _ (RingHom.id K)
    intro r
    rw [RingHom.id_apply, IsScalarTower.algebraMap_apply R₂ B K]
  calc
    (FractionalIdeal.extendedHom K B)
        (FractionalIdeal.spanSingleton R₁⁰ ((Additive.toMul g : Kˣ) : K)⁻¹) =
        FractionalIdeal.spanSingleton B⁰
          (IsFractionRing.map (FaithfulSMul.algebraMap_injective R₁ B)
            ((Additive.toMul g : Kˣ) : K)⁻¹) :=
      FractionalIdeal.extendedHom_spanSingleton K B _
    _ = FractionalIdeal.spanSingleton B⁰ ((Additive.toMul g : Kˣ) : K)⁻¹ := by
      rw [hmap₁, RingHom.id_apply]
    _ = FractionalIdeal.spanSingleton B⁰
          (IsFractionRing.map (FaithfulSMul.algebraMap_injective R₂ B)
            ((Additive.toMul g : Kˣ) : K)⁻¹) := by
      rw [hmap₂, RingHom.id_apply]
    _ = (FractionalIdeal.extendedHom K B)
        (FractionalIdeal.spanSingleton R₂⁰ ((Additive.toMul g : Kˣ) : K)⁻¹) :=
      (FractionalIdeal.extendedHom_spanSingleton K B _).symm

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension

/-- The concrete cross-chart principal-divisor consumer: one rational function gives
isomorphic chosen divisor line bundles on a common affine overlap once the two independent
restriction/base-change identifications are available. -/
noncomputable def chosenLineBundleRestrictionIsoPrincipal
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₁ B)]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₂ B)]
    (g : Additive Kˣ)
    (h₁ : RestrictionIdentifiesExtendedInverseIdeal R₁ B K
      ((OrderSystem.ofDedekindDomain R₁ K).principalDivisor g))
    (h₂ : RestrictionIdentifiesExtendedInverseIdeal R₂ B K
      ((OrderSystem.ofDedekindDomain R₂ K).principalDivisor g)) :
    (AffineDedekind.lineBundle R₁ K
        ((OrderSystem.ofDedekindDomain R₁ K).principalDivisor g)).obj.restrict
        (extensionMap R₁ B) ≅
      (AffineDedekind.lineBundle R₂ K
        ((OrderSystem.ofDedekindDomain R₂ K).principalDivisor g)).obj.restrict
        (extensionMap R₂ B) :=
  chosenLineBundleRestrictionIso R₁ R₂ B K _ _ h₁ h₂
    (Boundary.overlapInverseIdealExtensionEq_principal R₁ R₂ B K h₁.1 h₂.1 g)

/-- On any common affine overlap, one rational function gives isomorphic restrictions of the
chosen line bundles attached to its two chartwise principal divisors. No classical localization
presentation of either open immersion is required. -/
noncomputable def chosenLineBundleRestrictionIsoPrincipalOfIsOpenImmersion
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₁ B)]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₂ B)]
    (h₁ : IsScalarTower R₁ B K) (h₂ : IsScalarTower R₂ B K)
    (g : Additive Kˣ) :
    (AffineDedekind.lineBundle R₁ K
        ((OrderSystem.ofDedekindDomain R₁ K).principalDivisor g)).obj.restrict
        (extensionMap R₁ B) ≅
      (AffineDedekind.lineBundle R₂ K
        ((OrderSystem.ofDedekindDomain R₂ K).principalDivisor g)).obj.restrict
        (extensionMap R₂ B) :=
  chosenLineBundleRestrictionIsoOfOverlapExtensionEq R₁ R₂ B K _ _
    (Boundary.overlapInverseIdealExtensionEq_principal R₁ R₂ B K h₁ h₂ g)

/-- If the common affine overlap ring is a localization of each chart ring, the chosen line
bundles attached to the principal divisor of one rational function have isomorphic
restrictions, with no separate restriction/base-change hypothesis. -/
noncomputable def chosenLineBundleRestrictionIsoPrincipalOfIsLocalization
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₁ B)]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₂ B)]
    (S₁ : Submonoid R₁) [IsLocalization S₁ B]
    (S₂ : Submonoid R₂) [IsLocalization S₂ B]
    (h₁ : IsScalarTower R₁ B K) (h₂ : IsScalarTower R₂ B K)
    (g : Additive Kˣ) :
    (AffineDedekind.lineBundle R₁ K
        ((OrderSystem.ofDedekindDomain R₁ K).principalDivisor g)).obj.restrict
        (extensionMap R₁ B) ≅
      (AffineDedekind.lineBundle R₂ K
        ((OrderSystem.ofDedekindDomain R₂ K).principalDivisor g)).obj.restrict
        (extensionMap R₂ B) := by
  letI : IsScalarTower R₁ B K := h₁
  letI : IsScalarTower R₂ B K := h₂
  exact chosenLineBundleRestrictionIsoPrincipal R₁ R₂ B K g
    (restrictionIdentifiesExtendedInverseIdeal_of_isLocalization R₁ B K S₁ _)
    (restrictionIdentifiesExtendedInverseIdeal_of_isLocalization R₂ B K S₂ _)

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension

open CategoryTheory
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors TensorProduct

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary

private lemma divisorFractionalIdeal_coe_eq_prod
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (ExplicitIdeal.divisorFractionalIdeal R K D : FractionalIdeal R⁰ K) =
      D.prod fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e := by
  unfold ExplicitIdeal.divisorFractionalIdeal
  rw [fractionalIdealDivisorAddEquiv_symm_apply]
  rfl

private lemma algebraIsEpiOfOpenImmersion
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsOpenImmersion (CommonExtension.extensionMap R B)] : Algebra.IsEpi R B := by
  let f : CommRingCat.of R ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (algebraMap R B)
  letI : Mono (Scheme.Spec.map f.op) := by
    change Mono (Spec.map f)
    infer_instance
  letI : Mono f.op := Scheme.Spec.mono_of_mono_map inferInstance
  letI : Epi f := by
    change Epi f.op.unop
    infer_instance
  exact CommRingCat.epi_iff_epi.mp (inferInstanceAs (Epi f))

private lemma moduleFlatOfOpenImmersion
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [IsOpenImmersion (CommonExtension.extensionMap R B)] : Module.Flat R B := by
  let f : CommRingCat.of R ⟶ CommRingCat.of B :=
    CommRingCat.ofHom (algebraMap R B)
  have hs : _root_.AlgebraicGeometry.Flat (Spec.map f) := by
    change _root_.AlgebraicGeometry.Flat (CommonExtension.extensionMap R B)
    infer_instance
  exact RingHom.flat_algebraMap_iff.mp
    (_root_.AlgebraicGeometry.Flat.SpecMap_iff.mp hs)

private lemma idealMapComapEqOfFlatEpi
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsEpi R B] [Module.Flat R B] (J : Ideal B) :
    Ideal.map (algebraMap R B) (Ideal.comap (algebraMap R B) J) = J := by
  apply le_antisymm Ideal.map_comap_le
  intro x hx
  let g : R →ₗ[R] B ⧸ J :=
    (Ideal.Quotient.mkₐ R J).toLinearMap.comp (Algebra.linearMap R B)
  let I : Ideal R := Ideal.comap (algebraMap R B) J
  have hker : LinearMap.ker g = I.restrictScalars R := by
    ext r
    change (Ideal.Quotient.mk J) (algebraMap R B r) = 0 ↔
      algebraMap R B r ∈ J
    exact Ideal.Quotient.eq_zero_iff_mem
  let e : B ⊗[R] R ≃ₐ[B] B := Algebra.TensorProduct.rid R B B
  have hyker : e.symm x ∈ LinearMap.ker (LinearMap.lTensor B g) := by
    rw [LinearMap.mem_ker]
    apply (TensorProduct.lid' R B (B ⧸ J)).injective
    simp only [map_zero, e, Algebra.TensorProduct.rid_symm_apply,
      LinearMap.lTensor_tmul, TensorProduct.lid'_apply_tmul]
    simpa [g, Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem] using hx
  change e.symm x ∈ LinearMap.ker
    (TensorProduct.AlgebraTensorModule.lTensor B B g) at hyker
  rw [Module.Flat.ker_lTensor_eq, hker] at hyker
  have hyideal : e.symm x ∈
      Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] B ⊗[R] R) I := by
    change e.symm x ∈ (Ideal.map
      (Algebra.TensorProduct.includeRight : R →ₐ[R] B ⊗[R] R) I).restrictScalars R
    rw [Ideal.map_includeRight_eq]
    exact hyker
  have hmap : e (e.symm x) ∈
      Ideal.map e.toRingEquiv.toRingHom
        (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] B ⊗[R] R) I) :=
    Ideal.mem_map_of_mem e.toRingEquiv.toRingHom hyideal
  have hcomp : e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : R →ₐ[R] B ⊗[R] R).toRingHom =
        algebraMap R B := by
    ext r
    simp [e, Algebra.smul_def]
  have himage : Ideal.map e.toRingEquiv.toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[R] B ⊗[R] R) I) =
      Ideal.map (algebraMap R B) I := by
    calc
      _ = Ideal.map (e.toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight : R →ₐ[R] B ⊗[R] R).toRingHom) I :=
        Ideal.map_map _ _
      _ = Ideal.map (algebraMap R B) I := by rw [hcomp]
  rw [himage] at hmap
  simpa [I] using hmap

/-- Contract a height-one prime through an affine open immersion of Dedekind spectra. -/
def underHeightOneOpenImmersion
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B]
    [Algebra R B]
    [IsOpenImmersion (CommonExtension.extensionMap R B)]
    (q : HeightOneSpectrum B) : HeightOneSpectrum R where
  asIdeal := q.asIdeal.comap (algebraMap R B)
  isPrime := Ideal.IsPrime.comap (algebraMap R B)
  ne_bot := by
    letI := algebraIsEpiOfOpenImmersion R B
    letI := moduleFlatOfOpenImmersion R B
    intro hbot
    have hmap := idealMapComapEqOfFlatEpi R B q.asIdeal
    rw [hbot] at hmap
    exact q.ne_bot (by simpa using hmap.symm)

/-- A surviving height-one prime extends exactly to the prime above it through an affine open
immersion. This is the open-immersion replacement for `IsLocalization.map_under`. -/
lemma map_underHeightOneOpenImmersion
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B]
    [Algebra R B]
    [IsOpenImmersion (CommonExtension.extensionMap R B)]
    (q : HeightOneSpectrum B) :
    Ideal.map (algebraMap R B)
        (underHeightOneOpenImmersion R B q).asIdeal = q.asIdeal := by
  letI := algebraIsEpiOfOpenImmersion R B
  letI := moduleFlatOfOpenImmersion R B
  exact idealMapComapEqOfFlatEpi R B q.asIdeal

private lemma map_heightOne_eq_top_or_heightOne_of_isOpenImmersion
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B]
    [Algebra R B] [IsTorsionFree R B]
    [IsOpenImmersion (CommonExtension.extensionMap R B)]
    (v : HeightOneSpectrum R) :
    Ideal.map (algebraMap R B) v.asIdeal = ⊤ ∨
      ∃ w : HeightOneSpectrum B,
        Ideal.map (algebraMap R B) v.asIdeal = w.asIdeal := by
  letI := algebraIsEpiOfOpenImmersion R B
  letI := moduleFlatOfOpenImmersion R B
  let J := Ideal.map (algebraMap R B) v.asIdeal
  by_cases htop : J = ⊤
  · exact Or.inl htop
  · obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J htop
    have hvle : v.asIdeal ≤ Ideal.comap (algebraMap R B) M :=
      Ideal.map_le_iff_le_comap.mp hJM
    have hcomap : v.asIdeal = Ideal.comap (algebraMap R B) M :=
      v.isMaximal.eq_of_le (hM.isPrime.comap (algebraMap R B)).ne_top hvle
    have hmap : J = M := by
      change Ideal.map (algebraMap R B) v.asIdeal = M
      rw [hcomap]
      exact idealMapComapEqOfFlatEpi R B M
    let w : HeightOneSpectrum B :=
      { asIdeal := M
        isPrime := hM.isPrime
        ne_bot := by
          rw [← hmap]
          exact (Ideal.map_eq_bot_iff_of_injective
            (FaithfulSMul.algebraMap_injective R B)).not.mpr v.ne_bot }
    exact Or.inr ⟨w, hmap⟩

private lemma count_extended_prime_eq_of_isOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra R K] [IsFractionRing R K]
    [Algebra B K] [IsFractionRing B K]
    [IsOpenImmersion (CommonExtension.extensionMap R B)]
    (v : HeightOneSpectrum R) (q : HeightOneSpectrum B)
    (hvq : v = underHeightOneOpenImmersion R B q) :
    FractionalIdeal.count K q
        (FractionalIdeal.extendedHom K B
          (v.asIdeal : FractionalIdeal R⁰ K)) = 1 := by
  rw [FractionalIdeal.extendedHom_coeIdeal_eq_map]
  rw [hvq, map_underHeightOneOpenImmersion R B q]
  exact FractionalIdeal.count_self K q

private lemma count_extended_prime_ne_of_isOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra R K] [IsFractionRing R K]
    [Algebra B K] [IsFractionRing B K]
    [IsOpenImmersion (CommonExtension.extensionMap R B)]
    (v : HeightOneSpectrum R) (q : HeightOneSpectrum B)
    (hvq : v ≠ underHeightOneOpenImmersion R B q) :
    FractionalIdeal.count K q
        (FractionalIdeal.extendedHom K B
          (v.asIdeal : FractionalIdeal R⁰ K)) = 0 := by
  rw [FractionalIdeal.extendedHom_coeIdeal_eq_map]
  rcases map_heightOne_eq_top_or_heightOne_of_isOpenImmersion R B v with
    htop | ⟨w, hw⟩
  · rw [htop]
    exact FractionalIdeal.count_one K q
  · rw [hw]
    apply FractionalIdeal.count_maximal_coprime K q
    intro hwq
    apply hvq
    apply HeightOneSpectrum.ext
    apply v.isMaximal.eq_of_le
    · exact (underHeightOneOpenImmersion R B q).isPrime.ne_top
    · change v.asIdeal ≤ q.asIdeal.comap (algebraMap R B)
      apply Ideal.le_comap_of_map_le
      rw [hw, hwq]

/-- Coefficients of two chart divisors agree after contracting every height-one prime through
affine open immersions from a common Dedekind overlap. -/
def OpenImmersionCoefficientEq
    (R₁ R₂ B : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDedekindDomain B]
    [Algebra R₁ B] [Algebra R₂ B]
    [IsOpenImmersion (CommonExtension.extensionMap R₁ B)]
    [IsOpenImmersion (CommonExtension.extensionMap R₂ B)]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂)) : Prop :=
  ∀ q : HeightOneSpectrum B,
    coeff D₁ (underHeightOneOpenImmersion R₁ B q) =
      coeff D₂ (underHeightOneOpenImmersion R₂ B q)

private lemma count_extended_divisorFractionalIdeal_of_isOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra R K] [IsFractionRing R K]
    [Algebra B K] [IsFractionRing B K]
    [IsOpenImmersion (CommonExtension.extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) (q : HeightOneSpectrum B) :
    FractionalIdeal.count K q
        (FractionalIdeal.extendedHom K B
          (ExplicitIdeal.divisorFractionalIdeal R K D : FractionalIdeal R⁰ K)) =
      coeff D (underHeightOneOpenImmersion R B q) := by
  classical
  let F : FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ K :=
    FractionalIdeal.extendedHom K B
  rw [divisorFractionalIdeal_coe_eq_prod R K D, map_finsuppProd]
  change FractionalIdeal.count K q
      (∏ v ∈ D.support, F ((v.asIdeal : FractionalIdeal R⁰ K) ^ D v)) = _
  rw [FractionalIdeal.count_prod]
  · simp_rw [map_zpow₀, FractionalIdeal.count_zpow]
    let p := underHeightOneOpenImmersion R B q
    by_cases hp : p ∈ D.support
    · rw [Finset.sum_eq_single p]
      · rw [count_extended_prime_eq_of_isOpenImmersion R B K p q rfl, mul_one]
        rfl
      · intro v hv hvp
        rw [count_extended_prime_ne_of_isOpenImmersion R B K v q hvp, mul_zero]
      · intro hpnot
        exact (hpnot hp).elim
    · rw [Finset.sum_eq_zero]
      · have hpzero : D p = 0 := by
          simpa [Finsupp.mem_support_iff] using hp
        exact (by simpa only [coeff] using hpzero.symm)
      · intro v hv
        have hvp : v ≠ p := by
          intro hvp
          exact hp (hvp ▸ hv)
        rw [count_extended_prime_ne_of_isOpenImmersion R B K v q hvp, mul_zero]
  · intro v hv
    exact (FractionalIdeal.extendedHom_eq_zero_iff K B).not.mpr
      (zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

/-- Equality of contracted coefficients through arbitrary affine open immersions proves the
cross-chart equality of extended inverse divisor ideals. -/
theorem overlapInverseIdealExtensionEq_of_openImmersion_coeff_eq
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [IsOpenImmersion (CommonExtension.extensionMap R₁ B)]
    [IsOpenImmersion (CommonExtension.extensionMap R₂ B)]
    (h₁ : IsScalarTower R₁ B K) (h₂ : IsScalarTower R₂ B K)
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (hcoeff : OpenImmersionCoefficientEq R₁ R₂ B D₁ D₂) :
    OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂ := by
  letI : IsScalarTower R₁ B K := h₁
  letI : IsScalarTower R₂ B K := h₂
  refine ⟨h₁, h₂, ?_⟩
  let F₁ : FractionalIdeal R₁⁰ K →+* FractionalIdeal B⁰ K :=
    FractionalIdeal.extendedHom K B
  let F₂ : FractionalIdeal R₂⁰ K →+* FractionalIdeal B⁰ K :=
    FractionalIdeal.extendedHom K B
  have hbase :
      Units.map F₁.toMonoidHom (ExplicitIdeal.divisorFractionalIdeal R₁ K D₁) =
        Units.map F₂.toMonoidHom (ExplicitIdeal.divisorFractionalIdeal R₂ K D₂) := by
    apply Units.ext
    have hadd :
        Additive.ofMul (Units.map F₁.toMonoidHom
            (ExplicitIdeal.divisorFractionalIdeal R₁ K D₁)) =
          Additive.ofMul (Units.map F₂.toMonoidHom
            (ExplicitIdeal.divisorFractionalIdeal R₂ K D₂)) := by
      apply (fractionalIdealDivisorAddEquiv B K).injective
      ext q
      rw [fractionalIdealDivisorAddEquiv_apply,
        fractionalIdealDivisorAddEquiv_apply,
        coeff_fractionalIdealDivisor, coeff_fractionalIdealDivisor]
      change FractionalIdeal.count K q
          (F₁ (ExplicitIdeal.divisorFractionalIdeal R₁ K D₁ :
            FractionalIdeal R₁⁰ K)) =
        FractionalIdeal.count K q
          (F₂ (ExplicitIdeal.divisorFractionalIdeal R₂ K D₂ :
            FractionalIdeal R₂⁰ K))
      rw [count_extended_divisorFractionalIdeal_of_isOpenImmersion R₁ B K D₁ q,
        count_extended_divisorFractionalIdeal_of_isOpenImmersion R₂ B K D₂ q]
      exact hcoeff q
    exact congrArg
      (fun I : Additive ((FractionalIdeal B⁰ K)ˣ) ↦
        ((Additive.toMul I : (FractionalIdeal B⁰ K)ˣ) : FractionalIdeal B⁰ K)) hadd
  simpa only [map_inv] using congrArg Inv.inv hbase

/-- Contract a height-one prime through an injective localization of Dedekind domains. -/
def underHeightOne
    (R B : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B]
    (M : Submonoid R) (hM : M ≤ R⁰)
    [Algebra R B] [IsLocalization M B]
    (q : HeightOneSpectrum B) : HeightOneSpectrum R where
  asIdeal := q.asIdeal.under R
  isPrime := IsLocalization.isPrime_iff_isPrime_disjoint M B q.asIdeal |>.mp q.isPrime |>.1
  ne_bot := ne_of_gt (IsLocalization.bot_lt_under_prime M B hM q.asIdeal q.ne_bot)

/-- Coefficients of two chart divisors agree after contracting every height-one prime of a
common ring that is a localization of both chart rings. -/
def LocalizationCoefficientEq
    (R₁ R₂ B : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B]
    [Algebra R₁ B] [Algebra R₂ B]
    (M₁ : Submonoid R₁) (hM₁ : M₁ ≤ R₁⁰) [IsLocalization M₁ B]
    (M₂ : Submonoid R₂) (hM₂ : M₂ ≤ R₂⁰) [IsLocalization M₂ B]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂)) : Prop :=
  ∀ q : HeightOneSpectrum B,
    coeff D₁ (underHeightOne R₁ B M₁ hM₁ q) =
      coeff D₂ (underHeightOne R₂ B M₂ hM₂ q)

private lemma count_extended_prime_eq
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra R K] [IsFractionRing R K]
    [Algebra B K] [IsFractionRing B K]
    (M : Submonoid R) (hM : M ≤ R⁰) [IsLocalization M B]
    (v : HeightOneSpectrum R) (q : HeightOneSpectrum B)
    (hvq : v = underHeightOne R B M hM q) :
    FractionalIdeal.count K q
        (FractionalIdeal.extendedHom K B
          (v.asIdeal : FractionalIdeal R⁰ K)) = 1 := by
  rw [FractionalIdeal.extendedHom_coeIdeal_eq_map]
  have hmap : Ideal.map (algebraMap R B) v.asIdeal = q.asIdeal := by
    rw [hvq]
    exact IsLocalization.map_under M B q.asIdeal
  rw [hmap]
  exact FractionalIdeal.count_self K q

private lemma count_extended_prime_ne
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra R K] [IsFractionRing R K]
    [Algebra B K] [IsFractionRing B K]
    (M : Submonoid R) (hM : M ≤ R⁰) [IsLocalization M B]
    (v : HeightOneSpectrum R) (q : HeightOneSpectrum B)
    (hvq : v ≠ underHeightOne R B M hM q) :
    FractionalIdeal.count K q
        (FractionalIdeal.extendedHom K B
          (v.asIdeal : FractionalIdeal R⁰ K)) = 0 := by
  rw [FractionalIdeal.extendedHom_coeIdeal_eq_map]
  by_cases hvM : Disjoint (M : Set R) (v.asIdeal : Set R)
  · have hmap0 : Ideal.map (algebraMap R B) v.asIdeal ≠ ⊥ := by
      intro hzero
      have hunder := IsLocalization.under_map_of_isPrime_disjoint M B v.isPrime hvM
      rw [hzero] at hunder
      exact v.ne_bot (by simpa using hunder.symm)
    let w : HeightOneSpectrum B :=
      { asIdeal := Ideal.map (algebraMap R B) v.asIdeal
        isPrime := IsLocalization.isPrime_of_isPrime_disjoint M B v.asIdeal v.isPrime hvM
        ne_bot := hmap0 }
    have hwq : w ≠ q := by
      intro hwq
      apply hvq
      apply HeightOneSpectrum.ext
      change v.asIdeal = q.asIdeal.under R
      have hunder := IsLocalization.under_map_of_isPrime_disjoint M B v.isPrime hvM
      change w.asIdeal.under R = v.asIdeal at hunder
      rw [hwq] at hunder
      exact hunder.symm
    change FractionalIdeal.count K q
        (w.asIdeal : FractionalIdeal B⁰ K) = 0
    exact FractionalIdeal.count_maximal_coprime K q hwq
  · have hsubset : ¬ (v.asIdeal : Set R) ⊆ (M : Set R)ᶜ := by
      intro h
      apply hvM
      rw [Set.disjoint_left]
      intro x hxM hxv
      exact (h hxv) hxM
    rw [IsLocalization.map_eq_top_of_not_subset M B hsubset]
    exact FractionalIdeal.count_one K q

private lemma count_extended_divisorFractionalIdeal
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra R K] [IsFractionRing R K]
    [Algebra B K] [IsFractionRing B K]
    (M : Submonoid R) (hM : M ≤ R⁰) [IsLocalization M B]
    (D : WeilDivisor (HeightOneSpectrum R)) (q : HeightOneSpectrum B) :
    FractionalIdeal.count K q
        (FractionalIdeal.extendedHom K B
          (ExplicitIdeal.divisorFractionalIdeal R K D : FractionalIdeal R⁰ K)) =
      coeff D (underHeightOne R B M hM q) := by
  classical
  let F : FractionalIdeal R⁰ K →+* FractionalIdeal B⁰ K :=
    FractionalIdeal.extendedHom K B
  rw [divisorFractionalIdeal_coe_eq_prod R K D, map_finsuppProd]
  change FractionalIdeal.count K q
      (∏ v ∈ D.support, F ((v.asIdeal : FractionalIdeal R⁰ K) ^ D v)) = _
  rw [FractionalIdeal.count_prod]
  · simp_rw [map_zpow₀, FractionalIdeal.count_zpow]
    let p := underHeightOne R B M hM q
    by_cases hp : p ∈ D.support
    · rw [Finset.sum_eq_single p]
      · rw [count_extended_prime_eq R B K M hM p q rfl, mul_one]
        rfl
      · intro v hv hvp
        rw [count_extended_prime_ne R B K M hM v q hvp, mul_zero]
      · intro hpnot
        exact (hpnot hp).elim
    · rw [Finset.sum_eq_zero]
      · have hpzero : D p = 0 := by
          simpa [Finsupp.mem_support_iff] using hp
        exact (by simpa only [coeff] using hpzero.symm)
      · intro v hv
        have hvp : v ≠ p := by
          intro hvp
          exact hp (hvp ▸ hv)
        rw [count_extended_prime_ne R B K M hM v q hvp, mul_zero]
  · intro v hv
    exact (FractionalIdeal.extendedHom_eq_zero_iff K B).not.mpr
      (zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

/-- Equality of divisor coefficients after contraction from a common localization proves the
cross-chart equality of extended inverse divisor ideals for arbitrary divisors. -/
theorem overlapInverseIdealExtensionEq_of_localization_coeff_eq
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    (M₁ : Submonoid R₁) (hM₁ : M₁ ≤ R₁⁰) [IsLocalization M₁ B]
    (M₂ : Submonoid R₂) (hM₂ : M₂ ≤ R₂⁰) [IsLocalization M₂ B]
    (h₁ : IsScalarTower R₁ B K) (h₂ : IsScalarTower R₂ B K)
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (hcoeff : LocalizationCoefficientEq R₁ R₂ B
      M₁ hM₁ M₂ hM₂ D₁ D₂) :
    OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂ := by
  letI : IsScalarTower R₁ B K := h₁
  letI : IsScalarTower R₂ B K := h₂
  refine ⟨h₁, h₂, ?_⟩
  let F₁ : FractionalIdeal R₁⁰ K →+* FractionalIdeal B⁰ K :=
    FractionalIdeal.extendedHom K B
  let F₂ : FractionalIdeal R₂⁰ K →+* FractionalIdeal B⁰ K :=
    FractionalIdeal.extendedHom K B
  have hbase :
      Units.map F₁.toMonoidHom (ExplicitIdeal.divisorFractionalIdeal R₁ K D₁) =
        Units.map F₂.toMonoidHom (ExplicitIdeal.divisorFractionalIdeal R₂ K D₂) := by
    apply Units.ext
    have hadd :
        Additive.ofMul (Units.map F₁.toMonoidHom
            (ExplicitIdeal.divisorFractionalIdeal R₁ K D₁)) =
          Additive.ofMul (Units.map F₂.toMonoidHom
            (ExplicitIdeal.divisorFractionalIdeal R₂ K D₂)) := by
      apply (fractionalIdealDivisorAddEquiv B K).injective
      ext q
      rw [fractionalIdealDivisorAddEquiv_apply,
        fractionalIdealDivisorAddEquiv_apply,
        coeff_fractionalIdealDivisor, coeff_fractionalIdealDivisor]
      change FractionalIdeal.count K q
          (F₁ (ExplicitIdeal.divisorFractionalIdeal R₁ K D₁ :
            FractionalIdeal R₁⁰ K)) =
        FractionalIdeal.count K q
          (F₂ (ExplicitIdeal.divisorFractionalIdeal R₂ K D₂ :
            FractionalIdeal R₂⁰ K))
      rw [count_extended_divisorFractionalIdeal R₁ B K M₁ hM₁ D₁ q,
        count_extended_divisorFractionalIdeal R₂ B K M₂ hM₂ D₂ q]
      exact hcoeff q
    exact congrArg (fun I : Additive ((FractionalIdeal B⁰ K)ˣ) ↦
      ((Additive.toMul I : (FractionalIdeal B⁰ K)ˣ) : FractionalIdeal B⁰ K)) hadd
  simpa only [map_inv] using congrArg Inv.inv hbase

private lemma extended_prime_eq_one_of_mem
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    (v : HeightOneSpectrum R) (hfv : f ∈ v.asIdeal) :
    FractionalIdeal.extendedHom K (Localization.Away f)
        (v.asIdeal : FractionalIdeal R⁰ K) = 1 := by
  rw [FractionalIdeal.extendedHom_coeIdeal_eq_map]
  have htop : Ideal.map (algebraMap R (Localization.Away f)) v.asIdeal = ⊤ := by
    apply IsLocalization.map_eq_top_of_not_subset (.powers f)
    intro hsubset
    exact (hsubset hfv) (by simp)
  rw [htop]
  rfl

/-- Divisors with equal coefficients at every height-one prime in `D(f)` have equal inverse
fractional ideals after extension to the compatible principal-open coordinate ring. -/
theorem overlapInverseIdealExtensionEq_away_of_coeff_eq
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K]
    (D E : WeilDivisor (HeightOneSpectrum R))
    (hcoeff : ∀ v : HeightOneSpectrum R,
      f ∉ v.asIdeal → coeff D v = coeff E v) :
    OverlapInverseIdealExtensionEq R R (Localization.Away f) K D E := by
  classical
  have hf : f ≠ 0 := by
    intro hf
    have hu := IsLocalization.map_units (Localization.Away f)
      (⟨f, by simp⟩ : Submonoid.powers f)
    apply (IsUnit.ne_zero hu)
    rw [hf, map_zero]
  letI : IsDedekindDomain (Localization.Away f) :=
    IsLocalization.isDedekindDomain R (M := .powers f)
      (fun x hx => mem_nonZeroDivisors_iff_ne_zero.mpr
        (by rcases hx with ⟨n, rfl⟩; exact pow_ne_zero n hf))
      (Localization.Away f)
  refine ⟨inferInstance, inferInstance, ?_⟩
  let F : FractionalIdeal R⁰ K →+*
      FractionalIdeal (Localization.Away f)⁰ K :=
    FractionalIdeal.extendedHom K (Localization.Away f)
  have hbase :
      Units.map F.toMonoidHom (ExplicitIdeal.divisorFractionalIdeal R K D) =
        Units.map F.toMonoidHom (ExplicitIdeal.divisorFractionalIdeal R K E) := by
    apply Units.ext
    change F (ExplicitIdeal.divisorFractionalIdeal R K D : FractionalIdeal R⁰ K) =
      F (ExplicitIdeal.divisorFractionalIdeal R K E : FractionalIdeal R⁰ K)
    rw [divisorFractionalIdeal_coe_eq_prod R K D,
      divisorFractionalIdeal_coe_eq_prod R K E,
      map_finsuppProd, map_finsuppProd]
    apply Finsupp.prod_congr_of_eq_on_union
    · intro v hv
      by_cases hfv : f ∈ v.asIdeal
      · have hvone : F (v.asIdeal : FractionalIdeal R⁰ K) = 1 := by
          simpa [F] using extended_prime_eq_one_of_mem R K f v hfv
        simp [map_zpow₀, hvone]
      · rw [show D v = E v by simpa only [coeff] using hcoeff v hfv]
    · intro v hv
      simp
    · intro v hv
      simp
  simpa only [map_inv] using congrArg Inv.inv hbase

/-- Equality after common-field extension to a principal open implies equality of the abstract
localized inverse-ideal submodules. -/
theorem inverseIdealLocalizationEq_of_overlapExtensionEq_away
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K]
    (D E : WeilDivisor (HeightOneSpectrum R))
    (h : OverlapInverseIdealExtensionEq
      R R (Localization.Away f) K D E) :
    InverseIdealLocalizationEq R K D E f := by
  apply (Submodule.map_injective_of_injective
    (CommonExtension.localizedFractionEquiv R K f).injective)
  rw [CommonExtension.map_localized_inverseIdeal_eq_extended R K f D,
    CommonExtension.map_localized_inverseIdeal_eq_extended R K f E]
  exact congrArg
    (fun I : (FractionalIdeal (Localization.Away f)⁰ K)ˣ =>
      (I : Submodule (Localization.Away f) K)) h.2.2

/-- Same-chart divisors whose coefficients agree on `D(f)` have equal inverse ideals after
localization at `f`. This also covers the degenerate localization at `f = 0`. -/
theorem inverseIdealLocalizationEq_of_coeff_eq_away
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D E : WeilDivisor (HeightOneSpectrum R)) (f : R)
    (hcoeff : ∀ v : HeightOneSpectrum R,
      f ∉ v.asIdeal → coeff D v = coeff E v) :
    InverseIdealLocalizationEq R K D E f := by
  by_cases hf : f = 0
  · subst f
    have htop : ∀ T : Submodule R (FractionRing R),
        T.localized (.powers (0 : R)) = ⊤ := by
      intro T
      rw [← top_le_iff]
      intro x hx
      obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective
        (.powers (0 : R))
        (_root_.LocalizedModule.mkLinearMap
          (.powers (0 : R)) (FractionRing R)) x
      refine ⟨0, T.zero_mem, ⟨0, by simp⟩, ?_⟩
      change IsLocalizedModule.mk'
          (_root_.LocalizedModule.mkLinearMap
            (.powers (0 : R)) (FractionRing R))
          0 ⟨0, by simp⟩ =
        IsLocalizedModule.mk'
          (_root_.LocalizedModule.mkLinearMap
            (.powers (0 : R)) (FractionRing R))
          m s
      rw [IsLocalizedModule.mk'_eq_mk'_iff]
      exact ⟨1, by simp⟩
    unfold InverseIdealLocalizationEq
    rw [htop, htop]
  · letI : IsDomain (Localization.Away f) :=
      Localization.Away.isDomain hf
    let hunit : ∀ y : Submonoid.powers f,
        IsUnit ((algebraMap R K) (y : R)) := by
      rintro ⟨y, hy⟩
      apply isUnit_iff_ne_zero.mpr
      change algebraMap R K y ≠ 0
      apply (map_ne_zero_iff (algebraMap R K)
        (FaithfulSMul.algebraMap_injective R K)).2
      rcases hy with ⟨n, rfl⟩
      exact pow_ne_zero n hf
    letI : Algebra (Localization.Away f) K :=
      (IsLocalization.lift hunit).toAlgebra
    letI : IsScalarTower R (Localization.Away f) K :=
      IsScalarTower.of_algebraMap_eq fun x =>
        (IsLocalization.lift_eq hunit x).symm
    letI : IsFractionRing (Localization.Away f) K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
        (.powers f) (Localization.Away f) K
    exact inverseIdealLocalizationEq_of_overlapExtensionEq_away R K f D E
      (overlapInverseIdealExtensionEq_away_of_coeff_eq R K f D E hcoeff)

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Chain

/-- Pairwise same-chart coefficient agreement on a principal open supplies the corresponding
chosen line-bundle restriction isomorphism. This is the pairwise input toward a divisor descent
cocycle; cross-chart comparison and triple-overlap coherence remain separate requirements. -/
noncomputable def chosenTildeRestrictIsoOfCoeffEq
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (D E : WeilDivisor (HeightOneSpectrum R)) (f : R)
    (hcoeff : ∀ v : HeightOneSpectrum R,
      f ∉ v.asIdeal → coeff D v = coeff E v) :
    (AffineDedekind.lineBundle R K D).obj.restrict
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) ≅
      (AffineDedekind.lineBundle R K E).obj.restrict
        (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
  chosenTildeRestrictIsoOfInverseIdealEq R K D E f
    (Boundary.inverseIdealLocalizationEq_of_coeff_eq_away
      R K D E f hcoeff)

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Chain

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary

/-- Equality of the explicit inverse ideals after abstract module localization gives the
same-chart overlap-extension equality inside a compatible common fraction field. -/
theorem overlapInverseIdealExtensionEq_away
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K]
    (D E : WeilDivisor (HeightOneSpectrum R))
    (h : InverseIdealLocalizationEq R K D E f) :
    OverlapInverseIdealExtensionEq
      R R (Localization.Away f) K D E := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  change CommonExtension.extendedInverseIdeal R (Localization.Away f) K D =
    CommonExtension.extendedInverseIdeal R (Localization.Away f) K E
  rw [← CommonExtension.map_localized_inverseIdeal_eq_extended R K f D,
    ← CommonExtension.map_localized_inverseIdeal_eq_extended R K f E, h]

/-- On a compatible nonempty principal open, abstract module-localization equality is exactly
equality of the corresponding inverse ideals after extension inside the common fraction field. -/
theorem inverseIdealLocalizationEq_iff_overlapExtensionEq_away
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    InverseIdealLocalizationEq R K D E f ↔
      OverlapInverseIdealExtensionEq
        R R (Localization.Away f) K D E :=
  ⟨overlapInverseIdealExtensionEq_away R K f D E,
    inverseIdealLocalizationEq_of_overlapExtensionEq_away R K f D E⟩

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.Boundary

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension

/-- Same-chart localized inverse-ideal equality directly produces an isomorphism between the
chosen line-bundle restrictions on the corresponding nonempty principal open. -/
noncomputable def chosenLineBundleRestrictionIsoAwayOfLocalizationEq
    (R K : Type u) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) [IsDomain (Localization.Away f)]
    [Algebra (Localization.Away f) K]
    [IsFractionRing (Localization.Away f) K]
    [IsScalarTower R (Localization.Away f) K]
    (D E : WeilDivisor (HeightOneSpectrum R))
    (h : Boundary.InverseIdealLocalizationEq R K D E f) :
    (AffineDedekind.lineBundle R K D).obj.restrict
        (extensionMap R (Localization.Away f)) ≅
      (AffineDedekind.lineBundle R K E).obj.restrict
        (extensionMap R (Localization.Away f)) :=
  chosenLineBundleRestrictionIsoAway R K f D E
    (Boundary.overlapInverseIdealExtensionEq_away R K f D E h)

/-- Contracted coefficient compatibility through two arbitrary affine open immersions produces
an isomorphism of the actual chosen restrictions. The open-immersion prime-extension theorem
supplies equality of the extended inverse ideals, and affine-open base change supplies both
restriction comparisons. -/
noncomputable def chosenLineBundleRestrictionIsoOfOpenImmersionCoeffEq
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₁ B)]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₂ B)]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h₁ : IsScalarTower R₁ B K) (h₂ : IsScalarTower R₂ B K)
    (hcoeff : Boundary.OpenImmersionCoefficientEq R₁ R₂ B D₁ D₂) :
    (AffineDedekind.lineBundle R₁ K D₁).obj.restrict (extensionMap R₁ B) ≅
      (AffineDedekind.lineBundle R₂ K D₂).obj.restrict (extensionMap R₂ B) :=
  chosenLineBundleRestrictionIsoOfOverlapExtensionEq R₁ R₂ B K D₁ D₂
    (Boundary.overlapInverseIdealExtensionEq_of_openImmersion_coeff_eq
      R₁ R₂ B K h₁ h₂ D₁ D₂ hcoeff)

/-- Contracted coefficient compatibility on a common Dedekind localization produces an
isomorphism of the actual chosen restrictions. Affine-open flat epimorphic base change supplies
the two restriction identifications; the localization hypotheses are used only to compare the
divisor coefficients and extended ideals. -/
noncomputable def chosenLineBundleRestrictionIsoOfLocalizationCoeffEq
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₁ B)]
    [_root_.AlgebraicGeometry.IsOpenImmersion (extensionMap R₂ B)]
    (M₁ : Submonoid R₁) (hM₁ : M₁ ≤ R₁⁰) [IsLocalization M₁ B]
    (M₂ : Submonoid R₂) (hM₂ : M₂ ≤ R₂⁰) [IsLocalization M₂ B]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h₁ : IsScalarTower R₁ B K) (h₂ : IsScalarTower R₂ B K)
    (hcoeff : Boundary.LocalizationCoefficientEq R₁ R₂ B
      M₁ hM₁ M₂ hM₂ D₁ D₂) :
    (AffineDedekind.lineBundle R₁ K D₁).obj.restrict (extensionMap R₁ B) ≅
      (AffineDedekind.lineBundle R₂ K D₂).obj.restrict (extensionMap R₂ B) := by
  exact chosenLineBundleRestrictionIsoOfOverlapExtensionEq R₁ R₂ B K D₁ D₂
    (Boundary.overlapInverseIdealExtensionEq_of_localization_coeff_eq
      R₁ R₂ B K M₁ hM₁ M₂ hM₂ h₁ h₂ D₁ D₂ hcoeff)

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension
