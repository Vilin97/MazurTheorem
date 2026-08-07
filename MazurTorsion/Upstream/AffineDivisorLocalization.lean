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
data canonically from a chosen common Dedekind affine subopen. On one fixed common affine model,
the three specified restriction isomorphisms now satisfy the exact transitivity equation.
Inverse-ideal extension is also compatible with a further scalar-tower base change.  The
companion curve modules use this to identify pairwise-derived comparisons with direct
triple-affine comparisons.  The surrounding affine-tilde pullback isomorphisms are compatible
with composition as well, providing the coherence input for the companion transition module.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization

open CategoryTheory
open _root_.AlgebraicGeometry
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped ChangeOfRings nonZeroDivisors TensorProduct

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

private noncomputable def gammaPushforwardIsoRestrictScalarsCompPathRaw
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    Scheme.Modules.pushforward (Spec.map g ≫ Spec.map f) ⋙
        moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := C) ⋙
        ModuleCat.restrictScalars (f ≫ g).hom :=
  Functor.isoWhiskerRight
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f)).symm
      (moduleSpecΓFunctor (R := A)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward (Spec.map g))
      (gammaPushforwardIsoRestrictScalars A B f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (gammaPushforwardIsoRestrictScalars B C g)
      (ModuleCat.restrictScalars f.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := C))
      (ModuleCat.restrictScalarsComp f.hom g.hom).symm

private theorem gammaPushforwardIsoRestrictScalars_comp
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    gammaPushforwardIsoRestrictScalarsCompPathRaw A B C f g =
      Functor.isoWhiskerRight
          (Scheme.Modules.pushforwardCongr
            (show Spec.map g ≫ Spec.map f = Spec.map (f ≫ g) from
              (@Spec.map_comp A B C f g).symm))
          (moduleSpecΓFunctor (R := A)) ≪≫
        gammaPushforwardIsoRestrictScalars A C (f ≫ g) := by
  apply Iso.ext
  ext M x
  rfl

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

private noncomputable def tildePullbackAdjunctionCompRaw
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map g ≫ Spec.map f) ⊣
      Scheme.Modules.pushforward (Spec.map g ≫ Spec.map f) ⋙
        moduleSpecΓFunctor (R := A) :=
  (tilde.adjunction (R := A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g ≫ Spec.map f))

private noncomputable def extendScalarsTildeIsoPullback
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    ModuleCat.extendScalars f.hom ⋙ tilde.functor B ≅
      tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map f) :=
  (conjugateIsoEquiv (tildePullbackAdjunction A B f)
    (extendTildeAdjunction A B f)).symm
      (gammaPushforwardIsoRestrictScalars A B f)

private lemma conjugateEquiv_extendScalarsComp_hom
    {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) :
    conjugateEquiv
        ((ModuleCat.extendRestrictScalarsAdj f₁₂).comp
          (ModuleCat.extendRestrictScalarsAdj f₂₃))
        (ModuleCat.extendRestrictScalarsAdj (f₂₃.comp f₁₂))
        (ModuleCat.extendScalarsComp f₁₂ f₂₃).hom =
      (ModuleCat.restrictScalarsComp f₁₂ f₂₃).inv := by
  rw [← conjugateIsoEquiv_apply_hom]
  exact congrArg Iso.hom <|
    (conjugateIsoEquiv
      ((ModuleCat.extendRestrictScalarsAdj f₁₂).comp
        (ModuleCat.extendRestrictScalarsAdj f₂₃))
      (ModuleCat.extendRestrictScalarsAdj (f₂₃.comp f₁₂))).apply_symm_apply _

private lemma conjugateEquiv_extendScalarsTildeIsoPullback_hom
    (A B : CommRingCat.{u}) (f : A ⟶ B) :
    conjugateEquiv (tildePullbackAdjunction A B f)
        (extendTildeAdjunction A B f)
        (extendScalarsTildeIsoPullback A B f).hom =
      (gammaPushforwardIsoRestrictScalars A B f).hom := by
  rw [← conjugateIsoEquiv_apply_hom]
  exact congrArg Iso.hom <|
    (conjugateIsoEquiv (tildePullbackAdjunction A B f)
      (extendTildeAdjunction A B f)).apply_symm_apply _

private lemma conjugateEquiv_pullbackComp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
        ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
          (Scheme.Modules.pullbackPushforwardAdjunction f))
        (Scheme.Modules.pullbackComp f g).hom =
      (Scheme.Modules.pushforwardComp f g).inv := by
  apply (cancel_mono (Scheme.Modules.pushforwardComp f g).hom).mp
  rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_comp, Iso.inv_hom_id, conjugateEquiv_id,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv, Iso.inv_hom_id]

private lemma conjugateEquiv_pullbackCongr_hom
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction g)
        (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackCongr h).hom =
      (Scheme.Modules.pushforwardCongr h).inv := by
  cases h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    conjugateEquiv_id]
  ext M U x
  rw [Scheme.Modules.pushforwardCongr_inv_app_app]
  simp

private lemma pushforwardCongr_symm_hom
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pushforwardCongr h.symm).hom =
      (Scheme.Modules.pushforwardCongr h).inv := by
  cases h
  ext M U x
  rw [Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforwardCongr_inv_app_app]

private lemma conjugateEquiv_comp_seven
    {C D : Type*} [Category C] [Category D]
    {L₀ L₁ L₂ L₃ L₄ L₅ L₆ L₇ : C ⥤ D}
    {R₀ R₁ R₂ R₃ R₄ R₅ R₆ R₇ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄) (a₅ : L₅ ⊣ R₅)
    (a₆ : L₆ ⊣ R₆) (a₇ : L₇ ⊣ R₇)
    (s₀ : L₀ ⟶ L₁) (s₁ : L₁ ⟶ L₂) (s₂ : L₂ ⟶ L₃)
    (s₃ : L₃ ⟶ L₄) (s₄ : L₄ ⟶ L₅) (s₅ : L₅ ⟶ L₆)
    (s₆ : L₆ ⟶ L₇) :
    conjugateEquiv a₇ a₀ (s₀ ≫ s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ s₅ ≫ s₆) =
      conjugateEquiv a₇ a₆ s₆ ≫ conjugateEquiv a₆ a₅ s₅ ≫
        conjugateEquiv a₅ a₄ s₄ ≫ conjugateEquiv a₄ a₃ s₃ ≫
          conjugateEquiv a₃ a₂ s₂ ≫ conjugateEquiv a₂ a₁ s₁ ≫
            conjugateEquiv a₁ a₀ s₀ := by
  rw [← conjugateEquiv_comp a₇ a₁ a₀ (s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ s₅ ≫ s₆) s₀,
    ← conjugateEquiv_comp a₇ a₂ a₁ (s₂ ≫ s₃ ≫ s₄ ≫ s₅ ≫ s₆) s₁,
    ← conjugateEquiv_comp a₇ a₃ a₂ (s₃ ≫ s₄ ≫ s₅ ≫ s₆) s₂,
    ← conjugateEquiv_comp a₇ a₄ a₃ (s₄ ≫ s₅ ≫ s₆) s₃,
    ← conjugateEquiv_comp a₇ a₅ a₄ (s₅ ≫ s₆) s₄,
    ← conjugateEquiv_comp a₇ a₆ a₅ s₆ s₅]
  simp only [Category.assoc]

private lemma conjugateEquiv_comp_two
    {C D : Type*} [Category C] [Category D]
    {L₀ L₁ L₂ : C ⥤ D} {R₀ R₁ R₂ : D ⥤ C}
    (a₀ : L₀ ⊣ R₀) (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (s₀ : L₀ ⟶ L₁) (s₁ : L₁ ⟶ L₂) :
    conjugateEquiv a₂ a₀ (s₀ ≫ s₁) =
      conjugateEquiv a₂ a₁ s₁ ≫ conjugateEquiv a₁ a₀ s₀ := by
  exact (conjugateEquiv_comp a₂ a₁ a₀ s₁ s₀).symm

private lemma conjugateEquiv_associator_inv
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A}
    {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C}
    (a₀₁ : L₀₁ ⊣ R₁₀) (a₁₂ : L₁₂ ⊣ R₂₁)
    (a₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((a₀₁.comp a₁₂).comp a₂₃)
        (a₀₁.comp (a₁₂.comp a₂₃))
        (Functor.associator L₀₁ L₁₂ L₂₃).inv =
      (Functor.associator R₃₂ R₂₁ R₁₀).inv := by
  apply (cancel_mono (Functor.associator R₃₂ R₂₁ R₁₀).hom).mp
  rw [← conjugateEquiv_associator_hom a₀₁ a₁₂ a₂₃,
    conjugateEquiv_comp, Iso.hom_inv_id, conjugateEquiv_id,
    conjugateEquiv_associator_hom a₀₁ a₁₂ a₂₃,
    Iso.inv_hom_id]

private noncomputable def extendScalarsTildeIsoPullbackCompPathRaw
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    ModuleCat.extendScalars (f ≫ g).hom ⋙ tilde.functor C ≅
      tilde.functor A ⋙
        Scheme.Modules.pullback (Spec.map g ≫ Spec.map f) :=
  Functor.isoWhiskerRight (ModuleCat.extendScalarsComp f.hom g.hom)
      (tilde.functor C) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom)
      (extendScalarsTildeIsoPullback B C g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extendScalarsTildeIsoPullback A B f)
      (Scheme.Modules.pullback (Spec.map g)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tilde.functor A)
      (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f))

private theorem extendScalarsTildeIsoPullback_comp
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) :
    extendScalarsTildeIsoPullbackCompPathRaw A B C f g =
      extendScalarsTildeIsoPullback A C (f ≫ g) ≪≫
        Functor.isoWhiskerLeft (tilde.functor A)
          (Scheme.Modules.pullbackCongr
            (show Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f from
              @Spec.map_comp A B C f g)) := by
  let e_f := ModuleCat.extendRestrictScalarsAdj f.hom
  let e_g := ModuleCat.extendRestrictScalarsAdj g.hom
  let e_fg := ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom
  let tA := tilde.adjunction (R := A)
  let tB := tilde.adjunction (R := B)
  let tC := tilde.adjunction (R := C)
  let p_f := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)
  let p_g := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)
  let p_fg := Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map g ≫ Spec.map f)
  let p_d := Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g))
  let a₀ := e_fg.comp tC
  let a₁ := (e_f.comp e_g).comp tC
  let a₂ := e_f.comp (e_g.comp tC)
  let a₃ := e_f.comp (tB.comp p_g)
  let a₄ := (e_f.comp tB).comp p_g
  let a₅ := (tA.comp p_f).comp p_g
  let a₆ := tA.comp (p_f.comp p_g)
  let a₇ := tA.comp p_fg
  let a_d := tA.comp p_d
  let s₀ := (Functor.isoWhiskerRight
    (ModuleCat.extendScalarsComp f.hom g.hom) (tilde.functor C)).hom
  let s₁ := (Functor.associator (ModuleCat.extendScalars f.hom)
    (ModuleCat.extendScalars g.hom) (tilde.functor C)).hom
  let s₂ := (Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom)
    (extendScalarsTildeIsoPullback B C g)).hom
  let s₃ := (Functor.associator (ModuleCat.extendScalars f.hom)
    (tilde.functor B) (Scheme.Modules.pullback (Spec.map g))).inv
  let s₄ := (Functor.isoWhiskerRight
    (extendScalarsTildeIsoPullback A B f)
    (Scheme.Modules.pullback (Spec.map g))).hom
  let s₅ := (Functor.associator (tilde.functor A)
    (Scheme.Modules.pullback (Spec.map f))
    (Scheme.Modules.pullback (Spec.map g))).hom
  let s₆ := (Functor.isoWhiskerLeft (tilde.functor A)
    (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f))).hom
  let r₀ := (extendScalarsTildeIsoPullback A C (f ≫ g)).hom
  let r₁ := (Functor.isoWhiskerLeft (tilde.functor A)
    (Scheme.Modules.pullbackCongr
      (show Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f from
        @Spec.map_comp A B C f g))).hom
  apply (conjugateIsoEquiv a₇ a₀).injective
  apply Iso.ext
  simp only [conjugateIsoEquiv_apply_hom, Iso.trans_hom]
  change conjugateEquiv a₇ a₀ (s₀ ≫ s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ s₅ ≫ s₆) =
    conjugateEquiv a₇ a₀ (r₀ ≫ r₁)
  rw [conjugateEquiv_comp_seven a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇
      s₀ s₁ s₂ s₃ s₄ s₅ s₆,
    conjugateEquiv_comp_two a₀ a_d a₇ r₀ r₁]
  dsimp only [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇, a_d,
    s₀, s₁, s₂, s₃, s₄, s₅, s₆, r₀, r₁]
  simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  have hE_f := conjugateEquiv_extendScalarsTildeIsoPullback_hom A B f
  change conjugateEquiv (tA.comp p_f) (e_f.comp tB)
    (extendScalarsTildeIsoPullback A B f).hom =
      (gammaPushforwardIsoRestrictScalars A B f).hom at hE_f
  have hE_g := conjugateEquiv_extendScalarsTildeIsoPullback_hom B C g
  change conjugateEquiv (tB.comp p_g) (e_g.comp tC)
    (extendScalarsTildeIsoPullback B C g).hom =
      (gammaPushforwardIsoRestrictScalars B C g).hom at hE_g
  have hE_fg := conjugateEquiv_extendScalarsTildeIsoPullback_hom A C (f ≫ g)
  change conjugateEquiv (tA.comp p_d) (e_fg.comp tC)
    (extendScalarsTildeIsoPullback A C (f ≫ g)).hom =
      (gammaPushforwardIsoRestrictScalars A C (f ≫ g)).hom at hE_fg
  have hext := conjugateEquiv_extendScalarsComp_hom f.hom g.hom
  change conjugateEquiv (e_f.comp e_g) e_fg
    (ModuleCat.extendScalarsComp f.hom g.hom).hom =
      (ModuleCat.restrictScalarsComp f.hom g.hom).inv at hext
  rw [conjugateEquiv_whiskerLeft p_fg (p_f.comp p_g) tA,
    conjugateEquiv_pullbackComp_hom,
    conjugateEquiv_associator_hom tA p_f p_g,
    conjugateEquiv_whiskerRight
      (tA.comp p_f) (e_f.comp tB) p_g,
    hE_f,
    conjugateEquiv_associator_inv e_f tB p_g,
    conjugateEquiv_whiskerLeft
      (tB.comp p_g) (e_g.comp tC) e_f,
    hE_g,
    conjugateEquiv_associator_hom e_f e_g tC,
    conjugateEquiv_whiskerRight (e_f.comp e_g) e_fg tC,
    hext,
    conjugateEquiv_whiskerLeft
      p_fg p_d tA,
    conjugateEquiv_pullbackCongr_hom,
    hE_fg]
  rw [← pushforwardCongr_symm_hom (@Spec.map_comp A B C f g)]
  simpa only [gammaPushforwardIsoRestrictScalarsCompPathRaw, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom] using
      congrArg Iso.hom (gammaPushforwardIsoRestrictScalars_comp A B C f g)

private theorem extendScalarsTildeIsoPullback_comp_inv_app
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C)
    (M : ModuleCat A) :
    (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).inv.app
          ((tilde.functor A).obj M) ≫
        (Scheme.Modules.pullback (Spec.map g)).map
          ((extendScalarsTildeIsoPullback A B f).inv.app M) ≫
        (extendScalarsTildeIsoPullback B C g).inv.app
          ((ModuleCat.extendScalars f.hom).obj M) ≫
        (tilde.functor C).map
          ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) =
      (Scheme.Modules.pullbackCongr
          (show Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f from
            @Spec.map_comp A B C f g)).inv.app ((tilde.functor A).obj M) ≫
        (extendScalarsTildeIsoPullback A C (f ≫ g)).inv.app M := by
  have h := congrArg (fun e ↦ e.inv.app M)
    (extendScalarsTildeIsoPullback_comp A B C f g)
  simp only [extendScalarsTildeIsoPullbackCompPathRaw, Iso.trans_inv,
    CategoryTheory.NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_inv, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.comp_id] at h
  exact h

private theorem extendScalarsTildeIsoPullback_congr
    (A B : CommRingCat.{u}) {f g : A ⟶ B} (h : f = g)
    (M : ModuleCat A) :
    (tilde.functor B).map
          (eqToIso (congrArg
            (fun k : A ⟶ B ↦ (ModuleCat.extendScalars k.hom).obj M) h)).hom ≫
        (extendScalarsTildeIsoPullback A B g).hom.app M =
      (extendScalarsTildeIsoPullback A B f).hom.app M ≫
        (Scheme.Modules.pullbackCongr (congrArg Spec.map h)).hom.app
          ((tilde.functor A).obj M) := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, Scheme.Modules.pullbackCongr]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app,
    Category.id_comp]
  exact (Category.comp_id _).symm

private theorem extendScalarsTildeIsoPullback_congr_inv
    (A B : CommRingCat.{u}) {f g : A ⟶ B} (h : f = g)
    (M : ModuleCat A) :
    (Scheme.Modules.pullbackCongr (congrArg Spec.map h)).inv.app
          ((tilde.functor A).obj M) ≫
        (extendScalarsTildeIsoPullback A B f).inv.app M =
      (extendScalarsTildeIsoPullback A B g).inv.app M ≫
        (tilde.functor B).map
          (eqToIso (congrArg
            (fun k : A ⟶ B ↦ (ModuleCat.extendScalars k.hom).obj M) h)).inv := by
  subst g
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv,
    CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app]
  rw [Category.id_comp]
  exact (Category.comp_id _).symm

private theorem pullbackCongr_hom_comp_inv
    {X Y : Scheme.{u}} {f g h : X ⟶ Y}
    (hfg : f = g) (hfh : f = h) (hgh : g = h) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr hgh).hom.app M ≫
        (Scheme.Modules.pullbackCongr hfh).inv.app M =
      (Scheme.Modules.pullbackCongr hfg).inv.app M := by
  subst g
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    Iso.refl_inv, CategoryTheory.NatTrans.id_app, Category.id_comp]

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

/-- The extended inverse divisor ideal is the span, in the target fraction field, of the
original inverse divisor ideal.  This description is the input for tower compatibility of
inverse-ideal extension. -/
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

private lemma span_span_of_scalar_tower
    (B C K : Type u) [CommRing B] [CommRing C] [Field K]
    [Algebra B C] [Algebra B K] [Algebra C K] [IsScalarTower B C K]
    (s : Set K) :
    Submodule.span C (Submodule.span B s : Set K) = Submodule.span C s := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    refine Submodule.span_induction (p := fun x _ => x ∈ Submodule.span C s)
      (fun x hx => Submodule.subset_span hx) ?_ ?_ ?_ hx
    · exact (Submodule.span C s).zero_mem
    · intro x y _ _ hx hy
      exact (Submodule.span C s).add_mem hx hy
    · intro b x _ hx
      rw [← IsScalarTower.algebraMap_smul C b x]
      exact (Submodule.span C s).smul_mem (algebraMap B C b) hx
  · exact Submodule.span_mono Submodule.subset_span

/-- Extending an inverse divisor ideal first to `B` and then taking its `C`-span agrees with
extending it directly to `C`.  All three submodules live in the specified common fraction
field, so the statement records the scalar-tower compatibility needed on triple affine
intersections without choosing localization presentations. -/
theorem extendedInverseIdeal_span_tower
    (R B C K : Type u)
    [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    Submodule.span C (extendedInverseIdeal R B K D : Set K) =
      extendedInverseIdeal R C K D := by
  rw [extendedInverseIdeal_eq_span R B K D,
    extendedInverseIdeal_eq_span R C K D]
  exact span_span_of_scalar_tower B C K _

/-- A cross-chart inverse-ideal equality on `B` remains the same equality after extension to
`C`.  The scalar towers from the chart rings to `C` are derived from the given tower through
`B`; the equality itself is transported by the checked span-tower formula above.  This is the
algebraic restriction law needed to compare pairwise and triple affine overlap models. -/
theorem overlapInverseIdealExtensionEq_baseChange
    (R₁ R₂ B C K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R₁ C] [IsTorsionFree R₁ C]
    [Algebra R₂ C] [IsTorsionFree R₂ C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R₁ B C] [IsScalarTower R₂ B C]
    [IsScalarTower B C K]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    Boundary.OverlapInverseIdealExtensionEq R₁ R₂ C K D₁ D₂ := by
  letI : IsScalarTower R₁ B K := h.1
  letI : IsScalarTower R₂ B K := h.2.1
  let htower₁ : IsScalarTower R₁ C K := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro r
    change algebraMap R₁ K r = algebraMap C K (algebraMap R₁ C r)
    rw [IsScalarTower.algebraMap_apply R₁ B K,
      IsScalarTower.algebraMap_apply R₁ B C,
      IsScalarTower.algebraMap_apply B C K]
  let htower₂ : IsScalarTower R₂ C K := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro r
    change algebraMap R₂ K r = algebraMap C K (algebraMap R₂ C r)
    rw [IsScalarTower.algebraMap_apply R₂ B K,
      IsScalarTower.algebraMap_apply R₂ B C,
      IsScalarTower.algebraMap_apply B C K]
  letI : IsScalarTower R₁ C K := htower₁
  letI : IsScalarTower R₂ C K := htower₂
  refine ⟨htower₁, htower₂, ?_⟩
  have hB : extendedInverseIdeal R₁ B K D₁ =
      extendedInverseIdeal R₂ B K D₂ :=
    congrArg (fun I : (FractionalIdeal B⁰ K)ˣ ↦ (I : Submodule B K)) h.2.2
  have hC : extendedInverseIdeal R₁ C K D₁ =
      extendedInverseIdeal R₂ C K D₂ := by
    rw [← extendedInverseIdeal_span_tower R₁ B C K D₁,
      ← extendedInverseIdeal_span_tower R₂ B C K D₂, hB]
  apply Units.ext
  apply FractionalIdeal.coe_ext
  exact hC

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

/-- Extension of an inverse divisor ideal through a flat epimorphic scalar tower agrees with
the inverse divisor ideal obtained by extending directly to the top ring. -/
noncomputable def extendedInverseIdealBaseChangeEquiv
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    C ⊗[B] extendedInverseIdeal R B K D ≃ₗ[C]
      extendedInverseIdeal R C K D :=
  ((extendedInverseIdeal R B K D).tensorEquivSpan C).trans
    (LinearEquiv.ofEq _ _ (extendedInverseIdeal_span_tower R B C K D))

/-- The tower base-change equivalence is the evident multiplication map inside the common
fraction field. -/
lemma extendedInverseIdealBaseChangeEquiv_apply_tmul
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R)) (c : C)
    (x : extendedInverseIdeal R B K D) :
    ((extendedInverseIdealBaseChangeEquiv R B C K D) (c ⊗ₜ x) : K) =
      c • (x : K) := by
  rfl

/-- Equality-induced maps between two overlap inverse ideals commute with extension to a
further flat epimorphic overlap.  This is the module-level naturality square needed when a
pairwise overlap is pulled back to a triple overlap. -/
theorem extendedInverseIdealEquiv_baseChange
    (R₁ R₂ B C K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R₁ C] [IsTorsionFree R₁ C]
    [Algebra R₂ C] [IsTorsionFree R₂ C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R₁ B C] [IsScalarTower R₂ B C]
    [IsScalarTower B C K]
    [IsScalarTower R₁ B K] [IsScalarTower R₂ B K]
    [IsScalarTower R₁ C K] [IsScalarTower R₂ C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    let hC := overlapInverseIdealExtensionEq_baseChange R₁ R₂ B C K D₁ D₂ h
    ((extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ h).baseChange B C).trans
        (extendedInverseIdealBaseChangeEquiv R₂ B C K D₂) =
      (extendedInverseIdealBaseChangeEquiv R₁ B C K D₁).trans
        (extendedInverseIdealEquiv R₁ R₂ C K D₁ D₂ hC) := by
  let hC := overlapInverseIdealExtensionEq_baseChange R₁ R₂ B C K D₁ D₂ h
  dsimp only
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
      apply Subtype.ext
      simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
      change c • (x : K) = c • (x : K)
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

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

private lemma extendScalarsCarrierEquiv_apply_tmul
    (R B M N : Type u) [CommRing R] [CommRing B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N]
    [Algebra R B]
    (e : B ⊗[R] M ≃ₗ[B] N) (b : B) (m : M) :
    extendScalarsCarrierEquiv R B M N e (b ⊗ₜ[R] m) = e (b ⊗ₜ[R] m) := by
  change ((TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl B B) (LinearEquiv.refl R M)).trans e)
      (b ⊗ₜ[R] m) = e (b ⊗ₜ[R] m)
  simp

private noncomputable def extendedInverseIdealBaseChangeModuleEquiv
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (ModuleCat.extendScalars (algebraMap B C)).obj
        (ModuleCat.of B (extendedInverseIdeal R B K D)) ≃ₗ[C]
      extendedInverseIdeal R C K D :=
  extendScalarsCarrierEquiv B C _ _
    (extendedInverseIdealBaseChangeEquiv R B C K D)

private lemma extendedInverseIdealBaseChangeModuleEquiv_apply_one_tmul
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R))
    (x : extendedInverseIdeal R B K D) :
    ((extendedInverseIdealBaseChangeModuleEquiv R B C K D)
        ((1 : C) ⊗ₜ[B] x) : K) = (x : K) := by
  rw [show extendedInverseIdealBaseChangeModuleEquiv R B C K D =
      extendScalarsCarrierEquiv B C _ _
        (extendedInverseIdealBaseChangeEquiv R B C K D) from rfl]
  rw [extendScalarsCarrierEquiv_apply_tmul,
    extendedInverseIdealBaseChangeEquiv_apply_tmul, one_smul]

private theorem extendedInverseIdealEquiv_baseChange_module
    (R₁ R₂ B C K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R₁ C] [IsTorsionFree R₁ C]
    [Algebra R₂ C] [IsTorsionFree R₂ C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R₁ B C] [IsScalarTower R₂ B C]
    [IsScalarTower B C K]
    [IsScalarTower R₁ B K] [IsScalarTower R₂ B K]
    [IsScalarTower R₁ C K] [IsScalarTower R₂ C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    let hC := overlapInverseIdealExtensionEq_baseChange
      R₁ R₂ B C K D₁ D₂ h
    (ModuleCat.extendScalars (algebraMap B C)).map
          (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ h).toModuleIso.hom ≫
        (extendedInverseIdealBaseChangeModuleEquiv R₂ B C K D₂).toModuleIso.hom =
      (extendedInverseIdealBaseChangeModuleEquiv R₁ B C K D₁).toModuleIso.hom ≫
        (extendedInverseIdealEquiv R₁ R₂ C K D₁ D₂ hC).toModuleIso.hom := by
  let hC := overlapInverseIdealExtensionEq_baseChange
    R₁ R₂ B C K D₁ D₂ h
  dsimp only
  apply (ModuleCat.extendRestrictScalarsAdj (algebraMap B C)).homEquiv _ _ |>.injective
  ext x
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  change (extendedInverseIdealBaseChangeModuleEquiv R₂ B C K D₂
      ((1 : C) ⊗ₜ[B]
        (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ h x))) =
    extendedInverseIdealEquiv R₁ R₂ C K D₁ D₂ hC
      (extendedInverseIdealBaseChangeModuleEquiv R₁ B C K D₁
        ((1 : C) ⊗ₜ[B] x))
  apply Subtype.ext
  calc
    ((extendedInverseIdealBaseChangeModuleEquiv R₂ B C K D₂
        ((1 : C) ⊗ₜ[B]
          (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ h x))) : K) =
        (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ h x : K) :=
      extendedInverseIdealBaseChangeModuleEquiv_apply_one_tmul
        R₂ B C K D₂ _
    _ = (x : K) := rfl
    _ = ((extendedInverseIdealBaseChangeModuleEquiv R₁ B C K D₁
        ((1 : C) ⊗ₜ[B] x)) : K) :=
      (extendedInverseIdealBaseChangeModuleEquiv_apply_one_tmul
        R₁ B C K D₁ x).symm
    _ = (extendedInverseIdealEquiv R₁ R₂ C K D₁ D₂ hC
        (extendedInverseIdealBaseChangeModuleEquiv R₁ B C K D₁
          ((1 : C) ⊗ₜ[B] x)) : K) := rfl

private lemma chosenModuleBaseChangeEquivExtended_apply_one_tmul
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R))
    (m : AffineDedekind.lineBundleModule R K D) :
    ((chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D)
        ((1 : B) ⊗ₜ[R] m) : K) =
      (chosenModuleEquivOriginalInverseIdeal R K D m : K) := by
  rw [show chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D =
      extendScalarsCarrierEquiv R B
        (AffineDedekind.lineBundleModule R K D)
        (extendedInverseIdeal R B K D)
        (((chosenModuleEquivOriginalInverseIdeal R K D).baseChange R B).trans
          (originalInverseIdealBaseChangeEquivExtended_of_isOpenImmersion R B K D)) from rfl]
  rw [extendScalarsCarrierEquiv_apply_tmul]
  simp only [
    originalInverseIdealBaseChangeEquivExtended_of_isOpenImmersion,
    originalInverseIdealBaseChangeEquivExtended_of_flat_epi,
    LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  change (1 : B) • (chosenModuleEquivOriginalInverseIdeal R K D m : K) = _
  rw [one_smul]

private lemma extendScalarsCongr_inv_app_one_tmul
    {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f₁₂ : R₁ →+* R₂) (f₂₃ : R₂ →+* R₃) (f₁₃ : R₁ →+* R₃)
    (h : f₂₃.comp f₁₂ = f₁₃) (M : ModuleCat R₁) (m : M) :
    (eqToIso (congrArg (fun f : R₁ →+* R₃ ↦
        (ModuleCat.extendScalars f).obj M) h)).inv
        ((1 : R₃) ⊗ₜ[R₁,f₁₃] m) =
      (1 : R₃) ⊗ₜ[R₁,f₂₃.comp f₁₂] m := by
  subst f₁₃
  rfl

private theorem chosenModuleBaseChangeEquivExtended_tower
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [IsOpenImmersion (extensionMap R B)]
    [IsOpenImmersion (extensionMap R C)]
    [IsOpenImmersion (extensionMap B C)]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    let M := chosenModule R K D
    let hcomp : (algebraMap B C).comp (algebraMap R B) = algebraMap R C :=
      (IsScalarTower.algebraMap_eq R B C).symm
    (eqToIso (congrArg (fun f : R →+* C ↦
          (ModuleCat.extendScalars f).obj M) hcomp)).inv ≫
        (ModuleCat.extendScalarsComp (algebraMap R B) (algebraMap B C)).hom.app M ≫
        (ModuleCat.extendScalars (algebraMap B C)).map
          (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D).toModuleIso.hom ≫
        (extendedInverseIdealBaseChangeModuleEquiv R B C K D).toModuleIso.hom =
      (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R C K D).toModuleIso.hom := by
  let M := chosenModule R K D
  let hcomp : (algebraMap B C).comp (algebraMap R B) = algebraMap R C :=
    (IsScalarTower.algebraMap_eq R B C).symm
  dsimp only
  apply (ModuleCat.extendRestrictScalarsAdj (algebraMap R C)).homEquiv _ _ |>.injective
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  let x := (eqToIso (congrArg (fun f : R →+* C ↦
      (ModuleCat.extendScalars f).obj M) hcomp)).inv ((1 : C) ⊗ₜ[R] m)
  have hx : x = (1 : C) ⊗ₜ[R,(algebraMap B C).comp (algebraMap R B)] m :=
    extendScalarsCongr_inv_app_one_tmul
      (algebraMap R B) (algebraMap B C) (algebraMap R C) hcomp M m
  let y := (ModuleCat.extendScalarsComp
    (algebraMap R B) (algebraMap B C)).hom.app M x
  let y₀ := (ModuleCat.extendScalarsComp
    (algebraMap R B) (algebraMap B C)).hom.app M
      ((1 : C) ⊗ₜ[R,(algebraMap B C).comp (algebraMap R B)] m)
  have hy : y = y₀ := by
    dsimp only [y, y₀]
    rw [hx]
    rfl
  have hy₀ := ModuleCat.extendScalarsComp_hom_app_one_tmul
    (algebraMap R B) (algebraMap B C) M m
  change y₀ = _ at hy₀
  let z := (ModuleCat.extendScalars (algebraMap B C)).map
    (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D).toModuleIso.hom y
  have hz : z = (1 : C) ⊗ₜ[B,algebraMap B C]
      (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D
        ((1 : B) ⊗ₜ[R] m)) := by
    dsimp only [z]
    rw [hy, hy₀]
    rfl
  change (extendedInverseIdealBaseChangeModuleEquiv R B C K D z :
      extendedInverseIdeal R C K D) =
    chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R C K D
      ((1 : C) ⊗ₜ[R] m)
  rw [hz]
  apply Subtype.ext
  trans (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D
    ((1 : B) ⊗ₜ[R] m) : K)
  · exact extendedInverseIdealBaseChangeModuleEquiv_apply_one_tmul
      R B C K D _
  · rw [chosenModuleBaseChangeEquivExtended_apply_one_tmul,
      chosenModuleBaseChangeEquivExtended_apply_one_tmul]

private noncomputable def chosenLineBundlePullbackIsoExtendedInverseIdeal
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).obj
        (AffineDedekind.lineBundle R K D).obj ≅
      tilde (R := CommRingCat.of B)
        (ModuleCat.of B (extendedInverseIdeal R B K D)) :=
  ((extendScalarsTildeIsoPullback
      (CommRingCat.of R) (CommRingCat.of B)
      (CommRingCat.ofHom (algebraMap R B))).app (chosenModule R K D)).symm ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D).toModuleIso

private noncomputable def extendedInverseIdealPullbackIso
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap B C)).obj
        (tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K D))) ≅
      tilde (R := CommRingCat.of C)
        (ModuleCat.of C (extendedInverseIdeal R C K D)) :=
  ((extendScalarsTildeIsoPullback
      (CommRingCat.of B) (CommRingCat.of C)
      (CommRingCat.ofHom (algebraMap B C))).app
        (ModuleCat.of B (extendedInverseIdeal R B K D))).symm ≪≫
    (tilde.functor (CommRingCat.of C)).mapIso
      (extendedInverseIdealBaseChangeModuleEquiv R B C K D).toModuleIso

private theorem extendedInverseIdealTildeIso_pullback
    (R₁ R₂ B C K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R₁ C] [IsTorsionFree R₁ C]
    [Algebra R₂ C] [IsTorsionFree R₂ C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R₁ B C] [IsScalarTower R₂ B C]
    [IsScalarTower B C K]
    [IsScalarTower R₁ B K] [IsScalarTower R₂ B K]
    [IsScalarTower R₁ C K] [IsScalarTower R₂ C K]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    let hC := overlapInverseIdealExtensionEq_baseChange
      R₁ R₂ B C K D₁ D₂ h
    (Scheme.Modules.pullback (extensionMap B C)).map
          (extendedInverseIdealTildeIso R₁ R₂ B K D₁ D₂ h).hom ≫
        (extendedInverseIdealPullbackIso R₂ B C K D₂).hom =
      (extendedInverseIdealPullbackIso R₁ B C K D₁).hom ≫
        (extendedInverseIdealTildeIso R₁ R₂ C K D₁ D₂ hC).hom := by
  let hC := overlapInverseIdealExtensionEq_baseChange
    R₁ R₂ B C K D₁ D₂ h
  let E := extendScalarsTildeIsoPullback
    (CommRingCat.of B) (CommRingCat.of C)
      (CommRingCat.ofHom (algebraMap B C))
  let I₁ := ModuleCat.of B (extendedInverseIdeal R₁ B K D₁)
  let I₂ := ModuleCat.of B (extendedInverseIdeal R₂ B K D₂)
  let eB := (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ h).toModuleIso.hom
  let eC := (extendedInverseIdealEquiv R₁ R₂ C K D₁ D₂ hC).toModuleIso.hom
  let b₁ := (extendedInverseIdealBaseChangeModuleEquiv
    R₁ B C K D₁).toModuleIso.hom
  let b₂ := (extendedInverseIdealBaseChangeModuleEquiv
    R₂ B C K D₂).toModuleIso.hom
  have hE := E.inv.naturality eB
  have hb := extendedInverseIdealEquiv_baseChange_module
    R₁ R₂ B C K D₁ D₂ h
  change
    (Scheme.Modules.pullback (extensionMap B C)).map
          ((tilde.functor (CommRingCat.of B)).map eB) ≫
        E.inv.app I₂ =
      E.inv.app I₁ ≫ (tilde.functor (CommRingCat.of C)).map
        ((ModuleCat.extendScalars (algebraMap B C)).map eB) at hE
  change
    (Scheme.Modules.pullback (extensionMap B C)).map
          ((tilde.functor (CommRingCat.of B)).map eB) ≫
        E.inv.app I₂ ≫ (tilde.functor (CommRingCat.of C)).map b₂ =
      E.inv.app I₁ ≫ (tilde.functor (CommRingCat.of C)).map b₁ ≫
        (tilde.functor (CommRingCat.of C)).map eC
  rw [← Category.assoc, hE]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [hb]

private noncomputable def chosenLineBundlePullbackCompIso
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [CommRing C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [Algebra R C] [Algebra B C]
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    (Scheme.Modules.pullback (extensionMap B C)).obj
        ((Scheme.Modules.pullback (extensionMap R B)).obj
          (AffineDedekind.lineBundle R K D).obj) ≅
      (Scheme.Modules.pullback (extensionMap R C)).obj
        (AffineDedekind.lineBundle R K D).obj :=
  (Scheme.Modules.pullbackComp
      (extensionMap B C) (extensionMap R B)).app
        (AffineDedekind.lineBundle R K D).obj ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app
      (AffineDedekind.lineBundle R K D).obj

private theorem reassoc_middle_eq
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ Y : C}
    (p : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (v : X₄ ⟶ X₅)
    (b : X₂ ⟶ Y) (u : Y ⟶ X₄) (h : c ≫ d = b ≫ u) :
    p ≫ a ≫ c ≫ d ≫ v = p ≫ a ≫ b ≫ u ≫ v := by
  calc
    _ = p ≫ a ≫ (c ≫ d) ≫ v := by simp only [Category.assoc]
    _ = p ≫ a ≫ (b ≫ u) ≫ v := by rw [h]
    _ = _ := by simp only [Category.assoc]

private theorem insert_retraction_middle
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ Y Z : C}
    (p : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (b : X₂ ⟶ Y)
    (u : Y ⟶ X₃) (v : X₃ ⟶ X₄)
    (tinv : Y ⟶ Z) (thom : Z ⟶ Y) (h : tinv ≫ thom = 𝟙 Y) :
    p ≫ a ≫ b ≫ u ≫ v =
      (p ≫ a ≫ b ≫ tinv) ≫ thom ≫ u ≫ v := by
  simp only [Category.assoc]
  rw [← Category.assoc tinv thom (u ≫ v), h, Category.id_comp]

private theorem whisker_fourfold_eq
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y₁ Y₂ : C}
    (p : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (t : X₃ ⟶ X₄) (q : X₀ ⟶ Y₁) (r : Y₁ ⟶ Y₂)
    (s : Y₂ ⟶ X₄) (z₁ : X₄ ⟶ X₅)
    (z₂ : X₅ ⟶ X₆) (z₃ : X₆ ⟶ X₇)
    (h : p ≫ a ≫ b ≫ t = q ≫ r ≫ s) :
    (p ≫ a ≫ b ≫ t) ≫ z₁ ≫ z₂ ≫ z₃ =
      (q ≫ r ≫ s) ≫ z₁ ≫ z₂ ≫ z₃ := by
  rw [h]

private theorem reassoc_three_tail
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (q : X₀ ⟶ X₁) (r : X₁ ⟶ X₂) (s : X₂ ⟶ X₃)
    (z₁ : X₃ ⟶ X₄) (z₂ : X₄ ⟶ X₅) (z₃ : X₅ ⟶ X₆) :
    (q ≫ r ≫ s) ≫ z₁ ≫ z₂ ≫ z₃ =
      q ≫ r ≫ (s ≫ z₁ ≫ z₂ ≫ z₃) := by
  simp only [Category.assoc]

private theorem whisker_tail_eq
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ Y : C}
    (q : X₀ ⟶ X₁) (r : X₁ ⟶ X₂) (s : X₂ ⟶ X₃)
    (z₁ : X₃ ⟶ X₄) (z₂ : X₄ ⟶ X₅)
    (z₃ : X₅ ⟶ Y) (w : X₂ ⟶ Y)
    (h : s ≫ z₁ ≫ z₂ ≫ z₃ = w) :
    q ≫ r ≫ (s ≫ z₁ ≫ z₂ ≫ z₃) = q ≫ r ≫ w := by
  rw [h]

private theorem pullback_precomp_finish_of_core_and_tail
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y₁ Y₂ : C}
    (p : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (t : X₃ ⟶ X₄) (q : X₀ ⟶ Y₁) (r : Y₁ ⟶ Y₂)
    (s : Y₂ ⟶ X₄) (z₁ : X₄ ⟶ X₅)
    (z₂ : X₅ ⟶ X₆) (z₃ : X₆ ⟶ X₇) (w : Y₂ ⟶ X₇)
    (hcore : p ≫ a ≫ b ≫ t = q ≫ r ≫ s)
    (htail : s ≫ z₁ ≫ z₂ ≫ z₃ = w) :
    (p ≫ a ≫ b ≫ t) ≫ z₁ ≫ z₂ ≫ z₃ = q ≫ r ≫ w :=
  (whisker_fourfold_eq p a b t q r s z₁ z₂ z₃ hcore).trans
    ((reassoc_three_tail q r s z₁ z₂ z₃).trans
      (whisker_tail_eq q r s z₁ z₂ z₃ w htail))

private theorem pullback_precomp_of_naturality_retraction_core_tail
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y₁ Y₂ : C}
    (p : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (v : X₄ ⟶ X₇)
    (b : X₂ ⟶ Y₁) (u : Y₁ ⟶ X₄)
    (tinv : Y₁ ⟶ Y₂) (thom : Y₂ ⟶ Y₁)
    (q : X₀ ⟶ X₅) (r : X₅ ⟶ X₆) (s : X₆ ⟶ Y₂)
    (w : X₆ ⟶ X₇)
    (hnatural : c ≫ d = b ≫ u) (hretract : tinv ≫ thom = 𝟙 Y₁)
    (hcore : p ≫ a ≫ b ≫ tinv = q ≫ r ≫ s)
    (htail : s ≫ thom ≫ u ≫ v = w) :
    p ≫ a ≫ c ≫ d ≫ v = q ≫ r ≫ w :=
  (reassoc_middle_eq p a c d v b u hnatural).trans
    ((insert_retraction_middle p a b u v tinv thom hretract).trans
      (pullback_precomp_finish_of_core_and_tail
        p a b tinv q r s thom u v w hcore htail))

private theorem pullback_precomp_head_of_naturality_and_retraction
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₇ Y₁ Y₂ : C}
    (p : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (v : X₄ ⟶ X₇)
    (b : X₂ ⟶ Y₁) (u : Y₁ ⟶ X₄)
    (tinv : Y₁ ⟶ Y₂) (thom : Y₂ ⟶ Y₁)
    (hnatural : c ≫ d = b ≫ u) (hretract : tinv ≫ thom = 𝟙 Y₁) :
    p ≫ a ≫ c ≫ d ≫ v =
      (p ≫ a ≫ b ≫ tinv) ≫ thom ≫ u ≫ v :=
  (reassoc_middle_eq p a c d v b u hnatural).trans
    (insert_retraction_middle p a b u v tinv thom hretract)

private noncomputable def pullbackPrecompPostcompose
    {C : Type u} [Category C] {X Y Z : C} (p : X ⟶ Y) (z : Y ⟶ Z) : X ⟶ Z :=
  p ≫ z

private theorem pullbackPrecompPostcompose_eq
    {C : Type u} [Category C] {X Y Z : C} {p q : X ⟶ Y}
    (h : p = q) (z : Y ⟶ Z) :
    pullbackPrecompPostcompose p z = pullbackPrecompPostcompose q z :=
  congrArg (fun w ↦ pullbackPrecompPostcompose w z) h

private noncomputable def pullbackPrecompPrefix₂
    {C : Type u} [Category C] {X₀ X₁ X₂ X₃ : C}
    (q : X₀ ⟶ X₁) (r : X₁ ⟶ X₂) (s : X₂ ⟶ X₃) : X₀ ⟶ X₃ :=
  q ≫ r ≫ s

private theorem pullbackPrecompPrefix₂_eq
    {C : Type u} [Category C] {X₀ X₁ X₂ X₃ : C}
    (q : X₀ ⟶ X₁) (r : X₁ ⟶ X₂) {s t : X₂ ⟶ X₃}
    (h : s = t) : pullbackPrecompPrefix₂ q r s = pullbackPrecompPrefix₂ q r t :=
  congrArg (fun w ↦ pullbackPrecompPrefix₂ q r w) h

private theorem pullbackPrecompPostcompose_three_reassoc
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (q : X₀ ⟶ X₁) (r : X₁ ⟶ X₂) (s : X₂ ⟶ X₃)
    (z₁ : X₃ ⟶ X₄) (z₂ : X₄ ⟶ X₅) (z₃ : X₅ ⟶ X₆) :
    pullbackPrecompPostcompose
        (pullbackPrecompPostcompose
          (pullbackPrecompPostcompose (q ≫ r ≫ s) z₁) z₂) z₃ =
      q ≫ r ≫ (s ≫ z₁ ≫ z₂ ≫ z₃) := by
  unfold pullbackPrecompPostcompose
  simp only [Category.assoc]

private theorem pullbackPrecompPostcompose_three_reassoc_of_eq
    {C : Type u} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (p : X₀ ⟶ X₃) (q : X₀ ⟶ X₁) (r : X₁ ⟶ X₂)
    (s : X₂ ⟶ X₃) (z₁ : X₃ ⟶ X₄)
    (z₂ : X₄ ⟶ X₅) (z₃ : X₅ ⟶ X₆)
    (hp : p = q ≫ r ≫ s) :
    pullbackPrecompPostcompose
        (pullbackPrecompPostcompose
          (pullbackPrecompPostcompose p z₁) z₂) z₃ =
      q ≫ r ≫ (s ≫ z₁ ≫ z₂ ≫ z₃) := by
  rw [hp]
  exact pullbackPrecompPostcompose_three_reassoc q r s z₁ z₂ z₃

private noncomputable def extendScalarsTildeIsoPullbackTowerRightComponents
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C)
    (hfg : f ≫ g = k)
    (hcomp : Spec.map g ≫ Spec.map f = Spec.map k)
    (M : ModuleCat A) :=
  (Scheme.Modules.pullbackCongr hcomp).hom.app
        ((tilde.functor A).obj M) ≫
    (extendScalarsTildeIsoPullback A C k).inv.app M ≫
    (tilde.functor C).map
      (eqToIso (congrArg
        (fun q : A ⟶ C ↦ (ModuleCat.extendScalars q.hom).obj M) hfg)).inv

private noncomputable abbrev extendScalarsTildeIsoPullbackTowerRight
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C)
    (hfg : f ≫ g = k)
    (hcomp : Spec.map g ≫ Spec.map f = Spec.map k)
    (M : ModuleCat A) :=
  extendScalarsTildeIsoPullbackTowerRightComponents A B C f g k hfg hcomp M

private theorem extendScalarsTildeIsoPullbackTowerRight_eq_components
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C)
    (hfg : f ≫ g = k)
    (hcomp : Spec.map g ≫ Spec.map f = Spec.map k)
    (M : ModuleCat A) :
    extendScalarsTildeIsoPullbackTowerRight A B C f g k hfg hcomp M =
      extendScalarsTildeIsoPullbackTowerRightComponents
        A B C f g k hfg hcomp M := by
  rfl

private theorem extendScalarsTildeIsoPullbackTowerRightComponents_postcompose_three_reassoc
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C)
    (hfg : f ≫ g = k)
    (hcomp : Spec.map g ≫ Spec.map f = Spec.map k)
    (M : ModuleCat A)
    {X₄ X₅ X₆ : (Spec C).Modules}
    (z₁ : (tilde.functor C).obj
        ((ModuleCat.extendScalars (f ≫ g).hom).obj M) ⟶ X₄)
    (z₂ : X₄ ⟶ X₅) (z₃ : X₅ ⟶ X₆) :
    pullbackPrecompPostcompose
        (pullbackPrecompPostcompose
          (pullbackPrecompPostcompose
            (extendScalarsTildeIsoPullbackTowerRightComponents
              A B C f g k hfg hcomp M) z₁) z₂) z₃ =
      pullbackPrecompPrefix₂
        ((Scheme.Modules.pullbackCongr hcomp).hom.app
          ((tilde.functor A).obj M))
        ((extendScalarsTildeIsoPullback A C k).inv.app M)
        ((tilde.functor C).map
            (eqToIso (congrArg
              (fun q : A ⟶ C ↦ (ModuleCat.extendScalars q.hom).obj M) hfg)).inv ≫
          z₁ ≫ z₂ ≫ z₃) := by
  unfold extendScalarsTildeIsoPullbackTowerRightComponents
  unfold pullbackPrecompPrefix₂
  exact pullbackPrecompPostcompose_three_reassoc _ _ _ z₁ z₂ z₃

private theorem extendScalarsTildeIsoPullback_tower_inv_app_canonical
    (A B C : CommRingCat.{u}) (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C)
    (hfg : f ≫ g = k)
    (hcomp : Spec.map g ≫ Spec.map f = Spec.map k)
    (M : ModuleCat A) :
    (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).inv.app
          ((tilde.functor A).obj M) ≫
        (Scheme.Modules.pullback (Spec.map g)).map
          ((extendScalarsTildeIsoPullback A B f).inv.app M) ≫
        (extendScalarsTildeIsoPullback B C g).inv.app
          ((ModuleCat.extendScalars f.hom).obj M) ≫
        (tilde.functor C).map
          ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) =
      extendScalarsTildeIsoPullbackTowerRight A B C f g k hfg hcomp M := by
  unfold extendScalarsTildeIsoPullbackTowerRight
  unfold extendScalarsTildeIsoPullbackTowerRightComponents
  rw [extendScalarsTildeIsoPullback_comp_inv_app]
  rw [← extendScalarsTildeIsoPullback_congr_inv A C hfg M]
  rw [← pullbackCongr_hom_comp_inv
    (show Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f from
      @Spec.map_comp A B C f g)
    (congrArg Spec.map hfg) hcomp ((tilde.functor A).obj M)]
  exact Category.assoc _ _ _

/-- The affine-extension tower equality, named once so that all coherence paths use the same
proof term inside the corresponding `eqToIso`. -/
private theorem extensionCommRingCatHom_comp
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C] :
    let f : CommRingCat.of R ⟶ CommRingCat.of B :=
      CommRingCat.ofHom (algebraMap R B)
    let g : CommRingCat.of B ⟶ CommRingCat.of C :=
      CommRingCat.ofHom (algebraMap B C)
    let k : CommRingCat.of R ⟶ CommRingCat.of C :=
      CommRingCat.ofHom (algebraMap R C)
    f ≫ g = k := by
  dsimp only
  ext x
  exact (IsScalarTower.algebraMap_apply R B C x).symm

section PullbackPrecompStages

variable (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
  [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [Algebra R B] [IsTorsionFree R B]
  [Algebra B K] [IsFractionRing B K]
  [Algebra R C] [IsTorsionFree R C]
  [Algebra C K] [IsFractionRing C K]
  [Algebra B C] [IsScalarTower R B C] [IsScalarTower B C K]
  [IsScalarTower R B K] [IsScalarTower R C K]
  [IsOpenImmersion (extensionMap R B)]
  [IsOpenImmersion (extensionMap R C)]
  [IsOpenImmersion (extensionMap B C)]
  [Algebra.IsEpi B C] [Module.Flat B C]

/-- The module comparison attached to the named affine-extension tower equality.  This is kept as
a separate declaration so every sheaf-level path contains the same opaque comparison morphism. -/
private noncomputable def chosenModuleTowerCongrIso
    (D : WeilDivisor (HeightOneSpectrum R)) :=
  let A := CommRingCat.of R
  let C' := CommRingCat.of C
  let M := chosenModule R K D
  let hfg := extensionCommRingCatHom_comp R B C
  eqToIso (congrArg
    (fun q : A ⟶ C' ↦ (ModuleCat.extendScalars q.hom).obj M) hfg)

/- Superseded reducible path experiments.  The final proof below uses the generic categorical
composition lemma directly, so none of these intermediate declarations is part of the checked
API or proof term.

private noncomputable abbrev chosenLineBundlePullbackPrecompSource
    (D : WeilDivisor (HeightOneSpectrum R)) :=
  (Scheme.Modules.pullback
    (extensionMap B C ≫ extensionMap R B)).obj
      (AffineDedekind.lineBundle R K D).obj

private noncomputable abbrev chosenLineBundlePullbackPrecompTarget
    (D : WeilDivisor (HeightOneSpectrum R)) :=
  _root_.AlgebraicGeometry.tilde
    (R := CommRingCat.of C)
    (ModuleCat.of C (extendedInverseIdeal R C K D))

private noncomputable abbrev chosenLineBundlePullbackPrecompPath₀
    (D : WeilDivisor (HeightOneSpectrum R)) :
    chosenLineBundlePullbackPrecompSource R B C K D ⟶
      chosenLineBundlePullbackPrecompTarget R C K D := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let cc := (Scheme.Modules.pullback (Spec.map g)).map
    ((tilde.functor B').map cB)
  let dd := E_g.inv.app I
  let vv := (tilde.functor C').map b
  exact pcomp.inv ≫ aa ≫ cc ≫ dd ≫ vv

private noncomputable abbrev chosenLineBundlePullbackPrecompPath₁
    (D : WeilDivisor (HeightOneSpectrum R)) :
    chosenLineBundlePullbackPrecompSource R B C K D ⟶
      chosenLineBundlePullbackPrecompTarget R C K D := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let vv := (tilde.functor C').map b
  exact pcomp.inv ≫ aa ≫ bb ≫ uu ≫ vv

private noncomputable abbrev chosenLineBundlePullbackPrecompPath₂
    (D : WeilDivisor (HeightOneSpectrum R)) :
    chosenLineBundlePullbackPrecompSource R B C K D ⟶
      chosenLineBundlePullbackPrecompTarget R C K D := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let vv := (tilde.functor C').map b
  exact (pcomp.inv ≫ aa ≫ bb ≫ ti) ≫ th ≫ uu ≫ vv

private noncomputable abbrev chosenLineBundlePullbackPrecompPath₃
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompSource R B C K D ⟶
      chosenLineBundlePullbackPrecompTarget R C K D := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let hfg := extensionCommRingCatHom_comp R B C
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let th := (tilde.functor C').map mcomp.hom
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let vv := (tilde.functor C').map b
  exact (qq ≫ rr ≫ ss) ≫ th ≫ uu ≫ vv

private noncomputable abbrev chosenLineBundlePullbackPrecompPath₄
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompSource R B C K D ⟶
      chosenLineBundlePullbackPrecompTarget R C K D := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let hfg := extensionCommRingCatHom_comp R B C
  let mcongr := eqToIso (congrArg
    (fun q : A ⟶ C' ↦ (ModuleCat.extendScalars q.hom).obj M) hfg)
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let th := (tilde.functor C').map mcomp.hom
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let vv := (tilde.functor C').map b
  exact qq ≫ rr ≫ (ss ≫ th ≫ uu ≫ vv)

private noncomputable abbrev chosenLineBundlePullbackPrecompPath₅
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompSource R B C K D ⟶
      chosenLineBundlePullbackPrecompTarget R C K D := by
  let A := CommRingCat.of R
  let C' := CommRingCat.of C
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cC := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R C K D).toModuleIso.hom
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ww := (tilde.functor C').map cC
  exact qq ≫ rr ≫ ww

private theorem chosenLineBundlePullbackPrecompPaths_p₀₁
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompPath₀ R B C K D =
      chosenLineBundlePullbackPrecompPath₁ R B C K D := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  have hnatural := E_g.inv.naturality cB
  change
    (Scheme.Modules.pullback (Spec.map g)).map
          ((tilde.functor B').map cB) ≫ E_g.inv.app I =
      E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M) ≫
        (tilde.functor C').map
          ((ModuleCat.extendScalars g.hom).map cB) at hnatural
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let cc := (Scheme.Modules.pullback (Spec.map g)).map
    ((tilde.functor B').map cB)
  let dd := E_g.inv.app I
  let vv := (tilde.functor C').map b
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  change
    pcomp.inv ≫ aa ≫ cc ≫ dd ≫ vv =
      pcomp.inv ≫ aa ≫ bb ≫ uu ≫ vv
  exact reassoc_middle_eq pcomp.inv aa cc dd vv bb uu hnatural

private theorem chosenLineBundlePullbackPrecompPaths_p₁₂
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompPath₁ R B C K D =
      chosenLineBundlePullbackPrecompPath₂ R B C K D := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  have hmcomp :
      (tilde.functor C').map mcomp.inv ≫
          (tilde.functor C').map mcomp.hom = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let cc := (Scheme.Modules.pullback (Spec.map g)).map
    ((tilde.functor B').map cB)
  let dd := E_g.inv.app I
  let vv := (tilde.functor C').map b
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  change
    pcomp.inv ≫ aa ≫ bb ≫ uu ≫ vv =
      (pcomp.inv ≫ aa ≫ bb ≫ ti) ≫ th ≫ uu ≫ vv
  exact insert_retraction_middle pcomp.inv aa bb uu vv ti th hmcomp

/- A specialized declaration of the middle whiskering step also exceeds the kernel's
deterministic budget.  The final staged theorem below therefore applies the already checked
generic categorical whiskering lemma directly to the affine tower equality.

private structure PullbackPrecompStep
    {C₀ : Type u} [Category C₀] {X Y : C₀} (p q : X ⟶ Y) where
  hom_eq : p = q

private opaque chosenLineBundlePullbackPrecompPaths_p₂₃
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    PullbackPrecompStep
      (chosenLineBundlePullbackPrecompPath₂ R B C K D)
      (chosenLineBundlePullbackPrecompPath₃ R B C K D hcomp) := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let hfg := extensionCommRingCatHom_comp R B C
  have hcore := extendScalarsTildeIsoPullback_tower_inv_app_canonical
    A B' C' f g k hfg hcomp M
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let cc := (Scheme.Modules.pullback (Spec.map g)).map
    ((tilde.functor B').map cB)
  let dd := E_g.inv.app I
  let vv := (tilde.functor C').map b
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  change pcomp.inv ≫ aa ≫ bb ≫ ti = qq ≫ rr ≫ ss at hcore
  exact ⟨whisker_fourfold_eq pcomp.inv aa bb ti qq rr ss th uu vv hcore⟩

-/

private theorem chosenLineBundlePullbackPrecompPaths_p₃₄
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompPath₃ R B C K D hcomp =
      chosenLineBundlePullbackPrecompPath₄ R B C K D hcomp := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let vv := (tilde.functor C').map b
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let th := (tilde.functor C').map mcomp.hom
  exact reassoc_three_tail qq rr ss th uu vv

/- The last specialized whiskering theorem has the same kernel-size issue as the middle step;
the final staged theorem applies the generic tail-whiskering lemma directly instead.

private theorem chosenLineBundlePullbackPrecompPaths_p₄₅
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompPath₄ R B C K D hcomp =
      chosenLineBundlePullbackPrecompPath₅ R B C K D hcomp := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let cC := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R C K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  have hmodule := chosenModuleBaseChangeEquivExtended_tower R B C K D
  change mcongr.inv ≫ mcomp.hom ≫
      (ModuleCat.extendScalars g.hom).map cB ≫ b = cC at hmodule
  have hmoduleT := congrArg (fun z ↦ (tilde.functor C').map z) hmodule
  simp only [CategoryTheory.Functor.map_comp] at hmoduleT
  let vv := (tilde.functor C').map b
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let th := (tilde.functor C').map mcomp.hom
  let ww := (tilde.functor C').map cC
  have hnatural := E_g.inv.naturality cB
  change cc ≫ dd = bb ≫ uu at hnatural
  have hmcomp : ti ≫ th = 𝟙 _ := by
    dsimp only [ti, th]
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  change ss ≫ th ≫ uu ≫ vv = ww at hmoduleT
  exact whisker_tail_eq qq rr ss th uu vv ww hmoduleT

-/

/- This redundant aggregate equality forces the kernel to normalize both long endpoints a
second time.  The checked raw naturality theorem below chains the same staged equalities directly
against its own source and target.

private theorem chosenLineBundlePullbackPrecompPaths_p₀₅
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompPath₀ R B C K D =
      chosenLineBundlePullbackPrecompPath₅ R B C K D hcomp := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let cC := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R C K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let hfg := extensionCommRingCatHom_comp R B C
  have hcore := extendScalarsTildeIsoPullback_tower_inv_app_canonical
    A B' C' f g k hfg hcomp M
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let vv := (tilde.functor C').map b
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  let ww := (tilde.functor C').map cC
  have hnatural := E_g.inv.naturality cB
  change cc ≫ dd = bb ≫ uu at hnatural
  have hmcomp : ti ≫ th = 𝟙 _ := by
    dsimp only [ti, th]
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  change pcomp.inv ≫ aa ≫ bb ≫ ti = qq ≫ rr ≫ ss at hcore
  have hmodule := chosenModuleBaseChangeEquivExtended_tower R B C K D
  change mcongr.inv ≫ mcomp.hom ≫
      (ModuleCat.extendScalars g.hom).map cB ≫ b = cC at hmodule
  have hmoduleT := congrArg (fun z ↦ (tilde.functor C').map z) hmodule
  simp only [CategoryTheory.Functor.map_comp] at hmoduleT
  change ss ≫ th ≫ uu ≫ vv = ww at hmoduleT
  have hp₂₅ := pullback_precomp_finish_of_core_and_tail
    pcomp.inv aa bb ti qq rr ss th uu vv ww hcore hmoduleT
  exact (chosenLineBundlePullbackPrecompPaths_p₀₁ R B C K D hcomp).trans
    ((chosenLineBundlePullbackPrecompPaths_p₁₂ R B C K D hcomp).trans
      hp₂₅)

-/

/- A single opaque bundle of all six paths is mathematically equivalent to the staged proof
above, but exceeds Lean's deterministic kernel budget because all five equalities are checked as
one declaration.  It is retained temporarily while the independently checked declarations above
are validated, then removed before handoff.

private structure PullbackPrecompPaths
    {C₀ : Type u} [Category C₀] {X Y : C₀} (start finish : X ⟶ Y) where
  path₀ : X ⟶ Y
  path₁ : X ⟶ Y
  path₂ : X ⟶ Y
  path₃ : X ⟶ Y
  path₄ : X ⟶ Y
  path₅ : X ⟶ Y
  start_eq_path₀ : start = path₀
  path₀₁ : path₀ = path₁
  path₁₂ : path₁ = path₂
  path₂₃ : path₂ = path₃
  path₃₄ : path₃ = path₄
  path₄₅ : path₄ = path₅
  path₅_eq_finish : path₅ = finish

private noncomputable abbrev chosenLineBundlePullbackPrecompStart
    (D : WeilDivisor (HeightOneSpectrum R)) :=
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  pcomp.inv ≫
    (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M) ≫
    (Scheme.Modules.pullback (Spec.map g)).map ((tilde.functor B').map cB) ≫
    E_g.inv.app I ≫ (tilde.functor C').map b

private noncomputable abbrev chosenLineBundlePullbackPrecompFinish
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :=
  let A := CommRingCat.of R
  let C' := CommRingCat.of C
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cC := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R C K D).toModuleIso.hom
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  pcongr.hom ≫ E_k.inv.app M ≫ (tilde.functor C').map cC

private opaque chosenLineBundlePullbackPrecompPaths
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    PullbackPrecompPaths
      (chosenLineBundlePullbackPrecompStart R B C K D)
      (chosenLineBundlePullbackPrecompFinish R B C K D hcomp) := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let cC := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R C K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let cc := (Scheme.Modules.pullback (Spec.map g)).map
    ((tilde.functor B').map cB)
  let dd := E_g.inv.app I
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  let vv := (tilde.functor C').map b
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let ww := (tilde.functor C').map cC
  let p₀ := pcomp.inv ≫ aa ≫ cc ≫ dd ≫ vv
  let p₁ := pcomp.inv ≫ aa ≫ bb ≫ uu ≫ vv
  let p₂ := (pcomp.inv ≫ aa ≫ bb ≫ ti) ≫ th ≫ uu ≫ vv
  let p₃ := (qq ≫ rr ≫ ss) ≫ th ≫ uu ≫ vv
  let p₄ := qq ≫ rr ≫ (ss ≫ th ≫ uu ≫ vv)
  let p₅ := qq ≫ rr ≫ ww
  have hnatural := E_g.inv.naturality cB
  change cc ≫ dd = bb ≫ uu at hnatural
  have hmcomp : ti ≫ th = 𝟙 _ := by
    dsimp only [ti, th]
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  let hfg := extensionCommRingCatHom_comp R B C
  have hcore := extendScalarsTildeIsoPullback_tower_inv_app_canonical
    A B' C' f g k hfg hcomp M
  change pcomp.inv ≫ aa ≫ bb ≫ ti = qq ≫ rr ≫ ss at hcore
  have hmodule := chosenModuleBaseChangeEquivExtended_tower R B C K D
  change mcongr.inv ≫ mcomp.hom ≫
      (ModuleCat.extendScalars g.hom).map cB ≫ b = cC at hmodule
  have hmoduleT := congrArg (fun z ↦ (tilde.functor C').map z) hmodule
  simp only [CategoryTheory.Functor.map_comp] at hmoduleT
  change ss ≫ th ≫ uu ≫ vv = ww at hmoduleT
  refine
    { path₀ := p₀
      path₁ := p₁
      path₂ := p₂
      path₃ := p₃
      path₄ := p₄
      path₅ := p₅
      start_eq_path₀ := ?_
      path₀₁ := ?_
      path₁₂ := ?_
      path₂₃ := ?_
      path₃₄ := ?_
      path₄₅ := ?_
      path₅_eq_finish := ?_ }
  · rfl
  · exact reassoc_middle_eq pcomp.inv aa cc dd vv bb uu hnatural
  · exact insert_retraction_middle pcomp.inv aa bb uu vv ti th hmcomp
  · change
      (pcomp.inv ≫ aa ≫ bb ≫ ti) ≫ th ≫ uu ≫ vv =
        (qq ≫ rr ≫ ss) ≫ th ≫ uu ≫ vv
    rw [hcore]
  · dsimp only [p₃, p₄]
    simp only [Category.assoc]
  · change qq ≫ rr ≫ (ss ≫ th ≫ uu ≫ vv) = qq ≫ rr ≫ ww
    rw [hmoduleT]
  · rfl

private theorem chosenLineBundlePullbackPrecompPaths_start_finish
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    chosenLineBundlePullbackPrecompStart R B C K D =
      chosenLineBundlePullbackPrecompFinish R B C K D hcomp := by
  let P := chosenLineBundlePullbackPrecompPaths R B C K D hcomp
  exact P.start_eq_path₀.trans
    (P.path₀₁.trans (P.path₁₂.trans (P.path₂₃.trans
      (P.path₃₄.trans (P.path₄₅.trans P.path₅_eq_finish)))))

-/

-/

end PullbackPrecompStages

private structure PullbackPrecompWitness where
  C₀ : Type (u + 1)
  category : Category.{u} C₀
  X : C₀
  Y : C₀
  start : @Quiver.Hom C₀ category.toQuiver X Y
  finish : @Quiver.Hom C₀ category.toQuiver X Y
  coherent : start = finish

private noncomputable def PullbackPrecompWitness.whiskerRight₃
    (W : PullbackPrecompWitness) {Z₁ Z₂ Z₃ : W.C₀}
    (z₁ : @Quiver.Hom W.C₀ W.category.toQuiver W.Y Z₁)
    (z₂ : @Quiver.Hom W.C₀ W.category.toQuiver Z₁ Z₂)
    (z₃ : @Quiver.Hom W.C₀ W.category.toQuiver Z₂ Z₃) :
    PullbackPrecompWitness := by
  letI : Category.{u} W.C₀ := W.category
  refine
    { C₀ := W.C₀
      category := W.category
      X := W.X
      Y := Z₃
      start := (W.start ≫ z₁) ≫ z₂ ≫ z₃
      finish := (W.finish ≫ z₁) ≫ z₂ ≫ z₃
      coherent := ?_ }
  exact congrArg (fun z ↦ (z ≫ z₁) ≫ z₂ ≫ z₃) W.coherent

/- Superseded monolithic witness; split into independently elaborated head and tail witnesses
below so each declaration stays within Lean's deterministic budget.

private noncomputable def chosenLineBundlePullbackPrecompWitness
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [IsOpenImmersion (extensionMap R B)]
    [IsOpenImmersion (extensionMap R C)]
    [IsOpenImmersion (extensionMap B C)]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    PullbackPrecompWitness := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let cC := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R C K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let cc := (Scheme.Modules.pullback (Spec.map g)).map
    ((tilde.functor B').map cB)
  let dd := E_g.inv.app I
  let vv := (tilde.functor C').map b
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  let ww := (tilde.functor C').map cC
  have hnatural := E_g.inv.naturality cB
  change cc ≫ dd = bb ≫ uu at hnatural
  have hmcomp : ti ≫ th = 𝟙 _ := by
    dsimp only [ti, th]
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  let hfg := extensionCommRingCatHom_comp R B C
  have hcore := extendScalarsTildeIsoPullback_tower_inv_app_canonical
    A B' C' f g k hfg hcomp M
  change pcomp.inv ≫ aa ≫ bb ≫ ti = qq ≫ rr ≫ ss at hcore
  have hmodule := chosenModuleBaseChangeEquivExtended_tower R B C K D
  change mcongr.inv ≫ mcomp.hom ≫
      (ModuleCat.extendScalars g.hom).map cB ≫ b = cC at hmodule
  have hmoduleT := congrArg (fun z ↦ (tilde.functor C').map z) hmodule
  simp only [CategoryTheory.Functor.map_comp] at hmoduleT
  change ss ≫ th ≫ uu ≫ vv = ww at hmoduleT
  refine
    { C₀ := (Spec (.of C)).Modules
      category := (inferInstance : Category.{u} (Spec (.of C)).Modules)
      X := (Scheme.Modules.pullback
        (extensionMap B C ≫ extensionMap R B)).obj
          (AffineDedekind.lineBundle R K D).obj
      Y := _root_.AlgebraicGeometry.tilde
        (R := CommRingCat.of C)
        (ModuleCat.of C (extendedInverseIdeal R C K D))
      start := pcomp.inv ≫ aa ≫ cc ≫ dd ≫ vv
      finish := qq ≫ rr ≫ ww
      coherent := ?_ }
  exact pullback_precomp_of_naturality_retraction_core_tail
    pcomp.inv aa cc dd vv bb uu ti th qq rr ss ww
      hnatural hmcomp hcore hmoduleT

-/

section PullbackPrecompPackedWitnesses

variable (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
  [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [Algebra R B] [IsTorsionFree R B]
  [Algebra B K] [IsFractionRing B K]
  [Algebra R C] [IsTorsionFree R C]
  [Algebra C K] [IsFractionRing C K]
  [Algebra B C] [IsScalarTower R B C] [IsScalarTower B C K]
  [IsScalarTower R B K] [IsScalarTower R C K]
  [IsOpenImmersion (extensionMap R B)]
  [IsOpenImmersion (extensionMap R C)]
  [IsOpenImmersion (extensionMap B C)]
  [Algebra.IsEpi B C] [Module.Flat B C]

private noncomputable def chosenLineBundlePullbackPrecompHeadWitness
    (D : WeilDivisor (HeightOneSpectrum R)) : PullbackPrecompWitness := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let I := ModuleCat.of B (extendedInverseIdeal R B K D)
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let cc := (Scheme.Modules.pullback (Spec.map g)).map
    ((tilde.functor B').map cB)
  let dd := E_g.inv.app I
  let vv := (tilde.functor C').map b
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  have hnatural := E_g.inv.naturality cB
  change cc ≫ dd = bb ≫ uu at hnatural
  have hmcomp : ti ≫ th = 𝟙 _ := by
    dsimp only [ti, th]
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  refine
    { C₀ := (Spec (.of C)).Modules
      category := (inferInstance : Category.{u} (Spec (.of C)).Modules)
      X := (Scheme.Modules.pullback
        (extensionMap B C ≫ extensionMap R B)).obj
          (AffineDedekind.lineBundle R K D).obj
      Y := _root_.AlgebraicGeometry.tilde
        (R := CommRingCat.of C)
        (ModuleCat.of C (extendedInverseIdeal R C K D))
      start := pcomp.inv ≫ aa ≫ cc ≫ dd ≫ vv
      finish := (pcomp.inv ≫ aa ≫ bb ≫ ti) ≫ th ≫ uu ≫ vv
      coherent := ?_ }
  exact pullback_precomp_head_of_naturality_and_retraction
    pcomp.inv aa cc dd vv bb uu ti th hnatural hmcomp

/- Superseded two-step tail witness; the middle affine-tower step and the final module-tower
step are checked separately below.

private noncomputable def chosenLineBundlePullbackPrecompTailWitness
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    PullbackPrecompWitness := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let cC := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R C K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let vv := (tilde.functor C').map b
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  let ww := (tilde.functor C').map cC
  let hfg := extensionCommRingCatHom_comp R B C
  have hcore := extendScalarsTildeIsoPullback_tower_inv_app_canonical
    A B' C' f g k hfg hcomp M
  change pcomp.inv ≫ aa ≫ bb ≫ ti = qq ≫ rr ≫ ss at hcore
  have hmodule := chosenModuleBaseChangeEquivExtended_tower R B C K D
  change mcongr.inv ≫ mcomp.hom ≫
      (ModuleCat.extendScalars g.hom).map cB ≫ b = cC at hmodule
  have hmoduleT := congrArg (fun z ↦ (tilde.functor C').map z) hmodule
  simp only [CategoryTheory.Functor.map_comp] at hmoduleT
  change ss ≫ th ≫ uu ≫ vv = ww at hmoduleT
  refine
    { C₀ := (Spec (.of C)).Modules
      category := (inferInstance : Category.{u} (Spec (.of C)).Modules)
      X := (Scheme.Modules.pullback
        (extensionMap B C ≫ extensionMap R B)).obj
          (AffineDedekind.lineBundle R K D).obj
      Y := _root_.AlgebraicGeometry.tilde
        (R := CommRingCat.of C)
        (ModuleCat.of C (extendedInverseIdeal R C K D))
      start := (pcomp.inv ≫ aa ≫ bb ≫ ti) ≫ th ≫ uu ≫ vv
      finish := qq ≫ rr ≫ ww
      coherent := ?_ }
  exact pullback_precomp_finish_of_core_and_tail
    pcomp.inv aa bb ti qq rr ss th uu vv ww hcore hmoduleT

-/

/- Superseded direct middle witness; the active implementation below stores the unwhiskered
tower equality and applies the generic packed-witness whiskering operation.

private noncomputable def chosenLineBundlePullbackPrecompMiddleWitness
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    PullbackPrecompWitness := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let vv := (tilde.functor C').map b
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let ti := (tilde.functor C').map mcomp.inv
  let th := (tilde.functor C').map mcomp.hom
  let hfg := extensionCommRingCatHom_comp R B C
  have hcore := extendScalarsTildeIsoPullback_tower_inv_app_canonical
    A B' C' f g k hfg hcomp M
  change pcomp.inv ≫ aa ≫ bb ≫ ti = qq ≫ rr ≫ ss at hcore
  refine
    { C₀ := (Spec (.of C)).Modules
      category := (inferInstance : Category.{u} (Spec (.of C)).Modules)
      X := (Scheme.Modules.pullback
        (extensionMap B C ≫ extensionMap R B)).obj
          (AffineDedekind.lineBundle R K D).obj
      Y := _root_.AlgebraicGeometry.tilde
        (R := CommRingCat.of C)
        (ModuleCat.of C (extendedInverseIdeal R C K D))
      start := (pcomp.inv ≫ aa ≫ bb ≫ ti) ≫ th ≫ uu ≫ vv
      finish := (qq ≫ rr ≫ ss) ≫ th ≫ uu ≫ vv
      coherent := ?_ }
  exact whisker_fourfold_eq pcomp.inv aa bb ti qq rr ss th uu vv hcore

-/

/- Superseded category-packed core and whiskering witnesses.  The active proof thunks below pack
only the proposition and its proof, avoiding dependent category-field normalization.

private noncomputable def chosenLineBundlePullbackPrecompCoreWitness
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    PullbackPrecompWitness := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_f := extendScalarsTildeIsoPullback A B' f
  let E_g := extendScalarsTildeIsoPullback B' C' g
  let E_k := extendScalarsTildeIsoPullback A C' k
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let mcongr := chosenModuleTowerCongrIso R B C K D
  let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
    ((tilde.functor A).obj M)
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  let aa := (Scheme.Modules.pullback (Spec.map g)).map (E_f.inv.app M)
  let bb := E_g.inv.app ((ModuleCat.extendScalars f.hom).obj M)
  let qq := pcongr.hom
  let rr := E_k.inv.app M
  let ss := (tilde.functor C').map mcongr.inv
  let ti := (tilde.functor C').map mcomp.inv
  let hfg := extensionCommRingCatHom_comp R B C
  have hcore := extendScalarsTildeIsoPullback_tower_inv_app_canonical
    A B' C' f g k hfg hcomp M
  change pcomp.inv ≫ aa ≫ bb ≫ ti = qq ≫ rr ≫ ss at hcore
  refine
    { C₀ := (Spec (.of C)).Modules
      category := (inferInstance : Category.{u} (Spec (.of C)).Modules)
      X := _
      Y := _
      start := pcomp.inv ≫ aa ≫ bb ≫ ti
      finish := qq ≫ rr ≫ ss
      coherent := hcore }

private noncomputable def chosenLineBundlePullbackPrecompMiddleWitness
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    PullbackPrecompWitness := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let th := (tilde.functor C').map mcomp.hom
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  let vv := (tilde.functor C').map b
  exact (chosenLineBundlePullbackPrecompCoreWitness R B C K D hcomp).whiskerRight₃
    th uu vv

-/

private noncomputable def chosenLineBundlePullbackPrecompCore
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let hfg := extensionCommRingCatHom_comp R B C
  exact extendScalarsTildeIsoPullback_tower_inv_app_canonical
    A B' C' f g k hfg hcomp M

private noncomputable abbrev chosenLineBundlePullbackPrecompCoreRight
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let hfg := extensionCommRingCatHom_comp R B C
  exact extendScalarsTildeIsoPullbackTowerRight
    A B' C' f g k hfg hcomp M

private noncomputable def chosenLineBundlePullbackPrecompCoreWhiskerModuleComp
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let th := (tilde.functor C').map
    ((ModuleCat.extendScalarsComp f.hom g.hom).hom.app M)
  exact pullbackPrecompPostcompose_eq
    (chosenLineBundlePullbackPrecompCore R B C K D hcomp) th

private noncomputable def chosenLineBundlePullbackPrecompCoreWhiskerChosenModule
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  exact pullbackPrecompPostcompose_eq
    (chosenLineBundlePullbackPrecompCoreWhiskerModuleComp
      R B C K D hcomp) uu

private noncomputable def chosenLineBundlePullbackPrecompMiddle
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let C' := CommRingCat.of C
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let vv := (tilde.functor C').map b
  exact pullbackPrecompPostcompose_eq
    (chosenLineBundlePullbackPrecompCoreWhiskerChosenModule
      R B C K D hcomp) vv

private noncomputable def chosenLineBundlePullbackPrecompModuleTail
    (D : WeilDivisor (HeightOneSpectrum R))
    (_hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  have hmodule := chosenModuleBaseChangeEquivExtended_tower R B C K D
  have hmoduleT := congrArg (fun z ↦ (tilde.functor C').map z) hmodule
  simp only [CategoryTheory.Functor.map_comp] at hmoduleT
  exact hmoduleT

private noncomputable def chosenLineBundlePullbackPrecompEndCoreWhiskerModuleComp
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let hfg := extensionCommRingCatHom_comp R B C
  let th := (tilde.functor C').map
    ((ModuleCat.extendScalarsComp f.hom g.hom).hom.app M)
  exact pullbackPrecompPostcompose_eq
    (extendScalarsTildeIsoPullbackTowerRight_eq_components
      A B' C' f g k hfg hcomp M) th

private noncomputable def chosenLineBundlePullbackPrecompEndCoreWhiskerChosenModule
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let uu := (tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)
  exact pullbackPrecompPostcompose_eq
    (chosenLineBundlePullbackPrecompEndCoreWhiskerModuleComp
      R B C K D hcomp) uu

private noncomputable def chosenLineBundlePullbackPrecompEndCoreWhiskerBaseChange
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let C' := CommRingCat.of C
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let vv := (tilde.functor C').map b
  exact pullbackPrecompPostcompose_eq
    (chosenLineBundlePullbackPrecompEndCoreWhiskerChosenModule
      R B C K D hcomp) vv

private noncomputable def chosenLineBundlePullbackPrecompEndExpandedReassoc
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_k := extendScalarsTildeIsoPullback A C' k
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  let hfg := extensionCommRingCatHom_comp R B C
  exact extendScalarsTildeIsoPullbackTowerRightComponents_postcompose_three_reassoc
    A B' C' f g k hfg hcomp M
    ((tilde.functor C').map mcomp.hom)
    ((tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB))
    ((tilde.functor C').map b)

private noncomputable def chosenLineBundlePullbackPrecompEndReassoc
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :=
  (chosenLineBundlePullbackPrecompEndCoreWhiskerBaseChange
      R B C K D hcomp).trans
    (chosenLineBundlePullbackPrecompEndExpandedReassoc R B C K D hcomp)

private noncomputable def chosenLineBundlePullbackPrecompEndTail
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let A := CommRingCat.of R
  let C' := CommRingCat.of C
  let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
  let M := chosenModule R K D
  let E_k := extendScalarsTildeIsoPullback A C' k
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    ((tilde.functor A).obj M)
  exact pullbackPrecompPrefix₂_eq pcongr.hom (E_k.inv.app M)
    (chosenLineBundlePullbackPrecompModuleTail R B C K D hcomp)

/- The final transitivity join is intentionally left outside the compiling helper checkpoint.
Its two endpoints are now expressed through `pullbackPrecompPrefix₂`; the next integration step
is the one remaining typed equality recorded in the branch handoff.

private noncomputable def chosenLineBundlePullbackPrecompEnd
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :=
  (chosenLineBundlePullbackPrecompEndReassoc R B C K D hcomp).trans
    (chosenLineBundlePullbackPrecompEndTail R B C K D hcomp)

-/

private noncomputable def chosenLineBundlePullbackPrecompHeadMiddle
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :=
  (chosenLineBundlePullbackPrecompHeadWitness R B C K D).coherent.trans
    (chosenLineBundlePullbackPrecompMiddle R B C K D hcomp)

private noncomputable abbrev chosenLineBundlePullbackPrecompJunction
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let A := CommRingCat.of R
  let B' := CommRingCat.of B
  let C' := CommRingCat.of C
  let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
  let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
  let M := chosenModule R K D
  let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
    R B K D).toModuleIso.hom
  let b := (extendedInverseIdealBaseChangeModuleEquiv
    R B C K D).toModuleIso.hom
  let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
  exact pullbackPrecompPostcompose
    (pullbackPrecompPostcompose
      (pullbackPrecompPostcompose
        (chosenLineBundlePullbackPrecompCoreRight R B C K D hcomp)
        ((tilde.functor C').map mcomp.hom))
      ((tilde.functor C').map ((ModuleCat.extendScalars g.hom).map cB)))
    ((tilde.functor C').map b)

private noncomputable def chosenLineBundlePullbackPrecompMiddleEndEqJunction
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    let A := CommRingCat.of R
    let B' := CommRingCat.of B
    let C' := CommRingCat.of C
    let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
    let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
    let M := chosenModule R K D
    let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
      R B K D).toModuleIso.hom
    let b := (extendedInverseIdealBaseChangeModuleEquiv
      R B C K D).toModuleIso.hom
    let mcomp := (ModuleCat.extendScalarsComp f.hom g.hom).app M
    pullbackPrecompPostcompose
        (pullbackPrecompPostcompose
          (pullbackPrecompPostcompose
            (chosenLineBundlePullbackPrecompCoreRight R B C K D hcomp)
            ((tilde.functor C').map mcomp.hom))
          ((tilde.functor C').map
            ((ModuleCat.extendScalars g.hom).map cB)))
        ((tilde.functor C').map b) =
      chosenLineBundlePullbackPrecompJunction R B C K D hcomp := by
  rfl

private noncomputable def chosenLineBundlePullbackPrecompMiddleAtJunction
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  exact (chosenLineBundlePullbackPrecompMiddle R B C K D hcomp).trans
    (chosenLineBundlePullbackPrecompMiddleEndEqJunction R B C K D hcomp)

private noncomputable def chosenLineBundlePullbackPrecompHeadMiddleAtJunction
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  exact (chosenLineBundlePullbackPrecompHeadWitness R B C K D).coherent.trans
    (chosenLineBundlePullbackPrecompMiddleAtJunction R B C K D hcomp)

/- Aggregate consumers of the pending final end join.

private noncomputable def chosenLineBundlePullbackPrecompEndReassocAtJunction
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) := by
  let p := chosenLineBundlePullbackPrecompJunction R B C K D hcomp
  exact show p = _ from
    chosenLineBundlePullbackPrecompEndReassoc R B C K D hcomp

private noncomputable def chosenLineBundlePullbackPrecompEndAtJunction
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :=
  (chosenLineBundlePullbackPrecompEndReassocAtJunction
      R B C K D hcomp).trans
    (chosenLineBundlePullbackPrecompEndTail R B C K D hcomp)

private noncomputable def chosenLineBundlePullbackPrecompCoherent
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :=
  (chosenLineBundlePullbackPrecompHeadMiddleAtJunction
      R B C K D hcomp).trans
    (chosenLineBundlePullbackPrecompEndAtJunction R B C K D hcomp)

-/

end PullbackPrecompPackedWitnesses

/- Pending aggregate/public affine naturality consumer.

private theorem chosenLineBundlePullbackIsoExtendedInverseIdeal_pullback_precomp_raw
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [IsOpenImmersion (extensionMap R B)]
    [IsOpenImmersion (extensionMap R C)]
    [IsOpenImmersion (extensionMap B C)]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    let A := CommRingCat.of R
    let B' := CommRingCat.of B
    let C' := CommRingCat.of C
    let f : A ⟶ B' := CommRingCat.ofHom (algebraMap R B)
    let g : B' ⟶ C' := CommRingCat.ofHom (algebraMap B C)
    let k : A ⟶ C' := CommRingCat.ofHom (algebraMap R C)
    let M := chosenModule R K D
    let I := ModuleCat.of B (extendedInverseIdeal R B K D)
    let E_f := extendScalarsTildeIsoPullback A B' f
    let E_g := extendScalarsTildeIsoPullback B' C' g
    let E_k := extendScalarsTildeIsoPullback A C' k
    let cB := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
      R B K D).toModuleIso.hom
    let cC := (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion
      R C K D).toModuleIso.hom
    let b := (extendedInverseIdealBaseChangeModuleEquiv
      R B C K D).toModuleIso.hom
    let pcomp := (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).app
      ((tilde.functor A).obj M)
    let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
      ((tilde.functor A).obj M)
    pcomp.inv ≫ (Scheme.Modules.pullback (Spec.map g)).map
          (E_f.inv.app M ≫ (tilde.functor B').map cB) ≫
        E_g.inv.app I ≫ (tilde.functor C').map b =
      pcongr.hom ≫ E_k.inv.app M ≫ (tilde.functor C').map cC := by
  dsimp only
  rw [CategoryTheory.Functor.map_comp]
  exact chosenLineBundlePullbackPrecompCoherent R B C K D hcomp

private theorem chosenLineBundlePullbackIsoExtendedInverseIdeal_pullback
    (R B C K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R C] [IsTorsionFree R C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R B C] [IsScalarTower B C K]
    [IsScalarTower R B K] [IsScalarTower R C K]
    [IsOpenImmersion (extensionMap R B)]
    [IsOpenImmersion (extensionMap R C)]
    [IsOpenImmersion (extensionMap B C)]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D : WeilDivisor (HeightOneSpectrum R))
    (hcomp : extensionMap B C ≫ extensionMap R B = extensionMap R C) :
    (Scheme.Modules.pullback (extensionMap B C)).map
          (chosenLineBundlePullbackIsoExtendedInverseIdeal R B K D).hom ≫
        (extendedInverseIdealPullbackIso R B C K D).hom =
      (chosenLineBundlePullbackCompIso R B C K D hcomp).hom ≫
        (chosenLineBundlePullbackIsoExtendedInverseIdeal R C K D).hom := by
  let pcomp := (Scheme.Modules.pullbackComp
    (extensionMap B C) (extensionMap R B)).app
      (AffineDedekind.lineBundle R K D).obj
  let pcongr := (Scheme.Modules.pullbackCongr hcomp).app
    (AffineDedekind.lineBundle R K D).obj
  change
    (Scheme.Modules.pullback (extensionMap B C)).map
          (chosenLineBundlePullbackIsoExtendedInverseIdeal R B K D).hom ≫
        (extendedInverseIdealPullbackIso R B C K D).hom =
      pcomp.hom ≫ pcongr.hom ≫
        (chosenLineBundlePullbackIsoExtendedInverseIdeal R C K D).hom
  apply (cancel_epi pcomp.inv).1
  simp only [Iso.inv_hom_id_assoc]
  exact chosenLineBundlePullbackIsoExtendedInverseIdeal_pullback_precomp_raw
    R B C K D hcomp

-/

/-- On every affine open immersion between the chart spectrum and a common overlap spectrum,
restriction of the chosen affine divisor line bundle is *specified* by tilde of the extended
inverse divisor ideal.  Keeping this isomorphism as data, rather than immediately hiding it in a
`Nonempty`, is the coherence-ready form used by the overlap construction below.  No classical
localization presentation is required. -/
noncomputable def restrictionIsoExtendedInverseIdealOfIsOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    (AffineDedekind.lineBundle R K D).obj.restrict (extensionMap R B) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
        (ModuleCat.of B (extendedInverseIdeal R B K D)) := by
  let M := chosenModule R K D
  exact ((extendScalarsTildeIsoRestrict
      (CommRingCat.of R) (CommRingCat.of B)
      (CommRingCat.ofHom (algebraMap R B))).app M).symm ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (chosenModuleBaseChangeEquivExtended_of_isOpenImmersion R B K D).toModuleIso

private theorem restrictionIsoExtendedInverseIdealOfIsOpenImmersion_eq
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K D =
      (Scheme.Modules.restrictFunctorIsoPullback
          (extensionMap R B)).app
            (AffineDedekind.lineBundle R K D).obj ≪≫
        chosenLineBundlePullbackIsoExtendedInverseIdeal R B K D := by
  rfl

/-- Proposition-valued compatibility wrapper for the specified open-immersion comparison. -/
theorem restrictionIdentifiesExtendedInverseIdeal_of_isOpenImmersion
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    (D : WeilDivisor (HeightOneSpectrum R)) :
    RestrictionIdentifiesExtendedInverseIdeal R B K D :=
  ⟨inferInstance, ⟨restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K D⟩⟩

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
  exact restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₁ B K D₁ ≪≫
    extendedInverseIdealTildeIso R₁ R₂ B K D₁ D₂ h ≪≫
    (restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₂ B K D₂).symm

/-- The specified inverse-ideal comparison, expressed between ordinary module pullbacks rather
than the open-immersion restriction functors.  This is the affine model transported by the
curve-level pairwise overlap construction. -/
noncomputable def chosenLineBundlePullbackIsoOfOverlapExtensionEq
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
    (Scheme.Modules.pullback (extensionMap R₁ B)).obj
        (AffineDedekind.lineBundle R₁ K D₁).obj ≅
      (Scheme.Modules.pullback (extensionMap R₂ B)).obj
        (AffineDedekind.lineBundle R₂ K D₂).obj :=
  ((Scheme.Modules.restrictFunctorIsoPullback
      (extensionMap R₁ B)).app
        (AffineDedekind.lineBundle R₁ K D₁).obj).symm ≪≫
    chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      R₁ R₂ B K D₁ D₂ h ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback
      (extensionMap R₂ B)).app
        (AffineDedekind.lineBundle R₂ K D₂).obj

private theorem chosenLineBundlePullbackIsoOfOverlapExtensionEq_eq
    (R₁ R₂ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R₁ B K] [IsScalarTower R₂ B K]
    [IsOpenImmersion (extensionMap R₁ B)]
    [IsOpenImmersion (extensionMap R₂ B)]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂) :
    chosenLineBundlePullbackIsoOfOverlapExtensionEq
        R₁ R₂ B K D₁ D₂ h =
      chosenLineBundlePullbackIsoExtendedInverseIdeal R₁ B K D₁ ≪≫
        extendedInverseIdealTildeIso R₁ R₂ B K D₁ D₂ h ≪≫
        (chosenLineBundlePullbackIsoExtendedInverseIdeal R₂ B K D₂).symm := by
  apply Iso.ext
  simp only [chosenLineBundlePullbackIsoOfOverlapExtensionEq,
    chosenLineBundleRestrictionIsoOfOverlapExtensionEq,
    restrictionIsoExtendedInverseIdealOfIsOpenImmersion_eq,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/- Pending consumer of `chosenLineBundlePullbackIsoExtendedInverseIdeal_pullback`.

private theorem chosenLineBundlePullbackIsoOfOverlapExtensionEq_naturality
    (R₁ R₂ B C K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra B K] [IsFractionRing B K]
    [Algebra R₁ C] [IsTorsionFree R₁ C]
    [Algebra R₂ C] [IsTorsionFree R₂ C]
    [Algebra C K] [IsFractionRing C K]
    [Algebra B C] [IsScalarTower R₁ B C] [IsScalarTower R₂ B C]
    [IsScalarTower B C K]
    [IsScalarTower R₁ B K] [IsScalarTower R₂ B K]
    [IsScalarTower R₁ C K] [IsScalarTower R₂ C K]
    [IsOpenImmersion (extensionMap R₁ B)]
    [IsOpenImmersion (extensionMap R₂ B)]
    [IsOpenImmersion (extensionMap R₁ C)]
    [IsOpenImmersion (extensionMap R₂ C)]
    [IsOpenImmersion (extensionMap B C)]
    [Algebra.IsEpi B C] [Module.Flat B C]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (h : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂)
    (hcomp₁ : extensionMap B C ≫ extensionMap R₁ B = extensionMap R₁ C)
    (hcomp₂ : extensionMap B C ≫ extensionMap R₂ B = extensionMap R₂ C) :
    let hC := overlapInverseIdealExtensionEq_baseChange
      R₁ R₂ B C K D₁ D₂ h
    (Scheme.Modules.pullback (extensionMap B C)).map
          (chosenLineBundlePullbackIsoOfOverlapExtensionEq
            R₁ R₂ B K D₁ D₂ h).hom ≫
        (chosenLineBundlePullbackCompIso R₂ B C K D₂ hcomp₂).hom =
      (chosenLineBundlePullbackCompIso R₁ B C K D₁ hcomp₁).hom ≫
        (chosenLineBundlePullbackIsoOfOverlapExtensionEq
          R₁ R₂ C K D₁ D₂ hC).hom := by
  let hC := overlapInverseIdealExtensionEq_baseChange
    R₁ R₂ B C K D₁ D₂ h
  dsimp only
  let s₁B := chosenLineBundlePullbackIsoExtendedInverseIdeal R₁ B K D₁
  let s₂B := chosenLineBundlePullbackIsoExtendedInverseIdeal R₂ B K D₂
  let s₁C := chosenLineBundlePullbackIsoExtendedInverseIdeal R₁ C K D₁
  let s₂C := chosenLineBundlePullbackIsoExtendedInverseIdeal R₂ C K D₂
  let eB := extendedInverseIdealTildeIso R₁ R₂ B K D₁ D₂ h
  let eC := extendedInverseIdealTildeIso R₁ R₂ C K D₁ D₂ hC
  let t₁ := extendedInverseIdealPullbackIso R₁ B C K D₁
  let t₂ := extendedInverseIdealPullbackIso R₂ B C K D₂
  let A₁ := chosenLineBundlePullbackCompIso R₁ B C K D₁ hcomp₁
  let A₂ := chosenLineBundlePullbackCompIso R₂ B C K D₂ hcomp₂
  have hs₁ := chosenLineBundlePullbackIsoExtendedInverseIdeal_pullback
    R₁ B C K D₁ hcomp₁
  have hs₂ := chosenLineBundlePullbackIsoExtendedInverseIdeal_pullback
    R₂ B C K D₂ hcomp₂
  have he := extendedInverseIdealTildeIso_pullback
    R₁ R₂ B C K D₁ D₂ h
  have hs₂inv :
      (Scheme.Modules.pullback (extensionMap B C)).map s₂B.inv ≫
          A₂.hom ≫ s₂C.hom = t₂.hom := by
    calc
      _ = (Scheme.Modules.pullback (extensionMap B C)).map s₂B.inv ≫
          ((Scheme.Modules.pullback (extensionMap B C)).map s₂B.hom ≫
            t₂.hom) := by rw [← hs₂]
      _ = ((Scheme.Modules.pullback (extensionMap B C)).map s₂B.inv ≫
          (Scheme.Modules.pullback (extensionMap B C)).map s₂B.hom) ≫
            t₂.hom := (Category.assoc _ _ _).symm
      _ = (Scheme.Modules.pullback (extensionMap B C)).map
            (s₂B.inv ≫ s₂B.hom) ≫ t₂.hom := by
        rw [CategoryTheory.Functor.map_comp]
      _ = t₂.hom := by
        rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [chosenLineBundlePullbackIsoOfOverlapExtensionEq_eq,
    chosenLineBundlePullbackIsoOfOverlapExtensionEq_eq]
  change
    (Scheme.Modules.pullback (extensionMap B C)).map
          (s₁B.hom ≫ eB.hom ≫ s₂B.inv) ≫ A₂.hom =
      A₁.hom ≫ s₁C.hom ≫ eC.hom ≫ s₂C.inv
  apply (cancel_mono s₂C.hom).1
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [hs₂inv, he]
  rw [← Category.assoc, hs₁]
  exact Category.assoc _ _ _

-/

/-- On one common affine overlap, the specified inverse-ideal comparisons are transitive.
The intermediate restriction comparison cancels, while the equality-induced maps between the
three extended inverse ideals compose to the direct equality-induced map.  This is the algebraic
core of triple-overlap coherence; functoriality under restriction from pairwise to triple
intersections is a separate geometric comparison. -/
theorem chosenLineBundleRestrictionIsoOfOverlapExtensionEq_hom_trans
    (R₁ R₂ R₃ B K : Type u)
    [CommRing R₁] [IsDedekindDomain R₁]
    [CommRing R₂] [IsDedekindDomain R₂]
    [CommRing R₃] [IsDedekindDomain R₃]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R₁ K] [IsFractionRing R₁ K]
    [Algebra R₂ K] [IsFractionRing R₂ K]
    [Algebra R₃ K] [IsFractionRing R₃ K]
    [Algebra R₁ B] [IsTorsionFree R₁ B]
    [Algebra R₂ B] [IsTorsionFree R₂ B]
    [Algebra R₃ B] [IsTorsionFree R₃ B]
    [Algebra B K] [IsFractionRing B K]
    [IsOpenImmersion (extensionMap R₁ B)]
    [IsOpenImmersion (extensionMap R₂ B)]
    [IsOpenImmersion (extensionMap R₃ B)]
    (D₁ : WeilDivisor (HeightOneSpectrum R₁))
    (D₂ : WeilDivisor (HeightOneSpectrum R₂))
    (D₃ : WeilDivisor (HeightOneSpectrum R₃))
    (h₁₂ : Boundary.OverlapInverseIdealExtensionEq R₁ R₂ B K D₁ D₂)
    (h₂₃ : Boundary.OverlapInverseIdealExtensionEq R₂ R₃ B K D₂ D₃)
    (h₁₃ : Boundary.OverlapInverseIdealExtensionEq R₁ R₃ B K D₁ D₃) :
    (chosenLineBundleRestrictionIsoOfOverlapExtensionEq
        R₁ R₂ B K D₁ D₂ h₁₂).hom ≫
      (chosenLineBundleRestrictionIsoOfOverlapExtensionEq
        R₂ R₃ B K D₂ D₃ h₂₃).hom =
    (chosenLineBundleRestrictionIsoOfOverlapExtensionEq
      R₁ R₃ B K D₁ D₃ h₁₃).hom := by
  letI : IsScalarTower R₁ B K := h₁₂.1
  letI : IsScalarTower R₂ B K := h₁₂.2.1
  letI : IsScalarTower R₃ B K := h₂₃.2.1
  let e₁ := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₁ B K D₁
  let e₂ := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₂ B K D₂
  let e₃ := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R₃ B K D₃
  let b₁₂ := extendedInverseIdealTildeIso R₁ R₂ B K D₁ D₂ h₁₂
  let b₂₃ := extendedInverseIdealTildeIso R₂ R₃ B K D₂ D₃ h₂₃
  let b₁₃ := extendedInverseIdealTildeIso R₁ R₃ B K D₁ D₃ h₁₃
  change (e₁ ≪≫ b₁₂ ≪≫ e₂.symm).hom ≫
      (e₂ ≪≫ b₂₃ ≪≫ e₃.symm).hom =
    (e₁ ≪≫ b₁₃ ≪≫ e₃.symm).hom
  simp only [Iso.trans_hom, Category.assoc]
  change e₁.hom ≫ b₁₂.hom ≫ e₂.inv ≫ e₂.hom ≫ b₂₃.hom ≫ e₃.inv =
    e₁.hom ≫ b₁₃.hom ≫ e₃.inv
  rw [Iso.inv_hom_id_assoc]
  have hb : b₁₂.hom ≫ b₂₃.hom = b₁₃.hom := by
    dsimp only [b₁₂, b₂₃, b₁₃, extendedInverseIdealTildeIso]
    let F := tilde.functor (CommRingCat.of B)
    let c₁₂ :=
      (extendedInverseIdealEquiv R₁ R₂ B K D₁ D₂ h₁₂).toModuleIso.hom
    let c₂₃ :=
      (extendedInverseIdealEquiv R₂ R₃ B K D₂ D₃ h₂₃).toModuleIso.hom
    let c₁₃ :=
      (extendedInverseIdealEquiv R₁ R₃ B K D₁ D₃ h₁₃).toModuleIso.hom
    change F.map c₁₂ ≫ F.map c₂₃ = F.map c₁₃
    rw [← F.map_comp]
    congr 1
  simpa only [Category.assoc] using
    congrArg (fun z ↦ e₁.hom ≫ z ≫ e₃.inv) hb

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
