/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.DivisorLineBundle
import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# Localization boundary for affine divisor line bundles

The affine divisor line bundle in `DivisorLineBundle` uses a chosen `CommRing.Pic`
representative. This file proves that representative is linearly equivalent to the explicit
inverse fractional ideal attached to the divisor. Thus the choice made by `PicardGroup.Shrink`
is not an obstruction to comparing restrictions.

For a principal open, equality of the localized explicit ideals is then carried through chosen
module representatives, module localization, tilde, and restriction to an actual sheaf
isomorphism. For two coordinate rings mapping compatibly into a common function field through a
common affine overlap, the corresponding extension equality is isolated separately and identifies
the two extended ideal modules and their tilde sheaves. A second explicit boundary identifies each
actual chosen chart restriction with its extended-ideal tilde sheaf; together the two inputs give a
checked restriction isomorphism. Establishing those inputs for curve-chart overlaps, choosing them
coherently, proving the triple cocycle, and proving module effectivity remain open in the current
Mathlib and Tau Ceti dependency graph.
-/

namespace MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization

open CategoryTheory
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors

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

/-- The exact cross-chart boundary: after choosing two coordinate rings mapping through a common
affine overlap ring `B` into a common function field `K`, the maps form scalar towers and the
inverse divisor ideals extend to the same fractional ideal of `B`. Proving this requires the
currently missing compatibility of divisor coefficients with extension/localization. -/
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
the common affine overlap agrees with tilde of the extended inverse divisor ideal. The
principal-open chain below proves the analogous direct comparison from localized-ideal equality;
this identification remains an explicit input for an arbitrary affine open immersion. -/
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

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization
