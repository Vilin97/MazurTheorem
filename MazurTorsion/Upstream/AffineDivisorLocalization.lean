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
isomorphism. The stronger common-extension comparison is now proved on nonempty principal opens:
the actual chosen restriction is tilde of the inverse ideal extended inside the common fraction
field. In the same-chart case, abstract localized-ideal equality is converted to equality of
those common-field extensions and hence directly to an isomorphism of the chosen restrictions.
For two coordinate rings mapping compatibly through a common affine overlap, equality of their
extended ideals is isolated separately and identifies the two extended ideal modules and their
tilde sheaves. On general affine overlaps, identifying each chosen chart restriction remains an
explicit boundary; together those inputs give a checked restriction isomorphism. Establishing the
cross-chart extension equality, choosing the resulting isomorphisms coherently, proving the triple
cocycle, and proving module effectivity remain open in the current Mathlib and Tau Ceti dependency
graph.
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
principal-open theorem below discharges this input outright for nonempty principal opens; this
identification remains an explicit input for an arbitrary affine open immersion. -/
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

namespace CommonExtension

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
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped nonZeroDivisors

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

end MazurTorsion.AlgebraicGeometry.AffineDivisorLocalization.CommonExtension
