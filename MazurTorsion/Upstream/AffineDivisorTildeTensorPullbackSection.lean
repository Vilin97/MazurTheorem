/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTildeTensorBaseChange
import MazurTorsion.Upstream.AINTLIB.Picard.PullbackTensorSection

/-!
# Canonical pullback tensor sections for affine divisor line bundles

The canonical inverse tensorator for pullback is followed by the two factorwise affine
tilde/extension-of-scalars comparisons.  The resulting isomorphism is evaluated on pure tensor
sections coming from the pullback adjunction unit.

The direct `ViaExtendScalars` tensor comparison is proved equal to this canonical factorwise
path on the affine base-change leg.  No cross-chart or descent-data compatibility is asserted.
-/

namespace MazurTorsion.AlgebraicGeometry

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open Module IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry TensorProduct

universe u

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForDivisorTensorSection
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

namespace AffineDivisorLocalization.CommonExtension

/-- Pullback of the tensor of two fixed divisor line bundles, factored through the canonical
inverse pullback tensorator and the two single-factor affine tilde/scalar-extension
comparisons. -/
noncomputable def
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.pullback (extensionMap R B)).obj
        ((AffineDedekind.lineBundle R K D).obj ⊗
          (AffineDedekind.lineBundle R K E).obj) ≅
      _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K D)) ⊗
        _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
          (ModuleCat.of B (extendedInverseIdeal R B K E)) := by
  let PB := Scheme.Modules.pullback (extensionMap R B)
  let LD := (AffineDedekind.lineBundle R K D).obj
  let LE := (AffineDedekind.lineBundle R K E).obj
  let cD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D
  let cE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K E
  letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
  exact (Functor.Monoidal.μIso PB LD LE).symm ≪≫ (cD ⊗ᵢ cE)

/-- Hom expansion of the canonical-tensorator/factorwise affine divisor comparison. -/
private theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    let PB := Scheme.Modules.pullback (extensionMap R B)
    let LD := (AffineDedekind.lineBundle R K D).obj
    let LE := (AffineDedekind.lineBundle R K E).obj
    let cD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D
    let cE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K E
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal (extensionMap R B)
    (lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator
        R B K D E).hom =
      Functor.OplaxMonoidal.δ PB LD LE ≫ (cD.hom ⊗ₘ cE.hom) := by
  rfl

/-- The direct affine tilde/scalar-extension comparison is exactly the comparison through the
canonical pullback tensorator and the two factorwise affine comparisons. -/
theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_eq_viaCanonicalTensorator
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars R B K D E =
      lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator R B K D E := by
  apply Iso.ext
  have hdirect :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_eq_factorwise
      R B K D E
  have hcanonical :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator_hom
      R B K D E
  dsimp only at hdirect hcanonical
  exact hdirect.trans hcanonical.symm

/-- The canonical-tensorator/factorwise affine divisor comparison sends the pullback-unit image
of a pure tensor section to the pure tensor section of the two factorwise images. -/
theorem
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator_hom_unit_tensorSection
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R))
    (V : (Spec (.of R)).Opens)
    (x : Γ((AffineDedekind.lineBundle R K D).obj, V))
    (y : Γ((AffineDedekind.lineBundle R K E).obj, V)) :
    let f := extensionMap R B
    let LD := (AffineDedekind.lineBundle R K D).obj
    let LE := (AffineDedekind.lineBundle R K E).obj
    let TD := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
      (ModuleCat.of B (extendedInverseIdeal R B K D))
    let TE := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
      (ModuleCat.of B (extendedInverseIdeal R B K E))
    let cD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D
    let cE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K E
    let adj := Scheme.Modules.pullbackPushforwardAdjunction f
    (lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator
        R B K D E).hom.val.app (.op (f ⁻¹ᵁ V))
        ((adj.unit.app (LD ⊗ LE)).val.app (.op V)
          (ModularCurves.tensorSection LD LE V x y)) =
      ModularCurves.tensorSection TD TE (f ⁻¹ᵁ V)
        (cD.hom.val.app (.op (f ⁻¹ᵁ V))
          ((adj.unit.app LD).val.app (.op V) x))
        (cE.hom.val.app (.op (f ⁻¹ᵁ V))
          ((adj.unit.app LE).val.app (.op V) y)) := by
  dsimp only
  let f := extensionMap R B
  let PB := Scheme.Modules.pullback f
  let LD := (AffineDedekind.lineBundle R K D).obj
  let LE := (AffineDedekind.lineBundle R K E).obj
  let TD := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
    (ModuleCat.of B (extendedInverseIdeal R B K D))
  let TE := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of B)
    (ModuleCat.of B (extendedInverseIdeal R B K E))
  let cD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D
  let cE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K E
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let uD := (adj.unit.app LD).val.app (.op V) x
  let uE := (adj.unit.app LE).val.app (.op V) y
  letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  have hδ := ModularCurves.pullback_δ_unit_tensorSection f LD LE V x y
  dsimp only at hδ
  have hmap := ModularCurves.tensorSection_map cD.hom cE.hom (f ⁻¹ᵁ V) uD uE
  rw [lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator_hom
    R B K D E]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  exact (congrArg
    (fun z ↦ (cD.hom ⊗ₘ cE.hom).val.app (.op (f ⁻¹ᵁ V)) z) hδ).trans hmap

end AffineDivisorLocalization.CommonExtension
end MazurTorsion.AlgebraicGeometry
