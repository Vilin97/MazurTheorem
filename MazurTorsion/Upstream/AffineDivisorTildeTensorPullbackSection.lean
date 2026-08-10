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
path on the affine base-change leg.  Transport through the restriction-to-pullback comparison
then gives the tensor/addition square for the legacy restriction comparisons on that same leg.
No cross-chart or descent-data compatibility is asserted.
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

/-- The tensor comparator for open restriction obtained by transporting the canonical inverse
pullback tensorator through the restriction-to-pullback comparison in all three positions. -/
noncomputable def lineBundleTensorRestrictionIsoViaPullback
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B]
    [IsOpenImmersion (extensionMap R B)]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    (Scheme.Modules.restrictFunctor (extensionMap R B)).obj
        ((AffineDedekind.lineBundle R K D).obj ⊗
          (AffineDedekind.lineBundle R K E).obj) ≅
      (Scheme.Modules.restrictFunctor (extensionMap R B)).obj
          (AffineDedekind.lineBundle R K D).obj ⊗
        (Scheme.Modules.restrictFunctor (extensionMap R B)).obj
          (AffineDedekind.lineBundle R K E).obj := by
  let f := extensionMap R B
  let PB := Scheme.Modules.pullback f
  let q := Scheme.Modules.restrictFunctorIsoPullback f
  let LD := (AffineDedekind.lineBundle R K D).obj
  let LE := (AffineDedekind.lineBundle R K E).obj
  letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  exact q.app (LD ⊗ LE) ≪≫
    (Functor.Monoidal.μIso PB LD LE).symm ≪≫
    ((q.app LD).symm ⊗ᵢ (q.app LE).symm)

/-- Hom expansion of the restriction tensor comparator transported through pullback. -/
private theorem lineBundleTensorRestrictionIsoViaPullback_hom
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B]
    [IsOpenImmersion (extensionMap R B)]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    let f := extensionMap R B
    let PB := Scheme.Modules.pullback f
    let q := Scheme.Modules.restrictFunctorIsoPullback f
    let LD := (AffineDedekind.lineBundle R K D).obj
    let LE := (AffineDedekind.lineBundle R K E).obj
    letI : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
    (lineBundleTensorRestrictionIsoViaPullback R B K D E).hom =
      (q.app (LD ⊗ LE)).hom ≫
        Functor.OplaxMonoidal.δ PB LD LE ≫
        ((q.app LD).inv ⊗ₘ (q.app LE).inv) := by
  rfl

/-- On one open affine base-change leg, deterministic divisor addition commutes with the legacy
restriction comparisons after the restriction tensorator is transported through pullback. -/
theorem lineBundleAddIso_restrict_viaPullback
    (R B K : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing B] [IsDomain B] [Field K]
    [Algebra R K] [IsFractionRing R K]
    [Algebra R B] [IsTorsionFree R B]
    [Algebra B K] [IsFractionRing B K]
    [IsScalarTower R B K]
    [IsOpenImmersion (extensionMap R B)]
    [Algebra.IsEpi R B] [Module.Flat R B]
    (D E : WeilDivisor (HeightOneSpectrum R)) :
    ((Scheme.Modules.restrictFunctor (extensionMap R B)).mapIso
          (ExplicitIdeal.lineBundleAddIso R K D E) ≪≫
        lineBundleTensorRestrictionIsoViaPullback R B K D E) ≪≫
        (restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K D ⊗ᵢ
          restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K E) =
      restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K (D + E) ≪≫
        extendedInverseIdealAddIso R B K D E := by
  let f := extensionMap R B
  let F := Scheme.Modules.restrictFunctor f
  let PB := Scheme.Modules.pullback f
  let q := Scheme.Modules.restrictFunctorIsoPullback f
  let LD := (AffineDedekind.lineBundle R K D).obj
  let LE := (AffineDedekind.lineBundle R K E).obj
  let LDE := (AffineDedekind.lineBundle R K (D + E)).obj
  let add := ExplicitIdeal.lineBundleAddIso R K D E
  let κ := lineBundleTensorRestrictionIsoViaPullback R B K D E
  let ρD := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K D
  let ρE := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K E
  let ρDE := restrictionIsoExtendedInverseIdealOfIsOpenImmersion R B K (D + E)
  let cD := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K D
  let cE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K E
  let cDE := lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars R B K (D + E)
  let direct := lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars R B K D E
  let addB := extendedInverseIdealAddIso R B K D E
  letI pbMonoidal : PB.Monoidal := Scheme.Modules.pullbackMonoidal f
  let qT := (q.app (LD ⊗ LE)).hom
  let qD := (q.app LD).hom
  let qE := (q.app LE).hom
  let δ := Functor.OplaxMonoidal.δ PB LD LE
  let qInvPair := (q.app LD).inv ⊗ₘ (q.app LE).inv
  let qHomPair := qD ⊗ₘ qE
  let ρPair := ρD.hom ⊗ₘ ρE.hom
  let cPair := cD.hom ⊗ₘ cE.hom
  have hκ := lineBundleTensorRestrictionIsoViaPullback_hom R B K D E
  dsimp only at hκ
  change κ.hom = qT ≫ (δ ≫ qInvPair) at hκ
  have hρD := restrictionIsoExtendedInverseIdealOfIsOpenImmersion_eq_viaExtendScalars
    R B K D
  have hρE := restrictionIsoExtendedInverseIdealOfIsOpenImmersion_eq_viaExtendScalars
    R B K E
  have hρDE := restrictionIsoExtendedInverseIdealOfIsOpenImmersion_eq_viaExtendScalars
    R B K (D + E)
  have hρDhom := congrArg (fun e ↦ e.hom) hρD
  change ρD.hom = qD ≫ cD.hom at hρDhom
  have hρEhom := congrArg (fun e ↦ e.hom) hρE
  change ρE.hom = qE ≫ cE.hom at hρEhom
  have hρDEhom := congrArg (fun e ↦ e.hom) hρDE
  change ρDE.hom = (q.app LDE).hom ≫ cDE.hom at hρDEhom
  have hρPair₁ := congrArg₂ (fun a b ↦ a ⊗ₘ b) hρDhom hρEhom
  change ρPair = (qD ≫ cD.hom) ⊗ₘ (qE ≫ cE.hom) at hρPair₁
  have hρPair : ρPair = qHomPair ≫ cPair :=
    hρPair₁.trans
      (tensorHom_comp_tensorHom qD qE cD.hom cE.hom).symm
  have hqPair₁ : qInvPair ≫ qHomPair =
      ((q.app LD).inv ≫ qD) ⊗ₘ ((q.app LE).inv ≫ qE) :=
    tensorHom_comp_tensorHom (q.app LD).inv (q.app LE).inv qD qE
  have hqPair₂ :
      ((q.app LD).inv ≫ qD) ⊗ₘ ((q.app LE).inv ≫ qE) =
        (𝟙 (PB.obj LD) ⊗ₘ 𝟙 (PB.obj LE)) :=
    congrArg₂ (fun a b ↦ a ⊗ₘ b)
      (q.app LD).inv_hom_id (q.app LE).inv_hom_id
  have hqPair₃ :
      (𝟙 (PB.obj LD) ⊗ₘ 𝟙 (PB.obj LE)) =
        𝟙 (PB.obj LD ⊗ PB.obj LE) :=
    MonoidalCategory.id_tensorHom_id _ _
  have hqPair : qInvPair ≫ qHomPair = 𝟙 (PB.obj LD ⊗ PB.obj LE) :=
    hqPair₁.trans (hqPair₂.trans hqPair₃)
  have hcancel :
      (qT ≫ (δ ≫ qInvPair)) ≫ (qHomPair ≫ cPair) =
        qT ≫ (δ ≫ cPair) := by
    calc
      _ = qT ≫ ((δ ≫ qInvPair) ≫ (qHomPair ≫ cPair)) :=
        Category.assoc _ _ _
      _ = qT ≫ (δ ≫ (qInvPair ≫ (qHomPair ≫ cPair))) :=
        congrArg (qT ≫ ·) (Category.assoc _ _ _)
      _ = qT ≫ (δ ≫ ((qInvPair ≫ qHomPair) ≫ cPair)) :=
        congrArg (fun z ↦ qT ≫ (δ ≫ z))
          (Category.assoc qInvPair qHomPair cPair).symm
      _ = qT ≫ (δ ≫ (𝟙 _ ≫ cPair)) :=
        congrArg (fun z ↦ qT ≫ (δ ≫ (z ≫ cPair))) hqPair
      _ = qT ≫ (δ ≫ cPair) :=
        congrArg (fun z ↦ qT ≫ (δ ≫ z)) (Category.id_comp cPair)
  have hdirectHom :=
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars_hom_eq_factorwise
      R B K D E
  dsimp only at hdirectHom
  change direct.hom = δ ≫ cPair at hdirectHom
  have htail :
      κ.hom ≫ ρPair = qT ≫ direct.hom := by
    calc
      _ = (qT ≫ (δ ≫ qInvPair)) ≫ ρPair :=
        congrArg (· ≫ ρPair) hκ
      _ = (qT ≫ (δ ≫ qInvPair)) ≫ (qHomPair ≫ cPair) :=
        congrArg ((qT ≫ (δ ≫ qInvPair)) ≫ ·) hρPair
      _ = qT ≫ (δ ≫ cPair) := hcancel
      _ = qT ≫ direct.hom := congrArg (qT ≫ ·) hdirectHom.symm
  have hq := q.hom.naturality add.hom
  change F.map add.hom ≫ qT =
    (q.app LDE).hom ≫ PB.map add.hom at hq
  have hpull := lineBundleAddIso_pullback_viaExtendScalars R B K D E
  have hpullHom := congrArg (fun e ↦ e.hom) hpull
  change PB.map add.hom ≫ direct.hom = cDE.hom ≫ addB.hom at hpullHom
  apply Iso.ext
  change (F.map add.hom ≫ κ.hom) ≫ (ρD.hom ⊗ₘ ρE.hom) =
    ρDE.hom ≫ addB.hom
  calc
    _ = F.map add.hom ≫ (κ.hom ≫ ρPair) :=
      Category.assoc _ _ _
    _ = F.map add.hom ≫ (qT ≫ direct.hom) :=
      congrArg (F.map add.hom ≫ ·) htail
    _ = (F.map add.hom ≫ qT) ≫ direct.hom :=
      (Category.assoc _ _ _).symm
    _ = ((q.app LDE).hom ≫ PB.map add.hom) ≫ direct.hom :=
      congrArg (· ≫ direct.hom) hq
    _ = (q.app LDE).hom ≫ (PB.map add.hom ≫ direct.hom) :=
      Category.assoc _ _ _
    _ = (q.app LDE).hom ≫ (cDE.hom ≫ addB.hom) :=
      congrArg ((q.app LDE).hom ≫ ·) hpullHom
    _ = ((q.app LDE).hom ≫ cDE.hom) ≫ addB.hom :=
      (Category.assoc _ _ _).symm
    _ = ρDE.hom ≫ addB.hom :=
      congrArg (· ≫ addB.hom) hρDEhom.symm

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
