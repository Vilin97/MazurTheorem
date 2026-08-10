/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTildeTensorPullbackSection
import MazurTorsion.Upstream.CurveDivisorDescent

/-!
# Tilde tensor addition on a common affine restriction

The affine tilde-level naturality square for deterministic divisor addition is specialized to a
genuine restriction from a compatible Dedekind affine chart to a nonempty affine subopen.  All
algebra, flat-epimorphism, fraction-field, and scalar-tower data are the canonical data induced by
restriction of sections.

The direct comparison still lands in the tensor of the two raw extended inverse-ideal tilde
sheaves.  A separate canonical-tensorator/factorwise path is evaluated on pullback-unit pure
tensor sections, but no equality between those two tensor comparisons is asserted.  The
per-divisor comparison is identified with the specified restriction comparison used by the
overlap tower, but no compatibility between that legacy comparison and the factorwise tensor
path, and no cross-chart or descent-data compatibility, is asserted.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain
open AffineDivisorLocalization
open AffineDivisorLocalization.CommonExtension
open scoped AlgebraicGeometry TensorProduct

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForTildeRestriction (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- On a genuine affine restriction, the overlap tower's specified restriction comparison is the
restriction-to-pullback comparison followed by the public affine tilde/scalar-extension path. -/
theorem localRestrictionIsoExtendedInverseIdeal_eq_viaExtendScalarsOnCommonAffineOpen
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U W : X.Opens) [Nonempty U] [Nonempty W]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
    letI := restrictionAlgebra X U W hWU
    letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
      restrictionTorsionFree X U W hWU
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsScalarTower Γ(X, U) Γ(X, W) X.functionField :=
      restrictionFunctionFieldTower X U W hWU
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
    letI : Algebra.IsEpi Γ(X, U) Γ(X, W) :=
      CommonExtension.algebraIsEpiOfOpenImmersion Γ(X, U) Γ(X, W)
    letI : Module.Flat Γ(X, U) Γ(X, W) :=
      CommonExtension.moduleFlatOfOpenImmersion Γ(X, U) Γ(X, W)
    let d := localDivisor X U hU h D
    CommonExtension.restrictionIsoExtendedInverseIdealOfIsOpenImmersion
          Γ(X, U) Γ(X, W) X.functionField d =
      (Scheme.Modules.restrictFunctorIsoPullback
          (CommonExtension.extensionMap Γ(X, U) Γ(X, W))).app
            (AffineDedekind.lineBundle Γ(X, U) X.functionField d).obj ≪≫
        CommonExtension.lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
          Γ(X, U) Γ(X, W) X.functionField d := by
  letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
  letI := restrictionAlgebra X U W hWU
  letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
    restrictionTorsionFree X U W hWU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsScalarTower Γ(X, U) Γ(X, W) X.functionField :=
    restrictionFunctionFieldTower X U W hWU
  letI : IsOpenImmersion
      (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
  letI : Algebra.IsEpi Γ(X, U) Γ(X, W) :=
    CommonExtension.algebraIsEpiOfOpenImmersion Γ(X, U) Γ(X, W)
  letI : Module.Flat Γ(X, U) Γ(X, W) :=
    CommonExtension.moduleFlatOfOpenImmersion Γ(X, U) Γ(X, W)
  let d := localDivisor X U hU h D
  exact CommonExtension.restrictionIsoExtendedInverseIdealOfIsOpenImmersion_eq_viaExtendScalars
    Γ(X, U) Γ(X, W) X.functionField d

/-- On a genuine affine restriction `U → W`, pullback of deterministic divisor addition agrees
with addition of the two raw extended inverse-ideal tilde sheaves, relative to the canonical
affine tilde/extension-of-scalars comparison. -/
theorem localLineBundleAddIso_pullbackViaExtendScalarsOnCommonAffineOpen
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U W : X.Opens) [Nonempty U] [Nonempty W]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
    letI := restrictionAlgebra X U W hWU
    letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
      restrictionTorsionFree X U W hWU
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsScalarTower Γ(X, U) Γ(X, W) X.functionField :=
      restrictionFunctionFieldTower X U W hWU
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
    letI : Algebra.IsEpi Γ(X, U) Γ(X, W) :=
      CommonExtension.algebraIsEpiOfOpenImmersion Γ(X, U) Γ(X, W)
    letI : Module.Flat Γ(X, U) Γ(X, W) :=
      CommonExtension.moduleFlatOfOpenImmersion Γ(X, U) Γ(X, W)
    let d := localDivisor X U hU h D
    let e := localDivisor X U hU h E
    (Scheme.Modules.pullback
        (CommonExtension.extensionMap Γ(X, U) Γ(X, W))).mapIso
          (ExplicitIdeal.lineBundleAddIso Γ(X, U) X.functionField d e) ≪≫
        CommonExtension.lineBundleTensorPullbackIsoExtendedInverseIdealsViaExtendScalars
          Γ(X, U) Γ(X, W) X.functionField d e =
      CommonExtension.lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
          Γ(X, U) Γ(X, W) X.functionField (d + e) ≪≫
        CommonExtension.extendedInverseIdealAddIso
          Γ(X, U) Γ(X, W) X.functionField d e := by
  letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
  letI := restrictionAlgebra X U W hWU
  letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
    restrictionTorsionFree X U W hWU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsScalarTower Γ(X, U) Γ(X, W) X.functionField :=
    restrictionFunctionFieldTower X U W hWU
  letI : IsOpenImmersion
      (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
  letI : Algebra.IsEpi Γ(X, U) Γ(X, W) :=
    CommonExtension.algebraIsEpiOfOpenImmersion Γ(X, U) Γ(X, W)
  letI : Module.Flat Γ(X, U) Γ(X, W) :=
    CommonExtension.moduleFlatOfOpenImmersion Γ(X, U) Γ(X, W)
  let d := localDivisor X U hU h D
  let e := localDivisor X U hU h E
  exact CommonExtension.lineBundleAddIso_pullback_viaExtendScalars
    Γ(X, U) Γ(X, W) X.functionField d e

/-- On the full spectrum of a compatible Dedekind affine chart, the canonical inverse pullback
tensorator followed by the two factorwise affine tilde/scalar-extension comparisons sends a
pullback-unit pure tensor section to the pure tensor section of the factorwise images.

This does not identify the factorwise comparison with the direct `ViaExtendScalars` tensor
comparison, the legacy restriction mate, or any cross-chart descent datum. -/
theorem
    localLineBundleTensorPullbackIsoViaCanonicalTensorator_hom_unit_tensorSectionOnCommonAffineOpen
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (U W : X.Opens) [Nonempty U] [Nonempty W]
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (h : AffineChart.DedekindOrderCompatibility X U hU)
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
    letI := restrictionAlgebra X U W hWU
    letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
      restrictionTorsionFree X U W hWU
    letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsFractionRing Γ(X, W) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X W hW
    letI : IsScalarTower Γ(X, U) Γ(X, W) X.functionField :=
      restrictionFunctionFieldTower X U W hWU
    letI : IsOpenImmersion
        (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) :=
      restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
    letI : Algebra.IsEpi Γ(X, U) Γ(X, W) :=
      CommonExtension.algebraIsEpiOfOpenImmersion Γ(X, U) Γ(X, W)
    letI : Module.Flat Γ(X, U) Γ(X, W) :=
      CommonExtension.moduleFlatOfOpenImmersion Γ(X, U) Γ(X, W)
    let d := localDivisor X U hU h D
    let e := localDivisor X U hU h E
    let V : (Spec (.of Γ(X, U))).Opens := ⊤
    let LD := (AffineDedekind.lineBundle Γ(X, U) X.functionField d).obj
    let LE := (AffineDedekind.lineBundle Γ(X, U) X.functionField e).obj
    ∀ (x : Γ(LD, V)) (y : Γ(LE, V)),
      let f := CommonExtension.extensionMap Γ(X, U) Γ(X, W)
      let TD := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of Γ(X, W))
        (ModuleCat.of Γ(X, W)
          (CommonExtension.extendedInverseIdeal
            Γ(X, U) Γ(X, W) X.functionField d))
      let TE := _root_.AlgebraicGeometry.tilde (R := CommRingCat.of Γ(X, W))
        (ModuleCat.of Γ(X, W)
          (CommonExtension.extendedInverseIdeal
            Γ(X, U) Γ(X, W) X.functionField e))
      let cD :=
        CommonExtension.lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
          Γ(X, U) Γ(X, W) X.functionField d
      let cE :=
        CommonExtension.lineBundlePullbackIsoExtendedInverseIdealViaExtendScalars
          Γ(X, U) Γ(X, W) X.functionField e
      let adj := Scheme.Modules.pullbackPushforwardAdjunction f
      (lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator
          Γ(X, U) Γ(X, W) X.functionField d e).hom.val.app
            (.op (f ⁻¹ᵁ V))
          ((adj.unit.app (LD ⊗ LE)).val.app (.op V)
            (ModularCurves.tensorSection LD LE V x y)) =
        ModularCurves.tensorSection TD TE (f ⁻¹ᵁ V)
          (cD.hom.val.app (.op (f ⁻¹ᵁ V))
            ((adj.unit.app LD).val.app (.op V) x))
          (cE.hom.val.app (.op (f ⁻¹ᵁ V))
            ((adj.unit.app LE).val.app (.op V) y)) := by
  letI : IsDedekindDomain Γ(X, U) := h.isDedekindDomain
  letI := restrictionAlgebra X U W hWU
  letI : Module.IsTorsionFree Γ(X, U) Γ(X, W) :=
    restrictionTorsionFree X U W hWU
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(X, W) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X W hW
  letI : IsScalarTower Γ(X, U) Γ(X, W) X.functionField :=
    restrictionFunctionFieldTower X U W hWU
  letI : IsOpenImmersion
      (CommonExtension.extensionMap Γ(X, U) Γ(X, W)) :=
    restrictionExtensionMapIsOpenImmersion X U W hU hW hWU
  letI : Algebra.IsEpi Γ(X, U) Γ(X, W) :=
    CommonExtension.algebraIsEpiOfOpenImmersion Γ(X, U) Γ(X, W)
  letI : Module.Flat Γ(X, U) Γ(X, W) :=
    CommonExtension.moduleFlatOfOpenImmersion Γ(X, U) Γ(X, W)
  let d := localDivisor X U hU h D
  let e := localDivisor X U hU h E
  let V : (Spec (.of Γ(X, U))).Opens := ⊤
  dsimp only
  intro x y
  exact
    lineBundleTensorPullbackIsoExtendedInverseIdealsViaCanonicalTensorator_hom_unit_tensorSection
      Γ(X, U) Γ(X, W) X.functionField d e V x y

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
