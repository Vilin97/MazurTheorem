/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTildeTensorBaseChange
import MazurTorsion.Upstream.CurveDivisorDescent

/-!
# Tilde tensor addition on a common affine restriction

The affine tilde-level naturality square for deterministic divisor addition is specialized to a
genuine restriction from a compatible Dedekind affine chart to a nonempty affine subopen.  All
algebra, flat-epimorphism, fraction-field, and scalar-tower data are the canonical data induced by
restriction of sections.

The comparison still lands in the tensor of the two raw extended inverse-ideal tilde sheaves.  It
does not identify the affine comparison with the canonical pullback tensorator or with the legacy
overlap comparison, and it does not assert cross-chart or descent-data compatibility.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain
open AffineDivisorLocalization
open scoped AlgebraicGeometry TensorProduct

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForTildeRestriction (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

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

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
