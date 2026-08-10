/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AffineDivisorTensorBaseChange
import MazurTorsion.Upstream.CurveDivisorDescent

/-!
# Tensor addition on a common affine restriction

The fixed tensor-to-sum equivalence for divisor line-bundle modules commutes with restriction
from a compatible Dedekind affine chart to a nonempty affine subopen.  The scalar algebra,
function-field tower, flat epimorphism, and open immersion are all the canonical ones induced by
restriction of sections.

This is a raw module-level comparison.  It does not assert compatibility of tilde sheaves,
cross-chart descent maps, or a descended tensor-additive structure.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open IsDedekindDomain
open AffineDivisorLocalization
open scoped AlgebraicGeometry TensorProduct

/-- On a genuine restriction from a compatible Dedekind affine chart to a common nonempty
affine subopen, the fixed line-bundle-module tensor-to-sum equivalence commutes with scalar
extension and multiplication of the corresponding extended inverse ideals. -/
theorem localLineBundleModuleTensorAddEquiv_baseChangeOnCommonAffineOpen
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
    ((ExplicitIdeal.lineBundleModuleTensorAddEquiv
          Γ(X, U) X.functionField d e).baseChange Γ(X, U) Γ(X, W)).trans
        (CommonExtension.lineBundleModuleBaseChangeEquivExtendedInverseIdeal
          Γ(X, U) Γ(X, W) X.functionField (d + e)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange Γ(X, U) Γ(X, W)
          (AffineDedekind.lineBundleModule Γ(X, U) X.functionField d)
          (AffineDedekind.lineBundleModule Γ(X, U) X.functionField e)).trans
        ((TensorProduct.congr
            (CommonExtension.lineBundleModuleBaseChangeEquivExtendedInverseIdeal
              Γ(X, U) Γ(X, W) X.functionField d)
            (CommonExtension.lineBundleModuleBaseChangeEquivExtendedInverseIdeal
              Γ(X, U) Γ(X, W) X.functionField e)).trans
          (CommonExtension.extendedInverseIdealTensorAddEquiv
            Γ(X, U) Γ(X, W) X.functionField d e)) := by
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
  exact CommonExtension.lineBundleModuleTensorAddEquiv_baseChange
    Γ(X, U) Γ(X, W) X.functionField d e

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent
