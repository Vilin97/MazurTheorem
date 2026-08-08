/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import MazurTorsion.Upstream.AINTLIB.ForMathlib.AffineIdealQuotientPullbackUnit
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModulePullbackUnitComposition

/-!
# Pullback units on affine ideal-sheaf charts

The ideal-sheaf chart map is an ideal-quotient spectrum map followed by the
canonical affine-open spectrum isomorphism. Thus ideal annihilation makes the
pullback--pushforward unit invertible on the chart.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Pulling a restriction to an affine open back along its spectrum isomorphism
agrees with restriction along the canonical `fromSpec` map. -/
noncomputable def pullbackIsoSpecInvRestrictIso
    (F : X.Modules) (U : X.affineOpens) :
    (pullback U.2.isoSpec.inv).obj
          ((restrictFunctor U.1.ι).obj F) ≅
      @Scheme.Modules.restrict _ _ F U.2.fromSpec
        (IsAffineOpen.isOpenImmersion_fromSpec U.2) :=
  (restrictFunctorIsoPullback U.2.isoSpec.inv).symm.app
      ((restrictFunctor U.1.ι).obj F) ≪≫
    (restrictFunctorComp U.2.isoSpec.inv U.1.ι).symm.app F

/-- Ideal annihilation makes the pullback--pushforward unit invertible on an
affine ideal-sheaf chart. -/
theorem isIso_pullbackPushforward_unit_glueDataObjι
    (F : X.Modules) [F.IsQuasicoherent]
    (J : X.IdealSheafData) (U : X.affineOpens)
    (h : Module.IsTorsionBySet Γ(X, U.1)
      (moduleSpecΓFunctor.obj
        (@Scheme.Modules.restrict _ _ F U.2.fromSpec
          (IsAffineOpen.isOpenImmersion_fromSpec U.2)))
      (J.ideal U : Set Γ(X, U.1))) :
    IsIso
      ((pullbackPushforwardAdjunction
        (J.glueDataObjι U)).unit.app
          ((restrictFunctor U.1.ι).obj F)) := by
  let q := idealQuotientSpecMap (J.ideal U)
  let b := U.2.isoSpec.inv
  let FU := (restrictFunctor U.1.ι).obj F
  let H := @Scheme.Modules.restrict _ _ F U.2.fromSpec
    (IsAffineOpen.isOpenImmersion_fromSpec U.2)
  let e : (pullback b).obj FU ≅ H :=
    pullbackIsoSpecInvRestrictIso F U
  haveI hHQuasicoherent : H.IsQuasicoherent := by
    dsimp only [H]
    infer_instance
  haveI hQuotientUnit :
      IsIso ((pullbackPushforwardAdjunction q).unit.app H) := by
    dsimp only [q, H]
    exact isIso_pullbackPushforward_unit_affine_idealQuotient
      (@Scheme.Modules.restrict _ _ F U.2.fromSpec
        (IsAffineOpen.isOpenImmersion_fromSpec U.2))
      (J.ideal U) h
  haveI hPulledBackQuotientUnit :
      IsIso
        ((pullbackPushforwardAdjunction q).unit.app
          ((pullback b).obj FU)) :=
    NatTrans.isIso_app_of_iso
      (pullbackPushforwardAdjunction q).unit e
  haveI hb : IsIso b := by
    dsimp only [b]
    infer_instance
  change IsIso
    ((pullbackPushforwardAdjunction (q ≫ b)).unit.app FU)
  exact isIso_pullbackPushforward_unit_comp_of_isIso_right q b FU

end AlgebraicGeometry.Scheme.Modules
