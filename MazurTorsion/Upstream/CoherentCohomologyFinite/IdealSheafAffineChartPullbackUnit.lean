/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuotientPullbackUnit
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePullbackUnitComposition
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The pullback unit on an affine ideal-sheaf chart

On an affine open `U`, the ideal-sheaf chart map is the quotient-spectrum
map followed by the canonical isomorphism `Spec Γ(U) ≅ U`.  This file
transports the affine quotient theorem through that isomorphism.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

lemma affineOpenProperty (U : X.affineOpens) :
    IsAffineOpen U.1 := by
  change IsAffine (↑U.1 : Scheme)
  infer_instance

/--
Pulling the restriction of a module to an affine open back along the
canonical spectrum isomorphism agrees with restricting directly along
`fromSpec`.
-/
noncomputable def pullbackIsoSpecInvRestrictIso
    (F : X.Modules) (U : X.affineOpens) :
    (pullback (affineOpenProperty U).isoSpec.inv).obj
          ((restrictFunctor U.1.ι).obj F) ≅
      F.restrict (affineOpenProperty U).fromSpec :=
  (restrictFunctorIsoPullback (affineOpenProperty U).isoSpec.inv).symm.app
      ((restrictFunctor U.1.ι).obj F) ≪≫
    (restrictFunctorComp
      (affineOpenProperty U).isoSpec.inv U.1.ι).symm.app F

/--
If the affine sections are annihilated by the local ideal, then the
pullback--pushforward unit for the ideal-sheaf affine chart map is an
isomorphism.
-/
theorem isIso_pullbackPushforward_unit_glueDataObjι
    (F : X.Modules) [F.IsQuasicoherent]
    (J : X.IdealSheafData) (U : X.affineOpens)
    (h : Module.IsTorsionBySet Γ(X, U.1)
      (moduleSpecΓFunctor.obj
        (F.restrict (affineOpenProperty U).fromSpec))
      (J.ideal U : Set Γ(X, U.1))) :
    IsIso
      ((pullbackPushforwardAdjunction
        (J.glueDataObjι U)).unit.app
          ((restrictFunctor U.1.ι).obj F)) := by
  let q :=
    idealQuotientSpecMap (J.ideal U)
  let b := (affineOpenProperty U).isoSpec.inv
  let FU := (restrictFunctor U.1.ι).obj F
  let H := F.restrict (affineOpenProperty U).fromSpec
  let e :
      (pullback b).obj FU ≅ H :=
    pullbackIsoSpecInvRestrictIso F U
  haveI hHQuasicoherent : H.IsQuasicoherent := by
    dsimp only [H]
    infer_instance
  haveI hQuotientUnit :
      IsIso
        ((pullbackPushforwardAdjunction q).unit.app H) := by
    dsimp only [q, H]
    exact
      isIso_pullbackPushforward_unit_affine_idealQuotient
        (F.restrict (affineOpenProperty U).fromSpec) (J.ideal U) h
  haveI hPulledBackQuotientUnit :
      IsIso
        ((pullbackPushforwardAdjunction q).unit.app
          ((pullback b).obj FU)) :=
    NatTrans.isIso_app_of_iso
      (pullbackPushforwardAdjunction q).unit e
  haveI hb : IsIso b := by
    dsimp only [b]
    infer_instance
  change
    IsIso
      ((pullbackPushforwardAdjunction
        (q ≫ b)).unit.app FU)
  exact
    isIso_pullbackPushforward_unit_comp_of_isIso_right
      q b FU

end AlgebraicGeometry.Scheme.Modules
