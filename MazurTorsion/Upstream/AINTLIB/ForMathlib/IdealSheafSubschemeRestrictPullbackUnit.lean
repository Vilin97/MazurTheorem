/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.IdealSheafAffineChartPullbackUnit
import MazurTorsion.Upstream.AINTLIB.ForMathlib.IdealSheafSubschemeAffineChart

/-!
# Pullback units for restricted ideal-sheaf subschemes

The restriction of the global subscheme inclusion to an affine open is,
up to an isomorphism of its source, the affine ideal-quotient chart map.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Local ideal annihilation makes the pullback--pushforward unit for the
restricted ideal-sheaf subscheme inclusion invertible. -/
theorem isIso_pullbackPushforward_unit_subschemeι_restrict
    (F : X.Modules) [F.IsQuasicoherent]
    (J : X.IdealSheafData) (U : X.affineOpens)
    (h : Module.IsTorsionBySet Γ(X, U.1)
      (moduleSpecΓFunctor.obj
        (@Scheme.Modules.restrict _ _ F U.2.fromSpec
          (IsAffineOpen.isOpenImmersion_fromSpec U.2)))
      (J.ideal U : Set Γ(X, U.1))) :
    IsIso
      ((pullbackPushforwardAdjunction
        (J.subschemeι ∣_ U.1)).unit.app
          ((restrictFunctor U.1.ι).obj F)) := by
  let a := (J.subschemeAffineChartIso U).hom
  let g := J.subschemeι ∣_ U.1
  let FU := (restrictFunctor U.1.ι).obj F
  haveI ha : IsIso a := by
    dsimp only [a]
    infer_instance
  haveI hChartUnit :
      IsIso
        ((pullbackPushforwardAdjunction
          (J.glueDataObjι U)).unit.app FU) :=
    isIso_pullbackPushforward_unit_glueDataObjι F J U h
  haveI hCompositeUnit :
      IsIso
        ((pullbackPushforwardAdjunction
          (a ≫ g)).unit.app FU) := by
    rw [J.subschemeAffineChartIso_hom_restrict U]
    exact hChartUnit
  exact isIso_pullbackPushforward_unit_of_comp_of_isIso_left a g FU

end AlgebraicGeometry.Scheme.Modules
