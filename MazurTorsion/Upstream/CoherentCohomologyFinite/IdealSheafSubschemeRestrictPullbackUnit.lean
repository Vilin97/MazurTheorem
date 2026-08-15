/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.IdealSheafAffineChartPullbackUnit
import MazurTorsion.Upstream.CoherentCohomologyFinite.IdealSheafSubschemeAffineChart

/-!
# The pullback unit for a restricted ideal-sheaf subscheme

The restriction of the global subscheme inclusion to an affine open is,
after an isomorphism of its source, the affine quotient chart map.
Hence the affine annihilation theorem implies invertibility of its unit.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/--
On an affine open, annihilation by the local ideal makes the unit for the
restricted ideal-sheaf subscheme inclusion invertible.
-/
theorem isIso_pullbackPushforward_unit_subschemeι_restrict
    (F : X.Modules) [F.IsQuasicoherent]
    (J : X.IdealSheafData) (U : X.affineOpens)
    (h : Module.IsTorsionBySet Γ(X, U.1)
      (moduleSpecΓFunctor.obj
        (F.restrict (affineOpenProperty U).fromSpec))
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
    isIso_pullbackPushforward_unit_glueDataObjι
      F J U h
  haveI hCompositeUnit :
      IsIso
        ((pullbackPushforwardAdjunction
          (a ≫ g)).unit.app FU) := by
    rw [J.subschemeAffineChartIso_hom_restrict U]
    exact hChartUnit
  exact
    isIso_pullbackPushforward_unit_of_comp_of_isIso_left
      a g FU

end AlgebraicGeometry.Scheme.Modules
