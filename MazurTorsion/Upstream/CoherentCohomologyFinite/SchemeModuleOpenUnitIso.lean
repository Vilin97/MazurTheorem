/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenBaseChangeMate
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoAdjunction

/-!
# The adjunction unit over an isomorphism locus

The open base-change identity reduces the restriction of the unit
`M ⟶ f_* f^* M` to two invertible pieces: the unit for the restricted
morphism and the canonical pullback base-change isomorphism.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/--
If `f` is an isomorphism over `U`, then the pullback--pushforward unit becomes
an isomorphism after restriction to `U`.
-/
theorem isIso_restrict_pullbackPushforward_unit_of_isIso_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)]
    (M : Y.Modules) :
    IsIso
      ((restrictFunctor U.ι).map
        ((pullbackPushforwardAdjunction f).unit.app M)) := by
  letI : IsIso (pullbackRestrictMate f U) := by
    rw [pullbackRestrictMate_eq_baseChange]
    infer_instance
  let hbaseChange :
      IsIso ((pushforwardRestrictIso f U).hom.app
        ((pullback f).obj M)) :=
    (pushforwardRestrictIso f U).app ((pullback f).obj M) |>.isIso_hom
  let hmate :
      IsIso ((pullbackRestrictMate f U).app M) :=
    NatIso.isIso_app_of_isIso _ M
  let hmapMate :
      IsIso ((pushforward (f ∣_ U)).map
        ((pullbackRestrictMate f U).app M)) :=
    @Functor.map_isIso _ _ _ _ _ _
      (pushforward (f ∣_ U))
      ((pullbackRestrictMate f U).app M)
      hmate
  let hunit :
      IsIso ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        ((restrictFunctor U.ι).obj M)) :=
    pullbackPushforwardAdjunction_unit_app_isIso_of_isIso
      (f ∣_ U) ((restrictFunctor U.ι).obj M)
  let hright :
      IsIso
        ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
            ((restrictFunctor U.ι).obj M) ≫
          (pushforward (f ∣_ U)).map
            ((pullbackRestrictMate f U).app M)) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ hunit hmapMate
  let hcomposite :
      IsIso
        ((restrictFunctor U.ι).map
            ((pullbackPushforwardAdjunction f).unit.app M) ≫
          (pushforwardRestrictIso f U).hom.app
            ((pullback f).obj M)) := by
    rw [restrict_pullbackPushforward_unit_baseChange]
    exact hright
  exact
    @IsIso.of_isIso_comp_right _ _ _ _ _
      ((restrictFunctor U.ι).map
        ((pullbackPushforwardAdjunction f).unit.app M))
      ((pushforwardRestrictIso f U).hom.app
        ((pullback f).obj M))
      hbaseChange hcomposite

end AlgebraicGeometry.Scheme.Modules
