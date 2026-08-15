/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenBaseChangeMate

/-!
# Detecting a pullback unit after open base change

The open base-change formula identifies the restriction of a global
pullback--pushforward unit with the unit for the restricted morphism,
up to canonical isomorphisms.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/--
If the unit for a morphism restricted over an open is invertible, then
the restriction of the original unit to that open is invertible.
-/
theorem isIso_restrict_pullbackPushforward_unit_of_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (M : Y.Modules)
    [IsIso
      ((pullbackPushforwardAdjunction
        (f ∣_ U)).unit.app
          ((restrictFunctor U.ι).obj M))] :
    IsIso
      ((restrictFunctor U.ι).map
        ((pullbackPushforwardAdjunction f).unit.app M)) := by
  haveI hMate : IsIso (pullbackRestrictMate f U) := by
    rw [pullbackRestrictMate_eq_baseChange]
    infer_instance
  haveI hBaseChange :
      IsIso
        ((pushforwardRestrictIso f U).hom.app
          ((pullback f).obj M)) :=
    (pushforwardRestrictIso f U).app
      ((pullback f).obj M) |>.isIso_hom
  haveI hMappedMate :
      IsIso
        ((pushforward (f ∣_ U)).map
          ((pullbackRestrictMate f U).app M)) :=
    inferInstance
  haveI hRight :
      IsIso
        ((pullbackPushforwardAdjunction
            (f ∣_ U)).unit.app
              ((restrictFunctor U.ι).obj M) ≫
          (pushforward (f ∣_ U)).map
            ((pullbackRestrictMate f U).app M)) :=
    IsIso.comp_isIso'
      (inferInstanceAs
        (IsIso
          ((pullbackPushforwardAdjunction
            (f ∣_ U)).unit.app
              ((restrictFunctor U.ι).obj M))))
      hMappedMate
  haveI hComposite :
      IsIso
        ((restrictFunctor U.ι).map
            ((pullbackPushforwardAdjunction f).unit.app M) ≫
          (pushforwardRestrictIso f U).hom.app
            ((pullback f).obj M)) := by
    rw [restrict_pullbackPushforward_unit_baseChange]
    exact hRight
  exact
    @IsIso.of_isIso_comp_right _ _ _ _ _
      ((restrictFunctor U.ι).map
        ((pullbackPushforwardAdjunction f).unit.app M))
      ((pushforwardRestrictIso f U).hom.app
        ((pullback f).obj M))
      hBaseChange hComposite

end AlgebraicGeometry.Scheme.Modules
