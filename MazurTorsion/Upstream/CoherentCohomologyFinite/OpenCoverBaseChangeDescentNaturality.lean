/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentBaseChangeFunctor

/-!
# Effective descent and pullback of an open cover

Restriction to cover descent data identifies pullback along the canonical
map between glued covers with the chartwise base-change functor.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {S T : Scheme.{0}} (𝒰 : S.OpenCover) (f : T ⟶ S)

private abbrev D := 𝒰.gluedCover

private abbrev D' := gluedCover (𝒰.pullback₁ f)

/--
After restriction to effective descent data, pullback along the map
between the glued covers is the canonical base-change functor.
-/
noncomputable def restrictionBaseChangeNatIso :
    pullback (baseChangeGluedMap 𝒰 f) ⋙
        restrictionFunctor (D := D' 𝒰 f) ≅
      restrictionFunctor (D := D 𝒰) ⋙
        baseChangeFunctor 𝒰 f :=
  (pullback (baseChangeGluedMap 𝒰 f) ⋙
      restrictionFunctor (D := D' 𝒰 f)).leftUnitor.symm ≪≫
    Functor.isoWhiskerRight
      (restrictionGlueIso (D := D 𝒰))
      (pullback (baseChangeGluedMap 𝒰 f) ⋙
        restrictionFunctor (D := D' 𝒰 f)) ≪≫
    Functor.associator
      (restrictionFunctor (D := D 𝒰))
      (glueFunctor (D := D 𝒰))
      (pullback (baseChangeGluedMap 𝒰 f) ⋙
        restrictionFunctor (D := D' 𝒰 f)) ≪≫
    Functor.isoWhiskerLeft
      (restrictionFunctor (D := D 𝒰))
      (Functor.associator
        (glueFunctor (D := D 𝒰))
        (pullback (baseChangeGluedMap 𝒰 f))
        (restrictionFunctor (D := D' 𝒰 f))).symm ≪≫
    Functor.isoWhiskerLeft
      (restrictionFunctor (D := D 𝒰))
      (globalBaseChangeNatIso 𝒰 f)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData
