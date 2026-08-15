/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.PresentationFiniteMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverPresentation

/-!
# Moving slice-site presentations to open subschemes

`SheafOverPresentation` transports a presentation from a geometric open
restriction to the corresponding slice site.  This file records the
inverse transport through the same equivalence.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- The inverse functor of the open-slice equivalence preserves all
colimits. -/
theorem overEquivalenceInversePreservesColimits :
    PreservesColimitsOfSize.{u, u}
      (overEquivalence U).inverse :=
  (overEquivalence U).symm.toAdjunction.leftAdjoint_preservesColimits

/-- The inverse open-slice equivalence carries the slice-site structure
module back to the structure module on the open subscheme. -/
noncomputable def unitFromOverIso :
    SheafOfModules.unit (↑U : Scheme).ringCatSheaf ≅
      (overEquivalence U).inverse.obj
        (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (overEquivalence U).unitIso.app
      (SheafOfModules.unit (↑U : Scheme).ringCatSheaf) ≪≫
    (overEquivalence U).inverse.mapIso (unitOverIso U)

/-- Applying the inverse open-slice equivalence to ordinary slice
restriction recovers geometric restriction. -/
noncomputable def restrictFromOverIso (M : X.Modules) :
    (overEquivalence U).inverse.obj (M.over U) ≅
      M.restrict U.ι :=
  ((overEquivalence U).unitIso.app (M.restrict U.ι) ≪≫
    (overEquivalence U).inverse.mapIso
      (restrictOverIso U M)).symm

/--
A presentation on the slice site over `U` gives a presentation of the
geometric restriction to the open subscheme `U`.
-/
noncomputable def Presentation.restrictOfOver
    (M : X.Modules) (P : (M.over U).Presentation) :
    (M.restrict U.ι).Presentation :=
  let P' :=
    @SheafOfModules.Presentation.map
      _ _ _ _ _ _ _ _ _ _ _ _ _ P
      (overEquivalence U).inverse
      (overEquivalenceInversePreservesColimits U)
      (unitFromOverIso U)
  @SheafOfModules.Presentation.ofIsIso.{u, u, u}
    _ _ _ _ _ _ _ _ (restrictFromOverIso U M).hom
      (restrictFromOverIso U M).isIso_hom P'

/-- Finiteness is preserved when a slice-site presentation is moved to
the geometric open subscheme. -/
instance Presentation.restrictOfOver_isFinite
    (M : X.Modules) (P : (M.over U).Presentation) [P.IsFinite] :
    (Presentation.restrictOfOver U M P).IsFinite := by
  letI : PreservesColimitsOfSize.{u, u}
      (overEquivalence U).inverse :=
    overEquivalenceInversePreservesColimits U
  letI : IsIso (restrictFromOverIso U M).hom :=
    (restrictFromOverIso U M).isIso_hom
  dsimp only [Presentation.restrictOfOver]
  constructor
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance

end AlgebraicGeometry.Scheme.Modules
