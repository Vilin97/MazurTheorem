/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverEquivalence

/-!
# Presentations on an open and on its slice site

The equivalence between module sheaves on an open subscheme and module
sheaves on the corresponding slice site transports global
presentations.  This is the final categorical step needed to turn affine
presentations into Mathlib's local finite-presentation data.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- The open-slice equivalence preserves all colimits. -/
theorem overEquivalencePreservesColimits :
    Limits.PreservesColimitsOfSize.{u, u}
      (overEquivalence U).functor :=
  (overEquivalence U).toAdjunction.leftAdjoint_preservesColimits

/--
A presentation of the geometric restriction to an open gives a
presentation of ordinary slice-site restriction.
-/
noncomputable def Presentation.overOfRestrict
    (M : X.Modules)
    (P : (M.restrict U.ι).Presentation) :
    (M.over U).Presentation :=
  let P' :=
    @SheafOfModules.Presentation.map
      _ _ _ _ _ _ _ _ _ _ _ _ _ P
      (overEquivalence U).functor
      (overEquivalencePreservesColimits U)
      (unitOverIso U).symm
  @SheafOfModules.Presentation.ofIsIso.{u, u, u}
    _ _ _ _ _ _ _ _ (restrictOverIso U M).hom
      (restrictOverIso U M).isIso_hom P'

@[simp]
theorem Presentation.overOfRestrict_generators_I
    (M : X.Modules)
    (P : (M.restrict U.ι).Presentation) :
    (Presentation.overOfRestrict U M P).generators.I =
      P.generators.I :=
  rfl

@[simp]
theorem Presentation.overOfRestrict_relations_I
    (M : X.Modules)
    (P : (M.restrict U.ι).Presentation) :
    (Presentation.overOfRestrict U M P).relations.I =
      P.relations.I :=
  rfl

/-- Finiteness is preserved when a presentation is moved to the slice. -/
instance Presentation.overOfRestrict_isFinite
    (M : X.Modules)
    (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    (Presentation.overOfRestrict U M P).IsFinite where
  isFiniteType_generators := by
    refine
      SheafOfModules.GeneratingSections.IsFiniteType.mk
        (σ := (Presentation.overOfRestrict U M P).generators) ?_
    rw [Presentation.overOfRestrict_generators_I U M P]
    exact hP.isFiniteType_generators.finite
  isFiniteType_relations := by
    refine
      SheafOfModules.GeneratingSections.IsFiniteType.mk
        (σ := (Presentation.overOfRestrict U M P).relations) ?_
    rw [Presentation.overOfRestrict_relations_I U M P]
    exact hP.isFiniteType_relations.finite

end AlgebraicGeometry.Scheme.Modules
