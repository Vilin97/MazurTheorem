/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.PresentationFiniteMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafScalar

/-!
# Pulling back presentations of scheme modules

Module-sheaf pullback is a left adjoint, hence preserves colimits, and
it carries the structure module to the structure module.  Therefore it
maps presentations by free module sheaves to presentations with the
same generator and relation index types.
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Scheme-module pullback preserves all colimits of the ambient
universe. -/
theorem pullbackPreservesColimits :
    PreservesColimitsOfSize.{u, u} (pullback f) :=
  (pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits

/-- Pull a global presentation back along a scheme morphism. -/
noncomputable def Presentation.pullback
    {M : Y.Modules} (P : M.Presentation) :
    ((Scheme.Modules.pullback f).obj M).Presentation :=
  @SheafOfModules.Presentation.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (Scheme.Modules.pullback f)
    (pullbackPreservesColimits f)
    (MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar.pullbackUnitIso f).symm

@[simp]
theorem Presentation.pullback_generators_I
    {M : Y.Modules} (P : M.Presentation) :
    (Presentation.pullback f P).generators.I = P.generators.I :=
  rfl

@[simp]
theorem Presentation.pullback_relations_I
    {M : Y.Modules} (P : M.Presentation) :
    (Presentation.pullback f P).relations.I = P.relations.I :=
  rfl

/-- A finite presentation remains finite after pullback. -/
instance Presentation.pullback_isFinite
    {M : Y.Modules} (P : M.Presentation) [hP : P.IsFinite] :
    (Presentation.pullback f P).IsFinite where
  isFiniteType_generators := by
    refine
      SheafOfModules.GeneratingSections.IsFiniteType.mk
        (σ := (Presentation.pullback f P).generators) ?_
    rw [Presentation.pullback_generators_I f P]
    exact hP.isFiniteType_generators.finite
  isFiniteType_relations := by
    refine
      SheafOfModules.GeneratingSections.IsFiniteType.mk
        (σ := (Presentation.pullback f P).relations) ?_
    rw [Presentation.pullback_relations_I f P]
    exact hP.isFiniteType_relations.finite

end AlgebraicGeometry.Scheme.Modules
