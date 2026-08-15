/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerScalarNormalization

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- Finish the fully raw second chart route by trivializing the inverse
integer transition.  The cast stays literal so downstream pointwise
assembly never has to unfold its large abbreviation. -/
theorem projectiveIntegerRawSecondScalar_trivialize
    (m : ℤ) (i j : Fin (d + 1)) :
    ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation k d i j)).inv.app
        (OInt k d m) ≫
        projectiveIntegerSecondChartLegCore k d m i j) ≫
      ((integerTransitionFamily k d m i j).inv ≫
        (pullbackUnitIso ((glueData k d).f i j)).hom) =
      ((Scheme.Modules.pullbackCongr
          (projectiveIntegerOverlapEquation k d i j)).inv.app
          (OInt k d m) ≫
        projectiveIntegerSecondChartLegCore k d m i j) ≫
      ((pullbackUnitIso
          ((glueData k d).t i j ≫
            (glueData k d).f j i)).hom ≫
        endomorphism (((overlapUnit k d i j) ^ m).inv)) := by
  dsimp only [integerTransitionFamily]
  exact morphism_eq_whisker_left
    ((Scheme.Modules.pullbackCongr
        (projectiveIntegerOverlapEquation k d i j)).inv.app
        (OInt k d m) ≫
      projectiveIntegerSecondChartLegCore k d m i j)
    (integerTransition_inv_trivialize k d m i j)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
