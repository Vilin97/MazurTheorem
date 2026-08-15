/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectivePushforwardCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseCoordinateNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistOpenOverlapTransition

/-!
# Coherence of relative-projective direct images

The Laurent coordinate naturality and integer-chart transition theorems
are now unconditional over every commutative ring.  They discharge the
two residual hypotheses in the relative-projective finite-presentation
theorem.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

/--
The direct image of a finite-type quasicoherent module under a
relative-projective morphism to a locally Noetherian rational scheme is
coherent.
-/
theorem pushforward_coherent_of_relativeProjectiveFactorization
    {Y X : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of ℚ)}
    {f : Y ⟶ X}
    [IsLocallyNoetherian X]
    (hprojective : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    CoherentModule ((Scheme.Modules.pushforward f).obj M) := by
  letI :
      ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_relativeProjectiveFactorization
      hprojective M
      (fun _ _ d m =>
        baseStandardCoverCoordinatesNatural _ d m)
      (fun _ _ d N =>
        integerOverChartCoordinateTransition _ d N)
  exact
    ⟨SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
        ((Scheme.Modules.pushforward f).obj M),
      SheafOfModules.instIsQuasicoherentOfIsFinitePresentation
        ((Scheme.Modules.pushforward f).obj M)⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
