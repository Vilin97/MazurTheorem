/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowReduction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModulePullbackCoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProperCohomologyDevissage

/-!
# Coherence in the canonical support--Chow reduction

The canonical support module and its pullback to the Chow modification
are coherent.  This records the two applications of preservation of
finite presentation needed by the modification argument.
-/

open AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace CanonicalSupportThickening

variable {k : Type} [Field k] {X : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]
  {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]

/-- The module on the canonical support thickening is finitely
presented. -/
theorem modelModule_isFinitePresentation
    [IsLocallyNoetherian X]
    (A : CanonicalSupportThickening F) :
    A.modelModule.IsFinitePresentation := by
  exact
    Scheme.Modules.isFinitePresentation_pullback_of_isLocallyNoetherian
      A.inclusion F

/-- The module on the canonical support thickening is coherent. -/
theorem modelModule_coherent
    [IsLocallyNoetherian X]
    (A : CanonicalSupportThickening F) :
    CoherentModule A.modelModule := by
  letI : A.modelModule.IsFinitePresentation :=
    A.modelModule_isFinitePresentation
  exact
    ⟨SheafOfModules.instIsFiniteTypeOfIsFinitePresentation A.modelModule,
      SheafOfModules.instIsQuasicoherentOfIsFinitePresentation A.modelModule⟩

/-- Pulling the support module to its Chow modification preserves finite
presentation. -/
theorem chowPullback_isFinitePresentation
    (A : CanonicalSupportThickening F) :
    let P := A.chowModification (k := k) (f := f)
    ((Scheme.Modules.pullback P.toOriginal).obj
      A.modelModule).IsFinitePresentation := by
  dsimp only
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  letI : A.modelModule.IsFinitePresentation :=
    A.modelModule_isFinitePresentation
  exact
    Scheme.Modules.isFinitePresentation_pullback
      (A.chowModification (k := k) (f := f)).toOriginal
      A.modelModule

/-- The pullback of the support module to its Chow modification is
coherent. -/
theorem chowPullback_coherent
    (A : CanonicalSupportThickening F) :
    let P := A.chowModification (k := k) (f := f)
    CoherentModule
      ((Scheme.Modules.pullback P.toOriginal).obj
        A.modelModule) := by
  dsimp only
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  letI :
      ((Scheme.Modules.pullback
        (A.chowModification (k := k) (f := f)).toOriginal).obj
          A.modelModule).IsFinitePresentation :=
    A.chowPullback_isFinitePresentation
  exact
    ⟨SheafOfModules.instIsFiniteTypeOfIsFinitePresentation _,
      SheafOfModules.instIsQuasicoherentOfIsFinitePresentation _⟩

end CanonicalSupportThickening
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
