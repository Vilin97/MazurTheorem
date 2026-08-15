/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationAcyclicModel

/-!
# Support dévissage with support-adapted projective modifications

A single fixed projective modification need not have an isomorphism locus
meeting the support of every coherent module: a module may be supported
entirely in its exceptional complement.  Support dévissage naturally
allows the modification to depend on the module currently under study.

This file provides that more flexible wrapper.  It has the same proof as
the fixed-modification theorem, but permits choosing a modification adapted
to a generic point of the current support.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/--
Every coherent module has an acyclic model on some projective modification,
which may depend on the module.
-/
def HasVariableProjectiveAcyclicModels
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) : Prop :=
  ∀ (M : X.Modules), CoherentModule M →
    ∃ P : ProjectiveModification f,
      Nonempty (ModificationAcyclicModel P M)

/--
Support-adapted acyclic models imply finite rationalized cohomology for
every coherent module on a proper scheme.
-/
theorem rationalSheafHFinite_of_variableProjectiveAcyclicModels
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ))
    [IsProper f]
    (hmodels : HasVariableProjectiveAcyclicModels f)
    (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    RationalSheafHFinite M := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  apply
    rationalSheafHFinite_of_closedStalkSupport_comodels
      CoherentModule RationalSheafHFinite
  · intro Y hY
    obtain ⟨P, A⟩ := hmodels Y hY
    obtain ⟨A⟩ := A
    exact
      ⟨(Scheme.Modules.pushforward P.toOriginal).obj A.modelModule,
        A.comparison,
        A.pushforwardCohomologyFinite,
        A.kernelCoherent,
        A.cokernelCoherent,
        A.kernelSupportDrops,
        A.cokernelSupportDrops⟩
  · intro E hE
    exact hE
  · exact ⟨inferInstance, inferInstance⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
