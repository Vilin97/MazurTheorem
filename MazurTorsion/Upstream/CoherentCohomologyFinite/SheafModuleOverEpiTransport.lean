/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOverEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoproductEpiNaturalIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Epimorphic families across open restriction models

The equivalence between modules on an open subscheme and modules on its
slice site transports epimorphic coproduct families in both directions.
-/

open CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- An epimorphic coproduct family on the slice site remains epimorphic
after passing back to geometric restriction on the open subscheme. -/
theorem sigmaDesc_restrict_epi_of_over
    {ι : Type u}
    (A : ι → X.Modules) (M : X.Modules)
    (component : ∀ a, A a ⟶ M)
    (h :
      Epi
        (Limits.Sigma.desc
          (fun a => (component a).over U))) :
    Epi
      (Limits.Sigma.desc
        (fun a =>
          (restrictFunctor U.ι).map
            (component a))) := by
  letI : Limits.PreservesColimitsOfSize.{u, u}
      (overEquivalence.{u, u} U).functor :=
    (overEquivalence.{u, u} U).toAdjunction.leftAdjoint_preservesColimits
  letI : (overEquivalence.{u, u} U).functor.IsEquivalence :=
    CategoryTheory.Equivalence.isEquivalence_functor
      (overEquivalence.{u, u} U)
  exact
    @MazurTorsion.AlgebraicGeometry.CoherentCohomology.sigmaDesc_map_epi_of_comp_equivalence
      X.Modules _ ((↑U : Scheme).Modules) _
      (SheafOfModules (X.ringCatSheaf.over U)) _
      ι (restrictFunctor U.ι)
      (overEquivalence.{u, u} U).functor
      (CategoryTheory.Equivalence.isEquivalence_functor
        (overEquivalence.{u, u} U))
      (SheafOfModules.overFunctor X.ringCatSheaf U)
      (restrictOverNatIso U) A M component _ _ _ h

/-- An epimorphic coproduct family for open restriction remains
epimorphic after identifying restriction with geometric pullback. -/
theorem sigmaDesc_pullback_epi_of_restrict
    {Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f]
    {ι : Type u}
    (A : ι → Y.Modules) (M : Y.Modules)
    (component : ∀ a, A a ⟶ M)
    (h :
      Epi
        (Limits.Sigma.desc
          (fun a =>
            (restrictFunctor f).map
              (component a)))) :
    Epi
      (Limits.Sigma.desc
        (fun a =>
          (pullback f).map
            (component a))) := by
  exact
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.sigmaDesc_map_epi_of_natIso
      (pullback f) (restrictFunctor f)
      (restrictFunctorIsoPullback f).symm
      A M component h

/-- An epimorphic coproduct family on the slice site of an open remains
epimorphic after geometric pullback to that open subscheme. -/
theorem sigmaDesc_pullback_epi_of_over
    {ι : Type u}
    (A : ι → X.Modules) (M : X.Modules)
    (component : ∀ a, A a ⟶ M)
    (h :
      Epi
        (Limits.Sigma.desc
          (fun a => (component a).over U))) :
    Epi
      (Limits.Sigma.desc
        (fun a =>
          (pullback U.ι).map
            (component a))) := by
  apply sigmaDesc_pullback_epi_of_restrict U.ι
  exact sigmaDesc_restrict_epi_of_over U A M component h

end AlgebraicGeometry.Scheme.Modules
