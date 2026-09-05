/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.ProperCurveCechLowDegreeFinite
import MazurTorsion.Upstream.ProperCurveFiniteSupport

/-!
# Cohomology of strict support on a proper curve

This file is the cohomological consumer of the finite canonical-support
model. It turns finite global sections for strict support into canonical
degree-zero finiteness and, on a pointed curve, ordered degree-zero and
degree-one Cech finiteness.

The design boundary remains strict support. The missing full-support
comparison producer must reduce support before the closed-support induction
can use these declarations for an arbitrary coherent module.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
namespace CanonicalSupportThickening

/-- Canonical `H⁰` of a coherent strict-support module on a smooth proper
integral curve is finite-dimensional over the ground field. -/
theorem hZeroCanonical_finiteDimensional_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤) :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  exact hZeroCanonical_finiteDimensional_of_globalSections_module_finite
    K X f M
      (globalSections_module_finite_of_closedStalkSupport_lt_top
        K X f M A hM)

/-- A coherent strict-support module on a pointed smooth proper integral
curve has finite ordered base-Cech homology in degrees zero and one for every
linearly ordered affine cover. -/
theorem orderedBaseCechLowDegreeFinite_of_rationalSection_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    OrderedBaseCechLowDegreeFinite f U M := by
  exact
    orderedBaseCechLowDegreeFinite_of_rationalSection_of_globalSections_module_finite
      K X f s M U hU hUaff
        (globalSections_module_finite_of_closedStalkSupport_lt_top
          K X f M A hM)

end CanonicalSupportThickening
end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
