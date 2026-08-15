/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistSectionCechComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistStandardCechFiniteness

/-!
# Homology of the standard-cover free resolution against a Serre twist

The contravariant Hom complex of the normalized standard-cover free-sheaf
resolution is transported to the explicit Laurent Čech complex.
-/

open CategoryTheory AlgebraicGeometry


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology

local instance projectiveSpaceOverQForResolution (d : ℕ) :
    (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
  ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩

/-- The Hom complex of the normalized free-sheaf resolution of the
standard cover is the Laurent-coordinate standard-cover complex. -/
def standardCoverContravariantHomCocomplexIso
    (d : ℕ) (m : ℤ)
    (hchart : IntegerChartCoordinatesIndependent d m) :
    contravariantHomCocomplex (standardChart ℚ)
        (Geometric.moduleSheaf (OInt ℚ d m)) ≅
      standardCoverOIntCechComplex d m :=
  (contravariantHomCocomplexIsoSectionPiCech
    (standardChart ℚ)
    (Geometric.moduleSheaf (OInt ℚ d m))).trans <|
      standardCoverSectionPiCechComplexIsoStandardCech
        d m
        (standardCoverCoordinatesNatural_of_chart_independent
          d m hchart)

/-- Every homology module of the standard-cover contravariant Hom complex
against an integer Serre twist is finite-dimensional. -/
theorem standardCoverContravariantHomCocomplexHomology_finite
    (d : ℕ) (m : ℤ)
    (hchart : IntegerChartCoordinatesIndependent d m)
    (n : ℕ) :
    Module.Finite ℚ
      ((contravariantHomCocomplex (standardChart ℚ)
        (Geometric.moduleSheaf (OInt ℚ d m))).homology n) := by
  let e :=
    (HomologicalComplex.homologyFunctor
      (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
        (standardCoverContravariantHomCocomplexIso
          d m hchart)
  exact
    (Module.Finite.equiv_iff e.toLinearEquiv.symm).mp
      (standardCoverOIntCechHomology_finite d m n)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
