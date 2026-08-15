/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCoefficientBasicOpen
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartRatioTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleScalarAutomorphism

/-!
# Coefficient extension on standard projective overlaps

The standard overlap over an extended coefficient ring maps canonically
to the corresponding overlap over the original ring.  This map preserves
the Serre transition unit.
-/


open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

variable {k R : Type} [CommRing k] [CommRing R]
variable (φ : k →+* R) (d : ℕ)

/--
The coefficient-extension map from the `ij` overlap over `R` to the
corresponding overlap over `k`.
-/
def coefficientOverlapMap
    (i j : Fin (d + 1)) :
    (glueData R d).V (i, j) ⟶
      (glueData k d).V (i, j) :=
  overlapHom R d i j ≫
    coefficientPairBasicOpenMap φ d i j ≫
    (openOverlapToBasicOpenIso k d i j).inv

/--
The coefficient overlap map is characterized by its factorization through
the corresponding pair basic opens.
-/
@[reassoc]
theorem coefficientOverlapMap_comp_overlapHom
    (i j : Fin (d + 1)) :
    coefficientOverlapMap φ d i j ≫
        overlapHom k d i j =
      overlapHom R d i j ≫
        coefficientPairBasicOpenMap φ d i j := by
  rw [coefficientOverlapMap,
    ← openOverlapToBasicOpenIso_hom k d i j]
  let e := openOverlapToBasicOpenIso k d i j
  change
    ((overlapHom R d i j ≫ coefficientPairBasicOpenMap φ d i j) ≫ e.inv) ≫
        e.hom = overlapHom R d i j ≫ coefficientPairBasicOpenMap φ d i j
  exact (e.eq_comp_inv).mp rfl

/-- Coefficient extension preserves the basic Serre overlap unit. -/
theorem pullbackGlobalUnit_coefficientOverlapMap
    (i j : Fin (d + 1)) :
    pullbackGlobalUnit
        (coefficientOverlapMap φ d i j)
        (overlapUnit k d i j) =
      overlapUnit R d i j := by
  apply Units.ext
  let sk :=
    (Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i * coordinate k j)).topIso.inv
      (Proj.awayToSection (homogeneousGrading k d)
        (coordinate k i * coordinate k j)
        (awayFraction k d i j))
  let sr :=
    (Proj.basicOpen (homogeneousGrading R d)
      (coordinate R i * coordinate R j)).topIso.inv
      (Proj.awayToSection (homogeneousGrading R d)
        (coordinate R i * coordinate R j)
        (awayFraction R d i j))
  change
    (coefficientOverlapMap φ d i j).appTop
        ((overlapHom k d i j).appTop sk) =
      (overlapHom R d i j).appTop sr
  change (coefficientOverlapMap φ d i j ≫ overlapHom k d i j).appTop sk = _
  refine (congrArg (fun f => f.appTop sk)
    (coefficientOverlapMap_comp_overlapHom φ d i j)).trans ?_
  change (overlapHom R d i j).appTop
    ((coefficientPairBasicOpenMap φ d i j).appTop sk) = _
  exact congrArg (overlapHom R d i j).appTop
    (coefficientPairBasicOpenMap_appTop_awayFraction φ d i j)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
