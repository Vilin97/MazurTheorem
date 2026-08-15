/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartAnchor
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCoverUnits

/-!
# Coordinate functions in projective chart descent

Fixing a homogeneous coordinate `Xᵣ`, its expression on the standard
chart `D₊(Xⱼ)` is the regular function `Xᵣ / Xⱼ`.  These chart functions,
and their powers, are the local components of the canonical map into a
positive Serre twist.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

/--
The `N`-th power of the coordinate ratio `Xᵣ / Xⱼ`, viewed as a global
function on the chart object used by the standard-cover glue datum.
-/
def coordinateChartFunction
    (N : ℕ) (r j : Fin (d + 1)) :
    Γ((glueData k d).U j, ⊤) :=
  (standardChart k j).topIso.inv
    (Proj.awayToSection
      (homogeneousGrading k d) (coordinate k j)
      (chartRatioElement k d r j ^ N))

/-- On the chart selected by the same coordinate, the coordinate ratio
is one. -/
@[simp]
lemma coordinateChartFunction_self
    (N : ℕ) (r : Fin (d + 1)) :
    coordinateChartFunction k d N r r = 1 := by
  rw [coordinateChartFunction,
    chartRatioElement_self k d r,
    one_pow]
  change
    (((standardChart k r).topIso.inv.hom.comp
      (Proj.awayToSection
        (homogeneousGrading k d)
        (coordinate k r)).hom) 1) = 1
  exact map_one _

/-- The zeroth coordinate power is the constant function one on every
chart. -/
@[simp]
lemma coordinateChartFunction_zero
    (r j : Fin (d + 1)) :
    coordinateChartFunction k d 0 r j = 1 := by
  rw [coordinateChartFunction, pow_zero]
  change
    (((standardChart k j).topIso.inv.hom.comp
      (Proj.awayToSection
        (homogeneousGrading k d)
        (coordinate k j)).hom) 1) = 1
  exact map_one _

/-- Coordinate chart functions are multiplicative in the exponent. -/
lemma coordinateChartFunction_add
    (N M : ℕ) (r j : Fin (d + 1)) :
    coordinateChartFunction k d (N + M) r j =
      coordinateChartFunction k d N r j *
        coordinateChartFunction k d M r j := by
  rw [coordinateChartFunction, coordinateChartFunction,
    coordinateChartFunction, pow_add]
  change
    (((standardChart k j).topIso.inv.hom.comp
      (Proj.awayToSection
        (homogeneousGrading k d)
        (coordinate k j)).hom)
      (chartRatioElement k d r j ^ N *
        chartRatioElement k d r j ^ M)) =
      ((standardChart k j).topIso.inv.hom.comp
        (Proj.awayToSection
          (homogeneousGrading k d)
          (coordinate k j)).hom)
          (chartRatioElement k d r j ^ N) *
        ((standardChart k j).topIso.inv.hom.comp
          (Proj.awayToSection
            (homogeneousGrading k d)
            (coordinate k j)).hom)
          (chartRatioElement k d r j ^ M)
  exact map_mul _ _ _

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
