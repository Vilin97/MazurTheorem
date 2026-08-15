/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceCoefficientBaseChange

/-!
# Coefficient extension of the projective overlap ratio

Coefficient extension on the homogeneous localization away from
`XᵢXⱼ` carries the standard ratio `Xᵢ/Xⱼ` to the same ratio over the
new coefficient ring.
-/


open AlgebraicGeometry HomogeneousLocalization

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable {k R : Type} [CommRing k] [CommRing R]
variable (φ : k →+* R) (d : ℕ)

/-- Coefficient extension on the homogeneous localization away from a
product of two projective coordinates. -/
def coefficientPairAwayMap
    (i j : Fin (d + 1)) :
    Away
        (homogeneousGrading k d)
        (coordinate k i * coordinate k j) →+*
      Away
        (homogeneousGrading R d)
        (coordinate R i * coordinate R j) :=
  homogeneousAwayMapTo
    (coefficientGradedHom φ d)
    (coordinate k i * coordinate k j)
    (coordinate R i * coordinate R j)
    (by simp)

/-- Coefficient extension preserves the degree-zero overlap ratio. -/
@[simp]
theorem coefficientPairAwayMap_awayFraction
    (i j : Fin (d + 1)) :
    coefficientPairAwayMap φ d i j
        (awayFraction k d i j) =
      awayFraction R d i j := by
  rw [awayFraction, awayFraction,
    coefficientPairAwayMap,
    homogeneousAwayMapTo_mk
      (ht := coordinate_mul_mem_degreeTwo R d i j)]
  congr 1
  simp

/-- Coefficient extension preserves the overlap ratio as a unit of the
homogeneous localization. -/
@[simp]
theorem coefficientPairAwayMap_awayUnit
    (i j : Fin (d + 1)) :
    Units.map
        (coefficientPairAwayMap φ d i j).toMonoidHom
        (awayUnit k d i j) =
      awayUnit R d i j := by
  apply Units.ext
  exact coefficientPairAwayMap_awayFraction φ d i j

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
