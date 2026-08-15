/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceStandardCover

/-!
# Coordinate ratios on the standard affine charts

On the chart `D₊(Xⱼ) = Spec (S_(Xⱼ))₀`, the overlap with
`D₊(Xᵢ)` is the distinguished open cut out by the regular function
`Xᵢ / Xⱼ`.  These are the denominators used in the Serre
global-generation argument.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MvPolynomial HomogeneousLocalization

universe u

variable (k : Type u) [CommRing k] (d : ℕ)

/-- The standard affine cover, viewed as an open cover.  Its `i`-th object
is definitionally the spectrum of the degree-zero localization at `Xᵢ`. -/
abbrev standardAffineCover :
    (scheme k d).OpenCover :=
  (standardAffineOpenCover k d).openCover

/-- The regular coordinate ratio `Xᵢ / Xⱼ` on the `j`-th standard chart. -/
def chartRatio (i j : Fin (d + 1)) :
    Away (homogeneousGrading k d) (coordinate k j) :=
  Away.isLocalizationElem
    (coordinate_mem_degreeOne k j)
    (coordinate_mem_degreeOne k i)

/-- The inverse image of the `i`-th standard chart in the `j`-th affine
chart is the distinguished open `D(Xᵢ/Xⱼ)`. -/
lemma standardAffineCover_preimage_standardChart
    (i j : Fin (d + 1)) :
    (standardAffineOpenCover k d).f j ⁻¹ᵁ standardChart k i =
      PrimeSpectrum.basicOpen (chartRatio k d i j) := by
  exact Proj.awayι_preimage_basicOpen
    (𝒜 := homogeneousGrading k d)
    (coordinate_mem_degreeOne k j) Nat.zero_lt_one
    (coordinate_mem_degreeOne k i) Nat.zero_lt_one

/-- Localizing the `j`-th chart at `Xᵢ/Xⱼ` gives the degree-zero
localization at `XⱼXᵢ`. -/
instance chartRatio_isLocalization
    (i j : Fin (d + 1)) :
    letI := (awayMap
      (homogeneousGrading k d)
      (coordinate_mem_degreeOne k i)
      (rfl :
        coordinate k j * coordinate k i =
          coordinate k j * coordinate k i)).toAlgebra
    IsLocalization.Away (chartRatio k d i j)
      (Away (homogeneousGrading k d)
        (coordinate k j * coordinate k i)) := by
  dsimp only [chartRatio]
  exact Away.isLocalization_mul
    (coordinate_mem_degreeOne k j)
    (coordinate_mem_degreeOne k i)
    rfl Nat.one_ne_zero

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
