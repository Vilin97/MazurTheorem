/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistTransition

/-!
# A standard projective chart through a point

The finite standard affine cover supplies a canonical (choice-based)
coordinate index whose chart contains any given point of projective
space.
-/

open AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

/-- A chosen standard-coordinate chart containing a projective point. -/
def standardChartIndexAt
    (x : scheme k d) : Fin (d + 1) :=
  (cover k d).idx x

/-- The chosen coordinate chart does contain the given point. -/
theorem mem_standardChartIndexAt
    (x : scheme k d) :
    x ∈ standardChart k (standardChartIndexAt k d x) := by
  let i := (cover k d).idx x
  obtain ⟨y, hy⟩ := (cover k d).covers x
  have hi : x ∈ standardChart k i := by
    rw [← hy]
    exact y.2
  simpa only [standardChartIndexAt, i] using hi

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
