/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveStandardChartPoint
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveFactorizationChoice

/-!
# A projective coordinate chart through a relative-projective point

For a chosen relative projective factorization and a point of its
source, pull back a standard coordinate chart containing the image
point in absolute projective space.
-/

open AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
namespace IsRelativeProjectiveFactorization

variable {k : Type} [CommRing k]
  {X S : Scheme.{0}}
  {s : S ⟶ Spec (CommRingCat.of k)}
  {f : X ⟶ S}

/-- A chosen projective-coordinate index through `x`. -/
def chosenProjectiveChartIndexAt
    (h : IsRelativeProjectiveFactorization s f)
    (x : X) : Fin (h.chosenDimension + 1) :=
  standardChartIndexAt k h.chosenDimension
    (h.chosenProjectiveMap x)

/-- The inverse image of the chosen standard chart. -/
def chosenProjectiveChartAt
    (h : IsRelativeProjectiveFactorization s f)
    (x : X) : X.Opens :=
  h.chosenProjectiveMap ⁻¹ᵁ
    standardChart k (h.chosenProjectiveChartIndexAt x)

/-- The chosen source point belongs to its projective-coordinate
chart. -/
theorem mem_chosenProjectiveChartAt
    (h : IsRelativeProjectiveFactorization s f)
    (x : X) :
    x ∈ h.chosenProjectiveChartAt x :=
  mem_standardChartIndexAt
    k h.chosenDimension (h.chosenProjectiveMap x)

end IsRelativeProjectiveFactorization
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
