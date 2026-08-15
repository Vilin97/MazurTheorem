/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModification
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveFactorizationPointChart
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeIsomorphismOpenShrink

/-!
# Shrinking a modification open to one projective chart

Let a projective modification be an isomorphism over an open `U` of
the original scheme.  A point of `U` lifts uniquely to the model.  We
choose a standard projective chart containing its image under a chosen
relative projective factorization, then transport that chart back to a
smaller open of the original scheme.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace ProjectiveModification

open ProjectiveSpace
open ProjectiveSpace.IsRelativeProjectiveFactorization

variable {k : Type} [CommRing k]
  {X : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of k)}

/-- The unique point of the model over a point of an isomorphism
open. -/
def projectiveChartSourcePoint
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) : P.model :=
  (P.toOriginal ⁻¹ᵁ U).ι
    ((inv (P.toOriginal ∣_ U)) x)

/-- The projective-coordinate chart selected at the lifted point. -/
def projectiveChartOpenAt
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) : P.model.Opens :=
  P.relativeProjective.chosenProjectiveChartAt
    (P.projectiveChartSourcePoint U x)

/-- The selected projective-coordinate index. -/
def projectiveChartIndexAt
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) :
    Fin (P.relativeProjective.chosenDimension + 1) :=
  P.relativeProjective.chosenProjectiveChartIndexAt
    (P.projectiveChartSourcePoint U x)

/-- The smaller target open obtained by transporting the selected
projective chart through the inverse over `U`. -/
def projectiveChartTargetShrinkAt
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) : X.Opens :=
  isomorphismTargetShrink P.toOriginal U
    (P.projectiveChartOpenAt U x)

/-- The lifted point lies in the selected projective chart. -/
theorem projectiveChartSourcePoint_mem
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) :
    P.projectiveChartSourcePoint U x ∈
      P.projectiveChartOpenAt U x :=
  P.relativeProjective.mem_chosenProjectiveChartAt
    (P.projectiveChartSourcePoint U x)

/-- The original point lies in the transported smaller open. -/
theorem mem_projectiveChartTargetShrinkAt
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) :
    U.ι x ∈ P.projectiveChartTargetShrinkAt U x :=
  mem_isomorphismTargetShrink
    P.toOriginal U (P.projectiveChartOpenAt U x) x
    (P.projectiveChartSourcePoint_mem U x)

/-- The transported projective-chart open is contained in the original
isomorphism open. -/
theorem projectiveChartTargetShrinkAt_le
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) :
    P.projectiveChartTargetShrinkAt U x ≤ U :=
  isomorphismTargetShrink_le
    P.toOriginal U (P.projectiveChartOpenAt U x)

/-- The modification remains an isomorphism over the transported
projective-chart open. -/
theorem isIso_projectiveChartTargetShrinkAt
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) :
    IsIso
      (P.toOriginal ∣_
        P.projectiveChartTargetShrinkAt U x) :=
  isIso_isomorphismTargetShrink
    P.toOriginal U (P.projectiveChartOpenAt U x)

/-- Upstairs, the inverse image of the transported target open is the
intersection of the original inverse image and the selected projective
chart. -/
theorem preimage_projectiveChartTargetShrinkAt
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) :
    P.toOriginal ⁻¹ᵁ P.projectiveChartTargetShrinkAt U x =
      (P.toOriginal ⁻¹ᵁ U) ⊓
        P.projectiveChartOpenAt U x :=
  preimage_isomorphismTargetShrink
    P.toOriginal U (P.projectiveChartOpenAt U x)

/-- Over the transported target open, the chosen projective map lands
inside the selected standard chart. -/
theorem preimage_projectiveChartTargetShrinkAt_le_chart
    (P : ProjectiveModification f)
    (U : X.Opens) [IsIso (P.toOriginal ∣_ U)]
    (x : U.toScheme) :
    P.toOriginal ⁻¹ᵁ P.projectiveChartTargetShrinkAt U x ≤
      P.relativeProjective.chosenProjectiveMap ⁻¹ᵁ
        standardChart k (P.projectiveChartIndexAt U x) := by
  change
    P.toOriginal ⁻¹ᵁ P.projectiveChartTargetShrinkAt U x ≤
      P.projectiveChartOpenAt U x
  rw [P.preimage_projectiveChartTargetShrinkAt U x]
  exact inf_le_right

end ProjectiveModification
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
