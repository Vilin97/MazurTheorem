/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowSupport
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModificationPointChartShrink

/-!
# Support-adapted projective charts on a modification

This file packages the open produced by intersecting an isomorphism
open of a projective modification with one standard projective chart.
For the canonical Chow modification of a support thickening, either
the source module is zero or such an open contains a point of its
closed stalk support.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

/-- An isomorphism open on a projective modification which lies over
one selected standard coordinate chart and meets the source support. -/
structure SupportAdaptedProjectiveChart
    {k : Type} [CommRing k]
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (P : ProjectiveModification f)
    (M : X.Modules) where
  /-- The support-adapted open downstairs. -/
  openSubscheme : X.Opens
  /-- The selected standard projective coordinate. -/
  coordinate :
    Fin (P.relativeProjective.chosenDimension + 1)
  /-- The modification is unchanged over this open. -/
  restrictedMorphismIsIso :
    IsIso (P.toOriginal ∣_ openSubscheme)
  /-- Upstairs over this open, the chosen projective map lands in the
  selected standard chart. -/
  preimage_le_standardChart :
    P.toOriginal ⁻¹ᵁ openSubscheme ≤
      P.relativeProjective.chosenProjectiveMap ⁻¹ᵁ
        standardChart k coordinate
  /-- The open meets the closed stalk support of the source module. -/
  supportPoint :
    ∃ x : openSubscheme,
      openSubscheme.ι x ∈
        Scheme.Modules.closedStalkSupport M

/-- The chart package used by a modification comparison.  In the zero
case no support point is needed; otherwise the selected open meets the
source support. -/
structure ComparisonProjectiveChart
    {k : Type} [CommRing k]
    {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (P : ProjectiveModification f)
    (M : X.Modules) where
  openSubscheme : X.Opens
  coordinate :
    Fin (P.relativeProjective.chosenDimension + 1)
  restrictedMorphismIsIso :
    IsIso (P.toOriginal ∣_ openSubscheme)
  preimage_le_standardChart :
    P.toOriginal ⁻¹ᵁ openSubscheme ≤
      P.relativeProjective.chosenProjectiveMap ⁻¹ᵁ
        standardChart k coordinate
  sourceZeroOrSupportPoint :
    IsZero M ∨
      ∃ x : openSubscheme,
        openSubscheme.ι x ∈
          Scheme.Modules.closedStalkSupport M

namespace CanonicalSupportThickening

variable {X : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of ℚ)} [IsProper f]
  {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]

/-- Unless the canonical support module is zero, its Chow modification
has a support-adapted isomorphism open lying over one standard
projective chart. -/
theorem sourceZeroOrSupportAdaptedProjectiveChart
    (A : CanonicalSupportThickening F) :
    let P := A.chowModification (k := ℚ) (f := f)
    IsZero A.modelModule ∨
      Nonempty
        (SupportAdaptedProjectiveChart
          P A.modelModule) := by
  dsimp only
  let P := A.chowModification (k := ℚ) (f := f)
  letI : IsOpenImmersion P.toOriginalOpen :=
    P.isOpenImmersion_toOriginalOpen
  let U := P.toOriginalOpen.opensRange
  letI : IsIso (P.toOriginal ∣_ U) :=
    A.isIso_chowModification_restrict_commonOpen
  rcases
      A.sourceZeroOrSupportPoint_chowCommonOpen
        (k := ℚ) (f := f) with
    hzero | ⟨x, hx⟩
  · exact Or.inl hzero
  · right
    let V := P.projectiveChartTargetShrinkAt U x
    let r := P.projectiveChartIndexAt U x
    have hxV : U.ι x ∈ V :=
      P.mem_projectiveChartTargetShrinkAt U x
    let y : V.toScheme := ⟨U.ι x, hxV⟩
    refine ⟨
      { openSubscheme := V
        coordinate := r
        restrictedMorphismIsIso :=
          P.isIso_projectiveChartTargetShrinkAt U x
        preimage_le_standardChart :=
          P.preimage_projectiveChartTargetShrinkAt_le_chart U x
        supportPoint := ⟨y, ?_⟩ }⟩
    exact hx

/-- The canonical Chow modification always has a comparison chart:
when the support module is nonzero it is support-adapted, while in the
zero case an arbitrary coordinate chart suffices. -/
noncomputable def comparisonProjectiveChart
    (A : CanonicalSupportThickening F) :
    let P := A.chowModification (k := ℚ) (f := f)
    ComparisonProjectiveChart P A.modelModule := by
  dsimp only
  let P := A.chowModification (k := ℚ) (f := f)
  letI : IsOpenImmersion P.toOriginalOpen :=
    P.isOpenImmersion_toOriginalOpen
  let U := P.toOriginalOpen.opensRange
  letI : IsIso (P.toOriginal ∣_ U) :=
    A.isIso_chowModification_restrict_commonOpen
  by_cases hzero : IsZero A.modelModule
  · let r :
        Fin (P.relativeProjective.chosenDimension + 1) :=
      ⟨0, Nat.zero_lt_succ _⟩
    let W : P.model.Opens :=
      P.relativeProjective.chosenProjectiveMap ⁻¹ᵁ
        standardChart ℚ r
    let V : A.supportScheme.Opens :=
      isomorphismTargetShrink P.toOriginal U W
    exact
      { openSubscheme := V
        coordinate := r
        restrictedMorphismIsIso :=
          isIso_isomorphismTargetShrink
            P.toOriginal U W
        preimage_le_standardChart := by
          change P.toOriginal ⁻¹ᵁ V ≤ W
          rw [preimage_isomorphismTargetShrink]
          exact inf_le_right
        sourceZeroOrSupportPoint := Or.inl hzero }
  · have hC :
        Nonempty
          (SupportAdaptedProjectiveChart
            P A.modelModule) :=
      (A.sourceZeroOrSupportAdaptedProjectiveChart
        (f := f)).resolve_left hzero
    let C := Classical.choice hC
    exact
      { openSubscheme := C.openSubscheme
        coordinate := C.coordinate
        restrictedMorphismIsIso :=
          C.restrictedMorphismIsIso
        preimage_le_standardChart :=
          C.preimage_le_standardChart
        sourceZeroOrSupportPoint :=
          Or.inr C.supportPoint }

end CanonicalSupportThickening
end MazurTorsion.AlgebraicGeometry.CoherentCohomology
