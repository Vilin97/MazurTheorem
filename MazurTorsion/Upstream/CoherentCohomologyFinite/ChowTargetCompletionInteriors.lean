/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowRationalMapAmbient

/-!
# Completion-interior opens in the Chow target closure

For every affine chart of the original scheme, its projective
completion has a distinguished affine interior.  Pulling that interior
back along the corresponding labeled coordinate gives an open of the
target closure.  On this open the coordinate itself recovers a
canonical morphism to the original affine chart.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

namespace CommonDenseRelativeAffineCoverData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    [IsLocallyNoetherian X]
    (c : CommonDenseRelativeAffineCoverData k f)

instance isOpenImmersion_projectiveCompletion_openMap
    (i : c.toAffineCoverData.ι) :
    IsOpenImmersion (c.projectiveCompletion i).openMap :=
  (c.projectiveCompletion i).isOpenImmersion_openMap

/-- The open of the target closure on which the `i`-th completion
coordinate lies in its original affine chart. -/
abbrev targetCompletionInterior
    (i : c.toAffineCoverData.ι) :
    (c.toRationalProjectiveMapData).targetClosure.Opens :=
  c.targetClosureToProjectiveCompletion i ⁻¹ᵁ
    (c.projectiveCompletion i).openMap.opensRange

/-- On the completion-interior open, the `i`-th coordinate lifts
canonically to the corresponding affine chart. -/
def targetCompletionInteriorToChart
    (i : c.toAffineCoverData.ι) :
    (c.targetCompletionInterior i).toScheme ⟶
      Spec (c.toAffineCoverData.R i) := by
  letI :
      IsOpenImmersion (c.projectiveCompletion i).openMap :=
    (c.projectiveCompletion i).isOpenImmersion_openMap
  exact
    IsOpenImmersion.lift
      (c.projectiveCompletion i).openMap
      ((c.targetCompletionInterior i).ι ≫
        c.targetClosureToProjectiveCompletion i)
      (by
        rintro x ⟨y, rfl⟩
        have hy := y.2
        change
          c.targetClosureToProjectiveCompletion i
              ((c.targetCompletionInterior i).ι y) ∈
            (c.projectiveCompletion i).openMap.opensRange at hy
        exact (Scheme.Hom.mem_opensRange).1 hy)

/-- The affine-chart lift followed by the completion open immersion is
the restricted completion coordinate. -/
@[reassoc (attr := simp)]
theorem targetCompletionInteriorToChart_openMap
    (i : c.toAffineCoverData.ι) :
    c.targetCompletionInteriorToChart i ≫
        (c.projectiveCompletion i).openMap =
      (c.targetCompletionInterior i).ι ≫
        c.targetClosureToProjectiveCompletion i := by
  letI :
      IsOpenImmersion (c.projectiveCompletion i).openMap :=
    (c.projectiveCompletion i).isOpenImmersion_openMap
  exact IsOpenImmersion.lift_fac _ _ _

/-- The canonical local rational inverse from a completion-interior
open to the original scheme. -/
def targetCompletionInteriorToOriginal
    (i : c.toAffineCoverData.ι) :
    (c.targetCompletionInterior i).toScheme ⟶ X :=
  c.targetCompletionInteriorToChart i ≫
    c.toAffineCoverData.f i

/-- The local inverse is compatible with the fixed coefficient
spectrum. -/
@[reassoc]
theorem targetCompletionInteriorToOriginal_toBase
    (i : c.toAffineCoverData.ι) :
    c.targetCompletionInteriorToOriginal i ≫ f =
      (c.targetCompletionInterior i).ι ≫
        (c.toRationalProjectiveMapData).targetClosureToSpec := by
  rw [targetCompletionInteriorToOriginal,
    Category.assoc,
    c.chart_toBase i]
  rw [← (c.projectiveCompletion i).openMap_toSpec]
  rw [← Category.assoc,
    c.targetCompletionInteriorToChart_openMap]
  rw [Category.assoc,
    c.targetClosureToProjectiveCompletion_toSpec]

/-- The common dense domain maps into every completion-interior open. -/
def domainToTargetCompletionInterior
    (i : c.toAffineCoverData.ι) :
    c.domain ⟶ (c.targetCompletionInterior i).toScheme := by
  letI : IsOpenImmersion (c.targetCompletionInterior i).ι :=
    inferInstance
  exact
    IsOpenImmersion.lift
      (c.targetCompletionInterior i).ι
      (c.toRationalProjectiveMapData).toTargetClosure
      (by
        rintro x ⟨y, rfl⟩
        apply (Scheme.Hom.mem_opensRange).2
        let z :=
          (c.toRationalProjectiveMapData).toTargetClosure y
        have hz :
            c.targetClosureToProjectiveCompletion i z ∈
              (c.projectiveCompletion i).openMap.opensRange := by
          change
            c.targetClosureToProjectiveCompletion i
                ((c.toRationalProjectiveMapData).toTargetClosure y) ∈
              (c.projectiveCompletion i).openMap.opensRange
          erw [← Scheme.Hom.comp_apply]
          rw [c.toTargetClosure_targetClosureToProjectiveCompletion]
          exact
            ⟨c.domainToChart i y,
              by
                erw [← Scheme.Hom.comp_apply]⟩
        refine ⟨⟨z, ?_⟩, rfl⟩
        exact hz)

/-- The lift of the common domain to the target interior recovers its
map to the target closure. -/
@[reassoc (attr := simp)]
theorem domainToTargetCompletionInterior_ι
    (i : c.toAffineCoverData.ι) :
    c.domainToTargetCompletionInterior i ≫
        (c.targetCompletionInterior i).ι =
      (c.toRationalProjectiveMapData).toTargetClosure := by
  exact IsOpenImmersion.lift_fac _ _ _

/-- The local inverse agrees with the original dense-open inclusion. -/
@[reassoc]
theorem domainToTargetCompletionInterior_toOriginal
    (i : c.toAffineCoverData.ι) :
    c.domainToTargetCompletionInterior i ≫
        c.targetCompletionInteriorToOriginal i =
      c.domainInclusion := by
  rw [targetCompletionInteriorToOriginal,
    ← Category.assoc]
  have hchart :
      c.domainToTargetCompletionInterior i ≫
          c.targetCompletionInteriorToChart i =
        c.domainToChart i := by
    apply (cancel_mono
      (c.projectiveCompletion i).openMap).mp
    rw [Category.assoc,
      c.targetCompletionInteriorToChart_openMap,
      ← Category.assoc,
      c.domainToTargetCompletionInterior_ι]
    exact
      c.toTargetClosure_targetClosureToProjectiveCompletion i
  rw [hchart, c.domainToChart_chartMap]

end CommonDenseRelativeAffineCoverData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
