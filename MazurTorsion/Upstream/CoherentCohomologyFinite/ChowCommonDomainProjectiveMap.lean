/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowChartCompletions
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowCommonDenseAffineCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteProjectiveProductMaps

/-!
# The common dense domain mapped to all chart completions

A common dense affine open lies in every member of a
`CommonDenseRelativeAffineCoverData`.  It therefore maps to the
projective completion of each chart.  Taking the diagonal into the
finite product of these completions gives the rational projective map
used in Chow's graph construction.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

namespace CommonDenseRelativeAffineCoverData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (c : CommonDenseRelativeAffineCoverData k f)

/-- The structural morphism of the common dense domain. -/
abbrev domainToBase :
    c.domain ⟶ Spec (CommRingCat.of k) :=
  c.domainInclusion ≫ f

/-- The common domain, regarded as an open subscheme of one affine
cover member. -/
def domainToChart
    (i : c.toAffineCoverData.ι) :
    c.domain ⟶ Spec (c.toAffineCoverData.R i) :=
  IsOpenImmersion.lift
    (c.toAffineCoverData.f i)
    c.domainInclusion
    (by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact
        (Scheme.Hom.mem_opensRange).1
          (c.commonOpen_le_chart i y.2))

instance isOpenImmersion_domainToChart
    (i : c.toAffineCoverData.ι) :
    IsOpenImmersion (c.domainToChart i) :=
  by
    dsimp only [domainToChart]
    letI : IsOpenImmersion (c.toAffineCoverData.f i) :=
      c.toAffineCoverData.isOpenImmersion i
    letI : IsOpenImmersion c.domainInclusion := by
      dsimp only [domainInclusion, domain]
      infer_instance
    let hsubset : Set.range c.domainInclusion ⊆
        Set.range (c.toAffineCoverData.f i) := by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact
        (Scheme.Hom.mem_opensRange).1
          (c.commonOpen_le_chart i y.2)
    let l := IsOpenImmersion.lift
      (c.toAffineCoverData.f i) c.domainInclusion hsubset
    have hl : IsOpenImmersion
        (l ≫ c.toAffineCoverData.f i) := by
      rw [show l ≫ c.toAffineCoverData.f i =
          c.domainInclusion from
        IsOpenImmersion.lift_fac _ _ hsubset]
      infer_instance
    exact @IsOpenImmersion.of_comp _ _ _ l
      (c.toAffineCoverData.f i) inferInstance hl

@[reassoc (attr := simp)]
theorem domainToChart_chartMap
    (i : c.toAffineCoverData.ι) :
    c.domainToChart i ≫ c.toAffineCoverData.f i =
      c.domainInclusion :=
  IsOpenImmersion.lift_fac _ _ _

/-- The chosen projective completion of one enlarged affine chart. -/
abbrev projectiveCompletion
    (i : c.toAffineCoverData.ι) :
    ChartProjectiveCompletion k c.toRelativeAffineCoverData i :=
  chartProjectiveCompletion k c.toRelativeAffineCoverData i

/-- Map the common domain into the projective completion of one chart. -/
def domainToProjectiveCompletion
    (i : c.toAffineCoverData.ι) :
    c.domain ⟶ (c.projectiveCompletion i).model.carrier :=
  c.domainToChart i ≫
    (c.projectiveCompletion i).openMap

@[reassoc]
theorem domainToProjectiveCompletion_toSpec
    (i : c.toAffineCoverData.ι) :
    c.domainToProjectiveCompletion i ≫
        (c.projectiveCompletion i).model.toSpec =
      c.domainToBase := by
  rw [domainToProjectiveCompletion, Category.assoc,
    (c.projectiveCompletion i).openMap_toSpec]
  calc
    c.domainToChart i ≫ Spec.map (c.baseMap i) =
        c.domainToChart i ≫ c.toAffineCoverData.f i ≫ f := by
      rw [c.chart_toBase i]
    _ = c.domainInclusion ≫ f := by
      rw [← Category.assoc, c.domainToChart_chartMap]

/-- The map to one chart completion, packaged for finite fiber-product
assembly. -/
def projectiveCompletionMapFrom
    (i : c.toAffineCoverData.ι) :
    (c.projectiveCompletion i).model.MapFrom c.domainToBase where
  hom := c.domainToProjectiveCompletion i
  overBase := c.domainToProjectiveCompletion_toSpec i

/-- The common dense domain mapped diagonally into the chosen finite
product of all chart completions. -/
def finiteProjectiveAmbientWithMap
    (hsegre : StandardSegreEmbeddings k) :
    StandardProjectiveModel.ModelWithMapFrom k c.domainToBase :=
  StandardProjectiveModel.finiteFiberProductWithMap
    hsegre
    (fun i => (c.projectiveCompletion i).model)
    (fun i => c.projectiveCompletionMapFrom i)

/-- The finite ambient assembled from the chart completions is
projective over the coefficient ring. -/
theorem finiteProjectiveAmbientWithMap_projective
    (hsegre : StandardSegreEmbeddings k) :
    IsProjectiveFactorization
      (c.finiteProjectiveAmbientWithMap hsegre).1.toSpec :=
  (c.finiteProjectiveAmbientWithMap hsegre).1.projective

/-- The diagonal common-domain map is compatible with the structural
morphism to `Spec k`. -/
theorem finiteProjectiveAmbientWithMap_overBase
    (hsegre : StandardSegreEmbeddings k) :
    (c.finiteProjectiveAmbientWithMap hsegre).2.hom ≫
        (c.finiteProjectiveAmbientWithMap hsegre).1.toSpec =
      c.domainToBase :=
  (c.finiteProjectiveAmbientWithMap hsegre).2.overBase

end CommonDenseRelativeAffineCoverData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
