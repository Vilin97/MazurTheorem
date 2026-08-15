/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowCommonDomainProjectiveMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteProjectiveProductProjections
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreProductChartTransitionGeometry

/-!
# Labeled completion coordinates in Chow's finite projective product

The finite product used in Chow's construction is built by iterating
binary fiber products and then choosing Segre embeddings.  This file
retains, for each affine chart, the projection to that chart's chosen
projective completion.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

namespace CommonDenseRelativeAffineCoverData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (c : CommonDenseRelativeAffineCoverData k f)

/-- The projection from the chosen finite product to the projective
completion indexed by `i`. -/
def finiteProjectiveAmbientProjection
    (i : c.toAffineCoverData.ι) :
    (c.finiteProjectiveAmbientWithMap
          (standardSegreEmbeddings k)).1.carrier ⟶
      (c.projectiveCompletion i).model.carrier :=
  (StandardProjectiveModel.finiteFiberProductWithMapProjection
    (standardSegreEmbeddings k)
    (fun j => (c.projectiveCompletion j).model)
    (fun j => c.projectiveCompletionMapFrom j)
    i).hom

/-- A completion projection is compatible with the structural maps to
the coefficient spectrum. -/
@[reassoc]
theorem finiteProjectiveAmbientProjection_toSpec
    (i : c.toAffineCoverData.ι) :
    c.finiteProjectiveAmbientProjection i ≫
        (c.projectiveCompletion i).model.toSpec =
      (c.finiteProjectiveAmbientWithMap
        (standardSegreEmbeddings k)).1.toSpec :=
  (StandardProjectiveModel.finiteFiberProductWithMapProjection
    (standardSegreEmbeddings k)
    (fun j => (c.projectiveCompletion j).model)
    (fun j => c.projectiveCompletionMapFrom j)
    i).overBase

/-- On the common dense domain, the labeled projection recovers the
original map into that chart's projective completion. -/
@[reassoc]
theorem finiteProjectiveAmbientWithMap_projection
    (i : c.toAffineCoverData.ι) :
    (c.finiteProjectiveAmbientWithMap
          (standardSegreEmbeddings k)).2.hom ≫
        c.finiteProjectiveAmbientProjection i =
      c.domainToProjectiveCompletion i :=
  (StandardProjectiveModel.finiteFiberProductWithMapProjection
    (standardSegreEmbeddings k)
    (fun j => (c.projectiveCompletion j).model)
    (fun j => c.projectiveCompletionMapFrom j)
    i).from_hom

end CommonDenseRelativeAffineCoverData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
