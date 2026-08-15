/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowRationalProjectiveMap

/-!
# The projective closure of the Chow rational map

The rational map constructed from the finite affine cover is itself a
quasi-compact immersion into standard projective space.  Its
scheme-theoretic image is therefore an absolute projective
compactification of the common dense affine domain.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

namespace ChowRationalProjectiveMapData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (D : ChowRationalProjectiveMapData f)

/-- The scheme-theoretic closure of the rational map in its standard
projective target. -/
abbrev targetClosure : Scheme.{u} :=
  D.toProjective.image

/-- The common domain as a dense open in its projective closure. -/
abbrev toTargetClosure :
    D.domain ⟶ D.targetClosure :=
  D.toProjective.toImage

/-- The closed embedding of the target closure into standard
projective space. -/
abbrev targetClosureEmbedding :
    D.targetClosure ⟶ scheme k D.dimension :=
  D.toProjective.imageι

/-- The structural morphism of the target closure. -/
def targetClosureToSpec :
    D.targetClosure ⟶ Spec (CommRingCat.of k) :=
  D.targetClosureEmbedding ≫ toSpec k D.dimension

/-- The rational map factors as the dense-open map followed by the
target-closure embedding. -/
@[reassoc]
theorem toTargetClosure_targetClosureEmbedding :
    D.toTargetClosure ≫ D.targetClosureEmbedding =
      D.toProjective :=
  D.toProjective.toImage_imageι

/-- The common domain is open in its target closure. -/
theorem isOpenImmersion_toTargetClosure :
    IsOpenImmersion D.toTargetClosure := by
  letI : IsImmersion D.toProjective :=
    D.isImmersion_toProjective
  letI : QuasiCompact D.toProjective :=
    D.quasiCompact_toProjective
  infer_instance

/-- The common domain is dense in its target closure. -/
theorem dense_toTargetClosure :
    Dense (Set.range D.toTargetClosure.base) := by
  letI : QuasiCompact D.toProjective :=
    D.quasiCompact_toProjective
  simpa [DenseRange] using
    D.toProjective.toImage.denseRange

/-- The target closure is closed in standard projective space. -/
theorem isClosedImmersion_targetClosureEmbedding :
    IsClosedImmersion D.targetClosureEmbedding :=
  inferInstance

/-- The target closure is projective over the coefficient ring. -/
theorem targetClosure_projective :
    IsProjectiveFactorization D.targetClosureToSpec :=
  ⟨D.dimension, D.targetClosureEmbedding,
    inferInstance, rfl⟩

/-- The dense open of the target closure retains the original
structural morphism to the coefficient spectrum. -/
@[reassoc]
theorem toTargetClosure_targetClosureToSpec :
    D.toTargetClosure ≫ D.targetClosureToSpec =
      D.toOriginalOpen ≫ f := by
  rw [targetClosureToSpec, ← Category.assoc,
    D.toTargetClosure_targetClosureEmbedding,
    D.overBase]

end ChowRationalProjectiveMapData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology
