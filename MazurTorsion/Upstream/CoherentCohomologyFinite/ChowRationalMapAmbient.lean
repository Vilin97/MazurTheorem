/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowFiniteProductCompletionProjections
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowRationalProjectiveClosure
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeTheoreticImageClosedFactor

/-!
# The finite-product ambient behind the Chow rational map

The public rational-map package records only the final standard
projective space.  Here we expose its intermediate finite product so
that the individual chart-completion coordinates remain available on
the scheme-theoretic image.
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
    [IsLocallyNoetherian X]
    (c : CommonDenseRelativeAffineCoverData k f)

/-- The intermediate finite product of all projective chart
completions. -/
abbrev rationalMapFiniteAmbient :
    StandardProjectiveModel.ModelWithMapFrom k c.domainToBase :=
  c.finiteProjectiveAmbientWithMap
    (standardSegreEmbeddings k)

/-- The dimension of the standard projective space chosen for the
finite product. -/
abbrev rationalMapDimension : ℕ :=
  c.rationalMapFiniteAmbient.1.projective.choose

/-- The chosen closed embedding of the finite product in one standard
projective space. -/
abbrev rationalMapFiniteAmbientEmbedding :
    c.rationalMapFiniteAmbient.1.carrier ⟶
      scheme k c.rationalMapDimension :=
  c.rationalMapFiniteAmbient.1.projective.choose_spec.choose

instance isClosedImmersion_rationalMapFiniteAmbientEmbedding :
    IsClosedImmersion c.rationalMapFiniteAmbientEmbedding :=
  c.rationalMapFiniteAmbient.1.projective.choose_spec.choose_spec.1

/-- The chosen embedding is over the coefficient spectrum. -/
@[reassoc]
theorem rationalMapFiniteAmbientEmbedding_toSpec :
    c.rationalMapFiniteAmbientEmbedding ≫
        toSpec k c.rationalMapDimension =
      c.rationalMapFiniteAmbient.1.toSpec :=
  c.rationalMapFiniteAmbient.1.projective.choose_spec.choose_spec.2

/-- The packaged rational projective map is definitionally the
finite-product diagonal followed by the chosen embedding. -/
theorem toRationalProjectiveMapData_toProjective :
    (c.toRationalProjectiveMapData).toProjective =
      c.rationalMapFiniteAmbient.2.hom ≫
        c.rationalMapFiniteAmbientEmbedding :=
  rfl

/-- Its recorded dimension is the chosen ambient dimension. -/
theorem toRationalProjectiveMapData_dimension :
    (c.toRationalProjectiveMapData).dimension =
      c.rationalMapDimension :=
  rfl

/-- The target closure maps canonically into the intermediate finite
product. -/
def targetClosureToFiniteAmbient :
    (c.toRationalProjectiveMapData).targetClosure ⟶
      c.rationalMapFiniteAmbient.1.carrier :=
  by
    letI :
        IsClosedImmersion c.rationalMapFiniteAmbientEmbedding :=
      c.isClosedImmersion_rationalMapFiniteAmbientEmbedding
    exact
      @SchemeTheoreticImage.toClosedFactor
        _ _ _
        (c.toRationalProjectiveMapData).toProjective
        c.rationalMapFiniteAmbient.2.hom
        c.rationalMapFiniteAmbientEmbedding
        c.isClosedImmersion_rationalMapFiniteAmbientEmbedding
        c.toRationalProjectiveMapData_toProjective

/-- The target closure remains a closed subscheme of the finite
product. -/
instance isClosedImmersion_targetClosureToFiniteAmbient :
    IsClosedImmersion c.targetClosureToFiniteAmbient := by
  letI :
      IsClosedImmersion c.rationalMapFiniteAmbientEmbedding :=
    c.isClosedImmersion_rationalMapFiniteAmbientEmbedding
  exact
    @SchemeTheoreticImage.isClosedImmersion_toClosedFactor
      _ _ _
      (c.toRationalProjectiveMapData).toProjective
      c.rationalMapFiniteAmbient.2.hom
      c.rationalMapFiniteAmbientEmbedding
      c.isClosedImmersion_rationalMapFiniteAmbientEmbedding
      c.toRationalProjectiveMapData_toProjective

/-- The closed factorization through the finite ambient respects the
structural morphisms to the coefficient spectrum. -/
@[reassoc]
theorem targetClosureToFiniteAmbient_toSpec :
    c.targetClosureToFiniteAmbient ≫
        c.rationalMapFiniteAmbient.1.toSpec =
      (c.toRationalProjectiveMapData).targetClosureToSpec := by
  have hfactor :
      c.targetClosureToFiniteAmbient ≫
          c.rationalMapFiniteAmbientEmbedding =
        (c.toRationalProjectiveMapData).targetClosureEmbedding := by
    unfold targetClosureToFiniteAmbient
    exact
      @SchemeTheoreticImage.toClosedFactor_comp
        _ _ _
        (c.toRationalProjectiveMapData).toProjective
        c.rationalMapFiniteAmbient.2.hom
        c.rationalMapFiniteAmbientEmbedding
        c.isClosedImmersion_rationalMapFiniteAmbientEmbedding
        c.toRationalProjectiveMapData_toProjective
  rw [← c.rationalMapFiniteAmbientEmbedding_toSpec]
  rw [← Category.assoc]
  rw [hfactor]
  rfl

/-- On the common dense open, the factorization through the finite
ambient is the original diagonal map. -/
theorem toTargetClosure_targetClosureToFiniteAmbient :
    (c.toRationalProjectiveMapData).toTargetClosure ≫
        c.targetClosureToFiniteAmbient =
      c.rationalMapFiniteAmbient.2.hom :=
  by
    letI :
        IsClosedImmersion c.rationalMapFiniteAmbientEmbedding :=
      c.isClosedImmersion_rationalMapFiniteAmbientEmbedding
    change
      (c.toRationalProjectiveMapData).toProjective.toImage ≫
          c.targetClosureToFiniteAmbient =
        c.rationalMapFiniteAmbient.2.hom
    exact
      @SchemeTheoreticImage.toImage_toClosedFactor
        _ _ _
        (c.toRationalProjectiveMapData).toProjective
        c.rationalMapFiniteAmbient.2.hom
        c.rationalMapFiniteAmbientEmbedding
        c.isClosedImmersion_rationalMapFiniteAmbientEmbedding
        c.toRationalProjectiveMapData_toProjective

/-- The map from the target closure to its `i`-th projective
completion. -/
def targetClosureToProjectiveCompletion
    (i : c.toAffineCoverData.ι) :
    (c.toRationalProjectiveMapData).targetClosure ⟶
      (c.projectiveCompletion i).model.carrier :=
  c.targetClosureToFiniteAmbient ≫
    c.finiteProjectiveAmbientProjection i

/-- Every labeled completion coordinate is a morphism over the
coefficient spectrum. -/
@[reassoc]
theorem targetClosureToProjectiveCompletion_toSpec
    (i : c.toAffineCoverData.ι) :
    c.targetClosureToProjectiveCompletion i ≫
        (c.projectiveCompletion i).model.toSpec =
      (c.toRationalProjectiveMapData).targetClosureToSpec := by
  rw [targetClosureToProjectiveCompletion,
    Category.assoc,
    c.finiteProjectiveAmbientProjection_toSpec,
    c.targetClosureToFiniteAmbient_toSpec]

/-- On the common dense open, the `i`-th target-closure coordinate is
the original map into the `i`-th chart completion. -/
theorem toTargetClosure_targetClosureToProjectiveCompletion
    (i : c.toAffineCoverData.ι) :
    (c.toRationalProjectiveMapData).toTargetClosure ≫
        c.targetClosureToProjectiveCompletion i =
      c.domainToProjectiveCompletion i := by
  change
    (c.toRationalProjectiveMapData).toProjective.toImage ≫
        (c.targetClosureToFiniteAmbient ≫
          c.finiteProjectiveAmbientProjection i) =
      c.domainToProjectiveCompletion i
  rw [← Category.assoc,
    c.toTargetClosure_targetClosureToFiniteAmbient]
  exact c.finiteProjectiveAmbientWithMap_projection i

end CommonDenseRelativeAffineCoverData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow
