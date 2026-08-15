/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreImageGrading


/-!
# The remaining geometric input for the Segre embedding

The Segre coordinate image already has a canonical grading, and its
coordinate map is a surjective graded map.  In particular, both the
irrelevant-ideal condition and the resulting closed immersion on
`Proj` are formal consequences of the coordinate algebra.

This file isolates the only remaining geometric input: an
identification of the product of two projective spaces with the `Proj`
of the canonically graded Segre image algebra, compatibly over the base.
-/

open CategoryTheory AlgebraicGeometry
open HomogeneousIdeal MvPolynomial

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The canonical surjective graded coordinate map onto the Segre
image algebra. -/
abbrev segreImageGradedHom
    (k : Type u) [CommRing k] (m n : ℕ) :
    homogeneousGrading k (segreDimension m n) →+*ᵍ
      segreImageGrading k m n :=
  segreRangeGradedHom k m n
    (segreImageGrading k m n)
    (segreRangeCoordinateHom_mem_imageGrading k m n)

lemma segreImageGradedHom_surjective
    (k : Type u) [CommRing k] (m n : ℕ) :
    Function.Surjective
      (segreImageGradedHom k m n) :=
  segreRangeCoordinateHom_surjective k m n

/-- The irrelevant ideal of the Segre image is covered by the image of
the irrelevant ideal of the ambient projective-space coordinate ring.
-/
theorem segreImageIrrelevantLE
    (k : Type u) [CommRing k] (m n : ℕ) :
    (segreImageGrading k m n)₊ ≤
      (homogeneousGrading k
        (segreDimension m n))₊.map
          (segreImageGradedHom k m n) :=
  irrelevant_le_map_of_surjective
    (segreImageGradedHom k m n)
    (segreImageGradedHom_surjective k m n)

/-- The exact geometric identification still needed for the standard
Segre embedding.  Its coordinate algebra, grading, surjectivity,
irrelevant-ideal comparison, and closed-immersion consequence have
already been constructed. -/
structure SegreProductProjIdentification
    (k : Type u) [CommRing k] (m n : ℕ) where
  productIso :
    binaryProjectiveScheme k m n ≅
      Proj (segreImageGrading k m n)
  overBase :
    productIso.hom ≫
          Proj.map
            (segreImageGradedHom k m n)
            (segreImageIrrelevantLE k m n) ≫
        toSpec k (segreDimension m n) =
      binaryProjectiveToSpec k m n

namespace SegreProductProjIdentification

variable {k : Type u} [CommRing k] {m n : ℕ}

/-- Regard the fixed product--`Proj` identification as the older,
fully explicit `SegreProjComparison` package. -/
def toSegreProjComparison
    (D : SegreProductProjIdentification k m n) :
    SegreProjComparison k m n where
  gradingFamily :=
    Submodule k (SegreCoordinateRing k m n)
  setLike := inferInstance
  addSubgroupClass := inferInstance
  grading := segreImageGrading k m n
  gradedRing := inferInstance
  map_mem :=
    segreRangeCoordinateHom_mem_imageGrading k m n
  irrelevant_le := segreImageIrrelevantLE k m n
  productIso := D.productIso
  overBase := D.overBase

/-- The Segre morphism furnished by a product--`Proj`
identification. -/
def toProjective
    (D : SegreProductProjIdentification k m n) :
    binaryProjectiveScheme k m n ⟶
      scheme k (segreDimension m n) :=
  D.toSegreProjComparison.toProjective

theorem isClosedImmersion_toProjective
    (D : SegreProductProjIdentification k m n) :
    IsClosedImmersion D.toProjective :=
  D.toSegreProjComparison.isClosedImmersion_toProjective

@[reassoc]
theorem toProjective_toSpec
    (D : SegreProductProjIdentification k m n) :
    D.toProjective ≫
        toSpec k (segreDimension m n) =
      binaryProjectiveToSpec k m n :=
  D.toSegreProjComparison.toProjective_toSpec

end SegreProductProjIdentification

/-- The family of geometric product--`Proj` identifications that
remains to construct for all standard Segre embeddings. -/
def StandardSegreProductProjIdentifications
    (k : Type u) [CommRing k] : Prop :=
  ∀ (m n : ℕ),
    Nonempty (SegreProductProjIdentification k m n)

/-- Product--`Proj` identifications supply the explicit comparison
packages used by the coordinate-presentation layer. -/
theorem standardSegreProjComparisons_of_productProjIdentifications
    (k : Type u) [CommRing k]
    (h : StandardSegreProductProjIdentifications k) :
    StandardSegreProjComparisons k := by
  intro m n
  obtain ⟨D⟩ := h m n
  exact ⟨D.toSegreProjComparison⟩

/-- The sole remaining geometric input produces all standard
scheme-level Segre embeddings. -/
theorem standardSegreEmbeddings_of_productProjIdentifications
    (k : Type u) [CommRing k]
    (h : StandardSegreProductProjIdentifications k) :
    StandardSegreEmbeddings k :=
  standardSegreEmbeddings_of_projComparisons k
    (standardSegreProjComparisons_of_productProjIdentifications
      k h)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
