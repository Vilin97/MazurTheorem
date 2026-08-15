/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreImageAffineCover
import Mathlib.AlgebraicGeometry.Morphisms.Basic


/-!
# A chartwise criterion for the Segre product--`Proj` comparison

The standard coordinate basic opens cover the `Proj` of the Segre image.
Consequently, a morphism from the product of projective spaces is an
isomorphism as soon as its restriction over every standard Segre-image
chart is an isomorphism.

This reduces the remaining geometric Segre theorem to the familiar
affine-chart calculation.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- A candidate product--`Proj` morphism together with the exact local
isomorphism checks on the standard affine charts. -/
structure SegreChartwiseProjMorphism
    (k : Type u) [CommRing k] (m n : ℕ) where
  hom :
    binaryProjectiveScheme k m n ⟶
      Proj (segreImageGrading k m n)
  overBase :
    hom ≫
          Proj.map
            (segreImageGradedHom k m n)
            (segreImageIrrelevantLE k m n) ≫
        toSpec k (segreDimension m n) =
      binaryProjectiveToSpec k m n
  isIso_restrict :
    ∀ i : Fin (segreDimension m n + 1),
      IsIso
        (hom ∣_
          segreImageStandardChart k m n i)

namespace SegreChartwiseProjMorphism

variable {k : Type u} [CommRing k] {m n : ℕ}

/-- The chartwise local isomorphism checks imply that the candidate
Segre morphism is globally an isomorphism. -/
theorem isIso_hom
    (D : SegreChartwiseProjMorphism k m n) :
    IsIso D.hom := by
  exact
    (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := MorphismProperty.isomorphisms Scheme)
      (fun i =>
        segreImageStandardChart k m n i)
      (iSup_segreImageStandardChart k m n)).mpr
        D.isIso_restrict

/-- The global product--`Proj` isomorphism obtained by gluing the
standard affine-chart comparisons. -/
def productIso
    (D : SegreChartwiseProjMorphism k m n) :
    binaryProjectiveScheme k m n ≅
      Proj (segreImageGrading k m n) := by
  letI : IsIso D.hom := D.isIso_hom
  exact asIso D.hom

/-- Chartwise comparison data supplies the exact geometric input needed
by the Segre embedding construction. -/
def toProductProjIdentification
    (D : SegreChartwiseProjMorphism k m n) :
    SegreProductProjIdentification k m n where
  productIso := D.productIso
  overBase := by
    simpa [productIso] using D.overBase

end SegreChartwiseProjMorphism

/-- The family of standard chartwise Segre comparisons. -/
def StandardSegreChartwiseProjMorphisms
    (k : Type u) [CommRing k] : Prop :=
  ∀ (m n : ℕ),
    Nonempty (SegreChartwiseProjMorphism k m n)

/-- Standard chartwise comparisons imply the product--`Proj`
identifications. -/
theorem standardSegreProductProjIdentifications_of_chartwise
    (k : Type u) [CommRing k]
    (h : StandardSegreChartwiseProjMorphisms k) :
    StandardSegreProductProjIdentifications k := by
  intro m n
  obtain ⟨D⟩ := h m n
  exact ⟨D.toProductProjIdentification⟩

/-- The affine-chart comparison is sufficient for all scheme-level
standard Segre embeddings. -/
theorem standardSegreEmbeddings_of_chartwise
    (k : Type u) [CommRing k]
    (h : StandardSegreChartwiseProjMorphisms k) :
    StandardSegreEmbeddings k :=
  standardSegreEmbeddings_of_productProjIdentifications
    k
    (standardSegreProductProjIdentifications_of_chartwise
      k h)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
