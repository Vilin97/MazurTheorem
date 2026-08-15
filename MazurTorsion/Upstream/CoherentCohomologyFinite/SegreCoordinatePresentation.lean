/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BiprojectiveFactorization
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpectrumClosedImmersion
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreCoordinateAlgebra
import Mathlib.Algebra.MvPolynomial.Equiv


/-!
# The exact `Proj` comparison needed for the Segre embedding

The coordinate map for the Segre embedding has a canonical image
subalgebra.  Its range restriction is surjective, so any grading on that
image which makes the coordinate map graded produces a closed immersion
of its `Proj` into standard projective space.

Thus the remaining product theorem is reduced to the geometric
comparison identifying the product of projective spaces with this
`Proj`.  That comparison is isolated in `SegreProjComparison`.
-/

open CategoryTheory AlgebraicGeometry
open HomogeneousIdeal MvPolynomial
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The dimension of the standard target of the Segre embedding
`ℙ^m × ℙ^n ↪ ℙ^(mn+m+n)`. -/
def segreDimension (m n : ℕ) : ℕ :=
  m * n + m + n

lemma segreDimension_succ (m n : ℕ) :
    segreDimension m n + 1 = (m + 1) * (n + 1) := by
  simp only [segreDimension]
  ring

/-- Reindex the standard coordinates of the Segre target by pairs of
coordinates of its two factors. -/
def segreIndexEquiv (m n : ℕ) :
    Fin (segreDimension m n + 1) ≃
      Fin (m + 1) × Fin (n + 1) :=
  (finCongr (segreDimension_succ m n)).trans
    finProdFinEquiv.symm

/-- The coordinate map from the standard homogeneous coordinate ring
of the Segre target, with its variables reindexed by pairs. -/
def segreStandardCoordinateHom
    (k : Type u) [CommRing k] (m n : ℕ) :
    MvPolynomial (Fin (segreDimension m n + 1)) k →ₐ[k]
      MvPolynomial (Fin (m + 1)) k ⊗[k]
        MvPolynomial (Fin (n + 1)) k :=
  (segreCoordinateHom k m n).comp
    (MvPolynomial.renameEquiv k
      (segreIndexEquiv m n)).toAlgHom

@[simp]
lemma segreStandardCoordinateHom_X
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (segreDimension m n + 1)) :
    segreStandardCoordinateHom k m n
        (MvPolynomial.X i) =
        MvPolynomial.X (segreIndexEquiv m n i).1 ⊗ₜ[k]
        MvPolynomial.X (segreIndexEquiv m n i).2 := by
  change
    segreCoordinateHom k m n
        (MvPolynomial.rename
          (segreIndexEquiv m n)
          (MvPolynomial.X i)) =
      _
  rw [MvPolynomial.rename_X,
    segreCoordinateHom_X]

/-- The canonical homogeneous coordinate ring of the Segre image,
defined as the range of the coordinate map. -/
abbrev SegreCoordinateRing
    (k : Type u) [CommRing k] (m n : ℕ) :=
  (segreStandardCoordinateHom k m n).range

/-- The coordinate map with codomain restricted to its image. -/
abbrev segreRangeCoordinateHom
    (k : Type u) [CommRing k] (m n : ℕ) :
    MvPolynomial (Fin (segreDimension m n + 1)) k →ₐ[k]
      SegreCoordinateRing k m n :=
  (segreStandardCoordinateHom k m n).rangeRestrict

lemma segreRangeCoordinateHom_surjective
    (k : Type u) [CommRing k] (m n : ℕ) :
    Function.Surjective
      (segreRangeCoordinateHom k m n) :=
  AlgHom.rangeRestrict_surjective _

@[simp]
lemma segreRangeCoordinateHom_val
    (k : Type u) [CommRing k] (m n : ℕ)
    (p : MvPolynomial
      (Fin (segreDimension m n + 1)) k) :
    ((segreRangeCoordinateHom k m n p :
        SegreCoordinateRing k m n) :
      MvPolynomial (Fin (m + 1)) k ⊗[k]
        MvPolynomial (Fin (n + 1)) k) =
      segreStandardCoordinateHom k m n p :=
  rfl

/-- Package a proof that the range coordinate map respects a proposed
grading as a graded ring homomorphism. -/
def segreRangeGradedHom
    (k : Type u) [CommRing k] (m n : ℕ)
    {σ : Type u}
    [SetLike σ (SegreCoordinateRing k m n)]
    [AddSubgroupClass σ (SegreCoordinateRing k m n)]
    (𝒮 : ℕ → σ)
    (hmap :
      ∀ {d : ℕ}
        {p : MvPolynomial
          (Fin (segreDimension m n + 1)) k},
        p ∈ homogeneousGrading k (segreDimension m n) d →
          segreRangeCoordinateHom k m n p ∈ 𝒮 d) :
    homogeneousGrading k (segreDimension m n) →+*ᵍ 𝒮 where
  __ := (segreRangeCoordinateHom k m n).toRingHom
  map_mem := hmap

/-- The precise missing geometric comparison for a pair of projective
spaces.  All coordinate algebra and surjectivity are fixed; the data
still required are a compatible grading of the image algebra and an
identification of its `Proj` with the fiber product. -/
structure SegreProjComparison
    (k : Type u) [CommRing k] (m n : ℕ) where
  gradingFamily : Type u
  [setLike :
    SetLike gradingFamily (SegreCoordinateRing k m n)]
  [addSubgroupClass :
    AddSubgroupClass gradingFamily
      (SegreCoordinateRing k m n)]
  grading : ℕ → gradingFamily
  [gradedRing : GradedRing grading]
  map_mem :
    ∀ {d : ℕ}
      {p : MvPolynomial
        (Fin (segreDimension m n + 1)) k},
      p ∈ homogeneousGrading k (segreDimension m n) d →
        segreRangeCoordinateHom k m n p ∈ grading d
  irrelevant_le :
    grading₊ ≤
      (homogeneousGrading k
        (segreDimension m n))₊.map
          (segreRangeGradedHom
            k m n grading map_mem)
  productIso :
    binaryProjectiveScheme k m n ≅
      Proj grading
  overBase :
    productIso.hom ≫
          Proj.map
            (segreRangeGradedHom
              k m n grading map_mem)
            irrelevant_le ≫
        toSpec k (segreDimension m n) =
      binaryProjectiveToSpec k m n

namespace SegreProjComparison

variable {k : Type u} [CommRing k] {m n : ℕ}

/-- The morphism to standard projective space supplied by a Segre
`Proj` comparison. -/
def toProjective
    (D : SegreProjComparison k m n) :
    binaryProjectiveScheme k m n ⟶
      scheme k (segreDimension m n) := by
  letI := D.setLike
  letI := D.addSubgroupClass
  letI := D.gradedRing
  exact
    D.productIso.hom ≫
      Proj.map
        (segreRangeGradedHom
          k m n D.grading D.map_mem)
        D.irrelevant_le

theorem isClosedImmersion_toProjective
    (D : SegreProjComparison k m n) :
    IsClosedImmersion D.toProjective := by
  letI := D.setLike
  letI := D.addSubgroupClass
  letI := D.gradedRing
  dsimp only [toProjective]
  letI :
      IsClosedImmersion
        (Proj.map
          (segreRangeGradedHom
            k m n D.grading D.map_mem)
          D.irrelevant_le) :=
    isClosedImmersion_projMap_of_surjective
      (segreRangeGradedHom
        k m n D.grading D.map_mem)
      D.irrelevant_le
      (segreRangeCoordinateHom_surjective k m n)
  infer_instance

@[reassoc]
theorem toProjective_toSpec
    (D : SegreProjComparison k m n) :
    D.toProjective ≫
        toSpec k (segreDimension m n) =
      binaryProjectiveToSpec k m n := by
  letI := D.setLike
  letI := D.addSubgroupClass
  letI := D.gradedRing
  dsimp only [toProjective]
  rw [Category.assoc]
  exact D.overBase

end SegreProjComparison

/-- The family of geometric `Proj` comparisons which remains to
construct in order to obtain all standard Segre embeddings. -/
def StandardSegreProjComparisons
    (k : Type u) [CommRing k] : Prop :=
  ∀ (m n : ℕ),
    Nonempty (SegreProjComparison k m n)

/-- The exact `Proj` comparisons imply the scheme-level Segre interface
used by finite products of projective models. -/
theorem standardSegreEmbeddings_of_projComparisons
    (k : Type u) [CommRing k]
    (h : StandardSegreProjComparisons k) :
    StandardSegreEmbeddings k := by
  intro m n
  obtain ⟨D⟩ := h m n
  exact
    ⟨segreDimension m n, D.toProjective,
      D.isClosedImmersion_toProjective,
      D.toProjective_toSpec⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
