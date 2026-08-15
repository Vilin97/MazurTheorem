/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreStandardChartForward


/-!
# The inverse map on a standard Segre chart

Fixing the right anchor `j` sends `Xₐ` to the Segre coordinate
`XₐYⱼ`; fixing the left anchor `i` sends `Y_b` to `XᵢY_b`.
These graded maps induce maps from both projective chart rings to the
Segre-image chart ring.  Their tensor-product lift is the inverse
candidate to dehomogenization.
-/

open MvPolynomial
open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- Insert the left variables into the Segre variables along the
fixed right anchor `j`. -/
def segreLeftAnchorHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (j : Fin (n + 1)) :
    MvPolynomial (Fin (m + 1)) k →ₐ[k]
      SegreCoordinateRing k m n :=
  (segreRangeCoordinateHom k m n).comp
    (MvPolynomial.rename
      (fun a => segrePairIndex m n a j))

@[simp]
lemma segreLeftAnchorHom_X
    (k : Type u) [CommRing k] (m n : ℕ)
    (j : Fin (n + 1)) (a : Fin (m + 1)) :
    segreLeftAnchorHom k m n j (MvPolynomial.X a) =
      segreImageCoordinate k m n
        (segrePairIndex m n a j) := by
  simp [segreLeftAnchorHom, segreImageCoordinate]

lemma segreLeftAnchorHom_mem_grading
    (k : Type u) [CommRing k] (m n : ℕ)
    (j : Fin (n + 1)) {d : ℕ}
    {p : MvPolynomial (Fin (m + 1)) k}
    (hp : p ∈ homogeneousGrading k m d) :
    segreLeftAnchorHom k m n j p ∈
      segreImageGrading k m n d := by
  apply segreRangeCoordinateHom_mem_imageGrading
  exact hp.rename_isHomogeneous

/-- The left-anchor insertion as a graded ring homomorphism. -/
def segreLeftAnchorGradedHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (j : Fin (n + 1)) :
    homogeneousGrading k m →+*ᵍ
      segreImageGrading k m n where
  __ := (segreLeftAnchorHom k m n j).toRingHom
  map_mem := segreLeftAnchorHom_mem_grading k m n j

/-- The left-anchor insertion as a graded algebra homomorphism. -/
def segreLeftAnchorGradedAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (j : Fin (n + 1)) :
    homogeneousGrading k m →ₐᵍ[k]
      segreImageGrading k m n where
  __ := segreLeftAnchorHom k m n j
  map_mem := segreLeftAnchorHom_mem_grading k m n j

@[simp]
lemma segreLeftAnchorGradedHom_coordinate
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreLeftAnchorGradedHom k m n j
        (coordinate k i) =
      segreImageCoordinate k m n
        (segrePairIndex m n i j) := by
  simp [segreLeftAnchorGradedHom]

/-- Insert the right variables into the Segre variables along the
fixed left anchor `i`. -/
def segreRightAnchorHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k]
      SegreCoordinateRing k m n :=
  (segreRangeCoordinateHom k m n).comp
    (MvPolynomial.rename
      (fun b => segrePairIndex m n i b))

@[simp]
lemma segreRightAnchorHom_X
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (b : Fin (n + 1)) :
    segreRightAnchorHom k m n i (MvPolynomial.X b) =
      segreImageCoordinate k m n
        (segrePairIndex m n i b) := by
  simp [segreRightAnchorHom, segreImageCoordinate]

lemma segreRightAnchorHom_mem_grading
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) {d : ℕ}
    {p : MvPolynomial (Fin (n + 1)) k}
    (hp : p ∈ homogeneousGrading k n d) :
    segreRightAnchorHom k m n i p ∈
      segreImageGrading k m n d := by
  apply segreRangeCoordinateHom_mem_imageGrading
  exact hp.rename_isHomogeneous

/-- The right-anchor insertion as a graded ring homomorphism. -/
def segreRightAnchorGradedHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) :
    homogeneousGrading k n →+*ᵍ
      segreImageGrading k m n where
  __ := (segreRightAnchorHom k m n i).toRingHom
  map_mem := segreRightAnchorHom_mem_grading k m n i

/-- The right-anchor insertion as a graded algebra homomorphism. -/
def segreRightAnchorGradedAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) :
    homogeneousGrading k n →ₐᵍ[k]
      segreImageGrading k m n where
  __ := segreRightAnchorHom k m n i
  map_mem := segreRightAnchorHom_mem_grading k m n i

@[simp]
lemma segreRightAnchorGradedHom_coordinate
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreRightAnchorGradedHom k m n i
        (coordinate k j) =
      segreImageCoordinate k m n
        (segrePairIndex m n i j) := by
  simp [segreRightAnchorGradedHom]

/-- Map the left projective chart into the Segre-image chart. -/
abbrev segreLeftChartToImageRingHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway k m i →+*
      SegreImageChartRing k m n i j :=
  homogeneousAwayMapTo
    (segreLeftAnchorGradedHom k m n j)
    (coordinate k i)
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))
    (segreLeftAnchorGradedHom_coordinate
      k m n i j)

/-- Map the right projective chart into the Segre-image chart. -/
abbrev segreRightChartToImageRingHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway k n j →+*
      SegreImageChartRing k m n i j :=
  homogeneousAwayMapTo
    (segreRightAnchorGradedHom k m n i)
    (coordinate k j)
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))
    (segreRightAnchorGradedHom_coordinate
      k m n i j)

/-- The left projective-chart map as a coefficient-algebra map. -/
abbrev segreLeftChartToImageAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway k m i →ₐ[k]
      SegreImageChartRing k m n i j :=
  homogeneousAwayMapToAlgHom
    (segreLeftAnchorGradedAlgHom k m n j)
    (coordinate k i)
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))
    (by
      change segreLeftAnchorHom k m n j
          (coordinate k i) =
        segreImageCoordinate k m n
          (segrePairIndex m n i j)
      simp)
    (coordinate_mem_degreeOne k i)
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n i j))

/-- The right projective-chart map as a coefficient-algebra map. -/
abbrev segreRightChartToImageAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway k n j →ₐ[k]
      SegreImageChartRing k m n i j :=
  homogeneousAwayMapToAlgHom
    (segreRightAnchorGradedAlgHom k m n i)
    (coordinate k j)
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))
    (by
      change segreRightAnchorHom k m n i
          (coordinate k j) =
        segreImageCoordinate k m n
          (segrePairIndex m n i j)
      simp)
    (coordinate_mem_degreeOne k j)
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))

@[simp]
lemma segreLeftChartToImageRingHom_ratio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j : Fin (n + 1)) :
    segreLeftChartToImageRingHom k m n i j
        (projectiveCoordinateRatio k m i a) =
      segreImageChartRatio k m n i a j j := by
  unfold segreLeftChartToImageRingHom
  unfold projectiveCoordinateRatio segreImageChartRatio
  rw [homogeneousAwayMapTo_mk]
  congr 1
  exact segreLeftAnchorHom_X k m n j a
  exact
    segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n i j)

@[simp]
lemma segreLeftChartToImageAlgHom_ratio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j : Fin (n + 1)) :
    segreLeftChartToImageAlgHom k m n i j
        (projectiveCoordinateRatio k m i a) =
      segreImageChartRatio k m n i a j j := by
  exact segreLeftChartToImageRingHom_ratio k m n i a j

@[simp]
lemma segreRightChartToImageRingHom_ratio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreRightChartToImageRingHom k m n i j
        (projectiveCoordinateRatio k n j b) =
      segreImageChartRatio k m n i i j b := by
  unfold segreRightChartToImageRingHom
  unfold projectiveCoordinateRatio segreImageChartRatio
  rw [homogeneousAwayMapTo_mk]
  congr 1
  exact segreRightAnchorHom_X k m n i b
  exact
    segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n i j)

@[simp]
lemma segreRightChartToImageAlgHom_ratio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreRightChartToImageAlgHom k m n i j
        (projectiveCoordinateRatio k n j b) =
      segreImageChartRatio k m n i i j b := by
  exact segreRightChartToImageRingHom_ratio k m n i j b

lemma segreChartAnchorMaps_commute
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (x : ProjectiveCoordinateAway k m i)
    (y : ProjectiveCoordinateAway k n j) :
    Commute
      (segreLeftChartToImageAlgHom k m n i j x)
      (segreRightChartToImageAlgHom k m n i j y) :=
  Commute.all _ _

/-- Multiply the two anchor maps to obtain the inverse candidate on
the tensor-product chart ring. -/
def segreChartInverseAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreProductChartRing k m n i j →ₐ[k]
      SegreImageChartRing k m n i j :=
  Algebra.TensorProduct.lift
    (segreLeftChartToImageAlgHom k m n i j)
    (segreRightChartToImageAlgHom k m n i j)
    (segreChartAnchorMaps_commute k m n i j)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
