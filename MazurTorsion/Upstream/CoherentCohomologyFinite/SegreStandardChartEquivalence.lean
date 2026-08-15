/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreImageChartGeneration

/-!
# The standard Segre chart equivalence

The forward dehomogenization map and the anchor-insertion map are
inverse on each standard chart.
-/

open MvPolynomial
open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

lemma segreChartNumeratorHom_leftAnchor
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (p : MvPolynomial (Fin (m + 1)) k) :
    segreChartNumeratorHom k m n i j
        (segreLeftAnchorHom k m n j p) =
      (projectiveCoordinateDehomogenization k m i p) ⊗ₜ[k]
        (1 : ProjectiveCoordinateAway k n j) := by
  change
    ((segreChartNumeratorHom k m n i j).comp
        (segreLeftAnchorHom k m n j)) p =
      ((Algebra.TensorProduct.includeLeft :
          ProjectiveCoordinateAway k m i →ₐ[k]
            SegreProductChartRing k m n i j).comp
        (projectiveCoordinateDehomogenization k m i)) p
  congr 1
  ext a
  simp [Algebra.TensorProduct.one_def]

lemma segreChartNumeratorHom_rightAnchor
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (p : MvPolynomial (Fin (n + 1)) k) :
    segreChartNumeratorHom k m n i j
        (segreRightAnchorHom k m n i p) =
      (1 : ProjectiveCoordinateAway k m i) ⊗ₜ[k]
        projectiveCoordinateDehomogenization k n j p := by
  change
    ((segreChartNumeratorHom k m n i j).comp
        (segreRightAnchorHom k m n i)) p =
      ((Algebra.TensorProduct.includeRight :
          ProjectiveCoordinateAway k n j →ₐ[k]
            SegreProductChartRing k m n i j).comp
        (projectiveCoordinateDehomogenization k n j)) p
  congr 1
  ext b
  simp [Algebra.TensorProduct.one_def]

lemma segreChartForwardAlgHom_left_ratio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (a : Fin (m + 1)) :
    segreChartForwardAlgHom k m n i j
        (segreLeftChartToImageAlgHom k m n i j
          (projectiveCoordinateRatio k m i a)) =
      (Algebra.TensorProduct.includeLeft :
        ProjectiveCoordinateAway k m i →ₐ[k]
          SegreProductChartRing k m n i j)
        (projectiveCoordinateRatio k m i a) := by
  rw [segreLeftChartToImageAlgHom_ratio,
    segreChartForwardAlgHom_ratio]
  simp [Algebra.TensorProduct.one_def]

lemma segreChartForwardAlgHom_comp_left
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartForwardAlgHom k m n i j).comp
        (segreLeftChartToImageAlgHom k m n i j) =
      (Algebra.TensorProduct.includeLeft :
        ProjectiveCoordinateAway k m i →ₐ[k]
          SegreProductChartRing k m n i j) := by
  apply
    (AlgHom.cancel_right
      (projectiveCoordinateDehomogenization_surjective
        k m i)).mp
  ext a
  simpa using
    segreChartForwardAlgHom_left_ratio
      k m n i j a

lemma segreChartForwardAlgHom_right_ratio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (b : Fin (n + 1)) :
    segreChartForwardAlgHom k m n i j
        (segreRightChartToImageAlgHom k m n i j
          (projectiveCoordinateRatio k n j b)) =
      (Algebra.TensorProduct.includeRight :
        ProjectiveCoordinateAway k n j →ₐ[k]
          SegreProductChartRing k m n i j)
        (projectiveCoordinateRatio k n j b) := by
  rw [segreRightChartToImageAlgHom_ratio,
    segreChartForwardAlgHom_ratio]
  simp

lemma segreChartForwardAlgHom_comp_right
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartForwardAlgHom k m n i j).comp
        (segreRightChartToImageAlgHom k m n i j) =
      (Algebra.TensorProduct.includeRight :
        ProjectiveCoordinateAway k n j →ₐ[k]
          SegreProductChartRing k m n i j) := by
  apply
    (AlgHom.cancel_right
      (projectiveCoordinateDehomogenization_surjective
        k n j)).mp
  ext b
  simpa using
    segreChartForwardAlgHom_right_ratio
      k m n i j b

/-- Dehomogenization after anchor insertion is the identity on the
product standard chart. -/
lemma segreChartForwardAlgHom_comp_inverse
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartForwardAlgHom k m n i j).comp
        (segreChartInverseAlgHom k m n i j) =
      AlgHom.id k (SegreProductChartRing k m n i j) := by
  apply Algebra.TensorProduct.ext
  · ext x
    change
      segreChartForwardAlgHom k m n i j
          (segreChartInverseAlgHom k m n i j
            ((Algebra.TensorProduct.includeLeft :
              ProjectiveCoordinateAway k m i →ₐ[k]
                SegreProductChartRing k m n i j) x)) =
        (Algebra.TensorProduct.includeLeft :
          ProjectiveCoordinateAway k m i →ₐ[k]
            SegreProductChartRing k m n i j) x
    rw [show
      segreChartInverseAlgHom k m n i j
          ((Algebra.TensorProduct.includeLeft :
            ProjectiveCoordinateAway k m i →ₐ[k]
              SegreProductChartRing k m n i j) x) =
        segreLeftChartToImageAlgHom k m n i j x by
      simp [segreChartInverseAlgHom]]
    exact
      AlgHom.congr_fun
        (segreChartForwardAlgHom_comp_left
          k m n i j) x
  · ext y
    change
      segreChartForwardAlgHom k m n i j
          (segreChartInverseAlgHom k m n i j
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway k n j →ₐ[k]
                SegreProductChartRing k m n i j) y)) =
        (Algebra.TensorProduct.includeRight :
          ProjectiveCoordinateAway k n j →ₐ[k]
            SegreProductChartRing k m n i j) y
    rw [show
      segreChartInverseAlgHom k m n i j
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway k n j →ₐ[k]
              SegreProductChartRing k m n i j) y) =
        segreRightChartToImageAlgHom k m n i j y by
      simp [segreChartInverseAlgHom]]
    exact
      AlgHom.congr_fun
        (segreChartForwardAlgHom_comp_right
          k m n i j) y

/-- Anchor insertion after dehomogenization fixes each standard Segre
coordinate ratio. -/
lemma segreChartInverseAlgHom_forward_ratio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreChartInverseAlgHom k m n i j
        (segreChartForwardAlgHom k m n i j
          (segreImageChartRatio k m n i a j b)) =
      segreImageChartRatio k m n i a j b := by
  rw [segreChartForwardAlgHom_ratio]
  change
    Algebra.TensorProduct.lift
        (segreLeftChartToImageAlgHom k m n i j)
        (segreRightChartToImageAlgHom k m n i j)
        (segreChartAnchorMaps_commute k m n i j)
        (projectiveCoordinateRatio k m i a ⊗ₜ[k]
          projectiveCoordinateRatio k n j b) =
      _
  rw [Algebra.TensorProduct.lift_tmul,
    segreLeftChartToImageAlgHom_ratio,
    segreRightChartToImageAlgHom_ratio,
    segreImageChartRatio_mul_anchorRatios]

/-- The two explicit chart maps are inverse in the other order as
well. -/
lemma segreChartInverseAlgHom_comp_forward
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreChartInverseAlgHom k m n i j).comp
        (segreChartForwardAlgHom k m n i j) =
      AlgHom.id k (SegreImageChartRing k m n i j) := by
  apply AlgHom.ext_of_adjoin_eq_top
    (segreImageCoordinateRatio_adjoin_eq_top
      k m n (segrePairIndex m n i j))
  intro x hx
  obtain ⟨s, rfl⟩ := hx
  let a := (segreIndexEquiv m n s).1
  let b := (segreIndexEquiv m n s).2
  have hs : segrePairIndex m n a b = s := by
    exact (segreIndexEquiv m n).symm_apply_apply s
  rw [← hs,
    segreImageCoordinateRatio_segrePairIndex]
  exact segreChartInverseAlgHom_forward_ratio
    k m n i a j b

/-- The coordinate-ring equivalence on a standard Segre chart. -/
def segreStandardChartAlgEquiv
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreImageChartRing k m n i j ≃ₐ[k]
      SegreProductChartRing k m n i j :=
  { segreChartForwardAlgHom k m n i j with
    invFun := segreChartInverseAlgHom k m n i j
    left_inv := fun x =>
      AlgHom.congr_fun
        (segreChartInverseAlgHom_comp_forward
          k m n i j) x
    right_inv := fun x =>
      AlgHom.congr_fun
        (segreChartForwardAlgHom_comp_inverse
          k m n i j) x }

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
