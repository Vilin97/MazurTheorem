/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCoordinateChartAlgebra
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreImageAffineCover


/-!
# The forward map on a standard Segre chart

On the chart where `XᵢYⱼ` is nonzero, a Segre coordinate
`XₐY_b` dehomogenizes to
`(Xₐ / Xᵢ) ⊗ (Y_b / Yⱼ)`.  This file constructs that map on
homogeneous-localization coordinate rings.
-/

open MvPolynomial
open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The Segre target coordinate indexed by the pair `(i,j)`. -/
def segrePairIndex
    (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Fin (segreDimension m n + 1) :=
  (segreIndexEquiv m n).symm (i, j)

@[simp]
lemma segreIndexEquiv_segrePairIndex
    (m n : ℕ) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreIndexEquiv m n (segrePairIndex m n i j) = (i, j) :=
  (segreIndexEquiv m n).apply_symm_apply (i, j)

/-- The degree-zero coordinate ring of the standard Segre-image chart
`D₊(XᵢYⱼ)`. -/
abbrev SegreImageChartRing
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :=
  Away
    (segreImageGrading k m n)
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))

noncomputable instance segreCoordinateRingSubmoduleAddSubgroupClass
    (k : Type u) [CommRing k] (m n : ℕ) :
    AddSubgroupClass
      (Submodule k (SegreCoordinateRing k m n))
      (SegreCoordinateRing k m n) :=
  @Submodule.addSubgroupClass
    k (SegreCoordinateRing k m n)
    inferInstance inferInstance inferInstance

noncomputable instance segreImageAwayCommRing
    (k : Type u) [CommRing k] (m n : ℕ)
    (f : SegreCoordinateRing k m n) :
    CommRing
      (Away (segreImageGrading k m n) f) :=
  @HomogeneousLocalization.homogeneousLocalizationCommRing
    ℕ (SegreCoordinateRing k m n)
    (Submodule k (SegreCoordinateRing k m n))
    inferInstance inferInstance
    (segreCoordinateRingSubmoduleAddSubgroupClass k m n)
    inferInstance inferInstance
    (segreImageGrading k m n)
    (segreImageGradingGradedRing k m n)
    (Submonoid.powers f)

instance segreImageAwayAlgebra
    (k : Type u) [CommRing k] (m n : ℕ)
    (f : SegreCoordinateRing k m n) :
    Algebra k (Away (segreImageGrading k m n) f) :=
  by
    letI : CommRing
        (Away (segreImageGrading k m n) f) :=
      segreImageAwayCommRing k m n f
    exact
      homogeneousAwayCoefficientAlgebra
        k (SegreCoordinateRing k m n)
        (segreImageGrading k m n)
        f

/-- The tensor product of the two standard projective chart rings. -/
abbrev SegreProductChartRing
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :=
  ProjectiveCoordinateAway k m i ⊗[k]
    ProjectiveCoordinateAway k n j

/-- Evaluate a Segre-image numerator on the product of the two
standard affine charts. -/
def segreChartNumeratorHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreCoordinateRing k m n →ₐ[k]
      SegreProductChartRing k m n i j :=
  (Algebra.TensorProduct.map
      (projectiveCoordinateDehomogenization k m i)
      (projectiveCoordinateDehomogenization k n j)).comp
    (Subalgebra.val (SegreCoordinateRing k m n))

@[simp]
lemma segreChartNumeratorHom_coordinate
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (s : Fin (segreDimension m n + 1)) :
    segreChartNumeratorHom k m n i j
        (segreImageCoordinate k m n s) =
      projectiveCoordinateRatio k m i
          (segreIndexEquiv m n s).1 ⊗ₜ[k]
        projectiveCoordinateRatio k n j
          (segreIndexEquiv m n s).2 := by
  simp [segreChartNumeratorHom, segreImageCoordinate]

@[simp]
lemma segreChartNumeratorHom_anchor
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreChartNumeratorHom k m n i j
        (segreImageCoordinate k m n
          (segrePairIndex m n i j)) = 1 := by
  simp [Algebra.TensorProduct.one_def]

/-- Forget that the Segre chart localization is homogeneous. -/
def segreImageChartValRingHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreImageChartRing k m n i j →+*
      Localization.Away
        (segreImageCoordinate k m n
          (segrePairIndex m n i j)) where
  toFun := HomogeneousLocalization.val
  map_zero' := HomogeneousLocalization.val_zero
  map_one' := HomogeneousLocalization.val_one
  map_add' := HomogeneousLocalization.val_add
  map_mul' := HomogeneousLocalization.val_mul

@[simp]
lemma segreImageChartValRingHom_apply
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (x : SegreImageChartRing k m n i j) :
    segreImageChartValRingHom k m n i j x =
      HomogeneousLocalization.val x :=
  rfl

/-- The forward ring map from a standard Segre-image chart to the
tensor product of the corresponding standard projective chart rings. -/
def segreChartForwardRingHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreImageChartRing k m n i j →+*
      SegreProductChartRing k m n i j :=
  (Localization.awayLift
      (segreChartNumeratorHom k m n i j).toRingHom
      (segreImageCoordinate k m n
        (segrePairIndex m n i j))
      (by
        change IsUnit
          (segreChartNumeratorHom k m n i j
            (segreImageCoordinate k m n
              (segrePairIndex m n i j)))
        rw [segreChartNumeratorHom_anchor]
        exact isUnit_one)).comp
    (segreImageChartValRingHom k m n i j)

/-- The forward chart map sends a homogeneous fraction `p/(XᵢYⱼ)ⁿ`
to the dehomogenized numerator. -/
lemma segreChartForwardRingHom_mk
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (q : ℕ) (p : SegreCoordinateRing k m n)
    (hp : p ∈ segreImageGrading k m n (q • 1)) :
    segreChartForwardRingHom k m n i j
        (Away.mk
          (segreImageGrading k m n)
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          q p hp) =
      segreChartNumeratorHom k m n i j p := by
  rw [segreChartForwardRingHom, RingHom.comp_apply,
    segreImageChartValRingHom_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk
    (segreChartNumeratorHom k m n i j).toRingHom
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))
    p (1 : SegreProductChartRing k m n i j)
    (by simp [Algebra.TensorProduct.one_def]) q]
  simp

/-- The forward chart map respects the coefficient algebra
structures. -/
def segreChartForwardAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    SegreImageChartRing k m n i j →ₐ[k]
      SegreProductChartRing k m n i j where
  __ := segreChartForwardRingHom k m n i j
  commutes' r := by
    rw [homogeneousAway_algebraMap_eq_mk
      (𝒜 := segreImageGrading k m n)
      (segreImageCoordinate k m n
        (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j)) r]
    change
      segreChartForwardRingHom k m n i j
          (Away.mk
            (segreImageGrading k m n)
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n i j))
            0 (algebraMap k
              (SegreCoordinateRing k m n) r) _) =
        algebraMap k (SegreProductChartRing k m n i j) r
    rw [segreChartForwardRingHom_mk]
    exact
      (segreChartNumeratorHom k m n i j).commutes r

/-- The regular function
`(XₐY_b)/(XᵢYⱼ)` on a standard Segre-image chart. -/
@[reducible]
def segreImageChartRatio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartRing k m n i j :=
  Away.mk
    (segreImageGrading k m n)
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n i j))
    1
    (segreImageCoordinate k m n
      (segrePairIndex m n a b))
    (by
      simpa using
        segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n a b))

@[simp]
lemma segreChartForwardAlgHom_ratio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreChartForwardAlgHom k m n i j
        (segreImageChartRatio k m n i a j b) =
      projectiveCoordinateRatio k m i a ⊗ₜ[k]
        projectiveCoordinateRatio k n j b := by
  change
    segreChartForwardRingHom k m n i j
        (Away.mk
          (segreImageGrading k m n)
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          1
          (segreImageCoordinate k m n
            (segrePairIndex m n a b))
          _) = _
  rw [segreChartForwardRingHom_mk,
    segreChartNumeratorHom_coordinate]
  simp

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
