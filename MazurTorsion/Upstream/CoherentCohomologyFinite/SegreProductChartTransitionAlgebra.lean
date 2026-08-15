/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreProductStandardOverlap

/-!
# Transition maps between product charts

On the overlap of the product charts `(i,j)` and `(a,b)`, the two
factor transition functions are units because their product is the
element inverted in the overlap ring.  This file constructs the
resulting maps from the second pair of projective chart rings into the
first overlap ring.
-/

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The first factor of the first product chart, mapped to the
localized overlap ring. -/
def segreProductOverlapLeftRingHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway k m i →+*
      SegreProductChartOverlapRing k m n i a j b :=
  (algebraMap
      (SegreProductChartRing k m n i j)
      (SegreProductChartOverlapRing k m n i a j b)).comp
    (Algebra.TensorProduct.includeLeftRingHom :
      ProjectiveCoordinateAway k m i →+*
        SegreProductChartRing k m n i j)

/-- The second factor of the first product chart, mapped to the
localized overlap ring. -/
def segreProductOverlapRightRingHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway k n j →+*
      SegreProductChartOverlapRing k m n i a j b :=
  (algebraMap
      (SegreProductChartRing k m n i j)
      (SegreProductChartOverlapRing k m n i a j b)).comp
    ((Algebra.TensorProduct.includeRight :
      ProjectiveCoordinateAway k n j →ₐ[k]
        SegreProductChartRing k m n i j).toRingHom)

lemma segreProductOverlapLeftRatio_isUnit
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    IsUnit
      (segreProductOverlapLeftRingHom k m n i a j b
        (projectiveCoordinateRatio k m i a)) := by
  have hproduct :
      IsUnit
        (algebraMap
          (SegreProductChartRing k m n i j)
          (SegreProductChartOverlapRing k m n i a j b)
          (segreProductChartTransition k m n i a j b)) :=
    IsLocalization.Away.algebraMap_isUnit
      (segreProductChartTransition k m n i a j b)
  have hmul :
      segreProductOverlapLeftRingHom k m n i a j b
            (projectiveCoordinateRatio k m i a) *
          segreProductOverlapRightRingHom k m n i a j b
            (projectiveCoordinateRatio k n j b) =
        algebraMap
          (SegreProductChartRing k m n i j)
          (SegreProductChartOverlapRing k m n i a j b)
          (segreProductChartTransition k m n i a j b) := by
    simp [segreProductOverlapLeftRingHom,
      segreProductOverlapRightRingHom,
      segreProductChartTransition]
    rw [← map_mul]
    simp
  rw [← hmul] at hproduct
  exact (IsUnit.mul_iff.mp hproduct).1

lemma segreProductOverlapRightRatio_isUnit
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    IsUnit
      (segreProductOverlapRightRingHom k m n i a j b
        (projectiveCoordinateRatio k n j b)) := by
  have hproduct :
      IsUnit
        (algebraMap
          (SegreProductChartRing k m n i j)
          (SegreProductChartOverlapRing k m n i a j b)
          (segreProductChartTransition k m n i a j b)) :=
    IsLocalization.Away.algebraMap_isUnit
      (segreProductChartTransition k m n i a j b)
  have hmul :
      segreProductOverlapLeftRingHom k m n i a j b
            (projectiveCoordinateRatio k m i a) *
          segreProductOverlapRightRingHom k m n i a j b
            (projectiveCoordinateRatio k n j b) =
        algebraMap
          (SegreProductChartRing k m n i j)
          (SegreProductChartOverlapRing k m n i a j b)
          (segreProductChartTransition k m n i a j b) := by
    simp [segreProductOverlapLeftRingHom,
      segreProductOverlapRightRingHom,
      segreProductChartTransition]
    rw [← map_mul]
    simp
  rw [← hmul] at hproduct
  exact (IsUnit.mul_iff.mp hproduct).2

/-- The double homogeneous localization for two standard charts in
one projective-space factor. -/
abbrev ProjectiveCoordinateOverlapAway
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) :=
  Away
    (homogeneousGrading k d)
    (coordinate k i * coordinate k a)

instance projectiveCoordinateOverlapAwayAlgebra
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) :
    Algebra k (ProjectiveCoordinateOverlapAway k d i a) :=
  homogeneousAwayCoefficientAlgebra
    k (MvPolynomial (Fin (d + 1)) k)
    (homogeneousGrading k d)
    (coordinate k i * coordinate k a)

/-- Map the double homogeneous localization in the first projective
factor to the product-chart overlap ring. -/
def segreProductLeftOverlapLift
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateOverlapAway k m i a →+*
      SegreProductChartOverlapRing k m n i a j b := by
  letI :=
    (awayMap
      (homogeneousGrading k m)
      (coordinate_mem_degreeOne k a)
      (rfl :
        coordinate k i * coordinate k a =
          coordinate k i * coordinate k a)).toAlgebra
  letI :
      IsLocalization.Away
        (projectiveCoordinateRatio k m i a)
        (ProjectiveCoordinateOverlapAway k m i a) := by
    rw [← chartRatio_eq_projectiveCoordinateRatio]
    exact chartRatio_isLocalization k m a i
  exact
    IsLocalization.Away.lift
      (projectiveCoordinateRatio k m i a)
      (segreProductOverlapLeftRatio_isUnit
        k m n i a j b)

/-- Map the double homogeneous localization in the second projective
factor to the product-chart overlap ring. -/
def segreProductRightOverlapLift
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateOverlapAway k n j b →+*
      SegreProductChartOverlapRing k m n i a j b := by
  letI :=
    (awayMap
      (homogeneousGrading k n)
      (coordinate_mem_degreeOne k b)
      (rfl :
        coordinate k j * coordinate k b =
          coordinate k j * coordinate k b)).toAlgebra
  letI :
      IsLocalization.Away
        (projectiveCoordinateRatio k n j b)
        (ProjectiveCoordinateOverlapAway k n j b) := by
    rw [← chartRatio_eq_projectiveCoordinateRatio]
    exact chartRatio_isLocalization k n b j
  exact
    IsLocalization.Away.lift
      (projectiveCoordinateRatio k n j b)
      (segreProductOverlapRightRatio_isUnit
        k m n i a j b)

/-- The second chart of the first projective factor maps to the common
double homogeneous localization. -/
def projectiveSecondChartToOverlapAway
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) :
    ProjectiveCoordinateAway k d a →+*
      ProjectiveCoordinateOverlapAway k d i a :=
  awayMap
    (homogeneousGrading k d)
    (coordinate_mem_degreeOne k i)
    (mul_comm (coordinate k i) (coordinate k a))

/-- The first chart maps to the common double homogeneous
localization by the canonical homogeneous away map. -/
def projectiveFirstChartToOverlapAway
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) :
    ProjectiveCoordinateAway k d i →+*
      ProjectiveCoordinateOverlapAway k d i a :=
  awayMap
    (homogeneousGrading k d)
    (coordinate_mem_degreeOne k a)
    rfl

lemma projectiveFirstChartToOverlapAway_algebraMap
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) (r : k) :
    projectiveFirstChartToOverlapAway k d i a
        (algebraMap k (ProjectiveCoordinateAway k d i) r) =
      algebraMap k
        (ProjectiveCoordinateOverlapAway k d i a) r := by
  rw [homogeneousAway_algebraMap_eq_mk
    (coordinate k i)
    (coordinate_mem_degreeOne k i) r]
  change
    awayMap
        (homogeneousGrading k d)
        (coordinate_mem_degreeOne k a)
        rfl
        (Away.mk
          (homogeneousGrading k d)
          (coordinate_mem_degreeOne k i)
          0
          (algebraMap k
            (MvPolynomial (Fin (d + 1)) k) r) _) =
      _
  rw [HomogeneousLocalization.awayMap_mk]
  rw [homogeneousAway_algebraMap_eq_mk
    (coordinate k i * coordinate k a)
    (SetLike.mul_mem_graded
      (coordinate_mem_degreeOne k i)
      (coordinate_mem_degreeOne k a)) r]
  apply HomogeneousLocalization.val_injective
  simp

lemma projectiveSecondChartToOverlapAway_algebraMap
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) (r : k) :
    projectiveSecondChartToOverlapAway k d i a
        (algebraMap k (ProjectiveCoordinateAway k d a) r) =
      algebraMap k
        (ProjectiveCoordinateOverlapAway k d i a) r := by
  rw [homogeneousAway_algebraMap_eq_mk
    (coordinate k a)
    (coordinate_mem_degreeOne k a) r]
  change
    awayMap
        (homogeneousGrading k d)
        (coordinate_mem_degreeOne k i)
        (mul_comm (coordinate k i) (coordinate k a))
        (Away.mk
          (homogeneousGrading k d)
          (coordinate_mem_degreeOne k a)
          0
          (algebraMap k
            (MvPolynomial (Fin (d + 1)) k) r) _) =
      _
  rw [HomogeneousLocalization.awayMap_mk]
  rw [homogeneousAway_algebraMap_eq_mk
    (coordinate k i * coordinate k a)
    (SetLike.mul_mem_graded
      (coordinate_mem_degreeOne k i)
      (coordinate_mem_degreeOne k a)) r]
  apply HomogeneousLocalization.val_injective
  simp

@[reassoc]
lemma projectiveFirstChartToOverlapAway_toProj
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) :
    Spec.map
          (CommRingCat.ofHom
            (projectiveFirstChartToOverlapAway k d i a)) ≫
        Proj.awayι
          (homogeneousGrading k d)
          (coordinate k i)
          (coordinate_mem_degreeOne k i)
          Nat.zero_lt_one =
      Proj.awayι
        (homogeneousGrading k d)
        (coordinate k i * coordinate k a)
        (SetLike.mul_mem_graded
          (coordinate_mem_degreeOne k i)
          (coordinate_mem_degreeOne k a))
        (by omega) := by
  exact
    Proj.SpecMap_awayMap_awayι
      (homogeneousGrading k d)
      (coordinate_mem_degreeOne k i)
      Nat.zero_lt_one
      (coordinate_mem_degreeOne k a)
      rfl

@[reassoc]
lemma projectiveSecondChartToOverlapAway_toProj
    (k : Type u) [CommRing k] (d : ℕ)
    (i a : Fin (d + 1)) :
    Spec.map
          (CommRingCat.ofHom
            (projectiveSecondChartToOverlapAway k d i a)) ≫
        Proj.awayι
          (homogeneousGrading k d)
          (coordinate k a)
          (coordinate_mem_degreeOne k a)
          Nat.zero_lt_one =
      Proj.awayι
        (homogeneousGrading k d)
        (coordinate k i * coordinate k a)
        (SetLike.mul_mem_graded
          (coordinate_mem_degreeOne k i)
          (coordinate_mem_degreeOne k a))
        (by omega) := by
  exact
    Proj.SpecMap_awayMap_awayι
      (homogeneousGrading k d)
      (coordinate_mem_degreeOne k a)
      Nat.zero_lt_one
      (coordinate_mem_degreeOne k i)
      (mul_comm (coordinate k i) (coordinate k a))

/-- The first factor of the second product chart, expressed in the
localization model of the overlap. -/
def segreProductSecondLeftRingHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway k m a →+*
      SegreProductChartOverlapRing k m n i a j b :=
  (segreProductLeftOverlapLift k m n i a j b).comp
    (projectiveSecondChartToOverlapAway k m i a)

/-- The second factor of the second product chart, expressed in the
localization model of the overlap. -/
def segreProductSecondRightRingHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway k n b →+*
      SegreProductChartOverlapRing k m n i a j b :=
  (segreProductRightOverlapLift k m n i a j b).comp
    (projectiveSecondChartToOverlapAway k n j b)

lemma segreProductLeftOverlapLift_comp_first
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductLeftOverlapLift k m n i a j b).comp
        (projectiveFirstChartToOverlapAway k m i a) =
      segreProductOverlapLeftRingHom k m n i a j b := by
  letI :=
    (awayMap
      (homogeneousGrading k m)
      (coordinate_mem_degreeOne k a)
      (rfl :
        coordinate k i * coordinate k a =
          coordinate k i * coordinate k a)).toAlgebra
  letI :
      IsLocalization.Away
        (projectiveCoordinateRatio k m i a)
        (ProjectiveCoordinateOverlapAway k m i a) := by
    rw [← chartRatio_eq_projectiveCoordinateRatio]
    exact chartRatio_isLocalization k m a i
  change
    (IsLocalization.Away.lift
        (projectiveCoordinateRatio k m i a)
        (segreProductOverlapLeftRatio_isUnit
          k m n i a j b)).comp
          (algebraMap
            (ProjectiveCoordinateAway k m i)
            (ProjectiveCoordinateOverlapAway k m i a)) =
      segreProductOverlapLeftRingHom k m n i a j b
  exact
    IsLocalization.Away.lift_comp
      (projectiveCoordinateRatio k m i a)
      (segreProductOverlapLeftRatio_isUnit
        k m n i a j b)

lemma segreProductRightOverlapLift_comp_first
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductRightOverlapLift k m n i a j b).comp
        (projectiveFirstChartToOverlapAway k n j b) =
      segreProductOverlapRightRingHom k m n i a j b := by
  letI :=
    (awayMap
      (homogeneousGrading k n)
      (coordinate_mem_degreeOne k b)
      (rfl :
        coordinate k j * coordinate k b =
          coordinate k j * coordinate k b)).toAlgebra
  letI :
      IsLocalization.Away
        (projectiveCoordinateRatio k n j b)
        (ProjectiveCoordinateOverlapAway k n j b) := by
    rw [← chartRatio_eq_projectiveCoordinateRatio]
    exact chartRatio_isLocalization k n b j
  change
    (IsLocalization.Away.lift
        (projectiveCoordinateRatio k n j b)
        (segreProductOverlapRightRatio_isUnit
          k m n i a j b)).comp
          (algebraMap
            (ProjectiveCoordinateAway k n j)
            (ProjectiveCoordinateOverlapAway k n j b)) =
      segreProductOverlapRightRingHom k m n i a j b
  exact
    IsLocalization.Away.lift_comp
      (projectiveCoordinateRatio k n j b)
      (segreProductOverlapRightRatio_isUnit
        k m n i a j b)

lemma segreProductOverlapLeftRingHom_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreProductOverlapLeftRingHom k m n i a j b
        (algebraMap k (ProjectiveCoordinateAway k m i) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r := by
  simp [segreProductOverlapLeftRingHom]
  change
    algebraMap
        (SegreProductChartRing k m n i j)
        (SegreProductChartOverlapRing k m n i a j b)
        (algebraMap k
          (SegreProductChartRing k m n i j) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r
  exact
    (IsScalarTower.algebraMap_apply
      k
      (SegreProductChartRing k m n i j)
      (SegreProductChartOverlapRing k m n i a j b)
      r).symm

lemma segreProductOverlapRightRingHom_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreProductOverlapRightRingHom k m n i a j b
        (algebraMap k (ProjectiveCoordinateAway k n j) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r := by
  simp [segreProductOverlapRightRingHom]
  change
    algebraMap
        (SegreProductChartRing k m n i j)
        (SegreProductChartOverlapRing k m n i a j b)
        (algebraMap k
          (SegreProductChartRing k m n i j) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r
  exact
    (IsScalarTower.algebraMap_apply
      k
      (SegreProductChartRing k m n i j)
      (SegreProductChartOverlapRing k m n i a j b)
      r).symm

lemma segreProductLeftOverlapLift_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreProductLeftOverlapLift k m n i a j b
        (algebraMap k
          (ProjectiveCoordinateOverlapAway k m i a) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r := by
  rw [← projectiveFirstChartToOverlapAway_algebraMap
    k m i a r]
  change
    ((segreProductLeftOverlapLift k m n i a j b).comp
      (projectiveFirstChartToOverlapAway k m i a))
        (algebraMap k
          (ProjectiveCoordinateAway k m i) r) =
      _
  rw [segreProductLeftOverlapLift_comp_first]
  exact
    segreProductOverlapLeftRingHom_algebraMap
      k m n i a j b r

lemma segreProductRightOverlapLift_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreProductRightOverlapLift k m n i a j b
        (algebraMap k
          (ProjectiveCoordinateOverlapAway k n j b) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r := by
  rw [← projectiveFirstChartToOverlapAway_algebraMap
    k n j b r]
  change
    ((segreProductRightOverlapLift k m n i a j b).comp
      (projectiveFirstChartToOverlapAway k n j b))
        (algebraMap k
          (ProjectiveCoordinateAway k n j) r) =
      _
  rw [segreProductRightOverlapLift_comp_first]
  exact
    segreProductOverlapRightRingHom_algebraMap
      k m n i a j b r

lemma segreProductSecondLeftRingHom_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreProductSecondLeftRingHom k m n i a j b
        (algebraMap k (ProjectiveCoordinateAway k m a) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r := by
  rw [segreProductSecondLeftRingHom,
    RingHom.comp_apply,
    projectiveSecondChartToOverlapAway_algebraMap,
    segreProductLeftOverlapLift_algebraMap]

lemma segreProductSecondRightRingHom_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreProductSecondRightRingHom k m n i a j b
        (algebraMap k (ProjectiveCoordinateAway k n b) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r := by
  rw [segreProductSecondRightRingHom,
    RingHom.comp_apply,
    projectiveSecondChartToOverlapAway_algebraMap,
    segreProductRightOverlapLift_algebraMap]

/-- The first factor of the second product chart as a coefficient
algebra map into the overlap ring. -/
def segreProductSecondLeftAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway k m a →ₐ[k]
      SegreProductChartOverlapRing k m n i a j b where
  __ := segreProductSecondLeftRingHom k m n i a j b
  commutes' :=
    segreProductSecondLeftRingHom_algebraMap
      k m n i a j b

/-- The second factor of the second product chart as a coefficient
algebra map into the overlap ring. -/
def segreProductSecondRightAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    ProjectiveCoordinateAway k n b →ₐ[k]
      SegreProductChartOverlapRing k m n i a j b where
  __ := segreProductSecondRightRingHom k m n i a j b
  commutes' :=
    segreProductSecondRightRingHom_algebraMap
      k m n i a j b

/-- The transition homomorphism from the second product chart ring to
the localization model of the overlap. -/
def segreProductSecondChartAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreProductChartRing k m n a b →ₐ[k]
      SegreProductChartOverlapRing k m n i a j b :=
  Algebra.TensorProduct.lift
    (segreProductSecondLeftAlgHom k m n i a j b)
    (segreProductSecondRightAlgHom k m n i a j b)
    (fun _ _ => Commute.all _ _)

lemma segreProductSecondChartAlgHom_comp_left
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductSecondChartAlgHom k m n i a j b).comp
        (Algebra.TensorProduct.includeLeft :
          ProjectiveCoordinateAway k m a →ₐ[k]
            SegreProductChartRing k m n a b) =
      segreProductSecondLeftAlgHom k m n i a j b := by
  exact
    Algebra.TensorProduct.lift_comp_includeLeft
      (segreProductSecondLeftAlgHom k m n i a j b)
      (segreProductSecondRightAlgHom k m n i a j b)
      (fun _ _ => Commute.all _ _)

lemma segreProductSecondChartAlgHom_comp_right
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductSecondChartAlgHom k m n i a j b).comp
        (Algebra.TensorProduct.includeRight :
          ProjectiveCoordinateAway k n b →ₐ[k]
            SegreProductChartRing k m n a b) =
      segreProductSecondRightAlgHom k m n i a j b := by
  exact
    Algebra.TensorProduct.lift_comp_includeRight
      (segreProductSecondLeftAlgHom k m n i a j b)
      (segreProductSecondRightAlgHom k m n i a j b)
      (fun _ _ => Commute.all _ _)

/-- On the overlap, the first and second affine charts in the first
projective factor define the same morphism to projective space. -/
lemma segreProductOverlapLeftChartTransition_toProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec.map
          (CommRingCat.ofHom
            (segreProductOverlapLeftRingHom
              k m n i a j b)) ≫
        Proj.awayι
          (homogeneousGrading k m)
          (coordinate k i)
          (coordinate_mem_degreeOne k i)
          Nat.zero_lt_one =
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondLeftRingHom
              k m n i a j b)) ≫
        Proj.awayι
          (homogeneousGrading k m)
          (coordinate k a)
          (coordinate_mem_degreeOne k a)
          Nat.zero_lt_one := by
  let liftMap :=
    Spec.map
      (CommRingCat.ofHom
        (segreProductLeftOverlapLift k m n i a j b))
  calc
    _ = (liftMap ≫
          Spec.map
            (CommRingCat.ofHom
              (projectiveFirstChartToOverlapAway
                k m i a))) ≫
          Proj.awayι
            (homogeneousGrading k m)
            (coordinate k i)
            (coordinate_mem_degreeOne k i)
            Nat.zero_lt_one := by
      rw [← Spec.map_comp]
      have hcat :
          CommRingCat.ofHom
                (projectiveFirstChartToOverlapAway k m i a) ≫
              CommRingCat.ofHom
                (segreProductLeftOverlapLift k m n i a j b) =
            CommRingCat.ofHom
              (segreProductOverlapLeftRingHom
                k m n i a j b) := by
        ext x
        exact
          DFunLike.congr_fun
            (segreProductLeftOverlapLift_comp_first
              k m n i a j b) x
      rw [hcat]
    _ = liftMap ≫
          (Spec.map
              (CommRingCat.ofHom
                (projectiveFirstChartToOverlapAway
                  k m i a)) ≫
            Proj.awayι
              (homogeneousGrading k m)
              (coordinate k i)
              (coordinate_mem_degreeOne k i)
              Nat.zero_lt_one) := by
      rw [Category.assoc]
    _ = liftMap ≫
          Proj.awayι
            (homogeneousGrading k m)
            (coordinate k i * coordinate k a)
            (SetLike.mul_mem_graded
              (coordinate_mem_degreeOne k i)
              (coordinate_mem_degreeOne k a))
            (by omega) := by
      rw [projectiveFirstChartToOverlapAway_toProj]
    _ = liftMap ≫
          (Spec.map
              (CommRingCat.ofHom
                (projectiveSecondChartToOverlapAway
                  k m i a)) ≫
            Proj.awayι
              (homogeneousGrading k m)
              (coordinate k a)
              (coordinate_mem_degreeOne k a)
              Nat.zero_lt_one) := by
      rw [projectiveSecondChartToOverlapAway_toProj]
    _ = (liftMap ≫
          Spec.map
            (CommRingCat.ofHom
              (projectiveSecondChartToOverlapAway
                k m i a))) ≫
          Proj.awayι
            (homogeneousGrading k m)
            (coordinate k a)
            (coordinate_mem_degreeOne k a)
            Nat.zero_lt_one := by
      rw [Category.assoc]
    _ = _ := by
      rw [← Spec.map_comp]
      rfl

/-- On the overlap, the first and second affine charts in the second
projective factor define the same morphism to projective space. -/
lemma segreProductOverlapRightChartTransition_toProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec.map
          (CommRingCat.ofHom
            (segreProductOverlapRightRingHom
              k m n i a j b)) ≫
        Proj.awayι
          (homogeneousGrading k n)
          (coordinate k j)
          (coordinate_mem_degreeOne k j)
          Nat.zero_lt_one =
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondRightRingHom
              k m n i a j b)) ≫
        Proj.awayι
          (homogeneousGrading k n)
          (coordinate k b)
          (coordinate_mem_degreeOne k b)
          Nat.zero_lt_one := by
  let liftMap :=
    Spec.map
      (CommRingCat.ofHom
        (segreProductRightOverlapLift k m n i a j b))
  calc
    _ = (liftMap ≫
          Spec.map
            (CommRingCat.ofHom
              (projectiveFirstChartToOverlapAway
                k n j b))) ≫
          Proj.awayι
            (homogeneousGrading k n)
            (coordinate k j)
            (coordinate_mem_degreeOne k j)
            Nat.zero_lt_one := by
      rw [← Spec.map_comp]
      have hcat :
          CommRingCat.ofHom
                (projectiveFirstChartToOverlapAway k n j b) ≫
              CommRingCat.ofHom
                (segreProductRightOverlapLift k m n i a j b) =
            CommRingCat.ofHom
              (segreProductOverlapRightRingHom
                k m n i a j b) := by
        ext x
        exact
          DFunLike.congr_fun
            (segreProductRightOverlapLift_comp_first
              k m n i a j b) x
      rw [hcat]
    _ = liftMap ≫
          (Spec.map
              (CommRingCat.ofHom
                (projectiveFirstChartToOverlapAway
                  k n j b)) ≫
            Proj.awayι
              (homogeneousGrading k n)
              (coordinate k j)
              (coordinate_mem_degreeOne k j)
              Nat.zero_lt_one) := by
      rw [Category.assoc]
    _ = liftMap ≫
          Proj.awayι
            (homogeneousGrading k n)
            (coordinate k j * coordinate k b)
            (SetLike.mul_mem_graded
              (coordinate_mem_degreeOne k j)
              (coordinate_mem_degreeOne k b))
            (by omega) := by
      rw [projectiveFirstChartToOverlapAway_toProj]
    _ = liftMap ≫
          (Spec.map
              (CommRingCat.ofHom
                (projectiveSecondChartToOverlapAway
                  k n j b)) ≫
            Proj.awayι
              (homogeneousGrading k n)
              (coordinate k b)
              (coordinate_mem_degreeOne k b)
              Nat.zero_lt_one) := by
      rw [projectiveSecondChartToOverlapAway_toProj]
    _ = (liftMap ≫
          Spec.map
            (CommRingCat.ofHom
              (projectiveSecondChartToOverlapAway
                k n j b))) ≫
          Proj.awayι
            (homogeneousGrading k n)
            (coordinate k b)
            (coordinate_mem_degreeOne k b)
            Nat.zero_lt_one := by
      rw [Category.assoc]
    _ = _ := by
      rw [← Spec.map_comp]
      rfl

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
