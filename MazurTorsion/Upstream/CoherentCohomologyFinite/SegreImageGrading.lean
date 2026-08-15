/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreCoordinatePresentation
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring
import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas


/-!
# The canonical grading on the Segre image algebra

The tensor product of the two polynomial rings is graded by degree in
the second factor.  The Segre coordinate map preserves that grading.
Consequently its range is a homogeneous subalgebra, and intersecting
with the ambient homogeneous pieces gives the range algebra its
canonical grading.

This file constructs that grading.  After it, the only remaining Segre
input is the geometric identification of the product of projective
spaces with the `Proj` of this graded image algebra.
-/

open CategoryTheory AlgebraicGeometry
open MvPolynomial HomogeneousIdeal
open DirectSum
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The tensor-product ring containing the Segre coordinate algebra. -/
abbrev SegreTensorRing
    (k : Type u) [CommRing k] (m n : ℕ) :=
  MvPolynomial (Fin (m + 1)) k ⊗[k]
    MvPolynomial (Fin (n + 1)) k

/-- Grade the tensor-product ring by polynomial degree in its second
factor. -/
abbrev segreRightGrading
    (k : Type u) [CommRing k] (m n : ℕ) :
    ℕ → Submodule k (SegreTensorRing k m n) :=
  fun d =>
    ((homogeneousGrading k n d).baseChange
      (MvPolynomial (Fin (m + 1)) k)).restrictScalars k

instance segreRightGradingGradedRing
    (k : Type u) [CommRing k] (m n : ℕ) :
    GradedRing (segreRightGrading k m n) :=
  inferInstance

lemma segreStandardCoordinateValue_mem_degreeOne
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (segreDimension m n + 1)) :
    segreStandardCoordinateHom k m n
        (MvPolynomial.X i) ∈
      segreRightGrading k m n 1 := by
  rw [segreStandardCoordinateHom_X]
  exact Submodule.tmul_mem_baseChange_of_mem _
    (coordinate_mem_degreeOne k
      (segreIndexEquiv m n i).2)

lemma segreStandardCoordinateHom_eq_aeval
    (k : Type u) [CommRing k] (m n : ℕ) :
    segreStandardCoordinateHom k m n =
      MvPolynomial.aeval
        (fun i =>
          MvPolynomial.X (segreIndexEquiv m n i).1 ⊗ₜ[k]
            MvPolynomial.X (segreIndexEquiv m n i).2) := by
  ext i
  simp

/-- The Segre coordinate map preserves the standard degree, when the
tensor product is graded by degree in its second factor. -/
lemma segreStandardCoordinateHom_mem_grading
    (k : Type u) [CommRing k] (m n : ℕ)
    {d : ℕ}
    {p : MvPolynomial
      (Fin (segreDimension m n + 1)) k}
    (hp : p ∈ homogeneousGrading k
      (segreDimension m n) d) :
    segreStandardCoordinateHom k m n p ∈
      segreRightGrading k m n d := by
  rw [segreStandardCoordinateHom_eq_aeval]
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero =>
      exact (segreRightGrading k m n d).zero_mem
  | add p q hp hq ihp ihq =>
      simpa only [map_add] using
        (segreRightGrading k m n d).add_mem ihp ihq
  | monomial e r he =>
      rw [MvPolynomial.aeval_monomial]
      have hvariables :
          ∀ i ∈ e.support,
            (MvPolynomial.X
                  (segreIndexEquiv m n i).1 ⊗ₜ[k]
                MvPolynomial.X
                  (segreIndexEquiv m n i).2) ∈
              segreRightGrading k m n 1 := by
        intro i _
        simpa only [segreStandardCoordinateHom_X] using
          (segreStandardCoordinateValue_mem_degreeOne
            k m n i)
      have hproduct :
          e.prod
              (fun i exponent =>
                (MvPolynomial.X
                    (segreIndexEquiv m n i).1 ⊗ₜ[k]
                  MvPolynomial.X
                    (segreIndexEquiv m n i).2) ^
                    exponent) ∈
            segreRightGrading k m n
              (∑ i ∈ e.support, e i • 1) := by
        simpa only [Finsupp.prod] using
          (SetLike.prod_pow_mem_graded
            (segreRightGrading k m n)
            (fun _ => 1)
            (fun i =>
              MvPolynomial.X
                  (segreIndexEquiv m n i).1 ⊗ₜ[k]
                MvPolynomial.X
                  (segreIndexEquiv m n i).2)
            e
            hvariables)
      have hdegree :
          (∑ i ∈ e.support, e i • 1) = d := by
        change e.sum (fun _ c => c • 1) = d
        simpa only [Finsupp.weight_apply, Pi.one_apply,
          nsmul_eq_mul, mul_one] using he
      rw [hdegree] at hproduct
      have hcoeff :
          algebraMap k (SegreTensorRing k m n) r ∈
            segreRightGrading k m n 0 :=
        SetLike.algebraMap_mem_graded
          (segreRightGrading k m n) r
      simpa only [zero_add] using
        (SetLike.mul_mem_graded hcoeff hproduct)

/-- The coordinate map as a graded algebra homomorphism into the
right-degree grading of the tensor product. -/
def segreStandardGradedHom
    (k : Type u) [CommRing k] (m n : ℕ) :
    homogeneousGrading k (segreDimension m n) →ₐᵍ[k]
      segreRightGrading k m n where
  __ := segreStandardCoordinateHom k m n
  map_mem := segreStandardCoordinateHom_mem_grading k m n

/-- The image algebra is homogeneous inside the right-graded tensor
product. -/
lemma segreCoordinateRing_isHomogeneous
    (k : Type u) [CommRing k] (m n : ℕ) :
    DirectSum.SetLike.IsHomogeneous
      (segreRightGrading k m n)
      (SegreCoordinateRing k m n :
        Subalgebra k (SegreTensorRing k m n)) := by
  intro d x hx
  obtain ⟨p, rfl⟩ := hx
  refine ⟨DirectSum.decompose
    (homogeneousGrading k (segreDimension m n))
      p d, ?_⟩
  change
    segreStandardCoordinateHom k m n
        (DirectSum.decompose
          (homogeneousGrading k (segreDimension m n))
          p d) =
      DirectSum.decompose
        (segreRightGrading k m n)
        (segreStandardCoordinateHom k m n p) d
  exact map_directSumDecompose
    (homogeneousGrading k (segreDimension m n))
    (segreRightGrading k m n)
    (segreStandardGradedHom k m n).toGradedRingHom

/-- The canonical degree-`d` piece of the Segre image algebra. -/
def segreImageGrading
    (k : Type u) [CommRing k] (m n d : ℕ) :
    Submodule k (SegreCoordinateRing k m n) :=
  (segreRightGrading k m n d).comap
    (Subalgebra.val
      (SegreCoordinateRing k m n)).toLinearMap

instance segreImageGradingGradedMonoid
    (k : Type u) [CommRing k] (m n : ℕ) :
    SetLike.GradedMonoid (segreImageGrading k m n) where
  one_mem := by
    exact SetLike.one_mem_graded
      (segreRightGrading k m n)
  mul_mem i j x y hx hy := by
    change
      ((x * y : SegreCoordinateRing k m n) :
          SegreTensorRing k m n) ∈
        segreRightGrading k m n (i + j)
    change (x : SegreTensorRing k m n) ∈
      segreRightGrading k m n i at hx
    change (y : SegreTensorRing k m n) ∈
      segreRightGrading k m n j at hy
    exact SetLike.mul_mem_graded hx hy

lemma segreImageGrading_iSupIndep
    (k : Type u) [CommRing k] (m n : ℕ) :
    iSupIndep (segreImageGrading k m n) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  apply Subtype.ext
  have hambient :
      iSupIndep (segreRightGrading k m n) :=
    (DirectSum.Decomposition.isInternal
      (segreRightGrading k m n)).submodule_iSupIndep
  apply
    ((iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero
      (segreRightGrading k m n)).mp hambient
        s
        (fun j => ((v j :
          SegreCoordinateRing k m n) :
            SegreTensorRing k m n))
        (fun j hj => hv j hj)
        ?_ i hi)
  calc
    ∑ j ∈ s,
        ((v j : SegreCoordinateRing k m n) :
          SegreTensorRing k m n) =
        ((∑ j ∈ s, v j :
          SegreCoordinateRing k m n) :
            SegreTensorRing k m n) := by
      exact (map_sum
        (Subalgebra.val
          (SegreCoordinateRing k m n))
        (fun j => v j) s).symm
    _ = 0 := by rw [hsum]; rfl

lemma iSup_segreImageGrading
    (k : Type u) [CommRing k] (m n : ℕ) :
    iSup (segreImageGrading k m n) = ⊤ := by
  classical
  apply top_unique
  intro x _
  obtain ⟨p, rfl⟩ :=
    segreRangeCoordinateHom_surjective k m n x
  rw [← DirectSum.sum_support_decompose
    (homogeneousGrading k (segreDimension m n)) p,
    map_sum]
  apply Submodule.sum_mem
  intro d _
  apply (le_iSup (segreImageGrading k m n) d)
  change
    segreStandardCoordinateHom k m n
        (DirectSum.decompose
          (homogeneousGrading k
            (segreDimension m n)) p d) ∈
      segreRightGrading k m n d
  exact segreStandardCoordinateHom_mem_grading
    k m n
    (DirectSum.decompose
      (homogeneousGrading k
        (segreDimension m n)) p d).2

/-- The canonical grading of the Segre image algebra. -/
instance segreImageGradingGradedRing
    (k : Type u) [CommRing k] (m n : ℕ) :
    GradedRing (segreImageGrading k m n) where
  toGradedMonoid :=
    segreImageGradingGradedMonoid k m n
  toDecomposition :=
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (segreImageGrading_iSupIndep k m n)
      (iSup_segreImageGrading k m n)).chooseDecomposition

lemma segreRangeCoordinateHom_mem_imageGrading
    (k : Type u) [CommRing k] (m n : ℕ)
    {d : ℕ}
    {p : MvPolynomial
      (Fin (segreDimension m n + 1)) k}
    (hp : p ∈ homogeneousGrading k
      (segreDimension m n) d) :
    segreRangeCoordinateHom k m n p ∈
      segreImageGrading k m n d :=
  segreStandardCoordinateHom_mem_grading
    k m n hp

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
