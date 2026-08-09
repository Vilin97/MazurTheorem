/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.XOneThirteenProjectiveCurve
import TauCeti.AlgebraicGeometry.ProjectiveLine.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The hyperelliptic map from the order-thirteen curve

This file constructs the degree-two map from the glued order-thirteen curve
to Tau Ceti's actual projective line.  On the ordinary chart it is induced by
`K[x] → K[x,y]/(y²-f(x))`; on the reciprocal chart it is induced by the
coordinate `z = 1/x`.
-/

noncomputable section

namespace MazurTorsion.XOneThirteenHyperellipticMap

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped DirectSum
open TauCeti.AlgebraicGeometry

universe u

private lemma zero_lt_one : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

section ChartRingMaps

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A]

/-- Evaluation of the homogeneous coordinates at `[x:1]`. -/
private def standardCoordinatePolynomialHom (x : A) :
    MvPolynomial (Fin 2) K →+* A :=
  MvPolynomial.eval₂Hom (algebraMap K A)
    fun i ↦ if i = 0 then x else 1

private lemma standardCoordinatePolynomialHom_X_one (x : A) :
    standardCoordinatePolynomialHom K A x
        (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [standardCoordinatePolynomialHom]

/-- The standard projective-line chart ring map sending `X₀/X₁` to
`x`. -/
noncomputable def standardChartRingHom (x : A) :
    HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) →+* A :=
  (Localization.awayLift (standardCoordinatePolynomialHom K A x)
      (MvPolynomial.X (1 : Fin 2)) (by
        rw [standardCoordinatePolynomialHom_X_one]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

@[simp]
theorem standardChartRingHom_affineCoordinateAway (x : A) :
    standardChartRingHom K A x (ProjectiveLine.affineCoordinateAway K) = x := by
  simp only [standardChartRingHom, RingHom.comp_apply,
    ProjectiveLine.affineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    (by rw [standardCoordinatePolynomialHom_X_one]; simp) 1
  simpa [standardCoordinatePolynomialHom] using h

/-- Evaluation of the homogeneous coordinates at `[1:z]`. -/
private def inverseCoordinatePolynomialHom (z : A) :
    MvPolynomial (Fin 2) K →+* A :=
  MvPolynomial.eval₂Hom (algebraMap K A)
    fun i ↦ if i = 1 then z else 1

private lemma inverseCoordinatePolynomialHom_X_zero (z : A) :
    inverseCoordinatePolynomialHom K A z
        (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [inverseCoordinatePolynomialHom]

/-- The infinity projective-line chart ring map sending `X₁/X₀` to
`z`. -/
noncomputable def infinityChartRingHom (z : A) :
    HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) →+* A :=
  (Localization.awayLift (inverseCoordinatePolynomialHom K A z)
      (MvPolynomial.X (0 : Fin 2)) (by
        rw [inverseCoordinatePolynomialHom_X_zero]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

@[simp]
theorem infinityChartRingHom_inverseAffineCoordinateAway (z : A) :
    infinityChartRingHom K A z
        (ProjectiveLine.inverseAffineCoordinateAway K) = z := by
  simp only [infinityChartRingHom, RingHom.comp_apply,
    ProjectiveLine.inverseAffineCoordinateAway,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom K A z)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) 1
  simpa [inverseCoordinatePolynomialHom] using h

private theorem standardCoordinatePolynomialHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (x : A) :
    f.toRingHom.comp (standardCoordinatePolynomialHom K A x) =
      standardCoordinatePolynomialHom K B (f x) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [standardCoordinatePolynomialHom]
  · intro i
    fin_cases i <;> simp [standardCoordinatePolynomialHom]

private theorem infinityCoordinatePolynomialHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (z : A) :
    f.toRingHom.comp (inverseCoordinatePolynomialHom K A z) =
      inverseCoordinatePolynomialHom K B (f z) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    simp [inverseCoordinatePolynomialHom]
  · intro i
    fin_cases i <;> simp [inverseCoordinatePolynomialHom]

/-- Homogeneous evaluation is invariant under the projective rescaling
`[x:1] = [1:z]` when `xz=1`. -/
private theorem eval_standard_eq_pow_mul_eval_inverse
    (p : MvPolynomial (Fin 2) K) (n : ℕ)
    (hp : p.IsHomogeneous n) (x z : A) (hxz : x * z = 1) :
    standardCoordinatePolynomialHom K A x p =
      x ^ n * inverseCoordinatePolynomialHom K A z p := by
  simp only [standardCoordinatePolynomialHom,
    inverseCoordinatePolynomialHom, MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d 0 + d 1 = n := by
    have h := hp (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_two] using h
  simp only [Fin.prod_univ_two,
    if_neg (by decide : (1 : Fin 2) ≠ 0),
    if_neg (by decide : (0 : Fin 2) ≠ 1), if_true, one_pow,
    one_mul, mul_one]
  rw [← hdeg, pow_add]
  calc
    (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 =
        (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 * 1 := by
          rw [mul_one]
    _ = (algebraMap K A) (MvPolynomial.coeff d p) * x ^ d 0 *
        ((x * z) ^ d 1) := by rw [hxz, one_pow]
    _ = (x ^ d 0 * x ^ d 1) *
        ((algebraMap K A) (MvPolynomial.coeff d p) * z ^ d 1) := by
          rw [mul_pow]
          ring

private theorem overlapDenominator_mem_degree_two :
    MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2) ∈
      ProjectiveLine.homogeneousPieces K 2 := by
  simpa using
    (ProjectiveLine.X_one_mem_degree_one K).mul
      (ProjectiveLine.X_zero_mem_degree_one K)

/-- Evaluation on the common projective-line chart `D₊(X₁X₀)`,
normalized as `[x:1]` with chosen inverse `z`. -/
private noncomputable def overlapChartRingHom
    (x z : A) (hxz : x * z = 1) :
    HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2)) →+* A :=
  (Localization.awayLift (standardCoordinatePolynomialHom K A x)
      (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))
      (isUnit_iff_exists_inv.mpr ⟨z, by
        simpa [standardCoordinatePolynomialHom] using hxz⟩)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2)))
      (Localization.Away
        (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))))

private theorem standardChartRingHom_awayMk
    (x : A) (n : ℕ) (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ ProjectiveLine.homogeneousPieces K n) :
    standardChartRingHom K A x
        (HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_one_mem_degree_one K) n p
          (by simpa using hp)) =
      standardCoordinatePolynomialHom K A x p := by
  simp only [standardChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2)) p 1
    (by rw [standardCoordinatePolynomialHom_X_one]; simp) n
  simpa using h

private theorem infinityChartRingHom_awayMk
    (z : A) (n : ℕ) (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ ProjectiveLine.homogeneousPieces K n) :
    infinityChartRingHom K A z
        (HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_zero_mem_degree_one K) n p
          (by simpa using hp)) =
      inverseCoordinatePolynomialHom K A z p := by
  simp only [infinityChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (inverseCoordinatePolynomialHom K A z)
    (MvPolynomial.X (0 : Fin 2)) p 1
    (by rw [inverseCoordinatePolynomialHom_X_zero]; simp) n
  simpa using h

private theorem standardChartRingHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (x : A) :
    f.toRingHom.comp (standardChartRingHom K A x) =
      standardChartRingHom K B (f x) := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (ProjectiveLine.homogeneousPieces K)
      (ProjectiveLine.X_one_mem_degree_one K) q
  have hp' : p ∈ ProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  rw [RingHom.comp_apply,
    standardChartRingHom_awayMk K A x n p hp',
    standardChartRingHom_awayMk K B (f x) n p hp']
  exact DFunLike.congr_fun
    (standardCoordinatePolynomialHom_naturality K A B f x) p

private theorem infinityChartRingHom_naturality
    (B : Type u) [CommRing B] [Algebra K B]
    (f : A →ₐ[K] B) (z : A) :
    f.toRingHom.comp (infinityChartRingHom K A z) =
      infinityChartRingHom K B (f z) := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (ProjectiveLine.homogeneousPieces K)
      (ProjectiveLine.X_zero_mem_degree_one K) q
  have hp' : p ∈ ProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  rw [RingHom.comp_apply,
    infinityChartRingHom_awayMk K A z n p hp',
    infinityChartRingHom_awayMk K B (f z) n p hp']
  exact DFunLike.congr_fun
    (infinityCoordinatePolynomialHom_naturality K A B f z) p

private theorem overlapChartRingHom_awayMk
    (x z : A) (hxz : x * z = 1) (n : ℕ)
    (p : MvPolynomial (Fin 2) K)
    (hp : p ∈ ProjectiveLine.homogeneousPieces K (n • 2)) :
    overlapChartRingHom K A x z hxz
        (HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (overlapDenominator_mem_degree_two K) n p
          (by simpa using hp)) =
      standardCoordinatePolynomialHom K A x p * z ^ n := by
  simp only [overlapChartRingHom, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have h := Localization.awayLift_mk
    (standardCoordinatePolynomialHom K A x)
    (MvPolynomial.X (1 : Fin 2) * MvPolynomial.X (0 : Fin 2))
    p z (by simpa [standardCoordinatePolynomialHom] using hxz) n
  simpa using h

private theorem overlapChartRingHom_comp_standardAwayMap
    (x z : A) (hxz : x * z = 1) :
    (overlapChartRingHom K A x z hxz).comp
        (HomogeneousLocalization.awayMap
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_zero_mem_degree_one K) rfl) =
      standardChartRingHom K A x := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (ProjectiveLine.homogeneousPieces K)
      (ProjectiveLine.X_one_mem_degree_one K) q
  have hp' : p ∈ ProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.awayMap_mk]
  rw [overlapChartRingHom_awayMk K A x z hxz n
      (p * MvPolynomial.X (0 : Fin 2) ^ n),
    standardChartRingHom_awayMk K A x n p hp']
  · simp only [map_mul, map_pow, standardCoordinatePolynomialHom,
      MvPolynomial.eval₂Hom_X']
    simp only [if_pos]
    rw [mul_assoc, ← mul_pow, hxz, one_pow, mul_one]
  · simpa [nsmul_eq_mul, Nat.mul_two] using
      hp'.mul (SetLike.pow_mem_graded n
        (ProjectiveLine.X_zero_mem_degree_one K))

private theorem overlapChartRingHom_comp_infinityAwayMap
    (x z : A) (hxz : x * z = 1) :
    (overlapChartRingHom K A x z hxz).comp
        (HomogeneousLocalization.awayMap
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_one_mem_degree_one K)
          (mul_comm _ _)) =
      infinityChartRingHom K A z := by
  apply RingHom.ext
  intro q
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (ProjectiveLine.homogeneousPieces K)
      (ProjectiveLine.X_zero_mem_degree_one K) q
  have hp' : p ∈ ProjectiveLine.homogeneousPieces K n := by
    simpa using hp
  simp only [RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.awayMap_mk]
  rw [overlapChartRingHom_awayMk K A x z hxz n
      (p * MvPolynomial.X (1 : Fin 2) ^ n),
    infinityChartRingHom_awayMk K A z n p hp']
  · simp only [map_mul, map_pow, standardCoordinatePolynomialHom,
      MvPolynomial.eval₂Hom_X']
    simp only [if_neg (by decide : (1 : Fin 2) ≠ 0), one_pow,
      mul_one]
    change standardCoordinatePolynomialHom K A x p * z ^ n =
      inverseCoordinatePolynomialHom K A z p
    rw [eval_standard_eq_pow_mul_eval_inverse K A p n hp' x z hxz]
    calc
      (x ^ n * inverseCoordinatePolynomialHom K A z p) * z ^ n =
          inverseCoordinatePolynomialHom K A z p * (x * z) ^ n := by
            rw [mul_pow]
            ring
      _ = inverseCoordinatePolynomialHom K A z p := by
        rw [hxz, one_pow, mul_one]
  · simpa [nsmul_eq_mul, Nat.mul_two] using
      hp'.mul (SetLike.pow_mem_graded n
        (ProjectiveLine.X_one_mem_degree_one K))

end ChartRingMaps

section ChartFiniteness

variable (K : Type u) [Field K]

private noncomputable def standardPolynomialToAway :
    Polynomial K →+*
      HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) :=
  Polynomial.eval₂RingHom
    ((algebraMap (ProjectiveLine.homogeneousPieces K 0)
        (HomogeneousLocalization.Away
          (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2)))).comp
      (ProjectiveLine.degreeZeroRingEquiv K).toRingHom)
    (ProjectiveLine.affineCoordinateAway K)

private theorem standardChartRingHom_comp_standardPolynomialToAway :
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)).comp
        (standardPolynomialToAway K) =
      (AdjoinRoot.of
        (XOneThirteenAffineCurve.affineEquation K)) := by
  apply Polynomial.ringHom_ext
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show standardPolynomialToAway K (Polynomial.C k) =
        (algebraMap (ProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (ProjectiveLine.degreeZeroRingEquiv K k) by
      change Polynomial.eval₂ _ _ (Polynomial.C k) = _
      exact Polynomial.eval₂_C _ _]
    have hp : MvPolynomial.C k ∈
        ProjectiveLine.homogeneousPieces K 0 := by
      simp
    have hcoeff :
        (algebraMap (ProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))))
          (ProjectiveLine.degreeZeroRingEquiv K k) =
        HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_one_mem_degree_one K) 0
          (MvPolynomial.C k) (by simp) := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk
          (((ProjectiveLine.degreeZeroRingEquiv K k :
            ProjectiveLine.homogeneousPieces K 0) :
              MvPolynomial (Fin 2) K)) ⟨1, by simp⟩ =
        Localization.mk (MvPolynomial.C k) ⟨1, by simp⟩
      rw [ProjectiveLine.coe_degreeZeroRingEquiv_apply]
    rw [hcoeff,
      standardChartRingHom_awayMk K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K) 0
        (MvPolynomial.C k) hp]
    rw [show standardCoordinatePolynomialHom K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K) (MvPolynomial.C k) =
      algebraMap K (XOneThirteenAffineCurve.CoordinateRing K) k by
        simp [standardCoordinatePolynomialHom]]
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K)
        (XOneThirteenAffineCurve.CoordinateRing K) k)
  · simp [standardPolynomialToAway,
      XOneThirteenAffineCurve.xCoordinate]

private theorem affineEquation_monic :
    (XOneThirteenAffineCurve.affineEquation K).Monic := by
  exact Polynomial.monic_X_pow_sub_C _ (by norm_num)

/-- The standard chart of the hyperelliptic map is finite. -/
theorem standardChartRingHom_finite :
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)).Finite := by
  apply RingHom.Finite.of_comp_finite (f := standardPolynomialToAway K)
  rw [standardChartRingHom_comp_standardPolynomialToAway K]
  change (algebraMap (Polynomial K)
    (AdjoinRoot (XOneThirteenAffineCurve.affineEquation K))).Finite
  exact RingHom.finite_algebraMap.mpr
    (affineEquation_monic K |>.finite_adjoinRoot)

private noncomputable def infinityPolynomialToAway :
    Polynomial K →+*
      HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) :=
  Polynomial.eval₂RingHom
    ((algebraMap (ProjectiveLine.homogeneousPieces K 0)
        (HomogeneousLocalization.Away
          (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2)))).comp
      (ProjectiveLine.degreeZeroRingEquiv K).toRingHom)
    (ProjectiveLine.inverseAffineCoordinateAway K)

private theorem infinityChartRingHom_comp_infinityPolynomialToAway :
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)).comp
        (infinityPolynomialToAway K) =
      (AdjoinRoot.of
        (XOneThirteenProjectiveCurve.reciprocalEquation K)) := by
  apply Polynomial.ringHom_ext
  · intro k
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show infinityPolynomialToAway K (Polynomial.C k) =
        (algebraMap (ProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))))
          (ProjectiveLine.degreeZeroRingEquiv K k) by
      change Polynomial.eval₂ _ _ (Polynomial.C k) = _
      exact Polynomial.eval₂_C _ _]
    have hp : MvPolynomial.C k ∈
        ProjectiveLine.homogeneousPieces K 0 := by
      simp
    have hcoeff :
        (algebraMap (ProjectiveLine.homogeneousPieces K 0)
          (HomogeneousLocalization.Away
            (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))))
          (ProjectiveLine.degreeZeroRingEquiv K k) =
        HomogeneousLocalization.Away.mk
          (ProjectiveLine.homogeneousPieces K)
          (ProjectiveLine.X_zero_mem_degree_one K) 0
          (MvPolynomial.C k) (by simp) := by
      apply HomogeneousLocalization.val_injective
      change Localization.mk
          (((ProjectiveLine.degreeZeroRingEquiv K k :
            ProjectiveLine.homogeneousPieces K 0) :
              MvPolynomial (Fin 2) K)) ⟨1, by simp⟩ =
        Localization.mk (MvPolynomial.C k) ⟨1, by simp⟩
      rw [ProjectiveLine.coe_degreeZeroRingEquiv_apply]
    rw [hcoeff,
      infinityChartRingHom_awayMk K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K) 0
        (MvPolynomial.C k) hp]
    rw [show inverseCoordinatePolynomialHom K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K)
        (MvPolynomial.C k) =
      algebraMap K (XOneThirteenProjectiveCurve.ReciprocalRing K) k by
        simp [inverseCoordinatePolynomialHom]]
    simpa [AdjoinRoot.algebraMap_eq] using
      (IsScalarTower.algebraMap_apply K (Polynomial K)
        (XOneThirteenProjectiveCurve.ReciprocalRing K) k)
  · simp [infinityPolynomialToAway,
      XOneThirteenProjectiveCurve.zCoordinate]

private theorem reciprocalEquation_monic :
    (XOneThirteenProjectiveCurve.reciprocalEquation K).Monic := by
  exact Polynomial.monic_X_pow_sub_C _ (by norm_num)

/-- The infinity chart of the hyperelliptic map is finite. -/
theorem infinityChartRingHom_finite :
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)).Finite := by
  apply RingHom.Finite.of_comp_finite (f := infinityPolynomialToAway K)
  rw [infinityChartRingHom_comp_infinityPolynomialToAway K]
  change (algebraMap (Polynomial K)
    (AdjoinRoot
      (XOneThirteenProjectiveCurve.reciprocalEquation K))).Finite
  exact RingHom.finite_algebraMap.mpr
    (reciprocalEquation_monic K |>.finite_adjoinRoot)

end ChartFiniteness

section ChartMorphisms

variable (K : Type u) [Field K]

private theorem projectiveLine_chart_maps_eq
    (A : Type u) [CommRing A] [Algebra K A]
    (x z : A) (hxz : x * z = 1) :
    Spec.map (CommRingCat.ofHom (standardChartRingHom K A x)) ≫
        Proj.awayι (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2))
          (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one =
      Spec.map (CommRingCat.ofHom (infinityChartRingHom K A z)) ≫
        Proj.awayι (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2))
          (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one := by
  let H := ProjectiveLine.homogeneousPieces K
  let X₀ : MvPolynomial (Fin 2) K := MvPolynomial.X 0
  let X₁ : MvPolynomial (Fin 2) K := MvPolynomial.X 1
  let q : MvPolynomial (Fin 2) K := X₁ * X₀
  let hq : q ∈ H 2 := overlapDenominator_mem_degree_two K
  have hstd := overlapChartRingHom_comp_standardAwayMap K A x z hxz
  have hinf := overlapChartRingHom_comp_infinityAwayMap K A x z hxz
  calc
    Spec.map (CommRingCat.ofHom (standardChartRingHom K A x)) ≫
          Proj.awayι H X₁ (ProjectiveLine.X_one_mem_degree_one K)
            zero_lt_one =
        (Spec.map (CommRingCat.ofHom (overlapChartRingHom K A x z hxz)) ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.awayMap H
              (f := X₁) (x := q)
              (ProjectiveLine.X_zero_mem_degree_one K) rfl))) ≫
          Proj.awayι H X₁ (ProjectiveLine.X_one_mem_degree_one K)
            zero_lt_one := by
              rw [← Spec.map_comp]
              congr 2
              apply CommRingCat.hom_ext
              exact hstd.symm
    _ = Spec.map (CommRingCat.ofHom
          (overlapChartRingHom K A x z hxz)) ≫
        Proj.awayι H q hq (by omega) := by
          rw [Category.assoc,
            Proj.SpecMap_awayMap_awayι
              (f := X₁) (g := X₀) (x := q) H
              (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one
              (ProjectiveLine.X_zero_mem_degree_one K) rfl]
    _ = (Spec.map (CommRingCat.ofHom
          (overlapChartRingHom K A x z hxz)) ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.awayMap H
              (f := X₀) (x := q)
              (ProjectiveLine.X_one_mem_degree_one K)
              (mul_comm X₁ X₀)))) ≫
        Proj.awayι H X₀ (ProjectiveLine.X_zero_mem_degree_one K)
          zero_lt_one := by
            rw [Category.assoc,
              Proj.SpecMap_awayMap_awayι
                (f := X₀) (g := X₁) (x := q) H
                (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one
                (ProjectiveLine.X_one_mem_degree_one K) (mul_comm X₁ X₀)]
    _ = Spec.map (CommRingCat.ofHom (infinityChartRingHom K A z)) ≫
        Proj.awayι H X₀ (ProjectiveLine.X_zero_mem_degree_one K)
          zero_lt_one := by
            rw [← Spec.map_comp]
            congr 2
            apply CommRingCat.hom_ext
            exact hinf

/-- The ordinary hyperelliptic chart map, with projective coordinate
`[x:1]`. -/
noncomputable def ordinaryChartToProjectiveLine :
    XOneThirteenAffineCurve.scheme K ⟶ ProjectiveLine.scheme K :=
  Spec.map (CommRingCat.ofHom
      (standardChartRingHom K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K))) ≫
    Proj.awayι (ProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))
      (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one

/-- The reciprocal hyperelliptic chart map, with projective coordinate
`[1:z]`. -/
noncomputable def reciprocalChartToProjectiveLine :
    XOneThirteenProjectiveCurve.reciprocalScheme K ⟶
      ProjectiveLine.scheme K :=
  Spec.map (CommRingCat.ofHom
      (infinityChartRingHom K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K))) ≫
    Proj.awayι (ProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))
      (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one

set_option backward.isDefEq.respectTransparency false in
theorem ordinaryChartToProjectiveLine_preimage_standardAffineOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K = ⊤ := by
  rw [show ProjectiveLine.standardAffineOpen K =
      (Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one).opensRange by
    exact (Proj.opensRange_awayι _ _
      (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one).symm]
  unfold ordinaryChartToProjectiveLine
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
  simp

private theorem inverseAffineCoordinateAway_eq_isLocalizationElem :
    ProjectiveLine.inverseAffineCoordinateAway K =
      HomogeneousLocalization.Away.isLocalizationElem
        (ProjectiveLine.X_zero_mem_degree_one K)
        (ProjectiveLine.X_one_mem_degree_one K) := by
  simp [ProjectiveLine.inverseAffineCoordinateAway,
    HomogeneousLocalization.Away.isLocalizationElem]

set_option backward.isDefEq.respectTransparency false in
theorem reciprocalChartToProjectiveLine_preimage_standardAffineOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by
  unfold reciprocalChartToProjectiveLine
  change (Spec.map (CommRingCat.ofHom
      (infinityChartRingHom K
        (XOneThirteenProjectiveCurve.ReciprocalRing K)
        (XOneThirteenProjectiveCurve.zCoordinate K))) ≫
      Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one) ⁻¹ᵁ
      Proj.basicOpen (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)) = _
  rw [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen
    (ProjectiveLine.homogeneousPieces K)
    (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one
    (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  rw [← inverseAffineCoordinateAway_eq_isLocalizationElem K]
  exact infinityChartRingHom_inverseAffineCoordinateAway K
    (XOneThirteenProjectiveCurve.ReciprocalRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

set_option backward.isDefEq.respectTransparency false in
theorem reciprocalChartToProjectiveLine_preimage_infinityAffineOpen :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K = ⊤ := by
  rw [show ProjectiveLine.infinityAffineOpen K =
      (Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2))
        (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one).opensRange by
    exact (Proj.opensRange_awayι _ _
      (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one).symm]
  unfold reciprocalChartToProjectiveLine
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange]
  simp

private theorem affineCoordinateAway_eq_isLocalizationElem :
    ProjectiveLine.affineCoordinateAway K =
      HomogeneousLocalization.Away.isLocalizationElem
        (ProjectiveLine.X_one_mem_degree_one K)
        (ProjectiveLine.X_zero_mem_degree_one K) := by
  simp [ProjectiveLine.affineCoordinateAway,
    HomogeneousLocalization.Away.isLocalizationElem]

set_option backward.isDefEq.respectTransparency false in
theorem ordinaryChartToProjectiveLine_preimage_infinityAffineOpen :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K =
      PrimeSpectrum.basicOpen
        (XOneThirteenAffineCurve.xCoordinate K) := by
  unfold ordinaryChartToProjectiveLine
  change (Spec.map (CommRingCat.ofHom
      (standardChartRingHom K
        (XOneThirteenAffineCurve.CoordinateRing K)
        (XOneThirteenAffineCurve.xCoordinate K))) ≫
      Proj.awayι (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2))
        (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one) ⁻¹ᵁ
      Proj.basicOpen (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)) = _
  rw [Scheme.Hom.comp_preimage]
  rw [Proj.awayι_preimage_basicOpen
    (ProjectiveLine.homogeneousPieces K)
    (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one
    (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one]
  rw [SpecMap_preimage_basicOpen]
  congr 1
  rw [← affineCoordinateAway_eq_isLocalizationElem K]
  exact standardChartRingHom_affineCoordinateAway K
    (XOneThirteenAffineCurve.CoordinateRing K)
    (XOneThirteenAffineCurve.xCoordinate K)

private theorem ordinary_ne_reciprocal :
    (XOneThirteenProjectiveCurve.Chart.ordinary :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary :
    (XOneThirteenProjectiveCurve.Chart.reciprocal :
      XOneThirteenProjectiveCurve.Chart.{u}) ≠
      XOneThirteenProjectiveCurve.Chart.ordinary := by
  intro h
  cases h

private instance reciprocalOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        reciprocal_ne_ordinary) := by
  dsimp [XOneThirteenProjectiveCurve.overlapInclusion]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenProjectiveCurve.zCoordinate K)

set_option backward.isDefEq.respectTransparency false in
private theorem reciprocalOverlapInclusion_opensRange :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      reciprocal_ne_ordinary).opensRange =
        PrimeSpectrum.basicOpen
          (XOneThirteenProjectiveCurve.zCoordinate K) := by
  dsimp [XOneThirteenProjectiveCurve.overlapInclusion]
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.ReciprocalOverlapRing K)
    (XOneThirteenProjectiveCurve.zCoordinate K)

private instance reciprocalGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

set_option backward.isDefEq.respectTransparency false in
private theorem reciprocalChartToProjectiveLine_preimage_standardAffineOpen_eq_overlapRange :
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  calc
    reciprocalChartToProjectiveLine K ⁻¹ᵁ
          ProjectiveLine.standardAffineOpen K =
        (XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          reciprocal_ne_ordinary).opensRange := by
      rw [reciprocalChartToProjectiveLine_preimage_standardAffineOpen K,
        reciprocalOverlapInclusion_opensRange K]
    _ = ((XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
      symm
      dsimp [XOneThirteenProjectiveCurve.glueData,
        XOneThirteenProjectiveCurve.categoricalGlueData,
        CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f',
        XOneThirteenProjectiveCurve.overlapInclusion,
        ordinary_ne_reciprocal, reciprocal_ne_ordinary]
      simp only [dif_neg reciprocal_ne_ordinary]
      rw [Scheme.Hom.opensRange_comp_of_isIso]

set_option backward.isDefEq.respectTransparency false in
private theorem reciprocalChartMap_preimage_ordinaryChartMap_opensRange :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.reciprocalChartMap K q ∈
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))

private instance ordinaryOverlapInclusion_isOpenImmersion :
    IsOpenImmersion
      (XOneThirteenProjectiveCurve.overlapInclusion K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})
        ordinary_ne_reciprocal) := by
  dsimp [XOneThirteenProjectiveCurve.overlapInclusion]
  exact IsOpenImmersion.of_isLocalization
    (XOneThirteenAffineCurve.xCoordinate K)

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryOverlapInclusion_opensRange :
    (XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      ordinary_ne_reciprocal).opensRange =
        PrimeSpectrum.basicOpen
          (XOneThirteenAffineCurve.xCoordinate K) := by
  dsimp [XOneThirteenProjectiveCurve.overlapInclusion]
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range
    (XOneThirteenProjectiveCurve.OrdinaryOverlapRing K)
    (XOneThirteenAffineCurve.xCoordinate K)

private instance ordinaryGlueOverlap_isOpenImmersion :
    IsOpenImmersion
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})) :=
  (XOneThirteenProjectiveCurve.glueData K).f_open _ _

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryChartToProjectiveLine_preimage_infinityAffineOpen_eq_overlapRange :
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  calc
    ordinaryChartToProjectiveLine K ⁻¹ᵁ
          ProjectiveLine.infinityAffineOpen K =
        (XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          ordinary_ne_reciprocal).opensRange := by
      rw [ordinaryChartToProjectiveLine_preimage_infinityAffineOpen K,
        ordinaryOverlapInclusion_opensRange K]
    _ = ((XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
      symm
      dsimp [XOneThirteenProjectiveCurve.glueData,
        XOneThirteenProjectiveCurve.categoricalGlueData,
        CategoryTheory.GlueData.ofGlueData',
        CategoryTheory.GlueData'.f',
        XOneThirteenProjectiveCurve.overlapInclusion,
        ordinary_ne_reciprocal, reciprocal_ne_ordinary]
      simp only [dif_neg ordinary_ne_reciprocal]
      rw [Scheme.Hom.opensRange_comp_of_isIso]

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryChartMap_preimage_reciprocalChartMap_opensRange :
    XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange =
      ((XOneThirteenProjectiveCurve.glueData K).f
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext q
  change (XOneThirteenProjectiveCurve.ordinaryChartMap K q ∈
      (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange) ↔
    q ∈ ((XOneThirteenProjectiveCurve.glueData K).f
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})).opensRange
  constructor
  · rintro ⟨r, hr⟩
    have hrel :=
      ((XOneThirteenProjectiveCurve.glueData K).ι_eq_iff
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) q r).mp hr.symm
    obtain ⟨x, hx, -⟩ := hrel
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    refine ⟨((XOneThirteenProjectiveCurve.glueData K).t
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ≫
        (XOneThirteenProjectiveCurve.glueData K).f
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})) x, ?_⟩
    exact congrArg (fun f ↦ f x)
      ((XOneThirteenProjectiveCurve.glueData K).glue_condition
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}))

set_option backward.isDefEq.respectTransparency false in
private theorem ordinary_reciprocal_hyperelliptic_compatible :
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K =
      XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K := by
  let A := XOneThirteenAffineCurve.CoordinateRing K
  let B := XOneThirteenProjectiveCurve.ReciprocalRing K
  let LA := XOneThirteenProjectiveCurve.OrdinaryOverlapRing K
  let LB := XOneThirteenProjectiveCurve.ReciprocalOverlapRing K
  let x : LA := algebraMap A LA (XOneThirteenAffineCurve.xCoordinate K)
  let z : LA := IsLocalization.Away.invSelf
    (XOneThirteenAffineCurve.xCoordinate K)
  let ordinaryLocalization : A →ₐ[K] LA :=
    IsScalarTower.toAlgHom K A LA
  let reciprocalToOrdinary : B →ₐ[K] LA :=
    (XOneThirteenProjectiveCurve.reciprocalToOrdinary K).comp
      (IsScalarTower.toAlgHom K B LB)
  have hxz : x * z = 1 := by
    exact IsLocalization.Away.mul_invSelf
      (XOneThirteenAffineCurve.xCoordinate K)
  have hz : reciprocalToOrdinary
      (XOneThirteenProjectiveCurve.zCoordinate K) = z := by
    change XOneThirteenProjectiveCurve.reciprocalToOrdinary K
      (algebraMap B LB (XOneThirteenProjectiveCurve.zCoordinate K)) = z
    rw [XOneThirteenProjectiveCurve.reciprocalToOrdinary_algebraMap,
      XOneThirteenProjectiveCurve.reciprocalToOrdinaryBase_z]
    rfl
  have hordinary := standardChartRingHom_naturality K A LA
    ordinaryLocalization (XOneThirteenAffineCurve.xCoordinate K)
  have hreciprocal := infinityChartRingHom_naturality K B LA
    reciprocalToOrdinary (XOneThirteenProjectiveCurve.zCoordinate K)
  rw [hz] at hreciprocal
  calc
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K =
      Spec.map (CommRingCat.ofHom (standardChartRingHom K LA x)) ≫
        Proj.awayι (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (1 : Fin 2))
          (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one := by
      dsimp [XOneThirteenProjectiveCurve.overlapInclusion,
        ordinaryChartToProjectiveLine]
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      exact hordinary
    _ = Spec.map (CommRingCat.ofHom (infinityChartRingHom K LA z)) ≫
        Proj.awayι (ProjectiveLine.homogeneousPieces K)
          (MvPolynomial.X (0 : Fin 2))
          (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one :=
      projectiveLine_chart_maps_eq K LA x z hxz
    _ = XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K := by
      dsimp [XOneThirteenProjectiveCurve.overlapTransition,
        XOneThirteenProjectiveCurve.overlapInclusion,
        reciprocalChartToProjectiveLine]
      rw [XOneThirteenProjectiveCurve.overlapSchemeIso_hom]
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp]
      congr 2
      apply CommRingCat.hom_ext
      exact hreciprocal.symm

set_option backward.isDefEq.respectTransparency false in
private theorem reciprocal_ordinary_hyperelliptic_compatible :
    XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        reciprocalChartToProjectiveLine K =
      XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
  let l := XOneThirteenProjectiveCurve.overlapInclusion K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
    reciprocalChartToProjectiveLine K
  calc
    l = (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv ≫
        (XOneThirteenProjectiveCurve.overlapSchemeIso K).hom ≫ l := by
      rw [(XOneThirteenProjectiveCurve.overlapSchemeIso K).inv_hom_id_assoc]
    _ = (XOneThirteenProjectiveCurve.overlapSchemeIso K).inv ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
      rw [ordinary_reciprocal_hyperelliptic_compatible K]
      rfl
    _ = XOneThirteenProjectiveCurve.overlapTransition K
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u}) reciprocal_ne_ordinary ≫
        XOneThirteenProjectiveCurve.overlapInclusion K
          (XOneThirteenProjectiveCurve.Chart.ordinary :
            XOneThirteenProjectiveCurve.Chart.{u})
          (XOneThirteenProjectiveCurve.Chart.reciprocal :
            XOneThirteenProjectiveCurve.Chart.{u}) ordinary_ne_reciprocal ≫
        ordinaryChartToProjectiveLine K := by
      rfl

/-- The chartwise hyperelliptic maps before descent through the gluing. -/
noncomputable def chartToProjectiveLine :
    ∀ i : XOneThirteenProjectiveCurve.Chart.{u},
      XOneThirteenProjectiveCurve.chartScheme K i ⟶
        ProjectiveLine.scheme K
  | .ordinary => ordinaryChartToProjectiveLine K
  | .reciprocal => reciprocalChartToProjectiveLine K

set_option backward.isDefEq.respectTransparency false in
/-- The hyperelliptic map descended from the two checked chart maps. -/
noncomputable def gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.curveScheme K ⟶
      ProjectiveLine.scheme K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  exact Limits.Multicoequalizer.desc
    (XOneThirteenProjectiveCurve.glueData K).toGlueData.diagram
    (ProjectiveLine.scheme K) (chartToProjectiveLine K) (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          Limits.MultispanShape.prod]
        simp
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          XOneThirteenProjectiveCurve.overlapInclusion,
          XOneThirteenProjectiveCurve.overlapTransition,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact ordinary_reciprocal_hyperelliptic_compatible K
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          XOneThirteenProjectiveCurve.overlapInclusion,
          XOneThirteenProjectiveCurve.overlapTransition,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact reciprocal_ordinary_hyperelliptic_compatible K
      · dsimp [XOneThirteenProjectiveCurve.glueData,
          XOneThirteenProjectiveCurve.categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToProjectiveLine,
          Limits.MultispanShape.prod]
        simp)

@[simp, reassoc]
theorem ordinaryChartMap_gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
        gluedHyperellipticMap K =
      ordinaryChartToProjectiveLine K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  unfold XOneThirteenProjectiveCurve.ordinaryChartMap
    gluedHyperellipticMap
  apply Limits.Multicoequalizer.π_desc

@[simp, reassoc]
theorem reciprocalChartMap_gluedHyperellipticMap :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
        gluedHyperellipticMap K =
      reciprocalChartToProjectiveLine K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram
    (XOneThirteenProjectiveCurve.glueData K)
  unfold XOneThirteenProjectiveCurve.reciprocalChartMap
    gluedHyperellipticMap
  apply Limits.Multicoequalizer.π_desc

set_option backward.isDefEq.respectTransparency false in
theorem gluedHyperellipticMap_preimage_standardAffineOpen :
    gluedHyperellipticMap K ⁻¹ᵁ
        ProjectiveLine.standardAffineOpen K =
      (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
  have hordinary :
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K =
        XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              ProjectiveLine.standardAffineOpen K =
          (XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K := rfl
      _ = ordinaryChartToProjectiveLine K ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K := by
          rw [ordinaryChartMap_gluedHyperellipticMap]
      _ = ⊤ := ordinaryChartToProjectiveLine_preimage_standardAffineOpen K
      _ = XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
        rw [Scheme.Hom.preimage_opensRange]
  have hreciprocal :
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K =
        XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              ProjectiveLine.standardAffineOpen K =
          (XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K := rfl
      _ = reciprocalChartToProjectiveLine K ⁻¹ᵁ
            ProjectiveLine.standardAffineOpen K := by
          rw [reciprocalChartMap_gluedHyperellipticMap]
      _ = ((XOneThirteenProjectiveCurve.glueData K).f
            (XOneThirteenProjectiveCurve.Chart.reciprocal :
              XOneThirteenProjectiveCurve.Chart.{u})
            (XOneThirteenProjectiveCurve.Chart.ordinary :
              XOneThirteenProjectiveCurve.Chart.{u})).opensRange :=
        reciprocalChartToProjectiveLine_preimage_standardAffineOpen_eq_overlapRange K
      _ = XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange :=
        (reciprocalChartMap_preimage_ordinaryChartMap_opensRange K).symm
  apply TopologicalSpace.Opens.ext
  ext p
  obtain ⟨i, q, rfl⟩ :=
    (XOneThirteenProjectiveCurve.glueData K).ι_jointly_surjective p
  rcases i with (_ | _)
  · exact SetLike.ext_iff.mp hordinary q
  · exact SetLike.ext_iff.mp hreciprocal q

set_option backward.isDefEq.respectTransparency false in
theorem gluedHyperellipticMap_preimage_infinityAffineOpen :
    gluedHyperellipticMap K ⁻¹ᵁ
        ProjectiveLine.infinityAffineOpen K =
      (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
  have hordinary :
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K =
        XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              ProjectiveLine.infinityAffineOpen K =
          (XOneThirteenProjectiveCurve.ordinaryChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K := rfl
      _ = ordinaryChartToProjectiveLine K ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K := by
          rw [ordinaryChartMap_gluedHyperellipticMap]
      _ = ((XOneThirteenProjectiveCurve.glueData K).f
            (XOneThirteenProjectiveCurve.Chart.ordinary :
              XOneThirteenProjectiveCurve.Chart.{u})
            (XOneThirteenProjectiveCurve.Chart.reciprocal :
              XOneThirteenProjectiveCurve.Chart.{u})).opensRange :=
        ordinaryChartToProjectiveLine_preimage_infinityAffineOpen_eq_overlapRange K
      _ = XOneThirteenProjectiveCurve.ordinaryChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange :=
        (ordinaryChartMap_preimage_reciprocalChartMap_opensRange K).symm
  have hreciprocal :
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          gluedHyperellipticMap K ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K =
        XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
    calc
      XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
            gluedHyperellipticMap K ⁻¹ᵁ
              ProjectiveLine.infinityAffineOpen K =
          (XOneThirteenProjectiveCurve.reciprocalChartMap K ≫
              gluedHyperellipticMap K) ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K := rfl
      _ = reciprocalChartToProjectiveLine K ⁻¹ᵁ
            ProjectiveLine.infinityAffineOpen K := by
          rw [reciprocalChartMap_gluedHyperellipticMap]
      _ = ⊤ := reciprocalChartToProjectiveLine_preimage_infinityAffineOpen K
      _ = XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
          (XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange := by
        rw [Scheme.Hom.preimage_opensRange]
  apply TopologicalSpace.Opens.ext
  ext p
  obtain ⟨i, q, rfl⟩ :=
    (XOneThirteenProjectiveCurve.glueData K).ι_jointly_surjective p
  rcases i with (_ | _)
  · exact SetLike.ext_iff.mp hordinary q
  · exact SetLike.ext_iff.mp hreciprocal q

private noncomputable def projectiveLineChartScheme :
    XOneThirteenProjectiveCurve.Chart.{u} → Scheme
  | .ordinary => Spec (.of <|
      HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (1 : Fin 2)))
  | .reciprocal => Spec (.of <|
      HomogeneousLocalization.Away (ProjectiveLine.homogeneousPieces K)
        (MvPolynomial.X (0 : Fin 2)))

private noncomputable def projectiveLineChartMap :
    ∀ i : XOneThirteenProjectiveCurve.Chart.{u},
      projectiveLineChartScheme K i ⟶ ProjectiveLine.scheme K
  | .ordinary => Proj.awayι (ProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (1 : Fin 2))
      (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one
  | .reciprocal => Proj.awayι (ProjectiveLine.homogeneousPieces K)
      (MvPolynomial.X (0 : Fin 2))
      (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one

set_option backward.isDefEq.respectTransparency false in
private noncomputable def projectiveLineChartCover :
    (ProjectiveLine.scheme K).OpenCover where
  I₀ := XOneThirteenProjectiveCurve.Chart.{u}
  X := projectiveLineChartScheme K
  f := projectiveLineChartMap K
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro p
      have hp : p ∈ ProjectiveLine.standardAffineOpen K ⊔
          ProjectiveLine.infinityAffineOpen K := by
        rw [ProjectiveLine.standardAffineOpen_sup_infinityAffineOpen_eq_top]
        trivial
      change p ∈ (ProjectiveLine.standardAffineOpen K :
          Set (ProjectiveLine.scheme K)) ∪
        (ProjectiveLine.infinityAffineOpen K :
          Set (ProjectiveLine.scheme K)) at hp
      rcases hp with hp | hp
      · refine ⟨XOneThirteenProjectiveCurve.Chart.ordinary, ?_⟩
        change p ∈ (Proj.awayι (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (1 : Fin 2))
            (ProjectiveLine.X_one_mem_degree_one K) zero_lt_one).opensRange
        rw [Proj.opensRange_awayι]
        exact hp
      · refine ⟨XOneThirteenProjectiveCurve.Chart.reciprocal, ?_⟩
        change p ∈ (Proj.awayι (ProjectiveLine.homogeneousPieces K)
            (MvPolynomial.X (0 : Fin 2))
            (ProjectiveLine.X_zero_mem_degree_one K) zero_lt_one).opensRange
        rw [Proj.opensRange_awayι]
        exact hp
    · intro i
      rcases i with (_ | _) <;> dsimp [projectiveLineChartMap] <;>
        infer_instance

private noncomputable def ordinaryChartFiniteMap :
    XOneThirteenAffineCurve.scheme K ⟶
      projectiveLineChartScheme K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}) :=
  Spec.map (CommRingCat.ofHom
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K)))

private noncomputable def reciprocalChartFiniteMap :
    XOneThirteenProjectiveCurve.reciprocalScheme K ⟶
      projectiveLineChartScheme K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}) :=
  Spec.map (CommRingCat.ofHom
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K)))

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryChartSquare_isPullback :
    IsPullback (ordinaryChartFiniteMap K)
      (XOneThirteenProjectiveCurve.ordinaryChartMap K)
      (projectiveLineChartMap K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u}))
      (gluedHyperellipticMap K) := by
  letI : IsOpenImmersion
      (projectiveLineChartMap K
        (XOneThirteenProjectiveCurve.Chart.ordinary :
          XOneThirteenProjectiveCurve.Chart.{u})) := by
    dsimp [projectiveLineChartMap]
    infer_instance
  apply IsOpenImmersion.isPullback
  · simp [ordinaryChartFiniteMap, projectiveLineChartMap,
      ordinaryChartToProjectiveLine]
  · dsimp [projectiveLineChartMap]
    rw [Proj.opensRange_awayι,
      gluedHyperellipticMap_preimage_standardAffineOpen K]

set_option backward.isDefEq.respectTransparency false in
private theorem reciprocalChartSquare_isPullback :
    IsPullback (reciprocalChartFiniteMap K)
      (XOneThirteenProjectiveCurve.reciprocalChartMap K)
      (projectiveLineChartMap K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u}))
      (gluedHyperellipticMap K) := by
  letI : IsOpenImmersion
      (projectiveLineChartMap K
        (XOneThirteenProjectiveCurve.Chart.reciprocal :
          XOneThirteenProjectiveCurve.Chart.{u})) := by
    dsimp [projectiveLineChartMap]
    infer_instance
  apply IsOpenImmersion.isPullback
  · simp [reciprocalChartFiniteMap, projectiveLineChartMap,
      reciprocalChartToProjectiveLine]
  · dsimp [projectiveLineChartMap]
    rw [Proj.opensRange_awayι,
      gluedHyperellipticMap_preimage_infinityAffineOpen K]

set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryCoverPullbackHom_isFinite :
    IsFinite ((projectiveLineChartCover K).pullbackHom
      (gluedHyperellipticMap K)
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})) := by
  let h := ordinaryChartSquare_isPullback K
  change IsFinite (Limits.pullback.snd (gluedHyperellipticMap K)
    (projectiveLineChartMap K
      (XOneThirteenProjectiveCurve.Chart.ordinary :
        XOneThirteenProjectiveCurve.Chart.{u})))
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @IsFinite) h.flip.isoPullback.hom,
    h.flip.isoPullback_hom_snd]
  change IsFinite (Spec.map (CommRingCat.ofHom
    (standardChartRingHom K
      (XOneThirteenAffineCurve.CoordinateRing K)
      (XOneThirteenAffineCurve.xCoordinate K))))
  rw [IsFinite.SpecMap_iff]
  exact standardChartRingHom_finite K

set_option backward.isDefEq.respectTransparency false in
private theorem reciprocalCoverPullbackHom_isFinite :
    IsFinite ((projectiveLineChartCover K).pullbackHom
      (gluedHyperellipticMap K)
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})) := by
  let h := reciprocalChartSquare_isPullback K
  change IsFinite (Limits.pullback.snd (gluedHyperellipticMap K)
    (projectiveLineChartMap K
      (XOneThirteenProjectiveCurve.Chart.reciprocal :
        XOneThirteenProjectiveCurve.Chart.{u})))
  rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @IsFinite) h.flip.isoPullback.hom,
    h.flip.isoPullback_hom_snd]
  change IsFinite (Spec.map (CommRingCat.ofHom
    (infinityChartRingHom K
      (XOneThirteenProjectiveCurve.ReciprocalRing K)
      (XOneThirteenProjectiveCurve.zCoordinate K))))
  rw [IsFinite.SpecMap_iff]
  exact infinityChartRingHom_finite K

set_option backward.isDefEq.respectTransparency false in
noncomputable instance gluedHyperellipticMap_isFinite :
    IsFinite (gluedHyperellipticMap K) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (P := @IsFinite) (projectiveLineChartCover K)
  intro i
  rcases i with (_ | _)
  · exact ordinaryCoverPullbackHom_isFinite K
  · exact reciprocalCoverPullbackHom_isFinite K

end ChartMorphisms

end MazurTorsion.XOneThirteenHyperellipticMap

namespace MazurTorsion.XOneThirteenProjectiveCurve

open CategoryTheory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

universe u

variable (K : Type u) [Field K]

/-- The degree-two coordinate map from the glued order-thirteen curve to
Tau Ceti's concrete projective line. -/
noncomputable def hyperellipticMap :
    curveScheme K ⟶ ProjectiveLine.scheme K :=
  XOneThirteenHyperellipticMap.gluedHyperellipticMap K

@[simp, reassoc]
theorem ordinaryChartMap_hyperellipticMap :
    ordinaryChartMap K ≫ hyperellipticMap K =
      XOneThirteenHyperellipticMap.ordinaryChartToProjectiveLine K := by
  exact XOneThirteenHyperellipticMap.ordinaryChartMap_gluedHyperellipticMap K

@[simp, reassoc]
theorem reciprocalChartMap_hyperellipticMap :
    reciprocalChartMap K ≫ hyperellipticMap K =
      XOneThirteenHyperellipticMap.reciprocalChartToProjectiveLine K := by
  exact XOneThirteenHyperellipticMap.reciprocalChartMap_gluedHyperellipticMap K

@[simp]
theorem hyperellipticMap_preimage_standardAffineOpen :
    hyperellipticMap K ⁻¹ᵁ ProjectiveLine.standardAffineOpen K =
      (ordinaryChartMap K).opensRange :=
  XOneThirteenHyperellipticMap.gluedHyperellipticMap_preimage_standardAffineOpen K

@[simp]
theorem hyperellipticMap_preimage_infinityAffineOpen :
    hyperellipticMap K ⁻¹ᵁ ProjectiveLine.infinityAffineOpen K =
      (reciprocalChartMap K).opensRange :=
  XOneThirteenHyperellipticMap.gluedHyperellipticMap_preimage_infinityAffineOpen K

noncomputable instance hyperellipticMap_isFinite :
    IsFinite (hyperellipticMap K) :=
  XOneThirteenHyperellipticMap.gluedHyperellipticMap_isFinite K

end MazurTorsion.XOneThirteenProjectiveCurve
