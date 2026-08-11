/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenHaoQuadraticShift
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The explicit infinity chart of the even-degree `X₁(13)` model

Put `t = 1/x` and `z = y/x³`.  The normalized chart equation is

`z² = 1 + 2t + t² + 2t³ + 6t⁴ + 4t⁵ + t⁶`.

This file constructs its coordinate ring, the two rational ideals
`⟨t,z-1⟩` and `⟨t,z+1⟩`, and their evaluation maps and residue-field
certificates.  It also checks the reciprocal numerators of `X`, Hao's `w`,
`w-X`, and `w-(X²+2X)`, including their values at both infinity branches.

Only polynomial identities, ideal kernels, and nonvanishing values are
asserted here.  In particular, no divisor order is inferred from these data.
-/

namespace MazurTorsion.XOneThirteenInfinityChart

open Ideal Polynomial

open XOneThirteenMumford
open XOneThirteenPicard
open XOneThirteenHaoFunctions
open XOneThirteenHaoShift
open XOneThirteenHaoQuadraticShift

noncomputable section

/-! ## The chart coordinate ring -/

/-- The reversed sextic defining the normalized infinity chart. -/
def infinitySexticPolynomial : ℚ[X] :=
  1 + 2 * X + X ^ 2 + 2 * X ^ 3 +
    6 * X ^ 4 + 4 * X ^ 5 + X ^ 6

/-- The monic quadratic chart relation in the ordinate `z`. -/
def infinityRelationPolynomial : ℚ[X][X] :=
  X ^ 2 - C infinitySexticPolynomial

theorem infinityRelationPolynomial_monic :
    infinityRelationPolynomial.Monic := by
  simpa only [infinityRelationPolynomial] using
    (monic_X_pow_sub_C infinitySexticPolynomial
      (by norm_num : (2 : ℕ) ≠ 0))

/-- The coordinate ring of the normalized infinity chart. -/
abbrev InfinityCoordinateRing :=
  AdjoinRoot infinityRelationPolynomial

namespace InfinityCoordinateRing

noncomputable instance : Algebra ℚ[X] InfinityCoordinateRing := inferInstance

/-- The quotient map in the ordinate variable. -/
abbrev mk : ℚ[X][X] →+* InfinityCoordinateRing :=
  AdjoinRoot.mk infinityRelationPolynomial

/-- The reciprocal base coordinate `t`. -/
def tCoordinate : InfinityCoordinateRing :=
  algebraMap ℚ[X] InfinityCoordinateRing X

/-- The normalized ordinate `z = y/x³`. -/
def zCoordinate : InfinityCoordinateRing :=
  AdjoinRoot.root infinityRelationPolynomial

/-- The exact equation in the infinity-chart coordinate ring. -/
@[simp] theorem zCoordinate_sq :
    zCoordinate ^ 2 =
      algebraMap ℚ[X] InfinityCoordinateRing infinitySexticPolynomial := by
  change mk X ^ 2 = mk (C infinitySexticPolynomial)
  rw [← map_pow]
  exact AdjoinRoot.mk_eq_mk.mpr dvd_rfl

/-- Rational points of the normalized infinity chart. -/
def IsChartPoint (t z : ℚ) : Prop :=
  z ^ 2 = infinitySexticPolynomial.eval t

private theorem infinityRelationPolynomial_eval_chartPoint
    {t z : ℚ} (hchart : IsChartPoint t z) :
    infinityRelationPolynomial.eval₂ (Polynomial.evalRingHom t) z = 0 := by
  simp only [infinityRelationPolynomial, eval₂_sub, eval₂_pow,
    eval₂_X, eval₂_C]
  rw [show Polynomial.evalRingHom t infinitySexticPolynomial =
    infinitySexticPolynomial.eval t by rfl, ← hchart]
  ring

/-- Evaluation at a rational point of the normalized chart. -/
def pointEval (t z : ℚ) (hchart : IsChartPoint t z) :
    InfinityCoordinateRing →+* ℚ :=
  AdjoinRoot.lift (Polynomial.evalRingHom t) z
    (infinityRelationPolynomial_eval_chartPoint hchart)

@[simp] theorem pointEval_zCoordinate
    (t z : ℚ) (hchart : IsChartPoint t z) :
    pointEval t z hchart zCoordinate = z := by
  exact AdjoinRoot.lift_root
    (infinityRelationPolynomial_eval_chartPoint hchart)

@[simp] theorem pointEval_algebraMap
    (t z : ℚ) (hchart : IsChartPoint t z) (p : ℚ[X]) :
    pointEval t z hchart (algebraMap ℚ[X] InfinityCoordinateRing p) =
      p.eval t := by
  exact AdjoinRoot.lift_of
    (infinityRelationPolynomial_eval_chartPoint hchart)

@[simp] theorem pointEval_mk
    (t z : ℚ) (hchart : IsChartPoint t z) (p : ℚ[X][X]) :
    pointEval t z hchart (mk p) =
      p.eval₂ (Polynomial.evalRingHom t) z := by
  exact AdjoinRoot.lift_mk
    (infinityRelationPolynomial_eval_chartPoint hchart) p

/-- The class of `t-a`. -/
def tClass (a : ℚ) : InfinityCoordinateRing :=
  algebraMap ℚ[X] InfinityCoordinateRing (X - C a)

/-- The class of `z-b`. -/
def zClass (b : ℚ) : InfinityCoordinateRing :=
  zCoordinate - algebraMap ℚ[X] InfinityCoordinateRing (C b)

/-- The two-generator ideal of a rational chart point. -/
def pointIdeal (t z : ℚ) : Ideal InfinityCoordinateRing :=
  .span {tClass t, zClass z}

@[simp] theorem pointEval_tClass
    (t z : ℚ) (hchart : IsChartPoint t z) (a : ℚ) :
    pointEval t z hchart (tClass a) = t - a := by
  rw [tClass, pointEval_algebraMap]
  simp

@[simp] theorem pointEval_zClass
    (t z : ℚ) (hchart : IsChartPoint t z) (b : ℚ) :
    pointEval t z hchart (zClass b) = z - b := by
  rw [zClass, map_sub, pointEval_zCoordinate, pointEval_algebraMap]
  simp

theorem pointIdeal_le_pointEval_ker
    (t z : ℚ) (hchart : IsChartPoint t z) :
    pointIdeal t z ≤ RingHom.ker (pointEval t z hchart) := by
  rw [pointIdeal, Ideal.span_le]
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl
  · exact RingHom.mem_ker.mpr (by simp)
  · exact RingHom.mem_ker.mpr (by simp)

private theorem mk_outer_sub_eval_mem_pointIdeal
    (t z : ℚ) (p : ℚ[X][X]) :
    mk (p - C (p.eval (C z))) ∈ pointIdeal t z := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (p := p) (a := C z)
  rw [hq, map_mul]
  change zClass z * mk q ∈ pointIdeal t z
  exact (pointIdeal t z).mul_mem_right _
    (Ideal.subset_span (by simp))

private theorem algebraMap_eval_mem_pointIdeal
    (t z : ℚ) (p : ℚ[X][X])
    (heval : (p.eval (C z)).eval t = 0) :
    algebraMap ℚ[X] InfinityCoordinateRing (p.eval (C z)) ∈
      pointIdeal t z := by
  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval
    (p := p.eval (C z)) (a := t)
  have hp : p.eval (C z) = (X - C t) * q := by
    calc
      p.eval (C z) = p.eval (C z) - C ((p.eval (C z)).eval t) := by
        rw [heval, C_0, sub_zero]
      _ = (X - C t) * q := hq
  rw [hp, map_mul]
  change tClass t * algebraMap ℚ[X] InfinityCoordinateRing q ∈
    pointIdeal t z
  exact (pointIdeal t z).mul_mem_right _
    (Ideal.subset_span (by simp))

/-- Evaluation has exactly the displayed two-generator point ideal as its
kernel. -/
theorem pointEval_ker
    (t z : ℚ) (hchart : IsChartPoint t z) :
    RingHom.ker (pointEval t z hchart) = pointIdeal t z := by
  apply le_antisymm
  · intro u
    refine AdjoinRoot.induction_on infinityRelationPolynomial u ?_
    intro p hpker
    have hpzero : p.eval₂ (Polynomial.evalRingHom t) z = 0 := by
      exact RingHom.mem_ker.mp hpker
    have heval : (p.eval (C z)).eval t = 0 := by
      calc
        (p.eval (C z)).eval t =
            p.eval₂ (Polynomial.evalRingHom t)
              (Polynomial.evalRingHom t (C z)) := by
                rw [eval₂_at_apply]
                rfl
        _ = p.eval₂ (Polynomial.evalRingHom t) z := by simp
        _ = 0 := hpzero
    have hsum := (pointIdeal t z).add_mem
      (mk_outer_sub_eval_mem_pointIdeal t z p)
      (algebraMap_eval_mem_pointIdeal t z p heval)
    have hdecomp :
        mk p = mk (p - C (p.eval (C z))) +
          algebraMap ℚ[X] InfinityCoordinateRing (p.eval (C z)) := by
      rw [map_sub]
      simp
    rw [hdecomp]
    exact hsum
  · exact pointIdeal_le_pointEval_ker t z hchart

theorem pointEval_surjective
    (t z : ℚ) (hchart : IsChartPoint t z) :
    Function.Surjective (pointEval t z hchart) := by
  intro a
  refine ⟨algebraMap ℚ[X] InfinityCoordinateRing (C a), ?_⟩
  rw [pointEval_algebraMap]
  simp

/-- Every rational chart point cuts out a maximal ideal. -/
theorem pointIdeal_isMaximal
    (t z : ℚ) (hchart : IsChartPoint t z) :
    (pointIdeal t z).IsMaximal := by
  rw [← pointEval_ker t z hchart]
  exact RingHom.ker_isMaximal_of_surjective (pointEval t z hchart)
    (pointEval_surjective t z hchart)

/-- The residue field at a rational chart point is `ℚ`. -/
def pointIdealQuotientEquiv
    (t z : ℚ) (hchart : IsChartPoint t z) :
    InfinityCoordinateRing ⧸ pointIdeal t z ≃+* ℚ :=
  (Ideal.quotEquivOfEq (pointEval_ker t z hchart).symm).trans
    ((pointEval t z hchart).quotientKerEquivOfSurjective
      (pointEval_surjective t z hchart))

/-! ## The two infinity branches -/

theorem positiveInfinity_isChartPoint : IsChartPoint 0 1 := by
  norm_num [IsChartPoint, infinitySexticPolynomial]

theorem negativeInfinity_isChartPoint : IsChartPoint 0 (-1) := by
  norm_num [IsChartPoint, infinitySexticPolynomial]

/-- The infinity ideal `⟨t,z-1⟩`. -/
def positiveInfinityIdeal : Ideal InfinityCoordinateRing :=
  pointIdeal 0 1

/-- The infinity ideal `⟨t,z+1⟩`. -/
def negativeInfinityIdeal : Ideal InfinityCoordinateRing :=
  pointIdeal 0 (-1)

theorem positiveInfinityIdeal_eq :
    positiveInfinityIdeal =
      Ideal.span {tCoordinate, zCoordinate - 1} := by
  simp [positiveInfinityIdeal, pointIdeal, tClass, zClass, tCoordinate]

theorem negativeInfinityIdeal_eq :
    negativeInfinityIdeal =
      Ideal.span {tCoordinate, zCoordinate + 1} := by
  simp [negativeInfinityIdeal, pointIdeal, tClass, zClass, tCoordinate]

/-- Evaluation at the branch `z=1`. -/
def positiveInfinityEval : InfinityCoordinateRing →+* ℚ :=
  pointEval 0 1 positiveInfinity_isChartPoint

/-- Evaluation at the branch `z=-1`. -/
def negativeInfinityEval : InfinityCoordinateRing →+* ℚ :=
  pointEval 0 (-1) negativeInfinity_isChartPoint

theorem positiveInfinityEval_ker :
    RingHom.ker positiveInfinityEval = positiveInfinityIdeal :=
  pointEval_ker 0 1 positiveInfinity_isChartPoint

theorem negativeInfinityEval_ker :
    RingHom.ker negativeInfinityEval = negativeInfinityIdeal :=
  pointEval_ker 0 (-1) negativeInfinity_isChartPoint

theorem positiveInfinityIdeal_isMaximal :
    positiveInfinityIdeal.IsMaximal :=
  pointIdeal_isMaximal 0 1 positiveInfinity_isChartPoint

theorem negativeInfinityIdeal_isMaximal :
    negativeInfinityIdeal.IsMaximal :=
  pointIdeal_isMaximal 0 (-1) negativeInfinity_isChartPoint

/-! ## Reciprocal polynomial and numerator identities -/

/-- Exact reversal of the affine sextic. -/
theorem infinitySexticPolynomial_eq_reciprocal
    (t : ℚ) (ht : t ≠ 0) :
    infinitySexticPolynomial.eval t =
      t ^ 6 * sexticPolynomial.eval (1 / t) := by
  simp only [infinitySexticPolynomial, sexticPolynomial, eval_add,
    eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
  field_simp [ht]

/-- Reversal of the cubic polynomial in Hao's ordinate. -/
def infinityHaoPolynomial : ℚ[X] :=
  1 + X + X ^ 3

/-- Reversal of the ordinate polynomial for `w-X`. -/
def infinityShiftedHaoPolynomial : ℚ[X] :=
  1 + X + 2 * X ^ 2 + X ^ 3

/-- Reversal of the ordinate polynomial for `w-(X²+2X)`. -/
def infinityQuadraticShiftHaoPolynomial : ℚ[X] :=
  1 + 3 * X + 4 * X ^ 2 + X ^ 3

theorem infinityHaoPolynomial_eq_reciprocal
    (t : ℚ) (ht : t ≠ 0) :
    infinityHaoPolynomial.eval t =
      t ^ 3 * haoPolynomial.eval (1 / t) := by
  simp only [infinityHaoPolynomial, haoPolynomial, eval_add, eval_pow,
    eval_X, eval_one]
  field_simp [ht]

theorem infinityShiftedHaoPolynomial_eq_reciprocal
    (t : ℚ) (ht : t ≠ 0) :
    infinityShiftedHaoPolynomial.eval t =
      t ^ 3 * shiftedHaoPolynomial.eval (1 / t) := by
  simp only [infinityShiftedHaoPolynomial, shiftedHaoPolynomial,
    haoPolynomial, eval_add, eval_mul, eval_pow, eval_X, eval_one,
    eval_ofNat]
  field_simp [ht]
  ring

theorem infinityQuadraticShiftHaoPolynomial_eq_reciprocal
    (t : ℚ) (ht : t ≠ 0) :
    infinityQuadraticShiftHaoPolynomial.eval t =
      t ^ 3 * quadraticShiftHaoPolynomial.eval (1 / t) := by
  simp only [infinityQuadraticShiftHaoPolynomial,
    quadraticShiftHaoPolynomial, haoPolynomial, eval_add, eval_mul,
    eval_pow, eval_X, eval_one, eval_ofNat]
  field_simp [ht]
  ring

/-- The numerator obtained by clearing the simple pole of `X`. -/
def infinityXNumerator : InfinityCoordinateRing := 1

private def halfClass : InfinityCoordinateRing :=
  algebraMap ℚ[X] InfinityCoordinateRing (C (1 / 2 : ℚ))

/-- The numerator `t³w`. -/
def infinityHaoNumerator : InfinityCoordinateRing :=
  halfClass *
    (zCoordinate -
      algebraMap ℚ[X] InfinityCoordinateRing infinityHaoPolynomial)

/-- The numerator `t³(w-X)`. -/
def infinityHaoMinusXNumerator : InfinityCoordinateRing :=
  halfClass *
    (zCoordinate -
      algebraMap ℚ[X] InfinityCoordinateRing infinityShiftedHaoPolynomial)

/-- The numerator `t³(w-(X²+2X))`. -/
def infinityHaoMinusQuadraticNumerator : InfinityCoordinateRing :=
  halfClass *
    (zCoordinate - algebraMap ℚ[X] InfinityCoordinateRing
      infinityQuadraticShiftHaoPolynomial)

/-- Clearing the pole of `X=1/t` gives the constant numerator one. -/
theorem infinityXNumerator_eq_reciprocal
    (t : ℚ) (ht : t ≠ 0) :
    (1 : ℚ) = t * (1 / t) := by
  field_simp [ht]

/-- Exact scalar identity for the transformed numerator `t³w`. -/
theorem infinityHaoNumerator_eq_reciprocal
    (t z : ℚ) (ht : t ≠ 0) :
    (z - infinityHaoPolynomial.eval t) / 2 =
      t ^ 3 * ((z / t ^ 3 - haoPolynomial.eval (1 / t)) / 2) := by
  rw [infinityHaoPolynomial_eq_reciprocal t ht]
  field_simp [ht]

/-- Exact scalar identity for the transformed numerator `t³(w-X)`. -/
theorem infinityHaoMinusXNumerator_eq_reciprocal
    (t z : ℚ) (ht : t ≠ 0) :
    (z - infinityShiftedHaoPolynomial.eval t) / 2 =
      t ^ 3 *
        ((z / t ^ 3 - haoPolynomial.eval (1 / t)) / 2 - 1 / t) := by
  simp only [infinityShiftedHaoPolynomial, haoPolynomial,
    eval_add, eval_mul, eval_pow, eval_X, eval_one,
    eval_ofNat]
  field_simp [ht]
  ring

/-- Exact scalar identity for `t³(w-(X²+2X))`. -/
theorem infinityHaoMinusQuadraticNumerator_eq_reciprocal
    (t z : ℚ) (ht : t ≠ 0) :
    (z - infinityQuadraticShiftHaoPolynomial.eval t) / 2 =
      t ^ 3 *
        ((z / t ^ 3 - haoPolynomial.eval (1 / t)) / 2 -
          ((1 / t) ^ 2 + 2 * (1 / t))) := by
  simp only [infinityQuadraticShiftHaoPolynomial, haoPolynomial,
    eval_add, eval_mul, eval_pow, eval_X, eval_one, eval_ofNat]
  field_simp [ht]
  ring

@[simp] theorem pointEval_infinityXNumerator
    (t z : ℚ) (hchart : IsChartPoint t z) :
    pointEval t z hchart infinityXNumerator = 1 := by
  simp [infinityXNumerator]

@[simp] theorem pointEval_infinityHaoNumerator
    (t z : ℚ) (hchart : IsChartPoint t z) :
    pointEval t z hchart infinityHaoNumerator =
      (z - infinityHaoPolynomial.eval t) / 2 := by
  rw [infinityHaoNumerator, map_mul, map_sub, pointEval_zCoordinate,
    halfClass, pointEval_algebraMap, pointEval_algebraMap]
  simp
  ring

@[simp] theorem pointEval_infinityHaoMinusXNumerator
    (t z : ℚ) (hchart : IsChartPoint t z) :
    pointEval t z hchart infinityHaoMinusXNumerator =
      (z - infinityShiftedHaoPolynomial.eval t) / 2 := by
  rw [infinityHaoMinusXNumerator, map_mul, map_sub,
    pointEval_zCoordinate, halfClass, pointEval_algebraMap,
    pointEval_algebraMap]
  simp
  ring

@[simp] theorem pointEval_infinityHaoMinusQuadraticNumerator
    (t z : ℚ) (hchart : IsChartPoint t z) :
    pointEval t z hchart infinityHaoMinusQuadraticNumerator =
      (z - infinityQuadraticShiftHaoPolynomial.eval t) / 2 := by
  rw [infinityHaoMinusQuadraticNumerator, map_mul, map_sub,
    pointEval_zCoordinate, halfClass, pointEval_algebraMap,
    pointEval_algebraMap]
  simp
  ring

/-- All four normalized numerators at the infinity branch `z=1`. -/
theorem transformedNumerator_positiveInfinity_values :
    positiveInfinityEval infinityXNumerator = 1 ∧
      positiveInfinityEval infinityHaoNumerator = 0 ∧
      positiveInfinityEval infinityHaoMinusXNumerator = 0 ∧
      positiveInfinityEval infinityHaoMinusQuadraticNumerator = 0 := by
  norm_num [positiveInfinityEval, infinityHaoPolynomial,
    infinityShiftedHaoPolynomial, infinityQuadraticShiftHaoPolynomial]

/-- All four normalized numerators at the infinity branch `z=-1`. -/
theorem transformedNumerator_negativeInfinity_values :
    negativeInfinityEval infinityXNumerator = 1 ∧
      negativeInfinityEval infinityHaoNumerator = -1 ∧
      negativeInfinityEval infinityHaoMinusXNumerator = -1 ∧
      negativeInfinityEval infinityHaoMinusQuadraticNumerator = -1 := by
  norm_num [negativeInfinityEval, infinityHaoPolynomial,
    infinityShiftedHaoPolynomial, infinityQuadraticShiftHaoPolynomial]

end InfinityCoordinateRing

end

end MazurTorsion.XOneThirteenInfinityChart
