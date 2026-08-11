/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenInfinityChart

/-!
# Explicit infinity-order certificates for the `X₁(13)` Hao functions

This file records the exact ideal-power facts behind the orders of the three
pole-cleared Hao numerators at the two branches at infinity.  Membership is
proved by polynomial identities in the chart coordinate ring.  Sharpness at
the positive branch is certified by finite jet maps to
`ℚ[T]/(T⁵)`, `ℚ[T]/(T³)`, and `ℚ[T]/(T²)`; nonvanishing at the negative branch
is certified by rational evaluation.

No valuation or divisor-order API is used.
-/

namespace MazurTorsion.XOneThirteenInfinityChart

open Ideal Polynomial

open XOneThirteenHaoFunctions
open XOneThirteenHaoShift
open XOneThirteenHaoQuadraticShift

noncomputable section

namespace InfinityCoordinateRing

/-! ## Contact identities and ideal-power membership -/

/-- The scalar `1/2` in the chart coordinate ring. -/
def chartHalfClass : InfinityCoordinateRing :=
  algebraMap ℚ[X] InfinityCoordinateRing (C (1 / 2 : ℚ))

/-- The class of the reversed polynomial occurring in `t³w`. -/
def infinityHaoPolynomialClass : InfinityCoordinateRing :=
  algebraMap ℚ[X] InfinityCoordinateRing infinityHaoPolynomial

/-- The class of the reversed polynomial occurring in `t³(w-X)`. -/
def infinityShiftedHaoPolynomialClass : InfinityCoordinateRing :=
  algebraMap ℚ[X] InfinityCoordinateRing infinityShiftedHaoPolynomial

/-- The class of the reversed polynomial occurring in
`t³(w-(X²+2X))`. -/
def infinityQuadraticShiftHaoPolynomialClass : InfinityCoordinateRing :=
  algebraMap ℚ[X] InfinityCoordinateRing
    infinityQuadraticShiftHaoPolynomial

theorem infinityHaoNumerator_eq_chartHalfClass :
    infinityHaoNumerator =
      chartHalfClass * (zCoordinate - infinityHaoPolynomialClass) := by
  rfl

theorem infinityHaoMinusXNumerator_eq_chartHalfClass :
    infinityHaoMinusXNumerator =
      chartHalfClass *
        (zCoordinate - infinityShiftedHaoPolynomialClass) := by
  rfl

theorem infinityHaoMinusQuadraticNumerator_eq_chartHalfClass :
    infinityHaoMinusQuadraticNumerator =
      chartHalfClass *
        (zCoordinate - infinityQuadraticShiftHaoPolynomialClass) := by
  rfl

/-- The exact fourth-order contact identity for the reversed Hao polynomial. -/
theorem infinityHao_contact_product :
    (zCoordinate - infinityHaoPolynomialClass) *
        (zCoordinate + infinityHaoPolynomialClass) =
      4 * tCoordinate ^ 4 * (1 + tCoordinate) := by
  have hcurve := zCoordinate_sq
  simp only [infinitySexticPolynomial, infinityHaoPolynomial,
    infinityHaoPolynomialClass, tCoordinate, map_add, map_mul, map_pow,
    map_one, map_ofNat] at hcurve ⊢
  linear_combination hcurve

/-- The exact second-order contact identity for the reversed polynomial of
`w-X`. -/
theorem infinityHaoMinusX_contact_product :
    (zCoordinate - infinityShiftedHaoPolynomialClass) *
        (zCoordinate + infinityShiftedHaoPolynomialClass) =
      -4 * tCoordinate ^ 2 * (1 + tCoordinate) := by
  have hcurve := zCoordinate_sq
  simp only [infinitySexticPolynomial, infinityShiftedHaoPolynomial,
    infinityShiftedHaoPolynomialClass, tCoordinate, map_add, map_mul,
    map_pow, map_one, map_ofNat] at hcurve ⊢
  linear_combination hcurve

@[simp] private theorem chartHalfClass_mul_two_scalar :
    chartHalfClass * 2 = 1 := by
  rw [chartHalfClass, show (2 : InfinityCoordinateRing) =
      algebraMap ℚ[X] InfinityCoordinateRing (C 2) by
    rw [C_ofNat, map_ofNat]]
  rw [← map_mul, ← C_mul]
  norm_num

private theorem chartHalfClass_mul_two (u : InfinityCoordinateRing) :
    chartHalfClass * (2 * u) = u := by
  calc
    chartHalfClass * (2 * u) = (chartHalfClass * 2) * u := by ring
    _ = u := by rw [chartHalfClass_mul_two_scalar, one_mul]

private theorem positiveInfinity_mem_of_eval_zero
    {u : InfinityCoordinateRing} (hu : positiveInfinityEval u = 0) :
    u ∈ positiveInfinityIdeal := by
  rw [← positiveInfinityEval_ker]
  exact RingHom.mem_ker.mpr hu

private theorem haoDifference_mem_positiveInfinity :
    zCoordinate - infinityHaoPolynomialClass ∈ positiveInfinityIdeal := by
  apply positiveInfinity_mem_of_eval_zero
  rw [positiveInfinityEval, map_sub, pointEval_zCoordinate,
    infinityHaoPolynomialClass, pointEval_algebraMap]
  norm_num [infinityHaoPolynomial]

private theorem haoAugmentation_mem_positiveInfinity :
    zCoordinate + infinityHaoPolynomialClass - 2 ∈
      positiveInfinityIdeal := by
  apply positiveInfinity_mem_of_eval_zero
  rw [positiveInfinityEval, map_sub, map_add, pointEval_zCoordinate,
    infinityHaoPolynomialClass, pointEval_algebraMap, map_ofNat]
  norm_num [infinityHaoPolynomial]

private theorem shiftedHaoDifference_mem_positiveInfinity :
    zCoordinate - infinityShiftedHaoPolynomialClass ∈
      positiveInfinityIdeal := by
  apply positiveInfinity_mem_of_eval_zero
  rw [positiveInfinityEval, map_sub, pointEval_zCoordinate,
    infinityShiftedHaoPolynomialClass, pointEval_algebraMap]
  norm_num [infinityShiftedHaoPolynomial]

private theorem shiftedHaoAugmentation_mem_positiveInfinity :
    zCoordinate + infinityShiftedHaoPolynomialClass - 2 ∈
      positiveInfinityIdeal := by
  apply positiveInfinity_mem_of_eval_zero
  rw [positiveInfinityEval, map_sub, map_add, pointEval_zCoordinate,
    infinityShiftedHaoPolynomialClass, pointEval_algebraMap, map_ofNat]
  norm_num [infinityShiftedHaoPolynomial]

private theorem tCoordinate_mem_positiveInfinity :
    tCoordinate ∈ positiveInfinityIdeal := by
  rw [positiveInfinityIdeal_eq]
  exact Ideal.subset_span (by simp)

private theorem mem_next_power_of_contact
    (k : ℕ) (e a h : InfinityCoordinateRing)
    (he : e ∈ positiveInfinityIdeal ^ k)
    (ha : a ∈ positiveInfinityIdeal)
    (hh : h ∈ positiveInfinityIdeal ^ (k + 1))
    (hcontact : 2 * e = h - e * a) :
    e ∈ positiveInfinityIdeal ^ (k + 1) := by
  have hea : e * a ∈ positiveInfinityIdeal ^ (k + 1) := by
    simpa only [pow_succ] using Ideal.mul_mem_mul he ha
  have htwo : 2 * e ∈ positiveInfinityIdeal ^ (k + 1) := by
    rw [hcontact]
    exact (positiveInfinityIdeal ^ (k + 1)).sub_mem hh hea
  have hscaled :=
    (positiveInfinityIdeal ^ (k + 1)).mul_mem_left chartHalfClass htwo
  simpa only [chartHalfClass_mul_two] using hscaled

private theorem haoDifference_contact_rearranged :
    2 * (zCoordinate - infinityHaoPolynomialClass) =
      4 * tCoordinate ^ 4 * (1 + tCoordinate) -
        (zCoordinate - infinityHaoPolynomialClass) *
          (zCoordinate + infinityHaoPolynomialClass - 2) := by
  rw [← infinityHao_contact_product]
  ring

private theorem shiftedHaoDifference_contact_rearranged :
    2 * (zCoordinate - infinityShiftedHaoPolynomialClass) =
      -4 * tCoordinate ^ 2 * (1 + tCoordinate) -
        (zCoordinate - infinityShiftedHaoPolynomialClass) *
          (zCoordinate + infinityShiftedHaoPolynomialClass - 2) := by
  rw [← infinityHaoMinusX_contact_product]
  ring

private theorem haoContactTerm_mem_fourth :
    4 * tCoordinate ^ 4 * (1 + tCoordinate) ∈
      positiveInfinityIdeal ^ 4 := by
  have ht4 : tCoordinate ^ 4 ∈ positiveInfinityIdeal ^ 4 :=
    Ideal.pow_mem_pow tCoordinate_mem_positiveInfinity 4
  simpa only [mul_assoc] using
    (positiveInfinityIdeal ^ 4).mul_mem_left 4
      ((positiveInfinityIdeal ^ 4).mul_mem_right (1 + tCoordinate) ht4)

private theorem shiftedHaoContactTerm_mem_sq :
    -4 * tCoordinate ^ 2 * (1 + tCoordinate) ∈
      positiveInfinityIdeal ^ 2 := by
  have ht2 : tCoordinate ^ 2 ∈ positiveInfinityIdeal ^ 2 :=
    Ideal.pow_mem_pow tCoordinate_mem_positiveInfinity 2
  simpa only [mul_assoc] using
    (positiveInfinityIdeal ^ 2).mul_mem_left (-4)
      ((positiveInfinityIdeal ^ 2).mul_mem_right (1 + tCoordinate) ht2)

/-- The pole-cleared numerator `t³w` belongs to the fourth power of the
positive infinity ideal. -/
theorem infinityHaoNumerator_mem_positiveInfinityIdeal_fourth :
    infinityHaoNumerator ∈ positiveInfinityIdeal ^ 4 := by
  let e := zCoordinate - infinityHaoPolynomialClass
  let a := zCoordinate + infinityHaoPolynomialClass - 2
  have he1 : e ∈ positiveInfinityIdeal ^ 1 := by
    simpa only [pow_one, e] using haoDifference_mem_positiveInfinity
  have ha : a ∈ positiveInfinityIdeal := by
    simpa only [a] using haoAugmentation_mem_positiveInfinity
  have hh4 : 4 * tCoordinate ^ 4 * (1 + tCoordinate) ∈
      positiveInfinityIdeal ^ 4 := haoContactTerm_mem_fourth
  have hh2 : 4 * tCoordinate ^ 4 * (1 + tCoordinate) ∈
      positiveInfinityIdeal ^ 2 :=
    (Ideal.pow_le_pow_right (by norm_num : 2 ≤ 4)) hh4
  have he2 : e ∈ positiveInfinityIdeal ^ 2 := by
    exact mem_next_power_of_contact 1 e a _ he1 ha hh2 (by
      simpa only [e, a] using haoDifference_contact_rearranged)
  have hh3 : 4 * tCoordinate ^ 4 * (1 + tCoordinate) ∈
      positiveInfinityIdeal ^ 3 :=
    (Ideal.pow_le_pow_right (by norm_num : 3 ≤ 4)) hh4
  have he3 : e ∈ positiveInfinityIdeal ^ 3 := by
    exact mem_next_power_of_contact 2 e a _ he2 ha hh3 (by
      simpa only [e, a] using haoDifference_contact_rearranged)
  have he4 : e ∈ positiveInfinityIdeal ^ 4 := by
    exact mem_next_power_of_contact 3 e a _ he3 ha hh4 (by
      simpa only [e, a] using haoDifference_contact_rearranged)
  rw [infinityHaoNumerator_eq_chartHalfClass]
  exact (positiveInfinityIdeal ^ 4).mul_mem_left chartHalfClass he4

/-- The pole-cleared numerator `t³(w-X)` belongs to the square of the positive
infinity ideal. -/
theorem infinityHaoMinusXNumerator_mem_positiveInfinityIdeal_sq :
    infinityHaoMinusXNumerator ∈ positiveInfinityIdeal ^ 2 := by
  let e := zCoordinate - infinityShiftedHaoPolynomialClass
  let a := zCoordinate + infinityShiftedHaoPolynomialClass - 2
  have he1 : e ∈ positiveInfinityIdeal ^ 1 := by
    simpa only [pow_one, e] using shiftedHaoDifference_mem_positiveInfinity
  have ha : a ∈ positiveInfinityIdeal := by
    simpa only [a] using shiftedHaoAugmentation_mem_positiveInfinity
  have he2 : e ∈ positiveInfinityIdeal ^ 2 := by
    exact mem_next_power_of_contact 1 e a _ he1 ha
      shiftedHaoContactTerm_mem_sq (by
        simpa only [e, a] using shiftedHaoDifference_contact_rearranged)
  rw [infinityHaoMinusXNumerator_eq_chartHalfClass]
  exact (positiveInfinityIdeal ^ 2).mul_mem_left chartHalfClass he2

/-- The quadratic-shift numerator belongs to the positive infinity ideal. -/
theorem infinityHaoMinusQuadraticNumerator_mem_positiveInfinityIdeal :
    infinityHaoMinusQuadraticNumerator ∈ positiveInfinityIdeal := by
  apply positiveInfinity_mem_of_eval_zero
  exact transformedNumerator_positiveInfinity_values.2.2.2

/-! ## Truncated positive-branch jets -/

/-- The ideal `(T^n)` used for the `n`-th truncated jet. -/
def truncatedJetIdeal (n : ℕ) : Ideal ℚ[X] :=
  Ideal.span {(X : ℚ[X]) ^ n}

/-- The coefficient ring `ℚ[T]/(T^n)` of the `n`-th jet. -/
abbrev TruncatedJetRing (n : ℕ) := ℚ[X] ⧸ truncatedJetIdeal n

/-- The quotient map to `ℚ[T]/(T^n)`. -/
def truncatedJetMk (n : ℕ) : ℚ[X] →+* TruncatedJetRing n :=
  Ideal.Quotient.mk (truncatedJetIdeal n)

/-- The positive-branch expansion of `z` through degree four. -/
def positiveJetSeries : ℚ[X] :=
  1 + X + X ^ 3 + 2 * X ^ 4

theorem positiveJetSeries_sq_sub_infinitySexticPolynomial :
    positiveJetSeries ^ 2 - infinitySexticPolynomial =
      4 * X ^ 7 * (1 + X) := by
  simp [positiveJetSeries, infinitySexticPolynomial]
  ring

theorem positiveJetRelation_mem_two :
    positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal 2 := by
  rw [positiveJetSeries_sq_sub_infinitySexticPolynomial,
    truncatedJetIdeal, Ideal.mem_span_singleton]
  refine ⟨4 * X ^ 5 * (1 + X), ?_⟩
  ring

theorem positiveJetRelation_mem_three :
    positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal 3 := by
  rw [positiveJetSeries_sq_sub_infinitySexticPolynomial,
    truncatedJetIdeal, Ideal.mem_span_singleton]
  refine ⟨4 * X ^ 4 * (1 + X), ?_⟩
  ring

theorem positiveJetRelation_mem_five :
    positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal 5 := by
  rw [positiveJetSeries_sq_sub_infinitySexticPolynomial,
    truncatedJetIdeal, Ideal.mem_span_singleton]
  refine ⟨4 * X ^ 2 * (1 + X), ?_⟩
  ring

/-- Evaluation of the infinity chart on any truncated positive-branch jet
for which the displayed series satisfies the curve equation. -/
def positiveJetEval (n : ℕ)
    (hrelation : positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal n) :
    InfinityCoordinateRing →+* TruncatedJetRing n :=
  AdjoinRoot.lift (truncatedJetMk n) (truncatedJetMk n positiveJetSeries) (by
    have hzero : truncatedJetMk n
        (positiveJetSeries ^ 2 - infinitySexticPolynomial) = 0 := by
      change Ideal.Quotient.mk (truncatedJetIdeal n)
        (positiveJetSeries ^ 2 - infinitySexticPolynomial) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hrelation
    simpa only [infinityRelationPolynomial, eval₂_sub, eval₂_pow,
      eval₂_X, eval₂_C, map_sub, map_pow] using hzero)

@[simp] theorem positiveJetEval_zCoordinate
    (n : ℕ)
    (hrelation : positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal n) :
    positiveJetEval n hrelation zCoordinate =
      truncatedJetMk n positiveJetSeries := by
  exact AdjoinRoot.lift_root _

@[simp] theorem positiveJetEval_algebraMap
    (n : ℕ)
    (hrelation : positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal n) (p : ℚ[X]) :
    positiveJetEval n hrelation
        (algebraMap ℚ[X] InfinityCoordinateRing p) =
      truncatedJetMk n p := by
  exact AdjoinRoot.lift_of _

@[simp] theorem positiveJetEval_tCoordinate
    (n : ℕ)
    (hrelation : positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal n) :
    positiveJetEval n hrelation tCoordinate = truncatedJetMk n X := by
  exact positiveJetEval_algebraMap n hrelation X

/-- The principal tangent-direction ideal in the truncated jet ring. -/
def truncatedJetDirectionIdeal (n : ℕ) : Ideal (TruncatedJetRing n) :=
  Ideal.span {truncatedJetMk n X}

theorem positiveJetSeries_sub_one :
    positiveJetSeries - 1 = X * (1 + X ^ 2 + 2 * X ^ 3) := by
  simp [positiveJetSeries]
  ring

theorem positiveInfinityIdeal_le_positiveJet_comap
    (n : ℕ)
    (hrelation : positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal n) :
    positiveInfinityIdeal ≤
      (truncatedJetDirectionIdeal n).comap
        (positiveJetEval n hrelation) := by
  rw [positiveInfinityIdeal_eq, Ideal.span_le]
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl
  · change positiveJetEval n hrelation tCoordinate ∈
      truncatedJetDirectionIdeal n
    rw [positiveJetEval_tCoordinate]
    exact Ideal.subset_span (by simp)
  · change positiveJetEval n hrelation (zCoordinate - 1) ∈
      truncatedJetDirectionIdeal n
    rw [map_sub, positiveJetEval_zCoordinate, map_one]
    rw [← map_one (truncatedJetMk n), ← map_sub,
      positiveJetSeries_sub_one, map_mul]
    exact (truncatedJetDirectionIdeal n).mul_mem_right _
      (Ideal.subset_span (by simp))

theorem truncatedJetMk_X_pow_eq_zero_of_le
    {n k : ℕ} (hnk : n ≤ k) :
    truncatedJetMk n ((X : ℚ[X]) ^ k) = 0 := by
  change Ideal.Quotient.mk (truncatedJetIdeal n) ((X : ℚ[X]) ^ k) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, truncatedJetIdeal,
    Ideal.mem_span_singleton]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
  exact ⟨X ^ d, by rw [pow_add]⟩

theorem truncatedJetDirectionIdeal_pow_eq_bot (n : ℕ) :
    truncatedJetDirectionIdeal n ^ n = ⊥ := by
  rw [truncatedJetDirectionIdeal, Ideal.span_singleton_pow]
  have hx : (truncatedJetMk n X) ^ n = 0 := by
    rw [← map_pow]
    exact truncatedJetMk_X_pow_eq_zero_of_le le_rfl
  rw [hx]
  simp

theorem positiveInfinityIdeal_pow_le_positiveJetEval_ker
    (n : ℕ)
    (hrelation : positiveJetSeries ^ 2 - infinitySexticPolynomial ∈
      truncatedJetIdeal n) :
    positiveInfinityIdeal ^ n ≤
      RingHom.ker (positiveJetEval n hrelation) := by
  have hm := positiveInfinityIdeal_le_positiveJet_comap n hrelation
  have hpow : positiveInfinityIdeal ^ n ≤
      ((truncatedJetDirectionIdeal n).comap
        (positiveJetEval n hrelation)) ^ n :=
    Ideal.pow_right_mono hm n
  have hcomap := Ideal.le_comap_pow
    (positiveJetEval n hrelation) (K := truncatedJetDirectionIdeal n) n
  intro u hu
  have hu' := hcomap (hpow hu)
  have hzero : positiveJetEval n hrelation u = 0 := by
    have : positiveJetEval n hrelation u ∈
        truncatedJetDirectionIdeal n ^ n := hu'
    rw [truncatedJetDirectionIdeal_pow_eq_bot] at this
    exact Ideal.mem_bot.mp this
  exact RingHom.mem_ker.mpr hzero

theorem truncatedJetMk_X_pow_ne_zero
    {n k : ℕ} (hkn : k < n) :
    truncatedJetMk n ((X : ℚ[X]) ^ k) ≠ 0 := by
  intro hzero
  have hdiv : (X : ℚ[X]) ^ n ∣ X ^ k := by
    rw [← Ideal.mem_span_singleton]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hdegree := Polynomial.natDegree_le_of_dvd hdiv
    (by simp : (X : ℚ[X]) ^ k ≠ 0)
  simp only [natDegree_pow, natDegree_X, mul_one] at hdegree
  exact (Nat.not_le_of_lt hkn) hdegree

@[simp] private theorem polynomialHalf_mul_two :
    C (1 / 2 : ℚ) * (2 : ℚ[X]) = 1 := by
  rw [show (2 : ℚ[X]) = C 2 by rw [C_ofNat], ← C_mul]
  norm_num

theorem positiveFiveJetEval_infinityHaoNumerator :
    positiveJetEval 5 positiveJetRelation_mem_five infinityHaoNumerator =
      truncatedJetMk 5 (X ^ 4) := by
  rw [infinityHaoNumerator_eq_chartHalfClass]
  simp only [map_mul, map_sub, positiveJetEval_zCoordinate,
    infinityHaoPolynomialClass, positiveJetEval_algebraMap,
    chartHalfClass]
  change truncatedJetMk 5
      (C (1 / 2 : ℚ) * (positiveJetSeries - infinityHaoPolynomial)) =
    truncatedJetMk 5 (X ^ 4)
  rw [show positiveJetSeries - infinityHaoPolynomial = 2 * X ^ 4 by
    simp [positiveJetSeries, infinityHaoPolynomial]]
  congr 1
  calc
    C (1 / 2 : ℚ) * (2 * X ^ 4) =
        (C (1 / 2 : ℚ) * 2) * X ^ 4 := by ring
    _ = X ^ 4 := by rw [polynomialHalf_mul_two, one_mul]

theorem positiveThreeJetEval_infinityHaoMinusXNumerator :
    positiveJetEval 3 positiveJetRelation_mem_three
        infinityHaoMinusXNumerator =
      truncatedJetMk 3 (-X ^ 2) := by
  rw [infinityHaoMinusXNumerator_eq_chartHalfClass]
  simp only [map_mul, map_sub, positiveJetEval_zCoordinate,
    infinityShiftedHaoPolynomialClass, positiveJetEval_algebraMap,
    chartHalfClass]
  have hx4 : truncatedJetMk 3 ((X : ℚ[X]) ^ 4) = 0 :=
    truncatedJetMk_X_pow_eq_zero_of_le (by norm_num)
  change truncatedJetMk 3
      (C (1 / 2 : ℚ) *
        (positiveJetSeries - infinityShiftedHaoPolynomial)) =
    truncatedJetMk 3 (-X ^ 2)
  rw [show positiveJetSeries - infinityShiftedHaoPolynomial =
      2 * (-X ^ 2 + X ^ 4) by
    simp [positiveJetSeries, infinityShiftedHaoPolynomial]
    ring,
    show C (1 / 2 : ℚ) * (2 * (-X ^ 2 + X ^ 4)) =
      -X ^ 2 + X ^ 4 by
        calc
          C (1 / 2 : ℚ) * (2 * (-X ^ 2 + X ^ 4)) =
              (C (1 / 2 : ℚ) * 2) * (-X ^ 2 + X ^ 4) := by ring
          _ = -X ^ 2 + X ^ 4 := by
            rw [polynomialHalf_mul_two, one_mul],
    map_add, hx4, add_zero]

theorem positiveTwoJetEval_infinityHaoMinusQuadraticNumerator :
    positiveJetEval 2 positiveJetRelation_mem_two
        infinityHaoMinusQuadraticNumerator =
      truncatedJetMk 2 (-X) := by
  rw [infinityHaoMinusQuadraticNumerator_eq_chartHalfClass]
  simp only [map_mul, map_sub, positiveJetEval_zCoordinate,
    infinityQuadraticShiftHaoPolynomialClass,
    positiveJetEval_algebraMap, chartHalfClass]
  have hx2 : truncatedJetMk 2 ((X : ℚ[X]) ^ 2) = 0 :=
    truncatedJetMk_X_pow_eq_zero_of_le le_rfl
  have hx4 : truncatedJetMk 2 ((X : ℚ[X]) ^ 4) = 0 :=
    truncatedJetMk_X_pow_eq_zero_of_le (by norm_num)
  change truncatedJetMk 2
      (C (1 / 2 : ℚ) *
        (positiveJetSeries - infinityQuadraticShiftHaoPolynomial)) =
    truncatedJetMk 2 (-X)
  rw [show positiveJetSeries - infinityQuadraticShiftHaoPolynomial =
      2 * (-X - 2 * X ^ 2 + X ^ 4) by
    simp [positiveJetSeries, infinityQuadraticShiftHaoPolynomial]
    ring,
    show C (1 / 2 : ℚ) * (2 * (-X - 2 * X ^ 2 + X ^ 4)) =
      -X - 2 * X ^ 2 + X ^ 4 by
        calc
          C (1 / 2 : ℚ) * (2 * (-X - 2 * X ^ 2 + X ^ 4)) =
              (C (1 / 2 : ℚ) * 2) * (-X - 2 * X ^ 2 + X ^ 4) := by ring
          _ = -X - 2 * X ^ 2 + X ^ 4 := by
            rw [polynomialHalf_mul_two, one_mul],
    map_add, map_sub, map_mul, hx2, hx4]
  ring

/-! ## Sharpness and the exact ideal-power table -/

theorem infinityHaoNumerator_not_mem_positiveInfinityIdeal_fifth :
    infinityHaoNumerator ∉ positiveInfinityIdeal ^ 5 := by
  intro hmem
  have hker := positiveInfinityIdeal_pow_le_positiveJetEval_ker 5
    positiveJetRelation_mem_five hmem
  have hzero := RingHom.mem_ker.mp hker
  rw [positiveFiveJetEval_infinityHaoNumerator] at hzero
  exact (truncatedJetMk_X_pow_ne_zero (n := 5) (k := 4)
    (by norm_num)) hzero

theorem infinityHaoMinusXNumerator_not_mem_positiveInfinityIdeal_cube :
    infinityHaoMinusXNumerator ∉ positiveInfinityIdeal ^ 3 := by
  intro hmem
  have hker := positiveInfinityIdeal_pow_le_positiveJetEval_ker 3
    positiveJetRelation_mem_three hmem
  have hzero := RingHom.mem_ker.mp hker
  rw [positiveThreeJetEval_infinityHaoMinusXNumerator] at hzero
  have hne : truncatedJetMk 3 ((X : ℚ[X]) ^ 2) ≠ 0 :=
    truncatedJetMk_X_pow_ne_zero (n := 3) (k := 2) (by norm_num)
  exact hne (neg_eq_zero.mp hzero)

theorem infinityHaoMinusQuadraticNumerator_not_mem_positiveInfinityIdeal_sq :
    infinityHaoMinusQuadraticNumerator ∉ positiveInfinityIdeal ^ 2 := by
  intro hmem
  have hker := positiveInfinityIdeal_pow_le_positiveJetEval_ker 2
    positiveJetRelation_mem_two hmem
  have hzero := RingHom.mem_ker.mp hker
  rw [positiveTwoJetEval_infinityHaoMinusQuadraticNumerator] at hzero
  have hne : truncatedJetMk 2 (X : ℚ[X]) ≠ 0 :=
    by simpa using (truncatedJetMk_X_pow_ne_zero (n := 2) (k := 1)
      (by norm_num))
  exact hne (neg_eq_zero.mp hzero)

theorem infinityHaoNumerator_not_mem_negativeInfinityIdeal :
    infinityHaoNumerator ∉ negativeInfinityIdeal := by
  rw [← negativeInfinityEval_ker]
  intro hmem
  have hzero := RingHom.mem_ker.mp hmem
  rw [transformedNumerator_negativeInfinity_values.2.1] at hzero
  norm_num at hzero

theorem infinityHaoMinusXNumerator_not_mem_negativeInfinityIdeal :
    infinityHaoMinusXNumerator ∉ negativeInfinityIdeal := by
  rw [← negativeInfinityEval_ker]
  intro hmem
  have hzero := RingHom.mem_ker.mp hmem
  rw [transformedNumerator_negativeInfinity_values.2.2.1] at hzero
  norm_num at hzero

theorem infinityHaoMinusQuadraticNumerator_not_mem_negativeInfinityIdeal :
    infinityHaoMinusQuadraticNumerator ∉ negativeInfinityIdeal := by
  rw [← negativeInfinityEval_ker]
  intro hmem
  have hzero := RingHom.mem_ker.mp hmem
  rw [transformedNumerator_negativeInfinity_values.2.2.2] at hzero
  norm_num at hzero

/-- The complete ideal-theoretic exponent table for the three pole-cleared
numerators.  Each row contains positive-branch membership, sharpness in the
next power, and negative-branch nonmembership. -/
theorem transformedNumerator_infinityIdealPowerTable :
    (infinityHaoNumerator ∈ positiveInfinityIdeal ^ 4 ∧
      infinityHaoNumerator ∉ positiveInfinityIdeal ^ 5 ∧
      infinityHaoNumerator ∉ negativeInfinityIdeal) ∧
    (infinityHaoMinusXNumerator ∈ positiveInfinityIdeal ^ 2 ∧
      infinityHaoMinusXNumerator ∉ positiveInfinityIdeal ^ 3 ∧
      infinityHaoMinusXNumerator ∉ negativeInfinityIdeal) ∧
    (infinityHaoMinusQuadraticNumerator ∈ positiveInfinityIdeal ∧
      infinityHaoMinusQuadraticNumerator ∉ positiveInfinityIdeal ^ 2 ∧
      infinityHaoMinusQuadraticNumerator ∉ negativeInfinityIdeal) := by
  exact ⟨⟨infinityHaoNumerator_mem_positiveInfinityIdeal_fourth,
      infinityHaoNumerator_not_mem_positiveInfinityIdeal_fifth,
      infinityHaoNumerator_not_mem_negativeInfinityIdeal⟩,
    ⟨infinityHaoMinusXNumerator_mem_positiveInfinityIdeal_sq,
      infinityHaoMinusXNumerator_not_mem_positiveInfinityIdeal_cube,
      infinityHaoMinusXNumerator_not_mem_negativeInfinityIdeal⟩,
    ⟨infinityHaoMinusQuadraticNumerator_mem_positiveInfinityIdeal,
      infinityHaoMinusQuadraticNumerator_not_mem_positiveInfinityIdeal_sq,
      infinityHaoMinusQuadraticNumerator_not_mem_negativeInfinityIdeal⟩⟩

end InfinityCoordinateRing

end

end MazurTorsion.XOneThirteenInfinityChart
