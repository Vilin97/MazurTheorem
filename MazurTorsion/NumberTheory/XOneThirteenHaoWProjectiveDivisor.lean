/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenInfinityOrderCertificates
import MazurTorsion.NumberTheory.XOneThirteenRationalAffineDivisorClass
import MazurTorsion.NumberTheory.XOneThirteenUniversalCuspRelationGroup

/-!
# A certified projective divisor relation for Hao's function on `X₁(13)`

This file constructs the first projective consumer of the checked affine and
infinity-chart calculations.  The affine principal-ideal factorization of
Hao's function `w` is paired with exact first-order affine jets, exact orders
of the pole-cleared numerator at both infinity branches, and exact
first-order certificates for the chart parameter `t`.

The resulting raw six-cusp divisor is

`(0,1) + (-1,1) + ∞⁺ - 3∞⁻`.

It is translated to the first relation vector `A + B - 3D` in the existing
Mazur--Tate cusp presentation.  We then quotient the free cusp group only by
relations carrying this explicit certificate.  This is a curve-specific
principal-divisor presentation, not a construction of the full Picard group,
and it uses no UFD, Dedekind-domain, valuation, or Jacobian assumption.
-/

namespace MazurTorsion.XOneThirteenHaoWProjectiveDivisor

open Ideal Polynomial

open XOneThirteenMumford
open XOneThirteenPicard
open XOneThirteenPicard.CoordinateRing
open XOneThirteenHaoFunctions
open XOneThirteenInfinityChart

noncomputable section

/-- Concrete ideal-theoretic meaning of exact order `n`. -/
def HasExactIdealOrder {R : Type*} [CommSemiring R]
    (I : Ideal R) (u : R) (n : ℕ) : Prop :=
  u ∈ I ^ n ∧ u ∉ I ^ (n + 1)

/-! ## Exact first-order affine jets at the two zeros of `w` -/

abbrev TwoJetRing :=
  InfinityCoordinateRing.TruncatedJetRing 2

abbrev twoJetMk : ℚ[X] →+* TwoJetRing :=
  InfinityCoordinateRing.truncatedJetMk 2

/-- Substitution of an affine `X`-series into the two-jet ring. -/
def affineTwoJetBaseEval (xSeries : ℚ[X]) : ℚ[X] →+* TwoJetRing :=
  twoJetMk.comp (Polynomial.compRingHom xSeries)

/-- The first-order branch at the affine cusp `(0,1)`. -/
def cuspZeroPositiveXSeries : ℚ[X] := X

/-- The ordinate series `Y = 1+2T` at `(0,1)`. -/
def cuspZeroPositiveYSeries : ℚ[X] := 1 + 2 * X

/-- The first-order branch at the affine cusp `(-1,1)`. -/
def cuspNegOnePositiveXSeries : ℚ[X] := -1 + X

/-- The ordinate series `Y = 1-T` at `(-1,1)`. -/
def cuspNegOnePositiveYSeries : ℚ[X] := 1 - X

@[simp] private theorem polynomialHalf_mul_two :
    C (1 / 2 : ℚ) * (2 : ℚ[X]) = 1 := by
  rw [show (2 : ℚ[X]) = C 2 by rw [C_ofNat], ← C_mul]
  norm_num

theorem cuspZeroPositiveTwoJet_relation_mem :
    cuspZeroPositiveYSeries ^ 2 -
        sexticPolynomial.comp cuspZeroPositiveXSeries ∈
      InfinityCoordinateRing.truncatedJetIdeal 2 := by
  rw [InfinityCoordinateRing.truncatedJetIdeal,
    Ideal.mem_span_singleton]
  refine ⟨-(X ^ 4 + 2 * X ^ 3 + X ^ 2 + 2 * X + 2), ?_⟩
  simp [cuspZeroPositiveXSeries, cuspZeroPositiveYSeries,
    sexticPolynomial]
  ring

theorem cuspNegOnePositiveTwoJet_relation_mem :
    cuspNegOnePositiveYSeries ^ 2 -
        sexticPolynomial.comp cuspNegOnePositiveXSeries ∈
      InfinityCoordinateRing.truncatedJetIdeal 2 := by
  rw [InfinityCoordinateRing.truncatedJetIdeal,
    Ideal.mem_span_singleton]
  refine ⟨-X ^ 4 + 4 * X ^ 3 - 6 * X ^ 2 + 2 * X, ?_⟩
  simp [cuspNegOnePositiveXSeries, cuspNegOnePositiveYSeries,
    sexticPolynomial]
  ring

/-- An affine chart map to dual numbers from explicit `X`- and `Y`-series. -/
def affineTwoJetEval
    (xSeries ySeries : ℚ[X])
    (hrelation : ySeries ^ 2 - sexticPolynomial.comp xSeries ∈
      InfinityCoordinateRing.truncatedJetIdeal 2) :
    CoordinateRing →+* TwoJetRing :=
  AdjoinRoot.lift (affineTwoJetBaseEval xSeries) (twoJetMk ySeries) (by
    have hzero : twoJetMk
        (ySeries ^ 2 - sexticPolynomial.comp xSeries) = 0 := by
      change Ideal.Quotient.mk
        (InfinityCoordinateRing.truncatedJetIdeal 2)
          (ySeries ^ 2 - sexticPolynomial.comp xSeries) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hrelation
    simpa only [relationPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
      eval₂_C, affineTwoJetBaseEval, RingHom.comp_apply,
      Polynomial.coe_compRingHom_apply, map_sub, map_pow] using hzero)

@[simp] theorem affineTwoJetEval_yCoordinate
    (xSeries ySeries : ℚ[X])
    (hrelation : ySeries ^ 2 - sexticPolynomial.comp xSeries ∈
      InfinityCoordinateRing.truncatedJetIdeal 2) :
    affineTwoJetEval xSeries ySeries hrelation yCoordinate =
      twoJetMk ySeries := by
  exact AdjoinRoot.lift_root _

@[simp] theorem affineTwoJetEval_algebraMap
    (xSeries ySeries : ℚ[X])
    (hrelation : ySeries ^ 2 - sexticPolynomial.comp xSeries ∈
      InfinityCoordinateRing.truncatedJetIdeal 2) (p : ℚ[X]) :
    affineTwoJetEval xSeries ySeries hrelation
      (algebraMap ℚ[X] CoordinateRing p) =
      twoJetMk (p.comp xSeries) := by
  exact AdjoinRoot.lift_of _

/-- The affine two-jet at `(0,1)`. -/
def cuspZeroPositiveTwoJetEval : CoordinateRing →+* TwoJetRing :=
  affineTwoJetEval cuspZeroPositiveXSeries cuspZeroPositiveYSeries
    cuspZeroPositiveTwoJet_relation_mem

/-- The affine two-jet at `(-1,1)`. -/
def cuspNegOnePositiveTwoJetEval : CoordinateRing →+* TwoJetRing :=
  affineTwoJetEval cuspNegOnePositiveXSeries cuspNegOnePositiveYSeries
    cuspNegOnePositiveTwoJet_relation_mem

theorem cuspZeroPositiveTwoJetEval_haoW :
    cuspZeroPositiveTwoJetEval haoW = twoJetMk X := by
  simp only [cuspZeroPositiveTwoJetEval, haoW, halfClass,
    ordinateClass, map_mul, map_sub, affineTwoJetEval_yCoordinate,
    affineTwoJetEval_algebraMap]
  have hx2 : twoJetMk ((X : ℚ[X]) ^ 2) = 0 :=
    InfinityCoordinateRing.truncatedJetMk_X_pow_eq_zero_of_le le_rfl
  have hx3 : twoJetMk ((X : ℚ[X]) ^ 3) = 0 :=
    InfinityCoordinateRing.truncatedJetMk_X_pow_eq_zero_of_le (by norm_num)
  change twoJetMk
      ((C (1 / 2 : ℚ)).comp cuspZeroPositiveXSeries) *
        (twoJetMk cuspZeroPositiveYSeries -
          twoJetMk (haoPolynomial.comp cuspZeroPositiveXSeries)) =
    twoJetMk X
  simp only [C_comp, ← map_sub, ← map_mul]
  rw [show cuspZeroPositiveYSeries -
      haoPolynomial.comp cuspZeroPositiveXSeries =
      2 * X - X ^ 2 - X ^ 3 by
    simp [cuspZeroPositiveXSeries, cuspZeroPositiveYSeries,
      haoPolynomial]
    ring]
  rw [show C (1 / 2 : ℚ) * (2 * X - X ^ 2 - X ^ 3) =
      X - C (1 / 2 : ℚ) * X ^ 2 - C (1 / 2 : ℚ) * X ^ 3 by
    calc
      C (1 / 2 : ℚ) * (2 * X - X ^ 2 - X ^ 3) =
          (C (1 / 2 : ℚ) * 2) * X -
            C (1 / 2 : ℚ) * X ^ 2 -
              C (1 / 2 : ℚ) * X ^ 3 := by ring
      _ = X - C (1 / 2 : ℚ) * X ^ 2 -
          C (1 / 2 : ℚ) * X ^ 3 := by
        rw [polynomialHalf_mul_two, one_mul]]
  simp only [map_sub, map_mul, hx2, hx3, mul_zero, sub_zero]

theorem cuspNegOnePositiveTwoJetEval_haoW :
    cuspNegOnePositiveTwoJetEval haoW = twoJetMk (-X) := by
  simp only [cuspNegOnePositiveTwoJetEval, haoW, halfClass,
    ordinateClass, map_mul, map_sub, affineTwoJetEval_yCoordinate,
    affineTwoJetEval_algebraMap]
  have hx2 : twoJetMk ((X : ℚ[X]) ^ 2) = 0 :=
    InfinityCoordinateRing.truncatedJetMk_X_pow_eq_zero_of_le le_rfl
  have hx3 : twoJetMk ((X : ℚ[X]) ^ 3) = 0 :=
    InfinityCoordinateRing.truncatedJetMk_X_pow_eq_zero_of_le (by norm_num)
  change twoJetMk
      ((C (1 / 2 : ℚ)).comp cuspNegOnePositiveXSeries) *
        (twoJetMk cuspNegOnePositiveYSeries -
          twoJetMk (haoPolynomial.comp cuspNegOnePositiveXSeries)) =
    twoJetMk (-X)
  simp only [C_comp, ← map_sub, ← map_mul]
  rw [show cuspNegOnePositiveYSeries -
      haoPolynomial.comp cuspNegOnePositiveXSeries =
      -2 * X + 2 * X ^ 2 - X ^ 3 by
    simp [cuspNegOnePositiveXSeries, cuspNegOnePositiveYSeries,
      haoPolynomial]
    ring]
  rw [show C (1 / 2 : ℚ) * (-2 * X + 2 * X ^ 2 - X ^ 3) =
      -X + X ^ 2 - C (1 / 2 : ℚ) * X ^ 3 by
    calc
      C (1 / 2 : ℚ) * (-2 * X + 2 * X ^ 2 - X ^ 3) =
          -(C (1 / 2 : ℚ) * 2) * X +
            (C (1 / 2 : ℚ) * 2) * X ^ 2 -
              C (1 / 2 : ℚ) * X ^ 3 := by ring
      _ = -X + X ^ 2 - C (1 / 2 : ℚ) * X ^ 3 := by
        rw [polynomialHalf_mul_two, one_mul]
        ring]
  simp only [map_sub, map_add, map_neg, map_mul, hx2, hx3,
    mul_zero, sub_zero, add_zero]

private theorem pointIdeal_sq_le_affineTwoJetEval_ker
    (x y : ℚ) (xSeries ySeries : ℚ[X])
    (hrelation : ySeries ^ 2 - sexticPolynomial.comp xSeries ∈
      InfinityCoordinateRing.truncatedJetIdeal 2)
    (hx : affineTwoJetEval xSeries ySeries hrelation (xClass x) ∈
      InfinityCoordinateRing.truncatedJetDirectionIdeal 2)
    (hy : affineTwoJetEval xSeries ySeries hrelation (yClass y) ∈
      InfinityCoordinateRing.truncatedJetDirectionIdeal 2) :
    pointIdeal x y ^ 2 ≤
      RingHom.ker (affineTwoJetEval xSeries ySeries hrelation) := by
  have hm : pointIdeal x y ≤
      (InfinityCoordinateRing.truncatedJetDirectionIdeal 2).comap
        (affineTwoJetEval xSeries ySeries hrelation) := by
    rw [pointIdeal, Ideal.span_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hx
    · exact hy
  have hpow : pointIdeal x y ^ 2 ≤
      ((InfinityCoordinateRing.truncatedJetDirectionIdeal 2).comap
        (affineTwoJetEval xSeries ySeries hrelation)) ^ 2 :=
    Ideal.pow_right_mono hm 2
  have hcomap := Ideal.le_comap_pow
    (affineTwoJetEval xSeries ySeries hrelation)
    (K := InfinityCoordinateRing.truncatedJetDirectionIdeal 2) 2
  intro u hu
  have hu' := hcomap (hpow hu)
  have hzero : affineTwoJetEval xSeries ySeries hrelation u = 0 := by
    have : affineTwoJetEval xSeries ySeries hrelation u ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2 ^ 2 := hu'
    rw [InfinityCoordinateRing.truncatedJetDirectionIdeal_pow_eq_bot]
      at this
    exact Ideal.mem_bot.mp this
  exact RingHom.mem_ker.mpr hzero

theorem cuspZeroPositivePointIdeal_sq_le_twoJet_ker :
    pointIdeal 0 1 ^ 2 ≤ RingHom.ker cuspZeroPositiveTwoJetEval := by
  apply pointIdeal_sq_le_affineTwoJetEval_ker 0 1
      cuspZeroPositiveXSeries cuspZeroPositiveYSeries
      cuspZeroPositiveTwoJet_relation_mem
  · rw [xClass, affineTwoJetEval_algebraMap]
    have hX : twoJetMk X ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2 := by
      rw [InfinityCoordinateRing.truncatedJetDirectionIdeal]
      exact Ideal.subset_span (by simp)
    simpa [cuspZeroPositiveXSeries] using hX
  · rw [yClass, map_sub, affineTwoJetEval_yCoordinate,
      affineTwoJetEval_algebraMap]
    change twoJetMk cuspZeroPositiveYSeries -
      twoJetMk ((C 1).comp cuspZeroPositiveXSeries) ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2
    rw [← map_sub]
    have hX : twoJetMk X ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2 := by
      rw [InfinityCoordinateRing.truncatedJetDirectionIdeal]
      exact Ideal.subset_span (by simp)
    have hmem : (2 : TwoJetRing) * twoJetMk X ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2 :=
      (InfinityCoordinateRing.truncatedJetDirectionIdeal 2).mul_mem_left 2
        hX
    simpa [cuspZeroPositiveXSeries, cuspZeroPositiveYSeries,
      map_ofNat] using hmem

theorem cuspNegOnePositivePointIdeal_sq_le_twoJet_ker :
    pointIdeal (-1) 1 ^ 2 ≤ RingHom.ker cuspNegOnePositiveTwoJetEval := by
  apply pointIdeal_sq_le_affineTwoJetEval_ker (-1) 1
      cuspNegOnePositiveXSeries cuspNegOnePositiveYSeries
      cuspNegOnePositiveTwoJet_relation_mem
  · rw [xClass, affineTwoJetEval_algebraMap]
    have hX : twoJetMk X ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2 := by
      rw [InfinityCoordinateRing.truncatedJetDirectionIdeal]
      exact Ideal.subset_span (by simp)
    simpa [cuspNegOnePositiveXSeries] using hX
  · rw [yClass, map_sub, affineTwoJetEval_yCoordinate,
      affineTwoJetEval_algebraMap]
    change twoJetMk cuspNegOnePositiveYSeries -
      twoJetMk ((C 1).comp cuspNegOnePositiveXSeries) ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2
    rw [← map_sub]
    have hX : twoJetMk X ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2 := by
      rw [InfinityCoordinateRing.truncatedJetDirectionIdeal]
      exact Ideal.subset_span (by simp)
    have hmem : -twoJetMk X ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2 :=
      (InfinityCoordinateRing.truncatedJetDirectionIdeal 2).neg_mem
        hX
    simpa [cuspNegOnePositiveXSeries, cuspNegOnePositiveYSeries] using hmem

private theorem twoJetMk_X_ne_zero : twoJetMk X ≠ 0 := by
  simpa using
    (InfinityCoordinateRing.truncatedJetMk_X_pow_ne_zero
      (n := 2) (k := 1) (by norm_num))

theorem haoW_not_mem_cuspZeroPositivePointIdeal_sq :
    haoW ∉ pointIdeal 0 1 ^ 2 := by
  intro hmem
  have hzero := RingHom.mem_ker.mp
    (cuspZeroPositivePointIdeal_sq_le_twoJet_ker hmem)
  rw [cuspZeroPositiveTwoJetEval_haoW] at hzero
  exact twoJetMk_X_ne_zero hzero

theorem haoW_not_mem_cuspNegOnePositivePointIdeal_sq :
    haoW ∉ pointIdeal (-1) 1 ^ 2 := by
  intro hmem
  have hzero := RingHom.mem_ker.mp
    (cuspNegOnePositivePointIdeal_sq_le_twoJet_ker hmem)
  rw [cuspNegOnePositiveTwoJetEval_haoW] at hzero
  exact twoJetMk_X_ne_zero (neg_eq_zero.mp hzero)

theorem haoW_mem_cuspZeroPositivePointIdeal :
    haoW ∈ pointIdeal 0 1 := by
  rw [← pointEval_ker 0 1 cuspZeroPositive_isAffinePoint]
  apply RingHom.mem_ker.mpr
  norm_num [haoW, halfClass, ordinateClass, haoPolynomial]

private theorem cuspNegOnePositive_isAffinePoint :
    IsAffinePoint (-1) 1 := by
  norm_num [IsAffinePoint, sexticPolynomial]

theorem haoW_mem_cuspNegOnePositivePointIdeal :
    haoW ∈ pointIdeal (-1) 1 := by
  rw [← pointEval_ker (-1) 1 cuspNegOnePositive_isAffinePoint]
  apply RingHom.mem_ker.mpr
  norm_num [haoW, halfClass, ordinateClass, haoPolynomial]

theorem haoW_exactOrder_cuspZeroPositive :
    HasExactIdealOrder (pointIdeal 0 1) haoW 1 := by
  exact ⟨by simpa only [pow_one] using haoW_mem_cuspZeroPositivePointIdeal,
    by simpa only [Nat.reduceAdd] using
      haoW_not_mem_cuspZeroPositivePointIdeal_sq⟩

theorem haoW_exactOrder_cuspNegOnePositive :
    HasExactIdealOrder (pointIdeal (-1) 1) haoW 1 := by
  exact ⟨by simpa only [pow_one] using haoW_mem_cuspNegOnePositivePointIdeal,
    by simpa only [Nat.reduceAdd] using
      haoW_not_mem_cuspNegOnePositivePointIdeal_sq⟩

/-! ## The chart parameter has exact order one at both infinities -/

theorem tCoordinate_mem_positiveInfinityIdeal :
    InfinityCoordinateRing.tCoordinate ∈
      InfinityCoordinateRing.positiveInfinityIdeal := by
  rw [InfinityCoordinateRing.positiveInfinityIdeal_eq]
  exact Ideal.subset_span (by simp)

theorem tCoordinate_not_mem_positiveInfinityIdeal_sq :
    InfinityCoordinateRing.tCoordinate ∉
      InfinityCoordinateRing.positiveInfinityIdeal ^ 2 := by
  intro hmem
  have hker :=
    InfinityCoordinateRing.positiveInfinityIdeal_pow_le_positiveJetEval_ker
      2 InfinityCoordinateRing.positiveJetRelation_mem_two hmem
  have hzero := RingHom.mem_ker.mp hker
  rw [InfinityCoordinateRing.positiveJetEval_tCoordinate] at hzero
  exact twoJetMk_X_ne_zero hzero

/-- The first-order expansion `z=-1-T` at the negative infinity branch. -/
def negativeInfinityTwoJetSeries : ℚ[X] := -1 - X

theorem negativeInfinityTwoJet_relation_mem :
    negativeInfinityTwoJetSeries ^ 2 - infinitySexticPolynomial ∈
      InfinityCoordinateRing.truncatedJetIdeal 2 := by
  rw [InfinityCoordinateRing.truncatedJetIdeal,
    Ideal.mem_span_singleton]
  refine ⟨-(2 * X + 6 * X ^ 2 + 4 * X ^ 3 + X ^ 4), ?_⟩
  simp [negativeInfinityTwoJetSeries, infinitySexticPolynomial]
  ring

/-- The dual-number jet of the negative infinity branch. -/
def negativeInfinityTwoJetEval :
    InfinityCoordinateRing →+* TwoJetRing :=
  AdjoinRoot.lift twoJetMk (twoJetMk negativeInfinityTwoJetSeries) (by
    have hzero : twoJetMk
        (negativeInfinityTwoJetSeries ^ 2 -
          infinitySexticPolynomial) = 0 := by
      change Ideal.Quotient.mk
        (InfinityCoordinateRing.truncatedJetIdeal 2)
          (negativeInfinityTwoJetSeries ^ 2 -
            infinitySexticPolynomial) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        negativeInfinityTwoJet_relation_mem
    simpa only [infinityRelationPolynomial, eval₂_sub, eval₂_pow,
      eval₂_X, eval₂_C, map_sub, map_pow] using hzero)

@[simp] theorem negativeInfinityTwoJetEval_zCoordinate :
    negativeInfinityTwoJetEval InfinityCoordinateRing.zCoordinate =
      twoJetMk negativeInfinityTwoJetSeries := by
  exact AdjoinRoot.lift_root _

@[simp] theorem negativeInfinityTwoJetEval_algebraMap (p : ℚ[X]) :
    negativeInfinityTwoJetEval
        (algebraMap ℚ[X] InfinityCoordinateRing p) = twoJetMk p := by
  exact AdjoinRoot.lift_of _

@[simp] theorem negativeInfinityTwoJetEval_tCoordinate :
    negativeInfinityTwoJetEval InfinityCoordinateRing.tCoordinate =
      twoJetMk X := by
  exact negativeInfinityTwoJetEval_algebraMap X

theorem negativeInfinityIdeal_sq_le_twoJet_ker :
    InfinityCoordinateRing.negativeInfinityIdeal ^ 2 ≤
      RingHom.ker negativeInfinityTwoJetEval := by
  have hm : InfinityCoordinateRing.negativeInfinityIdeal ≤
      (InfinityCoordinateRing.truncatedJetDirectionIdeal 2).comap
        negativeInfinityTwoJetEval := by
    rw [InfinityCoordinateRing.negativeInfinityIdeal_eq,
      Ideal.span_le]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · change negativeInfinityTwoJetEval
        InfinityCoordinateRing.tCoordinate ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2
      rw [negativeInfinityTwoJetEval_tCoordinate]
      rw [InfinityCoordinateRing.truncatedJetDirectionIdeal]
      exact Ideal.subset_span (by simp)
    · change negativeInfinityTwoJetEval
        (InfinityCoordinateRing.zCoordinate + 1) ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2
      rw [map_add, negativeInfinityTwoJetEval_zCoordinate, map_one]
      have hX : twoJetMk X ∈
          InfinityCoordinateRing.truncatedJetDirectionIdeal 2 := by
        rw [InfinityCoordinateRing.truncatedJetDirectionIdeal]
        exact Ideal.subset_span (by simp)
      have heq : twoJetMk negativeInfinityTwoJetSeries + 1 =
          -twoJetMk X := by
        rw [← map_one twoJetMk, ← map_add, ← map_neg]
        congr 1
        simp [negativeInfinityTwoJetSeries]
        ring
      rw [heq]
      exact
        (InfinityCoordinateRing.truncatedJetDirectionIdeal 2).neg_mem hX
  have hpow : InfinityCoordinateRing.negativeInfinityIdeal ^ 2 ≤
      ((InfinityCoordinateRing.truncatedJetDirectionIdeal 2).comap
        negativeInfinityTwoJetEval) ^ 2 :=
    Ideal.pow_right_mono hm 2
  have hcomap := Ideal.le_comap_pow negativeInfinityTwoJetEval
    (K := InfinityCoordinateRing.truncatedJetDirectionIdeal 2) 2
  intro u hu
  have hu' := hcomap (hpow hu)
  have hzero : negativeInfinityTwoJetEval u = 0 := by
    have : negativeInfinityTwoJetEval u ∈
        InfinityCoordinateRing.truncatedJetDirectionIdeal 2 ^ 2 := hu'
    rw [InfinityCoordinateRing.truncatedJetDirectionIdeal_pow_eq_bot]
      at this
    exact Ideal.mem_bot.mp this
  exact RingHom.mem_ker.mpr hzero

theorem tCoordinate_mem_negativeInfinityIdeal :
    InfinityCoordinateRing.tCoordinate ∈
      InfinityCoordinateRing.negativeInfinityIdeal := by
  rw [InfinityCoordinateRing.negativeInfinityIdeal_eq]
  exact Ideal.subset_span (by simp)

theorem tCoordinate_not_mem_negativeInfinityIdeal_sq :
    InfinityCoordinateRing.tCoordinate ∉
      InfinityCoordinateRing.negativeInfinityIdeal ^ 2 := by
  intro hmem
  have hzero := RingHom.mem_ker.mp
    (negativeInfinityIdeal_sq_le_twoJet_ker hmem)
  rw [negativeInfinityTwoJetEval_tCoordinate] at hzero
  exact twoJetMk_X_ne_zero hzero

theorem tCoordinate_exactOrder_positiveInfinity :
    HasExactIdealOrder InfinityCoordinateRing.positiveInfinityIdeal
      InfinityCoordinateRing.tCoordinate 1 := by
  exact ⟨by simpa only [pow_one] using
      tCoordinate_mem_positiveInfinityIdeal,
    by simpa only [Nat.reduceAdd] using
      tCoordinate_not_mem_positiveInfinityIdeal_sq⟩

theorem tCoordinate_exactOrder_negativeInfinity :
    HasExactIdealOrder InfinityCoordinateRing.negativeInfinityIdeal
      InfinityCoordinateRing.tCoordinate 1 := by
  exact ⟨by simpa only [pow_one] using
      tCoordinate_mem_negativeInfinityIdeal,
    by simpa only [Nat.reduceAdd] using
      tCoordinate_not_mem_negativeInfinityIdeal_sq⟩

theorem infinityHaoNumerator_exactOrder_positiveInfinity :
    HasExactIdealOrder InfinityCoordinateRing.positiveInfinityIdeal
      InfinityCoordinateRing.infinityHaoNumerator 4 := by
  exact ⟨
    InfinityCoordinateRing.infinityHaoNumerator_mem_positiveInfinityIdeal_fourth,
    by simpa only [Nat.reduceAdd] using
      InfinityCoordinateRing.infinityHaoNumerator_not_mem_positiveInfinityIdeal_fifth⟩

theorem infinityHaoNumerator_exactOrder_negativeInfinity :
    HasExactIdealOrder InfinityCoordinateRing.negativeInfinityIdeal
      InfinityCoordinateRing.infinityHaoNumerator 0 := by
  constructor
  · simp
  · simpa only [Nat.reduceAdd, pow_one] using
      InfinityCoordinateRing.infinityHaoNumerator_not_mem_negativeInfinityIdeal

/-! ## The affine divisor and its existing affine class -/

/-- The affine cusp `(-1,1)` as a bundled rational point. -/
def cuspNegOnePositivePoint : RationalAffinePoint :=
  ⟨(-1, 1), cuspNegOnePositive_isAffinePoint⟩

/-- The two simple affine zeros of Hao's function. -/
def haoWAffineZeroDivisor : RationalAffineDivisor :=
  Finsupp.single cuspZeroPositivePoint 1 +
    Finsupp.single cuspNegOnePositivePoint 1

/-- The affine divisor class vanishes, as already implied by the exact
principal-ideal factorization.  The projective relation below refines this by
remembering both infinity branches. -/
theorem rationalAffineDivisorClass_haoWAffineZeroDivisor :
    rationalAffineDivisorClass haoWAffineZeroDivisor = 0 := by
  have hmul := cuspZeroClass_mul_cuspNegOneClass_eq_one
  have hadd := congrArg Additive.ofMul hmul
  simpa [haoWAffineZeroDivisor, rationalAffinePointClass,
    cuspZeroPositivePoint, cuspNegOnePositivePoint,
    cuspZeroClass, cuspNegOneClass] using hadd

/-! ## Raw six-cusp divisors and the canonical Mazur--Tate coordinates -/

/-- The six rational cusps occurring in the explicit projective model. -/
inductive ProjectiveCusp where
  | infinityPositive
  | infinityNegative
  | zeroPositive
  | zeroNegative
  | negOnePositive
  | negOneNegative
  deriving DecidableEq

/-- The free abelian group of divisors supported on the six rational cusps. -/
abbrev ProjectiveCuspDivisor := ProjectiveCusp →₀ ℤ

/-- A basis cusp divisor. -/
def cuspDivisor (P : ProjectiveCusp) : ProjectiveCuspDivisor :=
  Finsupp.single P 1

/-- The raw projective divisor certified for Hao's function. -/
def haoWProjectiveDivisor : ProjectiveCuspDivisor :=
  cuspDivisor .zeroPositive + cuspDivisor .negOnePositive +
    cuspDivisor .infinityPositive - 3 • cuspDivisor .infinityNegative

/-- The same divisor written directly from the checked numerator orders and
the third power of the local parameter in `t³w`. -/
def haoWDivisorFromOrderExponents : ProjectiveCuspDivisor :=
  cuspDivisor .zeroPositive + cuspDivisor .negOnePositive +
    ((4 : ℤ) - 3 * 1) • cuspDivisor .infinityPositive +
    ((0 : ℤ) - 3 * 1) • cuspDivisor .infinityNegative

theorem haoWDivisorFromOrderExponents_eq_projectiveDivisor :
    haoWDivisorFromOrderExponents = haoWProjectiveDivisor := by
  simp [haoWDivisorFromOrderExponents, haoWProjectiveDivisor]
  abel

open XOneThirteenUniversalCuspRelationGroup

/-- Expand the five degree-zero Mazur--Tate generators into raw six-cusp
divisors.  Here `D=∞⁻-∞⁺`, while the other four generators are affine cusps
based at `∞⁺`. -/
def generatorProjectiveCuspDivisor :
    CuspGenerator → ProjectiveCuspDivisor :=
  ![cuspDivisor .infinityNegative - cuspDivisor .infinityPositive,
    cuspDivisor .zeroPositive - cuspDivisor .infinityPositive,
    cuspDivisor .zeroNegative - cuspDivisor .infinityPositive,
    cuspDivisor .negOnePositive - cuspDivisor .infinityPositive,
    cuspDivisor .negOneNegative - cuspDivisor .infinityPositive]

/-- The additive expansion from the canonical five-generator presentation to
raw six-cusp divisors. -/
def freeCuspToProjectiveDivisor :
    FreeCuspGroup →+ ProjectiveCuspDivisor :=
  Finsupp.liftAddHom fun i =>
    zmultiplesHom ProjectiveCuspDivisor
      (generatorProjectiveCuspDivisor i)

@[simp] theorem freeCuspToProjectiveDivisor_freeGenerator
    (i : CuspGenerator) :
    freeCuspToProjectiveDivisor (freeGenerator i) =
      generatorProjectiveCuspDivisor i := by
  simp [freeCuspToProjectiveDivisor, freeGenerator]

/-- The first canonical relation vector expands to the raw divisor computed
from the affine and infinity orders. -/
theorem relationVector_zero_expands_to_haoWProjectiveDivisor :
    freeCuspToProjectiveDivisor (relationVector 0) =
      haoWProjectiveDivisor := by
  ext P
  cases P <;>
    simp [relationVector, freeA, freeB, freeD,
      generatorProjectiveCuspDivisor, haoWProjectiveDivisor,
      cuspDivisor]

/-! ## The complete checked principal-divisor certificate -/

/-- All exact interfaces needed to interpret the displayed raw divisor as the
principal divisor of `w`.  The affine factorization is an equality of ideals,
not a UFD or Dedekind-domain inference; every local order is separately
certified by ideal-power membership and nonmembership. -/
structure HaoWPrincipalDivisorCertificate : Prop where
  affineFactorization :
    Ideal.span {haoW} = pointIdeal 0 1 * pointIdeal (-1) 1
  affineOrderZeroPositive :
    HasExactIdealOrder (pointIdeal 0 1) haoW 1
  affineOrderNegOnePositive :
    HasExactIdealOrder (pointIdeal (-1) 1) haoW 1
  parameterOrderPositiveInfinity :
    HasExactIdealOrder InfinityCoordinateRing.positiveInfinityIdeal
      InfinityCoordinateRing.tCoordinate 1
  parameterOrderNegativeInfinity :
    HasExactIdealOrder InfinityCoordinateRing.negativeInfinityIdeal
      InfinityCoordinateRing.tCoordinate 1
  numeratorOrderPositiveInfinity :
    HasExactIdealOrder InfinityCoordinateRing.positiveInfinityIdeal
      InfinityCoordinateRing.infinityHaoNumerator 4
  numeratorOrderNegativeInfinity :
    HasExactIdealOrder InfinityCoordinateRing.negativeInfinityIdeal
      InfinityCoordinateRing.infinityHaoNumerator 0
  positiveInfinityCoefficient : (4 : ℤ) - 3 * 1 = 1
  negativeInfinityCoefficient : (0 : ℤ) - 3 * 1 = -3
  reciprocalIdentity :
    ∀ (t z : ℚ), t ≠ 0 →
      (z - InfinityCoordinateRing.infinityHaoPolynomial.eval t) / 2 =
        t ^ 3 *
          ((z / t ^ 3 - haoPolynomial.eval (1 / t)) / 2)

/-- The fully checked certificate for the divisor of Hao's function. -/
theorem haoWPrincipalDivisorCertificate :
    HaoWPrincipalDivisorCertificate where
  affineFactorization := span_haoW_eq_cuspPointIdealProduct
  affineOrderZeroPositive := haoW_exactOrder_cuspZeroPositive
  affineOrderNegOnePositive := haoW_exactOrder_cuspNegOnePositive
  parameterOrderPositiveInfinity :=
    tCoordinate_exactOrder_positiveInfinity
  parameterOrderNegativeInfinity :=
    tCoordinate_exactOrder_negativeInfinity
  numeratorOrderPositiveInfinity :=
    infinityHaoNumerator_exactOrder_positiveInfinity
  numeratorOrderNegativeInfinity :=
    infinityHaoNumerator_exactOrder_negativeInfinity
  positiveInfinityCoefficient := by norm_num
  negativeInfinityCoefficient := by norm_num
  reciprocalIdentity := fun t z ht =>
    InfinityCoordinateRing.infinityHaoNumerator_eq_reciprocal t z ht

/-- A raw six-cusp divisor is certified principal when it is the displayed
divisor and carries the complete checked Hao-function certificate. -/
def IsCertifiedHaoWPrincipalDivisor
    (E : ProjectiveCuspDivisor) : Prop :=
  E = haoWDivisorFromOrderExponents ∧ HaoWPrincipalDivisorCertificate

theorem haoWProjectiveDivisor_isCertified :
    IsCertifiedHaoWPrincipalDivisor haoWProjectiveDivisor :=
  ⟨haoWDivisorFromOrderExponents_eq_projectiveDivisor.symm,
    haoWPrincipalDivisorCertificate⟩

/-- A canonical free-cusp relation is accepted only when it is the first
Mazur--Tate row, expands to the certified raw divisor, and carries the complete
local certificate. -/
def IsCertifiedHaoWRelation (r : FreeCuspGroup) : Prop :=
  r = relationVector 0 ∧
    IsCertifiedHaoWPrincipalDivisor
      (freeCuspToProjectiveDivisor r)

theorem relationVector_zero_isCertifiedHaoWRelation :
    IsCertifiedHaoWRelation (relationVector 0) := by
  refine ⟨rfl, ?_⟩
  rw [relationVector_zero_expands_to_haoWProjectiveDivisor]
  exact haoWProjectiveDivisor_isCertified

/-- The subgroup generated only by relations with a checked Hao divisor
certificate. -/
def certifiedHaoWRelationSubgroup : AddSubgroup FreeCuspGroup :=
  AddSubgroup.closure {r | IsCertifiedHaoWRelation r}

/-- The curve-specific one-relation cusp-class quotient.  It is intentionally
not asserted to be the full projective Picard group. -/
abbrev CertifiedHaoWCuspClassGroup :=
  FreeCuspGroup ⧸ certifiedHaoWRelationSubgroup

/-- The class of a canonical free cusp generator in the certified quotient. -/
def certifiedGeneratorClass (i : CuspGenerator) :
    CertifiedHaoWCuspClassGroup :=
  (freeGenerator i : CertifiedHaoWCuspClassGroup)

def certifiedD : CertifiedHaoWCuspClassGroup := certifiedGeneratorClass 0
def certifiedA : CertifiedHaoWCuspClassGroup := certifiedGeneratorClass 1
def certifiedAbar : CertifiedHaoWCuspClassGroup := certifiedGeneratorClass 2
def certifiedB : CertifiedHaoWCuspClassGroup := certifiedGeneratorClass 3
def certifiedC : CertifiedHaoWCuspClassGroup := certifiedGeneratorClass 4

theorem relationVector_zero_mem_certifiedHaoWRelationSubgroup :
    relationVector 0 ∈ certifiedHaoWRelationSubgroup :=
  AddSubgroup.subset_closure relationVector_zero_isCertifiedHaoWRelation

/-- First genuine projective cusp-class consumer: the checked divisor of `w`
gives the Mazur--Tate relation `A+B=3D`. -/
theorem haoW_certified_projective_cusp_relation :
    certifiedA + certifiedB = 3 • certifiedD := by
  change ((freeA + freeB : FreeCuspGroup) :
      CertifiedHaoWCuspClassGroup) =
    ((3 • freeD : FreeCuspGroup) : CertifiedHaoWCuspClassGroup)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa [relationVector] using
    relationVector_zero_mem_certifiedHaoWRelationSubgroup

/-- The certified relation subgroup maps into the existing universal
Mazur--Tate relation subgroup, so the new relation is a literal checked input
to the downstream `ZMod 19` presentation. -/
theorem certifiedHaoWRelationSubgroup_le_relationSubgroup :
    certifiedHaoWRelationSubgroup ≤ relationSubgroup := by
  rw [certifiedHaoWRelationSubgroup, AddSubgroup.closure_le]
  intro r hr
  rcases hr with ⟨rfl, _⟩
  exact relationVector_mem 0

theorem certifiedHaoWRelationSubgroup_le_universalQuotient_ker :
    certifiedHaoWRelationSubgroup ≤
      (QuotientAddGroup.mk' relationSubgroup).ker := by
  intro r hr
  rw [AddMonoidHom.mem_ker, QuotientAddGroup.eq_zero_iff]
  exact certifiedHaoWRelationSubgroup_le_relationSubgroup hr

/-- Forgetting that only the Hao relation has been certified maps the
curve-specific quotient to the existing five-relation universal
Mazur--Tate presentation. -/
def certifiedHaoWToUniversalCuspRelationGroup :
    CertifiedHaoWCuspClassGroup →+
      UniversalCuspRelationGroup :=
  QuotientAddGroup.lift certifiedHaoWRelationSubgroup
    (QuotientAddGroup.mk' relationSubgroup)
    certifiedHaoWRelationSubgroup_le_universalQuotient_ker

@[simp] theorem certifiedHaoWToUniversalCuspRelationGroup_generator
    (i : CuspGenerator) :
    certifiedHaoWToUniversalCuspRelationGroup
        (certifiedGeneratorClass i) = generatorClass i := by
  rfl

/-- Downstream theorem in the canonical group used by the Mazur--Tate
`ZMod 19` computation, now derived from the geometric certificate rather than
from the formal presentation alone. -/
theorem haoW_relation_in_universalCuspRelationGroup_from_certificate :
    A + B = 3 • D := by
  have h := congrArg certifiedHaoWToUniversalCuspRelationGroup
    haoW_certified_projective_cusp_relation
  simpa [certifiedA, certifiedB, certifiedD, A, B, D] using h

end

end MazurTorsion.XOneThirteenHaoWProjectiveDivisor
