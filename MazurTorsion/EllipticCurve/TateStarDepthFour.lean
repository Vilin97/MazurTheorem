/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TateStarRepeatedRoot

/-!
# Exact depth four on the marked exceptional branch

On the marked exceptional-cubic branch, suppose the same integral point and short equation have
`x,y ∈ 𝔪²`, `a₄ ∈ 𝔪³`, and `a₆ ∉ 𝔪⁵`.  The equation forces `a₆ ∈ 𝔪⁴`, and this file proves that
the triple of that marked point has canonical nonsingular reduction.

The proof is entirely on the selected Weierstrass equation.  It follows the tangent and secant
formulas, separates slopes with a pole from integral-unit slopes, and handles equal-abscissa and
vertical cases in the group law explicitly.  It does not name a Kodaira symbol or construct a
regular model, strict transform, component group, or component-cardinality bound.
-/

noncomputable section

open IsLocalRing

namespace MazurTorsion.EllipticCurve

open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

universe u v

/-- Coordinate form of the depth-four tangent-and-secant calculation.  Splitting this calculation
from the coefficient-depth argument keeps both checked declarations within Lean's deterministic
elaboration budget. -/
private theorem three_nsmul_mem_nonsingularReductionSubgroup_of_coordinate_depths
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    {x y : v.adicCompletion K} (hxy : W.Nonsingular x y)
    (hxint : Valued.v x ≤ 1) (hyint : Valued.v y ≤ 1)
    (hxsq : (⟨x, hxint⟩ : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (hysq : (⟨y, hyint⟩ : v.adicCompletionIntegers K) ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₄cube : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3)
    (hyval : Valued.v y = exp (-2 : ℤ)) (hyne : y ≠ 0) :
    3 • (.some x y hxy : W.Point) ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  let H := nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)
  let x₀ : v.adicCompletionIntegers K := ⟨x, hxint⟩
  let y₀ : v.adicCompletionIntegers K := ⟨y, hyint⟩
  have hxsq' : x₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 := by
    simpa [x₀] using hxsq
  have hysq' : y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 := by
    simpa [y₀] using hysq
  have hxmax : x₀ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)) hxsq'
  have hymax : y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)) hysq'
  have hreszero : residue (v.adicCompletionIntegers K) x₀ = 0 ∧
      residue (v.adicCompletionIntegers K) y₀ = 0 :=
    ⟨(residue_eq_zero_iff x₀).mpr hxmax,
      (residue_eq_zero_iff y₀).mpr hymax⟩
  letI : Invertible (2 : ResidueField (v.adicCompletionIntegers K)) :=
    invertibleOfNonzero h2
  letI : Invertible (3 : ResidueField (v.adicCompletionIntegers K)) :=
    invertibleOfNonzero h3
  have ha₁ : W.a₁ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₁, W₀.a₁_of_isShortNF, map_zero]
  have ha₂ : W.a₂ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₂, W₀.a₂_of_isShortNF, map_zero]
  have ha₃ : W.a₃ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₃, W₀.a₃_of_isShortNF, map_zero]
  have ha₄coe : ((W₀.a₄ : v.adicCompletionIntegers K) :
      v.adicCompletion K) = W.a₄ := by
    rw [← hW, WeierstrassCurve.map_a₄]
    rfl
  let n₀ : v.adicCompletionIntegers K := 3 * x₀ ^ 2 + W₀.a₄
  have hn₀mem : n₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
    have hx4 : x₀ ^ 2 ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 4 := by
      rw [pow_two]
      exact pow_add (maximalIdeal (v.adicCompletionIntegers K)) 2 2 ▸
        Ideal.mul_mem_mul hxsq' hxsq'
    have hx3 : x₀ ^ 2 ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3 :=
      (Ideal.pow_le_pow_right (by norm_num : 3 ≤ 4)) hx4
    have h3x2 : 3 * x₀ ^ 2 ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 3 :=
      Ideal.mul_mem_left _ 3 hx3
    exact Ideal.add_mem _ h3x2 ha₄cube
  have hn₀coe : ((n₀ : v.adicCompletionIntegers K) : v.adicCompletion K) =
      3 * x ^ 2 + W.a₄ := by
    change 3 * x ^ 2 + ((W₀.a₄ : v.adicCompletionIntegers K) :
      v.adicCompletion K) = _
    rw [ha₄coe]
  have hnumle : Valued.v (3 * x ^ 2 + W.a₄) ≤ exp (-3 : ℤ) := by
    rw [← hn₀coe]
    simpa [n₀] using
      (v.mem_maximalIdeal_pow_iff (K := K) (x := n₀) (n := 3)).mp hn₀mem
  have htwoUnit : IsUnit (2 : v.adicCompletionIntegers K) :=
    (residue_ne_zero_iff_isUnit (2 : v.adicCompletionIntegers K)).mp (by
      simpa only [map_ofNat] using h2)
  have htwoval : Valued.v (2 : v.adicCompletion K) = 1 := by
    change Valued.v (((2 : v.adicCompletionIntegers K) :
      v.adicCompletion K)) = 1
    exact (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp
      htwoUnit
  have hyneg : y ≠ W.negY x y := by
    intro h
    rw [WeierstrassCurve.Affine.negY, ha₁, ha₃] at h
    have hzero : 2 * y = 0 := by linear_combination h
    have htwo_ne : (2 : v.adicCompletion K) ≠ 0 := by
      intro hzero'
      have h := htwoval
      rw [hzero', map_zero] at h
      exact zero_ne_one h
    exact hyne ((mul_eq_zero.mp hzero).resolve_left htwo_ne)
  have hslope : W.slope x x y y = (3 * x ^ 2 + W.a₄) / (2 * y) := by
    rw [W.slope_of_Y_ne rfl hyneg, ha₁, ha₂]
    simp only [zero_mul, sub_zero]
    rw [WeierstrassCurve.Affine.negY, ha₁, ha₃]
    ring
  have hslopele : Valued.v (W.slope x x y y) ≤ exp (-1 : ℤ) := by
    rw [hslope, map_div₀, map_mul, htwoval, one_mul, hyval]
    by_cases hnzero : 3 * x ^ 2 + W.a₄ = 0
    · rw [hnzero, map_zero, zero_div]
      exact bot_le
    · obtain ⟨dn, hdn⟩ : ∃ dn : ℤ,
          Valued.v (3 * x ^ 2 + W.a₄) = exp dn :=
        ⟨_, (exp_log ((Valued.v).pos_iff.mpr hnzero).ne').symm⟩
      have hdnle : dn ≤ -3 := by rwa [hdn, exp_le_exp] at hnumle
      rw [hdn, ← exp_sub, exp_le_exp]
      omega
  let L : v.adicCompletionIntegers K :=
    ⟨W.slope x x y y, hslopele.trans (by
      rw [← exp_zero, exp_le_exp]
      omega)⟩
  have hLmax : L ∈ maximalIdeal (v.adicCompletionIntegers K) := by
    simpa only [pow_one] using
      (v.mem_maximalIdeal_pow_iff (K := K) (x := L) (n := 1)).mpr
        (by simpa [L] using hslopele)
  let X₂ : v.adicCompletionIntegers K := L ^ 2 - 2 * x₀
  let Y₂ : v.adicCompletionIntegers K := L * (x₀ - X₂) - y₀
  have hX₂ : ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
      W.addX x x (W.slope x x y y) := by
    change (W.slope x x y y) ^ 2 - 2 * x =
      W.addX x x (W.slope x x y y)
    rw [WeierstrassCurve.Affine.addX, ha₁, ha₂]
    ring
  have hY₂ : ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
      W.addY x x y (W.slope x x y y) := by
    change W.slope x x y y * (x - (X₂ : v.adicCompletion K)) - y =
      W.addY x x y (W.slope x x y y)
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY, ha₁, ha₃, hX₂]
    ring
  have hdoubleNot : ¬(x = x ∧ y = W.negY x y) := fun h ↦ hyneg h.2
  have hdouble : W.Nonsingular
      (W.addX x x (W.slope x x y y))
      (W.addY x x y (W.slope x x y y)) :=
    W.nonsingular_add hxy hxy hdoubleNot
  have hdouble' : W.Nonsingular
      ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
      ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) := by
    rw [hX₂, hY₂]
    exact hdouble
  have hdoublePoint :
      (.some x y hxy : W.Point) + .some x y hxy =
        .some ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
          ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) hdouble' := by
    rw [Point.add_some hdoubleNot, Point.some.injEq]
    exact ⟨hX₂.symm, hY₂.symm⟩
  have hLres : residue (v.adicCompletionIntegers K) L = 0 :=
    (residue_eq_zero_iff L).mpr hLmax
  have hLsq : L ^ 2 ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hLmax hLmax
  have htwoxsq : 2 * x₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 :=
    Ideal.mul_mem_left _ 2 hxsq'
  have hX₂sq : X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 :=
    Ideal.sub_mem _ hLsq htwoxsq
  have hX₂res : residue (v.adicCompletionIntegers K) X₂ = 0 := by
    simp [X₂, hLres, hreszero.1]
  have hY₂res : residue (v.adicCompletionIntegers K) Y₂ = 0 := by
    simp [Y₂, hLres, hreszero.2]
  have hX₂max : X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (residue_eq_zero_iff X₂).mp hX₂res
  have hY₂max : Y₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (residue_eq_zero_iff Y₂).mp hY₂res
  have hcorr : Y₂ + y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
    have hdiff : x₀ - X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 :=
      Ideal.sub_mem _ hxsq' hX₂sq
    have hmul := Ideal.mul_mem_mul hLmax hdiff
    have hid : Y₂ + y₀ = L * (x₀ - X₂) := by simp [Y₂]
    rw [hid]
    simpa [pow_succ, pow_two, mul_assoc] using hmul
  have hcorrval : Valued.v
      (((Y₂ + y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
        exp (-3 : ℤ) :=
    (v.mem_maximalIdeal_pow_iff (K := K) (x := Y₂ + y₀) (n := 3)).mp hcorr
  have htwoyval : Valued.v (2 * y) = exp (-2 : ℤ) := by
    rw [map_mul, htwoval, one_mul, hyval]
  have hcorrlt : Valued.v
      (((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) + y) <
        Valued.v (2 * y) := by
    change Valued.v (((Y₂ + y₀ : v.adicCompletionIntegers K) :
      v.adicCompletion K)) < Valued.v (2 * y)
    rw [htwoyval]
    exact lt_of_le_of_lt hcorrval (exp_lt_exp.mpr (by norm_num))
  have hsecnum : Valued.v
      (y - ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) =
        exp (-2 : ℤ) := by
    rw [show y - ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
      2 * y - (((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) + y) by ring,
      Valuation.map_sub_eq_of_lt_left _ hcorrlt, htwoyval]
  have hthreePoint : 3 • (.some x y hxy : W.Point) =
      (.some x y hxy : W.Point) +
        .some ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
          ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) hdouble' := by
    calc
      3 • (.some x y hxy : W.Point) =
          (.some x y hxy : W.Point) + (.some x y hxy + .some x y hxy) := by
        rw [show 3 = 1 + 2 by norm_num, add_nsmul, one_nsmul, two_nsmul]
      _ = _ := by rw [hdoublePoint]
  rw [hthreePoint]
  by_cases hxx : x = ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
  · rcases W.Y_eq_of_X_eq hxy.left hdouble'.left hxx with hySame | hyAnti
    · have hpEq : (.some x y hxy : W.Point) =
          .some ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
            ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) hdouble' := by
        rw [Point.some.injEq]
        exact ⟨hxx, hySame⟩
      have hidem : (.some x y hxy : W.Point) + .some x y hxy =
          .some x y hxy := hdoublePoint.trans hpEq.symm
      have hz : (.some x y hxy : W.Point) = 0 := by
        have := congrArg (fun Q : W.Point ↦ Q - .some x y hxy) hidem
        simpa only [add_sub_cancel_right, sub_self] using this
      exact (Point.some_ne_zero hxy hz).elim
    · rw [Point.add_of_Y_eq hxx hyAnti]
      exact H.zero_mem
  · have hdensq : x₀ - X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 :=
      Ideal.sub_mem _ hxsq' hX₂sq
    by_cases hdencube : x₀ - X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3
    · have hdenval : Valued.v
          (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
            exp (-3 : ℤ) := by
        simpa [x₀] using
          (v.mem_maximalIdeal_pow_iff (K := K) (x := x₀ - X₂) (n := 3)).mp hdencube
      have hdenne : x - ((X₂ : v.adicCompletionIntegers K) :
          v.adicCompletion K) ≠ 0 := sub_ne_zero.mpr hxx
      obtain ⟨dd, hdd⟩ : ∃ dd : ℤ,
          Valued.v (x - ((X₂ : v.adicCompletionIntegers K) :
            v.adicCompletion K)) = exp dd :=
        ⟨_, (exp_log ((Valued.v).pos_iff.mpr hdenne).ne').symm⟩
      have hddle : dd ≤ -3 := by
        rwa [hdd, exp_le_exp] at hdenval
      have hsecSlope : exp (1 : ℤ) ≤ Valued.v
          ((y - ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) /
            (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K))) := by
        rw [map_div₀, hsecnum, hdd, ← exp_sub, exp_le_exp]
        omega
      exact filtration_le_nonsingularReductionSubgroup hW
        (nonsingularReduction_isAdditive hW)
        (add_mem_filtration_of_slope hW hxy hdouble' hxx x₀.property X₂.property hsecSlope)
    · have hdenval_le : Valued.v
          (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
            exp (-2 : ℤ) := by
        simpa [x₀] using
          (v.mem_maximalIdeal_pow_iff (K := K) (x := x₀ - X₂) (n := 2)).mp hdensq
      have hdenval_not_le : ¬Valued.v
          (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
            exp (-3 : ℤ) := by
        intro hval
        apply hdencube
        exact (v.mem_maximalIdeal_pow_iff (K := K) (x := x₀ - X₂) (n := 3)).mpr
          (by simpa [x₀] using hval)
      have hdenne : x - ((X₂ : v.adicCompletionIntegers K) :
          v.adicCompletion K) ≠ 0 := sub_ne_zero.mpr hxx
      obtain ⟨dd, hdd⟩ : ∃ dd : ℤ,
          Valued.v (x - ((X₂ : v.adicCompletionIntegers K) :
            v.adicCompletion K)) = exp dd :=
        ⟨_, (exp_log ((Valued.v).pos_iff.mpr hdenne).ne').symm⟩
      have hddle : dd ≤ -2 := by
        rwa [hdd, exp_le_exp] at hdenval_le
      have hddnotle : ¬dd ≤ -3 := by
        intro hle
        apply hdenval_not_le
        rwa [hdd, exp_le_exp]
      have hddeq : dd = -2 := by omega
      have hdenval : Valued.v
          (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) =
            exp (-2 : ℤ) := by rw [hdd, hddeq]
      have hsecSlopeVal : Valued.v (W.slope x
          ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
          ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) = 1 := by
        rw [W.slope_of_X_ne hxx, map_div₀, hsecnum, hdenval]
        exact div_self exp_ne_zero
      let S : v.adicCompletionIntegers K :=
        ⟨W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
          ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K), hsecSlopeVal.le⟩
      have hSunit : IsUnit S :=
        (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mpr
          hsecSlopeVal
      let X₃ : v.adicCompletionIntegers K := S ^ 2 - x₀ - X₂
      let Y₃ : v.adicCompletionIntegers K := S * (x₀ - X₃) - y₀
      have hX₃ : ((X₃ : v.adicCompletionIntegers K) : v.adicCompletion K) =
          W.addX x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
            (W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
              ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
        change (W.slope x ((X₂ : v.adicCompletion K)) y
            ((Y₂ : v.adicCompletion K))) ^ 2 - x - (X₂ : v.adicCompletion K) = _
        rw [WeierstrassCurve.Affine.addX, ha₁, ha₂]
        ring
      have hY₃ : ((Y₃ : v.adicCompletionIntegers K) : v.adicCompletion K) =
          W.addY x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
            (W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
              ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
        change W.slope x ((X₂ : v.adicCompletion K)) y
            ((Y₂ : v.adicCompletion K)) * (x - (X₃ : v.adicCompletion K)) - y = _
        rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
          WeierstrassCurve.Affine.negY, ha₁, ha₃, hX₃]
        ring
      have htripleNot : ¬(x = ((X₂ : v.adicCompletionIntegers K) :
          v.adicCompletion K) ∧
          y = W.negY ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
            ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) :=
        fun h ↦ hxx h.1
      have htriple : W.Nonsingular
          (W.addX x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
            (W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
              ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)))
          (W.addY x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
            (W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
              ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K))) :=
        W.nonsingular_add hxy hdouble' htripleNot
      have htriple' : W.Nonsingular
          ((X₃ : v.adicCompletionIntegers K) : v.adicCompletion K)
          ((Y₃ : v.adicCompletionIntegers K) : v.adicCompletion K) := by
        rw [hX₃, hY₃]
        exact htriple
      have heq₃ : W₀.toAffine.Equation X₃ Y₃ :=
        equation_integral hW htriple'.left X₃.property Y₃.property
      have heq₃bar : (cuspidalShortCurve
          (ResidueField (v.adicCompletionIntegers K))).toAffine.Equation
          (residue (v.adicCompletionIntegers K) X₃)
          (residue (v.adicCompletionIntegers K) Y₃) := by
        have heqmap := WeierstrassCurve.Affine.Equation.map
          (residue (v.adicCompletionIntegers K)) heq₃
        change (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Equation
          (residue (v.adicCompletionIntegers K) X₃)
          (residue (v.adicCompletionIntegers K) Y₃) at heqmap
        rwa [hspecial] at heqmap
      have hSres : residue (v.adicCompletionIntegers K) S ≠ 0 :=
        (residue_ne_zero_iff_isUnit S).mpr hSunit
      have hX₃res : residue (v.adicCompletionIntegers K) X₃ =
          residue (v.adicCompletionIntegers K) S ^ 2 := by
        simp only [X₃, map_sub, map_pow, hreszero.1, hX₂res,
          sub_zero]
      have hX₃res_ne : residue (v.adicCompletionIntegers K) X₃ ≠ 0 := by
        rw [hX₃res]
        exact pow_ne_zero 2 hSres
      have hnonsingular₃ :
          (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Nonsingular
            (residue (v.adicCompletionIntegers K) X₃)
            (residue (v.adicCompletionIntegers K) Y₃) := by
        rw [hspecial]
        exact cuspidalShortCurve_nonsingular_of_ne_origin heq₃bar
          (Or.inl hX₃res_ne)
      have hred₃ : HasNonsingularReduction hW
          (.some ((X₃ : v.adicCompletionIntegers K) : v.adicCompletion K)
            ((Y₃ : v.adicCompletionIntegers K) : v.adicCompletion K) htriple') := by
        intro hx₃gate
        have h₃int := integral_of_not_mem hW htriple'.left hx₃gate
        have hXint : (⟨(X₃ : v.adicCompletion K), h₃int.1⟩ :
            v.adicCompletionIntegers K) = X₃ := Subtype.ext rfl
        have hYint : (⟨(Y₃ : v.adicCompletion K), h₃int.2⟩ :
            v.adicCompletionIntegers K) = Y₃ := Subtype.ext rfl
        rw [hXint, hYint]
        exact hnonsingular₃
      rw [Point.add_some htripleNot]
      change HasNonsingularReduction hW
        (.some
          (W.addX x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
            (W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
              ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)))
          (W.addY x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
            (W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
              ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K))) htriple)
      have hpoint :
          (.some
            (W.addX x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
              (W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
                ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)))
            (W.addY x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
              (W.slope x ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) y
                ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K))) htriple : W.Point) =
            .some ((X₃ : v.adicCompletionIntegers K) : v.adicCompletion K)
              ((Y₃ : v.adicCompletionIntegers K) : v.adicCompletion K) htriple' := by
        rw [Point.some.injEq]
        exact ⟨hX₃.symm, hY₃.symm⟩
      rw [hpoint]
      exact hred₃

/-- If the marked point has `x,y ∈ 𝔪²`, `a₄ ∈ 𝔪³`, and `a₆ ∉ 𝔪⁵`, then its triple has
canonical nonsingular reduction.  The equation itself forces `a₆ ∈ 𝔪⁴`; it is not a premise. -/
theorem three_nsmul_mem_nonsingularReductionSubgroup_of_marked_a₆_not_fifth
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)} {P : W.Point}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hxsq : D.x ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₄cube : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3)
    (ha₆notfive : W₀.a₆ ∉ maximalIdeal (v.adicCompletionIntegers K) ^ 5) :
    3 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  let H := nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)
  rcases D with ⟨ϖ, hϖ, ⟨x, hxint⟩, ⟨y, hyint⟩, hxy, hpoint, X, A, B,
    hx_eq, ha₄_eq, ha₆_eq, hysq, hroot⟩
  change W.Nonsingular x y at hxy
  change P = .some x y hxy at hpoint
  rw [hpoint]
  let x₀ : v.adicCompletionIntegers K := ⟨x, hxint⟩
  let y₀ : v.adicCompletionIntegers K := ⟨y, hyint⟩
  change x₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 at hxsq
  change y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 at hysq
  have heq₀ : W₀.toAffine.Equation x₀ y₀ :=
    equation_integral hW hxy.left hxint hyint
  letI : Invertible (2 : ResidueField (v.adicCompletionIntegers K)) :=
    invertibleOfNonzero h2
  letI : Invertible (3 : ResidueField (v.adicCompletionIntegers K)) :=
    invertibleOfNonzero h3
  have hxmax : x₀ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)) hxsq
  have hymax : y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)) hysq
  have hreszero : residue (v.adicCompletionIntegers K) x₀ = 0 ∧
      residue (v.adicCompletionIntegers K) y₀ = 0 :=
    ⟨(residue_eq_zero_iff x₀).mpr hxmax,
      (residue_eq_zero_iff y₀).mpr hymax⟩
  have heqshort : y₀ ^ 2 = x₀ ^ 3 + W₀.a₄ * x₀ + W₀.a₆ := by
    have heq' := (WeierstrassCurve.Affine.equation_iff x₀ y₀).mp heq₀
    simp only [WeierstrassCurve.a₁_of_isShortNF,
      WeierstrassCurve.a₂_of_isShortNF,
      WeierstrassCurve.a₃_of_isShortNF, zero_mul] at heq'
    simpa only [zero_add, add_zero] using heq'
  have hynotcube : y₀ ∉ maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
    intro hycube
    apply ha₆notfive
    have hyfive : y₀ ^ 2 ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 5 := by
      have hmul := Ideal.mul_mem_mul hycube hysq
      simpa [pow_succ, pow_two, mul_assoc] using hmul
    have hxsix : x₀ ^ 3 ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 6 := by
      have hx4 := Ideal.mul_mem_mul hxsq hxsq
      have hx6 := Ideal.mul_mem_mul hx4 hxsq
      simpa [pow_succ, pow_two, mul_assoc] using hx6
    have hxfive : x₀ ^ 3 ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 5 :=
      (Ideal.pow_le_pow_right (by norm_num : 5 ≤ 6)) hxsix
    have ha₄x : W₀.a₄ * x₀ ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 5 := by
      have hmul := Ideal.mul_mem_mul ha₄cube hxsq
      simpa only [← pow_add, Nat.reduceAdd] using hmul
    have ha₆eq : W₀.a₆ = y₀ ^ 2 - x₀ ^ 3 - W₀.a₄ * x₀ := by
      linear_combination -heqshort
    rw [ha₆eq]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hyfive hxfive) ha₄x
  have hyval_le : Valued.v y ≤ exp (-2 : ℤ) := by
    simpa [y₀] using
      (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 2)).mp hysq
  have hyval_not_le : ¬Valued.v y ≤ exp (-3 : ℤ) := by
    intro hyval
    apply hynotcube
    exact (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 3)).mpr
      (by simpa [y₀] using hyval)
  have hyne : y ≠ 0 := by
    intro hyzero
    apply hynotcube
    have hy₀zero : y₀ = 0 := Subtype.ext hyzero
    rw [hy₀zero]
    exact Submodule.zero_mem _
  obtain ⟨dy, hdy⟩ : ∃ dy : ℤ, Valued.v y = exp dy :=
    ⟨_, (exp_log ((Valued.v).pos_iff.mpr hyne).ne').symm⟩
  have hdy_le : dy ≤ -2 := by
    rwa [hdy, exp_le_exp] at hyval_le
  have hdy_not_le : ¬dy ≤ -3 := by
    intro hle
    apply hyval_not_le
    rwa [hdy, exp_le_exp]
  have hdy_eq : dy = -2 := by omega
  have hyval : Valued.v y = exp (-2 : ℤ) := by rw [hdy, hdy_eq]
  exact
    three_nsmul_mem_nonsingularReductionSubgroup_of_coordinate_depths
      hW h2 h3 hspecial hxy hxint hyint
      (by simpa [x₀] using hxsq) (by simpa [y₀] using hysq)
      ha₄cube hyval hyne

/-- The marked branch outside `𝔪⁵` supplies the exponent twelve used by the arithmetic
specializations: it is four times the checked triple. -/
theorem twelve_nsmul_mem_nonsingularReductionSubgroup_of_marked_a₆_not_fifth
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)} {P : W.Point}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hxsq : D.x ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₄cube : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3)
    (ha₆notfive : W₀.a₆ ∉ maximalIdeal (v.adicCompletionIntegers K) ^ 5) :
    12 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  have hthree :=
    three_nsmul_mem_nonsingularReductionSubgroup_of_marked_a₆_not_fifth
      hW h2 h3 hspecial D hxsq ha₄cube ha₆notfive
  have hfour := (nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)).nsmul_mem hthree 4
  rw [← mul_nsmul] at hfour
  norm_num at hfour
  exact hfour

end MazurTorsion.EllipticCurve
