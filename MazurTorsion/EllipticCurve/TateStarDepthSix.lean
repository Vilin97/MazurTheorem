/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.MinimalModelScaling
import MazurTorsion.EllipticCurve.TateStarDepthFour

/-!
# The terminal weighted-depth branch of the marked short equation

This file continues the pointwise calculation on the selected short marked model.  From
`x ∈ 𝔪²`, `a₄ ∈ 𝔪³`, and `a₆ ∈ 𝔪⁵`, the equation first forces `y ∈ 𝔪³`.  If `a₄` has exact
depth three, the marked double has canonical nonsingular reduction.  Excluding that branch
forces the weighted depths `a₄ ∈ 𝔪⁴` and `a₆ ∈ 𝔪⁶`, to which the checked pure-scaling
minimality obstruction applies.

Only the selected equation, its marked point, and minimality are used.  No Kodaira symbol,
regular model, component group, or component-cardinality claim is made.
-/

noncomputable section

open IsLocalRing

namespace MazurTorsion.EllipticCurve

open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

universe u v

/-- On the selected marked short equation, the weighted coefficient depths
`x ∈ 𝔪²`, `a₄ ∈ 𝔪³`, and `a₆ ∈ 𝔪⁵` force the marked ordinate into `𝔪³`. -/
theorem markedExceptionalCubic_y_mem_cube_of_coefficient_depths
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)} {P : W.Point}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W₀.IsShortNF]
    (D : MarkedExceptionalCubicData W₀ W P)
    (hxsq : D.x ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₄cube : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3)
    (ha₆five : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 5) :
    D.y ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
  have heq₀ : W₀.toAffine.Equation D.x D.y :=
    equation_integral hW D.nonsingular.left D.x.property D.y.property
  have heqshort : D.y ^ 2 = D.x ^ 3 + W₀.a₄ * D.x + W₀.a₆ := by
    have heq' := (WeierstrassCurve.Affine.equation_iff D.x D.y).mp heq₀
    simp only [WeierstrassCurve.a₁_of_isShortNF,
      WeierstrassCurve.a₂_of_isShortNF,
      WeierstrassCurve.a₃_of_isShortNF, zero_mul] at heq'
    simpa only [zero_add, add_zero] using heq'
  have hxsix : D.x ^ 3 ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 6 := by
    have hx4 := Ideal.mul_mem_mul hxsq hxsq
    have hx6 := Ideal.mul_mem_mul hx4 hxsq
    simpa [pow_succ, pow_two, mul_assoc] using hx6
  have hxfive : D.x ^ 3 ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 5 :=
    (Ideal.pow_le_pow_right (by norm_num : 5 ≤ 6)) hxsix
  have ha₄x : W₀.a₄ * D.x ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 5 := by
    have hmul := Ideal.mul_mem_mul ha₄cube hxsq
    simpa only [← pow_add, Nat.reduceAdd] using hmul
  have hysqfive : D.y ^ 2 ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 5 := by
    rw [heqshort]
    exact Ideal.add_mem _ (Ideal.add_mem _ hxfive ha₄x) ha₆five
  by_cases hyzero : ((D.y : v.adicCompletionIntegers K) :
      v.adicCompletion K) = 0
  · have hyzero' : D.y = 0 := Subtype.ext hyzero
    rw [hyzero']
    exact Submodule.zero_mem _
  · have hysqval : Valued.v
        (((D.y ^ 2 : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
          exp (-5 : ℤ) :=
      (v.mem_maximalIdeal_pow_iff (K := K) (x := D.y ^ 2) (n := 5)).mp
        hysqfive
    obtain ⟨dy, hdy⟩ : ∃ dy : ℤ,
        Valued.v ((D.y : v.adicCompletionIntegers K) :
          v.adicCompletion K) = exp dy :=
      ⟨_, (exp_log ((Valued.v).pos_iff.mpr hyzero).ne').symm⟩
    have hdybound : 2 * dy ≤ -5 := by
      change Valued.v
          (((D.y : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2) ≤
        exp (-5 : ℤ) at hysqval
      rw [map_pow, hdy, ← exp_nsmul, exp_le_exp] at hysqval
      omega
    apply (v.mem_maximalIdeal_pow_iff (K := K) (x := D.y) (n := 3)).mpr
    rw [hdy, exp_le_exp]
    omega

/-- Once `a₄` reaches weighted depth four on the same marked short equation,
the equation upgrades `a₆ ∈ 𝔪⁵` to `a₆ ∈ 𝔪⁶`. -/
theorem markedExceptionalCubic_a₆_mem_sixth_of_coefficient_depths
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)} {P : W.Point}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W₀.IsShortNF]
    (D : MarkedExceptionalCubicData W₀ W P)
    (hxsq : D.x ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₄four : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 4)
    (ha₆five : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 5) :
    W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 6 := by
  have ha₄cube : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3 :=
    (Ideal.pow_le_pow_right (by norm_num : 3 ≤ 4)) ha₄four
  have hycube := markedExceptionalCubic_y_mem_cube_of_coefficient_depths
    hW D hxsq ha₄cube ha₆five
  have heq₀ : W₀.toAffine.Equation D.x D.y :=
    equation_integral hW D.nonsingular.left D.x.property D.y.property
  have heqshort : D.y ^ 2 = D.x ^ 3 + W₀.a₄ * D.x + W₀.a₆ := by
    have heq' := (WeierstrassCurve.Affine.equation_iff D.x D.y).mp heq₀
    simp only [WeierstrassCurve.a₁_of_isShortNF,
      WeierstrassCurve.a₂_of_isShortNF,
      WeierstrassCurve.a₃_of_isShortNF, zero_mul] at heq'
    simpa only [zero_add, add_zero] using heq'
  have hysix : D.y ^ 2 ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 6 := by
    have hmul := Ideal.mul_mem_mul hycube hycube
    simpa [pow_succ, pow_two, mul_assoc] using hmul
  have hxsix : D.x ^ 3 ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 6 := by
    have hx4 := Ideal.mul_mem_mul hxsq hxsq
    have hx6 := Ideal.mul_mem_mul hx4 hxsq
    simpa [pow_succ, pow_two, mul_assoc] using hx6
  have ha₄x : W₀.a₄ * D.x ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 6 := by
    have hmul := Ideal.mul_mem_mul ha₄four hxsq
    simpa only [← pow_add, Nat.reduceAdd] using hmul
  have ha₆eq : W₀.a₆ = D.y ^ 2 - D.x ^ 3 - W₀.a₄ * D.x := by
    linear_combination -heqshort
  rw [ha₆eq]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ hysix hxsix) ha₄x

/-- If `a₄` has exact depth three after the marked equation has reached
`x ∈ 𝔪²` and `a₆ ∈ 𝔪⁵`, the double of the marked point has canonical
nonsingular reduction. -/
theorem two_nsmul_mem_nonsingularReductionSubgroup_of_marked_a₄_not_fourth
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
    (ha₄notfour : W₀.a₄ ∉ maximalIdeal (v.adicCompletionIntegers K) ^ 4)
    (ha₆five : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 5) :
    2 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  have hycube := markedExceptionalCubic_y_mem_cube_of_coefficient_depths
    hW D hxsq ha₄cube ha₆five
  rcases D with ⟨ϖ, hϖ, x₀, y₀, hxy, hpoint, X, A, B,
    hx_eq, ha₄_eq, ha₆_eq, hysq, hroot⟩
  change W.Nonsingular (x₀ : v.adicCompletion K)
    (y₀ : v.adicCompletion K) at hxy
  change P = .some (x₀ : v.adicCompletion K)
    (y₀ : v.adicCompletion K) hxy at hpoint
  rw [hpoint, two_nsmul]
  let H := nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)
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
  have hx4 : x₀ ^ 2 ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 4 := by
    rw [pow_two]
    exact pow_add (maximalIdeal (v.adicCompletionIntegers K)) 2 2 ▸
      Ideal.mul_mem_mul hxsq hxsq
  have h3x4 : 3 * x₀ ^ 2 ∈
      maximalIdeal (v.adicCompletionIntegers K) ^ 4 :=
    Ideal.mul_mem_left _ 3 hx4
  let n₀ : v.adicCompletionIntegers K := 3 * x₀ ^ 2 + W₀.a₄
  have hn₀mem : n₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
    have h3x3 : 3 * x₀ ^ 2 ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 3 :=
      (Ideal.pow_le_pow_right (by norm_num : 3 ≤ 4)) h3x4
    exact Ideal.add_mem _ h3x3 ha₄cube
  have hn₀notfour : n₀ ∉
      maximalIdeal (v.adicCompletionIntegers K) ^ 4 := by
    intro hn₀four
    apply ha₄notfour
    have hid : W₀.a₄ = n₀ - 3 * x₀ ^ 2 := by simp [n₀]
    rw [hid]
    exact Ideal.sub_mem _ hn₀four h3x4
  have hn₀coe : ((n₀ : v.adicCompletionIntegers K) : v.adicCompletion K) =
      3 * (x₀ : v.adicCompletion K) ^ 2 + W.a₄ := by
    change 3 * (x₀ : v.adicCompletion K) ^ 2 +
      ((W₀.a₄ : v.adicCompletionIntegers K) : v.adicCompletion K) = _
    rw [ha₄coe]
  have hnval_le : Valued.v ((n₀ : v.adicCompletionIntegers K) :
      v.adicCompletion K) ≤ exp (-3 : ℤ) :=
    (v.mem_maximalIdeal_pow_iff (K := K) (x := n₀) (n := 3)).mp hn₀mem
  have hnval_not_le : ¬Valued.v ((n₀ : v.adicCompletionIntegers K) :
      v.adicCompletion K) ≤ exp (-4 : ℤ) := by
    intro hnval
    exact hn₀notfour
      ((v.mem_maximalIdeal_pow_iff (K := K) (x := n₀) (n := 4)).mpr hnval)
  have hnzero : ((n₀ : v.adicCompletionIntegers K) :
      v.adicCompletion K) ≠ 0 := by
    intro hnzero
    apply hn₀notfour
    have hnzero' : n₀ = 0 := Subtype.ext hnzero
    rw [hnzero']
    exact Submodule.zero_mem _
  obtain ⟨dn, hdn⟩ : ∃ dn : ℤ,
      Valued.v ((n₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) = exp dn :=
    ⟨_, (exp_log ((Valued.v).pos_iff.mpr hnzero).ne').symm⟩
  have hdnle : dn ≤ -3 := by
    rwa [hdn, exp_le_exp] at hnval_le
  have hdnnotle : ¬dn ≤ -4 := by
    intro hle
    apply hnval_not_le
    rwa [hdn, exp_le_exp]
  have hdneq : dn = -3 := by omega
  have hnum : Valued.v
      (3 * (x₀ : v.adicCompletion K) ^ 2 + W.a₄) = exp (-3 : ℤ) := by
    rw [← hn₀coe, hdn, hdneq]
  have htwoUnit : IsUnit (2 : v.adicCompletionIntegers K) :=
    (residue_ne_zero_iff_isUnit (2 : v.adicCompletionIntegers K)).mp (by
      simpa only [map_ofNat] using h2)
  have htwoval : Valued.v (2 : v.adicCompletion K) = 1 := by
    change Valued.v (((2 : v.adicCompletionIntegers K) :
      v.adicCompletion K)) = 1
    exact (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp
      htwoUnit
  rcases eq_or_ne ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)
      (W.negY ((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K)
        ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)) with
    hyneg | hyneg
  · rw [Point.add_self_of_Y_eq hyneg]
    exact H.zero_mem
  have hslope : W.slope
      ((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K)
      ((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K)
      ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)
      ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        (3 * (x₀ : v.adicCompletion K) ^ 2 + W.a₄) /
          (2 * (y₀ : v.adicCompletion K)) := by
    rw [W.slope_of_Y_ne rfl hyneg, ha₁, ha₂]
    simp only [zero_mul, sub_zero]
    rw [WeierstrassCurve.Affine.negY, ha₁, ha₃]
    ring
  by_cases hyfour : y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 4
  · have hyval : Valued.v ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ exp (-4 : ℤ) :=
      (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 4)).mp hyfour
    have hyne : ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≠ 0 := by
      intro hyzero
      apply hyneg
      rw [hyzero, WeierstrassCurve.Affine.negY, ha₁, ha₃]
      ring
    obtain ⟨dy, hdy⟩ : ∃ dy : ℤ,
        Valued.v ((y₀ : v.adicCompletionIntegers K) :
          v.adicCompletion K) = exp dy :=
      ⟨_, (exp_log ((Valued.v).pos_iff.mpr hyne).ne').symm⟩
    have hdyle : dy ≤ -4 := by
      rwa [hdy, exp_le_exp] at hyval
    have hslopeval : exp (1 : ℤ) ≤ Valued.v (W.slope
        (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
        (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)) := by
      rw [hslope, map_div₀, hnum, map_mul, htwoval, one_mul, hdy,
        ← exp_sub, exp_le_exp]
      omega
    exact filtration_le_nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW)
      (add_self_mem_filtration_of_slope hW hxy x₀.property hyneg hslopeval)
  · have hyval_le : Valued.v ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ exp (-3 : ℤ) :=
      (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 3)).mp hycube
    have hyval_not_le : ¬Valued.v ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ exp (-4 : ℤ) := by
      intro hyval
      exact hyfour
        ((v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 4)).mpr hyval)
    have hyne : ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≠ 0 := by
      intro hyzero
      apply hyfour
      have hyzero' : y₀ = 0 := Subtype.ext hyzero
      rw [hyzero']
      exact Submodule.zero_mem _
    obtain ⟨dy, hdy⟩ : ∃ dy : ℤ,
        Valued.v ((y₀ : v.adicCompletionIntegers K) :
          v.adicCompletion K) = exp dy :=
      ⟨_, (exp_log ((Valued.v).pos_iff.mpr hyne).ne').symm⟩
    have hdyle : dy ≤ -3 := by
      rwa [hdy, exp_le_exp] at hyval_le
    have hdynotle : ¬dy ≤ -4 := by
      intro hle
      apply hyval_not_le
      rwa [hdy, exp_le_exp]
    have hdyeq : dy = -3 := by omega
    have hyval : Valued.v ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) = exp (-3 : ℤ) := by rw [hdy, hdyeq]
    have hslopeval : Valued.v (W.slope
        (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
        (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)) = 1 := by
      rw [hslope, map_div₀, hnum, map_mul, htwoval, one_mul, hyval]
      exact div_self (exp_ne_zero : exp (-3 : ℤ) ≠ 0)
    let L : v.adicCompletionIntegers K :=
      ⟨W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
        (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K), hslopeval.le⟩
    have hLunit : IsUnit L :=
      (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mpr
        hslopeval
    let X₂ : v.adicCompletionIntegers K := L ^ 2 - 2 * x₀
    let Y₂ : v.adicCompletionIntegers K := L * (x₀ - X₂) - y₀
    have hX₂ : ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        W.addX (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
            (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)) := by
      change (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
        (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)) ^ 2 -
          2 * (x₀ : v.adicCompletion K) = _
      rw [WeierstrassCurve.Affine.addX, ha₁, ha₂]
      ring
    have hY₂ : ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        W.addY (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (y₀ : v.adicCompletion K)
          (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
            (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)) := by
      change W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K) *
          ((x₀ : v.adicCompletion K) - (X₂ : v.adicCompletion K)) -
          (y₀ : v.adicCompletion K) = _
      rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY, ha₁, ha₃, hX₂]
      ring
    have hnot : ¬((x₀ : v.adicCompletion K) = (x₀ : v.adicCompletion K) ∧
        (y₀ : v.adicCompletion K) =
          W.negY (x₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)) :=
      fun h ↦ hyneg h.2
    have hsum : W.Nonsingular
        (W.addX (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
            (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)))
        (W.addY (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (y₀ : v.adicCompletion K)
          (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
            (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K))) :=
      W.nonsingular_add hxy hxy hnot
    have hsum' : W.Nonsingular (X₂ : v.adicCompletion K)
        (Y₂ : v.adicCompletion K) := by
      rw [hX₂, hY₂]
      exact hsum
    have heq₂ : W₀.toAffine.Equation X₂ Y₂ :=
      equation_integral hW hsum'.left X₂.property Y₂.property
    have heq₂bar : (cuspidalShortCurve
        (ResidueField (v.adicCompletionIntegers K))).toAffine.Equation
        (residue (v.adicCompletionIntegers K) X₂)
        (residue (v.adicCompletionIntegers K) Y₂) := by
      have heqmap := WeierstrassCurve.Affine.Equation.map
        (residue (v.adicCompletionIntegers K)) heq₂
      change (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Equation
        (residue (v.adicCompletionIntegers K) X₂)
        (residue (v.adicCompletionIntegers K) Y₂) at heqmap
      rwa [hspecial] at heqmap
    have hxmax : x₀ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
      (Ideal.pow_le_self (by norm_num : (2 : ℕ) ≠ 0)) hxsq
    have hxres : residue (v.adicCompletionIntegers K) x₀ = 0 :=
      (residue_eq_zero_iff x₀).mpr hxmax
    have hLres : residue (v.adicCompletionIntegers K) L ≠ 0 :=
      (residue_ne_zero_iff_isUnit L).mpr hLunit
    have hX₂res : residue (v.adicCompletionIntegers K) X₂ =
        residue (v.adicCompletionIntegers K) L ^ 2 := by
      simp [X₂, hxres]
    have hX₂res_ne : residue (v.adicCompletionIntegers K) X₂ ≠ 0 := by
      rw [hX₂res]
      exact pow_ne_zero 2 hLres
    have hnonsingular₂ :
        (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Nonsingular
          (residue (v.adicCompletionIntegers K) X₂)
          (residue (v.adicCompletionIntegers K) Y₂) := by
      rw [hspecial]
      exact cuspidalShortCurve_nonsingular_of_ne_origin heq₂bar
        (Or.inl hX₂res_ne)
    have hred₂ : HasNonsingularReduction hW
        (.some (X₂ : v.adicCompletion K) (Y₂ : v.adicCompletion K) hsum') := by
      intro hx₂gate
      have h₂int := integral_of_not_mem hW hsum'.left hx₂gate
      have hXint : (⟨(X₂ : v.adicCompletion K), h₂int.1⟩ :
          v.adicCompletionIntegers K) = X₂ := Subtype.ext rfl
      have hYint : (⟨(Y₂ : v.adicCompletion K), h₂int.2⟩ :
          v.adicCompletionIntegers K) = Y₂ := Subtype.ext rfl
      rw [hXint, hYint]
      exact hnonsingular₂
    rw [Point.add_some hnot]
    change HasNonsingularReduction hW
      (.some
        (W.addX (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
            (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)))
        (W.addY (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (y₀ : v.adicCompletion K)
          (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
            (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K))) hsum)
    have hpoint₂ :
        (.some
          (W.addX (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
            (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
              (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)))
          (W.addY (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
            (y₀ : v.adicCompletion K)
            (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
              (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K))) hsum : W.Point) =
          .some (X₂ : v.adicCompletion K) (Y₂ : v.adicCompletion K) hsum' := by
      rw [Point.some.injEq]
      exact ⟨hX₂.symm, hY₂.symm⟩
    rw [hpoint₂]
    exact hred₂

/-- The exact-depth-three `a₄` branch supplies the exponent twelve required
by the arithmetic specializations. -/
theorem twelve_nsmul_mem_nonsingularReductionSubgroup_of_marked_a₄_not_fourth
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
    (ha₄notfour : W₀.a₄ ∉ maximalIdeal (v.adicCompletionIntegers K) ^ 4)
    (ha₆five : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 5) :
    12 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  have htwo :=
    two_nsmul_mem_nonsingularReductionSubgroup_of_marked_a₄_not_fourth
      hW h2 h3 hspecial D hxsq ha₄cube ha₄notfour ha₆five
  have hsix := (nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)).nsmul_mem htwo 6
  rw [← mul_nsmul] at hsix
  norm_num at hsix
  exact hsix

/-- A short integral model with weighted depths `a₄ ∈ 𝔪⁴` and
`a₆ ∈ 𝔪⁶` cannot have minimal generic fibre.  Scaling by the displayed
uniformizer would keep every coefficient integral while increasing the
discriminant valuation. -/
theorem not_isMinimal_of_short_model_weighted_coefficient_depths
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [W₀.IsShortNF]
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (ha₄four : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 4)
    (ha₆six : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 6) :
    ¬ W.IsMinimal (v.adicCompletionIntegers K) := by
  intro hminimal
  letI : W.IsMinimal (v.adicCompletionIntegers K) := hminimal
  have hϖne : ((ϖ : v.adicCompletionIntegers K) :
      v.adicCompletion K) ≠ 0 := by
    exact_mod_cast hϖ.ne_zero
  let u : (v.adicCompletion K)ˣ :=
    Units.mk0 ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) hϖne
  have hu : IsDedekindDomain.HeightOneSpectrum.valuation
      (v.adicCompletion K)
      (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K))
      (u : v.adicCompletion K) < 1 := by
    change IsDedekindDomain.HeightOneSpectrum.valuation
      (v.adicCompletion K)
      (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K))
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) < 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    change ϖ ∈ maximalIdeal (v.adicCompletionIntegers K)
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  apply tateAlgorithm_minimalityCoefficientObstruction
    (R := v.adicCompletionIntegers K) (K := v.adicCompletion K)
    (W := W) u hu
  have hmax : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  have ha₄div := ha₄four
  have ha₆div := ha₆six
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha₄div ha₆div
  obtain ⟨b₄, hb₄⟩ := ha₄div
  obtain ⟨b₆, hb₆⟩ := ha₆div
  have ha₁ : W.a₁ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₁, W₀.a₁_of_isShortNF, map_zero]
  have ha₂ : W.a₂ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₂, W₀.a₂_of_isShortNF, map_zero]
  have ha₃ : W.a₃ = 0 := by
    rw [← hW, WeierstrassCurve.map_a₃, W₀.a₃_of_isShortNF, map_zero]
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨b₄, ?_⟩, ⟨b₆, ?_⟩⟩
  · simp [ha₁]
  · simp [ha₂]
  · simp [ha₃]
  · have ha₄coe : algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K) W₀.a₄ = W.a₄ := by
      simpa only [WeierstrassCurve.map_a₄] using congrArg (fun V ↦ V.a₄) hW
    rw [← ha₄coe, hb₄]
    simp [u, map_mul, map_pow, hϖne]
  · have ha₆coe : algebraMap (v.adicCompletionIntegers K)
        (v.adicCompletion K) W₀.a₆ = W.a₆ := by
      simpa only [WeierstrassCurve.map_a₆] using congrArg (fun V ↦ V.a₆) hW
    rw [← ha₆coe, hb₆]
    simp [u, map_mul, map_pow, hϖne]

end MazurTorsion.EllipticCurve
