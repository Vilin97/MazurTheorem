/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TateTypeIIIComponent

/-!
# The marked triple in the next tame Tate branch

Let an integral short Weierstrass equation have standard cuspidal special fibre, with
`a₄ ∈ 𝔪²` and `a₆ ∈ 𝔪² \ 𝔪³`.  This file proves the pointwise consequence needed by the tame
torsion argument: the triple of every local point has canonical nonsingular reduction.

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

/-- In the exact depth-two `a₆` branch, the triple of every local point belongs to canonical
nonsingular reduction. -/
theorem three_nsmul_mem_nonsingularReductionSubgroup_of_a₄_sq_a₆_sq_not_cube
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
    (ha₄sq : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (_ha₆sq : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₆notcube : W₀.a₆ ∉ maximalIdeal (v.adicCompletionIntegers K) ^ 3)
    (P : W.Point) :
    3 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  let H := nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)
  by_cases hP : HasNonsingularReduction hW P
  · exact H.nsmul_mem hP 3
  rcases P with _ | ⟨x, y, hxy⟩
  · exact (hP (hasNonsingularReduction_zero hW)).elim
  have hxgate : ¬ exp (2 : ℤ) ≤ Valued.v x := by
    intro hx
    apply hP
    exact hasNonsingularReduction_of_mem_filtration hW
      ((some_mem_filtration (hW := hW) (n := 0)).mpr hx)
  have hxyint := integral_of_not_mem hW hxy.left hxgate
  let x₀ : v.adicCompletionIntegers K := ⟨x, hxyint.1⟩
  let y₀ : v.adicCompletionIntegers K := ⟨y, hxyint.2⟩
  have heq₀ : W₀.toAffine.Equation x₀ y₀ :=
    equation_integral hW hxy.left hxyint.1 hxyint.2
  have hsingular : ¬(W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Nonsingular
      (residue (v.adicCompletionIntegers K) x₀)
      (residue (v.adicCompletionIntegers K) y₀) := by
    intro hnonsingular
    apply hP
    intro _
    simpa [x₀, y₀] using hnonsingular
  have heqbar : (cuspidalShortCurve
      (ResidueField (v.adicCompletionIntegers K))).toAffine.Equation
      (residue (v.adicCompletionIntegers K) x₀)
      (residue (v.adicCompletionIntegers K) y₀) := by
    have := WeierstrassCurve.Affine.Equation.map
      (residue (v.adicCompletionIntegers K)) heq₀
    change (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Equation
      (residue (v.adicCompletionIntegers K) x₀)
      (residue (v.adicCompletionIntegers K) y₀) at this
    rwa [hspecial] at this
  letI : Invertible (2 : ResidueField (v.adicCompletionIntegers K)) :=
    invertibleOfNonzero h2
  letI : Invertible (3 : ResidueField (v.adicCompletionIntegers K)) :=
    invertibleOfNonzero h3
  have hreszero : residue (v.adicCompletionIntegers K) x₀ = 0 ∧
      residue (v.adicCompletionIntegers K) y₀ = 0 := by
    by_contra hne
    apply hsingular
    rw [hspecial]
    exact cuspidalShortCurve_nonsingular_of_ne_origin heqbar
      (not_and_or.mp hne)
  have hxmax : x₀ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (residue_eq_zero_iff x₀).mp hreszero.1
  have hymax : y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (residue_eq_zero_iff y₀).mp hreszero.2
  have heqshort : y₀ ^ 2 = x₀ ^ 3 + W₀.a₄ * x₀ + W₀.a₆ := by
    have heq' := (WeierstrassCurve.Affine.equation_iff x₀ y₀).mp heq₀
    simp only [WeierstrassCurve.a₁_of_isShortNF,
      WeierstrassCurve.a₂_of_isShortNF,
      WeierstrassCurve.a₃_of_isShortNF, zero_mul] at heq'
    simpa only [zero_add, add_zero] using heq'
  have hynotsq : y₀ ∉ maximalIdeal (v.adicCompletionIntegers K) ^ 2 := by
    intro hysq
    apply ha₆notcube
    have hycube : y₀ ^ 2 ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
      have hmul := Ideal.mul_mem_mul hysq hymax
      simpa [pow_succ, pow_two, mul_assoc] using hmul
    have hxcube : x₀ ^ 3 ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
      have hx2 := Ideal.mul_mem_mul hxmax hxmax
      have hx3 := Ideal.mul_mem_mul hx2 hxmax
      simpa [pow_succ, pow_two, mul_assoc] using hx3
    have ha₄x : W₀.a₄ * x₀ ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 3 := by
      have hmul := Ideal.mul_mem_mul ha₄sq hxmax
      simpa [pow_succ] using hmul
    have ha₆eq : W₀.a₆ = y₀ ^ 2 - x₀ ^ 3 - W₀.a₄ * x₀ := by
      linear_combination -heqshort
    rw [ha₆eq]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hycube hxcube) ha₄x
  have hyval_le : Valued.v y ≤ exp (-1 : ℤ) := by
    simpa [y₀] using
      (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 1)).mp
        (by simpa using hymax)
  have hyval_not_le : ¬Valued.v y ≤ exp (-2 : ℤ) := by
    intro hyval
    apply hynotsq
    exact (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 2)).mpr
      (by simpa [y₀] using hyval)
  have hyne : y ≠ 0 := by
    intro hyzero
    apply hynotsq
    have hy₀zero : y₀ = 0 := Subtype.ext hyzero
    rw [hy₀zero]
    exact Submodule.zero_mem _
  obtain ⟨dy, hdy⟩ : ∃ dy : ℤ, Valued.v y = exp dy :=
    ⟨_, (exp_log ((Valued.v).pos_iff.mpr hyne).ne').symm⟩
  have hdy_le : dy ≤ -1 := by
    rwa [hdy, exp_le_exp] at hyval_le
  have hdy_not_le : ¬dy ≤ -2 := by
    intro hle
    apply hyval_not_le
    rwa [hdy, exp_le_exp]
  have hdy_eq : dy = -1 := by omega
  have hyval : Valued.v y = exp (-1 : ℤ) := by rw [hdy, hdy_eq]
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
  have hn₀mem : n₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 := by
    have hx2 : x₀ ^ 2 ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 := by
      simpa [pow_two] using Ideal.mul_mem_mul hxmax hxmax
    have h3x2 : 3 * x₀ ^ 2 ∈
        maximalIdeal (v.adicCompletionIntegers K) ^ 2 :=
      Ideal.mul_mem_left _ 3 hx2
    exact Ideal.add_mem _ h3x2 ha₄sq
  have hn₀coe : ((n₀ : v.adicCompletionIntegers K) : v.adicCompletion K) =
      3 * x ^ 2 + W.a₄ := by
    change 3 * x ^ 2 + ((W₀.a₄ : v.adicCompletionIntegers K) :
      v.adicCompletion K) = _
    rw [ha₄coe]
  have hnumle : Valued.v (3 * x ^ 2 + W.a₄) ≤ exp (-2 : ℤ) := by
    rw [← hn₀coe]
    simpa [n₀] using
      (v.mem_maximalIdeal_pow_iff (K := K) (x := n₀) (n := 2)).mp hn₀mem
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
      have hdnle : dn ≤ -2 := by rwa [hdn, exp_le_exp] at hnumle
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
  have hX₂res : residue (v.adicCompletionIntegers K) X₂ = 0 := by
    simp [X₂, hLres, hreszero.1]
  have hY₂res : residue (v.adicCompletionIntegers K) Y₂ = 0 := by
    simp [Y₂, hLres, hreszero.2]
  have hX₂max : X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (residue_eq_zero_iff X₂).mp hX₂res
  have hY₂max : Y₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
    (residue_eq_zero_iff Y₂).mp hY₂res
  have hcorr : Y₂ + y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2 := by
    have hdiff : x₀ - X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
      Ideal.sub_mem _ hxmax hX₂max
    have hmul := Ideal.mul_mem_mul hLmax hdiff
    have hid : Y₂ + y₀ = L * (x₀ - X₂) := by simp [Y₂]
    rw [hid]
    simpa only [pow_two] using hmul
  have hcorrval : Valued.v
      (((Y₂ + y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
        exp (-2 : ℤ) :=
    (v.mem_maximalIdeal_pow_iff (K := K) (x := Y₂ + y₀) (n := 2)).mp hcorr
  have htwoyval : Valued.v (2 * y) = exp (-1 : ℤ) := by
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
        exp (-1 : ℤ) := by
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
  · have hdenmax : x₀ - X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) :=
      Ideal.sub_mem _ hxmax hX₂max
    by_cases hdensq : x₀ - X₂ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2
    · have hdenval : Valued.v
          (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
            exp (-2 : ℤ) := by
        simpa [x₀] using
          (v.mem_maximalIdeal_pow_iff (K := K) (x := x₀ - X₂) (n := 2)).mp hdensq
      have hdenne : x - ((X₂ : v.adicCompletionIntegers K) :
          v.adicCompletion K) ≠ 0 := sub_ne_zero.mpr hxx
      obtain ⟨dd, hdd⟩ : ∃ dd : ℤ,
          Valued.v (x - ((X₂ : v.adicCompletionIntegers K) :
            v.adicCompletion K)) = exp dd :=
        ⟨_, (exp_log ((Valued.v).pos_iff.mpr hdenne).ne').symm⟩
      have hddle : dd ≤ -2 := by
        rwa [hdd, exp_le_exp] at hdenval
      have hsecSlope : exp (1 : ℤ) ≤ Valued.v
          ((y - ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) /
            (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K))) := by
        rw [map_div₀, hsecnum, hdd, ← exp_sub, exp_le_exp]
        omega
      exact filtration_le_nonsingularReductionSubgroup hW
        (nonsingularReduction_isAdditive hW)
        (add_mem_filtration_of_slope hW hxy hdouble' hxx hxyint.1 X₂.property hsecSlope)
    · have hdenval_le : Valued.v
          (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
            exp (-1 : ℤ) := by
        simpa [x₀] using
          (v.mem_maximalIdeal_pow_iff (K := K) (x := x₀ - X₂) (n := 1)).mp
            (by simpa only [pow_one] using hdenmax)
      have hdenval_not_le : ¬Valued.v
          (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤
            exp (-2 : ℤ) := by
        intro hval
        apply hdensq
        exact (v.mem_maximalIdeal_pow_iff (K := K) (x := x₀ - X₂) (n := 2)).mpr
          (by simpa [x₀] using hval)
      have hdenne : x - ((X₂ : v.adicCompletionIntegers K) :
          v.adicCompletion K) ≠ 0 := sub_ne_zero.mpr hxx
      obtain ⟨dd, hdd⟩ : ∃ dd : ℤ,
          Valued.v (x - ((X₂ : v.adicCompletionIntegers K) :
            v.adicCompletion K)) = exp dd :=
        ⟨_, (exp_log ((Valued.v).pos_iff.mpr hdenne).ne').symm⟩
      have hddle : dd ≤ -1 := by
        rwa [hdd, exp_le_exp] at hdenval_le
      have hddnotle : ¬dd ≤ -2 := by
        intro hle
        apply hdenval_not_le
        rwa [hdd, exp_le_exp]
      have hddeq : dd = -1 := by omega
      have hdenval : Valued.v
          (x - ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)) =
            exp (-1 : ℤ) := by rw [hdd, hddeq]
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
        simp [X₃, hreszero.1, hX₂res]
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

/-- The exact depth-two `a₆` branch supplies the exponent twelve used by the arithmetic
specializations: it is four times the checked triple. -/
theorem twelve_nsmul_mem_nonsingularReductionSubgroup_of_a₄_sq_a₆_sq_not_cube
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
    (ha₄sq : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₆sq : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₆notcube : W₀.a₆ ∉ maximalIdeal (v.adicCompletionIntegers K) ^ 3)
    (P : W.Point) :
    12 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  have hthree :=
    three_nsmul_mem_nonsingularReductionSubgroup_of_a₄_sq_a₆_sq_not_cube
      hW h2 h3 hspecial ha₄sq ha₆sq ha₆notcube P
  have hfour := (nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)).nsmul_mem hthree 4
  rw [← mul_nsmul] at hfour
  norm_num at hfour
  exact hfour

end MazurTorsion.EllipticCurve
