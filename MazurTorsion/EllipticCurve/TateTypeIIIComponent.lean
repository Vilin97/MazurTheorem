/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TateTypeIIComponent

/-!
# The marked double in the next tame Tate branch

Let an integral short Weierstrass equation over the valuation ring of an adic completion have
standard cuspidal special fibre.  After the first coefficient split, suppose the quotient of
`a₄` by a uniformizer has nonzero residue.  This file proves the precise pointwise consequence
needed downstream: the double of every local point has canonical nonsingular reduction.

For a point specializing to the cusp, the tangent numerator has valuation exactly one.  If the
ordinate has valuation at least two, the tangent slope has a pole and the double belongs to the
formal kernel.  Otherwise the slope is an integral unit, and the double reduces to
`(lambda^2, -lambda^3)` on `Y² = X³`, away from its singular origin.  No Kodaira symbol,
strict-transform assertion, regular model, or component-cardinality statement is made.
-/

noncomputable section

open IsLocalRing

namespace MazurTorsion.EllipticCurve

open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

universe u v

/-- In the `a₄/ϖ`-nonzero branch of a normalized tame equation, the double of every local point
belongs to the canonical nonsingular-reduction subgroup. -/
theorem two_nsmul_mem_nonsingularReductionSubgroup_of_firstBlowup_residue_b₄_ne_zero
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
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (hb₄ : residue (v.adicCompletionIntegers K) B.coefficients.b₄ ≠ 0)
    (P : W.Point) :
    2 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  rw [two_nsmul]
  let H := nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)
  by_cases hP : HasNonsingularReduction hW P
  · exact H.add_mem hP hP
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
  have hb₄unit : IsUnit B.coefficients.b₄ :=
    (residue_ne_zero_iff_isUnit B.coefficients.b₄).mp hb₄
  have hb₄val : Valued.v ((B.coefficients.b₄ :
      v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
    (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp
      hb₄unit
  have hϖval : Valued.v ((B.uniformizer : v.adicCompletionIntegers K) :
      v.adicCompletion K) = exp (-1 : ℤ) :=
    v.valued_irreducible_adicCompletionIntegers B.uniformizer_irreducible
  have ha₄val : Valued.v W.a₄ = exp (-1 : ℤ) := by
    rw [← ha₄coe, B.coefficients.a₄_eq]
    change Valued.v
      ((B.uniformizer : v.adicCompletion K) *
        (B.coefficients.b₄ : v.adicCompletion K)) = _
    rw [map_mul, hϖval, hb₄val, mul_one]
  have hxval : Valued.v x ≤ exp (-1 : ℤ) := by
    simpa [x₀] using
      (v.mem_maximalIdeal_pow_iff (K := K) (x := x₀) (n := 1)).mp
        (by simpa using hxmax)
  have hthree : Valued.v (3 : v.adicCompletion K) ≤ 1 := by
    change Valued.v (((3 : v.adicCompletionIntegers K) :
      v.adicCompletion K)) ≤ 1
    exact (3 : v.adicCompletionIntegers K).property
  have hsmall : Valued.v (3 * x ^ 2) < Valued.v W.a₄ := by
    rw [ha₄val]
    calc
      Valued.v (3 * x ^ 2) = Valued.v 3 * Valued.v x ^ 2 := by
        rw [map_mul, map_pow]
      _ ≤ 1 * exp (-1 : ℤ) ^ 2 :=
        mul_le_mul' hthree (pow_le_pow_left' hxval 2)
      _ = exp (-2 : ℤ) := by
        rw [one_mul, ← exp_nsmul]
        norm_num
      _ < exp (-1 : ℤ) := by rw [exp_lt_exp]; norm_num
  have hnum : Valued.v (3 * x ^ 2 + W.a₄) = exp (-1 : ℤ) := by
    rw [Valuation.map_add_eq_of_lt_right _ hsmall, ha₄val]
  have hyneg_or_ne : y = W.negY x y ∨ y ≠ W.negY x y := eq_or_ne _ _
  rcases hyneg_or_ne with hyneg | hyneg
  · rw [Point.add_self_of_Y_eq hyneg]
    exact H.zero_mem
  have hslope : W.slope x x y y = (3 * x ^ 2 + W.a₄) / (2 * y) := by
    rw [W.slope_of_Y_ne rfl hyneg, ha₁, ha₂]
    simp only [zero_mul, sub_zero]
    rw [WeierstrassCurve.Affine.negY, ha₁, ha₃]
    ring
  have htwoUnit : IsUnit (2 : v.adicCompletionIntegers K) :=
    (residue_ne_zero_iff_isUnit (2 : v.adicCompletionIntegers K)).mp (by
      simpa only [map_ofNat] using h2)
  have htwoval : Valued.v (2 : v.adicCompletion K) = 1 := by
    change Valued.v (((2 : v.adicCompletionIntegers K) :
      v.adicCompletion K)) = 1
    exact (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp
      htwoUnit
  by_cases hydeep : y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2
  · have hyval : Valued.v y ≤ exp (-2 : ℤ) := by
      simpa [y₀] using
        (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 2)).mp hydeep
    have hyne : y ≠ 0 := by
      intro hyzero
      apply hyneg
      rw [hyzero, WeierstrassCurve.Affine.negY, ha₁, ha₃]
      ring
    obtain ⟨dy, hdy⟩ : ∃ dy : ℤ, Valued.v y = exp dy :=
      ⟨_, (exp_log ((Valued.v).pos_iff.mpr hyne).ne').symm⟩
    have hdy_le : dy ≤ -2 := by
      rwa [hdy, exp_le_exp] at hyval
    have hslopeval : exp (1 : ℤ) ≤ Valued.v (W.slope x x y y) := by
      rw [hslope, map_div₀, hnum, map_mul, htwoval, one_mul, hdy,
        ← exp_sub, exp_le_exp]
      omega
    exact filtration_le_nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW)
      (add_self_mem_filtration_of_slope hW hxy hxyint.1 hyneg hslopeval)
  · have hyval_le : Valued.v y ≤ exp (-1 : ℤ) := by
      simpa [y₀] using
        (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 1)).mp
          (by simpa using hymax)
    have hyval_not_le : ¬Valued.v y ≤ exp (-2 : ℤ) := by
      intro hyval
      apply hydeep
      exact (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 2)).mpr
        (by simpa [y₀] using hyval)
    have hyne : y ≠ 0 := by
      intro hyzero
      apply hydeep
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
    have hslopeval : Valued.v (W.slope x x y y) = 1 := by
      rw [hslope, map_div₀, hnum, map_mul, htwoval, one_mul, hyval]
      exact div_self (exp_ne_zero : exp (-1 : ℤ) ≠ 0)
    let L : v.adicCompletionIntegers K := ⟨W.slope x x y y, hslopeval.le⟩
    have hLunit : IsUnit L :=
      (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mpr
        hslopeval
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
    have hnot : ¬(x = x ∧ y = W.negY x y) := fun h ↦ hyneg h.2
    have hsum : W.Nonsingular
        (W.addX x x (W.slope x x y y))
        (W.addY x x y (W.slope x x y y)) :=
      W.nonsingular_add hxy hxy hnot
    have hsum' : W.Nonsingular
        ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
        ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) := by
      rw [hX₂, hY₂]
      exact hsum
    have heq₂ : W₀.toAffine.Equation X₂ Y₂ :=
      equation_integral hW hsum'.left X₂.property Y₂.property
    have heq₂bar : (cuspidalShortCurve
        (ResidueField (v.adicCompletionIntegers K))).toAffine.Equation
        (residue (v.adicCompletionIntegers K) X₂)
        (residue (v.adicCompletionIntegers K) Y₂) := by
      have := WeierstrassCurve.Affine.Equation.map
        (residue (v.adicCompletionIntegers K)) heq₂
      change (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Equation
        (residue (v.adicCompletionIntegers K) X₂)
        (residue (v.adicCompletionIntegers K) Y₂) at this
      rwa [hspecial] at this
    have hLres : residue (v.adicCompletionIntegers K) L ≠ 0 :=
      (residue_ne_zero_iff_isUnit L).mpr hLunit
    have hX₂res : residue (v.adicCompletionIntegers K) X₂ =
        residue (v.adicCompletionIntegers K) L ^ 2 := by
      simp [X₂, hreszero.1]
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
        (.some ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
          ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) hsum') := by
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
      (.some (W.addX x x (W.slope x x y y))
        (W.addY x x y (W.slope x x y y)) hsum)
    have hpoint :
        (.some (W.addX x x (W.slope x x y y))
          (W.addY x x y (W.slope x x y y)) hsum : W.Point) =
        .some ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
          ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) hsum' := by
      rw [Point.some.injEq]
      exact ⟨hX₂.symm, hY₂.symm⟩
    rw [hpoint]
    exact hred₂

/-- The same branch supplies the uniform exponent twelve used by the arithmetic specialization
consumers: it is six times the checked double. -/
theorem twelve_nsmul_mem_nonsingularReductionSubgroup_of_firstBlowup_residue_b₄_ne_zero
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
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (hb₄ : residue (v.adicCompletionIntegers K) B.coefficients.b₄ ≠ 0)
    (P : W.Point) :
    12 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  have htwo :=
    two_nsmul_mem_nonsingularReductionSubgroup_of_firstBlowup_residue_b₄_ne_zero
      hW B h2 h3 hspecial hb₄ P
  have hsix := (nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)).nsmul_mem htwo 6
  rw [← mul_nsmul] at hsix
  norm_num at hsix
  exact hsix

end MazurTorsion.EllipticCurve
