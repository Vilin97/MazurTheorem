/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TateShortCoefficientDepth
import MazurTorsion.EllipticCurve.TateTypeIVComponent

/-!
# The marked simple-root branch of the exceptional star cubic

For an integral short equation with `a₄ ∈ 𝔪²` and `a₆ ∈ 𝔪³`, a point specializing to the
cusp has coordinates `x = ϖ X` and `y ∈ 𝔪²`.  Removing the common factor `ϖ³` from its equation
gives the pointwise exceptional-cubic relation

`X̄³ + Ā X̄ + B̄ = 0`,

where `a₄ = ϖ² A` and `a₆ = ϖ³ B`.  This file proves exactly the branch needed downstream: if
the derivative `3 X̄² + Ā` at that marked root is nonzero, then the double of the marked point
has canonical nonsingular reduction.

The proof uses only the selected equation and its tangent formula.  It does not identify a
Kodaira symbol, construct a regular model, classify all roots, or assert component incidence or
cardinality.
-/

noncomputable section

open IsLocalRing

namespace MazurTorsion.EllipticCurve

open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

universe u v w

/-- Integral coordinates and coefficient quotients defining the exceptional cubic at one marked
point.  The root assertion is only for the displayed marked quotient `X`; no assertion about any
other root is bundled. -/
structure MarkedExceptionalCubicData
    {O : Type u} {F : Type v} [CommRing O] [IsLocalRing O]
    [Field F] [Algebra O F]
    (W₀ : WeierstrassCurve O) (W : WeierstrassCurve.Affine F) (P : W.Point) where
  uniformizer : O
  uniformizer_irreducible : Irreducible uniformizer
  x : O
  y : O
  nonsingular : W.Nonsingular (algebraMap O F x) (algebraMap O F y)
  point_eq : P = .some (algebraMap O F x) (algebraMap O F y) nonsingular
  X : O
  A : O
  B : O
  x_eq : x = uniformizer * X
  a₄_eq : W₀.a₄ = uniformizer ^ 2 * A
  a₆_eq : W₀.a₆ = uniformizer ^ 3 * B
  y_mem_maximalIdeal_sq : y ∈ maximalIdeal O ^ 2
  exceptionalCubic_root :
    residue O X ^ 3 + residue O A * residue O X + residue O B = 0

namespace MarkedExceptionalCubicData

variable {O : Type u} {F : Type v} [CommRing O] [IsLocalRing O]
  [Field F] [Algebra O F]
  {W₀ : WeierstrassCurve O} {W : WeierstrassCurve.Affine F} {P : W.Point}

/-- The derivative of the exceptional cubic at the bundled marked root. -/
def derivativeResidue (D : MarkedExceptionalCubicData W₀ W P) : ResidueField O :=
  residue O (3 * D.X ^ 2 + D.A)

end MarkedExceptionalCubicData

/-- A cusp-specializing integral point with the displayed coefficient quotients determines a
marked root of the exceptional cubic.  The square-depth assertion for `y` is the checked weighted
coordinate consequence of the short equation. -/
noncomputable def markedExceptionalCubicData_of_cusp
    {O : Type u} {F : Type v} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field F] [Algebra O F]
    (W₀ : WeierstrassCurve O) [W₀.IsShortNF]
    (W : WeierstrassCurve.Affine F)
    (ϖ : O) (hϖ : Irreducible ϖ)
    {x y X A B : O}
    (heq : W₀.toAffine.Equation x y)
    (hxy : W.Nonsingular (algebraMap O F x) (algebraMap O F y))
    (hx : x ∈ maximalIdeal O) (hy : y ∈ maximalIdeal O)
    (ha₄ : W₀.a₄ ∈ maximalIdeal O ^ 2)
    (ha₆ : W₀.a₆ ∈ maximalIdeal O ^ 3)
    (hx_eq : x = ϖ * X)
    (ha₄_eq : W₀.a₄ = ϖ ^ 2 * A)
    (ha₆_eq : W₀.a₆ = ϖ ^ 3 * B) :
    MarkedExceptionalCubicData W₀ W
      (.some (algebraMap O F x) (algebraMap O F y) hxy) := by
  have hy_sq : y ∈ maximalIdeal O ^ 2 :=
    y_mem_maximalIdeal_sq_of_short_equation_of_coefficient_divisibility
      W₀ heq hx hy ha₄ ha₆
  have hmax : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hy_div := hy_sq
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy_div
  let Y : O := Classical.choose hy_div
  have hY : y = ϖ ^ 2 * Y := Classical.choose_spec hy_div
  have heqshort : y ^ 2 = x ^ 3 + W₀.a₄ * x + W₀.a₆ := by
    have heq' := (WeierstrassCurve.Affine.equation_iff x y).mp heq
    simp only [WeierstrassCurve.a₁_of_isShortNF,
      WeierstrassCurve.a₂_of_isShortNF,
      WeierstrassCurve.a₃_of_isShortNF, zero_mul] at heq'
    simpa only [zero_add, add_zero] using heq'
  rw [hY, hx_eq, ha₄_eq, ha₆_eq] at heqshort
  have hfactored : ϖ ^ 3 * (ϖ * Y ^ 2) =
      ϖ ^ 3 * (X ^ 3 + A * X + B) := by
    calc
      ϖ ^ 3 * (ϖ * Y ^ 2) = (ϖ ^ 2 * Y) ^ 2 := by ring
      _ = (ϖ * X) ^ 3 + (ϖ ^ 2 * A) * (ϖ * X) + ϖ ^ 3 * B := heqshort
      _ = ϖ ^ 3 * (X ^ 3 + A * X + B) := by ring
  have hquotient : ϖ * Y ^ 2 = X ^ 3 + A * X + B :=
    mul_left_cancel₀ (pow_ne_zero 3 hϖ.ne_zero) hfactored
  have hϖmem : ϖ ∈ maximalIdeal O := by
    rw [hmax, Ideal.mem_span_singleton]
  have hϖzero : residue O ϖ = 0 := (residue_eq_zero_iff ϖ).mpr hϖmem
  have hroot : residue O X ^ 3 + residue O A * residue O X + residue O B = 0 := by
    have hmap := congrArg (residue O) hquotient.symm
    simpa [hϖzero] using hmap
  exact
    { uniformizer := ϖ
      uniformizer_irreducible := hϖ
      x := x
      y := y
      nonsingular := hxy
      point_eq := rfl
      X := X
      A := A
      B := B
      x_eq := hx_eq
      a₄_eq := ha₄_eq
      a₆_eq := ha₆_eq
      y_mem_maximalIdeal_sq := hy_sq
      exceptionalCubic_root := hroot }

/-- A local point outside canonical nonsingular reduction supplies integral coordinates at the
cusp and hence marked exceptional-cubic data for any chosen uniformizer.  The returned data uses
that exact uniformizer. -/
theorem exists_markedExceptionalCubicData_of_not_hasNonsingularReduction
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
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ)
    (ha₄ : W₀.a₄ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 2)
    (ha₆ : W₀.a₆ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3)
    (P : W.Point) (hP : ¬HasNonsingularReduction hW P) :
    ∃ D : MarkedExceptionalCubicData W₀ W P, D.uniformizer = ϖ := by
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
  have hsingular : ¬(W₀.map
      (residue (v.adicCompletionIntegers K))).toAffine.Nonsingular
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
    have heqmap := WeierstrassCurve.Affine.Equation.map
      (residue (v.adicCompletionIntegers K)) heq₀
    change (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Equation
      (residue (v.adicCompletionIntegers K) x₀)
      (residue (v.adicCompletionIntegers K) y₀) at heqmap
    rwa [hspecial] at heqmap
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
  have hmax : maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  have hxdiv := hxmax
  rw [hmax, Ideal.mem_span_singleton] at hxdiv
  obtain ⟨X, hx_eq⟩ := hxdiv
  have ha₄div := ha₄
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha₄div
  obtain ⟨A, ha₄_eq⟩ := ha₄div
  have ha₆div := ha₆
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha₆div
  obtain ⟨B, ha₆_eq⟩ := ha₆div
  have hxy₀ : W.Nonsingular
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x₀)
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y₀) := by
    simpa [x₀, y₀] using hxy
  have hpoint : (.some x y hxy : W.Point) =
      .some (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x₀)
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) y₀) hxy₀ := by
    rw [Point.some.injEq]
    exact ⟨rfl, rfl⟩
  rw [hpoint]
  let D := markedExceptionalCubicData_of_cusp W₀ W ϖ hϖ heq₀ hxy₀
    hxmax hymax ha₄ ha₆ hx_eq ha₄_eq ha₆_eq
  exact ⟨D, rfl⟩

/-- If the bundled marked exceptional root is simple, the double of the marked local point has
canonical nonsingular reduction.  A deep ordinate makes the tangent slope have a pole; an
ordinate of exact depth two makes the tangent slope a unit and the double reduces away from the
cusp. -/
theorem two_nsmul_mem_nonsingularReductionSubgroup_of_markedExceptionalCubic_simpleRoot
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hsimple : D.derivativeResidue ≠ 0) :
    2 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  rcases D with ⟨ϖ, hϖ, x₀, y₀, hxy, hpoint, X, A, B,
    hx_eq, ha₄_eq, ha₆_eq, hy_sq, hroot⟩
  simp only [MarkedExceptionalCubicData.derivativeResidue] at hsimple
  change W.Nonsingular (x₀ : v.adicCompletion K)
    (y₀ : v.adicCompletion K) at hxy
  change P = .some (x₀ : v.adicCompletion K)
    (y₀ : v.adicCompletion K) hxy at hpoint
  rw [hpoint, two_nsmul]
  let H := nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)
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
  have hquotientUnit : IsUnit (3 * X ^ 2 + A) :=
    (residue_ne_zero_iff_isUnit (3 * X ^ 2 + A)).mp hsimple
  have hquotientVal : Valued.v
      (((3 * X ^ 2 + A : v.adicCompletionIntegers K) :
        v.adicCompletion K)) = 1 :=
    (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp
      hquotientUnit
  have hthreeCoe : (((3 : v.adicCompletionIntegers K) :
      v.adicCompletion K)) = 3 := by
    change algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) 3 = 3
    exact map_ofNat _ 3
  have hϖval : Valued.v ((ϖ : v.adicCompletionIntegers K) :
      v.adicCompletion K) = exp (-1 : ℤ) :=
    v.valued_irreducible_adicCompletionIntegers hϖ
  have hnumfactor :
      3 * ((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 + W.a₄ =
        ((ϖ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 *
          (((3 * X ^ 2 + A : v.adicCompletionIntegers K) :
            v.adicCompletion K)) := by
    rw [← ha₄coe, hx_eq, ha₄_eq]
    push_cast
    rw [hthreeCoe]
    ring
  have hnum : Valued.v
      (3 * ((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 + W.a₄) =
        exp (-2 : ℤ) := by
    rw [hnumfactor, map_mul, map_pow, hϖval, hquotientVal, mul_one,
      ← exp_nsmul]
    norm_num
  have htwoUnit : IsUnit (2 : v.adicCompletionIntegers K) :=
    (residue_ne_zero_iff_isUnit (2 : v.adicCompletionIntegers K)).mp (by
      simpa only [map_ofNat] using h2)
  have htwoval : Valued.v (2 : v.adicCompletion K) = 1 := by
    change Valued.v (((2 : v.adicCompletionIntegers K) :
      v.adicCompletion K)) = 1
    exact (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mp
      htwoUnit
  rcases eq_or_ne (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
      (W.negY (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) with
    hyneg | hyneg
  · rw [Point.add_self_of_Y_eq hyneg]
    exact H.zero_mem
  have hslope : W.slope
      (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
      (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
      (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
      (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)) =
        (3 * ((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K) ^ 2 + W.a₄) /
          (2 * ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)) := by
    rw [W.slope_of_Y_ne rfl hyneg, ha₁, ha₂]
    simp only [zero_mul, sub_zero]
    rw [WeierstrassCurve.Affine.negY, ha₁, ha₃]
    ring
  by_cases hydeep : y₀ ∈ maximalIdeal (v.adicCompletionIntegers K) ^ 3
  · have hyval : Valued.v ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ exp (-3 : ℤ) :=
      (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 3)).mp hydeep
    have hyne : ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
      intro hyzero
      apply hyneg
      rw [hyzero, WeierstrassCurve.Affine.negY, ha₁, ha₃]
      ring
    obtain ⟨dy, hdy⟩ : ∃ dy : ℤ,
        Valued.v ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K) = exp dy :=
      ⟨_, (exp_log ((Valued.v).pos_iff.mpr hyne).ne').symm⟩
    have hdy_le : dy ≤ -3 := by
      rwa [hdy, exp_le_exp] at hyval
    have hslopeval : exp (1 : ℤ) ≤ Valued.v (W.slope
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) := by
      rw [hslope, map_div₀, hnum, map_mul, htwoval, one_mul, hdy,
        ← exp_sub, exp_le_exp]
      omega
    exact filtration_le_nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW)
      (add_self_mem_filtration_of_slope hW hxy x₀.property hyneg hslopeval)
  · have hyval_le : Valued.v ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ exp (-2 : ℤ) :=
      (v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 2)).mp hy_sq
    have hyval_not_le : ¬Valued.v ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) ≤ exp (-3 : ℤ) := by
      intro hyval
      exact hydeep
        ((v.mem_maximalIdeal_pow_iff (K := K) (x := y₀) (n := 3)).mpr hyval)
    have hyne : ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
      intro hyzero
      apply hydeep
      have hy₀zero : y₀ = 0 := Subtype.ext hyzero
      rw [hy₀zero]
      exact Submodule.zero_mem _
    obtain ⟨dy, hdy⟩ : ∃ dy : ℤ,
        Valued.v ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K) = exp dy :=
      ⟨_, (exp_log ((Valued.v).pos_iff.mpr hyne).ne').symm⟩
    have hdy_le : dy ≤ -2 := by
      rwa [hdy, exp_le_exp] at hyval_le
    have hdy_not_le : ¬dy ≤ -3 := by
      intro hle
      apply hyval_not_le
      rwa [hdy, exp_le_exp]
    have hdy_eq : dy = -2 := by omega
    have hyval : Valued.v ((y₀ : v.adicCompletionIntegers K) :
        v.adicCompletion K) = exp (-2 : ℤ) := by rw [hdy, hdy_eq]
    have hslopeval : Valued.v (W.slope
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) = 1 := by
      rw [hslope, map_div₀, hnum, map_mul, htwoval, one_mul, hyval]
      exact div_self (exp_ne_zero : exp (-2 : ℤ) ≠ 0)
    let L : v.adicCompletionIntegers K :=
      ⟨W.slope
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
        (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)),
        hslopeval.le⟩
    have hLunit : IsUnit L :=
      (Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one.mpr
        hslopeval
    let X₂ : v.adicCompletionIntegers K := L ^ 2 - 2 * x₀
    let Y₂ : v.adicCompletionIntegers K := L * (x₀ - X₂) - y₀
    have hX₂ : ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        W.addX
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) := by
      change (W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
        (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K)) ^ 2 -
          2 * (x₀ : v.adicCompletion K) = _
      rw [WeierstrassCurve.Affine.addX, ha₁, ha₂]
      ring
    have hY₂ : ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        W.addY
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) := by
      change W.slope (x₀ : v.adicCompletion K) (x₀ : v.adicCompletion K)
          (y₀ : v.adicCompletion K) (y₀ : v.adicCompletion K) *
          ((x₀ : v.adicCompletion K) - (X₂ : v.adicCompletion K)) -
          (y₀ : v.adicCompletion K) = _
      rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY, ha₁, ha₃, hX₂]
      ring
    have hnot : ¬(((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K) =
        ((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K) ∧
        ((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K) =
          W.negY (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))) :=
      fun h ↦ hyneg h.2
    have hsum : W.Nonsingular
        (W.addX
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))))
        (W.addY
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)))) :=
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
      have heqmap := WeierstrassCurve.Affine.Equation.map
        (residue (v.adicCompletionIntegers K)) heq₂
      change (W₀.map (residue (v.adicCompletionIntegers K))).toAffine.Equation
        (residue (v.adicCompletionIntegers K) X₂)
        (residue (v.adicCompletionIntegers K) Y₂) at heqmap
      rwa [hspecial] at heqmap
    letI : Invertible (2 : ResidueField (v.adicCompletionIntegers K)) :=
      invertibleOfNonzero h2
    letI : Invertible (3 : ResidueField (v.adicCompletionIntegers K)) :=
      invertibleOfNonzero h3
    have hLres : residue (v.adicCompletionIntegers K) L ≠ 0 :=
      (residue_ne_zero_iff_isUnit L).mpr hLunit
    have hϖmax : ϖ ∈ maximalIdeal (v.adicCompletionIntegers K) := by
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    have hϖres : residue (v.adicCompletionIntegers K) ϖ = 0 :=
      (residue_eq_zero_iff ϖ).mpr hϖmax
    have hxres : residue (v.adicCompletionIntegers K) x₀ = 0 := by
      rw [hx_eq]
      simp [hϖres]
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
      (.some
        (W.addX
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))))
        (W.addY
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
          (W.slope
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)))) hsum)
    have hpoint₂ :
        (.some
          (W.addX
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (W.slope
              (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
              (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
              (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
              (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))))
          (W.addY
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
            (W.slope
              (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
              (((x₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
              (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K))
              (((y₀ : v.adicCompletionIntegers K) : v.adicCompletion K)))) hsum : W.Point) =
          .some ((X₂ : v.adicCompletionIntegers K) : v.adicCompletion K)
            ((Y₂ : v.adicCompletionIntegers K) : v.adicCompletion K) hsum' := by
      rw [Point.some.injEq]
      exact ⟨hX₂.symm, hY₂.symm⟩
    rw [hpoint₂]
    exact hred₂

/-- The simple-root branch supplies the exponent twelve required by the arithmetic consumers: it
is six times the checked double. -/
theorem twelve_nsmul_mem_nonsingularReductionSubgroup_of_markedExceptionalCubic_simpleRoot
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    [CharZero K]
    {v : HeightOneSpectrum R}
    {W : WeierstrassCurve.Affine (v.adicCompletion K)}
    {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)
    [W.IsElliptic] [DecidableEq (v.adicCompletion K)]
    [W₀.IsShortNF]
    (h2 : (2 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (h3 : (3 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (hspecial : W₀.map (residue (v.adicCompletionIntegers K)) =
      cuspidalShortCurve (ResidueField (v.adicCompletionIntegers K)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hsimple : D.derivativeResidue ≠ 0) :
    12 • P ∈ nonsingularReductionSubgroup hW
      (nonsingularReduction_isAdditive hW) := by
  have htwo :=
    two_nsmul_mem_nonsingularReductionSubgroup_of_markedExceptionalCubic_simpleRoot
      hW h2 h3 hspecial D hsimple
  have hsix := (nonsingularReductionSubgroup hW
    (nonsingularReduction_isAdditive hW)).nsmul_mem htwo 6
  rw [← mul_nsmul] at hsix
  norm_num at hsix
  exact hsix

end MazurTorsion.EllipticCurve
