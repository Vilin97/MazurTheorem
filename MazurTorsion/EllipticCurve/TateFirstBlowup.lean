/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.CuspidalReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Affine charts for the first Tate blowup

Let `W` be an integral Weierstrass equation over a discrete valuation ring and suppose that all
five coefficients vanish on the special fibre.  After choosing a uniformizer `ϖ`, write each
coefficient as `ϖ bᵢ`.  This file records the quotients obtained after removing one exceptional
factor on the three standard affine charts of the blowup of the closed point `(ϖ, X, Y)`.

Mathlib does not yet provide a scheme-theoretic blowup API at the pinned revision.  Accordingly,
the interface here makes no universal-property or regularity claim: it gives the exact three
coordinate substitutions, factors the total transform once by the exceptional coordinate, and
computes the resulting equations on each exceptional chart.  If the original equation has
higher order at the center, this one-factor quotient need not yet be the scheme-theoretic strict
transform.  These identities are the reusable algebraic input for the subsequent valuation case
split in Tate's algorithm.
-/

namespace MazurTorsion.EllipticCurve

open IsLocalRing

universe u v

variable {R : Type u} [CommRing R]

/-- Quotients `bᵢ` witnessing `aᵢ = ϖ bᵢ` for an integral Weierstrass equation. -/
structure FirstBlowupCoefficientData (W : WeierstrassCurve R) (ϖ : R) where
  b₁ : R
  b₂ : R
  b₃ : R
  b₄ : R
  b₆ : R
  a₁_eq : W.a₁ = ϖ * b₁
  a₂_eq : W.a₂ = ϖ * b₂
  a₃_eq : W.a₃ = ϖ * b₃
  a₄_eq : W.a₄ = ϖ * b₄
  a₆_eq : W.a₆ = ϖ * b₆

namespace FirstBlowupCoefficientData

variable {W : WeierstrassCurve R} {ϖ : R}

/-- The one-factor quotient on the chart where the uniformizer is the exceptional coordinate,
obtained from `X = ϖ X₁` and `Y = ϖ Y₁` after removing one factor of `ϖ`. -/
def uniformizerChartQuotient
    (D : FirstBlowupCoefficientData W ϖ) (X₁ Y₁ : R) : R :=
  ϖ * Y₁ ^ 2 + ϖ ^ 2 * D.b₁ * X₁ * Y₁ + ϖ * D.b₃ * Y₁ -
    (ϖ ^ 2 * X₁ ^ 3 + ϖ ^ 2 * D.b₂ * X₁ ^ 2 + ϖ * D.b₄ * X₁ + D.b₆)

/-- The one-factor quotient on the `X`-exceptional chart.  Its coordinates satisfy `Y = X Y₁`
and `ϖ = X P`; the latter relation is an explicit premise of the factorization theorem below. -/
private def xChartQuotient
    (D : FirstBlowupCoefficientData W ϖ) (X Y₁ P : R) : R :=
  X * Y₁ ^ 2 + X ^ 2 * P * D.b₁ * Y₁ + X * P * D.b₃ * Y₁ -
    (X ^ 2 + X ^ 2 * P * D.b₂ + X * P * D.b₄ + P * D.b₆)

/-- The one-factor quotient on the `Y`-exceptional chart.  Its coordinates satisfy `X = Y X₁`
and `ϖ = Y P`; the latter relation is an explicit premise of the factorization theorem below. -/
private def yChartQuotient
    (D : FirstBlowupCoefficientData W ϖ) (X₁ Y P : R) : R :=
  Y + Y ^ 2 * P * D.b₁ * X₁ + Y * P * D.b₃ -
    (Y ^ 2 * X₁ ^ 3 + Y ^ 2 * P * D.b₂ * X₁ ^ 2 +
      Y * P * D.b₄ * X₁ + P * D.b₆)

/-- Exact total-transform factorization on the uniformizer-exceptional chart. -/
theorem evalEval_polynomial_uniformizerChart_factorization
    (D : FirstBlowupCoefficientData W ϖ) (X₁ Y₁ : R) :
    W.toAffine.polynomial.evalEval (ϖ * X₁) (ϖ * Y₁) =
      ϖ * D.uniformizerChartQuotient X₁ Y₁ := by
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₁_eq, D.a₂_eq,
    D.a₃_eq, D.a₄_eq, D.a₆_eq]
  simp only [uniformizerChartQuotient]
  ring

/-- Exact total-transform factorization on the `X`-exceptional chart. -/
private theorem evalEval_polynomial_xChart_factorization
    (D : FirstBlowupCoefficientData W ϖ) (X Y₁ P : R)
    (hϖ : ϖ = X * P) :
    W.toAffine.polynomial.evalEval X (X * Y₁) =
      X * D.xChartQuotient X Y₁ P := by
  subst ϖ
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₁_eq, D.a₂_eq,
    D.a₃_eq, D.a₄_eq, D.a₆_eq]
  simp only [xChartQuotient]
  ring

/-- Exact total-transform factorization on the `Y`-exceptional chart. -/
private theorem evalEval_polynomial_yChart_factorization
    (D : FirstBlowupCoefficientData W ϖ) (X₁ Y P : R)
    (hϖ : ϖ = Y * P) :
    W.toAffine.polynomial.evalEval (Y * X₁) Y =
      Y * D.yChartQuotient X₁ Y P := by
  subst ϖ
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₁_eq, D.a₂_eq,
    D.a₃_eq, D.a₄_eq, D.a₆_eq]
  simp only [yChartQuotient]
  ring

variable {S : Type v} [CommRing S]

/-- On the exceptional divisor of the uniformizer chart, the one-factor quotient restricts to
the negative residue of `b₆`. -/
theorem map_uniformizerChartQuotient_of_map_uniformizer_eq_zero
    (D : FirstBlowupCoefficientData W ϖ) (f : R →+* S)
    (hϖ : f ϖ = 0) (X₁ Y₁ : R) :
    f (D.uniformizerChartQuotient X₁ Y₁) = -f D.b₆ := by
  simp [uniformizerChartQuotient, hϖ]

/-- On the exceptional divisor of the `X`-chart, the one-factor quotient restricts to `-P b₆`. -/
private theorem map_xChartQuotient_of_map_exceptional_eq_zero
    (D : FirstBlowupCoefficientData W ϖ) (f : R →+* S)
    (X Y₁ P : R) (hX : f X = 0) :
    f (D.xChartQuotient X Y₁ P) = -(f P * f D.b₆) := by
  simp [xChartQuotient, hX]

/-- On the exceptional divisor of the `Y`-chart, the one-factor quotient restricts to `-P b₆`. -/
private theorem map_yChartQuotient_of_map_exceptional_eq_zero
    (D : FirstBlowupCoefficientData W ϖ) (f : R →+* S)
    (X₁ Y P : R) (hY : f Y = 0) :
    f (D.yChartQuotient X₁ Y P) = -(f P * f D.b₆) := by
  simp [yChartQuotient, hY]

/-- The exceptional restriction `b₆` is nonzero precisely in the order-one branch
`a₆ ∈ 𝔪 \ 𝔪²`.  This is the first valuation split following the one-factor chart
factorizations. -/
theorem residue_b₆_ne_zero_iff_a₆_not_mem_maximalIdeal_sq
    [IsDomain R] [IsDiscreteValuationRing R]
    (hϖ : Irreducible ϖ) (D : FirstBlowupCoefficientData W ϖ) :
    IsLocalRing.residue R D.b₆ ≠ 0 ↔
      W.a₆ ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  have hsquare : W.a₆ ∈ IsLocalRing.maximalIdeal R ^ 2 ↔
      D.b₆ ∈ IsLocalRing.maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton, D.a₆_eq, pow_two,
      mul_dvd_mul_iff_left hϖ.ne_zero]
  rw [not_congr hsquare]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit D.b₆).trans
    IsLocalRing.notMem_maximalIdeal.symm

end FirstBlowupCoefficientData

/-- On an integral short equation, a point whose two affine coordinates reduce to the cusp forces
`a₆` into the square of the maximal ideal.  This is the marked-point input for the first
order-one branch of the tame Tate calculation. -/
private theorem a₆_mem_maximalIdeal_sq_of_short_equation
    [IsLocalRing R]
    (W : WeierstrassCurve R) [W.IsShortNF]
    (ha₄ : W.a₄ ∈ IsLocalRing.maximalIdeal R)
    {x y : R} (heq : W.toAffine.Equation x y)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hy : y ∈ IsLocalRing.maximalIdeal R) :
    W.a₆ ∈ IsLocalRing.maximalIdeal R ^ 2 := by
  have heq' := (WeierstrassCurve.Affine.equation_iff x y).mp heq
  simp only [WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, zero_mul] at heq'
  have heq'' : y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
    simpa only [zero_add, add_zero] using heq'
  have hy2 : y ^ 2 ∈ IsLocalRing.maximalIdeal R ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hy hy
  have hx2 : x * x ∈ IsLocalRing.maximalIdeal R ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hx hx
  have hx3 : x ^ 3 ∈ IsLocalRing.maximalIdeal R ^ 2 := by
    have h := Ideal.mul_mem_left (IsLocalRing.maximalIdeal R ^ 2) x hx2
    simpa [pow_succ, mul_assoc] using h
  have ha4x : W.a₄ * x ∈ IsLocalRing.maximalIdeal R ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul ha₄ hx
  have ha6eq : W.a₆ = y ^ 2 - x ^ 3 - W.a₄ * x := by
    linear_combination -heq''
  rw [ha6eq]
  exact Ideal.sub_mem _ (Ideal.sub_mem _ hy2 hx3) ha4x

/-- Away from its affine origin, the standard cusp is nonsingular in characteristics different
from two and three. -/
private theorem cusp_nonsingular_aux
    {F : Type*} [Field F] [Invertible (2 : F)] [Invertible (3 : F)]
    {x y : F}
    (heq : (cuspidalShortCurve F).toAffine.Equation x y)
    (hne : x ≠ 0 ∨ y ≠ 0) :
    (cuspidalShortCurve F).toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨heq, ?_⟩
  rcases hne with hx | hy
  · left
    simpa [cuspidalShortCurve] using
      (mul_ne_zero (isUnit_of_invertible (3 : F)).ne_zero
        (pow_ne_zero 2 hx)).symm
  · right
    simp only [cuspidalShortCurve, zero_mul, sub_zero]
    intro h
    apply hy
    have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
    apply (mul_eq_zero.mp ?_).resolve_left h2
    linear_combination h

/-- **Order-one specialization endpoint.**  Let an integral short equation have standard
cuspidal special fibre.  If `a₄ ∈ 𝔪` and `a₆ ∉ 𝔪²`, then every integral affine point specializes
to a nonsingular point of the special fibre.

Indeed, simultaneous reduction of both coordinates to zero would force `a₆ ∈ 𝔪²` by the short
Weierstrass equation, while every other point of the standard cusp is nonsingular. -/
private theorem nonsingular_reduction_of_short_equation_of_a₆_not_mem_maximalIdeal_sq
    [IsLocalRing R]
    (W : WeierstrassCurve R) [W.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField R) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField R) ≠ 0)
    (hspecial : W.map (IsLocalRing.residue R) =
      cuspidalShortCurve (IsLocalRing.ResidueField R))
    (ha₄ : W.a₄ ∈ IsLocalRing.maximalIdeal R)
    (ha₆ : W.a₆ ∉ IsLocalRing.maximalIdeal R ^ 2)
    {x y : R} (heq : W.toAffine.Equation x y) :
    (W.map (IsLocalRing.residue R)).toAffine.Nonsingular
      (IsLocalRing.residue R x) (IsLocalRing.residue R y) := by
  have heqmap := WeierstrassCurve.Affine.Equation.map
    (IsLocalRing.residue R) heq
  change (W.map (IsLocalRing.residue R)).toAffine.Equation
    (IsLocalRing.residue R x) (IsLocalRing.residue R y) at heqmap
  have hne : IsLocalRing.residue R x ≠ 0 ∨
      IsLocalRing.residue R y ≠ 0 := by
    by_contra h
    have hnot := not_or.mp h
    have hx0 : IsLocalRing.residue R x = 0 := not_ne_iff.mp hnot.1
    have hy0 : IsLocalRing.residue R y = 0 := not_ne_iff.mp hnot.2
    apply ha₆
    exact a₆_mem_maximalIdeal_sq_of_short_equation W ha₄ heq
      ((IsLocalRing.residue_eq_zero_iff x).mp hx0)
      ((IsLocalRing.residue_eq_zero_iff y).mp hy0)
  letI : Invertible (2 : IsLocalRing.ResidueField R) := invertibleOfNonzero h2
  letI : Invertible (3 : IsLocalRing.ResidueField R) := invertibleOfNonzero h3
  rw [hspecial] at heqmap ⊢
  exact cusp_nonsingular_aux heqmap hne

/-- The three affine one-factor equation quotients attached to a choice of DVR uniformizer. -/
structure FirstBlowupEquationCharts
    (W : WeierstrassCurve R) [IsDomain R] [IsDiscreteValuationRing R] where
  uniformizer : R
  uniformizer_irreducible : Irreducible uniformizer
  coefficients : FirstBlowupCoefficientData W uniformizer

namespace FirstBlowupEquationCharts

variable [IsDomain R] [IsDiscreteValuationRing R] {W : WeierstrassCurve R}

/-- The uniformizer-chart factorization exposed directly from a bundled chart choice. -/
theorem evalEval_polynomial_uniformizerChart_factorization
    (B : FirstBlowupEquationCharts W) (X₁ Y₁ : R) :
    W.toAffine.polynomial.evalEval (B.uniformizer * X₁) (B.uniformizer * Y₁) =
      B.uniformizer * B.coefficients.uniformizerChartQuotient X₁ Y₁ :=
  B.coefficients.evalEval_polynomial_uniformizerChart_factorization X₁ Y₁

/-- The `X`-chart factorization exposed directly from a bundled chart choice. -/
private theorem evalEval_polynomial_xChart_factorization
    (B : FirstBlowupEquationCharts W) (X Y₁ P : R)
    (hϖ : B.uniformizer = X * P) :
    W.toAffine.polynomial.evalEval X (X * Y₁) =
      X * B.coefficients.xChartQuotient X Y₁ P :=
  B.coefficients.evalEval_polynomial_xChart_factorization X Y₁ P hϖ

/-- The `Y`-chart factorization exposed directly from a bundled chart choice. -/
private theorem evalEval_polynomial_yChart_factorization
    (B : FirstBlowupEquationCharts W) (X₁ Y P : R)
    (hϖ : B.uniformizer = Y * P) :
    W.toAffine.polynomial.evalEval (Y * X₁) Y =
      Y * B.coefficients.yChartQuotient X₁ Y P :=
  B.coefficients.evalEval_polynomial_yChart_factorization X₁ Y P hϖ

/-- The bundled coefficient quotient certifies that `a₄` lies in the maximal ideal. -/
theorem a₄_mem_maximalIdeal (B : FirstBlowupEquationCharts W) :
    W.a₄ ∈ IsLocalRing.maximalIdeal R := by
  rw [B.uniformizer_irreducible.maximalIdeal_eq,
    Ideal.mem_span_singleton, B.coefficients.a₄_eq]
  exact dvd_mul_right _ _

/-- For a bundled chart choice, nonvanishing of the exceptional `b₆` is exactly failure of
`a₆` to lie in the square of the maximal ideal. -/
theorem residue_b₆_ne_zero_iff_a₆_not_mem_maximalIdeal_sq
    (B : FirstBlowupEquationCharts W) :
    IsLocalRing.residue R B.coefficients.b₆ ≠ 0 ↔
      W.a₆ ∉ IsLocalRing.maximalIdeal R ^ 2 :=
  B.coefficients.residue_b₆_ne_zero_iff_a₆_not_mem_maximalIdeal_sq
    B.uniformizer_irreducible

/-- In the order-one `b₆ ≠ 0` branch, an integral point on a short equation cannot have both
affine coordinates reduce to the cusp. -/
theorem not_both_mem_maximalIdeal_of_residue_b₆_ne_zero
    (B : FirstBlowupEquationCharts W) [W.IsShortNF]
    {x y : R} (heq : W.toAffine.Equation x y)
    (hb₆ : IsLocalRing.residue R B.coefficients.b₆ ≠ 0) :
    ¬(x ∈ IsLocalRing.maximalIdeal R ∧
      y ∈ IsLocalRing.maximalIdeal R) := by
  rintro ⟨hx, hy⟩
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {B.uniformizer} :=
    B.uniformizer_irreducible.maximalIdeal_eq
  rw [hmax, Ideal.mem_span_singleton] at hx hy
  obtain ⟨X₁, hX₁⟩ := hx
  obtain ⟨Y₁, hY₁⟩ := hy
  have hfactor := B.evalEval_polynomial_uniformizerChart_factorization X₁ Y₁
  have heq' : W.toAffine.polynomial.evalEval x y = 0 := heq
  have hquotient : B.coefficients.uniformizerChartQuotient X₁ Y₁ = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left B.uniformizer_irreducible.ne_zero
    rw [← hfactor, ← hX₁, ← hY₁]
    exact heq'
  have hϖmem : B.uniformizer ∈ IsLocalRing.maximalIdeal R := by
    rw [hmax, Ideal.mem_span_singleton]
  have hϖzero : IsLocalRing.residue R B.uniformizer = 0 :=
    (IsLocalRing.residue_eq_zero_iff B.uniformizer).mpr hϖmem
  have hrestriction :=
    B.coefficients.map_uniformizerChartQuotient_of_map_uniformizer_eq_zero
      (IsLocalRing.residue R) hϖzero X₁ Y₁
  rw [hquotient, map_zero] at hrestriction
  exact hb₆ (neg_eq_zero.mp hrestriction.symm)

/-- In the order-one `b₆ ≠ 0` branch, every integral affine point on the bundled short equation
specializes to a nonsingular point of its standard cuspidal special fibre. -/
theorem nonsingular_reduction_of_equation_of_residue_b₆_ne_zero
    (B : FirstBlowupEquationCharts W) [W.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField R) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField R) ≠ 0)
    (hspecial : W.map (IsLocalRing.residue R) =
      cuspidalShortCurve (IsLocalRing.ResidueField R))
    {x y : R} (heq : W.toAffine.Equation x y)
    (hb₆ : IsLocalRing.residue R B.coefficients.b₆ ≠ 0) :
    (W.map (IsLocalRing.residue R)).toAffine.Nonsingular
      (IsLocalRing.residue R x) (IsLocalRing.residue R y) :=
  by
    have heqmap := WeierstrassCurve.Affine.Equation.map
      (IsLocalRing.residue R) heq
    change (W.map (IsLocalRing.residue R)).toAffine.Equation
      (IsLocalRing.residue R x) (IsLocalRing.residue R y) at heqmap
    have hne : IsLocalRing.residue R x ≠ 0 ∨
        IsLocalRing.residue R y ≠ 0 := by
      by_contra h
      have hnot := not_or.mp h
      apply B.not_both_mem_maximalIdeal_of_residue_b₆_ne_zero heq hb₆
      exact ⟨(IsLocalRing.residue_eq_zero_iff x).mp (not_ne_iff.mp hnot.1),
        (IsLocalRing.residue_eq_zero_iff y).mp (not_ne_iff.mp hnot.2)⟩
    letI : Invertible (2 : IsLocalRing.ResidueField R) := invertibleOfNonzero h2
    letI : Invertible (3 : IsLocalRing.ResidueField R) := invertibleOfNonzero h3
    rw [hspecial] at heqmap ⊢
    exact cusp_nonsingular_aux heqmap hne

end FirstBlowupEquationCharts

/-- Maximal-ideal divisibility of all five coefficients constructs the three affine first-blowup
charts, with no extra choice of coefficient quotients required from the caller. -/
theorem nonempty_firstBlowupEquationCharts_of_coefficients_mem_maximalIdeal
    [IsDomain R] [IsDiscreteValuationRing R]
    (W : WeierstrassCurve R)
    (ha₁ : W.a₁ ∈ IsLocalRing.maximalIdeal R)
    (ha₂ : W.a₂ ∈ IsLocalRing.maximalIdeal R)
    (ha₃ : W.a₃ ∈ IsLocalRing.maximalIdeal R)
    (ha₄ : W.a₄ ∈ IsLocalRing.maximalIdeal R)
    (ha₆ : W.a₆ ∈ IsLocalRing.maximalIdeal R) :
    Nonempty (FirstBlowupEquationCharts W) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  rw [hmax, Ideal.mem_span_singleton] at ha₁ ha₂ ha₃ ha₄ ha₆
  obtain ⟨b₁, hb₁⟩ := ha₁
  obtain ⟨b₂, hb₂⟩ := ha₂
  obtain ⟨b₃, hb₃⟩ := ha₃
  obtain ⟨b₄, hb₄⟩ := ha₄
  obtain ⟨b₆, hb₆⟩ := ha₆
  exact ⟨⟨ϖ, hϖ, ⟨b₁, b₂, b₃, b₄, b₆, hb₁, hb₂, hb₃, hb₄, hb₆⟩⟩⟩

end MazurTorsion.EllipticCurve
