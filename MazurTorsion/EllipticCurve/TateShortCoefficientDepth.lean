/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.Ring

/-!
# Coefficient-divisibility identities for short Tate equations

This file records internal substitution identities for a short Weierstrass polynomial
`F(X, Y) = Y^2 - X^3 - a₄ X - a₆`.  A bundled witness records chosen powers of an element
dividing `a₄` and `a₆`.

The first three identities remove two factors from the total transform when
`a₄ = ϖ A₁` and `a₆ = ϖ² B₂`.  The remaining identities are the four weighted substitutions
used later in the tame Tate case split.  They remain private until such a case has a checked
consumer.  These are only polynomial identities: no universal property, regularity statement,
or strict-transform claim is made here.  The public result is the coordinate-divisibility
consequence currently needed as the next route handoff.
-/

namespace MazurTorsion.EllipticCurve

open IsLocalRing

universe u

variable {R : Type u} [CommRing R]

/-- Quotients witnessing prescribed `ϖ`-power divisibility of the two coefficients of a short
Weierstrass equation. -/
private structure ShortCoefficientDivisibilityData
    (W : WeierstrassCurve R) (ϖ : R) (a₄Power a₆Power : ℕ) where
  a₄Quotient : R
  a₆Quotient : R
  a₄_eq : W.a₄ = ϖ ^ a₄Power * a₄Quotient
  a₆_eq : W.a₆ = ϖ ^ a₆Power * a₆Quotient

namespace ShortCoefficientDivisibilityData

variable {W : WeierstrassCurve R} {ϖ : R}

/-- The quotient after removing two factors from the substitution `X = ϖ X₁`,
`Y = ϖ Y₁`, assuming coefficient divisibilities `(1, 2)`. -/
private def uniformizerTwoFactorQuotient
    (D : ShortCoefficientDivisibilityData W ϖ 1 2) (X₁ Y₁ : R) : R :=
  Y₁ ^ 2 - (ϖ * X₁ ^ 3 + D.a₄Quotient * X₁ + D.a₆Quotient)

/-- Exact two-factor total-transform identity for `X = ϖ X₁`, `Y = ϖ Y₁`. -/
private theorem evalEval_polynomial_uniformizer_twoFactor_factorization
    (D : ShortCoefficientDivisibilityData W ϖ 1 2) [W.IsShortNF] (X₁ Y₁ : R) :
    W.toAffine.polynomial.evalEval (ϖ * X₁) (ϖ * Y₁) =
      ϖ ^ 2 * D.uniformizerTwoFactorQuotient X₁ Y₁ := by
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₄_eq, D.a₆_eq]
  simp only [WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, zero_mul]
  simp only [uniformizerTwoFactorQuotient]
  ring

/-- Exact two-factor total-transform identity under `Y = X Y₁` and `ϖ = X P`. -/
private theorem evalEval_polynomial_x_twoFactor_factorization
    (D : ShortCoefficientDivisibilityData W ϖ 1 2) [W.IsShortNF]
    (X Y₁ P : R) (hϖ : ϖ = X * P) :
    W.toAffine.polynomial.evalEval X (X * Y₁) =
      X ^ 2 *
        (Y₁ ^ 2 - X - P * D.a₄Quotient - P ^ 2 * D.a₆Quotient) := by
  subst ϖ
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₄_eq, D.a₆_eq]
  simp only [WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, zero_mul]
  ring

/-- Exact two-factor total-transform identity under `X = Y X₁` and `ϖ = Y P`. -/
private theorem evalEval_polynomial_y_twoFactor_factorization
    (D : ShortCoefficientDivisibilityData W ϖ 1 2) [W.IsShortNF]
    (X₁ Y P : R) (hϖ : ϖ = Y * P) :
    W.toAffine.polynomial.evalEval (Y * X₁) Y =
      Y ^ 2 *
        (1 - Y * X₁ ^ 3 - P * D.a₄Quotient * X₁ -
          P ^ 2 * D.a₆Quotient) := by
  subst ϖ
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₄_eq, D.a₆_eq]
  simp only [WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, zero_mul]
  ring

/-- The `(2, 3)` coefficient-divisibility identity under `X = ϖ X₁`, `Y = ϖ² Y₁`. -/
private theorem evalEval_polynomial_weighted_factorization_of_divisibility_two_three
    (D : ShortCoefficientDivisibilityData W ϖ 2 3) [W.IsShortNF] (X₁ Y₁ : R) :
    W.toAffine.polynomial.evalEval (ϖ * X₁) (ϖ ^ 2 * Y₁) =
      ϖ ^ 3 *
        (ϖ * Y₁ ^ 2 - X₁ ^ 3 - D.a₄Quotient * X₁ - D.a₆Quotient) := by
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₄_eq, D.a₆_eq]
  simp only [WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, zero_mul]
  ring

/-- The `(3, 4)` coefficient-divisibility identity under `X = ϖ² X₁`, `Y = ϖ² Y₁`. -/
private theorem evalEval_polynomial_weighted_factorization_of_divisibility_three_four
    (D : ShortCoefficientDivisibilityData W ϖ 3 4) [W.IsShortNF] (X₁ Y₁ : R) :
    W.toAffine.polynomial.evalEval (ϖ ^ 2 * X₁) (ϖ ^ 2 * Y₁) =
      ϖ ^ 4 *
        (Y₁ ^ 2 - ϖ ^ 2 * X₁ ^ 3 - ϖ * D.a₄Quotient * X₁ -
          D.a₆Quotient) := by
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₄_eq, D.a₆_eq]
  simp only [WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, zero_mul]
  ring

/-- The `(3, 5)` coefficient-divisibility identity under `X = ϖ² X₁`, `Y = ϖ³ Y₁`. -/
private theorem evalEval_polynomial_weighted_factorization_of_divisibility_three_five
    (D : ShortCoefficientDivisibilityData W ϖ 3 5) [W.IsShortNF] (X₁ Y₁ : R) :
    W.toAffine.polynomial.evalEval (ϖ ^ 2 * X₁) (ϖ ^ 3 * Y₁) =
      ϖ ^ 5 *
        (ϖ * Y₁ ^ 2 - ϖ * X₁ ^ 3 - D.a₄Quotient * X₁ -
          D.a₆Quotient) := by
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₄_eq, D.a₆_eq]
  simp only [WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, zero_mul]
  ring

/-- The `(4, 6)` coefficient-divisibility identity under the full weight-`(2, 3)`
substitution. -/
private theorem evalEval_polynomial_weighted_factorization_of_divisibility_four_six
    (D : ShortCoefficientDivisibilityData W ϖ 4 6) [W.IsShortNF] (X₁ Y₁ : R) :
    W.toAffine.polynomial.evalEval (ϖ ^ 2 * X₁) (ϖ ^ 3 * Y₁) =
      ϖ ^ 6 *
        (Y₁ ^ 2 - X₁ ^ 3 - D.a₄Quotient * X₁ - D.a₆Quotient) := by
  rw [WeierstrassCurve.Affine.evalEval_polynomial, D.a₄_eq, D.a₆_eq]
  simp only [WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, zero_mul]
  ring

end ShortCoefficientDivisibilityData

/-- **Coordinate-divisibility handoff.**  On a short equation over a DVR, suppose an integral point
specializes to the cusp.  If `a₄ ∈ 𝔪²` and `a₆ ∈ 𝔪³`, then its `Y`-coordinate lies in `𝔪²`.

After writing `X = ϖ X₁` and `Y = ϖ Y₁`, the two-factor identity reduces modulo `ϖ` to
`Y₁² = 0`.  The residue field is a domain, hence `Y₁` also vanishes modulo `ϖ`. -/
theorem y_mem_maximalIdeal_sq_of_short_equation_of_coefficient_divisibility
    [IsDomain R] [IsDiscreteValuationRing R]
    (W : WeierstrassCurve R) [W.IsShortNF]
    {x y : R} (heq : W.toAffine.Equation x y)
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hy : y ∈ IsLocalRing.maximalIdeal R)
    (ha₄ : W.a₄ ∈ IsLocalRing.maximalIdeal R ^ 2)
    (ha₆ : W.a₆ ∈ IsLocalRing.maximalIdeal R ^ 3) :
    y ∈ IsLocalRing.maximalIdeal R ^ 2 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  rw [hmax, Ideal.mem_span_singleton] at hx hy
  rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha₄ ha₆
  obtain ⟨X₁, hX₁⟩ := hx
  obtain ⟨Y₁, hY₁⟩ := hy
  obtain ⟨A₂, hA₂⟩ := ha₄
  obtain ⟨B₃, hB₃⟩ := ha₆
  let D : ShortCoefficientDivisibilityData W ϖ 1 2 :=
    { a₄Quotient := ϖ * A₂
      a₆Quotient := ϖ * B₃
      a₄_eq := by
        rw [hA₂]
        ring
      a₆_eq := by
        rw [hB₃]
        ring }
  have hfactor := D.evalEval_polynomial_uniformizer_twoFactor_factorization X₁ Y₁
  have hquotient : D.uniformizerTwoFactorQuotient X₁ Y₁ = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 2 hϖ.ne_zero)
    rw [← hfactor, ← hX₁, ← hY₁]
    exact heq
  have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [hmax, Ideal.mem_span_singleton]
  have hϖzero : IsLocalRing.residue R ϖ = 0 :=
    (IsLocalRing.residue_eq_zero_iff ϖ).mpr hϖmem
  have hY₁sq : IsLocalRing.residue R Y₁ ^ 2 = 0 := by
    have hmap := congrArg (IsLocalRing.residue R) hquotient
    simpa [D, ShortCoefficientDivisibilityData.uniformizerTwoFactorQuotient,
      hϖzero] using hmap
  have hY₁zero : IsLocalRing.residue R Y₁ = 0 := by
    have hmul : IsLocalRing.residue R Y₁ * IsLocalRing.residue R Y₁ = 0 := by
      simpa [pow_two] using hY₁sq
    rcases mul_eq_zero.mp hmul with h | h <;> exact h
  have hY₁mem : Y₁ ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.residue_eq_zero_iff Y₁).mp hY₁zero
  rw [hY₁]
  simpa [pow_two] using Ideal.mul_mem_mul hϖmem hY₁mem

end MazurTorsion.EllipticCurve
