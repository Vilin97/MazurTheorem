/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The tangent chart of Weierstrass doubling

This file constructs the affine principal-open chart on which
`2 * y + a₁ * x + a₃` is invertible.  Over an arbitrary commutative ring,
the denominator-cleared tangent equation makes the substituted Weierstrass
cubic factor with a double root at the source point.  Consequently the usual
doubling coordinates again satisfy the Weierstrass equation.

The resulting quotient-ring map is consumed by
`XZeroWeierstrassTangentAdditionMorphism`, which constructs an actual morphism
from this localization into the concrete projective cubic.  Nothing here
asserts a global group law, a cover by addition charts, compatibility on chart
overlaps, or gluing.
-/

noncomputable section

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {R : Type u} [CommRing R]

/-- The tangent-line factorization of the affine Weierstrass cubic, stated
without division over an arbitrary commutative ring. -/
private theorem addPolynomial_tangent_factorization
    (W : WeierstrassCurve R) (x y ℓ : R)
    (h : W.toAffine.Equation x y)
    (hℓ : ℓ * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) :
    W.toAffine.addPolynomial x y ℓ =
      -((Polynomial.X - Polynomial.C x) *
        (Polynomial.X - Polynomial.C x) *
        (Polynomial.X - Polynomial.C
          (W.toAffine.addX x x ℓ))) := by
  rw [WeierstrassCurve.Affine.addPolynomial_eq, neg_inj,
    Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective]
  rw [WeierstrassCurve.Affine.equation_iff] at h
  ext
  · rfl
  · simp only [WeierstrassCurve.Affine.addX]
    ring
  · simp only [WeierstrassCurve.Affine.addX]
    linear_combination -hℓ
  · simp only [WeierstrassCurve.Affine.addX]
    linear_combination x * hℓ - h

/-- A denominator-cleared tangent slope produces another point of the affine
Weierstrass equation over an arbitrary commutative ring. -/
private theorem equation_add_of_tangent
    (W : WeierstrassCurve R) (x y ℓ : R)
    (h : W.toAffine.Equation x y)
    (hℓ : ℓ * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) :
    W.toAffine.Equation
      (W.toAffine.addX x x ℓ)
      (W.toAffine.addY x x y ℓ) := by
  apply (W.toAffine.equation_neg _ _).mpr
  rw [WeierstrassCurve.Affine.equation_add_iff,
    addPolynomial_tangent_factorization W x y ℓ h hℓ]
  simp

/-! ## The principal-open coordinate ring -/

/-- The affine Weierstrass coordinate ring before tangent localization. -/
abbrev tangentSourceCoordinateRing {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :=
  Polynomial (Polynomial K) ⧸ Ideal.span {W.toAffine.polynomial}

/-- The structural coefficient map of the affine Weierstrass source. -/
def tangentSourceCoefficientHom {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : K →+* tangentSourceCoordinateRing W :=
  (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})).comp
    ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
      (Polynomial.C : K →+* Polynomial K))

/-- Universal abscissa in the affine Weierstrass coordinate ring. -/
def tangentSourceX {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentSourceCoordinateRing W :=
  Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
    (Polynomial.C Polynomial.X)

/-- Universal ordinate in the affine Weierstrass coordinate ring. -/
def tangentSourceY {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentSourceCoordinateRing W :=
  Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) Polynomial.X

/-- The tangent denominator `2y + a₁x + a₃` in the affine coordinate
ring. -/
def tangentDenominator {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentSourceCoordinateRing W :=
  2 * tangentSourceY W +
    tangentSourceCoefficientHom W W.a₁ * tangentSourceX W +
    tangentSourceCoefficientHom W W.a₃

/-- Coordinate ring of the principal open where the tangent denominator is
invertible. -/
abbrev tangentChartCoordinateRing {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :=
  Localization.Away (tangentDenominator W)

private def tangentCoordinate {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (q : tangentSourceCoordinateRing W) :
    tangentChartCoordinateRing W :=
  algebraMap (tangentSourceCoordinateRing W) (tangentChartCoordinateRing W) q

/-- The structural coefficient map of the tangent chart. -/
def tangentCoefficientHom {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : K →+* tangentChartCoordinateRing W :=
  (algebraMap (tangentSourceCoordinateRing W)
    (tangentChartCoordinateRing W)).comp (tangentSourceCoefficientHom W)

/-- The explicit coefficient map is the canonical algebra map. -/
theorem tangentCoefficientHom_eq_algebraMap
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    tangentCoefficientHom W = algebraMap K (tangentChartCoordinateRing W) := by
  rfl

/-- Universal abscissa on the tangent chart. -/
def tangentChartX {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentChartCoordinateRing W :=
  tangentCoordinate W (tangentSourceX W)

/-- Universal ordinate on the tangent chart. -/
def tangentChartY {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentChartCoordinateRing W :=
  tangentCoordinate W (tangentSourceY W)

/-- The tangent-chart abscissa is pulled back from the affine source
coordinate ring. -/
@[simp]
theorem tangentChartX_eq_algebraMap_sourceX
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    tangentChartX W =
      algebraMap (tangentSourceCoordinateRing W)
        (tangentChartCoordinateRing W) (tangentSourceX W) := by
  rfl

/-- The tangent-chart ordinate is pulled back from the affine source
coordinate ring. -/
@[simp]
theorem tangentChartY_eq_algebraMap_sourceY
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    tangentChartY W =
      algebraMap (tangentSourceCoordinateRing W)
        (tangentChartCoordinateRing W) (tangentSourceY W) := by
  rfl

/-- The universal denominator-cleared tangent numerator. -/
def tangentChartNumerator {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentChartCoordinateRing W :=
  let W' := W.map (tangentCoefficientHom W)
  3 * tangentChartX W ^ 2 + 2 * W'.a₂ * tangentChartX W +
    W'.a₄ - W'.a₁ * tangentChartY W

/-- The universal tangent slope on the principal open. -/
def tangentChartSlope {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentChartCoordinateRing W :=
  tangentChartNumerator W *
    IsLocalization.Away.invSelf (tangentDenominator W)

private def affineEquationExpression {K A : Type u}
    [CommRing K] [CommRing A] (W : WeierstrassCurve K)
    (c : K →+* A) (x y : A) : A :=
  y ^ 2 + c W.a₁ * x * y + c W.a₃ * y -
    (x ^ 3 + c W.a₂ * x ^ 2 + c W.a₄ * x + c W.a₆)

private theorem tangentSourcePolynomialEvaluation_eq_expression
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    Polynomial.eval₂
        (Polynomial.eval₂RingHom (tangentSourceCoefficientHom W)
          (tangentSourceX W))
        (tangentSourceY W) W.toAffine.polynomial =
      affineEquationExpression W (tangentSourceCoefficientHom W)
        (tangentSourceX W) (tangentSourceY W) := by
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    ← WeierstrassCurve.Affine.map_polynomial,
    (W.map (tangentSourceCoefficientHom W)).toAffine.evalEval_polynomial]
  rfl

private theorem tangentSource_equation {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    affineEquationExpression W (tangentSourceCoefficientHom W)
      (tangentSourceX W) (tangentSourceY W) = 0 := by
  rw [← tangentSourcePolynomialEvaluation_eq_expression]
  change (Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (tangentSourceCoefficientHom W)
        (tangentSourceX W)) (tangentSourceY W)) W.toAffine.polynomial = 0
  rw [show Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (tangentSourceCoefficientHom W)
          (tangentSourceX W)) (tangentSourceY W) =
      Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) by
    apply Polynomial.ringHom_ext
    · intro p
      have hinner : Polynomial.eval₂RingHom
          (tangentSourceCoefficientHom W) (tangentSourceX W) =
          (Ideal.Quotient.mk
            (Ideal.span {W.toAffine.polynomial})).comp Polynomial.C := by
        apply Polynomial.ringHom_ext
        · intro a
          simp [tangentSourceCoefficientHom]
        · simp [tangentSourceX]
      simpa using RingHom.congr_fun hinner p
    · simp [tangentSourceY]]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self _)

private theorem tangentChart_equation_source
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    (W.map (tangentCoefficientHom W)).toAffine.Equation
      (tangentChartX W) (tangentChartY W) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change affineEquationExpression W (tangentCoefficientHom W)
    (tangentChartX W) (tangentChartY W) = 0
  have h := congrArg
    (algebraMap (tangentSourceCoordinateRing W)
      (tangentChartCoordinateRing W)) (tangentSource_equation W)
  simpa [affineEquationExpression, tangentCoefficientHom,
    tangentChartX, tangentChartY, tangentCoordinate] using h

/-- The denominator expression on the tangent chart is the pullback of the
element inverted in its coordinate ring. -/
theorem tangentChartDenominator_eq
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    let W' := W.map (tangentCoefficientHom W)
    2 * tangentChartY W + W'.a₁ * tangentChartX W + W'.a₃ =
      algebraMap (tangentSourceCoordinateRing W)
        (tangentChartCoordinateRing W) (tangentDenominator W) := by
  simp [tangentDenominator, tangentChartX, tangentChartY,
    tangentCoordinate, tangentCoefficientHom]
  simp only [map_ofNat]

/-- The universal tangent slope satisfies the denominator-cleared tangent
equation. -/
theorem tangentChartSlope_mul_denominator
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    let W' := W.map (tangentCoefficientHom W)
    tangentChartSlope W *
        (2 * tangentChartY W + W'.a₁ * tangentChartX W + W'.a₃) =
      3 * tangentChartX W ^ 2 + 2 * W'.a₂ * tangentChartX W +
        W'.a₄ - W'.a₁ * tangentChartY W := by
  dsimp only
  rw [tangentChartSlope, tangentChartNumerator, mul_assoc,
    tangentChartDenominator_eq]
  change _ * (IsLocalization.Away.invSelf (tangentDenominator W) *
    algebraMap (tangentSourceCoordinateRing W) (tangentChartCoordinateRing W)
      (tangentDenominator W)) = _
  rw [mul_comm (IsLocalization.Away.invSelf (tangentDenominator W)),
    IsLocalization.Away.mul_invSelf, mul_one]

/-- The universal tangent formula is an actual point of the base-changed
affine cubic. -/
theorem tangentChart_equation_double {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    let W' := W.map (tangentCoefficientHom W)
    W'.toAffine.Equation
      (W'.toAffine.addX (tangentChartX W) (tangentChartX W)
        (tangentChartSlope W))
      (W'.toAffine.addY (tangentChartX W) (tangentChartX W)
        (tangentChartY W) (tangentChartSlope W)) := by
  dsimp only
  apply equation_add_of_tangent
  · exact tangentChart_equation_source W
  · exact tangentChartSlope_mul_denominator W

/-! ## The induced affine morphism -/

/-- Universal output abscissa of tangent doubling. -/
def tangentChartDoubleX {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentChartCoordinateRing W :=
  let W' := W.map (tangentCoefficientHom W)
  W'.toAffine.addX (tangentChartX W) (tangentChartX W)
    (tangentChartSlope W)

/-- Universal output ordinate of tangent doubling. -/
def tangentChartDoubleY {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) : tangentChartCoordinateRing W :=
  let W' := W.map (tangentCoefficientHom W)
  W'.toAffine.addY (tangentChartX W) (tangentChartX W)
    (tangentChartY W) (tangentChartSlope W)

private def tangentDoublingPolynomialEvaluation
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    Polynomial (Polynomial K) →+* tangentChartCoordinateRing W :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (tangentCoefficientHom W)
      (tangentChartDoubleX W)) (tangentChartDoubleY W)

private theorem tangentDoublingPolynomialEvaluation_eq_zero
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    tangentDoublingPolynomialEvaluation W W.toAffine.polynomial = 0 := by
  change Polynomial.eval₂
      (Polynomial.eval₂RingHom (tangentCoefficientHom W)
        (tangentChartDoubleX W))
      (tangentChartDoubleY W) W.toAffine.polynomial = 0
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    ← WeierstrassCurve.Affine.map_polynomial]
  simpa [tangentChartDoubleX, tangentChartDoubleY,
    WeierstrassCurve.Affine.Equation] using tangentChart_equation_double W

/-- Contravariant coordinate-ring map of tangent doubling on the principal
open `2y + a₁x + a₃ ≠ 0`. -/
def tangentDoublingToAffineRing {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    tangentSourceCoordinateRing W →+* tangentChartCoordinateRing W :=
  Ideal.Quotient.lift (Ideal.span {W.toAffine.polynomial})
    (tangentDoublingPolynomialEvaluation W) (by
      intro p hp
      apply (show Ideal.span {W.toAffine.polynomial} ≤
          RingHom.ker (tangentDoublingPolynomialEvaluation W) by
        apply Ideal.span_le.mpr
        intro q hq
        rw [Set.mem_singleton_iff.mp hq]
        exact tangentDoublingPolynomialEvaluation_eq_zero W) hp)

/-- The affine target's abscissa pulls back to the universal doubled
abscissa. -/
theorem tangentDoublingToAffineRing_abscissa
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    tangentDoublingToAffineRing W (tangentSourceX W) =
      tangentChartDoubleX W := by
  simp [tangentDoublingToAffineRing, tangentDoublingPolynomialEvaluation,
    tangentSourceX]

/-- The affine target's ordinate pulls back to the universal doubled
ordinate. -/
theorem tangentDoublingToAffineRing_ordinate
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    tangentDoublingToAffineRing W (tangentSourceY W) =
      tangentChartDoubleY W := by
  simp [tangentDoublingToAffineRing, tangentDoublingPolynomialEvaluation,
    tangentSourceY]

/-- Tangent doubling respects the structural coefficient maps. -/
@[simp]
theorem tangentDoublingToAffineRing_coefficient
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) (a : K) :
    tangentDoublingToAffineRing W (tangentSourceCoefficientHom W a) =
      tangentCoefficientHom W a := by
  simp [tangentDoublingToAffineRing, tangentDoublingPolynomialEvaluation,
    tangentSourceCoefficientHom, tangentCoefficientHom]

/-- Ring-hom form of compatibility with the base coefficients. -/
theorem tangentDoublingToAffineRing_comp_coefficient
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    (tangentDoublingToAffineRing W).comp (tangentSourceCoefficientHom W) =
      tangentCoefficientHom W := by
  ext a
  exact tangentDoublingToAffineRing_coefficient W a

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
