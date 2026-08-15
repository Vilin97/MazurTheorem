/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The secant chart of Weierstrass addition

This file records the first genuine coordinate-chart prerequisite for the multiplication morphism
on the concrete projective Weierstrass cubic.  Over an arbitrary commutative ring, two affine
points together with an element inverse to their difference of abscissas determine the usual
secant slope.  The checked polynomial identity below shows that the chord-and-tangent formula
lands on the same Weierstrass equation without using field division or a supplied group-object
structure.

The induced quotient-ring map is consumed by `XZeroWeierstrassSecantAdditionMorphism`, where it
defines an actual morphism from the explicit principal-open presentation into the concrete
projective cubic.  Global multiplication still requires identifying this presentation with the
corresponding open of the scheme product, constructing the tangent and infinity charts, and
scheme-level gluing.
-/

noncomputable section

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {R : Type u} [CommRing R]

/-- The secant-line factorization of the affine Weierstrass cubic.  Unlike the field-level
addition theorem, the slope is characterized by its denominator-cleared equation, which is the
form needed on a localized affine product chart. -/
private theorem addPolynomial_secant_factorization
    (W : WeierstrassCurve R) (x₁ x₂ y₁ y₂ ℓ : R)
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂)
    (hunit : IsUnit (x₁ - x₂)) :
    W.toAffine.addPolynomial x₁ y₁ ℓ =
      -((Polynomial.X - Polynomial.C x₁) *
        (Polynomial.X - Polynomial.C x₂) *
        (Polynomial.X - Polynomial.C (W.toAffine.addX x₁ x₂ ℓ))) := by
  rw [WeierstrassCurve.Affine.addPolynomial_eq, neg_inj,
    Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective]
  rw [WeierstrassCurve.Affine.equation_iff] at h₁ h₂
  ext
  · rfl
  · simp only [WeierstrassCurve.Affine.addX]
    ring
  · simp only [WeierstrassCurve.Affine.addX]
    apply hunit.mul_left_cancel
    linear_combination
      (-W.a₁ * x₂ - W.a₃ + ℓ * x₁ - ℓ * x₂ - y₁ - y₂) * hℓ - h₁ + h₂
  · simp only [WeierstrassCurve.Affine.addX]
    apply hunit.mul_left_cancel
    linear_combination
      -x₁ * (-W.a₁ * x₂ - W.a₃ + ℓ * x₁ - ℓ * x₂ - y₁ - y₂) * hℓ +
        x₂ * h₁ - x₁ * h₂

/-- The denominator-cleared secant formula lands on the affine Weierstrass equation over an
arbitrary commutative ring.  This is the algebraic input for the corresponding morphism from the
principal open in the affine product. -/
private theorem equation_add_of_secant
    (W : WeierstrassCurve R) (x₁ x₂ y₁ y₂ ℓ : R)
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hℓ : ℓ * (x₁ - x₂) = y₁ - y₂)
    (hunit : IsUnit (x₁ - x₂)) :
    W.toAffine.Equation
      (W.toAffine.addX x₁ x₂ ℓ)
      (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  apply (W.toAffine.equation_neg _ _).mpr
  rw [WeierstrassCurve.Affine.equation_add_iff,
    addPolynomial_secant_factorization W x₁ x₂ y₁ y₂ ℓ h₁ h₂ hℓ hunit]
  simp

/-! ## The principal-open coordinate ring -/

/-- Four affine coordinates for an ordered pair of Weierstrass points. -/
private abbrev secantPairPolynomialRing (K : Type u) [CommRing K] :=
  MvPolynomial (Fin 4) K

private abbrev secantX₁ {K : Type u} [CommRing K] : secantPairPolynomialRing K :=
  MvPolynomial.X 0

private abbrev secantY₁ {K : Type u} [CommRing K] : secantPairPolynomialRing K :=
  MvPolynomial.X 1

private abbrev secantX₂ {K : Type u} [CommRing K] : secantPairPolynomialRing K :=
  MvPolynomial.X 2

private abbrev secantY₂ {K : Type u} [CommRing K] : secantPairPolynomialRing K :=
  MvPolynomial.X 3

/-- The affine Weierstrass equation evaluated at two elements of a coefficient algebra. -/
private def affineEquationExpression {K A : Type u} [CommRing K] [CommRing A]
    (W : WeierstrassCurve K) (c : K →+* A) (x y : A) : A :=
  y ^ 2 + c W.a₁ * x * y + c W.a₃ * y -
    (x ^ 3 + c W.a₂ * x ^ 2 + c W.a₄ * x + c W.a₆)

/-- The two equations cutting out the affine product `E × E` in four-space. -/
private def secantPairIdeal {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    Ideal (secantPairPolynomialRing K) :=
  Ideal.span {
    affineEquationExpression W MvPolynomial.C secantX₁ secantY₁,
    affineEquationExpression W MvPolynomial.C secantX₂ secantY₂ }

/-- Coordinate ring of the affine product before restricting to the secant locus. -/
private abbrev secantPairCoordinateRing {K : Type u} [CommRing K] (W : WeierstrassCurve K) :=
  secantPairPolynomialRing K ⧸ secantPairIdeal W

/-- Difference of the two universal abscissas in the affine product coordinate ring. -/
private def secantDenominator {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  Ideal.Quotient.mk (secantPairIdeal W) (secantX₁ - secantX₂)

/-- Coordinate ring of the principal open in `E × E` where `x₁ - x₂` is invertible. -/
abbrev secantChartCoordinateRing {K : Type u} [CommRing K] (W : WeierstrassCurve K) :=
  Localization.Away (secantDenominator W)

private def secantCoordinate {K : Type u} [CommRing K] (W : WeierstrassCurve K)
    (q : secantPairPolynomialRing K) : secantChartCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
    (Ideal.Quotient.mk (secantPairIdeal W) q)

/-- The structural coefficient map of the secant chart. -/
def secantCoefficientHom {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    K →+* secantChartCoordinateRing W :=
  (algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)).comp
    ((Ideal.Quotient.mk (secantPairIdeal W)).comp MvPolynomial.C)

/-- First universal abscissa on the secant chart. -/
def secantChartX₁ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W := secantCoordinate W secantX₁

/-- First universal ordinate on the secant chart. -/
def secantChartY₁ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W := secantCoordinate W secantY₁

/-- Second universal abscissa on the secant chart. -/
def secantChartX₂ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W := secantCoordinate W secantX₂

/-- Second universal ordinate on the secant chart. -/
def secantChartY₂ {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W := secantCoordinate W secantY₂

/-- The universal secant slope on the principal open. -/
def secantChartSlope {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W :=
  (secantChartY₁ W - secantChartY₂ W) *
    IsLocalization.Away.invSelf (secantDenominator W)

private theorem secantPairEquation_mem_left {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    affineEquationExpression W MvPolynomial.C secantX₁ secantY₁ ∈
      secantPairIdeal W := by
  apply Ideal.subset_span
  simp

private theorem secantPairEquation_mem_right {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    affineEquationExpression W MvPolynomial.C secantX₂ secantY₂ ∈
      secantPairIdeal W := by
  apply Ideal.subset_span
  simp

/-- The first universal point satisfies the base-changed Weierstrass equation. -/
private theorem secantChart_equation_left {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (W.map (secantCoefficientHom W)).toAffine.Equation
      (secantChartX₁ W) (secantChartY₁ W) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change affineEquationExpression W (secantCoefficientHom W)
      (secantChartX₁ W) (secantChartY₁ W) = 0
  have hzero : secantCoordinate W
      (affineEquationExpression W MvPolynomial.C secantX₁ secantY₁) = 0 := by
    rw [secantCoordinate,
      Ideal.Quotient.eq_zero_iff_mem.mpr (secantPairEquation_mem_left W), map_zero]
  simpa [affineEquationExpression, secantChartX₁, secantChartY₁,
    secantCoordinate, secantCoefficientHom] using hzero

/-- The second universal point satisfies the base-changed Weierstrass equation. -/
private theorem secantChart_equation_right {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (W.map (secantCoefficientHom W)).toAffine.Equation
      (secantChartX₂ W) (secantChartY₂ W) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change affineEquationExpression W (secantCoefficientHom W)
      (secantChartX₂ W) (secantChartY₂ W) = 0
  have hzero : secantCoordinate W
      (affineEquationExpression W MvPolynomial.C secantX₂ secantY₂) = 0 := by
    rw [secantCoordinate,
      Ideal.Quotient.eq_zero_iff_mem.mpr (secantPairEquation_mem_right W), map_zero]
  simpa [affineEquationExpression, secantChartX₂, secantChartY₂,
    secantCoordinate, secantCoefficientHom] using hzero

private theorem secantChartX₁_sub_X₂ {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantChartX₁ W - secantChartX₂ W =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (secantDenominator W) := by
  simp [secantChartX₁, secantChartX₂, secantCoordinate, secantDenominator]

/-- The universal slope satisfies its denominator-cleared secant equation. -/
private theorem secantChartSlope_mul_sub {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantChartSlope W * (secantChartX₁ W - secantChartX₂ W) =
      secantChartY₁ W - secantChartY₂ W := by
  rw [secantChartSlope, mul_assoc]
  rw [secantChartX₁_sub_X₂]
  change (secantChartY₁ W - secantChartY₂ W) *
      (IsLocalization.Away.invSelf (secantDenominator W) *
        algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
          (secantDenominator W)) = _
  rw [mul_comm (IsLocalization.Away.invSelf (secantDenominator W)),
    IsLocalization.Away.mul_invSelf, mul_one]

/-- The universal secant formula is an actual point of the base-changed affine cubic. -/
theorem secantChart_equation_add {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    let W' := W.map (secantCoefficientHom W)
    W'.toAffine.Equation
      (W'.toAffine.addX (secantChartX₁ W) (secantChartX₂ W)
        (secantChartSlope W))
      (W'.toAffine.addY (secantChartX₁ W) (secantChartX₂ W)
        (secantChartY₁ W) (secantChartSlope W)) := by
  dsimp only
  apply equation_add_of_secant
  · exact secantChart_equation_left W
  · exact secantChart_equation_right W
  · exact secantChartSlope_mul_sub W
  · rw [secantChartX₁_sub_X₂]
    exact IsLocalization.Away.algebraMap_isUnit (secantDenominator W)

/-! ## The induced affine morphism -/

/-- The target affine coordinate ring of the Weierstrass cubic. -/
private abbrev secantTargetCoordinateRing {K : Type u} [CommRing K] (W : WeierstrassCurve K) :=
  Polynomial (Polynomial K) ⧸ Ideal.span {W.toAffine.polynomial}

/-- The structural coefficient map of the affine Weierstrass target. -/
def secantTargetCoefficientHom {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    K →+* secantTargetCoordinateRing W :=
  (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})).comp
    ((Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)).comp
      (Polynomial.C : K →+* Polynomial K))

/-- The universal output abscissa of the secant formula. -/
def secantChartAddX {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W :=
  let W' := W.map (secantCoefficientHom W)
  W'.toAffine.addX (secantChartX₁ W) (secantChartX₂ W) (secantChartSlope W)

/-- The universal output ordinate of the secant formula. -/
def secantChartAddY {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantChartCoordinateRing W :=
  let W' := W.map (secantCoefficientHom W)
  W'.toAffine.addY (secantChartX₁ W) (secantChartX₂ W)
    (secantChartY₁ W) (secantChartSlope W)

private def secantAdditionPolynomialEvaluation {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    Polynomial (Polynomial K) →+* secantChartCoordinateRing W :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (secantCoefficientHom W) (secantChartAddX W))
    (secantChartAddY W)

private theorem secantAdditionPolynomialEvaluation_eq_zero
    {K : Type u} [CommRing K] (W : WeierstrassCurve K) :
    secantAdditionPolynomialEvaluation W W.toAffine.polynomial = 0 := by
  change Polynomial.eval₂
      (Polynomial.eval₂RingHom (secantCoefficientHom W) (secantChartAddX W))
      (secantChartAddY W) W.toAffine.polynomial = 0
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    ← WeierstrassCurve.Affine.map_polynomial]
  simpa [secantChartAddX, secantChartAddY,
    WeierstrassCurve.Affine.Equation] using secantChart_equation_add W

/-- The contravariant coordinate-ring map of secant addition on the principal open
`x₁ - x₂ ≠ 0` in the affine product. -/
def secantAdditionToAffineRing {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W →+* secantChartCoordinateRing W :=
  Ideal.Quotient.lift (Ideal.span {W.toAffine.polynomial})
    (secantAdditionPolynomialEvaluation W) (by
      intro p hp
      apply (show Ideal.span {W.toAffine.polynomial} ≤
          RingHom.ker (secantAdditionPolynomialEvaluation W) by
        apply Ideal.span_le.mpr
        intro q hq
        rw [Set.mem_singleton_iff.mp hq]
        exact secantAdditionPolynomialEvaluation_eq_zero W) hp)

/-- The affine target's abscissa pulls back to the universal secant abscissa. -/
theorem secantAdditionToAffineRing_abscissa {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantAdditionToAffineRing W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
          (Polynomial.C Polynomial.X)) =
      secantChartAddX W := by
  simp [secantAdditionToAffineRing, secantAdditionPolynomialEvaluation]

/-- The affine target's ordinate pulls back to the universal secant ordinate. -/
theorem secantAdditionToAffineRing_ordinate {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    secantAdditionToAffineRing W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) Polynomial.X) =
      secantChartAddY W := by
  simp [secantAdditionToAffineRing, secantAdditionPolynomialEvaluation]

/-- Secant addition respects the structural coefficient maps. -/
@[simp]
theorem secantAdditionToAffineRing_coefficient {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) (a : K) :
    secantAdditionToAffineRing W (secantTargetCoefficientHom W a) =
      secantCoefficientHom W a := by
  simp [secantAdditionToAffineRing, secantAdditionPolynomialEvaluation,
    secantTargetCoefficientHom, secantCoefficientHom]

/-- Ring-hom form of compatibility with the base coefficients. -/
theorem secantAdditionToAffineRing_comp_coefficient {K : Type u} [CommRing K]
    (W : WeierstrassCurve K) :
    (secantAdditionToAffineRing W).comp (secantTargetCoefficientHom W) =
      secantCoefficientHom W := by
  ext a
  exact secantAdditionToAffineRing_coefficient W a

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
