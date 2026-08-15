/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassSecantAdditionMorphism
import MazurTorsion.ModularCurve.XZeroWeierstrassTangentAdditionMorphism
import Mathlib.Tactic.LinearCombination

/-!
# The product-neighbourhood chart of Weierstrass addition

The secant formula on `D(x₁ - x₂)` does not meet the diagonal.  This file
constructs the complementary affine product neighbourhood selected by

`B₁₂ = y₁ + y₂ + a₁x₁ + a₃`.

Its numerator

`A₁₂ = x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄ - a₁y₂`

satisfies the checked identity

`(y₁ - y₂)B₁₂ = (x₁ - x₂)A₁₂`.

Thus `A₁₂ / B₁₂` agrees with the existing secant slope on the genuine
intersection `D(B₁₂(x₁ - x₂))`.  On the diagonal, the same numerator and
denominator specialize to the checked tangent data.  We construct the
resulting morphism on `D(B₁₂)` and these two comparisons.  Nothing here
claims that the two affine charts cover the projective product, performs
scheme-level gluing, supplies infinity charts, or proves group laws.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

/-! ## Pair-coordinate numerator and denominator -/

variable {K : Type u} [CommRing K]

/-- The product-neighbourhood denominator
`B₁₂ = y₁ + y₂ + a₁x₁ + a₃`. -/
def additionB12 (W : WeierstrassCurve K) : secantPairCoordinateRing W :=
  secantPairY₁ W + secantPairY₂ W +
    secantPairCoefficientHom W W.a₁ * secantPairX₁ W +
    secantPairCoefficientHom W W.a₃

/-- The product-neighbourhood slope numerator
`A₁₂ = x₁² + x₁x₂ + x₂² + a₂(x₁ + x₂) + a₄ - a₁y₂`. -/
def additionA12 (W : WeierstrassCurve K) : secantPairCoordinateRing W :=
  secantPairX₁ W ^ 2 + secantPairX₁ W * secantPairX₂ W +
    secantPairX₂ W ^ 2 +
    secantPairCoefficientHom W W.a₂ *
      (secantPairX₁ W + secantPairX₂ W) +
    secantPairCoefficientHom W W.a₄ -
    secantPairCoefficientHom W W.a₁ * secantPairY₂ W

/-- Difference of the two universal curve equations, factored into the
exact numerator-denominator identity needed on the two addition charts. -/
theorem addition_pair_coordinate_identity (W : WeierstrassCurve K) :
    (secantPairY₁ W - secantPairY₂ W) * additionB12 W =
      (secantPairX₁ W - secantPairX₂ W) * additionA12 W := by
  have h₁ := secantPair_equation_left W
  have h₂ := secantPair_equation_right W
  rw [WeierstrassCurve.Affine.equation_iff] at h₁ h₂
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆] at h₁ h₂
  unfold additionB12 additionA12
  linear_combination h₁ - h₂

/-! ## The principal localization and its slope -/

/-- Coordinate ring of the product neighbourhood `D(B₁₂)`. -/
abbrev productNeighborhoodCoordinateRing (W : WeierstrassCurve K) :=
  Localization.Away (additionB12 W)

/-- Structural coefficient map of the product-neighbourhood chart. -/
def productNeighborhoodCoefficientHom (W : WeierstrassCurve K) :
    K →+* productNeighborhoodCoordinateRing W :=
  (algebraMap (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W)).comp
      (secantPairCoefficientHom W)

/-- The product-neighbourhood coefficient map is the canonical algebra map. -/
private theorem productNeighborhoodCoefficientHom_eq_algebraMap
    (W : WeierstrassCurve K) :
    productNeighborhoodCoefficientHom W =
      algebraMap K (productNeighborhoodCoordinateRing W) := by
  rw [productNeighborhoodCoefficientHom,
    secantPairCoefficientHom_eq_algebraMap]
  exact (IsScalarTower.algebraMap_eq K (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W)).symm

/-- First universal abscissa on `D(B₁₂)`. -/
def productNeighborhoodX₁ (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W) (secantPairX₁ W)

/-- First universal ordinate on `D(B₁₂)`. -/
def productNeighborhoodY₁ (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W) (secantPairY₁ W)

/-- Second universal abscissa on `D(B₁₂)`. -/
def productNeighborhoodX₂ (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W) (secantPairX₂ W)

/-- Second universal ordinate on `D(B₁₂)`. -/
def productNeighborhoodY₂ (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W) (secantPairY₂ W)

/-- Pullback of `A₁₂` to the product-neighbourhood chart. -/
def productNeighborhoodA12 (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W) (additionA12 W)

/-- Pullback of `B₁₂` to the product-neighbourhood chart. -/
def productNeighborhoodB12 (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (productNeighborhoodCoordinateRing W) (additionB12 W)

/-- The universal slope `A₁₂ / B₁₂` on `D(B₁₂)`. -/
def productNeighborhoodSlope (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  productNeighborhoodA12 W * IsLocalization.Away.invSelf (additionB12 W)

/-- The numerator-denominator identity after restriction to `D(B₁₂)`. -/
private theorem productNeighborhood_coordinate_identity (W : WeierstrassCurve K) :
    (productNeighborhoodY₁ W - productNeighborhoodY₂ W) *
        productNeighborhoodB12 W =
      (productNeighborhoodX₁ W - productNeighborhoodX₂ W) *
        productNeighborhoodA12 W := by
  simpa [productNeighborhoodX₁, productNeighborhoodX₂,
    productNeighborhoodY₁, productNeighborhoodY₂,
    productNeighborhoodA12, productNeighborhoodB12] using
      congrArg
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W))
        (addition_pair_coordinate_identity W)

/-- The `A₁₂ / B₁₂` slope satisfies the denominator-cleared secant equation
without requiring `x₁ - x₂` to be invertible. -/
theorem productNeighborhoodSlope_mul_sub (W : WeierstrassCurve K) :
    productNeighborhoodSlope W *
        (productNeighborhoodX₁ W - productNeighborhoodX₂ W) =
      productNeighborhoodY₁ W - productNeighborhoodY₂ W := by
  have h := productNeighborhood_coordinate_identity W
  calc
    productNeighborhoodSlope W *
        (productNeighborhoodX₁ W - productNeighborhoodX₂ W) =
      ((productNeighborhoodX₁ W - productNeighborhoodX₂ W) *
          productNeighborhoodA12 W) *
        IsLocalization.Away.invSelf (additionB12 W) := by
          simp only [productNeighborhoodSlope]
          ring
    _ = ((productNeighborhoodY₁ W - productNeighborhoodY₂ W) *
          productNeighborhoodB12 W) *
        IsLocalization.Away.invSelf (additionB12 W) := by rw [← h]
    _ = productNeighborhoodY₁ W - productNeighborhoodY₂ W := by
      rw [productNeighborhoodB12, mul_assoc,
        IsLocalization.Away.mul_invSelf, mul_one]

private theorem productNeighborhood_equation_left (W : WeierstrassCurve K) :
    (W.map (productNeighborhoodCoefficientHom W)).toAffine.Equation
      (productNeighborhoodX₁ W) (productNeighborhoodY₁ W) := by
  simpa [productNeighborhoodCoefficientHom, productNeighborhoodX₁,
    productNeighborhoodY₁, WeierstrassCurve.map_map] using
      (secantPair_equation_left W).map
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W))

private theorem productNeighborhood_equation_right (W : WeierstrassCurve K) :
    (W.map (productNeighborhoodCoefficientHom W)).toAffine.Equation
      (productNeighborhoodX₂ W) (productNeighborhoodY₂ W) := by
  simpa [productNeighborhoodCoefficientHom, productNeighborhoodX₂,
    productNeighborhoodY₂, WeierstrassCurve.map_map] using
      (secantPair_equation_right W).map
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W))

private theorem productNeighborhoodSlope_mul_B12 (W : WeierstrassCurve K) :
    productNeighborhoodSlope W * productNeighborhoodB12 W =
      productNeighborhoodA12 W := by
  rw [productNeighborhoodSlope, productNeighborhoodB12, mul_assoc,
    mul_comm (IsLocalization.Away.invSelf (additionB12 W)),
    IsLocalization.Away.mul_invSelf, mul_one]

/-! ## The addition formula on `D(B₁₂)` -/

private theorem addPolynomial_productNeighborhood_factorization
    (W : WeierstrassCurve K) (x₁ x₂ y₁ y₂ ℓ : K)
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hℓ : ℓ * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) +
        W.a₄ - W.a₁ * y₂)
    (hunit : IsUnit (y₁ + y₂ + W.a₁ * x₁ + W.a₃)) :
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
      (W.a₁ + ℓ) * h₂ - (W.a₁ + ℓ) * h₁ +
        (-W.a₁ * x₂ - W.a₃ + ℓ * x₁ - ℓ * x₂ - y₁ - y₂) * hℓ
  · simp only [WeierstrassCurve.Affine.addX]
    have hcoefficient :
        2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ +
            (-W.a₁ * y₁ + W.a₄) =
          x₁ * x₂ +
            x₁ * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) +
            x₂ * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) := by
      apply hunit.mul_left_cancel
      linear_combination
        (W.a₁ + ℓ) * h₂ - (W.a₁ + ℓ) * h₁ +
          (-W.a₁ * x₂ - W.a₃ + ℓ * x₁ - ℓ * x₂ - y₁ - y₂) * hℓ
    linear_combination -h₁ - x₁ * hcoefficient

private theorem equation_add_of_productNeighborhood
    (W : WeierstrassCurve K) (x₁ x₂ y₁ y₂ ℓ : K)
    (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂)
    (hℓ : ℓ * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) =
      x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) +
        W.a₄ - W.a₁ * y₂)
    (hunit : IsUnit (y₁ + y₂ + W.a₁ * x₁ + W.a₃)) :
    W.toAffine.Equation
      (W.toAffine.addX x₁ x₂ ℓ)
      (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  apply (W.toAffine.equation_neg _ _).mpr
  rw [WeierstrassCurve.Affine.equation_add_iff,
    addPolynomial_productNeighborhood_factorization W x₁ x₂ y₁ y₂ ℓ
      h₁ h₂ hℓ hunit]
  simp

/-- The `A₁₂ / B₁₂` formula is an actual point of the base-changed affine
Weierstrass cubic throughout `D(B₁₂)`. -/
theorem productNeighborhood_equation_add (W : WeierstrassCurve K) :
    let W' := W.map (productNeighborhoodCoefficientHom W)
    W'.toAffine.Equation
      (W'.toAffine.addX (productNeighborhoodX₁ W)
        (productNeighborhoodX₂ W) (productNeighborhoodSlope W))
      (W'.toAffine.addY (productNeighborhoodX₁ W)
        (productNeighborhoodX₂ W) (productNeighborhoodY₁ W)
        (productNeighborhoodSlope W)) := by
  dsimp only
  apply equation_add_of_productNeighborhood
  · exact productNeighborhood_equation_left W
  · exact productNeighborhood_equation_right W
  · simpa [productNeighborhoodB12, productNeighborhoodA12,
      additionB12, additionA12, productNeighborhoodX₁,
      productNeighborhoodX₂, productNeighborhoodY₁,
      productNeighborhoodY₂, productNeighborhoodCoefficientHom]
      using productNeighborhoodSlope_mul_B12 W
  · have hunit : IsUnit
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W) (additionB12 W)) :=
      IsLocalization.Away.algebraMap_isUnit (additionB12 W)
    simpa [productNeighborhoodB12, additionB12,
      productNeighborhoodX₁, productNeighborhoodY₁,
      productNeighborhoodY₂, productNeighborhoodCoefficientHom] using
        hunit

/-- Universal output abscissa of addition on `D(B₁₂)`. -/
def productNeighborhoodAddX (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  let W' := W.map (productNeighborhoodCoefficientHom W)
  W'.toAffine.addX (productNeighborhoodX₁ W)
    (productNeighborhoodX₂ W) (productNeighborhoodSlope W)

/-- Universal output ordinate of addition on `D(B₁₂)`. -/
def productNeighborhoodAddY (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W :=
  let W' := W.map (productNeighborhoodCoefficientHom W)
  W'.toAffine.addY (productNeighborhoodX₁ W)
    (productNeighborhoodX₂ W) (productNeighborhoodY₁ W)
    (productNeighborhoodSlope W)

private def productNeighborhoodAdditionPolynomialEvaluation
    (W : WeierstrassCurve K) :
    Polynomial (Polynomial K) →+* productNeighborhoodCoordinateRing W :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (productNeighborhoodCoefficientHom W)
      (productNeighborhoodAddX W))
    (productNeighborhoodAddY W)

private theorem productNeighborhoodAdditionPolynomialEvaluation_eq_zero
    (W : WeierstrassCurve K) :
    productNeighborhoodAdditionPolynomialEvaluation W
      W.toAffine.polynomial = 0 := by
  change Polynomial.eval₂
      (Polynomial.eval₂RingHom (productNeighborhoodCoefficientHom W)
        (productNeighborhoodAddX W))
      (productNeighborhoodAddY W) W.toAffine.polynomial = 0
  rw [Polynomial.eval₂_eval₂RingHom_apply,
    ← WeierstrassCurve.Affine.map_polynomial]
  simpa [productNeighborhoodAddX, productNeighborhoodAddY,
    WeierstrassCurve.Affine.Equation] using
      productNeighborhood_equation_add W

/-- Contravariant coordinate-ring map of addition on `D(B₁₂)`. -/
def productNeighborhoodAdditionToAffineRing (W : WeierstrassCurve K) :
    secantTargetCoordinateRing W →+* productNeighborhoodCoordinateRing W :=
  Ideal.Quotient.lift (Ideal.span {W.toAffine.polynomial})
    (productNeighborhoodAdditionPolynomialEvaluation W) (by
      intro p hp
      apply (show Ideal.span {W.toAffine.polynomial} ≤
          RingHom.ker (productNeighborhoodAdditionPolynomialEvaluation W) by
        apply Ideal.span_le.mpr
        intro q hq
        rw [Set.mem_singleton_iff.mp hq]
        exact productNeighborhoodAdditionPolynomialEvaluation_eq_zero W) hp)

/-- The affine target abscissa pulls back to the checked output abscissa on
`D(B₁₂)`. -/
theorem productNeighborhoodAdditionToAffineRing_abscissa
    (W : WeierstrassCurve K) :
    productNeighborhoodAdditionToAffineRing W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
          (Polynomial.C Polynomial.X)) =
      productNeighborhoodAddX W := by
  simp [productNeighborhoodAdditionToAffineRing,
    productNeighborhoodAdditionPolynomialEvaluation]

/-- The affine target ordinate pulls back to the checked output ordinate on
`D(B₁₂)`. -/
theorem productNeighborhoodAdditionToAffineRing_ordinate
    (W : WeierstrassCurve K) :
    productNeighborhoodAdditionToAffineRing W
        (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}) Polynomial.X) =
      productNeighborhoodAddY W := by
  simp [productNeighborhoodAdditionToAffineRing,
    productNeighborhoodAdditionPolynomialEvaluation]

/-- Product-neighbourhood addition respects the base coefficients. -/
@[simp]
theorem productNeighborhoodAdditionToAffineRing_coefficient
    (W : WeierstrassCurve K) (a : K) :
    productNeighborhoodAdditionToAffineRing W
        (secantTargetCoefficientHom W a) =
      productNeighborhoodCoefficientHom W a := by
  simp [productNeighborhoodAdditionToAffineRing,
    productNeighborhoodAdditionPolynomialEvaluation,
    secantTargetCoefficientHom, productNeighborhoodCoefficientHom]

/-- Ring-hom form of product-neighbourhood addition lying over the base. -/
private theorem productNeighborhoodAdditionToAffineRing_comp_coefficient
    (W : WeierstrassCurve K) :
    (productNeighborhoodAdditionToAffineRing W).comp
        (secantTargetCoefficientHom W) =
      productNeighborhoodCoefficientHom W := by
  ext a
  exact productNeighborhoodAdditionToAffineRing_coefficient W a

/-! ## Restriction to the diagonal tangent chart -/

/-- Comorphism of the diagonal from the affine-pair presentation to one
affine Weierstrass factor. -/
private noncomputable def secantPairDiagonalAlgHom (W : WeierstrassCurve K) :
    secantPairCoordinateRing W →ₐ[K] secantTargetCoordinateRing W :=
  (Algebra.TensorProduct.lift
    (AlgHom.id K (secantTargetCoordinateRing W))
    (AlgHom.id K (secantTargetCoordinateRing W))
    (fun _ _ => Commute.all _ _)).comp
      (secantPairTensorEquiv W).toAlgHom

@[simp]
private theorem secantPairDiagonalAlgHom_X₁ (W : WeierstrassCurve K) :
    secantPairDiagonalAlgHom W (secantPairX₁ W) = secantTargetX W := by
  simp [secantPairDiagonalAlgHom, secantPairTensorEquiv_X₁,
    Algebra.TensorProduct.lift_tmul]

@[simp]
private theorem secantPairDiagonalAlgHom_Y₁ (W : WeierstrassCurve K) :
    secantPairDiagonalAlgHom W (secantPairY₁ W) = secantTargetY W := by
  simp [secantPairDiagonalAlgHom, secantPairTensorEquiv_Y₁,
    Algebra.TensorProduct.lift_tmul]

@[simp]
private theorem secantPairDiagonalAlgHom_X₂ (W : WeierstrassCurve K) :
    secantPairDiagonalAlgHom W (secantPairX₂ W) = secantTargetX W := by
  simp [secantPairDiagonalAlgHom, secantPairTensorEquiv_X₂,
    Algebra.TensorProduct.lift_tmul]

@[simp]
private theorem secantPairDiagonalAlgHom_Y₂ (W : WeierstrassCurve K) :
    secantPairDiagonalAlgHom W (secantPairY₂ W) = secantTargetY W := by
  simp [secantPairDiagonalAlgHom, secantPairTensorEquiv_Y₂,
    Algebra.TensorProduct.lift_tmul]

@[simp]
private theorem secantPairDiagonalAlgHom_coefficient
    (W : WeierstrassCurve K) (a : K) :
    secantPairDiagonalAlgHom W (secantPairCoefficientHom W a) =
      secantTargetCoefficientHom W a := by
  rw [secantPairCoefficientHom_eq_algebraMap,
    (secantPairDiagonalAlgHom W).commutes,
    secantTargetCoefficientHom_eq_algebraMap]

/-- On the diagonal, `B₁₂` is the tangent denominator. -/
private theorem secantPairDiagonalAlgHom_B12 (W : WeierstrassCurve K) :
    secantPairDiagonalAlgHom W (additionB12 W) =
      2 * secantTargetY W +
        secantTargetCoefficientHom W W.a₁ * secantTargetX W +
        secantTargetCoefficientHom W W.a₃ := by
  simp only [additionB12, map_add, map_mul,
    secantPairDiagonalAlgHom_X₁, secantPairDiagonalAlgHom_Y₁,
    secantPairDiagonalAlgHom_Y₂, secantPairDiagonalAlgHom_coefficient]
  ring

/-- On the diagonal, `A₁₂` is the tangent numerator. -/
private theorem secantPairDiagonalAlgHom_A12 (W : WeierstrassCurve K) :
    secantPairDiagonalAlgHom W (additionA12 W) =
      3 * secantTargetX W ^ 2 +
        2 * secantTargetCoefficientHom W W.a₂ * secantTargetX W +
        secantTargetCoefficientHom W W.a₄ -
        secantTargetCoefficientHom W W.a₁ * secantTargetY W := by
  simp only [additionA12, map_add, map_sub, map_mul, map_pow,
    secantPairDiagonalAlgHom_X₁, secantPairDiagonalAlgHom_X₂,
    secantPairDiagonalAlgHom_Y₂, secantPairDiagonalAlgHom_coefficient]
  ring

private noncomputable def secantPairDiagonalToTangentChartAlgHom
    (W : WeierstrassCurve K) :
    secantPairCoordinateRing W →ₐ[K] tangentChartCoordinateRing W :=
  (Algebra.algHom K (tangentSourceCoordinateRing W)
    (tangentChartCoordinateRing W)).comp (secantPairDiagonalAlgHom W)

@[simp]
private theorem tangentAlgebraAlgHom_apply (W : WeierstrassCurve K)
    (a : tangentSourceCoordinateRing W) :
    Algebra.algHom K (tangentSourceCoordinateRing W)
        (tangentChartCoordinateRing W) a =
      algebraMap (tangentSourceCoordinateRing W)
        (tangentChartCoordinateRing W) a := by
  rfl

private theorem secantPairDiagonalToTangentChartAlgHom_B12
    (W : WeierstrassCurve K) :
    secantPairDiagonalToTangentChartAlgHom W (additionB12 W) =
      algebraMap (tangentSourceCoordinateRing W)
        (tangentChartCoordinateRing W) (tangentDenominator W) := by
  rw [secantPairDiagonalToTangentChartAlgHom, AlgHom.comp_apply,
    secantPairDiagonalAlgHom_B12]
  change algebraMap (tangentSourceCoordinateRing W)
      (tangentChartCoordinateRing W)
        (2 * tangentSourceY W +
          tangentSourceCoefficientHom W W.a₁ * tangentSourceX W +
          tangentSourceCoefficientHom W W.a₃) =
    algebraMap (tangentSourceCoordinateRing W)
      (tangentChartCoordinateRing W) (tangentDenominator W)
  rfl

/-- The diagonal comorphism extends from the pair coordinate ring to
`D(B₁₂)`, because `B₁₂` becomes the inverted tangent denominator. -/
private noncomputable def productNeighborhoodDiagonalAlgHom
    (W : WeierstrassCurve K) :
    productNeighborhoodCoordinateRing W →ₐ[K]
      tangentChartCoordinateRing W :=
  IsLocalization.Away.liftAlgHom (additionB12 W)
    (f := secantPairDiagonalToTangentChartAlgHom W) (by
      rw [secantPairDiagonalToTangentChartAlgHom_B12]
      exact IsLocalization.Away.algebraMap_isUnit (tangentDenominator W))

@[simp]
private theorem productNeighborhoodDiagonalAlgHom_algebraMap
    (W : WeierstrassCurve K) (a : secantPairCoordinateRing W) :
    productNeighborhoodDiagonalAlgHom W
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W) a) =
      secantPairDiagonalToTangentChartAlgHom W a := by
  simp [productNeighborhoodDiagonalAlgHom,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

@[simp]
private theorem productNeighborhoodDiagonalAlgHom_X₁
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodX₁ W) =
      tangentChartX W := by
  simp [productNeighborhoodX₁, secantPairDiagonalToTangentChartAlgHom,
    tangentChartX_eq_algebraMap_sourceX, tangentSourceX, secantTargetX]

@[simp]
private theorem productNeighborhoodDiagonalAlgHom_Y₁
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodY₁ W) =
      tangentChartY W := by
  simp [productNeighborhoodY₁, secantPairDiagonalToTangentChartAlgHom,
    tangentChartY_eq_algebraMap_sourceY, tangentSourceY, secantTargetY]

@[simp]
private theorem productNeighborhoodDiagonalAlgHom_X₂
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodX₂ W) =
      tangentChartX W := by
  simp [productNeighborhoodX₂, secantPairDiagonalToTangentChartAlgHom,
    tangentChartX_eq_algebraMap_sourceX, tangentSourceX, secantTargetX]

@[simp]
private theorem productNeighborhoodDiagonalAlgHom_Y₂
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodY₂ W) =
      tangentChartY W := by
  simp [productNeighborhoodY₂, secantPairDiagonalToTangentChartAlgHom,
    tangentChartY_eq_algebraMap_sourceY, tangentSourceY, secantTargetY]

@[simp]
private theorem productNeighborhoodDiagonalAlgHom_coefficient
    (W : WeierstrassCurve K) (a : K) :
    productNeighborhoodDiagonalAlgHom W
        (productNeighborhoodCoefficientHom W a) =
      tangentCoefficientHom W a := by
  rw [productNeighborhoodCoefficientHom_eq_algebraMap,
    tangentCoefficientHom_eq_algebraMap,
    (productNeighborhoodDiagonalAlgHom W).commutes]

private theorem productNeighborhoodDiagonalAlgHom_B12
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodB12 W) =
      algebraMap (tangentSourceCoordinateRing W)
        (tangentChartCoordinateRing W) (tangentDenominator W) := by
  rw [productNeighborhoodB12,
    productNeighborhoodDiagonalAlgHom_algebraMap,
    secantPairDiagonalToTangentChartAlgHom_B12]

private theorem productNeighborhoodDiagonalAlgHom_A12
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodA12 W) =
      tangentChartNumerator W := by
  rw [productNeighborhoodA12,
    productNeighborhoodDiagonalAlgHom_algebraMap,
    secantPairDiagonalToTangentChartAlgHom, AlgHom.comp_apply,
    secantPairDiagonalAlgHom_A12]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  simp [tangentChartNumerator, tangentChartX_eq_algebraMap_sourceX,
    tangentChartY_eq_algebraMap_sourceY, tangentCoefficientHom, tangentSourceX,
    tangentSourceY, tangentSourceCoefficientHom, secantTargetX,
    secantTargetY, secantTargetCoefficientHom]

/-- Named diagonal consumer: the `A₁₂ / B₁₂` slope restricts to the existing
tangent slope on the actual tangent principal open. -/
private theorem productNeighborhoodSlope_restrict_diagonal
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodSlope W) =
      tangentChartSlope W := by
  have hproduct := congrArg (productNeighborhoodDiagonalAlgHom W)
    (productNeighborhoodSlope_mul_B12 W)
  have hproduct' :
      productNeighborhoodDiagonalAlgHom W (productNeighborhoodSlope W) *
          algebraMap (tangentSourceCoordinateRing W)
            (tangentChartCoordinateRing W) (tangentDenominator W) =
        tangentChartNumerator W := by
    simpa [productNeighborhoodDiagonalAlgHom_B12,
      productNeighborhoodDiagonalAlgHom_A12] using hproduct
  have htangent := tangentChartSlope_mul_denominator W
  have htangent' :
      tangentChartSlope W *
          algebraMap (tangentSourceCoordinateRing W)
            (tangentChartCoordinateRing W) (tangentDenominator W) =
        tangentChartNumerator W := by
    rw [← tangentChartDenominator_eq W]
    simpa only [tangentChartNumerator] using htangent
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := tangentChartCoordinateRing W)
    (tangentDenominator W)).mul_right_cancel
  exact hproduct'.trans htangent'.symm

/-- The product-neighbourhood output abscissa restricts to the existing
tangent-doubling abscissa. -/
@[simp]
private theorem productNeighborhoodAddX_restrict_diagonal
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodAddX W) =
      tangentChartDoubleX W := by
  simp [productNeighborhoodAddX, tangentChartDoubleX,
    WeierstrassCurve.Affine.addX,
    productNeighborhoodSlope_restrict_diagonal]

/-- The product-neighbourhood output ordinate restricts to the existing
tangent-doubling ordinate. -/
@[simp]
private theorem productNeighborhoodAddY_restrict_diagonal
    (W : WeierstrassCurve K) :
    productNeighborhoodDiagonalAlgHom W (productNeighborhoodAddY W) =
      tangentChartDoubleY W := by
  simp [productNeighborhoodAddY, tangentChartDoubleY,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    productNeighborhoodSlope_restrict_diagonal]

/-- Ring-map form of diagonal compatibility: addition on `D(B₁₂)` followed
by diagonal restriction is the checked tangent-doubling map. -/
private theorem productNeighborhoodAdditionToAffineRing_comp_diagonal
    (W : WeierstrassCurve K) :
    (productNeighborhoodDiagonalAlgHom W).toRingHom.comp
        (productNeighborhoodAdditionToAffineRing W) =
      tangentDoublingToAffineRing W := by
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro p
    have hinner :
        ((((productNeighborhoodDiagonalAlgHom W).toRingHom.comp
            (productNeighborhoodAdditionToAffineRing W)).comp
              (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}))).comp
                Polynomial.C) =
          (((tangentDoublingToAffineRing W).comp
            (Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial}))).comp
              Polynomial.C) := by
      apply Polynomial.ringHom_ext
      · intro a
        change productNeighborhoodDiagonalAlgHom W
            (productNeighborhoodAdditionToAffineRing W
              (secantTargetCoefficientHom W a)) =
          tangentDoublingToAffineRing W (tangentSourceCoefficientHom W a)
        rw [productNeighborhoodAdditionToAffineRing_coefficient,
          tangentDoublingToAffineRing_coefficient,
          productNeighborhoodDiagonalAlgHom_coefficient]
      · change productNeighborhoodDiagonalAlgHom W
            (productNeighborhoodAdditionToAffineRing W (secantTargetX W)) =
          tangentDoublingToAffineRing W (tangentSourceX W)
        have hproductX :=
          productNeighborhoodAdditionToAffineRing_abscissa W
        change productNeighborhoodAdditionToAffineRing W (secantTargetX W) =
          productNeighborhoodAddX W at hproductX
        rw [hproductX, tangentDoublingToAffineRing_abscissa,
          productNeighborhoodAddX_restrict_diagonal]
    exact RingHom.congr_fun hinner p
  · change productNeighborhoodDiagonalAlgHom W
          (productNeighborhoodAdditionToAffineRing W (secantTargetY W)) =
        tangentDoublingToAffineRing W (tangentSourceY W)
    have hproductY := productNeighborhoodAdditionToAffineRing_ordinate W
    change productNeighborhoodAdditionToAffineRing W (secantTargetY W) =
      productNeighborhoodAddY W at hproductY
    rw [hproductY, tangentDoublingToAffineRing_ordinate,
      productNeighborhoodAddY_restrict_diagonal]

/-! ## The actual product open and its addition morphism -/

section Schemes

variable {F : Type u} [Field F]

/-- Affine scheme morphism induced by addition on `D(B₁₂)`. -/
def productNeighborhoodAdditionAffineMorphism (W : WeierstrassCurve F) :
    Spec (.of (productNeighborhoodCoordinateRing W)) ⟶
      Spec (.of (secantTargetCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom (productNeighborhoodAdditionToAffineRing W))

private theorem productNeighborhoodAdditionAffineMorphism_preimage
    (W : WeierstrassCurve F) :
    Spec.preimage (productNeighborhoodAdditionAffineMorphism W) =
      CommRingCat.ofHom (productNeighborhoodAdditionToAffineRing W) := by
  rw [productNeighborhoodAdditionAffineMorphism, Spec.preimage_map]

/-- The product-neighbourhood affine morphism pulls the target abscissa back
to the checked output coordinate. -/
theorem productNeighborhoodAdditionAffineMorphism_preimage_abscissa
    (W : WeierstrassCurve F) :
    (Spec.preimage (productNeighborhoodAdditionAffineMorphism W)).hom
        (secantTargetX W) = productNeighborhoodAddX W := by
  rw [productNeighborhoodAdditionAffineMorphism_preimage]
  exact productNeighborhoodAdditionToAffineRing_abscissa W

/-- The product-neighbourhood affine morphism pulls the target ordinate back
to the checked output coordinate. -/
theorem productNeighborhoodAdditionAffineMorphism_preimage_ordinate
    (W : WeierstrassCurve F) :
    (Spec.preimage (productNeighborhoodAdditionAffineMorphism W)).hom
        (secantTargetY W) = productNeighborhoodAddY W := by
  rw [productNeighborhoodAdditionAffineMorphism_preimage]
  exact productNeighborhoodAdditionToAffineRing_ordinate W

/-- Structure morphism of the product-neighbourhood chart. -/
def productNeighborhoodStructureMap (W : WeierstrassCurve F) :
    Spec (.of (productNeighborhoodCoordinateRing W)) ⟶ Spec (.of F) :=
  Spec.map (CommRingCat.ofHom (productNeighborhoodCoefficientHom W))

/-- Affine addition on `D(B₁₂)` lies over the ground field. -/
@[reassoc]
theorem productNeighborhoodAdditionAffineMorphism_comp_structureMap
    (W : WeierstrassCurve F) :
    productNeighborhoodAdditionAffineMorphism W ≫
        secantTargetStructureMap W =
      productNeighborhoodStructureMap W := by
  rw [productNeighborhoodAdditionAffineMorphism, secantTargetStructureMap,
    productNeighborhoodStructureMap, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  congr 1
  exact productNeighborhoodAdditionToAffineRing_comp_coefficient W

/-- The tangent chart maps to `D(B₁₂)` through the actual diagonal
comorphism `x₁,x₂ ↦ x` and `y₁,y₂ ↦ y`. -/
def tangentChartToProductNeighborhoodMorphism (W : WeierstrassCurve F) :
    Spec (.of (tangentChartCoordinateRing W)) ⟶
      Spec (.of (productNeighborhoodCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (productNeighborhoodDiagonalAlgHom W).toRingHom)

/-- Scheme-level diagonal compatibility on the affine target: restricting
addition on `D(B₁₂)` gives the existing tangent-doubling morphism. -/
theorem tangentChartToProductNeighborhoodMorphism_comp_additionAffine
    (W : WeierstrassCurve F) :
    tangentChartToProductNeighborhoodMorphism W ≫
        productNeighborhoodAdditionAffineMorphism W =
      tangentDoublingAffineMorphism W := by
  rw [tangentChartToProductNeighborhoodMorphism,
    productNeighborhoodAdditionAffineMorphism,
    tangentDoublingAffineMorphism, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp]
  congr 1
  exact productNeighborhoodAdditionToAffineRing_comp_diagonal W

/-- Localization map from `D(B₁₂)` into the four-coordinate affine-pair
presentation. -/
def productNeighborhoodToPair (W : WeierstrassCurve F) :
    Spec (.of (productNeighborhoodCoordinateRing W)) ⟶
      Spec (.of (secantPairCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (productNeighborhoodCoordinateRing W)))

instance productNeighborhoodToPair_isOpenImmersion
    (W : WeierstrassCurve F) :
    IsOpenImmersion (productNeighborhoodToPair W) := by
  dsimp only [productNeighborhoodToPair, productNeighborhoodCoordinateRing]
  infer_instance

/-- The localization map has precisely the principal-open range `D(B₁₂)`. -/
theorem productNeighborhoodToPair_opensRange (W : WeierstrassCurve F) :
    (productNeighborhoodToPair W).opensRange =
      PrimeSpectrum.basicOpen (additionB12 W) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (Localization.Away (additionB12 W))))).opensRange = _
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (secantPairCoordinateRing W)) (additionB12 W)

/-- The `D(B₁₂)` chart as an open subscheme of the genuine affine fibre
product of the two Weierstrass factors. -/
noncomputable def productNeighborhoodToAffineProduct
    (W : WeierstrassCurve F) :
    Spec (.of (productNeighborhoodCoordinateRing W)) ⟶ secantAffineProduct W :=
  productNeighborhoodToPair W ≫ (secantPairSchemeIsoAffineProduct W).hom

instance productNeighborhoodToAffineProduct_isOpenImmersion
    (W : WeierstrassCurve F) :
    IsOpenImmersion (productNeighborhoodToAffineProduct W) := by
  dsimp only [productNeighborhoodToAffineProduct]
  infer_instance

/-- The genuine product open represented by `D(B₁₂)`. -/
noncomputable def productNeighborhoodProductOpen (W : WeierstrassCurve F) :
    (secantAffineProduct W).Opens :=
  (productNeighborhoodToAffineProduct W).opensRange

/-- The explicit localization is canonically the corresponding open of the
actual affine product. -/
noncomputable def productNeighborhoodChartIsoProductOpen
    (W : WeierstrassCurve F) :
    Spec (.of (productNeighborhoodCoordinateRing W)) ≅
      (productNeighborhoodProductOpen W).toScheme :=
  IsOpenImmersion.isoOfRangeEq (productNeighborhoodToAffineProduct W)
    (productNeighborhoodProductOpen W).ι (by
      rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
      rfl)

/-- The chart isomorphism followed by the open inclusion recovers the
constructed immersion into the affine product. -/
theorem productNeighborhoodChartIsoProductOpen_hom_comp_ι
    (W : WeierstrassCurve F) :
    (productNeighborhoodChartIsoProductOpen W).hom ≫
        (productNeighborhoodProductOpen W).ι =
      productNeighborhoodToAffineProduct W := by
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem affineChartIso_comp_coveringStructureMap_productNeighborhood
    (W : WeierstrassCurve F) :
    (affineEquationSchemeIsoStandardChart W).hom ≫
      Spec.map (CommRingCat.ofHom (coveringChartStructureRingHom W true)) =
        secantTargetStructureMap W := by
  rw [show (affineEquationSchemeIsoStandardChart W).hom =
      Spec.map
        (affineEquationToStandardChartRingEquiv W).toCommRingCatIso.symm.hom
    from rfl]
  rw [secantTargetStructureMap, ← Spec.map_comp, Spec.map_inj]
  ext a
  change (affineEquationToStandardChartRingEquiv W).symm
      (coveringChartStructureRingHom W true a) =
    secantTargetCoefficientHom W a
  simp only [coveringChartStructureRingHom, coveringCoordinate,
    coveringChartIdeal, coveringChartEquation, secantTargetCoefficientHom,
    RingHom.coe_comp, Function.comp_apply]
  change (affineEquationToStandardChartRingEquiv W).symm
      (Ideal.Quotient.mk (standardChartIdeal W)
        (coordinateChartConstantHom (K := F) 2 a)) =
    Ideal.Quotient.mk (Ideal.span {W.toAffine.polynomial})
      (Polynomial.C (Polynomial.C a))
  apply (affineEquationToStandardChartRingEquiv W).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (standardChartIdeal W)
      (coordinateChartConstantHom (K := F) 2 a) =
    Ideal.Quotient.mk (standardChartIdeal W)
      (affineToStandardChart (K := F)
        (Polynomial.C (Polynomial.C a)))
  rw [affineToStandardChart_C_C]

private def standardProductNeighborhoodChartMap (W : WeierstrassCurve F) :
    standardAffineChartScheme W ⟶ scheme W :=
  coveringChartMap W true

/-- Addition on `D(B₁₂)` as a morphism into the concrete reduced projective
Weierstrass cubic. -/
def productNeighborhoodAdditionProjectiveMorphism
    (W : WeierstrassCurve F) :
    Spec (.of (productNeighborhoodCoordinateRing W)) ⟶ scheme W :=
  productNeighborhoodAdditionAffineMorphism W ≫
    (affineEquationSchemeIsoStandardChart W).hom ≫
    standardProductNeighborhoodChartMap W

/-- After the cubic's closed immersion, the product-neighbourhood formula is
the corresponding morphism into the ambient standard projective chart. -/
@[reassoc]
theorem productNeighborhoodAdditionProjectiveMorphism_comp_inclusion
    (W : WeierstrassCurve F) :
    productNeighborhoodAdditionProjectiveMorphism W ≫ inclusion W =
      productNeighborhoodAdditionAffineMorphism W ≫
        (affineEquationSchemeIsoStandardChart W).hom ≫
          coveringChartAmbientMap W true := by
  unfold productNeighborhoodAdditionProjectiveMorphism
  simp only [Category.assoc]
  congr 1
  congr 1
  exact coveringChartMap_comp_inclusion W true

/-- Product-neighbourhood addition regarded as a morphism from the genuine
open of the affine product. -/
noncomputable def productNeighborhoodAdditionOnProductOpen
    (W : WeierstrassCurve F) :
    (productNeighborhoodProductOpen W).toScheme ⟶ scheme W :=
  (productNeighborhoodChartIsoProductOpen W).inv ≫
    productNeighborhoodAdditionProjectiveMorphism W

/-- The projective chart morphism factors through the genuine product open. -/
theorem productNeighborhoodAdditionProjectiveMorphism_factors_through_productOpen
    (W : WeierstrassCurve F) :
    productNeighborhoodAdditionProjectiveMorphism W =
      (productNeighborhoodChartIsoProductOpen W).hom ≫
        productNeighborhoodAdditionOnProductOpen W := by
  simp [productNeighborhoodAdditionOnProductOpen]

/-- Projective addition on `D(B₁₂)` lies over the ground field. -/
theorem productNeighborhoodAdditionProjectiveMorphism_comp_structureMap
    (W : WeierstrassCurve F) :
    productNeighborhoodAdditionProjectiveMorphism W ≫ structureMap W =
      productNeighborhoodStructureMap W := by
  let chartStructureMap : standardAffineChartScheme W ⟶ Spec (.of F) :=
    Spec.map (CommRingCat.ofHom (coveringChartStructureRingHom W true))
  have hchart : standardProductNeighborhoodChartMap W ≫ structureMap W =
      chartStructureMap := coveringChartMap_comp_structureMap W true
  have htarget : (affineEquationSchemeIsoStandardChart W).hom ≫
      chartStructureMap = secantTargetStructureMap W :=
    affineChartIso_comp_coveringStructureMap_productNeighborhood W
  simp only [productNeighborhoodAdditionProjectiveMorphism,
    Category.assoc, hchart, htarget,
    productNeighborhoodAdditionAffineMorphism_comp_structureMap]

/-- The same diagonal restriction agrees with tangent doubling after mapping
to the concrete reduced projective cubic. -/
theorem tangentChartToProductNeighborhoodMorphism_comp_additionProjective
    (W : WeierstrassCurve F) :
    tangentChartToProductNeighborhoodMorphism W ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      tangentDoublingProjectiveMorphism W := by
  change tangentChartToProductNeighborhoodMorphism W ≫
      (productNeighborhoodAdditionAffineMorphism W ≫
        (affineEquationSchemeIsoStandardChart W).hom ≫
        standardProductNeighborhoodChartMap W) =
    tangentDoublingProjectiveMorphism W
  rw [← Category.assoc,
    tangentChartToProductNeighborhoodMorphism_comp_additionAffine]
  rfl

/-! ## The genuine intersection with the secant chart -/

/-- Coordinate ring of
`D(B₁₂) ∩ D(x₁ - x₂) = D(B₁₂(x₁ - x₂))`. -/
abbrev additionSecantIntersectionCoordinateRing
    (W : WeierstrassCurve F) :=
  Localization.Away (additionB12 W * secantDenominator W)

/-- The exact intersection localization mapped into the affine-pair
presentation. -/
def additionSecantIntersectionToPair (W : WeierstrassCurve F) :
    Spec (.of (additionSecantIntersectionCoordinateRing W)) ⟶
      Spec (.of (secantPairCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (additionSecantIntersectionCoordinateRing W)))

instance additionSecantIntersectionToPair_isOpenImmersion
    (W : WeierstrassCurve F) :
    IsOpenImmersion (additionSecantIntersectionToPair W) := by
  dsimp only [additionSecantIntersectionToPair,
    additionSecantIntersectionCoordinateRing]
  infer_instance

/-- The overlap localization has exactly the intersection of the two
principal-open ranges. -/
theorem additionSecantIntersectionToPair_opensRange
    (W : WeierstrassCurve F) :
    (additionSecantIntersectionToPair W).opensRange =
      PrimeSpectrum.basicOpen
        (additionB12 W * secantDenominator W) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (secantPairCoordinateRing W)
      (Localization.Away (additionB12 W * secantDenominator W))))).opensRange = _
  exact Scheme.Hom.opensRange_localizationAway
    (R := .of (secantPairCoordinateRing W))
    (additionB12 W * secantDenominator W)

/-- Algebraically, the overlap range is exactly
`D(B₁₂) ∩ D(x₁ - x₂)`. -/
theorem additionSecantIntersection_basicOpen
    (W : WeierstrassCurve F) :
    PrimeSpectrum.basicOpen (additionB12 W * secantDenominator W) =
      PrimeSpectrum.basicOpen (additionB12 W) ⊓
        PrimeSpectrum.basicOpen (secantDenominator W) :=
  PrimeSpectrum.basicOpen_mul _ _

/-- Restriction from the secant localization to the exact intersection
localization. -/
noncomputable def secantChartToAdditionSecantIntersectionRing
    (W : WeierstrassCurve F) :
    secantChartCoordinateRing W →+*
      additionSecantIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayLeft
    (S := secantChartCoordinateRing W)
    (P := additionSecantIntersectionCoordinateRing W)
    (secantDenominator W) (additionB12 W)

/-- Restriction from the `D(B₁₂)` localization to the exact intersection
localization. -/
noncomputable def productNeighborhoodToAdditionSecantIntersectionRing
    (W : WeierstrassCurve F) :
    productNeighborhoodCoordinateRing W →+*
      additionSecantIntersectionCoordinateRing W :=
  IsLocalization.Away.awayToAwayRight
    (S := productNeighborhoodCoordinateRing W)
    (P := additionSecantIntersectionCoordinateRing W)
    (additionB12 W) (secantDenominator W)

@[simp]
private theorem secantChartToAdditionSecantIntersectionRing_algebraMap
    (W : WeierstrassCurve F) (a : secantPairCoordinateRing W) :
    secantChartToAdditionSecantIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (secantChartCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (additionSecantIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayLeft_eq
    (S := secantChartCoordinateRing W)
    (P := additionSecantIntersectionCoordinateRing W)
    (secantDenominator W) (additionB12 W) a

@[simp]
private theorem productNeighborhoodToAdditionSecantIntersectionRing_algebraMap
    (W : WeierstrassCurve F) (a : secantPairCoordinateRing W) :
    productNeighborhoodToAdditionSecantIntersectionRing W
        (algebraMap (secantPairCoordinateRing W)
          (productNeighborhoodCoordinateRing W) a) =
      algebraMap (secantPairCoordinateRing W)
        (additionSecantIntersectionCoordinateRing W) a := by
  exact IsLocalization.Away.awayToAwayRight_eq
    (S := productNeighborhoodCoordinateRing W)
    (P := additionSecantIntersectionCoordinateRing W)
    (additionB12 W) (secantDenominator W) a

/-- Named compatibility consumer: `A₁₂ / B₁₂` and the existing secant slope
become literally equal on the genuine intersection
`D(B₁₂(x₁ - x₂))`. -/
theorem productNeighborhoodSlope_eq_secantSlope_on_intersection
    (W : WeierstrassCurve F) :
    productNeighborhoodToAdditionSecantIntersectionRing W
        (productNeighborhoodSlope W) =
      secantChartToAdditionSecantIntersectionRing W
        (secantChartSlope W) := by
  have hsecant := congrArg
    (secantChartToAdditionSecantIntersectionRing W)
    (secantChartSlope_mul_sub W)
  have hproduct := congrArg
    (productNeighborhoodToAdditionSecantIntersectionRing W)
    (productNeighborhoodSlope_mul_sub W)
  have hsecant' :
      secantChartToAdditionSecantIntersectionRing W
          (secantChartSlope W) *
        algebraMap (secantPairCoordinateRing W)
          (additionSecantIntersectionCoordinateRing W)
          (secantDenominator W) =
      algebraMap (secantPairCoordinateRing W)
          (additionSecantIntersectionCoordinateRing W)
          (secantPairY₁ W - secantPairY₂ W) := by
    simpa [secantChartX₁_eq_algebraMap_pairX₁,
      secantChartX₂_eq_algebraMap_pairX₂,
      secantChartY₁_eq_algebraMap_pairY₁,
      secantChartY₂_eq_algebraMap_pairY₂,
      secantDenominator] using hsecant
  have hproduct' :
      productNeighborhoodToAdditionSecantIntersectionRing W
          (productNeighborhoodSlope W) *
        algebraMap (secantPairCoordinateRing W)
          (additionSecantIntersectionCoordinateRing W)
          (secantDenominator W) =
      algebraMap (secantPairCoordinateRing W)
          (additionSecantIntersectionCoordinateRing W)
          (secantPairY₁ W - secantPairY₂ W) := by
    simpa [productNeighborhoodX₁, productNeighborhoodX₂,
      productNeighborhoodY₁, productNeighborhoodY₂,
      secantDenominator] using hproduct
  have hproductUnit : IsUnit
      (algebraMap (secantPairCoordinateRing W)
        (additionSecantIntersectionCoordinateRing W)
        (additionB12 W * secantDenominator W)) :=
    IsLocalization.Away.algebraMap_isUnit
      (additionB12 W * secantDenominator W)
  rw [map_mul] at hproductUnit
  apply (isUnit_of_mul_isUnit_right hproductUnit).mul_right_cancel
  exact hproduct'.trans hsecant'.symm

private theorem productNeighborhoodAddX_eq_secantChartAddX_on_intersection
    (W : WeierstrassCurve F) :
    productNeighborhoodToAdditionSecantIntersectionRing W
        (productNeighborhoodAddX W) =
      secantChartToAdditionSecantIntersectionRing W
        (secantChartAddX W) := by
  simp only [productNeighborhoodAddX, secantChartAddX,
    WeierstrassCurve.Affine.addX, map_sub, map_add, map_mul, map_pow,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]
  rw [productNeighborhoodSlope_eq_secantSlope_on_intersection]
  simp [productNeighborhoodCoefficientHom, secantCoefficientHom,
    secantPairCoefficientHom, productNeighborhoodX₁, productNeighborhoodX₂,
    secantChartX₁_eq_algebraMap_pairX₁,
    secantChartX₂_eq_algebraMap_pairX₂]

private theorem productNeighborhoodAddY_eq_secantChartAddY_on_intersection
    (W : WeierstrassCurve F) :
    productNeighborhoodToAdditionSecantIntersectionRing W
        (productNeighborhoodAddY W) =
      secantChartToAdditionSecantIntersectionRing W
        (secantChartAddY W) := by
  simp only [productNeighborhoodAddY, secantChartAddY,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    map_sub, map_add, map_neg, map_mul, map_pow,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃]
  rw [productNeighborhoodSlope_eq_secantSlope_on_intersection]
  simp [productNeighborhoodCoefficientHom, secantCoefficientHom,
    secantPairCoefficientHom, productNeighborhoodX₁, productNeighborhoodX₂,
    productNeighborhoodY₁, secantChartX₁_eq_algebraMap_pairX₁,
    secantChartX₂_eq_algebraMap_pairX₂,
    secantChartY₁_eq_algebraMap_pairY₁]

/-- On the exact overlap, the two affine addition formulas induce the same
coordinate-ring map, not merely the same slope. -/
theorem productNeighborhoodAdditionToAffineRing_eq_secant_on_intersection
    (W : WeierstrassCurve F) :
    (productNeighborhoodToAdditionSecantIntersectionRing W).comp
        (productNeighborhoodAdditionToAffineRing W) =
      (secantChartToAdditionSecantIntersectionRing W).comp
        (secantAdditionToAffineRing W) := by
  let productRestriction :=
    (productNeighborhoodToAdditionSecantIntersectionRing W).comp
      (productNeighborhoodAdditionToAffineRing W)
  let secantRestriction :=
    (secantChartToAdditionSecantIntersectionRing W).comp
      (secantAdditionToAffineRing W)
  change productRestriction = secantRestriction
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro p
    have hinner :
        ((productRestriction.comp
            (Ideal.Quotient.mk
              (Ideal.span {W.toAffine.polynomial}))).comp Polynomial.C) =
          ((secantRestriction.comp
            (Ideal.Quotient.mk
              (Ideal.span {W.toAffine.polynomial}))).comp Polynomial.C) := by
      apply Polynomial.ringHom_ext
      · intro a
        change productNeighborhoodToAdditionSecantIntersectionRing W
            (productNeighborhoodAdditionToAffineRing W
              (secantTargetCoefficientHom W a)) =
          secantChartToAdditionSecantIntersectionRing W
            (secantAdditionToAffineRing W
              (secantTargetCoefficientHom W a))
        rw [productNeighborhoodAdditionToAffineRing_coefficient,
          secantAdditionToAffineRing_coefficient]
        simp [productNeighborhoodCoefficientHom, secantCoefficientHom,
          secantPairCoefficientHom]
      · change productNeighborhoodToAdditionSecantIntersectionRing W
            (productNeighborhoodAdditionToAffineRing W (secantTargetX W)) =
          secantChartToAdditionSecantIntersectionRing W
            (secantAdditionToAffineRing W (secantTargetX W))
        have hproductX :=
          productNeighborhoodAdditionToAffineRing_abscissa W
        change productNeighborhoodAdditionToAffineRing W (secantTargetX W) =
          productNeighborhoodAddX W at hproductX
        have hsecantX := secantAdditionToAffineRing_abscissa W
        change secantAdditionToAffineRing W (secantTargetX W) =
          secantChartAddX W at hsecantX
        rw [hproductX, hsecantX]
        exact productNeighborhoodAddX_eq_secantChartAddX_on_intersection W
    exact RingHom.congr_fun hinner p
  · change productNeighborhoodToAdditionSecantIntersectionRing W
          (productNeighborhoodAdditionToAffineRing W (secantTargetY W)) =
        secantChartToAdditionSecantIntersectionRing W
          (secantAdditionToAffineRing W (secantTargetY W))
    have hproductY := productNeighborhoodAdditionToAffineRing_ordinate W
    change productNeighborhoodAdditionToAffineRing W (secantTargetY W) =
      productNeighborhoodAddY W at hproductY
    have hsecantY := secantAdditionToAffineRing_ordinate W
    change secantAdditionToAffineRing W (secantTargetY W) =
      secantChartAddY W at hsecantY
    rw [hproductY, hsecantY]
    exact productNeighborhoodAddY_eq_secantChartAddY_on_intersection W

/-- The exact overlap mapped to the product-neighbourhood chart. -/
def additionSecantIntersectionToProductNeighborhood
    (W : WeierstrassCurve F) :
    Spec (.of (additionSecantIntersectionCoordinateRing W)) ⟶
      Spec (.of (productNeighborhoodCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (productNeighborhoodToAdditionSecantIntersectionRing W))

/-- The exact overlap mapped to the existing secant chart. -/
def additionSecantIntersectionToSecantChart (W : WeierstrassCurve F) :
    Spec (.of (additionSecantIntersectionCoordinateRing W)) ⟶
      Spec (.of (secantChartCoordinateRing W)) :=
  Spec.map (CommRingCat.ofHom
    (secantChartToAdditionSecantIntersectionRing W))

/-- The affine product-neighbourhood and secant addition morphisms agree
after restriction to their exact overlap. -/
theorem additionSecantIntersection_additionAffine_eq (W : WeierstrassCurve F) :
    additionSecantIntersectionToProductNeighborhood W ≫
        productNeighborhoodAdditionAffineMorphism W =
      additionSecantIntersectionToSecantChart W ≫
        secantAdditionAffineMorphism W := by
  rw [additionSecantIntersectionToProductNeighborhood,
    productNeighborhoodAdditionAffineMorphism,
    additionSecantIntersectionToSecantChart, secantAdditionAffineMorphism,
    ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact productNeighborhoodAdditionToAffineRing_eq_secant_on_intersection W

private theorem productNeighborhoodAdditionProjectiveMorphism_eq_affine_comp
    (W : WeierstrassCurve F) :
    productNeighborhoodAdditionProjectiveMorphism W =
      productNeighborhoodAdditionAffineMorphism W ≫
        (affineEquationSchemeIsoStandardChart W).hom ≫
          coveringChartMap W true := by
  rfl

private theorem secantAdditionProjectiveMorphism_eq_affine_comp
    (W : WeierstrassCurve F) :
    secantAdditionProjectiveMorphism W =
      secantAdditionAffineMorphism W ≫
        (affineEquationSchemeIsoStandardChart W).hom ≫
          coveringChartMap W true := by
  rfl

/-- The product-neighbourhood and secant morphisms into the concrete
projective cubic agree on their genuine intersection. -/
theorem additionSecantIntersection_additionProjective_eq
    (W : WeierstrassCurve F) :
    additionSecantIntersectionToProductNeighborhood W ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      additionSecantIntersectionToSecantChart W ≫
        secantAdditionProjectiveMorphism W := by
  rw [productNeighborhoodAdditionProjectiveMorphism_eq_affine_comp,
    secantAdditionProjectiveMorphism_eq_affine_comp]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (affineEquationSchemeIsoStandardChart W).hom ≫
      coveringChartMap W true)
    (additionSecantIntersection_additionAffine_eq W)

end Schemes

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
