/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProductNeighborhoodAddition

/-!
# The antidiagonal chart of Weierstrass addition

The affine secant and tangent formulas do not include inverse pairs: there
`x₁ = x₂` and `B₁₂ = y₁ + y₂ + a₁x₁ + a₃ = 0`, while the sum is the point at
infinity.  This file constructs the denominator-cleared homogeneous output
needed on that locus.

Writing `A = A₁₂` and `B = B₁₂`, set

* `X = A² + a₁AB - (a₂ + x₁ + x₂)B²`;
* `Y = -(A + a₁B)X + Ax₁B² - (y₁ + a₃)B³`.

On `D(B)` these are the usual affine addition coordinates
`x₃ = X / B²` and `y₃ = Y / B³`, whereas the homogeneous triple
`[BX : Y : B³]` specializes to `[0 : -A³ : 0]` at an inverse pair.  The
construction below proves the homogeneous Weierstrass equation before any
scheme-level gluing.  It does not assume a group object or a supplied point
comparison.
-/

noncomputable section

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [CommRing K]

/-- Denominator-cleared abscissa numerator for the `A₁₂ / B₁₂` addition
formula. -/
def antidiagonalAddXNumerator (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  additionA12 W ^ 2 +
    secantPairCoefficientHom W W.a₁ * additionA12 W * additionB12 W -
    (secantPairCoefficientHom W W.a₂ + secantPairX₁ W + secantPairX₂ W) *
      additionB12 W ^ 2

/-- Denominator-cleared ordinate numerator for the `A₁₂ / B₁₂` addition
formula. -/
def antidiagonalAddYNumerator (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  -(additionA12 W +
      secantPairCoefficientHom W W.a₁ * additionB12 W) *
      antidiagonalAddXNumerator W +
    additionA12 W * secantPairX₁ W * additionB12 W ^ 2 -
    (secantPairY₁ W + secantPairCoefficientHom W W.a₃) *
      additionB12 W ^ 3

/-- At `B₁₂ = 0`, the cleared ordinate is `-A₁₂³`.  The displayed
factorization is the algebraic input that makes the infinity-output chart
cover the inverse-pair locus. -/
theorem antidiagonalAddYNumerator_add_A12_cube (W : WeierstrassCurve K) :
    antidiagonalAddYNumerator W + additionA12 W ^ 3 =
      additionB12 W *
        (-2 * secantPairCoefficientHom W W.a₁ * additionA12 W ^ 2 +
          additionA12 W *
            ((secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                secantPairX₂ W) -
              secantPairCoefficientHom W W.a₁ ^ 2 + secantPairX₁ W) *
            additionB12 W +
          (secantPairCoefficientHom W W.a₁ *
              (secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                secantPairX₂ W) -
            (secantPairY₁ W + secantPairCoefficientHom W W.a₃)) *
            additionB12 W ^ 2) := by
  unfold antidiagonalAddYNumerator antidiagonalAddXNumerator
  ring

/-- The denominator-cleared addition triple lies on the homogeneous
Weierstrass cubic. -/
theorem antidiagonal_homogeneous_equation (W : WeierstrassCurve K) :
    (W.map (secantPairCoefficientHom W)).toProjective.Equation
      ![additionB12 W * antidiagonalAddXNumerator W,
        antidiagonalAddYNumerator W,
        additionB12 W ^ 3] := by
  let a₁ := secantPairCoefficientHom W W.a₁
  let a₂ := secantPairCoefficientHom W W.a₂
  let a₃ := secantPairCoefficientHom W W.a₃
  let a₄ := secantPairCoefficientHom W W.a₄
  let a₆ := secantPairCoefficientHom W W.a₆
  let x₁ := secantPairX₁ W
  let y₁ := secantPairY₁ W
  let x₂ := secantPairX₂ W
  let y₂ := secantPairY₂ W
  let A := additionA12 W
  let B := additionB12 W
  let X := antidiagonalAddXNumerator W
  let Y := antidiagonalAddYNumerator W
  let affineResidual (x y : secantPairCoordinateRing W) :=
    y ^ 2 + a₁ * x * y + a₃ * y -
      (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
  have h₁ : affineResidual x₁ y₁ = 0 := by
    have h := secantPair_equation_left W
    rw [WeierstrassCurve.Affine.equation_iff] at h
    exact sub_eq_zero.mpr (by simpa [affineResidual, a₁, a₂, a₃, a₄,
      a₆, x₁, y₁] using h)
  have h₂ : affineResidual x₂ y₂ = 0 := by
    have h := secantPair_equation_right W
    rw [WeierstrassCurve.Affine.equation_iff] at h
    exact sub_eq_zero.mpr (by simpa [affineResidual, a₁, a₂, a₃, a₄,
      a₆, x₂, y₂] using h)
  let ABResidual := (y₁ - y₂) * B - (x₁ - x₂) * A
  have hAB : ABResidual = 0 := by
    exact sub_eq_zero.mpr (by simpa [ABResidual, x₁, y₁, x₂, y₂, A, B] using
      addition_pair_coordinate_identity W)
  let R := x₁ * B ^ 2 - X
  let S :=
    -A ^ 2 * x₁ + A ^ 2 * x₂ - A * B * a₁ * x₁ - A * B * a₃ -
      2 * A * B * y₂ - B ^ 2 * a₁ * y₂ + B ^ 2 * a₂ * x₁ +
      B ^ 2 * a₂ * x₂ + B ^ 2 * a₄ + B ^ 2 * x₁ ^ 2 +
      B ^ 2 * x₁ * x₂ + B ^ 2 * x₂ ^ 2
  have hS : S = A * (affineResidual x₁ y₁ - affineResidual x₂ y₂) := by
    dsimp only [S, A, B, affineResidual, a₁, a₂, a₃, a₄, a₆, x₁,
      y₁, x₂, y₂]
    unfold additionA12 additionB12
    ring
  have hidentity :
      Y ^ 2 * B ^ 3 + a₁ * (B * X) * Y * B ^ 3 +
          a₃ * Y * (B ^ 3) ^ 2 -
          ((B * X) ^ 3 + a₂ * (B * X) ^ 2 * B ^ 3 +
            a₄ * (B * X) * (B ^ 3) ^ 2 + a₆ * (B ^ 3) ^ 3) =
        B ^ 5 * (B ^ 4 * affineResidual x₁ y₁ -
          (2 * A + B * a₁) * R * ABResidual + R * S) := by
    dsimp only [Y, X, R, S, ABResidual, A, B, a₁, a₂, a₃, a₄, a₆, x₁, y₁,
      x₂, y₂]
    unfold antidiagonalAddYNumerator antidiagonalAddXNumerator
    ring
  have hzero :
      Y ^ 2 * B ^ 3 + a₁ * (B * X) * Y * B ^ 3 +
          a₃ * Y * (B ^ 3) ^ 2 -
          ((B * X) ^ 3 + a₂ * (B * X) ^ 2 * B ^ 3 +
            a₄ * (B * X) * (B ^ 3) ^ 2 + a₆ * (B ^ 3) ^ 3) = 0 := by
    rw [hidentity, h₁, hAB, hS, h₁, h₂]
    ring
  rw [WeierstrassCurve.Projective.equation_iff]
  simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, WeierstrassCurve.Projective.fin3_def_ext] using
    hzero

/-! ## The infinity-output principal open -/

section InfinityChart

variable {F : Type u} [Field F]

/-- Coordinate ring of the locus where the cleared output ordinate is
invertible.  On this open the homogeneous addition output lands in the
projective chart `Y ≠ 0`. -/
abbrev antidiagonalChartCoordinateRing (W : WeierstrassCurve F) :=
  Localization.Away (antidiagonalAddYNumerator W)

/-- Structural coefficient map on the infinity-output chart. -/
def antidiagonalChartCoefficientHom (W : WeierstrassCurve F) :
    F →+* antidiagonalChartCoordinateRing W :=
  (algebraMap (secantPairCoordinateRing W)
    (antidiagonalChartCoordinateRing W)).comp (secantPairCoefficientHom W)

/-- Pullback of the cleared homogeneous `X` coordinate. -/
def antidiagonalChartHomogeneousX (W : WeierstrassCurve F) :
    antidiagonalChartCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (antidiagonalChartCoordinateRing W)
      (additionB12 W * antidiagonalAddXNumerator W)

/-- Pullback of the cleared homogeneous `Y` coordinate. -/
def antidiagonalChartHomogeneousY (W : WeierstrassCurve F) :
    antidiagonalChartCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (antidiagonalChartCoordinateRing W) (antidiagonalAddYNumerator W)

/-- Pullback of the cleared homogeneous `Z` coordinate. -/
def antidiagonalChartHomogeneousZ (W : WeierstrassCurve F) :
    antidiagonalChartCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W)
    (antidiagonalChartCoordinateRing W) (additionB12 W ^ 3)

/-- The `X / Y` coordinate of the output on the infinity chart. -/
def antidiagonalChartXOverY (W : WeierstrassCurve F) :
    antidiagonalChartCoordinateRing W :=
  antidiagonalChartHomogeneousX W *
    IsLocalization.Away.invSelf (antidiagonalAddYNumerator W)

/-- The `Z / Y` coordinate of the output on the infinity chart. -/
def antidiagonalChartZOverY (W : WeierstrassCurve F) :
    antidiagonalChartCoordinateRing W :=
  antidiagonalChartHomogeneousZ W *
    IsLocalization.Away.invSelf (antidiagonalAddYNumerator W)

private theorem antidiagonalChartHomogeneousY_mul_invSelf
    (W : WeierstrassCurve F) :
    antidiagonalChartHomogeneousY W *
        IsLocalization.Away.invSelf (antidiagonalAddYNumerator W) = 1 := by
  exact IsLocalization.Away.mul_invSelf
    (S := antidiagonalChartCoordinateRing W) (antidiagonalAddYNumerator W)

/-- The two normalized output coordinates satisfy the actual equation of the
`Y ≠ 0` projective chart. -/
theorem antidiagonalChart_infinityEquation (W : WeierstrassCurve F) :
    antidiagonalChartXOverY W ^ 3 +
        antidiagonalChartCoefficientHom W W.a₂ *
          antidiagonalChartZOverY W * antidiagonalChartXOverY W ^ 2 +
        (antidiagonalChartCoefficientHom W W.a₄ *
            antidiagonalChartZOverY W ^ 2 -
          antidiagonalChartCoefficientHom W W.a₁ *
            antidiagonalChartZOverY W) * antidiagonalChartXOverY W +
        (antidiagonalChartCoefficientHom W W.a₆ *
            antidiagonalChartZOverY W ^ 3 -
          antidiagonalChartCoefficientHom W W.a₃ *
            antidiagonalChartZOverY W ^ 2 -
          antidiagonalChartZOverY W) = 0 := by
  let iY : antidiagonalChartCoordinateRing W :=
    IsLocalization.Away.invSelf (antidiagonalAddYNumerator W)
  let X := antidiagonalChartHomogeneousX W
  let Y := antidiagonalChartHomogeneousY W
  let Z := antidiagonalChartHomogeneousZ W
  let a₁ := antidiagonalChartCoefficientHom W W.a₁
  let a₂ := antidiagonalChartCoefficientHom W W.a₂
  let a₃ := antidiagonalChartCoefficientHom W W.a₃
  let a₄ := antidiagonalChartCoefficientHom W W.a₄
  let a₆ := antidiagonalChartCoefficientHom W W.a₆
  have hYiY : Y * iY = 1 := by
    exact antidiagonalChartHomogeneousY_mul_invSelf W
  have hYI₁ : Y ^ 3 * iY = Y ^ 2 := by
    calc
      Y ^ 3 * iY = Y ^ 2 * (Y * iY) := by ring
      _ = Y ^ 2 := by rw [hYiY, mul_one]
  have hYI₂ : Y ^ 3 * iY ^ 2 = Y := by
    calc
      Y ^ 3 * iY ^ 2 = Y * (Y * iY) ^ 2 := by ring
      _ = Y := by rw [hYiY, one_pow, mul_one]
  have hYI₃ : Y ^ 3 * iY ^ 3 = 1 := by
    calc
      Y ^ 3 * iY ^ 3 = (Y * iY) ^ 3 := by ring
      _ = 1 := by rw [hYiY, one_pow]
  have hprojective :
      Y ^ 2 * Z + a₁ * X * Y * Z + a₃ * Y * Z ^ 2 -
          (X ^ 3 + a₂ * X ^ 2 * Z + a₄ * X * Z ^ 2 + a₆ * Z ^ 3) = 0 := by
    have h := antidiagonal_homogeneous_equation W
    rw [WeierstrassCurve.Projective.equation_iff] at h
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, WeierstrassCurve.Projective.fin3_def_ext] at h
    have hmapped := congrArg
      (algebraMap (secantPairCoordinateRing W)
        (antidiagonalChartCoordinateRing W)) h
    simpa [X, Y, Z, a₁, a₂, a₃, a₄, a₆,
      antidiagonalChartHomogeneousX, antidiagonalChartHomogeneousY,
      antidiagonalChartHomogeneousZ, antidiagonalChartCoefficientHom]
      using hmapped
  have hscaled :
      Y ^ 3 *
          ((X * iY) ^ 3 + a₂ * (Z * iY) * (X * iY) ^ 2 +
            (a₄ * (Z * iY) ^ 2 - a₁ * (Z * iY)) * (X * iY) +
            (a₆ * (Z * iY) ^ 3 - a₃ * (Z * iY) ^ 2 - Z * iY)) = 0 := by
    calc
      Y ^ 3 *
          ((X * iY) ^ 3 + a₂ * (Z * iY) * (X * iY) ^ 2 +
            (a₄ * (Z * iY) ^ 2 - a₁ * (Z * iY)) * (X * iY) +
            (a₆ * (Z * iY) ^ 3 - a₃ * (Z * iY) ^ 2 - Z * iY)) =
        (Y ^ 3 * iY ^ 3) *
            (X ^ 3 + a₂ * X ^ 2 * Z + a₄ * X * Z ^ 2 + a₆ * Z ^ 3) -
          (Y ^ 3 * iY ^ 2) * (a₁ * X * Z + a₃ * Z ^ 2) -
          (Y ^ 3 * iY) * Z := by ring
      _ = -(
          Y ^ 2 * Z + a₁ * X * Y * Z + a₃ * Y * Z ^ 2 -
            (X ^ 3 + a₂ * X ^ 2 * Z + a₄ * X * Z ^ 2 + a₆ * Z ^ 3)) := by
        rw [hYI₁, hYI₂, hYI₃]
        ring
      _ = 0 := by rw [hprojective, neg_zero]
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := antidiagonalChartCoordinateRing W)
    (antidiagonalAddYNumerator W)).pow 3 |>.mul_left_cancel
  simpa [antidiagonalChartXOverY, antidiagonalChartZOverY,
    antidiagonalChartHomogeneousY, X, Y, Z, iY, a₁, a₂, a₃, a₄, a₆]
    using hscaled

private def antidiagonalInfinityPolynomialEvaluation
    (W : WeierstrassCurve F) :
    Polynomial (Polynomial F) →+* antidiagonalChartCoordinateRing W :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (antidiagonalChartCoefficientHom W)
      (antidiagonalChartZOverY W))
    (antidiagonalChartXOverY W)

private theorem antidiagonalInfinityPolynomialEvaluation_eq_zero
    (W : WeierstrassCurve F) :
    antidiagonalInfinityPolynomialEvaluation W
      (infinityChartPolynomial W) = 0 := by
  change Polynomial.eval₂
      (Polynomial.eval₂RingHom (antidiagonalChartCoefficientHom W)
        (antidiagonalChartZOverY W))
      (antidiagonalChartXOverY W) (infinityChartPolynomial W) = 0
  simpa [infinityChartPolynomial, infinityChartCoeffTwo,
    infinityChartCoeffOne, infinityChartCoeffZero, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_X_pow, Polynomial.eval₂_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    add_assoc] using
      antidiagonalChart_infinityEquation W

/-- Contravariant map from the normalized infinity-chart equation ring to
the antidiagonal output chart. -/
def antidiagonalAdditionToInfinityEquationRing (W : WeierstrassCurve F) :
    (Polynomial (Polynomial F) ⧸
      Ideal.span {infinityChartPolynomial W}) →+*
        antidiagonalChartCoordinateRing W :=
  Ideal.Quotient.lift (Ideal.span {infinityChartPolynomial W})
    (antidiagonalInfinityPolynomialEvaluation W) (by
      intro p hp
      apply (show Ideal.span {infinityChartPolynomial W} ≤
          RingHom.ker (antidiagonalInfinityPolynomialEvaluation W) by
        apply Ideal.span_le.mpr
        intro q hq
        rw [Set.mem_singleton_iff.mp hq]
        exact antidiagonalInfinityPolynomialEvaluation_eq_zero W) hp)

/-- The polynomial infinity-chart equation ring is the actual `Y ≠ 0`
coordinate ring of the projective cubic. -/
noncomputable def infinityEquationCoveringChartRingEquiv
    (W : WeierstrassCurve F) :
    (Polynomial (Polynomial F) ⧸
      Ideal.span {infinityChartPolynomial W}) ≃+*
        coveringChartCoordinateRing W false :=
  Ideal.quotientEquiv
    (Ideal.span {infinityChartPolynomial W}) (infinityChartIdeal W)
    (infinityChartRingEquiv (K := F)) (infinityChartIdeal_eq_map W)

/-- Contravariant coordinate-ring map of the antidiagonal addition morphism
into the actual `Y ≠ 0` chart of the reduced projective cubic. -/
noncomputable def antidiagonalAdditionToInfinityRing
    (W : WeierstrassCurve F) :
    coveringChartCoordinateRing W false →+*
      antidiagonalChartCoordinateRing W :=
  (antidiagonalAdditionToInfinityEquationRing W).comp
    (infinityEquationCoveringChartRingEquiv W).symm.toRingHom

private theorem infinityEquationToCoveringChartRingEquiv_symm_coefficient
    (W : WeierstrassCurve F) (a : F) :
    (infinityEquationCoveringChartRingEquiv W).symm
        (coveringChartStructureRingHom W false a) =
      Ideal.Quotient.mk (Ideal.span {infinityChartPolynomial W})
        (Polynomial.C (Polynomial.C a)) := by
  apply (infinityEquationCoveringChartRingEquiv W).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (infinityChartIdeal W)
      (coordinateChartConstantHom (K := F) 1 a) =
    Ideal.Quotient.mk (infinityChartIdeal W)
      (infinityChartRingEquiv (Polynomial.C (Polynomial.C a)))
  rw [infinityChartRingEquiv_constant]

/-- The infinity-chart addition comorphism respects base coefficients. -/
@[simp]
theorem antidiagonalAdditionToInfinityRing_coefficient
    (W : WeierstrassCurve F) (a : F) :
    antidiagonalAdditionToInfinityRing W
        (coveringChartStructureRingHom W false a) =
      antidiagonalChartCoefficientHom W a := by
  rw [antidiagonalAdditionToInfinityRing,
    RingHom.comp_apply]
  change antidiagonalAdditionToInfinityEquationRing W
      ((infinityEquationCoveringChartRingEquiv W).symm
        (coveringChartStructureRingHom W false a)) =
    antidiagonalChartCoefficientHom W a
  rw [infinityEquationToCoveringChartRingEquiv_symm_coefficient]
  simp [antidiagonalAdditionToInfinityEquationRing,
    antidiagonalInfinityPolynomialEvaluation]

/-- Ring-hom form of the base-compatibility statement. -/
theorem antidiagonalAdditionToInfinityRing_comp_coefficient
    (W : WeierstrassCurve F) :
    (antidiagonalAdditionToInfinityRing W).comp
        (coveringChartStructureRingHom W false) =
      antidiagonalChartCoefficientHom W := by
  ext a
  exact antidiagonalAdditionToInfinityRing_coefficient W a

private theorem infinityEquationToCoveringChartRingEquiv_symm_outerX
    (W : WeierstrassCurve F) :
    (infinityEquationCoveringChartRingEquiv W).symm
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 0)) =
      Ideal.Quotient.mk (Ideal.span {infinityChartPolynomial W})
        Polynomial.X := by
  apply (infinityEquationCoveringChartRingEquiv W).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (coveringChartIdeal W false)
      (coordinateChartRatio (K := F) 1 0) =
    Ideal.Quotient.mk (coveringChartIdeal W false)
      (infinityChartRingEquiv Polynomial.X)
  rw [infinityChartRingEquiv_outerX]

private theorem infinityEquationToCoveringChartRingEquiv_symm_innerX
    (W : WeierstrassCurve F) :
    (infinityEquationCoveringChartRingEquiv W).symm
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 2)) =
      Ideal.Quotient.mk (Ideal.span {infinityChartPolynomial W})
        (Polynomial.C Polynomial.X) := by
  apply (infinityEquationCoveringChartRingEquiv W).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (coveringChartIdeal W false)
      (coordinateChartRatio (K := F) 1 2) =
    Ideal.Quotient.mk (coveringChartIdeal W false)
      (infinityChartRingEquiv (Polynomial.C Polynomial.X))
  rw [infinityChartRingEquiv_innerX]

/-- The antidiagonal comorphism sends the ambient `X/Y` coordinate to the
normalized cleared abscissa. -/
@[simp]
theorem antidiagonalAdditionToInfinityRing_outerX
    (W : WeierstrassCurve F) :
    antidiagonalAdditionToInfinityRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 0)) =
      antidiagonalChartXOverY W := by
  change antidiagonalAdditionToInfinityEquationRing W
      ((infinityEquationCoveringChartRingEquiv W).symm
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 0))) = _
  rw [infinityEquationToCoveringChartRingEquiv_symm_outerX]
  simp [antidiagonalAdditionToInfinityEquationRing,
    antidiagonalInfinityPolynomialEvaluation]

/-- The antidiagonal comorphism sends the ambient `Z/Y` coordinate to the
normalized cleared third coordinate. -/
@[simp]
theorem antidiagonalAdditionToInfinityRing_innerX
    (W : WeierstrassCurve F) :
    antidiagonalAdditionToInfinityRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 2)) =
      antidiagonalChartZOverY W := by
  change antidiagonalAdditionToInfinityEquationRing W
      ((infinityEquationCoveringChartRingEquiv W).symm
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 2))) = _
  rw [infinityEquationToCoveringChartRingEquiv_symm_innerX]
  simp [antidiagonalAdditionToInfinityEquationRing,
    antidiagonalInfinityPolynomialEvaluation]

/-! ## Compatibility with the `D(B₁₂)` affine formula -/

/-- Clearing `B₁₂²` from the affine output abscissa gives the homogeneous
numerator used by the antidiagonal chart. -/
theorem productNeighborhoodAddX_mul_B12_sq
    (W : WeierstrassCurve F) :
    productNeighborhoodAddX W * productNeighborhoodB12 W ^ 2 =
      algebraMap (secantPairCoordinateRing W)
        (productNeighborhoodCoordinateRing W)
          (antidiagonalAddXNumerator W) := by
  have hslope : productNeighborhoodSlope W * productNeighborhoodB12 W =
      productNeighborhoodA12 W := by
    rw [productNeighborhoodSlope, productNeighborhoodB12, mul_assoc,
      mul_comm (IsLocalization.Away.invSelf (additionB12 W)),
      IsLocalization.Away.mul_invSelf, mul_one]
  simp only [productNeighborhoodAddX, WeierstrassCurve.Affine.addX]
  unfold antidiagonalAddXNumerator
  simp only [map_add, map_sub, map_mul, map_pow]
  rw [show algebraMap (secantPairCoordinateRing W)
      (productNeighborhoodCoordinateRing W) (additionA12 W) =
        productNeighborhoodA12 W from rfl,
    show algebraMap (secantPairCoordinateRing W)
      (productNeighborhoodCoordinateRing W) (additionB12 W) =
        productNeighborhoodB12 W from rfl]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]
  change
    (productNeighborhoodSlope W ^ 2 +
          productNeighborhoodCoefficientHom W W.a₁ *
            productNeighborhoodSlope W -
          productNeighborhoodCoefficientHom W W.a₂ -
          productNeighborhoodX₁ W - productNeighborhoodX₂ W) *
        productNeighborhoodB12 W ^ 2 =
      productNeighborhoodA12 W ^ 2 +
        productNeighborhoodCoefficientHom W W.a₁ *
          productNeighborhoodA12 W * productNeighborhoodB12 W -
        (productNeighborhoodCoefficientHom W W.a₂ +
          productNeighborhoodX₁ W + productNeighborhoodX₂ W) *
          productNeighborhoodB12 W ^ 2
  calc
    _ = (productNeighborhoodSlope W * productNeighborhoodB12 W) ^ 2 +
          productNeighborhoodCoefficientHom W W.a₁ *
            (productNeighborhoodSlope W * productNeighborhoodB12 W) *
              productNeighborhoodB12 W -
          (productNeighborhoodCoefficientHom W W.a₂ +
            productNeighborhoodX₁ W + productNeighborhoodX₂ W) *
              productNeighborhoodB12 W ^ 2 := by ring
    _ = _ := by rw [hslope]

/-- Clearing `B₁₂³` from the affine output ordinate gives the homogeneous
numerator used by the antidiagonal chart. -/
theorem productNeighborhoodAddY_mul_B12_cube
    (W : WeierstrassCurve F) :
    productNeighborhoodAddY W * productNeighborhoodB12 W ^ 3 =
      algebraMap (secantPairCoordinateRing W)
        (productNeighborhoodCoordinateRing W)
          (antidiagonalAddYNumerator W) := by
  have hslope : productNeighborhoodSlope W * productNeighborhoodB12 W =
      productNeighborhoodA12 W := by
    rw [productNeighborhoodSlope, productNeighborhoodB12, mul_assoc,
      mul_comm (IsLocalization.Away.invSelf (additionB12 W)),
      IsLocalization.Away.mul_invSelf, mul_one]
  have hX := productNeighborhoodAddX_mul_B12_sq W
  simp only [productNeighborhoodAddY, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX]
  unfold antidiagonalAddYNumerator
  simp only [map_add, map_sub, map_neg, map_mul, map_pow]
  rw [show algebraMap (secantPairCoordinateRing W)
      (productNeighborhoodCoordinateRing W) (additionA12 W) =
        productNeighborhoodA12 W from rfl,
    show algebraMap (secantPairCoordinateRing W)
      (productNeighborhoodCoordinateRing W) (additionB12 W) =
        productNeighborhoodB12 W from rfl]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃]
  change
    (-((productNeighborhoodSlope W *
            (productNeighborhoodAddX W - productNeighborhoodX₁ W) +
          productNeighborhoodY₁ W)) -
        productNeighborhoodCoefficientHom W W.a₁ *
          productNeighborhoodAddX W -
        productNeighborhoodCoefficientHom W W.a₃) *
          productNeighborhoodB12 W ^ 3 =
      -(productNeighborhoodA12 W +
          productNeighborhoodCoefficientHom W W.a₁ *
            productNeighborhoodB12 W) *
          algebraMap (secantPairCoordinateRing W)
            (productNeighborhoodCoordinateRing W)
              (antidiagonalAddXNumerator W) +
        productNeighborhoodA12 W * productNeighborhoodX₁ W *
          productNeighborhoodB12 W ^ 2 -
        (productNeighborhoodY₁ W +
          productNeighborhoodCoefficientHom W W.a₃) *
          productNeighborhoodB12 W ^ 3
  calc
    _ = -(productNeighborhoodSlope W * productNeighborhoodB12 W +
          productNeighborhoodCoefficientHom W W.a₁ *
            productNeighborhoodB12 W) *
          (productNeighborhoodAddX W *
            productNeighborhoodB12 W ^ 2) +
        (productNeighborhoodSlope W * productNeighborhoodB12 W) *
          productNeighborhoodX₁ W * productNeighborhoodB12 W ^ 2 -
        (productNeighborhoodY₁ W +
          productNeighborhoodCoefficientHom W W.a₃) *
          productNeighborhoodB12 W ^ 3 := by ring
    _ = _ := by rw [hslope, hX]

end InfinityChart

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
