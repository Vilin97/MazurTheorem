/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassAntidiagonalAddition

/-!
# The vertical infinity chart of Weierstrass addition

The ordinary secant formula uses
`C₁₂ / D₁₂ = (y₁ - y₂) / (x₁ - x₂)`.  Clearing powers of `D₁₂` gives a
homogeneous output that remains meaningful on the inverse-pair locus when
the vertical derivative `C₁₂` is nonzero.  This is the second infinity
chart needed beside the `A₁₂ / B₁₂` antidiagonal formula.

The construction is a polynomial identity in the actual affine-pair
coordinate ring.  It assumes no group object and no supplied pointwise
addition law.
-/

noncomputable section

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [CommRing K]

/-- Numerator of the ordinary secant slope. -/
def verticalAdditionA (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  secantPairY₁ W - secantPairY₂ W

/-- Denominator of the ordinary secant slope. -/
def verticalAdditionB (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  secantPairX₁ W - secantPairX₂ W

/-- Denominator-cleared output abscissa for the ordinary secant slope. -/
def verticalAddXNumerator (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  verticalAdditionA W ^ 2 +
    secantPairCoefficientHom W W.a₁ * verticalAdditionA W *
      verticalAdditionB W -
    (secantPairCoefficientHom W W.a₂ + secantPairX₁ W + secantPairX₂ W) *
      verticalAdditionB W ^ 2

/-- Denominator-cleared output ordinate for the ordinary secant slope. -/
def verticalAddYNumerator (W : WeierstrassCurve K) :
    secantPairCoordinateRing W :=
  -(verticalAdditionA W +
      secantPairCoefficientHom W W.a₁ * verticalAdditionB W) *
      verticalAddXNumerator W +
    verticalAdditionA W * secantPairX₁ W * verticalAdditionB W ^ 2 -
    (secantPairY₁ W + secantPairCoefficientHom W W.a₃) *
      verticalAdditionB W ^ 3

/-- At `D₁₂ = 0`, the cleared ordinate is `-C₁₂³`. -/
theorem verticalAddYNumerator_add_A_cube (W : WeierstrassCurve K) :
    verticalAddYNumerator W + verticalAdditionA W ^ 3 =
      verticalAdditionB W *
        (-2 * secantPairCoefficientHom W W.a₁ * verticalAdditionA W ^ 2 +
          verticalAdditionA W *
            ((secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                secantPairX₂ W) -
              secantPairCoefficientHom W W.a₁ ^ 2 + secantPairX₁ W) *
            verticalAdditionB W +
          (secantPairCoefficientHom W W.a₁ *
              (secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
                secantPairX₂ W) -
            (secantPairY₁ W + secantPairCoefficientHom W W.a₃)) *
            verticalAdditionB W ^ 2) := by
  unfold verticalAddYNumerator verticalAddXNumerator
  ring

/-- The denominator-cleared vertical output lies on the homogeneous
Weierstrass cubic. -/
theorem vertical_homogeneous_equation (W : WeierstrassCurve K) :
    (W.map (secantPairCoefficientHom W)).toProjective.Equation
      ![verticalAdditionB W * verticalAddXNumerator W,
        verticalAddYNumerator W,
        verticalAdditionB W ^ 3] := by
  let a₁ := secantPairCoefficientHom W W.a₁
  let a₂ := secantPairCoefficientHom W W.a₂
  let a₃ := secantPairCoefficientHom W W.a₃
  let a₄ := secantPairCoefficientHom W W.a₄
  let a₆ := secantPairCoefficientHom W W.a₆
  let x₁ := secantPairX₁ W
  let y₁ := secantPairY₁ W
  let x₂ := secantPairX₂ W
  let y₂ := secantPairY₂ W
  let A := verticalAdditionA W
  let B := verticalAdditionB W
  let X := verticalAddXNumerator W
  let Y := verticalAddYNumerator W
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
    dsimp only [ABResidual, A, B, x₁, y₁, x₂, y₂]
    unfold verticalAdditionA verticalAdditionB
    ring
  let R := x₁ * B ^ 2 - X
  let S :=
    -A ^ 2 * x₁ + A ^ 2 * x₂ - A * B * a₁ * x₁ - A * B * a₃ -
      2 * A * B * y₂ - B ^ 2 * a₁ * y₂ + B ^ 2 * a₂ * x₁ +
      B ^ 2 * a₂ * x₂ + B ^ 2 * a₄ + B ^ 2 * x₁ ^ 2 +
      B ^ 2 * x₁ * x₂ + B ^ 2 * x₂ ^ 2
  have hS : S = -B * (affineResidual x₁ y₁ - affineResidual x₂ y₂) := by
    dsimp only [S, A, B, affineResidual, a₁, a₂, a₃, a₄, a₆, x₁,
      y₁, x₂, y₂]
    unfold verticalAdditionA verticalAdditionB
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
    unfold verticalAddYNumerator verticalAddXNumerator
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

/-! ## Compatibility of the two denominator-cleared triples -/

/-- The `X/Y` cross-product of the antidiagonal and vertical homogeneous
triples agrees in the affine-pair coordinate ring.  This is a polynomial
consequence of the checked numerator-denominator identity, with no
cancellation or reducedness hypothesis. -/
theorem antidiagonalVertical_homogeneousX_mul_Y (W : WeierstrassCurve K) :
    (additionB12 W * antidiagonalAddXNumerator W) *
        verticalAddYNumerator W =
      (verticalAdditionB W * verticalAddXNumerator W) *
        antidiagonalAddYNumerator W := by
  let a := secantPairCoefficientHom W W.a₁
  let H := secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
    secantPairX₂ W
  let x := secantPairX₁ W
  let y := secantPairY₁ W + secantPairCoefficientHom W W.a₃
  let A := additionA12 W
  let B := additionB12 W
  let C := verticalAdditionA W
  let D := verticalAdditionB W
  let Q :=
    A ^ 2 * C ^ 2 + A ^ 2 * C * D * a - A ^ 2 * D ^ 2 * H +
      A * B * C ^ 2 * a + A * B * C * D * a ^ 2 +
      A * B * C * D * x - A * B * D ^ 2 * H * a -
      A * B * D ^ 2 * y - B ^ 2 * C ^ 2 * H -
      B ^ 2 * C * D * H * a - B ^ 2 * C * D * y +
      B ^ 2 * D ^ 2 * H ^ 2 + B ^ 2 * D ^ 2 * H * x -
      B ^ 2 * D ^ 2 * a * y
  have hcross : A * D = B * C := by
    simpa only [A, B, C, D, verticalAdditionA, verticalAdditionB,
      mul_comm] using
      (addition_pair_coordinate_identity W).symm
  apply sub_eq_zero.mp
  calc
    (additionB12 W * antidiagonalAddXNumerator W) *
          verticalAddYNumerator W -
        (verticalAdditionB W * verticalAddXNumerator W) *
          antidiagonalAddYNumerator W = (A * D - B * C) * Q := by
            dsimp only [A, B, C, D, Q, a, H, x, y]
            simp only [antidiagonalAddYNumerator,
              antidiagonalAddXNumerator, verticalAddYNumerator,
              verticalAddXNumerator]
            ring
    _ = 0 := by rw [hcross]; ring

/-- The `Z/Y` cross-product of the antidiagonal and vertical homogeneous
triples agrees without inverting either slope denominator. -/
theorem antidiagonalVertical_homogeneousZ_mul_Y (W : WeierstrassCurve K) :
    additionB12 W ^ 3 * verticalAddYNumerator W =
      verticalAdditionB W ^ 3 * antidiagonalAddYNumerator W := by
  let a := secantPairCoefficientHom W W.a₁
  let H := secantPairCoefficientHom W W.a₂ + secantPairX₁ W +
    secantPairX₂ W
  let x := secantPairX₁ W
  let A := additionA12 W
  let B := additionB12 W
  let C := verticalAdditionA W
  let D := verticalAdditionB W
  let Q :=
    -(A ^ 2 * D ^ 2) - A * B * C * D - 2 * A * B * D ^ 2 * a -
      B ^ 2 * C ^ 2 - 2 * B ^ 2 * C * D * a + B ^ 2 * D ^ 2 * H -
      B ^ 2 * D ^ 2 * a ^ 2 + B ^ 2 * D ^ 2 * x
  have hcross : A * D = B * C := by
    simpa only [A, B, C, D, verticalAdditionA, verticalAdditionB,
      mul_comm] using
      (addition_pair_coordinate_identity W).symm
  apply sub_eq_zero.mp
  calc
    additionB12 W ^ 3 * verticalAddYNumerator W -
        verticalAdditionB W ^ 3 * antidiagonalAddYNumerator W =
      -(A * D - B * C) * Q := by
        dsimp only [A, B, C, D, Q, a, H, x]
        simp only [antidiagonalAddYNumerator, antidiagonalAddXNumerator,
          verticalAddYNumerator, verticalAddXNumerator]
        ring
    _ = 0 := by rw [hcross]; ring

section InfinityChart

variable {F : Type u} [Field F]

/-- Coordinate ring where the vertical cleared output ordinate is
invertible. -/
abbrev verticalChartCoordinateRing (W : WeierstrassCurve F) :=
  Localization.Away (verticalAddYNumerator W)

/-- Structural coefficient map on the vertical infinity chart. -/
def verticalChartCoefficientHom (W : WeierstrassCurve F) :
    F →+* verticalChartCoordinateRing W :=
  (algebraMap (secantPairCoordinateRing W)
    (verticalChartCoordinateRing W)).comp (secantPairCoefficientHom W)

/-- Pullback of the cleared homogeneous `X` coordinate. -/
def verticalChartHomogeneousX (W : WeierstrassCurve F) :
    verticalChartCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W) (verticalChartCoordinateRing W)
    (verticalAdditionB W * verticalAddXNumerator W)

/-- Pullback of the cleared homogeneous `Y` coordinate. -/
def verticalChartHomogeneousY (W : WeierstrassCurve F) :
    verticalChartCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W) (verticalChartCoordinateRing W)
    (verticalAddYNumerator W)

/-- Pullback of the cleared homogeneous `Z` coordinate. -/
def verticalChartHomogeneousZ (W : WeierstrassCurve F) :
    verticalChartCoordinateRing W :=
  algebraMap (secantPairCoordinateRing W) (verticalChartCoordinateRing W)
    (verticalAdditionB W ^ 3)

/-- Normalized `X/Y` coordinate of the vertical output. -/
def verticalChartXOverY (W : WeierstrassCurve F) :
    verticalChartCoordinateRing W :=
  verticalChartHomogeneousX W *
    IsLocalization.Away.invSelf (verticalAddYNumerator W)

/-- Normalized `Z/Y` coordinate of the vertical output. -/
def verticalChartZOverY (W : WeierstrassCurve F) :
    verticalChartCoordinateRing W :=
  verticalChartHomogeneousZ W *
    IsLocalization.Away.invSelf (verticalAddYNumerator W)

private theorem verticalChartHomogeneousY_mul_invSelf
    (W : WeierstrassCurve F) :
    verticalChartHomogeneousY W *
        IsLocalization.Away.invSelf (verticalAddYNumerator W) = 1 := by
  exact IsLocalization.Away.mul_invSelf
    (S := verticalChartCoordinateRing W) (verticalAddYNumerator W)

/-- The normalized vertical output satisfies the actual `Y ≠ 0` chart
equation. -/
theorem verticalChart_infinityEquation (W : WeierstrassCurve F) :
    verticalChartXOverY W ^ 3 +
        verticalChartCoefficientHom W W.a₂ *
          verticalChartZOverY W * verticalChartXOverY W ^ 2 +
        (verticalChartCoefficientHom W W.a₄ *
            verticalChartZOverY W ^ 2 -
          verticalChartCoefficientHom W W.a₁ *
            verticalChartZOverY W) * verticalChartXOverY W +
        (verticalChartCoefficientHom W W.a₆ *
            verticalChartZOverY W ^ 3 -
          verticalChartCoefficientHom W W.a₃ *
            verticalChartZOverY W ^ 2 -
          verticalChartZOverY W) = 0 := by
  let iY : verticalChartCoordinateRing W :=
    IsLocalization.Away.invSelf (verticalAddYNumerator W)
  let X := verticalChartHomogeneousX W
  let Y := verticalChartHomogeneousY W
  let Z := verticalChartHomogeneousZ W
  let a₁ := verticalChartCoefficientHom W W.a₁
  let a₂ := verticalChartCoefficientHom W W.a₂
  let a₃ := verticalChartCoefficientHom W W.a₃
  let a₄ := verticalChartCoefficientHom W W.a₄
  let a₆ := verticalChartCoefficientHom W W.a₆
  have hYiY : Y * iY = 1 := verticalChartHomogeneousY_mul_invSelf W
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
    have h := vertical_homogeneous_equation W
    rw [WeierstrassCurve.Projective.equation_iff] at h
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆, WeierstrassCurve.Projective.fin3_def_ext] at h
    have hmapped := congrArg
      (algebraMap (secantPairCoordinateRing W)
        (verticalChartCoordinateRing W)) h
    simpa [X, Y, Z, a₁, a₂, a₃, a₄, a₆,
      verticalChartHomogeneousX, verticalChartHomogeneousY,
      verticalChartHomogeneousZ, verticalChartCoefficientHom] using hmapped
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
    (S := verticalChartCoordinateRing W)
    (verticalAddYNumerator W)).pow 3 |>.mul_left_cancel
  simpa [verticalChartXOverY, verticalChartZOverY,
    verticalChartHomogeneousY, X, Y, Z, iY, a₁, a₂, a₃, a₄, a₆] using
    hscaled

private def verticalInfinityPolynomialEvaluation
    (W : WeierstrassCurve F) :
    Polynomial (Polynomial F) →+* verticalChartCoordinateRing W :=
  Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (verticalChartCoefficientHom W)
      (verticalChartZOverY W))
    (verticalChartXOverY W)

private theorem verticalInfinityPolynomialEvaluation_eq_zero
    (W : WeierstrassCurve F) :
    verticalInfinityPolynomialEvaluation W (infinityChartPolynomial W) = 0 := by
  change Polynomial.eval₂
      (Polynomial.eval₂RingHom (verticalChartCoefficientHom W)
        (verticalChartZOverY W))
      (verticalChartXOverY W) (infinityChartPolynomial W) = 0
  simpa [infinityChartPolynomial, infinityChartCoeffTwo,
    infinityChartCoeffOne, infinityChartCoeffZero, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_X_pow, Polynomial.eval₂_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    add_assoc] using verticalChart_infinityEquation W

/-- Contravariant map from the polynomial infinity equation ring to the
vertical source chart. -/
def verticalAdditionToInfinityEquationRing (W : WeierstrassCurve F) :
    (Polynomial (Polynomial F) ⧸
      Ideal.span {infinityChartPolynomial W}) →+*
        verticalChartCoordinateRing W :=
  Ideal.Quotient.lift (Ideal.span {infinityChartPolynomial W})
    (verticalInfinityPolynomialEvaluation W) (by
      intro p hp
      apply (show Ideal.span {infinityChartPolynomial W} ≤
          RingHom.ker (verticalInfinityPolynomialEvaluation W) by
        apply Ideal.span_le.mpr
        intro q hq
        rw [Set.mem_singleton_iff.mp hq]
        exact verticalInfinityPolynomialEvaluation_eq_zero W) hp)

/-- Coordinate-ring map from the actual `Y ≠ 0` chart of the reduced cubic
to the vertical source chart. -/
noncomputable def verticalAdditionToInfinityRing
    (W : WeierstrassCurve F) :
    coveringChartCoordinateRing W false →+* verticalChartCoordinateRing W :=
  (verticalAdditionToInfinityEquationRing W).comp
    (infinityEquationCoveringChartRingEquiv W).symm.toRingHom

private theorem vertical_equiv_symm_coefficient
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

@[simp]
theorem verticalAdditionToInfinityRing_coefficient
    (W : WeierstrassCurve F) (a : F) :
    verticalAdditionToInfinityRing W
        (coveringChartStructureRingHom W false a) =
      verticalChartCoefficientHom W a := by
  rw [verticalAdditionToInfinityRing, RingHom.comp_apply]
  change verticalAdditionToInfinityEquationRing W
      ((infinityEquationCoveringChartRingEquiv W).symm
        (coveringChartStructureRingHom W false a)) = _
  rw [vertical_equiv_symm_coefficient]
  simp [verticalAdditionToInfinityEquationRing,
    verticalInfinityPolynomialEvaluation]

theorem verticalAdditionToInfinityRing_comp_coefficient
    (W : WeierstrassCurve F) :
    (verticalAdditionToInfinityRing W).comp
        (coveringChartStructureRingHom W false) =
      verticalChartCoefficientHom W := by
  ext a
  exact verticalAdditionToInfinityRing_coefficient W a

private theorem vertical_equiv_symm_outerX
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

private theorem vertical_equiv_symm_innerX
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

@[simp]
theorem verticalAdditionToInfinityRing_outerX
    (W : WeierstrassCurve F) :
    verticalAdditionToInfinityRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 0)) =
      verticalChartXOverY W := by
  change verticalAdditionToInfinityEquationRing W
      ((infinityEquationCoveringChartRingEquiv W).symm
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 0))) = _
  rw [vertical_equiv_symm_outerX]
  simp [verticalAdditionToInfinityEquationRing,
    verticalInfinityPolynomialEvaluation]

@[simp]
theorem verticalAdditionToInfinityRing_innerX
    (W : WeierstrassCurve F) :
    verticalAdditionToInfinityRing W
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 2)) =
      verticalChartZOverY W := by
  change verticalAdditionToInfinityEquationRing W
      ((infinityEquationCoveringChartRingEquiv W).symm
        (Ideal.Quotient.mk (coveringChartIdeal W false)
          (coordinateChartRatio (K := F) 1 2))) = _
  rw [vertical_equiv_symm_innerX]
  simp [verticalAdditionToInfinityEquationRing,
    verticalInfinityPolynomialEvaluation]

end InfinityChart

section SecantCompatibility

variable {F : Type u} [Field F]

/-- Clearing the square of the secant denominator from the affine output
abscissa gives the vertical homogeneous numerator. -/
theorem secantChartAddX_mul_verticalB_sq (W : WeierstrassCurve F) :
    secantChartAddX W *
        algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
          (verticalAdditionB W) ^ 2 =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (verticalAddXNumerator W) := by
  have hslope : secantChartSlope W *
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (verticalAdditionB W) =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (verticalAdditionA W) := by
    simpa [verticalAdditionA, verticalAdditionB,
      secantChartX₁_eq_algebraMap_pairX₁,
      secantChartX₂_eq_algebraMap_pairX₂,
      secantChartY₁_eq_algebraMap_pairY₁,
      secantChartY₂_eq_algebraMap_pairY₂, map_sub] using
      secantChartSlope_mul_sub W
  simp only [secantChartAddX, WeierstrassCurve.Affine.addX]
  unfold verticalAddXNumerator
  simp only [map_add, map_sub, map_mul, map_pow]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]
  change
    (secantChartSlope W ^ 2 +
          secantCoefficientHom W W.a₁ * secantChartSlope W -
          secantCoefficientHom W W.a₂ - secantChartX₁ W - secantChartX₂ W) *
        algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
          (verticalAdditionB W) ^ 2 = _
  calc
    _ = (secantChartSlope W *
          algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
            (verticalAdditionB W)) ^ 2 +
        secantCoefficientHom W W.a₁ *
          (secantChartSlope W *
            algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
              (verticalAdditionB W)) *
          algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
            (verticalAdditionB W) -
        (secantCoefficientHom W W.a₂ + secantChartX₁ W + secantChartX₂ W) *
          algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
            (verticalAdditionB W) ^ 2 := by ring
    _ = _ := by
      rw [hslope]
      simp only [verticalAdditionA, verticalAdditionB,
        secantChartX₁_eq_algebraMap_pairX₁,
        secantChartX₂_eq_algebraMap_pairX₂, secantCoefficientHom, map_sub]
      rfl

/-- Clearing the cube of the secant denominator from the affine output
ordinate gives the vertical homogeneous numerator. -/
theorem secantChartAddY_mul_verticalB_cube (W : WeierstrassCurve F) :
    secantChartAddY W *
        algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
          (verticalAdditionB W) ^ 3 =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (verticalAddYNumerator W) := by
  have hslope : secantChartSlope W *
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (verticalAdditionB W) =
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (verticalAdditionA W) := by
    simpa [verticalAdditionA, verticalAdditionB,
      secantChartX₁_eq_algebraMap_pairX₁,
      secantChartX₂_eq_algebraMap_pairX₂,
      secantChartY₁_eq_algebraMap_pairY₁,
      secantChartY₂_eq_algebraMap_pairY₂, map_sub] using
      secantChartSlope_mul_sub W
  have hX := secantChartAddX_mul_verticalB_sq W
  simp only [secantChartAddY, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX]
  unfold verticalAddYNumerator
  simp only [map_add, map_sub, map_neg, map_mul, map_pow]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃]
  change
    (-((secantChartSlope W * (secantChartAddX W - secantChartX₁ W) +
          secantChartY₁ W)) - secantCoefficientHom W W.a₁ *
        secantChartAddX W - secantCoefficientHom W W.a₃) *
      algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
        (verticalAdditionB W) ^ 3 = _
  calc
    _ = -(secantChartSlope W *
          algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
            (verticalAdditionB W) +
          secantCoefficientHom W W.a₁ *
            algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
              (verticalAdditionB W)) *
        (secantChartAddX W *
          algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
            (verticalAdditionB W) ^ 2) +
      (secantChartSlope W *
        algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
          (verticalAdditionB W)) * secantChartX₁ W *
        algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
          (verticalAdditionB W) ^ 2 -
      (secantChartY₁ W + secantCoefficientHom W W.a₃) *
        algebraMap (secantPairCoordinateRing W) (secantChartCoordinateRing W)
          (verticalAdditionB W) ^ 3 := by ring
    _ = _ := by
      rw [hslope, hX]
      simp only [verticalAdditionA, verticalAdditionB,
        secantChartX₁_eq_algebraMap_pairX₁,
        secantChartY₁_eq_algebraMap_pairY₁, secantCoefficientHom, map_sub]
      rfl

end SecantCompatibility

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
