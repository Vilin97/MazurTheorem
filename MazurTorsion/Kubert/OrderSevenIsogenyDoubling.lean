/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.DoublingCoordinates
import MazurTorsion.Kubert.OrderSevenIsogeny
import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificate
import MazurTorsion.Kubert.OrderSevenIsogenyDoublingSpecialization

/-!
# Fixed-doubling compatibility for the explicit order-seven isogeny

This file proves the amount of multiplicative compatibility needed by the
order-`49` tower.  It uses denominator-free tangent-doubling coordinates and
homogeneous polynomial certificates, avoiding a case analysis for the full
binary addition law.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

private abbrev orderSevenVeluA6 := OrderSevenDoublingSpecialization.a₆
private abbrev orderSevenVeluA5 := OrderSevenDoublingSpecialization.a₅
private abbrev orderSevenVeluA4 := OrderSevenDoublingSpecialization.a₄
private abbrev orderSevenVeluA3 := OrderSevenDoublingSpecialization.a₃
private abbrev orderSevenVeluA2 := OrderSevenDoublingSpecialization.a₂
private abbrev orderSevenVeluA1 := OrderSevenDoublingSpecialization.a₁
private abbrev orderSevenVeluA0 := OrderSevenDoublingSpecialization.a₀

/-- Homogenization of the cleared order-seven Vélu abscissa numerator. -/
def orderSevenVeluXNumeratorHomogeneous
    {R : Type*} [CommRing R] (d u v : R) : R :=
  u ^ 7 - 2 * d * (d - 1) * (d + 1) * u ^ 6 * v +
    d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1) *
        u ^ 5 * v ^ 2 -
    d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1) *
        u ^ 4 * v ^ 3 +
    d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1) *
        u ^ 3 * v ^ 4 -
    d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3) * u ^ 2 * v ^ 5 +
    d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3) * u * v ^ 6 +
    d ^ 10 * (d - 1) ^ 6 * v ^ 7

/-- Homogenization of the cleared order-seven Vélu differential numerator. -/
def orderSevenVeluDifferentialNumeratorHomogeneous
    {R : Type*} [CommRing R] (d u v : R) : R :=
  u ^ 9 - 3 * d * (d - 1) * (d + 1) * u ^ 8 * v -
    d * (d - 1) *
      (d ^ 5 - 2 * d ^ 4 - 12 * d ^ 3 + 14 * d ^ 2 - 3 * d + 1) *
        u ^ 7 * v ^ 2 -
    d ^ 2 * (d - 1) ^ 2 *
      (d ^ 6 - 9 * d ^ 5 + 25 * d ^ 4 - 22 * d ^ 3 +
        16 * d ^ 2 - 4 * d + 1) * u ^ 6 * v ^ 3 +
    3 * d ^ 4 * (d - 1) ^ 3 *
      (d ^ 4 - 7 * d ^ 3 + 13 * d ^ 2 + 2) * u ^ 5 * v ^ 4 +
    d ^ 5 * (d - 1) ^ 4 *
      (d ^ 6 - 10 * d ^ 5 + 35 * d ^ 4 - 36 * d ^ 3 -
        21 * d ^ 2 - 18 * d - 1) * u ^ 4 * v ^ 5 +
    d ^ 7 * (d - 1) ^ 5 *
      (d ^ 5 - 5 * d ^ 4 - 3 * d ^ 3 + 27 * d ^ 2 +
        30 * d + 5) * u ^ 3 * v ^ 6 +
    3 * d ^ 9 * (d - 1) ^ 6 *
      (d ^ 3 - 2 * d ^ 2 - 8 * d - 3) * u ^ 2 * v ^ 7 -
    d ^ 11 * (d - 1) ^ 7 * (d ^ 2 - 7 * d - 7) * u * v ^ 8 -
    2 * d ^ 13 * (d - 1) ^ 8 * v ^ 9

@[simp] theorem orderSevenVeluXNumeratorHomogeneous_at_one
    (d x : ℚ) :
    orderSevenVeluXNumeratorHomogeneous d x 1 =
      orderSevenVeluXNumerator d x := by
  simp only [orderSevenVeluXNumeratorHomogeneous,
    orderSevenVeluXNumerator]
  ring

@[simp] theorem orderSevenVeluDifferentialNumeratorHomogeneous_at_one
    (d x : ℚ) :
    orderSevenVeluDifferentialNumeratorHomogeneous d x 1 =
      orderSevenVeluDifferentialNumerator d x := by
  simp only [orderSevenVeluDifferentialNumeratorHomogeneous,
    orderSevenVeluDifferentialNumerator]
  ring

private theorem derivativeVeluXHomogeneous_eq
    (d u v : ℚ) :
    OrderSevenDoublingDerivative.veluXHomogeneous
        (orderSevenVeluA6 d) (orderSevenVeluA5 d)
        (orderSevenVeluA4 d) (orderSevenVeluA3 d)
        (orderSevenVeluA2 d) (orderSevenVeluA1 d)
        (orderSevenVeluA0 d) u v =
      orderSevenVeluXNumeratorHomogeneous d u v := by
  simp only [OrderSevenDoublingDerivative.veluXHomogeneous,
    orderSevenVeluXNumeratorHomogeneous, orderSevenVeluA6,
    orderSevenVeluA5, orderSevenVeluA4, orderSevenVeluA3,
    orderSevenVeluA2, orderSevenVeluA1, orderSevenVeluA0,
    OrderSevenDoublingSpecialization.a₆,
    OrderSevenDoublingSpecialization.a₅,
    OrderSevenDoublingSpecialization.a₄,
    OrderSevenDoublingSpecialization.a₃,
    OrderSevenDoublingSpecialization.a₂,
    OrderSevenDoublingSpecialization.a₁,
    OrderSevenDoublingSpecialization.a₀]
  ring

private theorem derivativeVeluDifferentialHomogeneous_eq
    (d u v : ℚ) :
    OrderSevenDoublingDerivative.veluDifferentialHomogeneous
        (orderSevenVeluA6 d) (orderSevenVeluA5 d)
        (orderSevenVeluA4 d) (orderSevenVeluA3 d)
        (orderSevenVeluA2 d) (orderSevenVeluA1 d)
        (orderSevenVeluA0 d) (orderSevenB d) (orderSevenC d) u v =
      orderSevenVeluDifferentialNumeratorHomogeneous d u v := by
  simp only [OrderSevenDoublingDerivative.veluDifferentialHomogeneous,
    OrderSevenDoublingDerivative.veluXHomogeneous,
    OrderSevenDoublingDerivative.kernelHomogeneous,
    orderSevenVeluDifferentialNumeratorHomogeneous, orderSevenVeluA6,
    orderSevenVeluA5, orderSevenVeluA4, orderSevenVeluA3,
    orderSevenVeluA2, orderSevenVeluA1, orderSevenVeluA0,
    OrderSevenDoublingSpecialization.a₆,
    OrderSevenDoublingSpecialization.a₅,
    OrderSevenDoublingSpecialization.a₄,
    OrderSevenDoublingSpecialization.a₃,
    OrderSevenDoublingSpecialization.a₂,
    OrderSevenDoublingSpecialization.a₁,
    OrderSevenDoublingSpecialization.a₀,
    orderSevenB, orderSevenC]
  ring

private theorem orderSevenVeluX_double_homogeneous (d x : ℚ) :
    orderSevenVeluXNumeratorHomogeneous d
        (Doubling.xNumerator (orderSevenFamily d) x)
        (Doubling.completedCubic (orderSevenFamily d) x) =
      Doubling.xNumeratorHomogeneous (orderSevenQuotient d)
        (orderSevenVeluXNumerator d x)
        (orderSevenKernelPolynomial d x ^ 2) := by
  have h := congrArg (Polynomial.eval x)
    (OrderSevenDoublingCertificate.polynomial_identity d)
  simpa [OrderSevenDoublingCertificate.veluXHomogeneousPolynomial,
    OrderSevenDoublingCertificate.sourceDoubleXPolynomial,
    OrderSevenDoublingCertificate.sourceCompletedCubicPolynomial,
    OrderSevenDoublingCertificate.doubleXHomogeneousPolynomial,
    OrderSevenDoublingCertificate.veluXPolynomial,
    OrderSevenDoublingCertificate.kernelPolynomial,
    orderSevenVeluXNumeratorHomogeneous,
    orderSevenVeluXNumerator, orderSevenKernelPolynomial,
    Doubling.xNumerator, Doubling.completedCubic,
    Doubling.xNumeratorHomogeneous] using h

private theorem derivative_doubleX_certificate (d : ℚ) :
    OrderSevenDoublingDerivative.composedVeluX
        (orderSevenVeluA6 d) (orderSevenVeluA5 d)
        (orderSevenVeluA4 d) (orderSevenVeluA3 d)
        (orderSevenVeluA2 d) (orderSevenVeluA1 d)
        (orderSevenVeluA0 d) (orderSevenFamily d) =
      OrderSevenDoublingDerivative.targetDoubleX
        (orderSevenQuotient d)
        (orderSevenVeluA6 d) (orderSevenVeluA5 d)
        (orderSevenVeluA4 d) (orderSevenVeluA3 d)
        (orderSevenVeluA2 d) (orderSevenVeluA1 d)
        (orderSevenVeluA0 d) (orderSevenB d) (orderSevenC d) := by
  apply Polynomial.funext
  intro x
  have h := orderSevenVeluX_double_homogeneous d x
  simpa only [OrderSevenDoublingDerivative.composedVeluX,
    OrderSevenDoublingDerivative.targetDoubleX,
    OrderSevenDoublingDerivative.sourceDoubleX,
    OrderSevenDoublingDerivative.sourceCompletedCubic,
    OrderSevenDoublingDerivative.baseVeluX,
    OrderSevenDoublingDerivative.baseKernel,
    OrderSevenDoublingDerivative.eval_veluXPolynomial,
    OrderSevenDoublingDerivative.eval_doubleXPolynomial,
    OrderSevenDoublingDerivative.eval_completedCubicPolynomial,
    OrderSevenDoublingDerivative.eval_kernelPolynomial,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow,
    Doubling.xNumeratorHomogeneous_at_one,
    Doubling.completedCubicHomogeneous_at_one,
    derivativeVeluXHomogeneous_eq,
    orderSevenVeluXNumeratorHomogeneous_at_one,
    OrderSevenDoublingDerivative.kernelHomogeneous,
    orderSevenKernelPolynomial, mul_one] using h

private theorem orderSevenVeluX_double_homogeneous_of_abscissa
    (d x x₂ : ℚ)
    (hx₂ : Doubling.xNumerator (orderSevenFamily d) x =
      x₂ * Doubling.completedCubic (orderSevenFamily d) x) :
    orderSevenVeluXNumerator d x₂ *
        Doubling.completedCubic (orderSevenFamily d) x ^ 7 =
      Doubling.xNumeratorHomogeneous (orderSevenQuotient d)
        (orderSevenVeluXNumerator d x)
        (orderSevenKernelPolynomial d x ^ 2) := by
  rw [← orderSevenVeluXNumeratorHomogeneous_at_one]
  calc
    orderSevenVeluXNumeratorHomogeneous d x₂ 1 *
          Doubling.completedCubic (orderSevenFamily d) x ^ 7 =
        orderSevenVeluXNumeratorHomogeneous d
          (x₂ * Doubling.completedCubic (orderSevenFamily d) x)
          (Doubling.completedCubic (orderSevenFamily d) x) := by
      simp only [orderSevenVeluXNumeratorHomogeneous]
      ring
    _ = orderSevenVeluXNumeratorHomogeneous d
          (Doubling.xNumerator (orderSevenFamily d) x)
          (Doubling.completedCubic (orderSevenFamily d) x) := by
      rw [hx₂]
    _ = Doubling.xNumeratorHomogeneous (orderSevenQuotient d)
          (orderSevenVeluXNumerator d x)
          (orderSevenKernelPolynomial d x ^ 2) :=
      orderSevenVeluX_double_homogeneous d x

private theorem orderSeven_kernel_double_certificate (d x : ℚ) :
    let H := Doubling.completedCubic (orderSevenFamily d) x
    let p := Doubling.xNumerator (orderSevenFamily d) x
    p * (p - orderSevenB d * H) * (p - orderSevenC d * H) =
      orderSevenKernelPolynomial d x *
        orderSevenVeluDifferentialNumerator d x := by
  simp only [Doubling.completedCubic, Doubling.xNumerator,
    orderSevenVeluDifferentialNumerator,
    orderSevenFamily, orderSevenB, orderSevenC, tateNormalCurve,
    orderSevenKernelPolynomial, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private theorem orderSevenVeluDifferential_double_homogeneous
    (d x : ℚ)
    (hK : orderSevenKernelPolynomial d x ≠ 0)
    (hN : orderSevenVeluDifferentialNumerator d x ≠ 0) :
    orderSevenVeluDifferentialNumeratorHomogeneous d
        (Doubling.xNumerator (orderSevenFamily d) x)
        (Doubling.completedCubic (orderSevenFamily d) x) *
          Doubling.completedYNumerator (orderSevenFamily d) x =
      Doubling.completedYNumeratorHomogeneous (orderSevenQuotient d)
        (orderSevenVeluXNumerator d x)
        (orderSevenKernelPolynomial d x ^ 2) := by
  have hK' :
      (OrderSevenDoublingDerivative.baseKernel
        (orderSevenB d) (orderSevenC d)).eval x ≠ 0 := by
    simpa [OrderSevenDoublingDerivative.baseKernel,
      OrderSevenDoublingDerivative.kernelPolynomial,
      OrderSevenDoublingDerivative.kernelHomogeneous,
      orderSevenKernelPolynomial] using hK
  have hN' :
      (OrderSevenDoublingDerivative.baseVeluDifferential
        (orderSevenVeluA6 d) (orderSevenVeluA5 d)
        (orderSevenVeluA4 d) (orderSevenVeluA3 d)
        (orderSevenVeluA2 d) (orderSevenVeluA1 d)
        (orderSevenVeluA0 d) (orderSevenB d) (orderSevenC d)).eval x ≠ 0 := by
    rw [OrderSevenDoublingSpecialization.baseVeluDifferential_eq]
    simpa using hN
  have h := OrderSevenDoublingDerivative.vertical_at_point
    (orderSevenVeluA6 d) (orderSevenVeluA5 d)
    (orderSevenVeluA4 d) (orderSevenVeluA3 d)
    (orderSevenVeluA2 d) (orderSevenVeluA1 d)
    (orderSevenVeluA0 d) (orderSevenB d) (orderSevenC d)
    (orderSevenFamily d) (orderSevenQuotient d) x
    (derivative_doubleX_certificate d)
    (OrderSevenDoublingSpecialization.kernel_polynomial_identity d)
    (OrderSevenDoublingSpecialization.landing_polynomial_identity d)
    hK' hN'
  have h' := h
  simp only [OrderSevenDoublingDerivative.composedVeluDifferential,
    OrderSevenDoublingDerivative.sourceDoubleX,
    OrderSevenDoublingDerivative.sourceCompletedCubic,
    OrderSevenDoublingDerivative.sourceDoubleCompletedY,
    OrderSevenDoublingDerivative.targetDoubleCompletedY,
    OrderSevenDoublingDerivative.baseVeluX,
    OrderSevenDoublingDerivative.baseKernel,
    OrderSevenDoublingDerivative.eval_veluDifferentialPolynomial,
    OrderSevenDoublingDerivative.eval_doubleXPolynomial,
    OrderSevenDoublingDerivative.eval_completedCubicPolynomial,
    OrderSevenDoublingDerivative.eval_doubleCompletedYPolynomial,
    OrderSevenDoublingDerivative.eval_veluXPolynomial,
    OrderSevenDoublingDerivative.eval_kernelPolynomial,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow,
    Doubling.xNumeratorHomogeneous_at_one,
    Doubling.completedCubicHomogeneous_at_one,
    Doubling.completedYNumeratorHomogeneous_at_one] at h'
  rw [derivativeVeluDifferentialHomogeneous_eq,
    derivativeVeluXHomogeneous_eq] at h'
  simpa [OrderSevenDoublingDerivative.kernelHomogeneous,
    orderSevenKernelPolynomial] using h'

private theorem orderSevenVeluDifferential_double_homogeneous_of_abscissa
    (d x x₂ : ℚ)
    (hx₂ : Doubling.xNumerator (orderSevenFamily d) x =
      x₂ * Doubling.completedCubic (orderSevenFamily d) x)
    (hK : orderSevenKernelPolynomial d x ≠ 0)
    (hN : orderSevenVeluDifferentialNumerator d x ≠ 0) :
    orderSevenVeluDifferentialNumerator d x₂ *
          Doubling.completedCubic (orderSevenFamily d) x ^ 9 *
        Doubling.completedYNumerator (orderSevenFamily d) x =
      Doubling.completedYNumeratorHomogeneous (orderSevenQuotient d)
        (orderSevenVeluXNumerator d x)
        (orderSevenKernelPolynomial d x ^ 2) := by
  rw [← orderSevenVeluDifferentialNumeratorHomogeneous_at_one]
  calc
    orderSevenVeluDifferentialNumeratorHomogeneous d x₂ 1 *
          Doubling.completedCubic (orderSevenFamily d) x ^ 9 *
        Doubling.completedYNumerator (orderSevenFamily d) x =
      orderSevenVeluDifferentialNumeratorHomogeneous d
          (x₂ * Doubling.completedCubic (orderSevenFamily d) x)
          (Doubling.completedCubic (orderSevenFamily d) x) *
        Doubling.completedYNumerator (orderSevenFamily d) x := by
      simp only [orderSevenVeluDifferentialNumeratorHomogeneous]
      ring
    _ = orderSevenVeluDifferentialNumeratorHomogeneous d
          (Doubling.xNumerator (orderSevenFamily d) x)
          (Doubling.completedCubic (orderSevenFamily d) x) *
        Doubling.completedYNumerator (orderSevenFamily d) x := by
      rw [hx₂]
    _ = Doubling.completedYNumeratorHomogeneous (orderSevenQuotient d)
          (orderSevenVeluXNumerator d x)
          (orderSevenKernelPolynomial d x ^ 2) :=
      orderSevenVeluDifferential_double_homogeneous d x hK hN

private theorem kernelPolynomial_at_double
    {b c H p x₂ K N : ℚ}
    (hp : p = x₂ * H)
    (hcert : p * (p - b * H) * (p - c * H) = K * N) :
    x₂ * (x₂ - b) * (x₂ - c) * H ^ 3 = K * N := by
  rw [hp] at hcert
  linear_combination hcert

private theorem quotient_doubleX_of_homogeneous
    {H F₂ K₂ K N PhiT : ℚ}
    (hH : H ≠ 0) (hK : K ≠ 0) (hN : N ≠ 0) (hK₂ : K₂ ≠ 0)
    (hkernel : K₂ * H ^ 3 = K * N)
    (hhom : F₂ * H ^ 7 = PhiT) :
    F₂ / K₂ ^ 2 =
      (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := by
  field_simp [hH, hK, hN, hK₂]
  have hkernel₂ : K₂ ^ 2 * H ^ 6 = K ^ 2 * N ^ 2 := by
    calc
      K₂ ^ 2 * H ^ 6 = (K₂ * H ^ 3) ^ 2 := by ring
      _ = (K * N) ^ 2 := by rw [hkernel]
      _ = K ^ 2 * N ^ 2 := by ring
  calc
    F₂ * K ^ 2 * N ^ 2 * H = F₂ * (K ^ 2 * N ^ 2) * H := by ring
    _ = F₂ * (K₂ ^ 2 * H ^ 6) * H := by rw [← hkernel₂]
    _ = K₂ ^ 2 * (F₂ * H ^ 7) := by ring
    _ = K₂ ^ 2 * PhiT := by rw [hhom]

private theorem quotient_doubleCompletedY_of_homogeneous
    {V H R V₂ N₂ K₂ K N RT : ℚ}
    (hV : V ≠ 0) (hK : K ≠ 0) (hN : N ≠ 0) (hK₂ : K₂ ≠ 0)
    (hH : H = V ^ 2)
    (hsource : V ^ 3 * V₂ = R)
    (hkernel : K₂ * H ^ 3 = K * N)
    (hhom : N₂ * H ^ 9 * R = RT) :
    (N₂ / K₂ ^ 3) * V₂ =
      (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := by
  field_simp [hV, hK, hN, hK₂]
  rw [hH] at hkernel hhom
  have hkernel₃ : K₂ ^ 3 * V ^ 18 = K ^ 3 * N ^ 3 := by
    calc
      K₂ ^ 3 * V ^ 18 = (K₂ * (V ^ 2) ^ 3) ^ 3 := by ring
      _ = (K * N) ^ 3 := by rw [hkernel]
      _ = K ^ 3 * N ^ 3 := by ring
  calc
    N₂ * V₂ * K ^ 3 * N ^ 3 * V ^ 3 =
        N₂ * V₂ * (K ^ 3 * N ^ 3) * V ^ 3 := by ring
    _ = N₂ * V₂ * (K₂ ^ 3 * V ^ 18) * V ^ 3 := by
      rw [← hkernel₃]
    _ = K₂ ^ 3 * (N₂ * V ^ 18 * (V ^ 3 * V₂)) := by ring
    _ = K₂ ^ 3 * (N₂ * V ^ 18 * R) := by rw [hsource]
    _ = K₂ ^ 3 * RT := by
      rw [← hhom]
      ring

private theorem xNumerator_div_square
    (W : WeierstrassCurve ℚ) {u k : ℚ} (hk : k ≠ 0) :
    Doubling.xNumerator W (u / k ^ 2) =
      Doubling.xNumeratorHomogeneous W u (k ^ 2) / k ^ 8 := by
  simp only [Doubling.xNumerator, Doubling.xNumeratorHomogeneous]
  field_simp [hk]

private theorem completedYNumerator_div_square
    (W : WeierstrassCurve ℚ) {u k : ℚ} (hk : k ≠ 0) :
    Doubling.completedYNumerator W (u / k ^ 2) =
      Doubling.completedYNumeratorHomogeneous W u (k ^ 2) /
        k ^ 12 := by
  simp only [Doubling.completedYNumerator,
    Doubling.completedYNumeratorHomogeneous]
  field_simp [hk]

private theorem two_nsmul_ne_zero_of_order_fortyNine
    {G : Type*} [AddCommGroup G] {P : G}
    (hP : addOrderOf P = 49) :
    (2 : ℕ) • P ≠ 0 := by
  intro hzero
  have hdvd : (49 : ℕ) ∣ 2 := by
    rw [← hP]
    exact addOrderOf_dvd_of_nsmul_eq_zero hzero
  norm_num at hdvd

private def OrderSevenDoublingCoordinates (d x y : ℚ) : Prop :=
  let W := (orderSevenFamily d).toAffine
  let Wq := (orderSevenQuotient d).toAffine
  let m := W.slope x x y y
  let x₂ := W.addX x x m
  let y₂ := W.addY x x y m
  let X := orderSevenVeluX d x
  let Y := orderSevenVeluY d x y
  let M := Wq.slope X X Y Y
  let X₂ := Wq.addX X X M
  let Y₂ := Wq.addY X X Y M
  orderSevenVeluX d x₂ = X₂ ∧
    2 * orderSevenVeluY d x₂ y₂ +
        Wq.a₁ * orderSevenVeluX d x₂ + Wq.a₃ =
      2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃

private theorem orderSevenVeluPoint_two_nsmul_of_coordinates
    {d x y x₂ y₂ : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hP₂ : (orderSevenFamily d).toAffine.Nonsingular x₂ y₂)
    (hx0 : x ≠ 0) (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d)
    (hx0₂ : x₂ ≠ 0) (hxb₂ : x₂ ≠ orderSevenB d)
    (hxc₂ : x₂ ≠ orderSevenC d)
    (hcompletedY :
      2 * orderSevenVeluY d x y +
          (orderSevenQuotient d).toAffine.a₁ * orderSevenVeluX d x +
          (orderSevenQuotient d).toAffine.a₃ ≠ 0)
    (hX : orderSevenVeluX d x₂ =
      (orderSevenQuotient d).toAffine.addX
        (orderSevenVeluX d x) (orderSevenVeluX d x)
        ((orderSevenQuotient d).toAffine.slope
          (orderSevenVeluX d x) (orderSevenVeluX d x)
          (orderSevenVeluY d x y) (orderSevenVeluY d x y)))
    (hcompleted :
      2 * orderSevenVeluY d x₂ y₂ +
          (orderSevenQuotient d).toAffine.a₁ * orderSevenVeluX d x₂ +
          (orderSevenQuotient d).toAffine.a₃ =
        2 * (orderSevenQuotient d).toAffine.addY
            (orderSevenVeluX d x) (orderSevenVeluX d x)
            (orderSevenVeluY d x y)
            ((orderSevenQuotient d).toAffine.slope
              (orderSevenVeluX d x) (orderSevenVeluX d x)
              (orderSevenVeluY d x y) (orderSevenVeluY d x y)) +
          (orderSevenQuotient d).toAffine.a₁ *
            (orderSevenQuotient d).toAffine.addX
              (orderSevenVeluX d x) (orderSevenVeluX d x)
              ((orderSevenQuotient d).toAffine.slope
                (orderSevenVeluX d x) (orderSevenVeluX d x)
                (orderSevenVeluY d x y) (orderSevenVeluY d x y)) +
          (orderSevenQuotient d).toAffine.a₃) :
    orderSevenVeluPoint hP₂ hx0₂ hxb₂ hxc₂ =
      (2 : ℕ) • orderSevenVeluPoint hP hx0 hxb hxc := by
  have hYne : orderSevenVeluY d x y ≠
      (orderSevenQuotient d).toAffine.negY
        (orderSevenVeluX d x) (orderSevenVeluY d x y) := by
    intro hY
    apply hcompletedY
    simp only [WeierstrassCurve.Affine.negY] at hY
    linear_combination hY
  rw [two_nsmul]
  simp only [orderSevenVeluPoint]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hYne]
  apply WeierstrassCurve.Affine.Point.some_eq_some
    (orderSevenQuotient d)
  · exact hX
  · linear_combination
      (1 / 2 : ℚ) * hcompleted -
        ((orderSevenQuotient d).toAffine.a₁ / 2) * hX

private theorem orderSevenPointMap_two_nsmul_of_order_fortyNine_affine
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hcoordinates : OrderSevenDoublingCoordinates d x y) :
    orderSevenPointMap d
        ((2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          (orderSevenFamily d).toAffine.Point)) =
      (2 : ℕ) • orderSevenPointMap d
        (WeierstrassCurve.Affine.Point.some x y hP) := by
  let W := (orderSevenFamily d).toAffine
  let m := W.slope x x y y
  let x₂ := W.addX x x m
  let y₂ := W.addY x x y m
  have htwo_ne :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) ≠ 0 :=
    two_nsmul_ne_zero_of_order_fortyNine horder
  have hy : y ≠ W.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  let hP₂ : (orderSevenFamily d).toAffine.Nonsingular x₂ y₂ :=
    W.nonsingular_add hP hP (fun hxy ↦ hy hxy.2)
  have hadd :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          (orderSevenFamily d).toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    rw [two_nsmul,
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  have horder₂ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ :
        (orderSevenFamily d).toAffine.Point) = 49 := by
    rw [← hadd, addOrderOf_nsmul'
      (WeierstrassCurve.Affine.Point.some x y hP) (by norm_num), horder]
    norm_num
  have hx := not_orderSevenKernelX_of_order_fortyNine hP horder
  have hx₂ := not_orderSevenKernelX_of_order_fortyNine hP₂ horder₂
  have hx0 : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxb : x ≠ orderSevenB d :=
    fun h ↦ hx (Or.inr (Or.inl h))
  have hxc : x ≠ orderSevenC d :=
    fun h ↦ hx (Or.inr (Or.inr h))
  have hx0₂ : x₂ ≠ 0 := fun h ↦ hx₂ (Or.inl h)
  have hxb₂ : x₂ ≠ orderSevenB d :=
    fun h ↦ hx₂ (Or.inr (Or.inl h))
  have hxc₂ : x₂ ≠ orderSevenC d :=
    fun h ↦ hx₂ (Or.inr (Or.inr h))
  have hK : orderSevenKernelPolynomial d x ≠ 0 :=
    mul_ne_zero (mul_ne_zero hx0 (sub_ne_zero.mpr hxb))
      (sub_ne_zero.mpr hxc)
  have hK₂ : orderSevenKernelPolynomial d x₂ ≠ 0 :=
    mul_ne_zero (mul_ne_zero hx0₂ (sub_ne_zero.mpr hxb₂))
      (sub_ne_zero.mpr hxc₂)
  have hv : 2 * y + (orderSevenFamily d).a₁ * x +
      (orderSevenFamily d).a₃ ≠ 0 := by
    intro hv
    apply hy
    simp only [W, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.toAffine]
    linarith
  have hH : Doubling.completedCubic (orderSevenFamily d) x ≠ 0 := by
    rw [Doubling.completedCubic_eq_completedY_sq
      (orderSevenFamily d) hP.1]
    exact pow_ne_zero 2 hv
  have hp : Doubling.xNumerator (orderSevenFamily d) x =
      x₂ * Doubling.completedCubic (orderSevenFamily d) x :=
    (Doubling.addX_self_mul_completedCubic
      (orderSevenFamily d) hP.1 hv).symm
  have hkernel :
      orderSevenKernelPolynomial d x₂ *
          Doubling.completedCubic (orderSevenFamily d) x ^ 3 =
        orderSevenKernelPolynomial d x *
          orderSevenVeluDifferentialNumerator d x := by
    exact kernelPolynomial_at_double hp
      (orderSeven_kernel_double_certificate d x)
  have hN : orderSevenVeluDifferentialNumerator d x ≠ 0 := by
    intro hN
    have hleft : orderSevenKernelPolynomial d x₂ *
        Doubling.completedCubic (orderSevenFamily d) x ^ 3 ≠ 0 :=
      mul_ne_zero hK₂ (pow_ne_zero 3 hH)
    apply hleft
    rw [hkernel, hN, mul_zero]
  have hdiff : orderSevenVeluDifferential d x ≠ 0 := by
    rw [orderSevenVeluDifferential_eq_div hx0 hxb hxc]
    exact div_ne_zero hN (pow_ne_zero 3 hK)
  have hcompletedY :
      2 * orderSevenVeluY d x y +
          (orderSevenQuotient d).toAffine.a₁ * orderSevenVeluX d x +
          (orderSevenQuotient d).toAffine.a₃ ≠ 0 := by
    rw [orderSevenVelu_completedY]
    exact mul_ne_zero hdiff hv
  obtain ⟨hX, hcompleted⟩ := hcoordinates
  rw [hadd, orderSevenPointMap_some_of_not_kernelX hP₂ hx₂,
    orderSevenPointMap_some_of_not_kernelX hP hx]
  exact orderSevenVeluPoint_two_nsmul_of_coordinates hP hP₂
    hx0 hxb hxc hx0₂ hxb₂ hxc₂ hcompletedY hX hcompleted

private theorem orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    (hcoordinates : ∀ {x y : ℚ}
      (hP : (orderSevenFamily d).toAffine.Nonsingular x y),
      addOrderOf
          (WeierstrassCurve.Affine.Point.some x y hP :
            (orderSevenFamily d).toAffine.Point) = 49 →
        OrderSevenDoublingCoordinates d x y)
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • orderSevenPointMap d Q := by
  cases Q with
  | zero =>
      have hfalse : (1 : ℕ) = 49 := by
        rw [← hQ]
        exact (addOrderOf_zero
          (G := (orderSevenFamily d).toAffine.Point)).symm
      norm_num at hfalse
  | some x y hP =>
      exact orderSevenPointMap_two_nsmul_of_order_fortyNine_affine
        hP hQ (hcoordinates hP hQ)

private theorem orderSevenVelu_double_coordinates
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49) :
    OrderSevenDoublingCoordinates d x y := by
  let W := orderSevenFamily d
  let Wq := orderSevenQuotient d
  let m := W.toAffine.slope x x y y
  let x₂ := W.toAffine.addX x x m
  let y₂ := W.toAffine.addY x x y m
  let X := orderSevenVeluX d x
  let Y := orderSevenVeluY d x y
  let M := Wq.toAffine.slope X X Y Y
  let X₂ := Wq.toAffine.addX X X M
  let Y₂ := Wq.toAffine.addY X X Y M
  change orderSevenVeluX d x₂ = X₂ ∧
    2 * orderSevenVeluY d x₂ y₂ + Wq.a₁ * orderSevenVeluX d x₂ +
        Wq.a₃ = 2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃
  have htwo_ne :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) ≠ 0 :=
    two_nsmul_ne_zero_of_order_fortyNine horder
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  let hP₂ : W.toAffine.Nonsingular x₂ y₂ :=
    W.toAffine.nonsingular_add hP hP (fun hxy ↦ hy hxy.2)
  have hadd :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          W.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    rw [two_nsmul,
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  have horder₂ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ :
        W.toAffine.Point) = 49 := by
    rw [← hadd, addOrderOf_nsmul'
      (WeierstrassCurve.Affine.Point.some x y hP) (by norm_num), horder]
    norm_num
  have hx := not_orderSevenKernelX_of_order_fortyNine hP horder
  have hx₂ := not_orderSevenKernelX_of_order_fortyNine hP₂ horder₂
  have hx0 : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxb : x ≠ orderSevenB d :=
    fun h ↦ hx (Or.inr (Or.inl h))
  have hxc : x ≠ orderSevenC d :=
    fun h ↦ hx (Or.inr (Or.inr h))
  have hx0₂ : x₂ ≠ 0 := fun h ↦ hx₂ (Or.inl h)
  have hxb₂ : x₂ ≠ orderSevenB d :=
    fun h ↦ hx₂ (Or.inr (Or.inl h))
  have hxc₂ : x₂ ≠ orderSevenC d :=
    fun h ↦ hx₂ (Or.inr (Or.inr h))
  let V := 2 * y + W.a₁ * x + W.a₃
  let V₂ := 2 * y₂ + W.a₁ * x₂ + W.a₃
  let H := Doubling.completedCubic W x
  let p := Doubling.xNumerator W x
  let K := orderSevenKernelPolynomial d x
  let K₂ := orderSevenKernelPolynomial d x₂
  let N := orderSevenVeluDifferentialNumerator d x
  let N₂ := orderSevenVeluDifferentialNumerator d x₂
  let F := orderSevenVeluXNumerator d x
  let F₂ := orderSevenVeluXNumerator d x₂
  let PhiT := Doubling.xNumeratorHomogeneous Wq F (K ^ 2)
  let R := Doubling.completedYNumerator W x
  let RT := Doubling.completedYNumeratorHomogeneous Wq F (K ^ 2)
  have hK : K ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hx0 (sub_ne_zero.mpr hxb))
      (sub_ne_zero.mpr hxc)
  have hK₂ : K₂ ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hx0₂ (sub_ne_zero.mpr hxb₂))
      (sub_ne_zero.mpr hxc₂)
  have hV : V ≠ 0 := by
    intro hV
    apply hy
    simp only [W, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.toAffine]
    linarith
  have hH_eq : H = V ^ 2 := by
    exact Doubling.completedCubic_eq_completedY_sq W hP.1
  have hH : H ≠ 0 := by
    rw [hH_eq]
    exact pow_ne_zero 2 hV
  have hp : p = x₂ * H := by
    exact (Doubling.addX_self_mul_completedCubic W hP.1 hV).symm
  have hkernel : K₂ * H ^ 3 = K * N := by
    exact kernelPolynomial_at_double hp
      (orderSeven_kernel_double_certificate d x)
  have hN : N ≠ 0 := by
    intro hN
    have hleft : K₂ * H ^ 3 ≠ 0 :=
      mul_ne_zero hK₂ (pow_ne_zero 3 hH)
    apply hleft
    rw [hkernel, hN, mul_zero]
  have hsourceY : V ^ 3 * V₂ = R := by
    exact Doubling.completedY_add_self W hP.1 hV
  have hhomX : F₂ * H ^ 7 = PhiT := by
    exact orderSevenVeluX_double_homogeneous_of_abscissa d x x₂ hp
  have hhomY : N₂ * H ^ 9 * R = RT := by
    exact orderSevenVeluDifferential_double_homogeneous_of_abscissa
      d x x₂ hp hK hN
  have hquotX :
      F₂ / K₂ ^ 2 =
        (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) :=
    quotient_doubleX_of_homogeneous hH hK hN hK₂ hkernel hhomX
  have hquotY :
      (N₂ / K₂ ^ 3) * V₂ =
        (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) :=
    quotient_doubleCompletedY_of_homogeneous hV hK hN hK₂
      hH_eq hsourceY hkernel hhomY
  have hxMap : X = F / K ^ 2 := by
    exact orderSevenVeluX_eq_div hx0 hxb hxc
  have hxMap₂ : orderSevenVeluX d x₂ = F₂ / K₂ ^ 2 := by
    exact orderSevenVeluX_eq_div hx0₂ hxb₂ hxc₂
  have hdiff : orderSevenVeluDifferential d x = N / K ^ 3 := by
    exact orderSevenVeluDifferential_eq_div hx0 hxb hxc
  have hdiff₂ : orderSevenVeluDifferential d x₂ = N₂ / K₂ ^ 3 := by
    exact orderSevenVeluDifferential_eq_div hx0₂ hxb₂ hxc₂
  have hcurveImage : Wq.toAffine.Equation X Y := by
    exact orderSevenVelu_equation hP.1 hx0 hxb hxc
  have himageV : 2 * Y + Wq.a₁ * X + Wq.a₃ = N / K ^ 3 * V := by
    calc
      2 * Y + Wq.a₁ * X + Wq.a₃ =
          orderSevenVeluDifferential d x * V :=
        orderSevenVelu_completedY d x y
      _ = N / K ^ 3 * V := by rw [hdiff]
  have himageV_ne : 2 * Y + Wq.a₁ * X + Wq.a₃ ≠ 0 := by
    rw [himageV]
    exact mul_ne_zero (div_ne_zero hN (pow_ne_zero 3 hK)) hV
  have htargetH :
      Doubling.completedCubic Wq X = (N / K ^ 3) ^ 2 * H := by
    have hsquare := orderSevenVelu_completedSquare hx0 hxb hxc
    change orderSevenVeluDifferential d x ^ 2 * H =
      Doubling.completedCubic Wq X at hsquare
    rw [hdiff] at hsquare
    exact hsquare.symm
  have htargetH_ne : (N / K ^ 3) ^ 2 * H ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (div_ne_zero hN (pow_ne_zero 3 hK))) hH
  have htargetNumerator :
      Doubling.xNumerator Wq X = PhiT / K ^ 8 := by
    rw [hxMap]
    exact xNumerator_div_square Wq hK
  have htargetCompletedYNumerator :
      Doubling.completedYNumerator Wq X = RT / K ^ 12 := by
    rw [hxMap]
    exact completedYNumerator_div_square Wq hK
  have htargetXmul :
      X₂ * Doubling.completedCubic Wq X =
        Doubling.xNumerator Wq X := by
    exact Doubling.addX_self_mul_completedCubic Wq hcurveImage himageV_ne
  have htargetX :
      X₂ = (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := by
    apply (eq_div_iff htargetH_ne).2
    calc
      X₂ * ((N / K ^ 3) ^ 2 * H) =
          X₂ * Doubling.completedCubic Wq X := by rw [htargetH]
      _ = Doubling.xNumerator Wq X := htargetXmul
      _ = PhiT / K ^ 8 := htargetNumerator
  have htargetYmul :
      (2 * Y + Wq.a₁ * X + Wq.a₃) ^ 3 *
          (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) =
        Doubling.completedYNumerator Wq X := by
    exact Doubling.completedY_add_self Wq hcurveImage himageV_ne
  have htargetY :
      2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃ =
        (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := by
    apply (eq_div_iff (pow_ne_zero 3
      (mul_ne_zero (div_ne_zero hN (pow_ne_zero 3 hK)) hV))).2
    calc
      (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) *
          (N / K ^ 3 * V) ^ 3 =
        (2 * Y + Wq.a₁ * X + Wq.a₃) ^ 3 *
          (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) := by
            rw [himageV]
            ring
      _ = Doubling.completedYNumerator Wq X := htargetYmul
      _ = RT / K ^ 12 := htargetCompletedYNumerator
  constructor
  · calc
      orderSevenVeluX d x₂ = F₂ / K₂ ^ 2 := hxMap₂
      _ = (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := hquotX
      _ = X₂ := htargetX.symm
  · calc
      2 * orderSevenVeluY d x₂ y₂ +
          Wq.a₁ * orderSevenVeluX d x₂ + Wq.a₃ =
        orderSevenVeluDifferential d x₂ * V₂ :=
          orderSevenVelu_completedY d x₂ y₂
      _ = (N₂ / K₂ ^ 3) * V₂ := by rw [hdiff₂]
      _ = (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := hquotY
      _ = 2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃ := htargetY.symm

/-- On an exact-order-`49` point, the explicit total order-seven Vélu map
commutes with tangent doubling. -/
theorem orderSevenPointMap_two_nsmul_of_order_fortyNine
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    orderSevenPointMap d ((2 : ℕ) • Q) =
      (2 : ℕ) • orderSevenPointMap d Q := by
  apply orderSevenPointMap_two_nsmul_of_order_fortyNine_of_coordinates
    (fun hP horder ↦ orderSevenVelu_double_coordinates hP horder)
  exact hQ

/-- If `7 • Q` lies in the explicit zero fiber, doubling compatibility and
translation invariance force the Vélu map to commute with that multiple. -/
theorem orderSevenPointMap_seven_nsmul_of_order_fortyNine
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • orderSevenPointMap d Q := by
  have h2Q : addOrderOf ((2 : ℕ) • Q) = 49 := by
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have h4Q : addOrderOf ((4 : ℕ) • Q) = 49 := by
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have hdoubleQ :=
    orderSevenPointMap_two_nsmul_of_order_fortyNine hQ
  have hdouble2Q := orderSevenPointMap_two_nsmul_of_order_fortyNine
    (Q := (2 : ℕ) • Q) h2Q
  have hdouble4Q := orderSevenPointMap_two_nsmul_of_order_fortyNine
    (Q := (4 : ℕ) • Q) h4Q
  have hmap4 : orderSevenPointMap d ((4 : ℕ) • Q) =
      (4 : ℕ) • orderSevenPointMap d Q := by
    calc
      orderSevenPointMap d ((4 : ℕ) • Q) =
          orderSevenPointMap d ((2 : ℕ) • ((2 : ℕ) • Q)) := by
            rw [← mul_nsmul]
      _ = (2 : ℕ) • orderSevenPointMap d ((2 : ℕ) • Q) :=
        hdouble2Q
      _ = (2 : ℕ) • ((2 : ℕ) • orderSevenPointMap d Q) := by
        rw [hdoubleQ]
      _ = (4 : ℕ) • orderSevenPointMap d Q := by
        rw [← mul_nsmul]
  have hmap8 : orderSevenPointMap d ((8 : ℕ) • Q) =
      (8 : ℕ) • orderSevenPointMap d Q := by
    calc
      orderSevenPointMap d ((8 : ℕ) • Q) =
          orderSevenPointMap d ((2 : ℕ) • ((4 : ℕ) • Q)) := by
            rw [← mul_nsmul]
      _ = (2 : ℕ) • orderSevenPointMap d ((4 : ℕ) • Q) :=
        hdouble4Q
      _ = (2 : ℕ) • ((4 : ℕ) • orderSevenPointMap d Q) := by
        rw [hmap4]
      _ = (8 : ℕ) • orderSevenPointMap d Q := by
        rw [← mul_nsmul]
  obtain ⟨n, _hn, h7Q⟩ :=
    exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero hkernel
  have hinvariant : orderSevenPointMap d ((8 : ℕ) • Q) =
      orderSevenPointMap d Q := by
    calc
      orderSevenPointMap d ((8 : ℕ) • Q) =
          orderSevenPointMap d (Q + (7 : ℕ) • Q) := by
            congr 2
            abel
      _ = orderSevenPointMap d (Q + n • orderSevenOrigin d) := by
        rw [h7Q]
      _ = orderSevenPointMap d Q :=
        orderSevenPointMap_add_nsmul_origin_of_order_fortyNine hQ n
  have h8image : (8 : ℕ) • orderSevenPointMap d Q =
      orderSevenPointMap d Q := hmap8.symm.trans hinvariant
  have h7image : (7 : ℕ) • orderSevenPointMap d Q = 0 := by
    calc
      (7 : ℕ) • orderSevenPointMap d Q =
          (8 : ℕ) • orderSevenPointMap d Q -
            orderSevenPointMap d Q := by abel
      _ = 0 := by rw [h8image]; simp
  rw [hkernel]
  exact h7image.symm

/-- Under the single zero-fiber hypothesis at `7 • Q`, the Vélu image of
an exact-order-`49` point has exact order seven. -/
theorem addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    addOrderOf (orderSevenPointMap d Q) = 7 := by
  exact addOrderOf_orderSevenPointMap_of_order_fortyNine hQ hkernel
    (orderSevenPointMap_seven_nsmul_of_order_fortyNine hQ hkernel)

/-- The order-`49` image supplies a residual level-seven Hauptmodul from
the zero-fiber hypothesis alone. -/
theorem exists_orderSevenHauptmodul_of_order_fortyNine_image_of_kernel
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : orderSevenPointMap d ((7 : ℕ) • Q) = 0) :
    ∃ B : ℚ, B ≠ 0 ∧
      orderSevenJNumerator B * (orderSevenQuotient d).Δ =
        (orderSevenQuotient d).c₄ ^ 3 * B ^ 7 := by
  exact exists_orderSevenHauptmodul_of_order_fortyNine_image hQ hkernel
    (orderSevenPointMap_seven_nsmul_of_order_fortyNine hQ hkernel)

/-- The explicit residual Hauptmodul satisfies its quotient identity from
the zero-fiber hypothesis alone. -/
theorem orderSevenResidualHauptmodul_spec_of_order_fortyNine_of_kernel
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0) :
    orderSevenResidualHauptmodul d x y ≠ 0 ∧
      orderSevenJNumerator (orderSevenResidualHauptmodul d x y) *
          (orderSevenQuotient d).Δ =
        (orderSevenQuotient d).c₄ ^ 3 *
          orderSevenResidualHauptmodul d x y ^ 7 := by
  exact orderSevenResidualHauptmodul_spec_of_order_fortyNine
    hP hQ hkernel
      (orderSevenPointMap_seven_nsmul_of_order_fortyNine hQ hkernel)

/-- A nonbacktracking residual Hauptmodul lies on the level-`49`
correspondence from the zero-fiber hypothesis alone. -/
theorem orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_kernel
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hoff : orderSevenFrickeParameter d ≠
      orderSevenResidualHauptmodul d x y) :
    orderSevenG7F (orderSevenFrickeParameter d)
        (orderSevenResidualHauptmodul d x y) = 0 := by
  exact orderSevenG7F_residual_eq_zero_of_order_fortyNine
    hP hQ hkernel
      (orderSevenPointMap_seven_nsmul_of_order_fortyNine hQ hkernel) hoff

end MazurTorsion.Kubert
