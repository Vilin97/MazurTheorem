/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.DoublingCoordinates
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Polynomial derivative infrastructure for order-seven doubling

This file isolates the formal-derivative argument used to recover the
completed-ordinate certificate from three smaller polynomial identities:
the abscissa identity, the kernel identity, and the completed-square landing
identity.  The degree-seven numerator and cubic denominator are kept generic;
the order-seven specialization supplies only their seven coefficients.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingDerivative

/-- A monic degree-seven binary form, written with its seven lower
coefficients. -/
def veluXHomogeneous
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v : ℚ) : ℚ :=
  u ^ 7 + a₆ * u ^ 6 * v + a₅ * u ^ 5 * v ^ 2 +
    a₄ * u ^ 4 * v ^ 3 + a₃ * u ^ 3 * v ^ 4 +
    a₂ * u ^ 2 * v ^ 5 + a₁ * u * v ^ 6 + a₀ * v ^ 7

/-- Directional derivative of `veluXHomogeneous`. -/
def veluXHomogeneousDirectional
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v du dv : ℚ) : ℚ :=
  (7 * u ^ 6 + 6 * a₆ * u ^ 5 * v + 5 * a₅ * u ^ 4 * v ^ 2 +
      4 * a₄ * u ^ 3 * v ^ 3 + 3 * a₃ * u ^ 2 * v ^ 4 +
      2 * a₂ * u * v ^ 5 + a₁ * v ^ 6) * du +
    (a₆ * u ^ 6 + 2 * a₅ * u ^ 5 * v + 3 * a₄ * u ^ 4 * v ^ 2 +
      4 * a₃ * u ^ 3 * v ^ 3 + 5 * a₂ * u ^ 2 * v ^ 4 +
      6 * a₁ * u * v ^ 5 + 7 * a₀ * v ^ 6) * dv

/-- Homogenization of the cubic denominator `X (X - b) (X - c)`. -/
def kernelHomogeneous (b c u v : ℚ) : ℚ :=
  u * (u - b * v) * (u - c * v)

/-- Directional derivative of `kernelHomogeneous`. -/
def kernelHomogeneousDirectional (b c u v du dv : ℚ) : ℚ :=
  ((u - b * v) * (u - c * v) + u * (u - c * v) +
      u * (u - b * v)) * du +
    (-b * u * (u - c * v) - c * u * (u - b * v)) * dv

/-- Homogenization to degree nine of `F'K - 2FK'`, for the degree-seven
form `F` and cubic kernel `K`. -/
def veluDifferentialHomogeneous
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v : ℚ) : ℚ :=
  (7 * u ^ 6 + 6 * a₆ * u ^ 5 * v + 5 * a₅ * u ^ 4 * v ^ 2 +
      4 * a₄ * u ^ 3 * v ^ 3 + 3 * a₃ * u ^ 2 * v ^ 4 +
      2 * a₂ * u * v ^ 5 + a₁ * v ^ 6) *
      kernelHomogeneous b c u v -
    2 * veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
      ((u - b * v) * (u - c * v) + u * (u - c * v) +
        u * (u - b * v))

/-- Directional numerator identity for a rational function `F / K²`,
where `F` is monic of degree seven and `K = X (X-b) (X-c)`. -/
theorem veluXHomogeneous_directional
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v du dv : ℚ) :
    veluXHomogeneousDirectional a₆ a₅ a₄ a₃ a₂ a₁ a₀
          u v du dv * v * kernelHomogeneous b c u v -
        veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
          (dv * kernelHomogeneous b c u v +
            2 * v * kernelHomogeneousDirectional b c u v du dv) =
      veluDifferentialHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v *
        (du * v - u * dv) := by
  simp only [veluXHomogeneousDirectional, kernelHomogeneous,
    veluXHomogeneous, kernelHomogeneousDirectional,
    veluDifferentialHomogeneous]
  ring

/-! ## Polynomial versions and their chain rules -/

noncomputable def completedCubicPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) : ℚ[X] :=
  C 4 * u ^ 3 + C W.b₂ * u ^ 2 * v + C (2 * W.b₄) * u * v ^ 2 +
    C W.b₆ * v ^ 3

noncomputable def doubleXPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u ^ 4 - C W.b₄ * u ^ 2 * v ^ 2 - C (2 * W.b₆) * u * v ^ 3 -
    C W.b₈ * v ^ 4

noncomputable def doubleCompletedYPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) : ℚ[X] :=
  C 2 * u ^ 6 + C W.b₂ * u ^ 5 * v + C (5 * W.b₄) * u ^ 4 * v ^ 2 +
    C (10 * W.b₆) * u ^ 3 * v ^ 3 + C (10 * W.b₈) * u ^ 2 * v ^ 4 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * u * v ^ 5 +
    C (W.b₄ * W.b₈ - W.b₆ ^ 2) * v ^ 6

noncomputable def veluXPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u ^ 7 + C a₆ * u ^ 6 * v + C a₅ * u ^ 5 * v ^ 2 +
    C a₄ * u ^ 4 * v ^ 3 + C a₃ * u ^ 3 * v ^ 4 +
    C a₂ * u ^ 2 * v ^ 5 + C a₁ * u * v ^ 6 + C a₀ * v ^ 7

noncomputable def kernelPolynomial
    (b c : ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u * (u - C b * v) * (u - C c * v)

noncomputable def veluDifferentialPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (u v : ℚ[X]) : ℚ[X] :=
  (C 7 * u ^ 6 + C (6 * a₆) * u ^ 5 * v + C (5 * a₅) * u ^ 4 * v ^ 2 +
      C (4 * a₄) * u ^ 3 * v ^ 3 + C (3 * a₃) * u ^ 2 * v ^ 4 +
      C (2 * a₂) * u * v ^ 5 + C a₁ * v ^ 6) *
      kernelPolynomial b c u v -
    C 2 * veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
      ((u - C b * v) * (u - C c * v) +
        u * (u - C c * v) + u * (u - C b * v))

theorem eval_completedCubicPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (completedCubicPolynomial W u v).eval x =
      Doubling.completedCubicHomogeneous W (u.eval x) (v.eval x) := by
  simp [completedCubicPolynomial, Doubling.completedCubicHomogeneous]

theorem eval_derivative_completedCubicPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (derivative (completedCubicPolynomial W u v)).eval x =
      Doubling.completedCubicHomogeneousDirectional W
        (u.eval x) (v.eval x) ((derivative u).eval x)
          ((derivative v).eval x) := by
  simp [completedCubicPolynomial,
    Doubling.completedCubicHomogeneousDirectional, derivative_mul,
    derivative_pow]
  ring

theorem eval_doubleXPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (doubleXPolynomial W u v).eval x =
      Doubling.xNumeratorHomogeneous W (u.eval x) (v.eval x) := by
  simp [doubleXPolynomial, Doubling.xNumeratorHomogeneous]

theorem eval_derivative_doubleXPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (derivative (doubleXPolynomial W u v)).eval x =
      Doubling.xNumeratorHomogeneousDirectional W
        (u.eval x) (v.eval x) ((derivative u).eval x)
          ((derivative v).eval x) := by
  simp [doubleXPolynomial, Doubling.xNumeratorHomogeneousDirectional,
    derivative_sub, derivative_mul, derivative_pow]
  ring

theorem eval_doubleCompletedYPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (doubleCompletedYPolynomial W u v).eval x =
      Doubling.completedYNumeratorHomogeneous W (u.eval x) (v.eval x) := by
  simp [doubleCompletedYPolynomial,
    Doubling.completedYNumeratorHomogeneous]

theorem eval_veluXPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v).eval x =
      veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ (u.eval x) (v.eval x) := by
  simp [veluXPolynomial, veluXHomogeneous]

theorem eval_derivative_veluXPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (derivative (veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v)).eval x =
      veluXHomogeneousDirectional a₆ a₅ a₄ a₃ a₂ a₁ a₀
        (u.eval x) (v.eval x) ((derivative u).eval x)
          ((derivative v).eval x) := by
  simp [veluXPolynomial, veluXHomogeneousDirectional, derivative_mul,
    derivative_pow]
  ring

theorem eval_kernelPolynomial
    (b c : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (kernelPolynomial b c u v).eval x =
      kernelHomogeneous b c (u.eval x) (v.eval x) := by
  simp [kernelPolynomial, kernelHomogeneous]

theorem eval_derivative_kernelPolynomial
    (b c : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (derivative (kernelPolynomial b c u v)).eval x =
      kernelHomogeneousDirectional b c (u.eval x) (v.eval x)
        ((derivative u).eval x) ((derivative v).eval x) := by
  simp [kernelPolynomial, kernelHomogeneousDirectional, derivative_sub,
    derivative_mul]
  ring

theorem eval_veluDifferentialPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (u v : ℚ[X]) (x : ℚ) :
    (veluDifferentialPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v).eval x =
      veluDifferentialHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
        (u.eval x) (v.eval x) := by
  simp [veluDifferentialPolynomial, veluDifferentialHomogeneous,
    kernelPolynomial, kernelHomogeneous, veluXPolynomial,
    veluXHomogeneous]

/-! ## The common-denominator derivative argument -/

private theorem vertical_of_common_denominator_derivative
    {A Ad B Bd H Hd Kh Khd Q Qd Ht Htd Nh R Rt K N : ℚ}
    (hA : A = B) (hAd : Ad = Bd)
    (hden : H * Kh ^ 2 = Q * Ht)
    (hdendot : Hd * Kh ^ 2 + 2 * H * Kh * Khd = Qd * Ht + Q * Htd)
    (hleft : Ad * H * Kh - A * (Hd * Kh + 2 * H * Khd) = 2 * Nh * R)
    (hright : Bd * Q * Ht - B * (Qd * Ht + Q * Htd) = 2 * Rt * K * N)
    (hKh : Kh = K * N) (hK : K ≠ 0) (hN : N ≠ 0) :
    Nh * R = Rt := by
  have hcommon :
      Kh * (Ad * H * Kh - A * (Hd * Kh + 2 * H * Khd)) =
        Bd * Q * Ht - B * (Qd * Ht + Q * Htd) := by
    linear_combination
      Ad * hden + (Q * Ht) * hAd - A * hdendot -
        (Qd * Ht + Q * Htd) * hA
  rw [hleft, hright, hKh] at hcommon
  have hcancel : (2 * K * N) * (Nh * R) = (2 * K * N) * Rt := by
    linear_combination hcommon
  exact mul_left_cancel₀
    (mul_ne_zero (mul_ne_zero (by norm_num) hK) hN) hcancel

private theorem vertical_of_polynomial_certificates
    (A B H Kh K N Q Ht : ℚ[X]) (x Nh R Rt : ℚ)
    (hA : A = B) (hKh : Kh = K * N) (hQ : Q = K ^ 2)
    (hHt : Ht = H * N ^ 2)
    (hK : K.eval x ≠ 0) (hN : N.eval x ≠ 0)
    (hleft :
      (derivative A).eval x * H.eval x * Kh.eval x - A.eval x *
          ((derivative H).eval x * Kh.eval x +
            2 * H.eval x * (derivative Kh).eval x) =
        2 * Nh * R)
    (hright :
      (derivative B).eval x * Q.eval x * Ht.eval x - B.eval x *
          ((derivative Q).eval x * Ht.eval x +
            Q.eval x * (derivative Ht).eval x) =
        2 * Rt * K.eval x * N.eval x) :
    Nh * R = Rt := by
  have hdenPoly : H * Kh ^ 2 = Q * Ht := by
    rw [hKh, hQ, hHt]
    ring
  have hAeval : A.eval x = B.eval x := by rw [hA]
  have hAderiv : (derivative A).eval x = (derivative B).eval x := by rw [hA]
  have hden : H.eval x * Kh.eval x ^ 2 = Q.eval x * Ht.eval x := by
    simpa using congrArg (Polynomial.eval x) hdenPoly
  have hdendot :
      (derivative H).eval x * Kh.eval x ^ 2 +
          2 * H.eval x * Kh.eval x * (derivative Kh).eval x =
        (derivative Q).eval x * Ht.eval x +
          Q.eval x * (derivative Ht).eval x := by
    have hd := congrArg Polynomial.derivative hdenPoly
    have hde := congrArg (Polynomial.eval x) hd
    simp [derivative_mul, derivative_pow] at hde
    linear_combination hde
  have hKheval : Kh.eval x = K.eval x * N.eval x := by
    simpa using congrArg (Polynomial.eval x) hKh
  exact vertical_of_common_denominator_derivative
    hAeval hAderiv hden hdendot hleft hright hKheval hK hN

/-! ## End-to-end reusable vertical certificate -/

noncomputable def sourceCompletedCubic
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  completedCubicPolynomial W X 1

noncomputable def sourceDoubleX
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  doubleXPolynomial W X 1

noncomputable def sourceDoubleCompletedY
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  doubleCompletedYPolynomial W X 1

noncomputable def baseVeluX
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) : ℚ[X] :=
  veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ X 1

noncomputable def baseKernel (b c : ℚ) : ℚ[X] :=
  kernelPolynomial b c X 1

noncomputable def baseVeluDifferential
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ) : ℚ[X] :=
  veluDifferentialPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c X 1

noncomputable def composedVeluX
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ)
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀
    (sourceDoubleX W) (sourceCompletedCubic W)

noncomputable def composedKernel
    (b c : ℚ) (W : WeierstrassCurve ℚ) : ℚ[X] :=
  kernelPolynomial b c (sourceDoubleX W) (sourceCompletedCubic W)

noncomputable def composedVeluDifferential
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (W : WeierstrassCurve ℚ) : ℚ[X] :=
  veluDifferentialPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
    (sourceDoubleX W) (sourceCompletedCubic W)

noncomputable def targetDoubleX
    (W' : WeierstrassCurve ℚ)
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ) : ℚ[X] :=
  doubleXPolynomial W'
    (baseVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀) (baseKernel b c ^ 2)

noncomputable def targetCompletedCubic
    (W' : WeierstrassCurve ℚ)
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ) : ℚ[X] :=
  completedCubicPolynomial W'
    (baseVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀) (baseKernel b c ^ 2)

noncomputable def targetDoubleCompletedY
    (W' : WeierstrassCurve ℚ)
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ) : ℚ[X] :=
  doubleCompletedYPolynomial W'
    (baseVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀) (baseKernel b c ^ 2)

/-- The vertical homogeneous certificate obtained by differentiating the
abscissa, kernel, and landing polynomial certificates. -/
theorem vertical_at_point
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (W W' : WeierstrassCurve ℚ) (x : ℚ)
    (hX : composedVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀ W =
      targetDoubleX W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c)
    (hkernel : composedKernel b c W =
      baseKernel b c * baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c)
    (hlanding :
      targetCompletedCubic W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c =
        sourceCompletedCubic W *
          baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c ^ 2)
    (hK : (baseKernel b c).eval x ≠ 0)
    (hN : (baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c).eval x ≠ 0) :
    (composedVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c W).eval x *
        (sourceDoubleCompletedY W).eval x =
      (targetDoubleCompletedY W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c).eval x := by
  let p := sourceDoubleX W
  let h := sourceCompletedCubic W
  let f := baseVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀
  let k := baseKernel b c
  let n := baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
  let q := k ^ 2
  let A := composedVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀ W
  let Kh := composedKernel b c W
  let Nh := composedVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c W
  let B := targetDoubleX W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
  let Ht := targetCompletedCubic W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
  let Rs := sourceDoubleCompletedY W
  let Rt := targetDoubleCompletedY W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
  have hsource :
      (derivative p).eval x * h.eval x - p.eval x * (derivative h).eval x =
        2 * Rs.eval x := by
    have hs := Doubling.xNumeratorHomogeneous_directional W x 1 1 0
    simp only [p, h, Rs, sourceDoubleX, sourceCompletedCubic,
      sourceDoubleCompletedY, eval_derivative_doubleXPolynomial,
      eval_doubleXPolynomial, eval_derivative_completedCubicPolynomial,
      eval_completedCubicPolynomial, eval_doubleCompletedYPolynomial,
      eval_X, eval_one, derivative_X, derivative_one]
    simpa using hs
  have hleft :
      (derivative A).eval x * h.eval x * Kh.eval x - A.eval x *
          ((derivative h).eval x * Kh.eval x +
            2 * h.eval x * (derivative Kh).eval x) =
        2 * Nh.eval x * Rs.eval x := by
    have hv := veluXHomogeneous_directional a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
      (p.eval x) (h.eval x) ((derivative p).eval x) ((derivative h).eval x)
    have hv' :
        (derivative A).eval x * h.eval x * Kh.eval x - A.eval x *
            ((derivative h).eval x * Kh.eval x +
              2 * h.eval x * (derivative Kh).eval x) =
          Nh.eval x *
            ((derivative p).eval x * h.eval x -
              p.eval x * (derivative h).eval x) := by
      simpa only [A, Kh, Nh, p, h, composedVeluX, composedKernel,
        composedVeluDifferential, eval_derivative_veluXPolynomial,
        eval_veluXPolynomial, eval_derivative_kernelPolynomial,
        eval_kernelPolynomial, eval_veluDifferentialPolynomial] using hv
    rw [hv', hsource]
    ring
  have hbase :
      (derivative f).eval x * k.eval x -
          2 * f.eval x * (derivative k).eval x = n.eval x := by
    have hv := veluXHomogeneous_directional a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c x 1 1 0
    simp only [f, k, n, baseVeluX, baseKernel, baseVeluDifferential,
      eval_derivative_veluXPolynomial, eval_veluXPolynomial,
      eval_derivative_kernelPolynomial, eval_kernelPolynomial,
      eval_veluDifferentialPolynomial, eval_X, eval_one, derivative_X,
      derivative_one, eval_zero, mul_one, mul_zero, zero_mul,
      sub_zero] at hv ⊢
    linear_combination hv
  have hcross :
      (derivative f).eval x * q.eval x - f.eval x * (derivative q).eval x =
        k.eval x * n.eval x := by
    simp [q, derivative_pow]
    linear_combination k.eval x * hbase
  have hright :
      (derivative B).eval x * q.eval x * Ht.eval x - B.eval x *
          ((derivative q).eval x * Ht.eval x +
            q.eval x * (derivative Ht).eval x) =
        2 * Rt.eval x * k.eval x * n.eval x := by
    have ht := Doubling.xNumeratorHomogeneous_directional W'
      (f.eval x) (q.eval x) ((derivative f).eval x) ((derivative q).eval x)
    have ht' :
        (derivative B).eval x * q.eval x * Ht.eval x - B.eval x *
            ((derivative q).eval x * Ht.eval x +
              q.eval x * (derivative Ht).eval x) =
          2 * Rt.eval x *
            ((derivative f).eval x * q.eval x -
              f.eval x * (derivative q).eval x) := by
      simpa only [B, Ht, Rt, f, q, targetDoubleX,
        targetCompletedCubic, targetDoubleCompletedY,
        eval_derivative_doubleXPolynomial, eval_doubleXPolynomial,
        eval_derivative_completedCubicPolynomial,
        eval_completedCubicPolynomial,
        eval_doubleCompletedYPolynomial] using ht
    rw [ht', hcross]
    ring
  apply vertical_of_polynomial_certificates A B h Kh k n q Ht x
    (Nh.eval x) (Rs.eval x) (Rt.eval x)
  · simpa only [A, B] using hX
  · simpa only [Kh, k, n] using hkernel
  · rfl
  · simpa only [Ht, h, n] using hlanding
  · simpa only [k] using hK
  · simpa only [n] using hN
  · exact hleft
  · exact hright

end MazurTorsion.Kubert.OrderSevenDoublingDerivative
