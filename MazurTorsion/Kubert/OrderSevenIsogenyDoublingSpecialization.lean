/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogeny
import MazurTorsion.Kubert.OrderSevenIsogenyDoublingDerivative

/-!
# Order-seven specialization of the doubling derivative certificates

This file supplies the seven coefficients and the two small polynomial
identities needed to invoke `OrderSevenDoublingDerivative.vertical_at_point`.
The large abscissa identity remains in its independent interpolation module.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingSpecialization

open OrderSevenDoublingDerivative

def a₆ (d : ℚ) : ℚ := -2 * d * (d - 1) * (d + 1)

def a₅ (d : ℚ) : ℚ :=
  d * (d - 1) *
    (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1)

def a₄ (d : ℚ) : ℚ :=
  -d ^ 3 * (d - 1) ^ 2 *
    (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1)

def a₃ (d : ℚ) : ℚ :=
  d ^ 4 * (d - 1) ^ 3 *
    (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1)

def a₂ (d : ℚ) : ℚ :=
  -d ^ 6 * (d - 1) ^ 4 * (d + 1) * (3 * d ^ 2 - 5 * d - 3)

def a₁ (d : ℚ) : ℚ :=
  d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3)

def a₀ (d : ℚ) : ℚ := d ^ 10 * (d - 1) ^ 6

/-- The polynomial whose evaluation is the cleared Vélu differential
numerator. -/
noncomputable def differentialPolynomial (d : ℚ) : ℚ[X] :=
  X ^ 9 - C (3 * d * (d - 1) * (d + 1)) * X ^ 8 -
    C (d * (d - 1) *
      (d ^ 5 - 2 * d ^ 4 - 12 * d ^ 3 + 14 * d ^ 2 - 3 * d + 1)) * X ^ 7 -
    C (d ^ 2 * (d - 1) ^ 2 *
      (d ^ 6 - 9 * d ^ 5 + 25 * d ^ 4 - 22 * d ^ 3 +
        16 * d ^ 2 - 4 * d + 1)) * X ^ 6 +
    C (3 * d ^ 4 * (d - 1) ^ 3 *
      (d ^ 4 - 7 * d ^ 3 + 13 * d ^ 2 + 2)) * X ^ 5 +
    C (d ^ 5 * (d - 1) ^ 4 *
      (d ^ 6 - 10 * d ^ 5 + 35 * d ^ 4 - 36 * d ^ 3 -
        21 * d ^ 2 - 18 * d - 1)) * X ^ 4 +
    C (d ^ 7 * (d - 1) ^ 5 *
      (d ^ 5 - 5 * d ^ 4 - 3 * d ^ 3 + 27 * d ^ 2 + 30 * d + 5)) * X ^ 3 +
    C (3 * d ^ 9 * (d - 1) ^ 6 *
      (d ^ 3 - 2 * d ^ 2 - 8 * d - 3)) * X ^ 2 -
    C (d ^ 11 * (d - 1) ^ 7 * (d ^ 2 - 7 * d - 7)) * X -
    C (2 * d ^ 13 * (d - 1) ^ 8)

@[simp] theorem differentialPolynomial_eval (d x : ℚ) :
    (differentialPolynomial d).eval x =
      orderSevenVeluDifferentialNumerator d x := by
  simp [differentialPolynomial,
    orderSevenVeluDifferentialNumerator]

/-- The generic `F'K - 2FK'` polynomial specializes to the explicit
order-seven differential numerator. -/
theorem baseVeluDifferential_eq (d : ℚ) :
    baseVeluDifferential (a₆ d) (a₅ d) (a₄ d) (a₃ d)
        (a₂ d) (a₁ d) (a₀ d) (orderSevenB d) (orderSevenC d) =
      differentialPolynomial d := by
  apply Polynomial.funext
  intro x
  simp [baseVeluDifferential, veluDifferentialPolynomial,
    veluXPolynomial, kernelPolynomial, a₆, a₅, a₄, a₃, a₂, a₁, a₀,
    differentialPolynomial, orderSevenB, orderSevenC]
  ring

/-- The cubic kernel evaluated at the source doubling forms factors as
`K * N`. -/
theorem kernel_polynomial_identity (d : ℚ) :
    composedKernel (orderSevenB d) (orderSevenC d) (orderSevenFamily d) =
      baseKernel (orderSevenB d) (orderSevenC d) *
        baseVeluDifferential (a₆ d) (a₅ d) (a₄ d) (a₃ d)
          (a₂ d) (a₁ d) (a₀ d) (orderSevenB d) (orderSevenC d) := by
  rw [baseVeluDifferential_eq]
  apply Polynomial.funext
  intro x
  simp [composedKernel, sourceDoubleX, sourceCompletedCubic,
    doubleXPolynomial, completedCubicPolynomial, baseKernel,
    kernelPolynomial, differentialPolynomial, orderSevenFamily,
    orderSevenB, orderSevenC, tateNormalCurve, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- The completed-square cubic of the quotient image is `H * N²`. -/
theorem landing_polynomial_identity (d : ℚ) :
    targetCompletedCubic (orderSevenQuotient d)
        (a₆ d) (a₅ d) (a₄ d) (a₃ d) (a₂ d) (a₁ d) (a₀ d)
        (orderSevenB d) (orderSevenC d) =
      sourceCompletedCubic (orderSevenFamily d) *
        baseVeluDifferential (a₆ d) (a₅ d) (a₄ d) (a₃ d)
          (a₂ d) (a₁ d) (a₀ d) (orderSevenB d) (orderSevenC d) ^ 2 := by
  rw [baseVeluDifferential_eq]
  apply Polynomial.funext
  intro x
  simp [targetCompletedCubic, sourceCompletedCubic,
    completedCubicPolynomial, baseVeluX, veluXPolynomial, baseKernel,
    kernelPolynomial, differentialPolynomial, a₆, a₅, a₄, a₃, a₂, a₁, a₀,
    orderSevenFamily, orderSevenQuotient, orderSevenB, orderSevenC,
    tateNormalCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

end MazurTorsion.Kubert.OrderSevenDoublingSpecialization
