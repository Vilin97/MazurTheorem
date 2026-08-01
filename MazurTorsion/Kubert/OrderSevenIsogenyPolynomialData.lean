/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogeny

/-!
# Shared polynomial data for the explicit order-seven isogeny

This file packages the source kernel cubic and the cleared Vélu abscissa as
univariate polynomials.  They are shared by the doubling and dual-kernel
certificates.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData

/-- The polynomial form of the three source kernel abscissae. -/
noncomputable def kernelPolynomial (d : ℚ) : ℚ[X] :=
  X * (X - C (orderSevenB d)) * (X - C (orderSevenC d))

/-- The polynomial form of the cleared explicit Vélu abscissa numerator. -/
noncomputable def veluXPolynomial (d : ℚ) : ℚ[X] :=
  X ^ 7 - C (2 * d * (d - 1) * (d + 1)) * X ^ 6 +
    C (d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1)) *
        X ^ 5 -
    C (d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1)) * X ^ 4 +
    C (d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1)) * X ^ 3 -
    C (d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3)) * X ^ 2 +
    C (d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3)) * X +
    C (d ^ 10 * (d - 1) ^ 6)

@[simp] theorem kernelPolynomial_eval (d x : ℚ) :
    (kernelPolynomial d).eval x = orderSevenKernelPolynomial d x := by
  simp [kernelPolynomial, orderSevenKernelPolynomial]

@[simp] theorem veluXPolynomial_eval (d x : ℚ) :
    (veluXPolynomial d).eval x = orderSevenVeluXNumerator d x := by
  simp [veluXPolynomial, orderSevenVeluXNumerator]

end MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData
