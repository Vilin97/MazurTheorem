/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData
import Mathlib.Tactic.ComputeDegree

/-!
# Polynomial data for the order-seven doubling certificate

This file contains the two degree-`28` polynomials and their degree bounds.
The pointwise ring certificates are split into serially imported blocks so a
cold build does not place the entire normalization proof in one Lean process.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate

noncomputable def sourceCompletedCubicPolynomial (d : ℚ) : ℚ[X] :=
  C 4 * X ^ 3 + C (orderSevenFamily d).b₂ * X ^ 2 +
    C (2 * (orderSevenFamily d).b₄) * X + C (orderSevenFamily d).b₆

noncomputable def sourceDoubleXPolynomial (d : ℚ) : ℚ[X] :=
  X ^ 4 - C (orderSevenFamily d).b₄ * X ^ 2 -
    C (2 * (orderSevenFamily d).b₆) * X - C (orderSevenFamily d).b₈

/-- Compatibility alias for the shared source kernel polynomial. -/
noncomputable abbrev kernelPolynomial :=
  OrderSevenIsogenyPolynomialData.kernelPolynomial

/-- Compatibility alias for the shared cleared Vélu abscissa polynomial. -/
noncomputable abbrev veluXPolynomial :=
  OrderSevenIsogenyPolynomialData.veluXPolynomial

noncomputable def veluXHomogeneousPolynomial
    (d : ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u ^ 7 - C (2 * d * (d - 1) * (d + 1)) * u ^ 6 * v +
    C (d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1)) *
        u ^ 5 * v ^ 2 -
    C (d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1)) *
        u ^ 4 * v ^ 3 +
    C (d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1)) *
        u ^ 3 * v ^ 4 -
    C (d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3)) * u ^ 2 * v ^ 5 +
    C (d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3)) * u * v ^ 6 +
    C (d ^ 10 * (d - 1) ^ 6) * v ^ 7

noncomputable def doubleXHomogeneousPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) : ℚ[X] :=
  u ^ 4 - C W.b₄ * u ^ 2 * v ^ 2 - C (2 * W.b₆) * u * v ^ 3 -
    C W.b₈ * v ^ 4

namespace Internal

lemma left_degree (d : ℚ) :
    (veluXHomogeneousPolynomial d (sourceDoubleXPolynomial d)
      (sourceCompletedCubicPolynomial d)).natDegree ≤ 28 := by
  unfold veluXHomogeneousPolynomial sourceDoubleXPolynomial
    sourceCompletedCubicPolynomial
  compute_degree

lemma right_degree (d : ℚ) :
    (doubleXHomogeneousPolynomial (orderSevenQuotient d)
      (veluXPolynomial d) (kernelPolynomial d ^ 2)).natDegree ≤ 28 := by
  unfold doubleXHomogeneousPolynomial veluXPolynomial kernelPolynomial
    OrderSevenIsogenyPolynomialData.veluXPolynomial
    OrderSevenIsogenyPolynomialData.kernelPolynomial
  compute_degree

def EvalCertificate (d n : ℚ) : Prop :=
  (veluXHomogeneousPolynomial d (sourceDoubleXPolynomial d)
    (sourceCompletedCubicPolynomial d)).eval n =
  (doubleXHomogeneousPolynomial (orderSevenQuotient d)
    (veluXPolynomial d) (kernelPolynomial d ^ 2)).eval n

end Internal

end MazurTorsion.Kubert.OrderSevenDoublingCertificate
