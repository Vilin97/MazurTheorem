/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.Rat.Lemmas

/-!
# Shared factor data for the order-25 unit-relation certificates

This module gives stable names to the factorized Sutherland-chart functions
used by the separately checked order-25 coefficient certificates.  Keeping
these definitions public prevents those certificates from exposing
module-private constants in their theorem statements.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveUnitRelationFactorData

/-- The factor `r - s`. -/
def A (r s : ℚ) : ℚ :=
  r - s

/-- The factor `s - 1`. -/
def B (_r s : ℚ) : ℚ :=
  s - 1

/-- The first quadratic factor in the raw orbit coordinates. -/
def C (r s : ℚ) : ℚ :=
  r * s - 2 * r + 1

/-- The factor occurring in the denominator of the ninth raw abscissa. -/
def K (r s : ℚ) : ℚ :=
  r - s ^ 2 + s - 1

/-- A common cubic factor in the later raw abscissas. -/
def D (r s : ℚ) : ℚ :=
  r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s

/-- A common factor in the eleventh and twelfth raw abscissas. -/
def E (r s : ℚ) : ℚ :=
  r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1

/-- The remaining numerator factor in the ninth and eleventh raw abscissas. -/
def G (r s : ℚ) : ℚ :=
  r * s ^ 2 - 3 * r * s + r + s ^ 2

/-- The remaining numerator factor in the twelfth raw abscissa. -/
def L (r s : ℚ) : ℚ :=
  r ^ 3
  - r ^ 2 * s ^ 4
  + 5 * r ^ 2 * s ^ 3
  - 9 * r ^ 2 * s ^ 2
  + 4 * r ^ 2 * s
  - 2 * r ^ 2
  - r * s ^ 3
  + 6 * r * s ^ 2
  - 3 * r * s
  + r
  - s ^ 3

/-- A numerator factor of the first factorized orbit unit. -/
def J (r s : ℚ) : ℚ :=
  r ^ 3 * s ^ 2
  - 4 * r ^ 3 * s
  + 2 * r ^ 3
  + 3 * r ^ 2 * s ^ 2
  + 2 * r ^ 2 * s
  - 2 * r ^ 2
  - r * s ^ 5
  + 4 * r * s ^ 4
  - 10 * r * s ^ 3
  + 6 * r * s ^ 2
  - 3 * r * s
  + r
  + s ^ 4

/-- A numerator factor of the fourth factorized orbit unit. -/
def T (r s : ℚ) : ℚ :=
  r ^ 2 * s ^ 3
  - 5 * r ^ 2 * s ^ 2
  + 6 * r ^ 2 * s
  - r ^ 2
  + r * s ^ 4
  - 3 * r * s ^ 3
  + 6 * r * s ^ 2
  - 7 * r * s
  + r
  + s

/-- A numerator factor shared by the second and ninth factorized orbit units. -/
def M (r s : ℚ) : ℚ :=
  r ^ 4 * s ^ 3
  - 6 * r ^ 4 * s ^ 2
  + 9 * r ^ 4 * s
  - r ^ 4
  + r ^ 3 * s ^ 5
  - 7 * r ^ 3 * s ^ 4
  + 20 * r ^ 3 * s ^ 3
  - 19 * r ^ 3 * s ^ 2
  - 8 * r ^ 3 * s
  + r ^ 3
  + r ^ 2 * s ^ 4
  - 11 * r ^ 2 * s ^ 3
  + 28 * r ^ 2 * s ^ 2
  + r * s ^ 4
  - 5 * r * s ^ 3
  - 8 * r * s ^ 2
  + s ^ 4
  + s ^ 3
  + s ^ 2

/-- The final numerator factor in the ninth factorized orbit unit. -/
def N (r s : ℚ) : ℚ :=
  r ^ 5
  - r ^ 4 * s ^ 6
  + 9 * r ^ 4 * s ^ 5
  - 31 * r ^ 4 * s ^ 4
  + 50 * r ^ 4 * s ^ 3
  - 39 * r ^ 4 * s ^ 2
  + 10 * r ^ 4 * s
  - 3 * r ^ 4
  - r ^ 3 * s ^ 6
  + 3 * r ^ 3 * s ^ 5
  + 12 * r ^ 3 * s ^ 4
  - 46 * r ^ 3 * s ^ 3
  + 54 * r ^ 3 * s ^ 2
  - 15 * r ^ 3 * s
  + 3 * r ^ 3
  - r ^ 2 * s ^ 6
  - 3 * r ^ 2 * s ^ 5
  + 9 * r ^ 2 * s ^ 4
  + r ^ 2 * s ^ 3
  - 21 * r ^ 2 * s ^ 2
  + 6 * r ^ 2 * s
  - r ^ 2
  + r * s ^ 7
  - 3 * r * s ^ 6
  + 6 * r * s ^ 5
  - 10 * r * s ^ 4
  + 11 * r * s ^ 3
  - s ^ 3

/-- The cross-difference factor used in the denominator of `y2`. -/
def P6 (r s : ℚ) : ℚ :=
  D r s ^ 2 * A r s * K r s -
    C r s ^ 2 * s * B r s * G r s * E r s

/-- The cross-difference factor used in the denominator of `y9`. -/
def P9 (r s : ℚ) : ℚ :=
  D r s ^ 3 * L r s - r * s * B r s ^ 3 * G r s * E r s ^ 3

/-- The first factorized Lécacheux orbit unit on the raw chart. -/
def y1 (r s : ℚ) : ℚ :=
  C r s * L r s * J r s / (r * B r s ^ 2 * K r s ^ 2 * E r s ^ 2)

/-- The second factorized Lécacheux orbit unit on the raw chart. -/
def y2 (r s : ℚ) : ℚ :=
  -(r * B r s ^ 3 * C r s * K r s * M r s) / (A r s ^ 2 * P6 r s)

/-- The fourth factorized Lécacheux orbit unit on the raw chart. -/
def y4 (r s : ℚ) : ℚ :=
  -(r * A r s * B r s * K r s ^ 2 * E r s * T r s) /
    (C r s * D r s ^ 2 * J r s)

/-- The eighth factorized Lécacheux orbit unit on the raw chart. -/
def y8 (r s : ℚ) : ℚ :=
  -(A r s * B r s * E r s) / L r s

/-- The ninth factorized Lécacheux orbit unit on the raw chart. -/
def y9 (r s : ℚ) : ℚ :=
  -(K r s * D r s * M r s * N r s) / (s * A r s * C r s ^ 2 * P9 r s)

private def fC0 (s : ℚ) : ℚ :=
  s ^ 10

private def fC1 (s : ℚ) : ℚ :=
  6 * s ^ 10
  - 28 * s ^ 9
  + 21 * s ^ 8
  - 15 * s ^ 7
  + 10 * s ^ 6
  - 6 * s ^ 5
  + 3 * s ^ 4
  - s ^ 3

private def fC2 (s : ℚ) : ℚ :=
  s ^ 15
  - 6 * s ^ 14
  + 21 * s ^ 13
  - 56 * s ^ 12
  + 126 * s ^ 11
  - 231 * s ^ 10
  + 266 * s ^ 9
  - 126 * s ^ 8
  + 96 * s ^ 7
  - 91 * s ^ 6
  + 75 * s ^ 5
  - 45 * s ^ 4
  + 15 * s ^ 3

private def fC3 (s : ℚ) : ℚ :=
  s ^ 15
  - 9 * s ^ 14
  + 25 * s ^ 13
  - 35 * s ^ 12
  + 45 * s ^ 11
  - 181 * s ^ 10
  + 569 * s ^ 9
  - 705 * s ^ 8
  + 5 * s ^ 7
  + 470 * s ^ 6
  - 540 * s ^ 5
  + 340 * s ^ 4
  - 105 * s ^ 3

private def fC4 (s : ℚ) : ℚ :=
  s ^ 15
  - 12 * s ^ 14
  + 48 * s ^ 13
  - 49 * s ^ 12
  - 165 * s ^ 11
  + 609 * s ^ 10
  - 433 * s ^ 9
  - 1623 * s ^ 8
  + 4299 * s ^ 7
  - 4615 * s ^ 6
  + 3435 * s ^ 5
  - 1740 * s ^ 4
  + 455 * s ^ 3

private def fC5 (s : ℚ) : ℚ :=
  s ^ 15
  - 15 * s ^ 14
  + 90 * s ^ 13
  - 245 * s ^ 12
  + 90 * s ^ 11
  + 1587 * s ^ 10
  - 6145 * s ^ 9
  + 12270 * s ^ 8
  - 15060 * s ^ 7
  + 12520 * s ^ 6
  - 8214 * s ^ 5
  + 3660 * s ^ 4
  - 685 * s ^ 3
  - 120 * s ^ 2
  + 15 * s
  - 1

private def fC6 (s : ℚ) : ℚ :=
  s ^ 15
  - 18 * s ^ 14
  + 151 * s ^ 13
  - 770 * s ^ 12
  + 2655 * s ^ 11
  - 6558 * s ^ 10
  + 11834 * s ^ 9
  - 15408 * s ^ 8
  + 14630 * s ^ 7
  - 11195 * s ^ 6
  + 7227 * s ^ 5
  - 2441 * s ^ 4
  - 388 * s ^ 3
  + 555 * s ^ 2
  - 70 * s
  + 5

private def fC7 (s : ℚ) : ℚ :=
  -21 * s ^ 10
  + 161 * s ^ 9
  - 351 * s ^ 8
  - 144 * s ^ 7
  + 1289 * s ^ 6
  - 789 * s ^ 5
  - 1551 * s ^ 4
  + 2166 * s ^ 3
  - 996 * s ^ 2
  + 126 * s
  - 10

private def fC8 (s : ℚ) : ℚ :=
  -6 * s ^ 10
  + 74 * s ^ 9
  - 345 * s ^ 8
  + 690 * s ^ 7
  - 185 * s ^ 6
  - 1659 * s ^ 5
  + 3051 * s ^ 4
  - 2320 * s ^ 3
  + 840 * s ^ 2
  - 105 * s
  + 10

private def fC9 (s : ℚ) : ℚ :=
  -s ^ 10
  + 17 * s ^ 9
  - 123 * s ^ 8
  + 494 * s ^ 7
  - 1205 * s ^ 6
  + 1836 * s ^ 5
  - 1732 * s ^ 4
  + 968 * s ^ 3
  - 294 * s ^ 2
  + 35 * s
  - 5

private def fC10 (_s : ℚ) : ℚ :=
  1

/-- Sutherland's raw order-25 affine equation in coefficient form. -/
def F (r s : ℚ) : ℚ :=
  fC10 s * r ^ 10
    + fC9 s * r ^ 9
    + fC8 s * r ^ 8
    + fC7 s * r ^ 7
    + fC6 s * r ^ 6
    + fC5 s * r ^ 5
    + fC4 s * r ^ 4
    + fC3 s * r ^ 3
    + fC2 s * r ^ 2
    + fC1 s * r
    + fC0 s

end MazurTorsion.Kubert.OrderTwentyFiveUnitRelationFactorData
