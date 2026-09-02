/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Exact raw-orbit certificate data for order twenty-five

These private-namespace coefficient blocks support the checked rational
function identities in `OrderTwentyFiveNormalizedModel`.  They were
discovered by exact polynomial division over `ℚ`; the downstream Lean
ring normalizer checks every identity.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawOrbitData

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient0 (s : ℚ) : ℚ :=
  s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient1 (s : ℚ) : ℚ :=
  6 * s ^ 10
    - 28 * s ^ 9
    + 21 * s ^ 8
    - 15 * s ^ 7
    + 10 * s ^ 6
    - 6 * s ^ 5
    + 3 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient2 (s : ℚ) : ℚ :=
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

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient3 (s : ℚ) : ℚ :=
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

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient4 (s : ℚ) : ℚ :=
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

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient5 (s : ℚ) : ℚ :=
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

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient6 (s : ℚ) : ℚ :=
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

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient7 (s : ℚ) : ℚ :=
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

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient8 (s : ℚ) : ℚ :=
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

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient9 (s : ℚ) : ℚ :=
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

/-- Coefficient of the indicated power of the raw chart variable. -/
def sutherlandPolynomialCoefficient10 (_s : ℚ) : ℚ :=
  1

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def sutherlandPolynomial (r s : ℚ) : ℚ :=
  sutherlandPolynomialCoefficient0 s +
    sutherlandPolynomialCoefficient1 s * r +
    sutherlandPolynomialCoefficient2 s * r ^ 2 +
    sutherlandPolynomialCoefficient3 s * r ^ 3 +
    sutherlandPolynomialCoefficient4 s * r ^ 4 +
    sutherlandPolynomialCoefficient5 s * r ^ 5 +
    sutherlandPolynomialCoefficient6 s * r ^ 6 +
    sutherlandPolynomialCoefficient7 s * r ^ 7 +
    sutherlandPolynomialCoefficient8 s * r ^ 8 +
    sutherlandPolynomialCoefficient9 s * r ^ 9 +
    sutherlandPolynomialCoefficient10 s * r ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneNumeratorCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneNumeratorCoefficient1 (s : ℚ) : ℚ :=
  -3 * s ^ 7
    + 16 * s ^ 6
    - 9 * s ^ 5
    + 4 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneNumeratorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 9
    - 7 * s ^ 8
    + 21 * s ^ 7
    - 13 * s ^ 6
    - 56 * s ^ 5
    + 60 * s ^ 4
    - 43 * s ^ 3
    + 21 * s ^ 2
    - 6 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneNumeratorCoefficient3 (s : ℚ) : ℚ :=
  s ^ 9
    - 14 * s ^ 8
    + 77 * s ^ 7
    - 230 * s ^ 6
    + 362 * s ^ 5
    - 280 * s ^ 4
    + 190 * s ^ 3
    - 96 * s ^ 2
    + 31 * s
    - 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneNumeratorCoefficient4 (s : ℚ) : ℚ :=
  s ^ 10
    - 11 * s ^ 9
    + 57 * s ^ 8
    - 174 * s ^ 7
    + 326 * s ^ 6
    - 360 * s ^ 5
    + 272 * s ^ 4
    - 261 * s ^ 3
    + 165 * s ^ 2
    - 65 * s
    + 15

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneNumeratorCoefficient5 (s : ℚ) : ℚ :=
  -3 * s ^ 7
    + 16 * s ^ 6
    - 14 * s ^ 5
    - 84 * s ^ 4
    + 211 * s ^ 3
    - 160 * s ^ 2
    + 75 * s
    - 20

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneNumeratorCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 7
    + 11 * s ^ 6
    - 49 * s ^ 5
    + 112 * s ^ 4
    - 133 * s ^ 3
    + 85 * s ^ 2
    - 46 * s
    + 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneNumeratorCoefficient7 (s : ℚ) : ℚ :=
  s ^ 3
    - 6 * s ^ 2
    + 10 * s
    - 4

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitOneNumerator (r s : ℚ) : ℚ :=
  rawUnitOneNumeratorCoefficient0 s +
    rawUnitOneNumeratorCoefficient1 s * r +
    rawUnitOneNumeratorCoefficient2 s * r ^ 2 +
    rawUnitOneNumeratorCoefficient3 s * r ^ 3 +
    rawUnitOneNumeratorCoefficient4 s * r ^ 4 +
    rawUnitOneNumeratorCoefficient5 s * r ^ 5 +
    rawUnitOneNumeratorCoefficient6 s * r ^ 6 +
    rawUnitOneNumeratorCoefficient7 s * r ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneDenominatorCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneDenominatorCoefficient1 (s : ℚ) : ℚ :=
  s ^ 10
    - 4 * s ^ 9
    + 10 * s ^ 8
    - 18 * s ^ 7
    + 25 * s ^ 6
    - 28 * s ^ 5
    + 25 * s ^ 4
    - 18 * s ^ 3
    + 10 * s ^ 2
    - 4 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneDenominatorCoefficient2 (s : ℚ) : ℚ :=
  -2 * s ^ 9
    + 12 * s ^ 7
    - 38 * s ^ 6
    + 70 * s ^ 5
    - 88 * s ^ 4
    + 84 * s ^ 3
    - 58 * s ^ 2
    + 28 * s
    - 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneDenominatorCoefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 9
    + 15 * s ^ 8
    - 36 * s ^ 7
    + 76 * s ^ 6
    - 132 * s ^ 5
    + 183 * s ^ 4
    - 204 * s ^ 3
    + 162 * s ^ 2
    - 90 * s
    + 28

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneDenominatorCoefficient4 (s : ℚ) : ℚ :=
  2 * s ^ 8
    - 4 * s ^ 7
    - 28 * s ^ 6
    + 100 * s ^ 5
    - 204 * s ^ 4
    + 284 * s ^ 3
    - 260 * s ^ 2
    + 164 * s
    - 54

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneDenominatorCoefficient5 (s : ℚ) : ℚ :=
  s ^ 8
    - 10 * s ^ 7
    + 37 * s ^ 6
    - 84 * s ^ 5
    + 171 * s ^ 4
    - 250 * s ^ 3
    + 251 * s ^ 2
    - 176 * s
    + 60

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneDenominatorCoefficient6 (s : ℚ) : ℚ :=
  -2 * s ^ 6
    + 18 * s ^ 5
    - 60 * s ^ 4
    + 104 * s ^ 3
    - 126 * s ^ 2
    + 102 * s
    - 36

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitOneDenominatorCoefficient7 (s : ℚ) : ℚ :=
  s ^ 4
    - 8 * s ^ 3
    + 22 * s ^ 2
    - 24 * s
    + 9

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitOneDenominator (r s : ℚ) : ℚ :=
  rawUnitOneDenominatorCoefficient0 s +
    rawUnitOneDenominatorCoefficient1 s * r +
    rawUnitOneDenominatorCoefficient2 s * r ^ 2 +
    rawUnitOneDenominatorCoefficient3 s * r ^ 3 +
    rawUnitOneDenominatorCoefficient4 s * r ^ 4 +
    rawUnitOneDenominatorCoefficient5 s * r ^ 5 +
    rawUnitOneDenominatorCoefficient6 s * r ^ 6 +
    rawUnitOneDenominatorCoefficient7 s * r ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoNumeratorCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoNumeratorCoefficient1 (s : ℚ) : ℚ :=
  s ^ 9
    - 3 * s ^ 8
    + 4 * s ^ 7
    - 4 * s ^ 6
    + 4 * s ^ 5
    - 4 * s ^ 4
    + 3 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoNumeratorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 10
    - 4 * s ^ 9
    + s ^ 8
    + 6 * s ^ 7
    + 4 * s ^ 6
    - 30 * s ^ 5
    + 47 * s ^ 4
    - 36 * s ^ 3
    + 11 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoNumeratorCoefficient3 (s : ℚ) : ℚ :=
  s ^ 10
    - 10 * s ^ 9
    + 21 * s ^ 8
    + 34 * s ^ 7
    - 190 * s ^ 6
    + 339 * s ^ 5
    - 350 * s ^ 4
    + 209 * s ^ 3
    - 54 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoNumeratorCoefficient4 (s : ℚ) : ℚ :=
  2 * s ^ 10
    - 28 * s ^ 9
    + 163 * s ^ 8
    - 500 * s ^ 7
    + 918 * s ^ 6
    - 1116 * s ^ 5
    + 918 * s ^ 4
    - 448 * s ^ 3
    + 80 * s ^ 2
    + 12 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoNumeratorCoefficient5 (s : ℚ) : ℚ :=
  s ^ 11
    - 13 * s ^ 10
    + 77 * s ^ 9
    - 266 * s ^ 8
    + 587 * s ^ 7
    - 887 * s ^ 6
    + 959 * s ^ 5
    - 687 * s ^ 4
    + 221 * s ^ 3
    + 53 * s ^ 2
    - 49 * s
    + 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoNumeratorCoefficient6 (s : ℚ) : ℚ :=
  -4 * s ^ 7
    + 22 * s ^ 6
    - 24 * s ^ 5
    - 67 * s ^ 4
    + 190 * s ^ 3
    - 174 * s ^ 2
    + 62 * s
    - 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoNumeratorCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 7
    + 11 * s ^ 6
    - 48 * s ^ 5
    + 107 * s ^ 4
    - 130 * s ^ 3
    + 84 * s ^ 2
    - 25 * s
    + 2

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitTwoNumerator (r s : ℚ) : ℚ :=
  rawUnitTwoNumeratorCoefficient0 s +
    rawUnitTwoNumeratorCoefficient1 s * r +
    rawUnitTwoNumeratorCoefficient2 s * r ^ 2 +
    rawUnitTwoNumeratorCoefficient3 s * r ^ 3 +
    rawUnitTwoNumeratorCoefficient4 s * r ^ 4 +
    rawUnitTwoNumeratorCoefficient5 s * r ^ 5 +
    rawUnitTwoNumeratorCoefficient6 s * r ^ 6 +
    rawUnitTwoNumeratorCoefficient7 s * r ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient0 (s : ℚ) : ℚ :=
  s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient1 (s : ℚ) : ℚ :=
  3 * s ^ 8
    - 17 * s ^ 7
    + 10 * s ^ 6
    - 6 * s ^ 5
    + 3 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 11
    - 6 * s ^ 10
    + 21 * s ^ 9
    - 50 * s ^ 8
    + 60 * s ^ 7
    + 5 * s ^ 5
    - 6 * s ^ 4
    + s ^ 3
    + 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 10
    + 9 * s ^ 9
    - 39 * s ^ 8
    + 121 * s ^ 7
    - 159 * s ^ 6
    + 6 * s ^ 5
    + 11 * s ^ 4
    + 9 * s ^ 3
    - 11 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 9
    + 12 * s ^ 8
    + 6 * s ^ 7
    - 152 * s ^ 6
    + 270 * s ^ 5
    - 54 * s ^ 4
    - 42 * s ^ 3
    + 24 * s ^ 2
    + 7 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 9
    + 15 * s ^ 8
    - 75 * s ^ 7
    + 126 * s ^ 6
    + 20 * s ^ 5
    - 249 * s ^ 4
    + 149 * s ^ 3
    - 20 * s ^ 2
    - 21 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient6 (s : ℚ) : ℚ :=
  2 * s ^ 8
    - 24 * s ^ 7
    + 108 * s ^ 6
    - 219 * s ^ 5
    + 182 * s ^ 4
    + 6 * s ^ 3
    - 64 * s ^ 2
    + 37 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 7
    + 11 * s ^ 6
    - 48 * s ^ 5
    + 105 * s ^ 4
    - 121 * s ^ 3
    + 69 * s ^ 2
    - 22 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoDenominatorCoefficient8 (_s : ℚ) : ℚ :=
  1

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitTwoDenominator (r s : ℚ) : ℚ :=
  rawUnitTwoDenominatorCoefficient0 s +
    rawUnitTwoDenominatorCoefficient1 s * r +
    rawUnitTwoDenominatorCoefficient2 s * r ^ 2 +
    rawUnitTwoDenominatorCoefficient3 s * r ^ 3 +
    rawUnitTwoDenominatorCoefficient4 s * r ^ 4 +
    rawUnitTwoDenominatorCoefficient5 s * r ^ 5 +
    rawUnitTwoDenominatorCoefficient6 s * r ^ 6 +
    rawUnitTwoDenominatorCoefficient7 s * r ^ 7 +
    rawUnitTwoDenominatorCoefficient8 s * r ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 9
    + 3 * s ^ 8
    - 6 * s ^ 7
    + 8 * s ^ 6
    - 8 * s ^ 5
    + 6 * s ^ 4
    - 3 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 12
    + 6 * s ^ 11
    - 21 * s ^ 10
    + 51 * s ^ 9
    - 88 * s ^ 8
    + 122 * s ^ 7
    - 133 * s ^ 6
    + 118 * s ^ 5
    - 81 * s ^ 4
    + 39 * s ^ 3
    - 12 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient3 (s : ℚ) : ℚ :=
  s ^ 11
    + s ^ 10
    - 14 * s ^ 9
    + 52 * s ^ 8
    - 131 * s ^ 7
    + 207 * s ^ 6
    - 242 * s ^ 5
    + 190 * s ^ 4
    - 93 * s ^ 3
    + 21 * s ^ 2
    + 9 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient4 (s : ℚ) : ℚ :=
  s ^ 11
    - 8 * s ^ 10
    + 26 * s ^ 9
    - 79 * s ^ 8
    + 175 * s ^ 7
    - 260 * s ^ 6
    + 292 * s ^ 5
    - 191 * s ^ 4
    + 49 * s ^ 3
    + 40 * s ^ 2
    - 51 * s
    + 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient5 (s : ℚ) : ℚ :=
  -5 * s ^ 9
    + 31 * s ^ 8
    - 63 * s ^ 7
    + 77 * s ^ 6
    - 45 * s ^ 5
    - 85 * s ^ 4
    + 184 * s ^ 3
    - 202 * s ^ 2
    + 123 * s
    - 15

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 9
    + 11 * s ^ 8
    - 43 * s ^ 7
    + 93 * s ^ 6
    - 181 * s ^ 5
    + 296 * s ^ 4
    - 336 * s ^ 3
    + 293 * s ^ 2
    - 151 * s
    + 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 7
    - 20 * s ^ 6
    + 75 * s ^ 5
    - 145 * s ^ 4
    + 189 * s ^ 3
    - 181 * s ^ 2
    + 92 * s
    - 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourNumeratorCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 5
    + 9 * s ^ 4
    - 29 * s ^ 3
    + 40 * s ^ 2
    - 22 * s
    + 3

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitFourNumerator (r s : ℚ) : ℚ :=
  rawUnitFourNumeratorCoefficient0 s +
    rawUnitFourNumeratorCoefficient1 s * r +
    rawUnitFourNumeratorCoefficient2 s * r ^ 2 +
    rawUnitFourNumeratorCoefficient3 s * r ^ 3 +
    rawUnitFourNumeratorCoefficient4 s * r ^ 4 +
    rawUnitFourNumeratorCoefficient5 s * r ^ 5 +
    rawUnitFourNumeratorCoefficient6 s * r ^ 6 +
    rawUnitFourNumeratorCoefficient7 s * r ^ 7 +
    rawUnitFourNumeratorCoefficient8 s * r ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient0 (s : ℚ) : ℚ :=
  s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient1 (s : ℚ) : ℚ :=
  -2 * s ^ 8
    + 6 * s ^ 7
    - 6 * s ^ 6
    - 10 * s ^ 5
    + 6 * s ^ 4
    - 3 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 10
    - 6 * s ^ 9
    + 12 * s ^ 8
    + 14 * s ^ 7
    - 90 * s ^ 6
    + 150 * s ^ 5
    - 80 * s ^ 4
    + 39 * s ^ 3
    - 12 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient3 (s : ℚ) : ℚ :=
  4 * s ^ 10
    - 40 * s ^ 9
    + 180 * s ^ 8
    - 467 * s ^ 7
    + 723 * s ^ 6
    - 660 * s ^ 5
    + 320 * s ^ 4
    - 166 * s ^ 3
    + 48 * s ^ 2
    + 2 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 12
    + 12 * s ^ 11
    - 71 * s ^ 10
    + 260 * s ^ 9
    - 634 * s ^ 8
    + 1039 * s ^ 7
    - 1106 * s ^ 6
    + 736 * s ^ 5
    - 355 * s ^ 4
    + 274 * s ^ 3
    - 68 * s ^ 2
    - 16 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient5 (s : ℚ) : ℚ :=
  5 * s ^ 9
    - 39 * s ^ 8
    + 137 * s ^ 7
    - 247 * s ^ 6
    + 174 * s ^ 5
    + 120 * s ^ 4
    - 266 * s ^ 3
    + 18 * s ^ 2
    + 41 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient6 (s : ℚ) : ℚ :=
  s ^ 9
    - 12 * s ^ 8
    + 63 * s ^ 7
    - 197 * s ^ 6
    + 384 * s ^ 5
    - 442 * s ^ 4
    + 222 * s ^ 3
    + 60 * s ^ 2
    - 47 * s
    - 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient7 (s : ℚ) : ℚ :=
  -2 * s ^ 6
    + 18 * s ^ 5
    - 64 * s ^ 4
    + 119 * s ^ 3
    - 107 * s ^ 2
    + 22 * s
    + 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitFourDenominatorCoefficient8 (s : ℚ) : ℚ :=
  s ^ 3
    - 6 * s ^ 2
    + 10 * s
    - 4

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitFourDenominator (r s : ℚ) : ℚ :=
  rawUnitFourDenominatorCoefficient0 s +
    rawUnitFourDenominatorCoefficient1 s * r +
    rawUnitFourDenominatorCoefficient2 s * r ^ 2 +
    rawUnitFourDenominatorCoefficient3 s * r ^ 3 +
    rawUnitFourDenominatorCoefficient4 s * r ^ 4 +
    rawUnitFourDenominatorCoefficient5 s * r ^ 5 +
    rawUnitFourDenominatorCoefficient6 s * r ^ 6 +
    rawUnitFourDenominatorCoefficient7 s * r ^ 7 +
    rawUnitFourDenominatorCoefficient8 s * r ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightNumeratorCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 4
    + s ^ 3
    - s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightNumeratorCoefficient1 (s : ℚ) : ℚ :=
  2 * s ^ 3
    + s ^ 2
    - 2 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightNumeratorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 3
    - 5 * s ^ 2
    + s
    + 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightNumeratorCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 2
    + 4 * s
    - 3

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitEightNumerator (r s : ℚ) : ℚ :=
  rawUnitEightNumeratorCoefficient0 s +
    rawUnitEightNumeratorCoefficient1 s * r +
    rawUnitEightNumeratorCoefficient2 s * r ^ 2 +
    rawUnitEightNumeratorCoefficient3 s * r ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightDenominatorCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightDenominatorCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 3
    + 6 * s ^ 2
    - 3 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightDenominatorCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 4
    + 5 * s ^ 3
    - 9 * s ^ 2
    + 4 * s
    - 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightDenominatorCoefficient3 (_s : ℚ) : ℚ :=
  1

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitEightDenominator (r s : ℚ) : ℚ :=
  rawUnitEightDenominatorCoefficient0 s +
    rawUnitEightDenominatorCoefficient1 s * r +
    rawUnitEightDenominatorCoefficient2 s * r ^ 2 +
    rawUnitEightDenominatorCoefficient3 s * r ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 10
    - s ^ 8
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient1 (s : ℚ) : ℚ :=
  s ^ 14
    - 3 * s ^ 13
    + 8 * s ^ 12
    - 16 * s ^ 11
    + 22 * s ^ 10
    - 10 * s ^ 9
    + 25 * s ^ 8
    - 15 * s ^ 7
    + 24 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 16
    + 6 * s ^ 15
    - 19 * s ^ 14
    + 36 * s ^ 13
    - 66 * s ^ 12
    + 83 * s ^ 11
    - 74 * s ^ 10
    + 101 * s ^ 9
    - 278 * s ^ 8
    + 240 * s ^ 7
    - 208 * s ^ 6
    - 23 * s ^ 5
    + 6 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 16
    + 13 * s ^ 15
    - 51 * s ^ 14
    + 105 * s ^ 13
    - 104 * s ^ 12
    + 25 * s ^ 11
    + 417 * s ^ 10
    - 1398 * s ^ 9
    + 2236 * s ^ 8
    - 1634 * s ^ 7
    + 738 * s ^ 6
    + 397 * s ^ 5
    - 99 * s ^ 4
    + 16 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 16
    + 21 * s ^ 15
    - 153 * s ^ 14
    + 578 * s ^ 13
    - 1521 * s ^ 12
    + 3317 * s ^ 11
    - 6481 * s ^ 10
    + 9388 * s ^ 9
    - 8569 * s ^ 8
    + 3403 * s ^ 7
    + 1055 * s ^ 6
    - 3129 * s ^ 5
    + 716 * s ^ 4
    - 108 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 17
    + 14 * s ^ 16
    - 92 * s ^ 15
    + 370 * s ^ 14
    - 1115 * s ^ 13
    + 2979 * s ^ 12
    - 6801 * s ^ 11
    + 11268 * s ^ 10
    - 10225 * s ^ 9
    - 24 * s ^ 8
    + 12950 * s ^ 7
    - 17505 * s ^ 6
    + 12666 * s ^ 5
    - 2425 * s ^ 4
    + 291 * s ^ 3
    + 27 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient6 (s : ℚ) : ℚ :=
  s ^ 16
    - 6 * s ^ 15
    - 22 * s ^ 14
    + 349 * s ^ 13
    - 1380 * s ^ 12
    + 1798 * s ^ 11
    + 3954 * s ^ 10
    - 21605 * s ^ 9
    + 44797 * s ^ 8
    - 56671 * s ^ 7
    + 46705 * s ^ 6
    - 22903 * s ^ 5
    + 2234 * s ^ 4
    + 169 * s ^ 3
    - 201 * s ^ 2
    + 9 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient7 (s : ℚ) : ℚ :=
  s ^ 16
    - 13 * s ^ 15
    + 52 * s ^ 14
    + 109 * s ^ 13
    - 2017 * s ^ 12
    + 9926 * s ^ 11
    - 28664 * s ^ 10
    + 55531 * s ^ 9
    - 75599 * s ^ 8
    + 73204 * s ^ 7
    - 46672 * s ^ 6
    + 13273 * s ^ 5
    + 4634 * s ^ 4
    - 1911 * s ^ 3
    + 538 * s ^ 2
    - 15 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient8 (s : ℚ) : ℚ :=
  s ^ 16
    - 20 * s ^ 15
    + 186 * s ^ 14
    - 1059 * s ^ 13
    + 4092 * s ^ 12
    - 11285 * s ^ 11
    + 22849 * s ^ 10
    - 34355 * s ^ 9
    + 37824 * s ^ 8
    - 27680 * s ^ 7
    + 6799 * s ^ 6
    + 10544 * s ^ 5
    - 11603 * s ^ 4
    + 2833 * s ^ 3
    - 594 * s ^ 2
    - 22 * s
    + 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 13
    + 12 * s ^ 12
    - 68 * s ^ 11
    + 285 * s ^ 10
    - 1096 * s ^ 9
    + 3611 * s ^ 8
    - 8919 * s ^ 7
    + 14936 * s ^ 6
    - 15281 * s ^ 5
    + 8050 * s ^ 4
    - 1106 * s ^ 3
    + 156 * s ^ 2
    + 91 * s
    - 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 12
    + 18 * s ^ 11
    - 143 * s ^ 10
    + 665 * s ^ 9
    - 2005 * s ^ 8
    + 4027 * s ^ 7
    - 5190 * s ^ 6
    + 3747 * s ^ 5
    - 805 * s ^ 4
    - 591 * s ^ 3
    + 174 * s ^ 2
    - 104 * s
    + 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient11 (s : ℚ) : ℚ :=
  s ^ 9
    - 15 * s ^ 8
    + 94 * s ^ 7
    - 317 * s ^ 6
    + 618 * s ^ 5
    - 694 * s ^ 4
    + 408 * s ^ 3
    - 105 * s ^ 2
    + 51 * s
    - 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineNumeratorCoefficient12 (s : ℚ) : ℚ :=
  -s ^ 3
    + 6 * s ^ 2
    - 9 * s
    + 1

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitNineNumerator (r s : ℚ) : ℚ :=
  rawUnitNineNumeratorCoefficient0 s +
    rawUnitNineNumeratorCoefficient1 s * r +
    rawUnitNineNumeratorCoefficient2 s * r ^ 2 +
    rawUnitNineNumeratorCoefficient3 s * r ^ 3 +
    rawUnitNineNumeratorCoefficient4 s * r ^ 4 +
    rawUnitNineNumeratorCoefficient5 s * r ^ 5 +
    rawUnitNineNumeratorCoefficient6 s * r ^ 6 +
    rawUnitNineNumeratorCoefficient7 s * r ^ 7 +
    rawUnitNineNumeratorCoefficient8 s * r ^ 8 +
    rawUnitNineNumeratorCoefficient9 s * r ^ 9 +
    rawUnitNineNumeratorCoefficient10 s * r ^ 10 +
    rawUnitNineNumeratorCoefficient11 s * r ^ 11 +
    rawUnitNineNumeratorCoefficient12 s * r ^ 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient0 (s : ℚ) : ℚ :=
  s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 14
    + 3 * s ^ 13
    - 6 * s ^ 12
    + 10 * s ^ 11
    - 15 * s ^ 10
    + 23 * s ^ 9
    - 25 * s ^ 8
    - s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient2 (s : ℚ) : ℚ :=
  -2 * s ^ 15
    + 9 * s ^ 14
    - 14 * s ^ 13
    + 28 * s ^ 12
    - 63 * s ^ 11
    + 117 * s ^ 10
    - 143 * s ^ 9
    + 23 * s ^ 8
    + 151 * s ^ 7
    - 56 * s ^ 6
    + 21 * s ^ 5
    - 6 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 16
    + 5 * s ^ 15
    + s ^ 14
    - 10 * s ^ 13
    - 76 * s ^ 12
    + 218 * s ^ 11
    - 203 * s ^ 10
    - 333 * s ^ 9
    + 1327 * s ^ 8
    - 1499 * s ^ 7
    + 491 * s ^ 6
    - 185 * s ^ 5
    + 53 * s ^ 4
    - 7 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 16
    + 12 * s ^ 15
    - 25 * s ^ 14
    - 81 * s ^ 13
    + 236 * s ^ 12
    + 375 * s ^ 11
    - 2597 * s ^ 10
    + 6290 * s ^ 9
    - 8485 * s ^ 8
    + 5676 * s ^ 7
    - 1335 * s ^ 6
    + 583 * s ^ 5
    - 168 * s ^ 4
    + 2 * s ^ 3
    + 13 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 16
    + 17 * s ^ 15
    - 81 * s ^ 14
    - 79 * s ^ 13
    + 1857 * s ^ 12
    - 7111 * s ^ 11
    + 15408 * s ^ 10
    - 22144 * s ^ 9
    + 19229 * s ^ 8
    - 7045 * s ^ 7
    - 383 * s ^ 6
    - 681 * s ^ 5
    + 153 * s ^ 4
    + 145 * s ^ 3
    - 76 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient6 (s : ℚ) : ℚ :=
  -3 * s ^ 16
    + 58 * s ^ 15
    - 511 * s ^ 14
    + 2576 * s ^ 13
    - 8111 * s ^ 12
    + 17051 * s ^ 11
    - 24908 * s ^ 10
    + 23210 * s ^ 9
    - 7317 * s ^ 8
    - 8512 * s ^ 7
    + 6923 * s ^ 6
    + 530 * s ^ 5
    + 421 * s ^ 4
    - 747 * s ^ 3
    + 264 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 17
    + 18 * s ^ 16
    - 150 * s ^ 15
    + 741 * s ^ 14
    - 2327 * s ^ 13
    + 4701 * s ^ 12
    - 5657 * s ^ 11
    + 1083 * s ^ 10
    + 12223 * s ^ 9
    - 26962 * s ^ 8
    + 24382 * s ^ 7
    - 5821 * s ^ 6
    - 2419 * s ^ 5
    - 2099 * s ^ 4
    + 2103 * s ^ 3
    - 607 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient8 (s : ℚ) : ℚ :=
  s ^ 16
    - 18 * s ^ 15
    + 153 * s ^ 14
    - 788 * s ^ 13
    + 2745 * s ^ 12
    - 7104 * s ^ 11
    + 14521 * s ^ 10
    - 22199 * s ^ 9
    + 20314 * s ^ 8
    - 4120 * s ^ 7
    - 8581 * s ^ 6
    + 2630 * s ^ 5
    + 5925 * s ^ 4
    - 3936 * s ^ 3
    + 951 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient9 (s : ℚ) : ℚ :=
  4 * s ^ 13
    - 63 * s ^ 12
    + 335 * s ^ 11
    - 519 * s ^ 10
    - 1673 * s ^ 9
    + 8455 * s ^ 8
    - 13817 * s ^ 7
    + 7157 * s ^ 6
    + 6321 * s ^ 5
    - 10199 * s ^ 4
    + 4755 * s ^ 3
    - 970 * s ^ 2
    - 6 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient10 (s : ℚ) : ℚ :=
  s ^ 13
    - 23 * s ^ 12
    + 211 * s ^ 11
    - 1013 * s ^ 10
    + 2704 * s ^ 9
    - 3557 * s ^ 8
    - 77 * s ^ 7
    + 7771 * s ^ 6
    - 12106 * s ^ 5
    + 8793 * s ^ 4
    - 3215 * s ^ 3
    + 564 * s ^ 2
    + 13 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 12
    + 19 * s ^ 11
    - 158 * s ^ 10
    + 755 * s ^ 9
    - 2288 * s ^ 8
    + 4576 * s ^ 7
    - 6088 * s ^ 6
    + 5293 * s ^ 5
    - 2872 * s ^ 4
    + 898 * s ^ 3
    - 134 * s ^ 2
    - 12 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNineDenominatorCoefficient12 (s : ℚ) : ℚ :=
  s ^ 3
    - 4 * s ^ 2
    + 4 * s

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitNineDenominator (r s : ℚ) : ℚ :=
  rawUnitNineDenominatorCoefficient0 s +
    rawUnitNineDenominatorCoefficient1 s * r +
    rawUnitNineDenominatorCoefficient2 s * r ^ 2 +
    rawUnitNineDenominatorCoefficient3 s * r ^ 3 +
    rawUnitNineDenominatorCoefficient4 s * r ^ 4 +
    rawUnitNineDenominatorCoefficient5 s * r ^ 5 +
    rawUnitNineDenominatorCoefficient6 s * r ^ 6 +
    rawUnitNineDenominatorCoefficient7 s * r ^ 7 +
    rawUnitNineDenominatorCoefficient8 s * r ^ 8 +
    rawUnitNineDenominatorCoefficient9 s * r ^ 9 +
    rawUnitNineDenominatorCoefficient10 s * r ^ 10 +
    rawUnitNineDenominatorCoefficient11 s * r ^ 11 +
    rawUnitNineDenominatorCoefficient12 s * r ^ 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoPoleFactorCoefficient0 (s : ℚ) : ℚ :=
  s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoPoleFactorCoefficient1 (s : ℚ) : ℚ :=
  3 * s ^ 6
    - 15 * s ^ 5
    + 10 * s ^ 4
    - 6 * s ^ 3
    + 3 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoPoleFactorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 9
    - 6 * s ^ 8
    + 21 * s ^ 7
    - 50 * s ^ 6
    + 66 * s ^ 5
    - 31 * s ^ 4
    + 25 * s ^ 3
    - 18 * s ^ 2
    + 7 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoPoleFactorCoefficient3 (s : ℚ) : ℚ :=
  -3 * s ^ 7
    + 3 * s ^ 6
    + 21 * s ^ 5
    - 30 * s ^ 4
    - 41 * s ^ 3
    + 51 * s ^ 2
    - 21 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoPoleFactorCoefficient4 (s : ℚ) : ℚ :=
  -2 * s ^ 7
    + 12 * s ^ 6
    - 9 * s ^ 5
    - 60 * s ^ 4
    + 144 * s ^ 3
    - 105 * s ^ 2
    + 35 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoPoleFactorCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 7
    + 11 * s ^ 6
    - 48 * s ^ 5
    + 105 * s ^ 4
    - 121 * s ^ 3
    + 69 * s ^ 2
    - 20 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitTwoPoleFactorCoefficient6 (_s : ℚ) : ℚ :=
  1

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitTwoPoleFactor (r s : ℚ) : ℚ :=
  rawUnitTwoPoleFactorCoefficient0 s +
    rawUnitTwoPoleFactorCoefficient1 s * r +
    rawUnitTwoPoleFactorCoefficient2 s * r ^ 2 +
    rawUnitTwoPoleFactorCoefficient3 s * r ^ 3 +
    rawUnitTwoPoleFactorCoefficient4 s * r ^ 4 +
    rawUnitTwoPoleFactorCoefficient5 s * r ^ 5 +
    rawUnitTwoPoleFactorCoefficient6 s * r ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightPoleFactorCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightPoleFactorCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 3
    + 6 * s ^ 2
    - 3 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightPoleFactorCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 4
    + 5 * s ^ 3
    - 9 * s ^ 2
    + 4 * s
    - 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitEightPoleFactorCoefficient3 (_s : ℚ) : ℚ :=
  1

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitEightPoleFactor (r s : ℚ) : ℚ :=
  rawUnitEightPoleFactorCoefficient0 s +
    rawUnitEightPoleFactorCoefficient1 s * r +
    rawUnitEightPoleFactorCoefficient2 s * r ^ 2 +
    rawUnitEightPoleFactorCoefficient3 s * r ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient1 (s : ℚ) : ℚ :=
  s ^ 12
    - 3 * s ^ 11
    + 6 * s ^ 10
    - 10 * s ^ 9
    + 15 * s ^ 8
    - 21 * s ^ 7
    + 21 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 12
    - 9 * s ^ 11
    + 13 * s ^ 10
    - s ^ 9
    - 24 * s ^ 8
    + 28 * s ^ 7
    + 42 * s ^ 6
    - 126 * s ^ 5
    + 56 * s ^ 4
    - 21 * s ^ 3
    + 6 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient3 (s : ℚ) : ℚ :=
  s ^ 12
    - 15 * s ^ 11
    + 66 * s ^ 10
    - 84 * s ^ 9
    - 45 * s ^ 8
    + 402 * s ^ 7
    - 833 * s ^ 6
    + 837 * s ^ 5
    - 351 * s ^ 4
    + 145 * s ^ 3
    - 48 * s ^ 2
    + 9 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient4 (s : ℚ) : ℚ :=
  s ^ 12
    - 21 * s ^ 11
    + 165 * s ^ 10
    - 650 * s ^ 9
    + 1530 * s ^ 8
    - 2562 * s ^ 7
    + 2957 * s ^ 6
    - 2046 * s ^ 5
    + 780 * s ^ 4
    - 415 * s ^ 3
    + 171 * s ^ 2
    - 36 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient5 (s : ℚ) : ℚ :=
  s ^ 13
    - 14 * s ^ 12
    + 93 * s ^ 11
    - 370 * s ^ 10
    + 970 * s ^ 9
    - 1827 * s ^ 8
    + 2553 * s ^ 7
    - 2296 * s ^ 6
    + 1095 * s ^ 5
    - 480 * s ^ 4
    + 686 * s ^ 3
    - 369 * s ^ 2
    + 84 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient6 (s : ℚ) : ℚ :=
  -10 * s ^ 9
    + 45 * s ^ 8
    + 24 * s ^ 7
    - 357 * s ^ 6
    + 324 * s ^ 5
    + 570 * s ^ 4
    - 1130 * s ^ 3
    + 576 * s ^ 2
    - 126 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient7 (s : ℚ) : ℚ :=
  -4 * s ^ 9
    + 39 * s ^ 8
    - 120 * s ^ 7
    + 28 * s ^ 6
    + 597 * s ^ 5
    - 1341 * s ^ 4
    + 1256 * s ^ 3
    - 525 * s ^ 2
    + 105 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 9
    + 15 * s ^ 8
    - 94 * s ^ 7
    + 319 * s ^ 6
    - 636 * s ^ 5
    + 756 * s ^ 4
    - 520 * s ^ 3
    + 189 * s ^ 2
    - 35 * s
    - 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def rawUnitNinePoleFactorCoefficient9 (_s : ℚ) : ℚ :=
  1

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def rawUnitNinePoleFactor (r s : ℚ) : ℚ :=
  rawUnitNinePoleFactorCoefficient0 s +
    rawUnitNinePoleFactorCoefficient1 s * r +
    rawUnitNinePoleFactorCoefficient2 s * r ^ 2 +
    rawUnitNinePoleFactorCoefficient3 s * r ^ 3 +
    rawUnitNinePoleFactorCoefficient4 s * r ^ 4 +
    rawUnitNinePoleFactorCoefficient5 s * r ^ 5 +
    rawUnitNinePoleFactorCoefficient6 s * r ^ 6 +
    rawUnitNinePoleFactorCoefficient7 s * r ^ 7 +
    rawUnitNinePoleFactorCoefficient8 s * r ^ 8 +
    rawUnitNinePoleFactorCoefficient9 s * r ^ 9

/-- Factorization of the first raw-unit denominator. -/
theorem rawUnitOneDenominator_factorization (r s : ℚ) :
    rawUnitOneDenominator r s =
      (s - 1) ^ 2 * r * (r - s ^ 2 + s - 1) ^ 2 *
        (r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) ^ 2 := by
  simp only [rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominator]
  ring

/-- Factorization of the second raw-unit denominator. -/
theorem rawUnitTwoDenominator_factorization (r s : ℚ) :
    rawUnitTwoDenominator r s =
      (r - s) ^ 2 * rawUnitTwoPoleFactor r s := by
  simp only [rawUnitTwoDenominatorCoefficient0,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominator,
    rawUnitTwoPoleFactorCoefficient0,
    rawUnitTwoPoleFactorCoefficient1,
    rawUnitTwoPoleFactorCoefficient2,
    rawUnitTwoPoleFactorCoefficient3,
    rawUnitTwoPoleFactorCoefficient4,
    rawUnitTwoPoleFactorCoefficient5,
    rawUnitTwoPoleFactorCoefficient6,
    rawUnitTwoPoleFactor]
  ring

/-- Factorization of the eighth raw-unit denominator. -/
theorem rawUnitEightDenominator_factorization (r s : ℚ) :
    rawUnitEightDenominator r s = rawUnitEightPoleFactor r s := by
  simp only [rawUnitEightDenominatorCoefficient0,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominator,
    rawUnitEightPoleFactorCoefficient0,
    rawUnitEightPoleFactorCoefficient1,
    rawUnitEightPoleFactorCoefficient2,
    rawUnitEightPoleFactorCoefficient3,
    rawUnitEightPoleFactor]

/-- Factorization of the ninth raw-unit denominator. -/
theorem rawUnitNineDenominator_factorization (r s : ℚ) :
    rawUnitNineDenominator r s =
      s * (r - s) * (r * s - 2 * r + 1) ^ 2 *
        rawUnitNinePoleFactor r s := by
  simp only [rawUnitNineDenominatorCoefficient0,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominator,
    rawUnitNinePoleFactorCoefficient0,
    rawUnitNinePoleFactorCoefficient1,
    rawUnitNinePoleFactorCoefficient2,
    rawUnitNinePoleFactorCoefficient3,
    rawUnitNinePoleFactorCoefficient4,
    rawUnitNinePoleFactorCoefficient5,
    rawUnitNinePoleFactorCoefficient6,
    rawUnitNinePoleFactorCoefficient7,
    rawUnitNinePoleFactorCoefficient8,
    rawUnitNinePoleFactorCoefficient9,
    rawUnitNinePoleFactor]
  ring

namespace RelationZeroCertificate

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 17
    + 4 * s ^ 16
    - 10 * s ^ 15
    + 18 * s ^ 14
    - 25 * s ^ 13
    + 28 * s ^ 12
    - 25 * s ^ 11
    + 18 * s ^ 10
    - 10 * s ^ 9
    + 4 * s ^ 8
    - s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient2 (s : ℚ) : ℚ :=
  -3 * s ^ 17
    + 30 * s ^ 16
    - 103 * s ^ 15
    + 242 * s ^ 14
    - 432 * s ^ 13
    + 620 * s ^ 12
    - 742 * s ^ 11
    + 740 * s ^ 10
    - 622 * s ^ 9
    + 434 * s ^ 8
    - 246 * s ^ 7
    + 110 * s ^ 6
    - 35 * s ^ 5
    + 8 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient3 (s : ℚ) : ℚ :=
  s ^ 19
    - 11 * s ^ 18
    + 59 * s ^ 17
    - 177 * s ^ 16
    + 310 * s ^ 15
    - 409 * s ^ 14
    + 359 * s ^ 13
    - 97 * s ^ 12
    - 384 * s ^ 11
    + 1050 * s ^ 10
    - 1658 * s ^ 9
    + 2034 * s ^ 8
    - 2008 * s ^ 7
    + 1607 * s ^ 6
    - 1040 * s ^ 5
    + 515 * s ^ 4
    - 197 * s ^ 3
    + 55 * s ^ 2
    - 10 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient4 (s : ℚ) : ℚ :=
  s ^ 19
    - 20 * s ^ 18
    + 157 * s ^ 17
    - 720 * s ^ 16
    + 2154 * s ^ 15
    - 4722 * s ^ 14
    + 8841 * s ^ 13
    - 14470 * s ^ 12
    + 21134 * s ^ 11
    - 27504 * s ^ 10
    + 31426 * s ^ 9
    - 31544 * s ^ 8
    + 27301 * s ^ 7
    - 20068 * s ^ 6
    + 12263 * s ^ 5
    - 6000 * s ^ 4
    + 2328 * s ^ 3
    - 674 * s ^ 2
    + 131 * s
    - 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient5 (s : ℚ) : ℚ :=
  s ^ 20
    - 15 * s ^ 19
    + 107 * s ^ 18
    - 473 * s ^ 17
    + 1490 * s ^ 16
    - 3817 * s ^ 15
    + 9215 * s ^ 14
    - 21074 * s ^ 13
    + 41611 * s ^ 12
    - 70562 * s ^ 11
    + 102212 * s ^ 10
    - 126905 * s ^ 9
    + 135789 * s ^ 8
    - 123557 * s ^ 7
    + 94741 * s ^ 6
    - 60087 * s ^ 5
    + 30750 * s ^ 4
    - 12567 * s ^ 3
    + 3849 * s ^ 2
    - 799 * s
    + 91

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient6 (s : ℚ) : ℚ :=
  -2 * s ^ 19
    + 20 * s ^ 18
    - 60 * s ^ 17
    - 212 * s ^ 16
    + 2646 * s ^ 15
    - 12116 * s ^ 14
    + 35389 * s ^ 13
    - 78054 * s ^ 12
    + 143006 * s ^ 11
    - 222168 * s ^ 10
    + 296317 * s ^ 9
    - 338462 * s ^ 8
    + 326325 * s ^ 7
    - 263858 * s ^ 6
    + 176013 * s ^ 5
    - 95370 * s ^ 4
    + 41455 * s ^ 3
    - 13498 * s ^ 2
    + 2991 * s
    - 362

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient7 (s : ℚ) : ℚ :=
  -2 * s ^ 19
    + 37 * s ^ 18
    - 313 * s ^ 17
    + 1647 * s ^ 16
    - 6107 * s ^ 15
    + 17427 * s ^ 14
    - 41965 * s ^ 13
    + 91771 * s ^ 12
    - 180959 * s ^ 11
    + 308655 * s ^ 10
    - 450051 * s ^ 9
    + 552911 * s ^ 8
    - 567569 * s ^ 7
    + 486717 * s ^ 6
    - 344465 * s ^ 5
    + 199565 * s ^ 4
    - 92895 * s ^ 3
    + 32244 * s ^ 2
    - 7626 * s
    + 978

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient8 (s : ℚ) : ℚ :=
  2 * s ^ 18
    - 25 * s ^ 17
    + 114 * s ^ 16
    - 15 * s ^ 15
    - 2660 * s ^ 14
    + 16807 * s ^ 13
    - 60536 * s ^ 12
    + 152883 * s ^ 11
    - 298520 * s ^ 10
    + 474459 * s ^ 9
    - 621364 * s ^ 8
    + 678625 * s ^ 7
    - 621344 * s ^ 6
    + 472185 * s ^ 5
    - 296052 * s ^ 4
    + 148455 * s ^ 3
    - 55022 * s ^ 2
    + 13890 * s
    - 1882

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient9 (s : ℚ) : ℚ :=
  s ^ 18
    - 21 * s ^ 17
    + 206 * s ^ 16
    - 1280 * s ^ 15
    + 5659 * s ^ 14
    - 18881 * s ^ 13
    + 49889 * s ^ 12
    - 109775 * s ^ 11
    + 208035 * s ^ 10
    - 338668 * s ^ 9
    + 468541 * s ^ 8
    - 553423 * s ^ 7
    + 553611 * s ^ 6
    - 462102 * s ^ 5
    + 318219 * s ^ 4
    - 172546 * s ^ 3
    + 68322 * s ^ 2
    - 18416 * s
    + 2629

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient10 (s : ℚ) : ℚ :=
  -2 * s ^ 16
    + 35 * s ^ 15
    - 300 * s ^ 14
    + 1740 * s ^ 13
    - 7586 * s ^ 12
    + 25320 * s ^ 11
    - 64922 * s ^ 10
    + 131010 * s ^ 9
    - 216872 * s ^ 8
    + 300666 * s ^ 7
    - 345096 * s ^ 6
    + 325549 * s ^ 5
    - 248530 * s ^ 4
    + 145427 * s ^ 3
    - 61510 * s ^ 2
    + 17733 * s
    - 2662

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient11 (s : ℚ) : ℚ :=
  -s ^ 15
    + 22 * s ^ 14
    - 209 * s ^ 13
    + 1174 * s ^ 12
    - 4559 * s ^ 11
    + 13679 * s ^ 10
    - 33904 * s ^ 9
    + 69743 * s ^ 8
    - 115757 * s ^ 7
    + 153508 * s ^ 6
    - 163776 * s ^ 5
    + 137320 * s ^ 4
    - 86065 * s ^ 3
    + 39019 * s ^ 2
    - 12105 * s
    + 1911

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient12 (s : ℚ) : ℚ :=
  2 * s ^ 13
    - 40 * s ^ 12
    + 354 * s ^ 11
    - 1846 * s ^ 10
    + 6391 * s ^ 9
    - 15826 * s ^ 8
    + 29831 * s ^ 7
    - 44774 * s ^ 6
    + 53482 * s ^ 5
    - 48758 * s ^ 4
    + 32885 * s ^ 3
    - 16320 * s ^ 2
    + 5543 * s
    - 924

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient13 (s : ℚ) : ℚ :=
  -s ^ 11
    + 19 * s ^ 10
    - 161 * s ^ 9
    + 800 * s ^ 8
    - 2568 * s ^ 7
    + 5540 * s ^ 6
    - 8203 * s ^ 5
    + 8590 * s ^ 4
    - 6685 * s ^ 3
    + 3917 * s ^ 2
    - 1518 * s
    + 270

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient14 (s : ℚ) : ℚ :=
  s ^ 7
    - 14 * s ^ 6
    + 80 * s ^ 5
    - 240 * s ^ 4
    + 405 * s ^ 3
    - 382 * s ^ 2
    + 186 * s
    - 36

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t1Step1 (r s : ℚ) : ℚ :=
  t1Step1Coefficient0 s +
    t1Step1Coefficient1 s * r +
    t1Step1Coefficient2 s * r ^ 2 +
    t1Step1Coefficient3 s * r ^ 3 +
    t1Step1Coefficient4 s * r ^ 4 +
    t1Step1Coefficient5 s * r ^ 5 +
    t1Step1Coefficient6 s * r ^ 6 +
    t1Step1Coefficient7 s * r ^ 7 +
    t1Step1Coefficient8 s * r ^ 8 +
    t1Step1Coefficient9 s * r ^ 9 +
    t1Step1Coefficient10 s * r ^ 10 +
    t1Step1Coefficient11 s * r ^ 11 +
    t1Step1Coefficient12 s * r ^ 12 +
    t1Step1Coefficient13 s * r ^ 13 +
    t1Step1Coefficient14 s * r ^ 14

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_0 (s : ℚ) :
    t1Step1Coefficient0 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t1Step1Coefficient0,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_1 (s : ℚ) :
    t1Step1Coefficient1 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t1Step1Coefficient1,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_2 (s : ℚ) :
    t1Step1Coefficient2 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t1Step1Coefficient2,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_3 (s : ℚ) :
    t1Step1Coefficient3 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t1Step1Coefficient3,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_4 (s : ℚ) :
    t1Step1Coefficient4 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t1Step1Coefficient4,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_5 (s : ℚ) :
    t1Step1Coefficient5 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t1Step1Coefficient5,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_6 (s : ℚ) :
    t1Step1Coefficient6 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t1Step1Coefficient6,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_7 (s : ℚ) :
    t1Step1Coefficient7 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t1Step1Coefficient7,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_8 (s : ℚ) :
    t1Step1Coefficient8 s =
      rawUnitOneNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient1 s := by
  simp only [t1Step1Coefficient8,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_9 (s : ℚ) :
    t1Step1Coefficient9 s =
      rawUnitOneNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient2 s := by
  simp only [t1Step1Coefficient9,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_10 (s : ℚ) :
    t1Step1Coefficient10 s =
      rawUnitOneNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient3 s := by
  simp only [t1Step1Coefficient10,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_11 (s : ℚ) :
    t1Step1Coefficient11 s =
      rawUnitOneNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient4 s := by
  simp only [t1Step1Coefficient11,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_12 (s : ℚ) :
    t1Step1Coefficient12 s =
      rawUnitOneNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient5 s := by
  simp only [t1Step1Coefficient12,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_13 (s : ℚ) :
    t1Step1Coefficient13 s =
      rawUnitOneNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient6 s := by
  simp only [t1Step1Coefficient13,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step1Coefficient_product_certificate_14 (s : ℚ) :
    t1Step1Coefficient14 s =
      rawUnitOneNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient7 s := by
  simp only [t1Step1Coefficient14,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step1_eq_rawUnitOneNumerator_mul_rawUnitOneDenominator (r s : ℚ) :
    t1Step1 r s =
      rawUnitOneNumerator r s * rawUnitOneDenominator r s := by
  have h0 := t1Step1Coefficient_product_certificate_0 s
  have h1 := t1Step1Coefficient_product_certificate_1 s
  have h2 := t1Step1Coefficient_product_certificate_2 s
  have h3 := t1Step1Coefficient_product_certificate_3 s
  have h4 := t1Step1Coefficient_product_certificate_4 s
  have h5 := t1Step1Coefficient_product_certificate_5 s
  have h6 := t1Step1Coefficient_product_certificate_6 s
  have h7 := t1Step1Coefficient_product_certificate_7 s
  have h8 := t1Step1Coefficient_product_certificate_8 s
  have h9 := t1Step1Coefficient_product_certificate_9 s
  have h10 := t1Step1Coefficient_product_certificate_10 s
  have h11 := t1Step1Coefficient_product_certificate_11 s
  have h12 := t1Step1Coefficient_product_certificate_12 s
  have h13 := t1Step1Coefficient_product_certificate_13 s
  have h14 := t1Step1Coefficient_product_certificate_14 s
  simp only [t1Step1, rawUnitOneNumerator, rawUnitOneDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 25
    + 4 * s ^ 24
    - 10 * s ^ 23
    + 18 * s ^ 22
    - 25 * s ^ 21
    + 28 * s ^ 20
    - 25 * s ^ 19
    + 18 * s ^ 18
    - 10 * s ^ 17
    + 4 * s ^ 16
    - s ^ 15

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient2 (s : ℚ) : ℚ :=
  s ^ 31
    - 7 * s ^ 30
    + 28 * s ^ 29
    - 82 * s ^ 28
    + 194 * s ^ 27
    - 394 * s ^ 26
    + 703 * s ^ 25
    - 1080 * s ^ 24
    + 1426 * s ^ 23
    - 1585 * s ^ 22
    + 1447 * s ^ 21
    - 1027 * s ^ 20
    + 465 * s ^ 19
    + 15 * s ^ 18
    - 283 * s ^ 17
    + 321 * s ^ 16
    - 225 * s ^ 15
    + 111 * s ^ 14
    - 35 * s ^ 13
    + 8 * s ^ 12
    - s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient3 (s : ℚ) : ℚ :=
  2 * s ^ 32
    - 14 * s ^ 31
    + 31 * s ^ 30
    + s ^ 29
    - 234 * s ^ 28
    + 940 * s ^ 27
    - 2531 * s ^ 26
    + 5731 * s ^ 25
    - 11561 * s ^ 24
    + 20512 * s ^ 23
    - 31985 * s ^ 22
    + 43372 * s ^ 21
    - 50940 * s ^ 20
    + 51548 * s ^ 19
    - 44368 * s ^ 18
    + 32114 * s ^ 17
    - 18904 * s ^ 16
    + 8546 * s ^ 15
    - 2550 * s ^ 14
    + 142 * s ^ 13
    + 272 * s ^ 12
    - 170 * s ^ 11
    + 55 * s ^ 10
    - 10 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient4 (s : ℚ) : ℚ :=
  11 * s ^ 32
    - 156 * s ^ 31
    + 894 * s ^ 30
    - 3094 * s ^ 29
    + 8135 * s ^ 28
    - 18224 * s ^ 27
    + 37418 * s ^ 26
    - 71779 * s ^ 25
    + 124148 * s ^ 24
    - 186393 * s ^ 23
    + 237862 * s ^ 22
    - 248102 * s ^ 21
    + 195992 * s ^ 20
    - 84444 * s ^ 19
    - 53820 * s ^ 18
    + 168468 * s ^ 17
    - 224049 * s ^ 16
    + 212439 * s ^ 15
    - 156957 * s ^ 14
    + 92113 * s ^ 13
    - 42358 * s ^ 12
    + 15457 * s ^ 11
    - 4334 * s ^ 10
    + 894 * s ^ 9
    - 133 * s ^ 8
    + 13 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient5 (s : ℚ) : ℚ :=
  -2 * s ^ 34
    + 34 * s ^ 33
    - 269 * s ^ 32
    + 1177 * s ^ 31
    - 2943 * s ^ 30
    + 4475 * s ^ 29
    - 5285 * s ^ 28
    + 8727 * s ^ 27
    - 20099 * s ^ 26
    + 23738 * s ^ 25
    + 54164 * s ^ 24
    - 344182 * s ^ 23
    + 979073 * s ^ 22
    - 2009331 * s ^ 21
    + 3288727 * s ^ 20
    - 4483187 * s ^ 19
    + 5175149 * s ^ 18
    - 5080204 * s ^ 17
    + 4232864 * s ^ 16
    - 2939702 * s ^ 15
    + 1647281 * s ^ 14
    - 689856 * s ^ 13
    + 166091 * s ^ 12
    + 21569 * s ^ 11
    - 48601 * s ^ 10
    + 29541 * s ^ 9
    - 11780 * s ^ 8
    + 3503 * s ^ 7
    - 794 * s ^ 6
    + 137 * s ^ 5
    - 16 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 35
    + 13 * s ^ 34
    - 42 * s ^ 33
    - 302 * s ^ 32
    + 3650 * s ^ 31
    - 17497 * s ^ 30
    + 51458 * s ^ 29
    - 116722 * s ^ 28
    + 266000 * s ^ 27
    - 694026 * s ^ 26
    + 1859942 * s ^ 25
    - 4443872 * s ^ 24
    + 9013195 * s ^ 23
    - 15584028 * s ^ 22
    + 23213982 * s ^ 21
    - 29876385 * s ^ 20
    + 33147862 * s ^ 19
    - 31262714 * s ^ 18
    + 24300679 * s ^ 17
    - 14386301 * s ^ 16
    + 4624799 * s ^ 15
    + 2226728 * s ^ 14
    - 5168240 * s ^ 13
    + 4996041 * s ^ 12
    - 3393434 * s ^ 11
    + 1803322 * s ^ 10
    - 768997 * s ^ 9
    + 264684 * s ^ 8
    - 73524 * s ^ 7
    + 16129 * s ^ 6
    - 2670 * s ^ 5
    + 283 * s ^ 4
    - 11 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient7 (s : ℚ) : ℚ :=
  -4 * s ^ 35
    + 87 * s ^ 34
    - 827 * s ^ 33
    + 4524 * s ^ 32
    - 15712 * s ^ 31
    + 38670 * s ^ 30
    - 99696 * s ^ 29
    + 386550 * s ^ 28
    - 1533120 * s ^ 27
    + 4839248 * s ^ 26
    - 12045958 * s ^ 25
    + 24323754 * s ^ 24
    - 40943190 * s ^ 23
    + 58318639 * s ^ 22
    - 69609589 * s ^ 21
    + 66298884 * s ^ 20
    - 42423152 * s ^ 19
    - 1143139 * s ^ 18
    + 54286196 * s ^ 17
    - 101160875 * s ^ 16
    + 127294888 * s ^ 15
    - 126142845 * s ^ 14
    + 102829931 * s ^ 13
    - 69857387 * s ^ 12
    + 39732952 * s ^ 11
    - 19034171 * s ^ 10
    + 7624684 * s ^ 9
    - 2528651 * s ^ 8
    + 684310 * s ^ 7
    - 145520 * s ^ 6
    + 22365 * s ^ 5
    - 1803 * s ^ 4
    - 70 * s ^ 3
    + 27 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient8 (s : ℚ) : ℚ :=
  -s ^ 36
    + 18 * s ^ 35
    - 116 * s ^ 34
    + 165 * s ^ 33
    + 1594 * s ^ 32
    - 5126 * s ^ 31
    - 45480 * s ^ 30
    + 467238 * s ^ 29
    - 2155855 * s ^ 28
    + 6533393 * s ^ 27
    - 14523217 * s ^ 26
    + 24447838 * s ^ 25
    - 29560574 * s ^ 24
    + 16719589 * s ^ 23
    + 33692743 * s ^ 22
    - 144699890 * s ^ 21
    + 331388597 * s ^ 20
    - 585038978 * s ^ 19
    + 863671209 * s ^ 18
    - 1097313733 * s ^ 17
    + 1214674589 * s ^ 16
    - 1174717054 * s ^ 15
    + 989284364 * s ^ 14
    - 722098549 * s ^ 13
    + 454021905 * s ^ 12
    - 244877602 * s ^ 11
    + 112972375 * s ^ 10
    - 44001751 * s ^ 9
    + 14245774 * s ^ 8
    - 3736400 * s ^ 7
    + 744185 * s ^ 6
    - 93386 * s ^ 5
    + 105 * s ^ 4
    + 2380 * s ^ 3
    - 349 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient9 (s : ℚ) : ℚ :=
  -s ^ 36
    + 25 * s ^ 35
    - 207 * s ^ 34
    + 128 * s ^ 33
    + 10742 * s ^ 32
    - 99298 * s ^ 31
    + 481195 * s ^ 30
    - 1425842 * s ^ 29
    + 2236027 * s ^ 28
    + 1424684 * s ^ 27
    - 21525950 * s ^ 26
    + 82079928 * s ^ 25
    - 223069780 * s ^ 24
    + 502575202 * s ^ 23
    - 992599573 * s ^ 22
    + 1753625008 * s ^ 21
    - 2783599767 * s ^ 20
    + 3971158919 * s ^ 19
    - 5087300291 * s ^ 18
    + 5838893694 * s ^ 17
    - 5982153641 * s ^ 16
    + 5436982453 * s ^ 15
    - 4350573809 * s ^ 14
    + 3043708757 * s ^ 13
    - 1849269568 * s ^ 12
    + 971169564 * s ^ 11
    - 437851284 * s ^ 10
    + 166369186 * s ^ 9
    - 52018424 * s ^ 8
    + 12737510 * s ^ 7
    - 2094350 * s ^ 6
    + 67427 * s ^ 5
    + 83520 * s ^ 4
    - 25057 * s ^ 3
    + 2873 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient10 (s : ℚ) : ℚ :=
  -2 * s ^ 36
    + 62 * s ^ 35
    - 823 * s ^ 34
    + 5755 * s ^ 33
    - 17768 * s ^ 32
    - 51013 * s ^ 31
    + 895825 * s ^ 30
    - 5508295 * s ^ 29
    + 22793899 * s ^ 28
    - 73313183 * s ^ 27
    + 198063232 * s ^ 26
    - 473018187 * s ^ 25
    + 1028191662 * s ^ 24
    - 2056912052 * s ^ 23
    + 3781820258 * s ^ 22
    - 6345878206 * s ^ 21
    + 9661955870 * s ^ 20
    - 13307000815 * s ^ 19
    + 16533374160 * s ^ 18
    - 18459948657 * s ^ 17
    + 18419764576 * s ^ 16
    - 16305882689 * s ^ 15
    + 12713520989 * s ^ 14
    - 8676670565 * s ^ 13
    + 5152978177 * s ^ 12
    - 2648279375 * s ^ 11
    + 1162678013 * s ^ 10
    - 423184937 * s ^ 9
    + 121634288 * s ^ 8
    - 23820858 * s ^ 7
    + 756319 * s ^ 6
    + 1650232 * s ^ 5
    - 743180 * s ^ 4
    + 164191 * s ^ 3
    - 16903 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient11 (s : ℚ) : ℚ :=
  -4 * s ^ 36
    + 146 * s ^ 35
    - 2515 * s ^ 34
    + 26965 * s ^ 33
    - 201475 * s ^ 32
    + 1120398 * s ^ 31
    - 4870410 * s ^ 30
    + 17336357 * s ^ 29
    - 53159574 * s ^ 28
    + 147718070 * s ^ 27
    - 384544256 * s ^ 26
    + 941673452 * s ^ 25
    - 2138128268 * s ^ 24
    + 4431127862 * s ^ 23
    - 8300285122 * s ^ 22
    + 14005445673 * s ^ 21
    - 21300617967 * s ^ 20
    + 29214156936 * s ^ 19
    - 36055058220 * s ^ 18
    + 39854192776 * s ^ 17
    - 39200927219 * s ^ 16
    + 34066843938 * s ^ 15
    - 26000499684 * s ^ 14
    + 17337210703 * s ^ 13
    - 10037038704 * s ^ 12
    + 4991236118 * s ^ 11
    - 2069996204 * s ^ 10
    + 667365484 * s ^ 9
    - 136674978 * s ^ 8
    - 7386406 * s ^ 7
    + 22858624 * s ^ 6
    - 12152055 * s ^ 5
    + 3930325 * s ^ 4
    - 776338 * s ^ 3
    + 75571 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient12 (s : ℚ) : ℚ :=
  -s ^ 37
    + 33 * s ^ 36
    - 518 * s ^ 35
    + 5102 * s ^ 34
    - 35285 * s ^ 33
    + 184293 * s ^ 32
    - 784423 * s ^ 31
    + 3005678 * s ^ 30
    - 11380063 * s ^ 29
    + 43113460 * s ^ 28
    - 153590932 * s ^ 27
    + 485899278 * s ^ 26
    - 1336735868 * s ^ 25
    + 3206494263 * s ^ 24
    - 6778258249 * s ^ 23
    + 12765049840 * s ^ 22
    - 21597136603 * s ^ 21
    + 32957346211 * s ^ 20
    - 45289602829 * s ^ 19
    + 55738476705 * s ^ 18
    - 61009054451 * s ^ 17
    + 58967133109 * s ^ 16
    - 50017288577 * s ^ 15
    + 37052435212 * s ^ 14
    - 23815908969 * s ^ 13
    + 13102253522 * s ^ 12
    - 5955498866 * s ^ 11
    + 2000088732 * s ^ 10
    - 280394346 * s ^ 9
    - 210462751 * s ^ 8
    + 222687479 * s ^ 7
    - 127281014 * s ^ 6
    + 51731406 * s ^ 5
    - 15049320 * s ^ 4
    + 2825083 * s ^ 3
    - 266321 * s ^ 2
    - 20 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient13 (s : ℚ) : ℚ :=
  3 * s ^ 36
    - 83 * s ^ 35
    + 1020 * s ^ 34
    - 6633 * s ^ 33
    + 14621 * s ^ 32
    + 148659 * s ^ 31
    - 1879856 * s ^ 30
    + 12003928 * s ^ 29
    - 54596127 * s ^ 28
    + 195679281 * s ^ 27
    - 584160164 * s ^ 26
    + 1510103889 * s ^ 25
    - 3473377668 * s ^ 24
    + 7221067318 * s ^ 23
    - 13649723915 * s ^ 22
    + 23416107030 * s ^ 21
    - 36180047258 * s ^ 20
    + 49847722830 * s ^ 19
    - 60688435369 * s ^ 18
    + 64812932607 * s ^ 17
    - 60340734615 * s ^ 16
    + 48692826441 * s ^ 15
    - 33750775588 * s ^ 14
    + 19601002580 * s ^ 13
    - 8836475773 * s ^ 12
    + 2157279001 * s ^ 11
    + 1024266424 * s ^ 10
    - 1823973145 * s ^ 9
    + 1480467332 * s ^ 8
    - 891047730 * s ^ 7
    + 426802441 * s ^ 6
    - 160516944 * s ^ 5
    + 44760941 * s ^ 4
    - 8192433 * s ^ 3
    + 756767 * s ^ 2
    + 188 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient14 (s : ℚ) : ℚ :=
  2 * s ^ 36
    - 75 * s ^ 35
    + 1328 * s ^ 34
    - 14806 * s ^ 33
    + 116700 * s ^ 32
    - 693211 * s ^ 31
    + 3245007 * s ^ 30
    - 12460508 * s ^ 29
    + 41020995 * s ^ 28
    - 121600826 * s ^ 27
    + 338125007 * s ^ 26
    - 893712745 * s ^ 25
    + 2211063343 * s ^ 24
    - 4991998503 * s ^ 23
    + 10071283038 * s ^ 22
    - 17888532898 * s ^ 21
    + 27680088473 * s ^ 20
    - 37048327329 * s ^ 19
    + 42657943881 * s ^ 18
    - 41946806204 * s ^ 17
    + 34748328350 * s ^ 16
    - 23454841775 * s ^ 15
    + 11457782173 * s ^ 14
    - 1439041304 * s ^ 13
    - 5223845831 * s ^ 12
    + 8312868032 * s ^ 11
    - 8380333267 * s ^ 10
    + 6553883837 * s ^ 9
    - 4230431687 * s ^ 8
    + 2319432049 * s ^ 7
    - 1063575578 * s ^ 6
    + 390463554 * s ^ 5
    - 106984837 * s ^ 4
    + 19314486 * s ^ 3
    - 1757769 * s ^ 2
    - 1102 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient15 (s : ℚ) : ℚ :=
  -4 * s ^ 35
    + 131 * s ^ 34
    - 2027 * s ^ 33
    + 19426 * s ^ 32
    - 126282 * s ^ 31
    + 564465 * s ^ 30
    - 1571321 * s ^ 29
    + 909072 * s ^ 28
    + 16787788 * s ^ 27
    - 107964007 * s ^ 26
    + 417127666 * s ^ 25
    - 1215976233 * s ^ 24
    + 2862509320 * s ^ 23
    - 5583543705 * s ^ 22
    + 9079144271 * s ^ 21
    - 12229446125 * s ^ 20
    + 13355590500 * s ^ 19
    - 11092942045 * s ^ 18
    + 5311691378 * s ^ 17
    + 2664421462 * s ^ 16
    - 10879225338 * s ^ 15
    + 17817113505 * s ^ 14
    - 22564908267 * s ^ 13
    + 24460866960 * s ^ 12
    - 23173102232 * s ^ 11
    + 19099321601 * s ^ 10
    - 13635122668 * s ^ 9
    + 8494862265 * s ^ 8
    - 4607227548 * s ^ 7
    + 2104080999 * s ^ 6
    - 768914029 * s ^ 5
    + 209121997 * s ^ 4
    - 37426832 * s ^ 3
    + 3361352 * s ^ 2
    + 4505 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient16 (s : ℚ) : ℚ :=
  -s ^ 35
    + 41 * s ^ 34
    - 795 * s ^ 33
    + 9744 * s ^ 32
    - 84801 * s ^ 31
    + 557367 * s ^ 30
    - 2873300 * s ^ 29
    + 11917733 * s ^ 28
    - 40506430 * s ^ 27
    + 114281091 * s ^ 26
    - 269204169 * s ^ 25
    + 525046403 * s ^ 24
    - 813354672 * s ^ 23
    + 863789446 * s ^ 22
    - 141256307 * s ^ 21
    - 2004150127 * s ^ 20
    + 5965892880 * s ^ 19
    - 11564729145 * s ^ 18
    + 18079033761 * s ^ 17
    - 24669515458 * s ^ 16
    + 30835826621 * s ^ 15
    - 36205327437 * s ^ 14
    + 39840830622 * s ^ 13
    - 40313089255 * s ^ 12
    + 36719240838 * s ^ 11
    - 29648408011 * s ^ 10
    + 21154907725 * s ^ 9
    - 13371861019 * s ^ 8
    + 7368183030 * s ^ 7
    - 3396426304 * s ^ 6
    + 1243647675 * s ^ 5
    - 336936857 * s ^ 4
    + 59874911 * s ^ 3
    - 5302196 * s ^ 2
    - 13604 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient17 (s : ℚ) : ℚ :=
  s ^ 34
    - 37 * s ^ 33
    + 664 * s ^ 32
    - 7663 * s ^ 31
    + 63644 * s ^ 30
    - 404617 * s ^ 29
    + 2052813 * s ^ 28
    - 8595757 * s ^ 27
    + 30640961 * s ^ 26
    - 95656328 * s ^ 25
    + 266870839 * s ^ 24
    - 669336167 * s ^ 23
    + 1499478767 * s ^ 22
    - 2977135171 * s ^ 21
    + 5249874736 * s ^ 20
    - 8354561004 * s ^ 19
    + 12310515478 * s ^ 18
    - 17265146056 * s ^ 17
    + 23504396898 * s ^ 16
    - 31053757260 * s ^ 15
    + 38925606324 * s ^ 14
    - 44938202477 * s ^ 13
    + 46757143509 * s ^ 12
    - 43355336855 * s ^ 11
    + 35739302375 * s ^ 10
    - 26284757829 * s ^ 9
    + 17168824513 * s ^ 8
    - 9686979219 * s ^ 7
    + 4518214241 * s ^ 6
    - 1658922468 * s ^ 5
    + 447918440 * s ^ 4
    - 79016219 * s ^ 3
    + 6879581 * s ^ 2
    + 31343 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient18 (s : ℚ) : ℚ :=
  -s ^ 32
    + 39 * s ^ 31
    - 774 * s ^ 30
    + 10013 * s ^ 29
    - 92510 * s ^ 28
    + 641112 * s ^ 27
    - 3436034 * s ^ 26
    + 14531707 * s ^ 25
    - 49273362 * s ^ 24
    + 136514255 * s ^ 23
    - 318975341 * s ^ 22
    + 662557035 * s ^ 21
    - 1306856415 * s ^ 20
    + 2558065487 * s ^ 19
    - 4947081395 * s ^ 18
    + 9141955295 * s ^ 17
    - 15608250978 * s ^ 16
    + 24013742983 * s ^ 15
    - 32814268672 * s ^ 14
    + 39667161082 * s ^ 13
    - 42538151758 * s ^ 12
    + 40685730189 * s ^ 11
    - 34908717902 * s ^ 10
    + 26866342724 * s ^ 9
    - 18224556630 * s ^ 8
    + 10512962141 * s ^ 7
    - 4948416952 * s ^ 6
    + 1818629634 * s ^ 5
    - 488951402 * s ^ 4
    + 85527886 * s ^ 3
    - 7285370 * s ^ 2
    - 56086 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient19 (s : ℚ) : ℚ :=
  -8 * s ^ 30
    + 273 * s ^ 29
    - 4385 * s ^ 28
    + 44062 * s ^ 27
    - 308181 * s ^ 26
    + 1566024 * s ^ 25
    - 5788354 * s ^ 24
    + 14665174 * s ^ 23
    - 18408084 * s ^ 22
    - 35806859 * s ^ 21
    + 294543500 * s ^ 20
    - 1042085986 * s ^ 19
    + 2697316418 * s ^ 18
    - 5711867158 * s ^ 17
    + 10316064564 * s ^ 16
    - 16196727636 * s ^ 15
    + 22403990369 * s ^ 14
    - 27640578098 * s ^ 13
    + 30710533273 * s ^ 12
    - 30890246456 * s ^ 11
    + 28083103957 * s ^ 10
    - 22750357935 * s ^ 9
    + 15953974368 * s ^ 8
    - 9345238278 * s ^ 7
    + 4418379283 * s ^ 6
    - 1621620085 * s ^ 5
    + 433662470 * s ^ 4
    - 75095110 * s ^ 3
    + 6210322 * s ^ 2
    + 78556 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient20 (s : ℚ) : ℚ :=
  -s ^ 30
    + 40 * s ^ 29
    - 761 * s ^ 28
    + 9234 * s ^ 27
    - 80437 * s ^ 26
    + 534281 * s ^ 25
    - 2800766 * s ^ 24
    + 11862310 * s ^ 23
    - 41474801 * s ^ 22
    + 122704475 * s ^ 21
    - 316048034 * s ^ 20
    + 727642460 * s ^ 19
    - 1520805746 * s ^ 18
    + 2892267122 * s ^ 17
    - 4991908250 * s ^ 16
    + 7828863935 * s ^ 15
    - 11216071442 * s ^ 14
    + 14728205907 * s ^ 13
    - 17682517388 * s ^ 12
    + 19244947925 * s ^ 11
    - 18691282301 * s ^ 10
    + 15813617824 * s ^ 9
    - 11322739923 * s ^ 8
    + 6675180934 * s ^ 7
    - 3156490710 * s ^ 6
    + 1155210971 * s ^ 5
    - 307117140 * s ^ 4
    + 52543014 * s ^ 3
    - 4166660 * s ^ 2
    - 86072 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient21 (s : ℚ) : ℚ :=
  s ^ 28
    - 29 * s ^ 27
    + 400 * s ^ 26
    - 3786 * s ^ 25
    + 30395 * s ^ 24
    - 222504 * s ^ 23
    + 1411656 * s ^ 22
    - 7309979 * s ^ 21
    + 30275219 * s ^ 20
    - 101157156 * s ^ 19
    + 279233312 * s ^ 18
    - 656903011 * s ^ 17
    + 1357887533 * s ^ 16
    - 2517512799 * s ^ 15
    + 4210410320 * s ^ 14
    - 6321479489 * s ^ 13
    + 8445227523 * s ^ 12
    - 9925795349 * s ^ 11
    + 10103362306 * s ^ 10
    - 8735523871 * s ^ 9
    + 6291572911 * s ^ 8
    - 3707873141 * s ^ 7
    + 1751071093 * s ^ 6
    - 639487895 * s ^ 5
    + 169099202 * s ^ 4
    - 28506276 * s ^ 3
    + 2120297 * s ^ 2
    + 73117 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient22 (s : ℚ) : ℚ :=
  s ^ 27
    - 39 * s ^ 26
    + 699 * s ^ 25
    - 7684 * s ^ 24
    + 58471 * s ^ 23
    - 331236 * s ^ 22
    + 1479960 * s ^ 21
    - 5514706 * s ^ 20
    + 18069882 * s ^ 19
    - 53918853 * s ^ 18
    + 147068199 * s ^ 17
    - 359924509 * s ^ 16
    + 774648997 * s ^ 15
    - 1450950435 * s ^ 14
    + 2358508886 * s ^ 13
    - 3320122821 * s ^ 12
    + 4021511271 * s ^ 11
    - 4144722161 * s ^ 10
    + 3588764028 * s ^ 9
    - 2580030626 * s ^ 8
    + 1520926444 * s ^ 7
    - 720334061 * s ^ 6
    + 263617540 * s ^ 5
    - 69470892 * s ^ 4
    + 11486046 * s ^ 3
    - 765153 * s ^ 2
    - 47248 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient23 (s : ℚ) : ℚ :=
  -2 * s ^ 25
    + 77 * s ^ 24
    - 1388 * s ^ 23
    + 15593 * s ^ 22
    - 122648 * s ^ 21
    + 719979 * s ^ 20
    - 3287890 * s ^ 19
    + 12045749 * s ^ 18
    - 36325593 * s ^ 17
    + 92229967 * s ^ 16
    - 200891268 * s ^ 15
    + 379926873 * s ^ 14
    - 625554669 * s ^ 13
    + 891377589 * s ^ 12
    - 1087627816 * s ^ 11
    + 1124462621 * s ^ 10
    - 977140260 * s ^ 9
    + 708669292 * s ^ 8
    - 423933232 * s ^ 7
    + 204087342 * s ^ 6
    - 75555132 * s ^ 5
    + 19907628 * s ^ 4
    - 3192856 * s ^ 3
    + 167586 * s ^ 2
    + 22458 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient24 (s : ℚ) : ℚ :=
  s ^ 23
    - 38 * s ^ 22
    + 680 * s ^ 21
    - 7615 * s ^ 20
    + 59802 * s ^ 19
    - 349722 * s ^ 18
    + 1578560 * s ^ 17
    - 5627015 * s ^ 16
    + 16085822 * s ^ 15
    - 37282034 * s ^ 14
    + 70661823 * s ^ 13
    - 110386706 * s ^ 12
    + 143283691 * s ^ 11
    - 155752154 * s ^ 10
    + 142479599 * s ^ 9
    - 109324070 * s ^ 8
    + 69164238 * s ^ 7
    - 34868860 * s ^ 6
    + 13280834 * s ^ 5
    - 3505620 * s ^ 4
    + 526170 * s ^ 3
    - 9982 * s ^ 2
    - 7404 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient25 (s : ℚ) : ℚ :=
  -s ^ 19
    + 33 * s ^ 18
    - 504 * s ^ 17
    + 4727 * s ^ 16
    - 30463 * s ^ 15
    + 143004 * s ^ 14
    - 505803 * s ^ 13
    + 1375185 * s ^ 12
    - 2905856 * s ^ 11
    + 4792668 * s ^ 10
    - 6160194 * s ^ 9
    + 6125134 * s ^ 8
    - 4644700 * s ^ 7
    + 2621803 * s ^ 6
    - 1054149 * s ^ 5
    + 272822 * s ^ 4
    - 30658 * s ^ 3
    - 4560 * s ^ 2
    + 1512 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient26 (s : ℚ) : ℚ :=
  s ^ 10
    - 18 * s ^ 9
    + 140 * s ^ 8
    - 616 * s ^ 7
    + 1685 * s ^ 6
    - 2962 * s ^ 5
    + 3334 * s ^ 4
    - 2308 * s ^ 3
    + 888 * s ^ 2
    - 144 * s

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t1Step2 (r s : ℚ) : ℚ :=
  t1Step2Coefficient0 s +
    t1Step2Coefficient1 s * r +
    t1Step2Coefficient2 s * r ^ 2 +
    t1Step2Coefficient3 s * r ^ 3 +
    t1Step2Coefficient4 s * r ^ 4 +
    t1Step2Coefficient5 s * r ^ 5 +
    t1Step2Coefficient6 s * r ^ 6 +
    t1Step2Coefficient7 s * r ^ 7 +
    t1Step2Coefficient8 s * r ^ 8 +
    t1Step2Coefficient9 s * r ^ 9 +
    t1Step2Coefficient10 s * r ^ 10 +
    t1Step2Coefficient11 s * r ^ 11 +
    t1Step2Coefficient12 s * r ^ 12 +
    t1Step2Coefficient13 s * r ^ 13 +
    t1Step2Coefficient14 s * r ^ 14 +
    t1Step2Coefficient15 s * r ^ 15 +
    t1Step2Coefficient16 s * r ^ 16 +
    t1Step2Coefficient17 s * r ^ 17 +
    t1Step2Coefficient18 s * r ^ 18 +
    t1Step2Coefficient19 s * r ^ 19 +
    t1Step2Coefficient20 s * r ^ 20 +
    t1Step2Coefficient21 s * r ^ 21 +
    t1Step2Coefficient22 s * r ^ 22 +
    t1Step2Coefficient23 s * r ^ 23 +
    t1Step2Coefficient24 s * r ^ 24 +
    t1Step2Coefficient25 s * r ^ 25 +
    t1Step2Coefficient26 s * r ^ 26

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_0 (s : ℚ) :
    t1Step2Coefficient0 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient0,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_1 (s : ℚ) :
    t1Step2Coefficient1 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient1,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_2 (s : ℚ) :
    t1Step2Coefficient2 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient2,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_3 (s : ℚ) :
    t1Step2Coefficient3 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient3,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_4 (s : ℚ) :
    t1Step2Coefficient4 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient4,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_5 (s : ℚ) :
    t1Step2Coefficient5 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient5,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_6 (s : ℚ) :
    t1Step2Coefficient6 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient6,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_7 (s : ℚ) :
    t1Step2Coefficient7 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient7,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_8 (s : ℚ) :
    t1Step2Coefficient8 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient8,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_9 (s : ℚ) :
    t1Step2Coefficient9 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient9,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_10 (s : ℚ) :
    t1Step2Coefficient10 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient10,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_11 (s : ℚ) :
    t1Step2Coefficient11 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient11,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_12 (s : ℚ) :
    t1Step2Coefficient12 s =
      t1Step1Coefficient0 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient12,
    t1Step1Coefficient0,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_13 (s : ℚ) :
    t1Step2Coefficient13 s =
      t1Step1Coefficient1 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient13,
    t1Step1Coefficient1,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_14 (s : ℚ) :
    t1Step2Coefficient14 s =
      t1Step1Coefficient2 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient1 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [t1Step2Coefficient14,
    t1Step1Coefficient2,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient1,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_15 (s : ℚ) :
    t1Step2Coefficient15 s =
      t1Step1Coefficient3 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient2 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient1 s := by
  simp only [t1Step2Coefficient15,
    t1Step1Coefficient3,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient2,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_16 (s : ℚ) :
    t1Step2Coefficient16 s =
      t1Step1Coefficient4 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient3 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient2 s := by
  simp only [t1Step2Coefficient16,
    t1Step1Coefficient4,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient3,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_17 (s : ℚ) :
    t1Step2Coefficient17 s =
      t1Step1Coefficient5 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient4 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient3 s := by
  simp only [t1Step2Coefficient17,
    t1Step1Coefficient5,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient4,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_18 (s : ℚ) :
    t1Step2Coefficient18 s =
      t1Step1Coefficient6 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient5 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient4 s := by
  simp only [t1Step2Coefficient18,
    t1Step1Coefficient6,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient5,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_19 (s : ℚ) :
    t1Step2Coefficient19 s =
      t1Step1Coefficient7 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient6 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient5 s := by
  simp only [t1Step2Coefficient19,
    t1Step1Coefficient7,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient6,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_20 (s : ℚ) :
    t1Step2Coefficient20 s =
      t1Step1Coefficient8 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient7 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient6 s := by
  simp only [t1Step2Coefficient20,
    t1Step1Coefficient8,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient7,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_21 (s : ℚ) :
    t1Step2Coefficient21 s =
      t1Step1Coefficient9 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient8 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient7 s := by
  simp only [t1Step2Coefficient21,
    t1Step1Coefficient9,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient8,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_22 (s : ℚ) :
    t1Step2Coefficient22 s =
      t1Step1Coefficient10 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient9 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient8 s := by
  simp only [t1Step2Coefficient22,
    t1Step1Coefficient10,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient9,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient8]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_23 (s : ℚ) :
    t1Step2Coefficient23 s =
      t1Step1Coefficient11 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient10 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient9 s := by
  simp only [t1Step2Coefficient23,
    t1Step1Coefficient11,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient10,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient9]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_24 (s : ℚ) :
    t1Step2Coefficient24 s =
      t1Step1Coefficient12 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient11 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient10 s := by
  simp only [t1Step2Coefficient24,
    t1Step1Coefficient12,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient11,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient10]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_25 (s : ℚ) :
    t1Step2Coefficient25 s =
      t1Step1Coefficient13 s *
          rawUnitNineDenominatorCoefficient12 s +
        t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient11 s := by
  simp only [t1Step2Coefficient25,
    t1Step1Coefficient13,
    rawUnitNineDenominatorCoefficient12,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient11]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step2Coefficient_product_certificate_26 (s : ℚ) :
    t1Step2Coefficient26 s =
      t1Step1Coefficient14 s *
          rawUnitNineDenominatorCoefficient12 s := by
  simp only [t1Step2Coefficient26,
    t1Step1Coefficient14,
    rawUnitNineDenominatorCoefficient12]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step2_eq_t1Step1_mul_rawUnitNineDenominator (r s : ℚ) :
    t1Step2 r s =
      t1Step1 r s * rawUnitNineDenominator r s := by
  have h0 := t1Step2Coefficient_product_certificate_0 s
  have h1 := t1Step2Coefficient_product_certificate_1 s
  have h2 := t1Step2Coefficient_product_certificate_2 s
  have h3 := t1Step2Coefficient_product_certificate_3 s
  have h4 := t1Step2Coefficient_product_certificate_4 s
  have h5 := t1Step2Coefficient_product_certificate_5 s
  have h6 := t1Step2Coefficient_product_certificate_6 s
  have h7 := t1Step2Coefficient_product_certificate_7 s
  have h8 := t1Step2Coefficient_product_certificate_8 s
  have h9 := t1Step2Coefficient_product_certificate_9 s
  have h10 := t1Step2Coefficient_product_certificate_10 s
  have h11 := t1Step2Coefficient_product_certificate_11 s
  have h12 := t1Step2Coefficient_product_certificate_12 s
  have h13 := t1Step2Coefficient_product_certificate_13 s
  have h14 := t1Step2Coefficient_product_certificate_14 s
  have h15 := t1Step2Coefficient_product_certificate_15 s
  have h16 := t1Step2Coefficient_product_certificate_16 s
  have h17 := t1Step2Coefficient_product_certificate_17 s
  have h18 := t1Step2Coefficient_product_certificate_18 s
  have h19 := t1Step2Coefficient_product_certificate_19 s
  have h20 := t1Step2Coefficient_product_certificate_20 s
  have h21 := t1Step2Coefficient_product_certificate_21 s
  have h22 := t1Step2Coefficient_product_certificate_22 s
  have h23 := t1Step2Coefficient_product_certificate_23 s
  have h24 := t1Step2Coefficient_product_certificate_24 s
  have h25 := t1Step2Coefficient_product_certificate_25 s
  have h26 := t1Step2Coefficient_product_certificate_26 s
  simp only [t1Step2, t1Step1, rawUnitNineDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient1 (s : ℚ) : ℚ :=
  s ^ 28
    - 4 * s ^ 27
    + 10 * s ^ 26
    - 18 * s ^ 25
    + 25 * s ^ 24
    - 28 * s ^ 23
    + 25 * s ^ 22
    - 18 * s ^ 21
    + 10 * s ^ 20
    - 4 * s ^ 19
    + s ^ 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 34
    + 7 * s ^ 33
    - 28 * s ^ 32
    + 82 * s ^ 31
    - 194 * s ^ 30
    + 394 * s ^ 29
    - 702 * s ^ 28
    + 1070 * s ^ 27
    - 1389 * s ^ 26
    + 1494 * s ^ 25
    - 1280 * s ^ 24
    + 785 * s ^ 23
    - 179 * s ^ 22
    - 292 * s ^ 21
    + 504 * s ^ 20
    - 464 * s ^ 19
    + 298 * s ^ 18
    - 139 * s ^ 17
    + 42 * s ^ 16
    - 9 * s ^ 15
    + s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 35
    + 13 * s ^ 34
    - 18 * s ^ 33
    - 74 * s ^ 32
    + 506 * s ^ 31
    - 1717 * s ^ 30
    + 4364 * s ^ 29
    - 9471 * s ^ 28
    + 18274 * s ^ 27
    - 31029 * s ^ 26
    + 46292 * s ^ 25
    - 60050 * s ^ 24
    + 67312 * s ^ 23
    - 64632 * s ^ 22
    + 52158 * s ^ 21
    - 34535 * s ^ 20
    + 17538 * s ^ 19
    - 5648 * s ^ 18
    - 112 * s ^ 17
    + 1543 * s ^ 16
    - 1046 * s ^ 15
    + 435 * s ^ 14
    - 120 * s ^ 13
    + 21 * s ^ 12
    - 2 * s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient4 (s : ℚ) : ℚ :=
  -14 * s ^ 35
    + 194 * s ^ 34
    - 1087 * s ^ 33
    + 3612 * s ^ 32
    - 8888 * s ^ 31
    + 18136 * s ^ 30
    - 33347 * s ^ 29
    + 56889 * s ^ 28
    - 84785 * s ^ 27
    + 98826 * s ^ 26
    - 70324 * s ^ 25
    - 29882 * s ^ 24
    + 203822 * s ^ 23
    - 414316 * s ^ 22
    + 592814 * s ^ 21
    - 670303 * s ^ 20
    + 623771 * s ^ 19
    - 480388 * s ^ 18
    + 304064 * s ^ 17
    - 154817 * s ^ 16
    + 60383 * s ^ 15
    - 17070 * s ^ 14
    + 2696 * s ^ 13
    + 208 * s ^ 12
    - 261 * s ^ 11
    + 78 * s ^ 10
    - 12 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient5 (s : ℚ) : ℚ :=
  2 * s ^ 37
    - 36 * s ^ 36
    + 282 * s ^ 35
    - 1074 * s ^ 34
    + 1368 * s ^ 33
    + 4362 * s ^ 32
    - 26218 * s ^ 31
    + 77755 * s ^ 30
    - 181918 * s ^ 29
    + 402497 * s ^ 28
    - 881170 * s ^ 27
    + 1794404 * s ^ 26
    - 3224424 * s ^ 25
    + 5027687 * s ^ 24
    - 6737444 * s ^ 23
    + 7722192 * s ^ 22
    - 7471014 * s ^ 21
    + 5923971 * s ^ 20
    - 3593186 * s ^ 19
    + 1256368 * s ^ 18
    + 394992 * s ^ 17
    - 1109664 * s ^ 16
    + 1084990 * s ^ 15
    - 722044 * s ^ 14
    + 367448 * s ^ 13
    - 146930 * s ^ 12
    + 46390 * s ^ 11
    - 11489 * s ^ 10
    + 2190 * s ^ 9
    - 317 * s ^ 8
    + 32 * s ^ 7
    - 2 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient6 (s : ℚ) : ℚ :=
  s ^ 38
    - 11 * s ^ 37
    - 15 * s ^ 36
    + 992 * s ^ 35
    - 8318 * s ^ 34
    + 37355 * s ^ 33
    - 109686 * s ^ 32
    + 249482 * s ^ 31
    - 538691 * s ^ 30
    + 1248431 * s ^ 29
    - 2944945 * s ^ 28
    + 6241364 * s ^ 27
    - 11086984 * s ^ 26
    + 16161939 * s ^ 25
    - 18826192 * s ^ 24
    + 15892339 * s ^ 23
    - 5557692 * s ^ 22
    - 11041097 * s ^ 21
    + 29338776 * s ^ 20
    - 43180161 * s ^ 19
    + 48100585 * s ^ 18
    - 43280884 * s ^ 17
    + 31988238 * s ^ 16
    - 19283237 * s ^ 15
    + 9227917 * s ^ 14
    - 3328629 * s ^ 13
    + 739659 * s ^ 12
    + 34570 * s ^ 11
    - 124321 * s ^ 10
    + 68112 * s ^ 9
    - 24192 * s ^ 8
    + 6410 * s ^ 7
    - 1289 * s ^ 6
    + 192 * s ^ 5
    - 19 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient7 (s : ℚ) : ℚ :=
  7 * s ^ 38
    - 150 * s ^ 37
    + 1407 * s ^ 36
    - 7350 * s ^ 35
    + 21778 * s ^ 34
    - 29336 * s ^ 33
    - 8592 * s ^ 32
    + 5352 * s ^ 31
    + 530896 * s ^ 30
    - 2383558 * s ^ 29
    + 5406168 * s ^ 28
    - 6086866 * s ^ 27
    - 4021980 * s ^ 26
    + 36635852 * s ^ 25
    - 102099965 * s ^ 24
    + 202055736 * s ^ 23
    - 322156229 * s ^ 22
    + 432366262 * s ^ 21
    - 496007565 * s ^ 20
    + 487695638 * s ^ 19
    - 407568745 * s ^ 18
    + 281768404 * s ^ 17
    - 151451506 * s ^ 16
    + 51495078 * s ^ 15
    + 3818860 * s ^ 14
    - 21616596 * s ^ 13
    + 19449218 * s ^ 12
    - 11703772 * s ^ 11
    + 5422992 * s ^ 10
    - 2015744 * s ^ 9
    + 607621 * s ^ 8
    - 147894 * s ^ 7
    + 28202 * s ^ 6
    - 3958 * s ^ 5
    + 346 * s ^ 4
    - 10 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient8 (s : ℚ) : ℚ :=
  2 * s ^ 39
    - 32 * s ^ 38
    + 121 * s ^ 37
    + 1167 * s ^ 36
    - 16073 * s ^ 35
    + 88819 * s ^ 34
    - 274744 * s ^ 33
    + 462558 * s ^ 32
    - 349436 * s ^ 31
    + 969192 * s ^ 30
    - 9063498 * s ^ 29
    + 42901493 * s ^ 28
    - 134361202 * s ^ 27
    + 320595819 * s ^ 26
    - 626412253 * s ^ 25
    + 1042571872 * s ^ 24
    - 1503406431 * s ^ 23
    + 1883295386 * s ^ 22
    - 2032461065 * s ^ 21
    + 1842624110 * s ^ 20
    - 1317882455 * s ^ 19
    + 591732458 * s ^ 18
    + 121848553 * s ^ 17
    - 620007122 * s ^ 16
    + 810143902 * s ^ 15
    - 735846306 * s ^ 14
    + 526818901 * s ^ 13
    - 310623496 * s ^ 12
    + 153206088 * s ^ 11
    - 63525177 * s ^ 10
    + 22089134 * s ^ 9
    - 6377718 * s ^ 8
    + 1497281 * s ^ 7
    - 272076 * s ^ 6
    + 34379 * s ^ 5
    - 2048 * s ^ 4
    - 132 * s ^ 3
    + 29 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient9 (s : ℚ) : ℚ :=
  6 * s ^ 39
    - 156 * s ^ 38
    + 1732 * s ^ 37
    - 10502 * s ^ 36
    + 35150 * s ^ 35
    - 48038 * s ^ 34
    - 16926 * s ^ 33
    - 602562 * s ^ 32
    + 7407458 * s ^ 31
    - 38817820 * s ^ 30
    + 134021656 * s ^ 29
    - 350552180 * s ^ 28
    + 743085240 * s ^ 27
    - 1325029695 * s ^ 26
    + 2025292292 * s ^ 25
    - 2642566721 * s ^ 24
    + 2824231194 * s ^ 23
    - 2148318185 * s ^ 22
    + 323964706 * s ^ 21
    + 2577666169 * s ^ 20
    - 6000709368 * s ^ 19
    + 9042628051 * s ^ 18
    - 10796463740 * s ^ 17
    + 10769329375 * s ^ 16
    - 9148939400 * s ^ 15
    + 6665667035 * s ^ 14
    - 4179200724 * s ^ 13
    + 2259723759 * s ^ 12
    - 1050978326 * s ^ 11
    + 418146491 * s ^ 10
    - 140849032 * s ^ 9
    + 39428577 * s ^ 8
    - 8847350 * s ^ 7
    + 1460129 * s ^ 6
    - 135792 * s ^ 5
    - 5763 * s ^ 4
    + 3664 * s ^ 3
    - 404 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient10 (s : ℚ) : ℚ :=
  s ^ 40
    - 20 * s ^ 39
    + 122 * s ^ 38
    + 272 * s ^ 37
    - 6852 * s ^ 36
    + 19547 * s ^ 35
    + 220655 * s ^ 34
    - 2648191 * s ^ 33
    + 15012140 * s ^ 32
    - 56833051 * s ^ 31
    + 158654841 * s ^ 30
    - 341645153 * s ^ 29
    + 573085083 * s ^ 28
    - 703885555 * s ^ 27
    + 395779838 * s ^ 26
    + 961023169 * s ^ 25
    - 4301939102 * s ^ 24
    + 10728437443 * s ^ 23
    - 20978461182 * s ^ 22
    + 34711669113 * s ^ 21
    - 50010741664 * s ^ 20
    + 63535064257 * s ^ 19
    - 71540684407 * s ^ 18
    + 71392888028 * s ^ 17
    - 62961034241 * s ^ 16
    + 48894988333 * s ^ 15
    - 33316870976 * s ^ 14
    + 19869584809 * s ^ 13
    - 10341487722 * s ^ 12
    + 4665681353 * s ^ 11
    - 1806610114 * s ^ 10
    + 590240742 * s ^ 9
    - 157645212 * s ^ 8
    + 32057251 * s ^ 7
    - 3930775 * s ^ 6
    - 133053 * s ^ 5
    + 186577 * s ^ 4
    - 39902 * s ^ 3
    + 3598 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient11 (s : ℚ) : ℚ :=
  s ^ 40
    - 24 * s ^ 39
    + 121 * s ^ 38
    + 2324 * s ^ 37
    - 45984 * s ^ 36
    + 407300 * s ^ 35
    - 2267634 * s ^ 34
    + 8495942 * s ^ 33
    - 20430915 * s ^ 32
    + 19283696 * s ^ 31
    + 81593106 * s ^ 30
    - 517556870 * s ^ 29
    + 1788731372 * s ^ 28
    - 4834738624 * s ^ 27
    + 11282003953 * s ^ 26
    - 23652391450 * s ^ 25
    + 45142282657 * s ^ 24
    - 78469591898 * s ^ 23
    + 123912918685 * s ^ 22
    - 177454241040 * s ^ 21
    + 230134507693 * s ^ 20
    - 269660004478 * s ^ 19
    + 284439561748 * s ^ 18
    - 268700695388 * s ^ 17
    + 226107887756 * s ^ 16
    - 168684281932 * s ^ 15
    + 111120837229 * s ^ 14
    - 64420709172 * s ^ 13
    + 32691469040 * s ^ 12
    - 14369156516 * s ^ 11
    + 5381345219 * s ^ 10
    - 1664618478 * s ^ 9
    + 396472026 * s ^ 8
    - 57128574 * s ^ 7
    - 3718555 * s ^ 6
    + 5151968 * s ^ 5
    - 1630192 * s ^ 4
    + 278886 * s ^ 3
    - 22998 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient12 (s : ℚ) : ℚ :=
  3 * s ^ 40
    - 101 * s ^ 39
    + 1499 * s ^ 38
    - 12135 * s ^ 37
    + 46989 * s ^ 36
    + 93650 * s ^ 35
    - 2594754 * s ^ 34
    + 19582593 * s ^ 33
    - 97296996 * s ^ 32
    + 370239245 * s ^ 31
    - 1163081936 * s ^ 30
    + 3185687815 * s ^ 29
    - 7920973092 * s ^ 28
    + 18278363578 * s ^ 27
    - 39321034471 * s ^ 26
    + 78386131624 * s ^ 25
    - 143576362190 * s ^ 24
    + 240181293379 * s ^ 23
    - 366010618028 * s ^ 22
    + 507491854397 * s ^ 21
    - 638973966488 * s ^ 20
    + 728001183033 * s ^ 19
    - 746887414080 * s ^ 18
    + 686241171556 * s ^ 17
    - 561928992323 * s ^ 16
    + 408432429522 * s ^ 15
    - 262535277797 * s ^ 14
    + 148545702967 * s ^ 13
    - 73267699932 * s ^ 12
    + 30911652460 * s ^ 11
    - 10777959856 * s ^ 10
    + 2853289669 * s ^ 9
    - 405326330 * s ^ 8
    - 93083290 * s ^ 7
    + 91368412 * s ^ 6
    - 36178299 * s ^ 5
    + 9091555 * s ^ 4
    - 1424096 * s ^ 3
    + 112247 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient13 (s : ℚ) : ℚ :=
  5 * s ^ 40
    - 208 * s ^ 39
    + 4083 * s ^ 38
    - 50200 * s ^ 37
    + 433642 * s ^ 36
    - 2807196 * s ^ 35
    + 14250221 * s ^ 34
    - 59046588 * s ^ 33
    + 208489588 * s ^ 32
    - 657915770 * s ^ 31
    + 1935291123 * s ^ 30
    - 5410681816 * s ^ 29
    + 14273293062 * s ^ 28
    - 34868577186 * s ^ 27
    + 77725187787 * s ^ 26
    - 157036994280 * s ^ 25
    + 287371969699 * s ^ 24
    - 477320092432 * s ^ 23
    + 720977994711 * s ^ 22
    - 989872971266 * s ^ 21
    + 1231540371399 * s ^ 20
    - 1381900520728 * s ^ 19
    + 1391096226897 * s ^ 18
    - 1250229192514 * s ^ 17
    + 999365100642 * s ^ 16
    - 707988721042 * s ^ 15
    + 442334791415 * s ^ 14
    - 241317736240 * s ^ 13
    + 112369118294 * s ^ 12
    - 42501149986 * s ^ 11
    + 11389272020 * s ^ 10
    - 724095634 * s ^ 9
    - 1438405330 * s ^ 8
    + 1097390244 * s ^ 7
    - 500303137 * s ^ 6
    + 162379956 * s ^ 5
    - 37511979 * s ^ 4
    + 5643068 * s ^ 3
    - 434302 * s ^ 2
    - 22 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient14 (s : ℚ) : ℚ :=
  s ^ 41
    - 38 * s ^ 40
    + 687 * s ^ 39
    - 7817 * s ^ 38
    + 62736 * s ^ 37
    - 380967 * s ^ 36
    + 1870781 * s ^ 35
    - 8087092 * s ^ 34
    + 33779274 * s ^ 33
    - 142026542 * s ^ 32
    + 577677682 * s ^ 31
    - 2137823953 * s ^ 30
    + 6957004121 * s ^ 29
    - 19780003425 * s ^ 28
    + 49510946854 * s ^ 27
    - 110401882390 * s ^ 26
    + 221702913962 * s ^ 25
    - 404055124820 * s ^ 24
    + 670665247059 * s ^ 23
    - 1012799262017 * s ^ 22
    + 1385410044432 * s ^ 21
    - 1706752371779 * s ^ 20
    + 1883064744439 * s ^ 19
    - 1851820931058 * s ^ 18
    + 1617259604849 * s ^ 17
    - 1249943891762 * s ^ 16
    + 849732599426 * s ^ 15
    - 501109655743 * s ^ 14
    + 247668541277 * s ^ 13
    - 93148473703 * s ^ 12
    + 17041741872 * s ^ 11
    + 9893737648 * s ^ 10
    - 13280908999 * s ^ 9
    + 9078714474 * s ^ 8
    - 4577872578 * s ^ 7
    + 1799978758 * s ^ 6
    - 545522842 * s ^ 5
    + 121605842 * s ^ 4
    - 17953214 * s ^ 3
    + 1364336 * s ^ 2
    + 229 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient15 (s : ℚ) : ℚ :=
  -3 * s ^ 40
    + 96 * s ^ 39
    - 1371 * s ^ 38
    + 10576 * s ^ 37
    - 32243 * s ^ 36
    - 241150 * s ^ 35
    + 4033531 * s ^ 34
    - 31038318 * s ^ 33
    + 167982362 * s ^ 32
    - 712417780 * s ^ 31
    + 2500268353 * s ^ 30
    - 7541080114 * s ^ 29
    + 20127520021 * s ^ 28
    - 48553820236 * s ^ 27
    + 107125227162 * s ^ 26
    - 216871419910 * s ^ 25
    + 401569762221 * s ^ 24
    - 675299898288 * s ^ 23
    + 1022786550030 * s ^ 22
    - 1384817918744 * s ^ 21
    + 1666717496590 * s ^ 20
    - 1775567428952 * s ^ 19
    + 1667970996905 * s ^ 18
    - 1374783914196 * s ^ 17
    + 982881873352 * s ^ 16
    - 590854182144 * s ^ 15
    + 271540472545 * s ^ 14
    - 57443306918 * s ^ 13
    - 53777620499 * s ^ 12
    + 87048891800 * s ^ 11
    - 76687363176 * s ^ 10
    + 51724645762 * s ^ 9
    - 28615886792 * s ^ 8
    + 13139445284 * s ^ 7
    - 4926283989 * s ^ 6
    + 1455026000 * s ^ 5
    - 319629209 * s ^ 4
    + 46816506 * s ^ 3
    - 3533566 * s ^ 2
    - 1498 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient16 (s : ℚ) : ℚ :=
  -2 * s ^ 40
    + 85 * s ^ 39
    - 1716 * s ^ 38
    + 21933 * s ^ 37
    - 199363 * s ^ 36
    + 1373615 * s ^ 35
    - 7488371 * s ^ 34
    + 33474392 * s ^ 33
    - 127290538 * s ^ 32
    + 429291074 * s ^ 31
    - 1339078492 * s ^ 30
    + 3969865245 * s ^ 29
    - 11190955383 * s ^ 28
    + 29416486519 * s ^ 27
    - 70470465849 * s ^ 26
    + 151274583910 * s ^ 25
    - 287870453058 * s ^ 24
    + 482257364565 * s ^ 23
    - 707885935014 * s ^ 22
    + 907143695124 * s ^ 21
    - 1010381982853 * s ^ 20
    + 969803551272 * s ^ 19
    - 786256582835 * s ^ 18
    + 507952675455 * s ^ 17
    - 203819302510 * s ^ 16
    - 63914879928 * s ^ 15
    + 253267682216 * s ^ 14
    - 346124696725 * s ^ 13
    + 348341856497 * s ^ 12
    - 287851139437 * s ^ 11
    + 202947997025 * s ^ 10
    - 123907426898 * s ^ 9
    + 65316838968 * s ^ 8
    - 29257764656 * s ^ 7
    + 10820108534 * s ^ 6
    - 3170901685 * s ^ 5
    + 693382674 * s ^ 4
    - 101326421 * s ^ 3
    + 7615734 * s ^ 2
    + 6897 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient17 (s : ℚ) : ℚ :=
  4 * s ^ 39
    - 150 * s ^ 38
    + 2670 * s ^ 37
    - 29673 * s ^ 36
    + 226810 * s ^ 35
    - 1224397 * s ^ 34
    + 4437292 * s ^ 33
    - 7386876 * s ^ 32
    - 29250574 * s ^ 31
    + 309337944 * s ^ 30
    - 1540306502 * s ^ 29
    + 5563628695 * s ^ 28
    - 16074063868 * s ^ 27
    + 38617302942 * s ^ 26
    - 78439059308 * s ^ 25
    + 135236352487 * s ^ 24
    - 196764296988 * s ^ 23
    + 237142182931 * s ^ 22
    - 225020557022 * s ^ 21
    + 139187765214 * s ^ 20
    + 18564235178 * s ^ 19
    - 223703432407 * s ^ 18
    + 442033261696 * s ^ 17
    - 641048433854 * s ^ 16
    + 790186412766 * s ^ 15
    - 860518972122 * s ^ 14
    + 834228542882 * s ^ 13
    - 718633768424 * s ^ 12
    + 549650949512 * s ^ 11
    - 373738947376 * s ^ 10
    + 224915746214 * s ^ 9
    - 118079180682 * s ^ 8
    + 52861840628 * s ^ 7
    - 19549836340 * s ^ 6
    + 5730553670 * s ^ 5
    - 1253558307 * s ^ 4
    + 183272888 * s ^ 3
    - 13723837 * s ^ 2
    - 23716 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient18 (s : ℚ) : ℚ :=
  s ^ 39
    - 46 * s ^ 38
    + 1008 * s ^ 37
    - 14049 * s ^ 36
    + 139950 * s ^ 35
    - 1060479 * s ^ 34
    + 6351006 * s ^ 33
    - 30839681 * s ^ 32
    + 123640983 * s ^ 31
    - 414567289 * s ^ 30
    + 1171671180 * s ^ 29
    - 2791738710 * s ^ 28
    + 5524295135 * s ^ 27
    - 8617666407 * s ^ 26
    + 8743327928 * s ^ 25
    + 1590605929 * s ^ 24
    - 33744562119 * s ^ 23
    + 99282025076 * s ^ 22
    - 204468218515 * s ^ 21
    + 347089513594 * s ^ 20
    - 518502949294 * s ^ 19
    + 708935100264 * s ^ 18
    - 908126563334 * s ^ 17
    + 1096202296177 * s ^ 16
    - 1235903133884 * s ^ 15
    + 1282606187838 * s ^ 14
    - 1209541280460 * s ^ 13
    + 1028623463994 * s ^ 12
    - 787052932439 * s ^ 11
    + 540380399166 * s ^ 10
    - 329454712630 * s ^ 9
    + 175013668841 * s ^ 8
    - 79020810883 * s ^ 7
    + 29384613389 * s ^ 6
    - 8645697695 * s ^ 5
    + 1896416425 * s ^ 4
    - 277729906 * s ^ 3
    + 20696880 * s ^ 2
    + 63056 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient19 (s : ℚ) : ℚ :=
  -s ^ 38
    + 42 * s ^ 37
    - 858 * s ^ 36
    + 11320 * s ^ 35
    - 108089 * s ^ 34
    + 794758 * s ^ 33
    - 4685978 * s ^ 32
    + 22845810 * s ^ 31
    - 94554499 * s ^ 30
    + 340248562 * s ^ 29
    - 1086221830 * s ^ 28
    + 3117047414 * s ^ 27
    - 8071474052 * s ^ 26
    + 18806967100 * s ^ 25
    - 39316317786 * s ^ 24
    + 74002479356 * s ^ 23
    - 127039666331 * s ^ 22
    + 203002569640 * s ^ 21
    - 308640539478 * s ^ 20
    + 453422360910 * s ^ 19
    - 644819777526 * s ^ 18
    + 876136407332 * s ^ 17
    - 1114233626047 * s ^ 16
    + 1302517777106 * s ^ 15
    - 1383979774423 * s ^ 14
    + 1330146722446 * s ^ 13
    - 1155658693252 * s ^ 12
    + 907361568794 * s ^ 11
    - 639761384747 * s ^ 10
    + 398980351208 * s ^ 9
    - 215514840184 * s ^ 8
    + 98389188796 * s ^ 7
    - 36850218336 * s ^ 6
    + 10898405108 * s ^ 5
    - 2399867877 * s ^ 4
    + 352191066 * s ^ 3
    - 26053098 * s ^ 2
    - 132376 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient20 (s : ℚ) : ℚ :=
  s ^ 36
    - 44 * s ^ 35
    + 979 * s ^ 34
    - 14266 * s ^ 33
    + 150002 * s ^ 32
    - 1197808 * s ^ 31
    + 7498995 * s ^ 30
    - 37610150 * s ^ 29
    + 153572522 * s ^ 28
    - 518334676 * s ^ 27
    + 1474382870 * s ^ 26
    - 3641070210 * s ^ 25
    + 8154764246 * s ^ 24
    - 17397074112 * s ^ 23
    + 36457491173 * s ^ 22
    - 74778090501 * s ^ 21
    + 146361909524 * s ^ 20
    - 266321007588 * s ^ 19
    + 442226910814 * s ^ 18
    - 662872597440 * s ^ 17
    + 893220807879 * s ^ 16
    - 1082999439847 * s ^ 15
    + 1185637745497 * s ^ 14
    - 1176512113917 * s ^ 13
    + 1060127735643 * s ^ 12
    - 864067439030 * s ^ 11
    + 629284427716 * s ^ 10
    - 402038642740 * s ^ 9
    + 220754012491 * s ^ 8
    - 101861164878 * s ^ 7
    + 38432820553 * s ^ 6
    - 11433330899 * s ^ 5
    + 2529437936 * s ^ 4
    - 371963437 * s ^ 3
    + 27200631 * s ^ 2
    + 222071 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient21 (s : ℚ) : ℚ :=
  8 * s ^ 34
    - 312 * s ^ 33
    + 5775 * s ^ 32
    - 67434 * s ^ 31
    + 554398 * s ^ 30
    - 3373796 * s ^ 29
    + 15443031 * s ^ 28
    - 52154294 * s ^ 27
    + 117145882 * s ^ 26
    - 79800300 * s ^ 25
    - 689571995 * s ^ 24
    + 4028903166 * s ^ 23
    - 13916386191 * s ^ 22
    + 37167843646 * s ^ 21
    - 83074709476 * s ^ 20
    + 160893041156 * s ^ 19
    - 274881800236 * s ^ 18
    + 419107863138 * s ^ 17
    - 575758282859 * s ^ 16
    + 718314879002 * s ^ 15
    - 817928643563 * s ^ 14
    + 850801911810 * s ^ 13
    - 804617052706 * s ^ 12
    + 683898639246 * s ^ 11
    - 513842580645 * s ^ 10
    + 335241959882 * s ^ 9
    - 186623584981 * s ^ 8
    + 86928880882 * s ^ 7
    - 33045167161 * s ^ 6
    + 9897215566 * s ^ 5
    - 2201890087 * s ^ 4
    + 324378952 * s ^ 3
    - 23300234 * s ^ 2
    - 299270 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient22 (s : ℚ) : ℚ :=
  s ^ 34
    - 45 * s ^ 33
    + 970 * s ^ 32
    - 13404 * s ^ 31
    + 133644 * s ^ 30
    - 1022961 * s ^ 29
    + 6235752 * s ^ 28
    - 31017479 * s ^ 27
    + 128341223 * s ^ 26
    - 450055287 * s ^ 25
    + 1365103898 * s ^ 24
    - 3660259414 * s ^ 23
    + 8846889951 * s ^ 22
    - 19520878968 * s ^ 21
    + 39496686353 * s ^ 20
    - 73277641355 * s ^ 19
    + 124735693110 * s ^ 18
    - 195327475223 * s ^ 17
    + 282019385158 * s ^ 16
    - 375132854697 * s ^ 15
    + 457558133302 * s ^ 14
    - 507472194415 * s ^ 13
    + 505657276750 * s ^ 12
    - 446117280253 * s ^ 11
    + 343403512624 * s ^ 10
    - 227571064684 * s ^ 9
    + 128089255582 * s ^ 8
    - 60204232539 * s ^ 7
    + 23084290797 * s ^ 6
    - 6973323242 * s ^ 5
    + 1562452329 * s ^ 4
    - 230501595 * s ^ 3
    + 16100300 * s ^ 2
    + 323817 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient23 (s : ℚ) : ℚ :=
  -s ^ 32
    + 34 * s ^ 31
    - 556 * s ^ 30
    + 6136 * s ^ 29
    - 54738 * s ^ 28
    + 431364 * s ^ 27
    - 2999435 * s ^ 26
    + 17724448 * s ^ 25
    - 86809415 * s ^ 24
    + 351003670 * s ^ 23
    - 1183675436 * s ^ 22
    + 3390225758 * s ^ 21
    - 8430709568 * s ^ 20
    + 18595897760 * s ^ 19
    - 36954274759 * s ^ 18
    + 66614528826 * s ^ 17
    - 108846580687 * s ^ 16
    + 160458078028 * s ^ 15
    - 212043294270 * s ^ 14
    + 249204773034 * s ^ 13
    - 258040220218 * s ^ 12
    + 233155063638 * s ^ 11
    - 182242886607 * s ^ 10
    + 122187320128 * s ^ 9
    - 69516433555 * s ^ 8
    + 33037802060 * s ^ 7
    - 12819434194 * s ^ 6
    + 3919212480 * s ^ 5
    - 886552894 * s ^ 4
    + 130876718 * s ^ 3
    - 8738195 * s ^ 2
    - 279554 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient24 (s : ℚ) : ℚ :=
  -s ^ 31
    + 44 * s ^ 30
    - 903 * s ^ 29
    + 11537 * s ^ 28
    - 103458 * s ^ 27
    + 697876 * s ^ 26
    - 3722415 * s ^ 25
    + 16395044 * s ^ 24
    - 62123861 * s ^ 23
    + 209826084 * s ^ 22
    - 645326077 * s ^ 21
    + 1811724516 * s ^ 20
    - 4594839312 * s ^ 19
    + 10398067591 * s ^ 18
    - 20836847420 * s ^ 17
    + 36876911560 * s ^ 16
    - 57594308667 * s ^ 15
    + 79228931178 * s ^ 14
    - 95619129616 * s ^ 13
    + 100733565888 * s ^ 12
    - 92190864822 * s ^ 11
    + 72955772802 * s ^ 10
    - 49602766282 * s ^ 9
    + 28673172418 * s ^ 8
    - 13868388697 * s ^ 7
    + 5482507978 * s ^ 6
    - 1706352230 * s ^ 5
    + 391111965 * s ^ 4
    - 57674614 * s ^ 3
    + 3561823 * s ^ 2
    + 190071 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient25 (s : ℚ) : ℚ :=
  2 * s ^ 29
    - 87 * s ^ 28
    + 1792 * s ^ 27
    - 23274 * s ^ 26
    + 214160 * s ^ 25
    - 1487857 * s ^ 24
    + 8127046 * s ^ 23
    - 35925593 * s ^ 22
    + 131482546 * s ^ 21
    - 406239306 * s ^ 20
    + 1078002714 * s ^ 19
    - 2492668490 * s ^ 18
    + 5073963266 * s ^ 17
    - 9134175011 * s ^ 16
    + 14531561190 * s ^ 15
    - 20349988433 * s ^ 14
    + 24975715862 * s ^ 13
    - 26778993552 * s ^ 12
    + 25024776102 * s ^ 11
    - 20307640482 * s ^ 10
    + 14206796940 * s ^ 9
    - 8465828133 * s ^ 8
    + 4224558080 * s ^ 7
    - 1722270385 * s ^ 6
    + 550878748 * s ^ 5
    - 128591686 * s ^ 4
    + 18851672 * s ^ 3
    - 998263 * s ^ 2
    - 99568 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient26 (s : ℚ) : ℚ :=
  -s ^ 27
    + 43 * s ^ 26
    - 881 * s ^ 25
    + 11438 * s ^ 24
    - 105539 * s ^ 23
    + 735657 * s ^ 22
    - 4019895 * s ^ 21
    + 17642435 * s ^ 20
    - 63242170 * s ^ 19
    + 187474082 * s ^ 18
    - 464175631 * s ^ 17
    + 968521355 * s ^ 16
    - 1718234154 * s ^ 15
    + 2615606575 * s ^ 14
    - 3446077890 * s ^ 13
    + 3953786189 * s ^ 12
    - 3955675091 * s ^ 11
    + 3435161375 * s ^ 10
    - 2564526298 * s ^ 9
    + 1624551077 * s ^ 8
    - 858430083 * s ^ 7
    + 368593958 * s ^ 6
    - 122970207 * s ^ 5
    + 29412434 * s ^ 4
    - 4226394 * s ^ 3
    + 148838 * s ^ 2
    + 38778 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient27 (s : ℚ) : ℚ :=
  2 * s ^ 23
    - 76 * s ^ 22
    + 1358 * s ^ 21
    - 15163 * s ^ 20
    + 118570 * s ^ 19
    - 689666 * s ^ 18
    + 3093466 * s ^ 17
    - 10949557 * s ^ 16
    + 31052772 * s ^ 15
    - 71289867 * s ^ 14
    + 133450406 * s ^ 13
    - 204820592 * s ^ 12
    + 258977940 * s ^ 11
    - 270948264 * s ^ 10
    + 235260168 * s ^ 9
    - 169277872 * s ^ 8
    + 99796182 * s ^ 7
    - 46900307 * s ^ 6
    + 16704330 * s ^ 5
    - 4109566 * s ^ 4
    + 549802 * s ^ 3
    + 6506 * s ^ 2
    - 10572 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient28 (s : ℚ) : ℚ :=
  -s ^ 19
    + 33 * s ^ 18
    - 504 * s ^ 17
    + 4727 * s ^ 16
    - 30463 * s ^ 15
    + 143003 * s ^ 14
    - 505780 * s ^ 13
    + 1374946 * s ^ 12
    - 2904374 * s ^ 11
    + 4786569 * s ^ 10
    - 6142667 * s ^ 9
    + 6089081 * s ^ 8
    - 4591092 * s ^ 7
    + 2564151 * s ^ 6
    - 1009533 * s ^ 5
    + 248210 * s ^ 4
    - 21194 * s ^ 3
    - 6912 * s ^ 2
    + 1800 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient29 (s : ℚ) : ℚ :=
  s ^ 10
    - 18 * s ^ 9
    + 140 * s ^ 8
    - 616 * s ^ 7
    + 1685 * s ^ 6
    - 2962 * s ^ 5
    + 3334 * s ^ 4
    - 2308 * s ^ 3
    + 888 * s ^ 2
    - 144 * s

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t1Step3 (r s : ℚ) : ℚ :=
  t1Step3Coefficient0 s +
    t1Step3Coefficient1 s * r +
    t1Step3Coefficient2 s * r ^ 2 +
    t1Step3Coefficient3 s * r ^ 3 +
    t1Step3Coefficient4 s * r ^ 4 +
    t1Step3Coefficient5 s * r ^ 5 +
    t1Step3Coefficient6 s * r ^ 6 +
    t1Step3Coefficient7 s * r ^ 7 +
    t1Step3Coefficient8 s * r ^ 8 +
    t1Step3Coefficient9 s * r ^ 9 +
    t1Step3Coefficient10 s * r ^ 10 +
    t1Step3Coefficient11 s * r ^ 11 +
    t1Step3Coefficient12 s * r ^ 12 +
    t1Step3Coefficient13 s * r ^ 13 +
    t1Step3Coefficient14 s * r ^ 14 +
    t1Step3Coefficient15 s * r ^ 15 +
    t1Step3Coefficient16 s * r ^ 16 +
    t1Step3Coefficient17 s * r ^ 17 +
    t1Step3Coefficient18 s * r ^ 18 +
    t1Step3Coefficient19 s * r ^ 19 +
    t1Step3Coefficient20 s * r ^ 20 +
    t1Step3Coefficient21 s * r ^ 21 +
    t1Step3Coefficient22 s * r ^ 22 +
    t1Step3Coefficient23 s * r ^ 23 +
    t1Step3Coefficient24 s * r ^ 24 +
    t1Step3Coefficient25 s * r ^ 25 +
    t1Step3Coefficient26 s * r ^ 26 +
    t1Step3Coefficient27 s * r ^ 27 +
    t1Step3Coefficient28 s * r ^ 28 +
    t1Step3Coefficient29 s * r ^ 29

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_0 (s : ℚ) :
    t1Step3Coefficient0 s =
      t1Step2Coefficient0 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient0,
    t1Step2Coefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_1 (s : ℚ) :
    t1Step3Coefficient1 s =
      t1Step2Coefficient0 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient1 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient1,
    t1Step2Coefficient0,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_2 (s : ℚ) :
    t1Step3Coefficient2 s =
      t1Step2Coefficient0 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient1 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient2 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient2,
    t1Step2Coefficient0,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient1,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient2,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_3 (s : ℚ) :
    t1Step3Coefficient3 s =
      t1Step2Coefficient0 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient1 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient2 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient3 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient3,
    t1Step2Coefficient0,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient1,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient2,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient3,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_4 (s : ℚ) :
    t1Step3Coefficient4 s =
      t1Step2Coefficient1 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient2 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient3 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient4 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient4,
    t1Step2Coefficient1,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient2,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient3,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient4,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_5 (s : ℚ) :
    t1Step3Coefficient5 s =
      t1Step2Coefficient2 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient3 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient4 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient5 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient5,
    t1Step2Coefficient2,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient3,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient4,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient5,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_6 (s : ℚ) :
    t1Step3Coefficient6 s =
      t1Step2Coefficient3 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient4 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient5 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient6 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient6,
    t1Step2Coefficient3,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient4,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient5,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient6,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_7 (s : ℚ) :
    t1Step3Coefficient7 s =
      t1Step2Coefficient4 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient5 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient6 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient7 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient7,
    t1Step2Coefficient4,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient5,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient6,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient7,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_8 (s : ℚ) :
    t1Step3Coefficient8 s =
      t1Step2Coefficient5 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient6 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient7 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient8 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient8,
    t1Step2Coefficient5,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient6,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient7,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient8,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_9 (s : ℚ) :
    t1Step3Coefficient9 s =
      t1Step2Coefficient6 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient7 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient8 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient9 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient9,
    t1Step2Coefficient6,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient7,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient8,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient9,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_10 (s : ℚ) :
    t1Step3Coefficient10 s =
      t1Step2Coefficient7 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient8 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient9 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient10 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient10,
    t1Step2Coefficient7,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient8,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient9,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient10,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_11 (s : ℚ) :
    t1Step3Coefficient11 s =
      t1Step2Coefficient8 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient9 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient10 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient11 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient11,
    t1Step2Coefficient8,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient9,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient10,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient11,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_12 (s : ℚ) :
    t1Step3Coefficient12 s =
      t1Step2Coefficient9 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient10 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient11 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient12 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient12,
    t1Step2Coefficient9,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient10,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient11,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient12,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_13 (s : ℚ) :
    t1Step3Coefficient13 s =
      t1Step2Coefficient10 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient11 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient12 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient13 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient13,
    t1Step2Coefficient10,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient11,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient12,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient13,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_14 (s : ℚ) :
    t1Step3Coefficient14 s =
      t1Step2Coefficient11 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient12 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient13 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient14 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient14,
    t1Step2Coefficient11,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient12,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient13,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient14,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_15 (s : ℚ) :
    t1Step3Coefficient15 s =
      t1Step2Coefficient12 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient13 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient14 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient15 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient15,
    t1Step2Coefficient12,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient13,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient14,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient15,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_16 (s : ℚ) :
    t1Step3Coefficient16 s =
      t1Step2Coefficient13 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient14 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient15 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient16 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient16,
    t1Step2Coefficient13,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient14,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient15,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient16,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_17 (s : ℚ) :
    t1Step3Coefficient17 s =
      t1Step2Coefficient14 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient15 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient16 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient17 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient17,
    t1Step2Coefficient14,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient15,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient16,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient17,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_18 (s : ℚ) :
    t1Step3Coefficient18 s =
      t1Step2Coefficient15 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient16 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient17 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient18 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient18,
    t1Step2Coefficient15,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient16,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient17,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient18,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_19 (s : ℚ) :
    t1Step3Coefficient19 s =
      t1Step2Coefficient16 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient17 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient18 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient19 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient19,
    t1Step2Coefficient16,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient17,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient18,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient19,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_20 (s : ℚ) :
    t1Step3Coefficient20 s =
      t1Step2Coefficient17 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient18 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient19 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient20 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient20,
    t1Step2Coefficient17,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient18,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient19,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient20,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_21 (s : ℚ) :
    t1Step3Coefficient21 s =
      t1Step2Coefficient18 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient19 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient20 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient21 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient21,
    t1Step2Coefficient18,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient19,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient20,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient21,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_22 (s : ℚ) :
    t1Step3Coefficient22 s =
      t1Step2Coefficient19 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient20 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient21 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient22 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient22,
    t1Step2Coefficient19,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient20,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient21,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient22,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_23 (s : ℚ) :
    t1Step3Coefficient23 s =
      t1Step2Coefficient20 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient21 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient22 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient23 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient23,
    t1Step2Coefficient20,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient21,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient22,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient23,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_24 (s : ℚ) :
    t1Step3Coefficient24 s =
      t1Step2Coefficient21 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient22 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient23 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient24 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient24,
    t1Step2Coefficient21,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient22,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient23,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient24,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_25 (s : ℚ) :
    t1Step3Coefficient25 s =
      t1Step2Coefficient22 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient23 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient24 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient25 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient25,
    t1Step2Coefficient22,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient23,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient24,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient25,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_26 (s : ℚ) :
    t1Step3Coefficient26 s =
      t1Step2Coefficient23 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient24 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient25 s *
          rawUnitEightDenominatorCoefficient1 s +
        t1Step2Coefficient26 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t1Step3Coefficient26,
    t1Step2Coefficient23,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient24,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient25,
    rawUnitEightDenominatorCoefficient1,
    t1Step2Coefficient26,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_27 (s : ℚ) :
    t1Step3Coefficient27 s =
      t1Step2Coefficient24 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient25 s *
          rawUnitEightDenominatorCoefficient2 s +
        t1Step2Coefficient26 s *
          rawUnitEightDenominatorCoefficient1 s := by
  simp only [t1Step3Coefficient27,
    t1Step2Coefficient24,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient25,
    rawUnitEightDenominatorCoefficient2,
    t1Step2Coefficient26,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_28 (s : ℚ) :
    t1Step3Coefficient28 s =
      t1Step2Coefficient25 s *
          rawUnitEightDenominatorCoefficient3 s +
        t1Step2Coefficient26 s *
          rawUnitEightDenominatorCoefficient2 s := by
  simp only [t1Step3Coefficient28,
    t1Step2Coefficient25,
    rawUnitEightDenominatorCoefficient3,
    t1Step2Coefficient26,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t1Step3Coefficient_product_certificate_29 (s : ℚ) :
    t1Step3Coefficient29 s =
      t1Step2Coefficient26 s *
          rawUnitEightDenominatorCoefficient3 s := by
  simp only [t1Step3Coefficient29,
    t1Step2Coefficient26,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step3_eq_t1Step2_mul_rawUnitEightDenominator (r s : ℚ) :
    t1Step3 r s =
      t1Step2 r s * rawUnitEightDenominator r s := by
  have h0 := t1Step3Coefficient_product_certificate_0 s
  have h1 := t1Step3Coefficient_product_certificate_1 s
  have h2 := t1Step3Coefficient_product_certificate_2 s
  have h3 := t1Step3Coefficient_product_certificate_3 s
  have h4 := t1Step3Coefficient_product_certificate_4 s
  have h5 := t1Step3Coefficient_product_certificate_5 s
  have h6 := t1Step3Coefficient_product_certificate_6 s
  have h7 := t1Step3Coefficient_product_certificate_7 s
  have h8 := t1Step3Coefficient_product_certificate_8 s
  have h9 := t1Step3Coefficient_product_certificate_9 s
  have h10 := t1Step3Coefficient_product_certificate_10 s
  have h11 := t1Step3Coefficient_product_certificate_11 s
  have h12 := t1Step3Coefficient_product_certificate_12 s
  have h13 := t1Step3Coefficient_product_certificate_13 s
  have h14 := t1Step3Coefficient_product_certificate_14 s
  have h15 := t1Step3Coefficient_product_certificate_15 s
  have h16 := t1Step3Coefficient_product_certificate_16 s
  have h17 := t1Step3Coefficient_product_certificate_17 s
  have h18 := t1Step3Coefficient_product_certificate_18 s
  have h19 := t1Step3Coefficient_product_certificate_19 s
  have h20 := t1Step3Coefficient_product_certificate_20 s
  have h21 := t1Step3Coefficient_product_certificate_21 s
  have h22 := t1Step3Coefficient_product_certificate_22 s
  have h23 := t1Step3Coefficient_product_certificate_23 s
  have h24 := t1Step3Coefficient_product_certificate_24 s
  have h25 := t1Step3Coefficient_product_certificate_25 s
  have h26 := t1Step3Coefficient_product_certificate_26 s
  have h27 := t1Step3Coefficient_product_certificate_27 s
  have h28 := t1Step3Coefficient_product_certificate_28 s
  have h29 := t1Step3Coefficient_product_certificate_29 s
  simp only [t1Step3, t1Step2, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient1 (s : ℚ) : ℚ :=
  s ^ 36
    - 4 * s ^ 35
    + 10 * s ^ 34
    - 18 * s ^ 33
    + 25 * s ^ 32
    - 28 * s ^ 31
    + 25 * s ^ 30
    - 18 * s ^ 29
    + 10 * s ^ 28
    - 4 * s ^ 27
    + s ^ 26

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 42
    + 7 * s ^ 41
    - 28 * s ^ 40
    + 82 * s ^ 39
    - 194 * s ^ 38
    + 394 * s ^ 37
    - 699 * s ^ 36
    + 1041 * s ^ 35
    - 1281 * s ^ 34
    + 1224 * s ^ 33
    - 772 * s ^ 32
    + 23 * s ^ 31
    + 764 * s ^ 30
    - 1265 * s ^ 29
    + 1351 * s ^ 28
    - 1085 * s ^ 27
    + 680 * s ^ 26
    - 335 * s ^ 25
    + 124 * s ^ 24
    - 37 * s ^ 23
    + 8 * s ^ 22
    - s ^ 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 43
    + 10 * s ^ 42
    + 20 * s ^ 41
    - 287 * s ^ 40
    + 1305 * s ^ 39
    - 4028 * s ^ 38
    + 9909 * s ^ 37
    - 21010 * s ^ 36
    + 39399 * s ^ 35
    - 64730 * s ^ 34
    + 92898 * s ^ 33
    - 115210 * s ^ 32
    + 122231 * s ^ 31
    - 109039 * s ^ 30
    + 78596 * s ^ 29
    - 41851 * s ^ 28
    + 10470 * s ^ 27
    + 8096 * s ^ 26
    - 13769 * s ^ 25
    + 11552 * s ^ 24
    - 6858 * s ^ 23
    + 3213 * s ^ 22
    - 1201 * s ^ 21
    + 352 * s ^ 20
    - 77 * s ^ 19
    + 12 * s ^ 18
    - s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 45
    + 13 * s ^ 44
    - 111 * s ^ 43
    + 714 * s ^ 42
    - 3066 * s ^ 41
    + 8938 * s ^ 40
    - 19301 * s ^ 39
    + 32007 * s ^ 38
    - 39686 * s ^ 37
    + 25404 * s ^ 36
    + 50472 * s ^ 35
    - 256066 * s ^ 34
    + 657542 * s ^ 33
    - 1274290 * s ^ 32
    + 2016428 * s ^ 31
    - 2688794 * s ^ 30
    + 3062632 * s ^ 29
    - 2988040 * s ^ 28
    + 2496007 * s ^ 27
    - 1765520 * s ^ 26
    + 1035997 * s ^ 25
    - 482866 * s ^ 24
    + 158341 * s ^ 23
    - 19009 * s ^ 22
    - 18948 * s ^ 21
    + 17831 * s ^ 20
    - 9293 * s ^ 19
    + 3462 * s ^ 18
    - 970 * s ^ 17
    + 198 * s ^ 16
    - 27 * s ^ 15
    + 2 * s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient5 (s : ℚ) : ℚ :=
  -2 * s ^ 46
    + 27 * s ^ 45
    - 172 * s ^ 44
    + 624 * s ^ 43
    - 294 * s ^ 42
    - 10768 * s ^ 41
    + 66827 * s ^ 40
    - 237976 * s ^ 39
    + 636202 * s ^ 38
    - 1425752 * s ^ 37
    + 2859846 * s ^ 36
    - 5263751 * s ^ 35
    + 8757105 * s ^ 34
    - 12814293 * s ^ 33
    + 16078011 * s ^ 32
    - 16590002 * s ^ 31
    + 12829644 * s ^ 30
    - 4768944 * s ^ 29
    - 5635532 * s ^ 28
    + 15087832 * s ^ 27
    - 20717168 * s ^ 26
    + 21325505 * s ^ 25
    - 17849422 * s ^ 24
    + 12485644 * s ^ 23
    - 7357178 * s ^ 22
    + 3668895 * s ^ 21
    - 1531659 * s ^ 20
    + 520070 * s ^ 19
    - 134190 * s ^ 18
    + 21362 * s ^ 17
    + 776 * s ^ 16
    - 1772 * s ^ 15
    + 615 * s ^ 14
    - 124 * s ^ 13
    + 15 * s ^ 12
    - s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient6 (s : ℚ) : ℚ :=
  -13 * s ^ 46
    + 277 * s ^ 45
    - 2746 * s ^ 44
    + 17610 * s ^ 43
    - 81415 * s ^ 42
    + 277086 * s ^ 41
    - 700706 * s ^ 40
    + 1367406 * s ^ 39
    - 2198751 * s ^ 38
    + 3083339 * s ^ 37
    - 3609548 * s ^ 36
    + 1617021 * s ^ 35
    + 8937704 * s ^ 34
    - 37725010 * s ^ 33
    + 93751738 * s ^ 32
    - 178444127 * s ^ 31
    + 278728953 * s ^ 30
    - 368032639 * s ^ 29
    + 415573418 * s ^ 28
    - 401723115 * s ^ 27
    + 329781994 * s ^ 26
    - 223736590 * s ^ 25
    + 117035545 * s ^ 24
    - 36079377 * s ^ 23
    - 9268343 * s ^ 22
    + 24523400 * s ^ 21
    - 22707894 * s ^ 20
    + 15107123 * s ^ 19
    - 8051129 * s ^ 18
    + 3546762 * s ^ 17
    - 1303247 * s ^ 16
    + 397504 * s ^ 15
    - 99508 * s ^ 14
    + 20141 * s ^ 13
    - 3232 * s ^ 12
    + 403 * s ^ 11
    - 36 * s ^ 10
    + 2 * s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 48
    - 48 * s ^ 47
    + 550 * s ^ 46
    - 3794 * s ^ 45
    + 16701 * s ^ 44
    - 42465 * s ^ 43
    + 720 * s ^ 42
    + 546569 * s ^ 41
    - 2820029 * s ^ 40
    + 8942825 * s ^ 39
    - 22041303 * s ^ 38
    + 48686386 * s ^ 37
    - 105478102 * s ^ 36
    + 225804981 * s ^ 35
    - 452386670 * s ^ 34
    + 806509738 * s ^ 33
    - 1250104745 * s ^ 32
    + 1665048460 * s ^ 31
    - 1873285246 * s ^ 30
    + 1714155203 * s ^ 29
    - 1135686648 * s ^ 28
    + 253917535 * s ^ 27
    + 679366753 * s ^ 26
    - 1392466833 * s ^ 25
    + 1710474871 * s ^ 24
    - 1627742773 * s ^ 23
    + 1279144842 * s ^ 22
    - 848891613 * s ^ 21
    + 479526486 * s ^ 20
    - 228494015 * s ^ 19
    + 88963177 * s ^ 18
    - 25902482 * s ^ 17
    + 3804074 * s ^ 16
    + 1293498 * s ^ 15
    - 1315284 * s ^ 14
    + 626224 * s ^ 13
    - 214447 * s ^ 12
    + 57316 * s ^ 11
    - 12226 * s ^ 10
    + 2050 * s ^ 9
    - 259 * s ^ 8
    + 22 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient8 (s : ℚ) : ℚ :=
  s ^ 49
    - 17 * s ^ 48
    + 70 * s ^ 47
    + 880 * s ^ 46
    - 15389 * s ^ 45
    + 122541 * s ^ 44
    - 651052 * s ^ 43
    + 2550530 * s ^ 42
    - 7672597 * s ^ 41
    + 18441545 * s ^ 40
    - 38962549 * s ^ 39
    + 84818431 * s ^ 38
    - 202737581 * s ^ 37
    + 475608415 * s ^ 36
    - 967336627 * s ^ 35
    + 1588208443 * s ^ 34
    - 1964757073 * s ^ 33
    + 1447850563 * s ^ 32
    + 688494171 * s ^ 31
    - 4865815400 * s ^ 30
    + 10779630857 * s ^ 29
    - 17255014298 * s ^ 28
    + 22533517039 * s ^ 27
    - 25002561971 * s ^ 26
    + 23935835605 * s ^ 25
    - 19799677869 * s ^ 24
    + 14035532013 * s ^ 23
    - 8334372350 * s ^ 22
    + 3919651161 * s ^ 21
    - 1202512577 * s ^ 20
    - 82139504 * s ^ 19
    + 460892073 * s ^ 18
    - 417531047 * s ^ 17
    + 261157455 * s ^ 16
    - 129697108 * s ^ 15
    + 53160151 * s ^ 14
    - 18181447 * s ^ 13
    + 5180689 * s ^ 12
    - 1215100 * s ^ 11
    + 228187 * s ^ 10
    - 31997 * s ^ 9
    + 2769 * s ^ 8
    - 9 * s ^ 7
    - 30 * s ^ 6
    + 3 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient9 (s : ℚ) : ℚ :=
  7 * s ^ 49
    - 194 * s ^ 48
    + 2497 * s ^ 47
    - 19688 * s ^ 46
    + 104495 * s ^ 45
    - 379123 * s ^ 44
    + 860427 * s ^ 43
    - 586438 * s ^ 42
    - 3609911 * s ^ 41
    + 13558889 * s ^ 40
    - 12364057 * s ^ 39
    - 50547394 * s ^ 38
    + 187991984 * s ^ 37
    - 114532863 * s ^ 36
    - 1160155514 * s ^ 35
    + 5568132495 * s ^ 34
    - 15605445136 * s ^ 33
    + 33270596501 * s ^ 32
    - 58655268838 * s ^ 31
    + 88648722809 * s ^ 30
    - 116701402926 * s ^ 29
    + 134495409226 * s ^ 28
    - 135140927006 * s ^ 27
    + 116620437227 * s ^ 26
    - 83160299347 * s ^ 25
    + 43767145401 * s ^ 24
    - 8648259013 * s ^ 23
    - 15083049155 * s ^ 22
    + 25607300762 * s ^ 21
    - 25751542677 * s ^ 20
    + 20319705837 * s ^ 19
    - 13470883183 * s ^ 18
    + 7679507043 * s ^ 17
    - 3790606490 * s ^ 16
    + 1618449083 * s ^ 15
    - 593243109 * s ^ 14
    + 184227187 * s ^ 13
    - 47400888 * s ^ 12
    + 9678842 * s ^ 11
    - 1408017 * s ^ 10
    + 86052 * s ^ 9
    + 20349 * s ^ 8
    - 7034 * s ^ 7
    + 933 * s ^ 6
    - 42 * s ^ 5
    - 3 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient10 (s : ℚ) : ℚ :=
  2 * s ^ 50
    - 44 * s ^ 49
    + 342 * s ^ 48
    + 29 * s ^ 47
    - 23678 * s ^ 46
    + 243989 * s ^ 45
    - 1451873 * s ^ 44
    + 5937289 * s ^ 43
    - 17320263 * s ^ 42
    + 35731604 * s ^ 41
    - 56751821 * s ^ 40
    + 146202483 * s ^ 39
    - 768186844 * s ^ 38
    + 3488512633 * s ^ 37
    - 11733703889 * s ^ 36
    + 30733046074 * s ^ 35
    - 65787198184 * s ^ 34
    + 119002227348 * s ^ 33
    - 185833031035 * s ^ 32
    + 252648827797 * s ^ 31
    - 296901051619 * s ^ 30
    + 292658825653 * s ^ 29
    - 221367483047 * s ^ 28
    + 83104312388 * s ^ 27
    + 98102027494 * s ^ 26
    - 280290803751 * s ^ 25
    + 418215949392 * s ^ 24
    - 480993246722 * s ^ 23
    + 464418906376 * s ^ 22
    - 389114377647 * s ^ 21
    + 287673351778 * s ^ 20
    - 189209036734 * s ^ 19
    + 110767439042 * s ^ 18
    - 57456472746 * s ^ 17
    + 26187952049 * s ^ 16
    - 10357896036 * s ^ 15
    + 3484544744 * s ^ 14
    - 964106893 * s ^ 13
    + 204258811 * s ^ 12
    - 26043780 * s ^ 11
    - 1590657 * s ^ 10
    + 1980071 * s ^ 9
    - 593177 * s ^ 8
    + 101531 * s ^ 7
    - 8381 * s ^ 6
    - 185 * s ^ 5
    + 86 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient11 (s : ℚ) : ℚ :=
  6 * s ^ 50
    - 196 * s ^ 49
    + 2880 * s ^ 48
    - 25187 * s ^ 47
    + 144036 * s ^ 46
    - 544226 * s ^ 45
    + 1242498 * s ^ 44
    - 1268629 * s ^ 43
    + 3928123 * s ^ 42
    - 69309814 * s ^ 41
    + 541383839 * s ^ 40
    - 2643302096 * s ^ 39
    + 9378282315 * s ^ 38
    - 25861419572 * s ^ 37
    + 57533107641 * s ^ 36
    - 105463786981 * s ^ 35
    + 160036096601 * s ^ 34
    - 195786403831 * s ^ 33
    + 169311297676 * s ^ 32
    - 21735369813 * s ^ 31
    - 307922036207 * s ^ 30
    + 853972839497 * s ^ 29
    - 1591163329266 * s ^ 28
    + 2417809360711 * s ^ 27
    - 3170915355898 * s ^ 26
    + 3675037321060 * s ^ 25
    - 3804838018367 * s ^ 24
    + 3537823490771 * s ^ 23
    - 2964807145395 * s ^ 22
    + 2244737845201 * s ^ 21
    - 1537006317621 * s ^ 20
    + 949297592082 * s ^ 19
    - 524700324017 * s ^ 18
    + 256421093489 * s ^ 17
    - 108890691519 * s ^ 16
    + 39080087615 * s ^ 15
    - 11219662286 * s ^ 14
    + 2217703160 * s ^ 13
    - 79946100 * s ^ 12
    - 161337783 * s ^ 11
    + 83826335 * s ^ 10
    - 25717602 * s ^ 9
    + 5295009 * s ^ 8
    - 646790 * s ^ 7
    + 10107 * s ^ 6
    + 9690 * s ^ 5
    - 1110 * s ^ 4
    - 36 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient12 (s : ℚ) : ℚ :=
  s ^ 51
    - 26 * s ^ 50
    + 251 * s ^ 49
    - 560 * s ^ 48
    - 10105 * s ^ 47
    + 104517 * s ^ 46
    - 310895 * s ^ 45
    - 2198384 * s ^ 44
    + 32393530 * s ^ 43
    - 218173793 * s ^ 42
    + 1014463329 * s ^ 41
    - 3562835491 * s ^ 40
    + 9669206330 * s ^ 39
    - 19926736115 * s ^ 38
    + 28234284486 * s ^ 37
    - 12907542381 * s ^ 36
    - 72552448101 * s ^ 35
    + 305943902128 * s ^ 34
    - 799528223527 * s ^ 33
    + 1697223825873 * s ^ 32
    - 3150049298412 * s ^ 31
    + 5248831646300 * s ^ 30
    - 7929761864956 * s ^ 29
    + 10909926400718 * s ^ 28
    - 13701719517430 * s ^ 27
    + 15724162456088 * s ^ 26
    - 16486444845777 * s ^ 25
    + 15776130391300 * s ^ 24
    - 13767027532190 * s ^ 23
    + 10953051033828 * s ^ 22
    - 7936931730420 * s ^ 21
    + 5218861320555 * s ^ 20
    - 3084618441912 * s ^ 19
    + 1611611615607 * s ^ 18
    - 725880957349 * s ^ 17
    + 269604275575 * s ^ 16
    - 74023604801 * s ^ 15
    + 8577865507 * s ^ 14
    + 5231952714 * s ^ 13
    - 4444136493 * s ^ 12
    + 2015811592 * s ^ 11
    - 656887154 * s ^ 10
    + 157593225 * s ^ 9
    - 24912887 * s ^ 8
    + 1304886 * s ^ 7
    + 470265 * s ^ 6
    - 118089 * s ^ 5
    + 8015 * s ^ 4
    + 628 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient13 (s : ℚ) : ℚ :=
  s ^ 51
    - 32 * s ^ 50
    + 335 * s ^ 49
    + 587 * s ^ 48
    - 54944 * s ^ 47
    + 739355 * s ^ 46
    - 5960302 * s ^ 45
    + 33807568 * s ^ 44
    - 140326323 * s ^ 43
    + 409628871 * s ^ 42
    - 627347004 * s ^ 41
    - 1235194090 * s ^ 40
    + 13323515616 * s ^ 39
    - 58317297884 * s ^ 38
    + 185155454818 * s ^ 37
    - 481907865331 * s ^ 36
    + 1091209232453 * s ^ 35
    - 2232552717113 * s ^ 34
    + 4222049677339 * s ^ 33
    - 7447429342539 * s ^ 32
    + 12240814177542 * s ^ 31
    - 18655267997223 * s ^ 30
    + 26260152275379 * s ^ 29
    - 34079761339841 * s ^ 28
    + 40728732729188 * s ^ 27
    - 44756601392145 * s ^ 26
    + 45133705534214 * s ^ 25
    - 41689867922969 * s ^ 24
    + 35235769711318 * s ^ 23
    - 27207942111261 * s ^ 22
    + 19098925601315 * s ^ 21
    - 12042842546046 * s ^ 20
    + 6662032227288 * s ^ 19
    - 3099713569148 * s ^ 18
    + 1107716911651 * s ^ 17
    - 209660847887 * s ^ 16
    - 78890471588 * s ^ 15
    + 108134933975 * s ^ 14
    - 67614173538 * s ^ 13
    + 30528340156 * s ^ 12
    - 10726046276 * s ^ 11
    + 2914738559 * s ^ 10
    - 558158551 * s ^ 9
    + 45576878 * s ^ 8
    + 12490550 * s ^ 7
    - 5423530 * s ^ 6
    + 835520 * s ^ 5
    - 27838 * s ^ 4
    - 7073 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient14 (s : ℚ) : ℚ :=
  3 * s ^ 51
    - 121 * s ^ 50
    + 2225 * s ^ 49
    - 23894 * s ^ 48
    + 153878 * s ^ 47
    - 414723 * s ^ 46
    - 2868879 * s ^ 45
    + 45640832 * s ^ 44
    - 343306811 * s ^ 43
    + 1852573090 * s ^ 42
    - 7919313550 * s ^ 41
    + 28021983611 * s ^ 40
    - 84437223996 * s ^ 39
    + 222422600687 * s ^ 38
    - 527438261305 * s ^ 37
    + 1160662242741 * s ^ 36
    - 2423903492318 * s ^ 35
    + 4833288225262 * s ^ 34
    - 9122959641829 * s ^ 33
    + 16077619109941 * s ^ 32
    - 26180666488906 * s ^ 31
    + 39227163403381 * s ^ 30
    - 54088055131799 * s ^ 29
    + 68692876027765 * s ^ 28
    - 80312888467821 * s ^ 27
    + 86278585903051 * s ^ 26
    - 84984957413829 * s ^ 25
    + 76637522207378 * s ^ 24
    - 63143413940563 * s ^ 23
    + 47208217869102 * s ^ 22
    - 31455261901646 * s ^ 21
    + 17970394707172 * s ^ 20
    - 8060008340541 * s ^ 19
    + 2061483488091 * s ^ 18
    + 675980786140 * s ^ 17
    - 1355956243042 * s ^ 16
    + 1108980948785 * s ^ 15
    - 656711091550 * s ^ 14
    + 308587031425 * s ^ 13
    - 117355063565 * s ^ 12
    + 35439750914 * s ^ 11
    - 7782095448 * s ^ 10
    + 792248925 * s ^ 9
    + 233402368 * s ^ 8
    - 140044096 * s ^ 7
    + 34308473 * s ^ 6
    - 3832614 * s ^ 5
    - 70171 * s ^ 4
    + 57776 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient15 (s : ℚ) : ℚ :=
  5 * s ^ 51
    - 244 * s ^ 50
    + 5666 * s ^ 49
    - 83403 * s ^ 48
    + 875273 * s ^ 47
    - 6989559 * s ^ 46
    + 44285688 * s ^ 45
    - 229205122 * s ^ 44
    + 990135327 * s ^ 43
    - 3634969086 * s ^ 42
    + 11563824164 * s ^ 41
    - 32771666210 * s ^ 40
    + 86186445456 * s ^ 39
    - 220313788190 * s ^ 38
    + 561043866468 * s ^ 37
    - 1400850510253 * s ^ 36
    + 3302080656639 * s ^ 35
    - 7126715507141 * s ^ 34
    + 13895061803166 * s ^ 33
    - 24470758843683 * s ^ 32
    + 39198260679063 * s ^ 31
    - 57596044025781 * s ^ 30
    + 78042363804266 * s ^ 29
    - 97531783790580 * s ^ 28
    + 112050539516765 * s ^ 27
    - 117910994861643 * s ^ 26
    + 113357013216799 * s ^ 25
    - 99214868071270 * s ^ 24
    + 78148409423124 * s ^ 23
    - 53581675039925 * s ^ 22
    + 29336492068267 * s ^ 21
    - 9271918863221 * s ^ 20
    - 3835048002930 * s ^ 19
    + 9518321010465 * s ^ 18
    - 9695402052032 * s ^ 17
    + 7219996251935 * s ^ 16
    - 4337667601716 * s ^ 15
    + 2157410891254 * s ^ 14
    - 885831213827 * s ^ 13
    + 291926313238 * s ^ 12
    - 70091336552 * s ^ 11
    + 7179460122 * s ^ 10
    + 3467572223 * s ^ 9
    - 2389722807 * s ^ 8
    + 779206328 * s ^ 7
    - 146737537 * s ^ 6
    + 10279864 * s ^ 5
    + 1655488 * s ^ 4
    - 364310 * s ^ 3
    - 31 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient16 (s : ℚ) : ℚ :=
  s ^ 52
    - 44 * s ^ 51
    + 926 * s ^ 50
    - 12330 * s ^ 49
    + 115959 * s ^ 48
    - 815195 * s ^ 47
    + 4425643 * s ^ 46
    - 18941269 * s ^ 45
    + 65391443 * s ^ 44
    - 194735705 * s ^ 43
    + 610902295 * s ^ 42
    - 2547800199 * s ^ 41
    + 12532040739 * s ^ 40
    - 57002696870 * s ^ 39
    + 218214867105 * s ^ 38
    - 695194834586 * s ^ 37
    + 1865649366968 * s ^ 36
    - 4297115742677 * s ^ 35
    + 8680972164889 * s ^ 34
    - 15742465875030 * s ^ 33
    + 26192216233701 * s ^ 32
    - 40602248507897 * s ^ 31
    + 58872412010950 * s ^ 30
    - 79266123522890 * s ^ 29
    + 97946788379228 * s ^ 28
    - 110096704390368 * s ^ 27
    + 112051882757084 * s ^ 26
    - 102541427916602 * s ^ 25
    + 82194305076005 * s ^ 24
    - 52797927431114 * s ^ 23
    + 18152896958764 * s ^ 22
    + 14866764687213 * s ^ 21
    - 38272533799215 * s ^ 20
    + 47339529422269 * s ^ 19
    - 43395777990149 * s ^ 18
    + 32294754739513 * s ^ 17
    - 20171551449349 * s ^ 16
    + 10645482526809 * s ^ 15
    - 4682105949376 * s ^ 14
    + 1645438202382 * s ^ 13
    - 405874663607 * s ^ 12
    + 24139473190 * s ^ 11
    + 42225717907 * s ^ 10
    - 28962106628 * s ^ 9
    + 11426317863 * s ^ 8
    - 2952635625 * s ^ 7
    + 430243916 * s ^ 6
    + 569962 * s ^ 5
    - 12618392 * s ^ 4
    + 1841931 * s ^ 3
    + 462 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient17 (s : ℚ) : ℚ :=
  -5 * s ^ 51
    + 199 * s ^ 50
    - 3773 * s ^ 49
    + 44798 * s ^ 48
    - 366413 * s ^ 47
    + 2103265 * s ^ 46
    - 7715660 * s ^ 45
    + 6244821 * s ^ 44
    + 152135172 * s ^ 43
    - 1393241792 * s ^ 42
    + 7757245478 * s ^ 41
    - 32773853495 * s ^ 40
    + 111889405562 * s ^ 39
    - 317559902810 * s ^ 38
    + 764926266722 * s ^ 37
    - 1603471988403 * s ^ 36
    + 3035669104417 * s ^ 35
    - 5444263659330 * s ^ 34
    + 9614319531890 * s ^ 33
    - 16755775920798 * s ^ 32
    + 27851861372768 * s ^ 31
    - 42325818218180 * s ^ 30
    + 57149227048971 * s ^ 29
    - 67807451567013 * s ^ 28
    + 70525419135524 * s ^ 27
    - 63137224423967 * s ^ 26
    + 43732937760555 * s ^ 25
    - 10024260832114 * s ^ 24
    - 37319630181585 * s ^ 23
    + 89594448598746 * s ^ 22
    - 130771337880655 * s ^ 21
    + 146595481367907 * s ^ 20
    - 134139407464455 * s ^ 19
    + 102914913390513 * s ^ 18
    - 67179837329005 * s ^ 17
    + 37339831707419 * s ^ 16
    - 17283783825025 * s ^ 15
    + 6237829420327 * s ^ 14
    - 1379596359813 * s ^ 13
    - 176149358979 * s ^ 12
    + 397279194357 * s ^ 11
    - 259895471439 * s ^ 10
    + 115946709807 * s ^ 9
    - 37447693336 * s ^ 8
    + 8007743851 * s ^ 7
    - 706403342 * s ^ 6
    - 169549909 * s ^ 5
    + 65336849 * s ^ 4
    - 7654216 * s ^ 3
    - 4406 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient18 (s : ℚ) : ℚ :=
  -2 * s ^ 51
    + 102 * s ^ 50
    - 2442 * s ^ 49
    + 36989 * s ^ 48
    - 401124 * s ^ 47
    + 3333038 * s ^ 46
    - 22125280 * s ^ 45
    + 120369044 * s ^ 44
    - 543536943 * s ^ 43
    + 2038552244 * s ^ 42
    - 6273696909 * s ^ 41
    + 15391479009 * s ^ 40
    - 28380425144 * s ^ 39
    + 34454891971 * s ^ 38
    - 19895370705 * s ^ 37
    + 33985594770 * s ^ 36
    - 353893547615 * s ^ 35
    + 1664984073627 * s ^ 34
    - 4959248653200 * s ^ 33
    + 10833791249246 * s ^ 32
    - 18398908064279 * s ^ 31
    + 24880603949375 * s ^ 30
    - 26943932238206 * s ^ 29
    + 22625779846346 * s ^ 28
    - 10761911356430 * s ^ 27
    - 12573099529836 * s ^ 26
    + 55354329975530 * s ^ 25
    - 123025651104212 * s ^ 24
    + 207103273438427 * s ^ 23
    - 281638188975068 * s ^ 22
    + 316467557278523 * s ^ 21
    - 297804783614013 * s ^ 20
    + 236950324882637 * s ^ 19
    - 160366011554287 * s ^ 18
    + 91955629560906 * s ^ 17
    - 43148717133391 * s ^ 16
    + 14570802223123 * s ^ 15
    - 1377400385080 * s ^ 14
    - 2698223924137 * s ^ 13
    + 2756124272657 * s ^ 12
    - 1745829770376 * s ^ 11
    + 848893325232 * s ^ 10
    - 322630564931 * s ^ 9
    + 89653497453 * s ^ 8
    - 14364266617 * s ^ 7
    - 642407258 * s ^ 6
    + 1045445667 * s ^ 5
    - 261239338 * s ^ 4
    + 26580711 * s ^ 3
    + 30196 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient19 (s : ℚ) : ℚ :=
  7 * s ^ 50
    - 306 * s ^ 49
    + 6475 * s ^ 48
    - 88843 * s ^ 47
    + 893704 * s ^ 46
    - 7060422 * s ^ 45
    + 45664990 * s ^ 44
    - 247148397 * s ^ 43
    + 1124543591 * s ^ 42
    - 4251270588 * s ^ 41
    + 12929506916 * s ^ 40
    - 29264469171 * s ^ 39
    + 36738215600 * s ^ 38
    + 46745311748 * s ^ 37
    - 434754439590 * s ^ 36
    + 1467753191782 * s ^ 35
    - 3376089977127 * s ^ 34
    + 5763911642959 * s ^ 33
    - 7183830939373 * s ^ 32
    + 5555502528774 * s ^ 31
    + 346258490520 * s ^ 30
    - 9996513944825 * s ^ 29
    + 23710564944771 * s ^ 28
    - 48303536271117 * s ^ 27
    + 98741193949003 * s ^ 26
    - 188184180751995 * s ^ 25
    + 310029856935156 * s ^ 24
    - 428898838979519 * s ^ 23
    + 495834595274848 * s ^ 22
    - 480382383716630 * s ^ 21
    + 391261040194562 * s ^ 20
    - 267417893684937 * s ^ 19
    + 150602359797485 * s ^ 18
    - 64364463668316 * s ^ 17
    + 12586327170099 * s ^ 16
    + 11204990557462 * s ^ 15
    - 16855587604833 * s ^ 14
    + 13857002317800 * s ^ 13
    - 8755700425683 * s ^ 12
    + 4570358637913 * s ^ 11
    - 1970499541976 * s ^ 10
    + 664620614641 * s ^ 9
    - 149717379837 * s ^ 8
    + 7791466473 * s ^ 7
    + 9436606271 * s ^ 6
    - 4156702801 * s ^ 5
    + 847760742 * s ^ 4
    - 77999732 * s ^ 3
    - 158273 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient20 (s : ℚ) : ℚ :=
  s ^ 50
    - 53 * s ^ 49
    + 1291 * s ^ 48
    - 19810 * s ^ 47
    + 220867 * s ^ 46
    - 1958102 * s ^ 45
    + 14686911 * s ^ 44
    - 96448258 * s ^ 43
    + 558010776 * s ^ 42
    - 2809265062 * s ^ 41
    + 12081784005 * s ^ 40
    - 43594103853 * s ^ 39
    + 129533856721 * s ^ 38
    - 308574653138 * s ^ 37
    + 557057547727 * s ^ 36
    - 634414812357 * s ^ 35
    - 67038891418 * s ^ 34
    + 2386434822114 * s ^ 33
    - 6709348590444 * s ^ 32
    + 12127991168470 * s ^ 31
    - 17062723533972 * s ^ 30
    + 23180351329989 * s ^ 29
    - 41174131334351 * s ^ 28
    + 91269466189941 * s ^ 27
    - 191072165579647 * s ^ 26
    + 334610424628992 * s ^ 25
    - 480640725758668 * s ^ 24
    + 567985213041519 * s ^ 23
    - 553606665372091 * s ^ 22
    + 442763672799435 * s ^ 21
    - 283380888578118 * s ^ 20
    + 131727137242370 * s ^ 19
    - 21567575830251 * s ^ 18
    - 41417648341243 * s ^ 17
    + 66216776258285 * s ^ 16
    - 64984543966628 * s ^ 15
    + 50202047342781 * s ^ 14
    - 32560738152634 * s ^ 13
    + 18186563355325 * s ^ 12
    - 8712438961953 * s ^ 11
    + 3420721479266 * s ^ 10
    - 974513601197 * s ^ 9
    + 118580148029 * s ^ 8
    + 55046658180 * s ^ 7
    - 39621665040 * s ^ 6
    + 12680936868 * s ^ 5
    - 2289523632 * s ^ 4
    + 194773075 * s ^ 3
    + 658959 * s ^ 2
    + 23 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient21 (s : ℚ) : ℚ :=
  -s ^ 49
    + 23 * s ^ 48
    + 52 * s ^ 47
    - 8784 * s ^ 46
    + 162752 * s ^ 45
    - 1655655 * s ^ 44
    + 10441775 * s ^ 43
    - 34654467 * s ^ 42
    - 55848188 * s ^ 41
    + 1559164411 * s ^ 40
    - 11474047530 * s ^ 39
    + 55929329461 * s ^ 38
    - 205510444034 * s ^ 37
    + 592869961744 * s ^ 36
    - 1353815313812 * s ^ 35
    + 2400701919319 * s ^ 34
    - 3084925456429 * s ^ 33
    + 2241894151682 * s ^ 32
    + 395488901432 * s ^ 31
    - 802543972577 * s ^ 30
    - 12928598640725 * s ^ 29
    + 59094442928097 * s ^ 28
    - 150919402816797 * s ^ 27
    + 278925642998275 * s ^ 26
    - 402129037166528 * s ^ 25
    + 462832432504319 * s ^ 24
    - 421908072962064 * s ^ 23
    + 288345234117723 * s ^ 22
    - 114802545146096 * s ^ 21
    - 38503365276998 * s ^ 20
    + 138219721644185 * s ^ 19
    - 183718502286915 * s ^ 18
    + 189336710105996 * s ^ 17
    - 168013781469896 * s ^ 16
    + 130489445953190 * s ^ 15
    - 88878124787828 * s ^ 14
    + 53331634798030 * s ^ 13
    - 28063587825833 * s ^ 12
    + 12490706091103 * s ^ 11
    - 4236404257555 * s ^ 10
    + 740181448845 * s ^ 9
    + 235416847721 * s ^ 8
    - 258427173950 * s ^ 7
    + 114805057431 * s ^ 6
    - 31417260043 * s ^ 5
    + 5217587421 * s ^ 4
    - 415409024 * s ^ 3
    - 2233007 * s ^ 2
    - 251 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient22 (s : ℚ) : ℚ :=
  -7 * s ^ 48
    + 397 * s ^ 47
    - 10508 * s ^ 46
    + 173576 * s ^ 45
    - 2010561 * s ^ 44
    + 17335257 * s ^ 43
    - 114857448 * s ^ 42
    + 592307775 * s ^ 41
    - 2358771422 * s ^ 40
    + 6915497847 * s ^ 39
    - 12218046444 * s ^ 38
    - 6191614893 * s ^ 37
    + 143585324133 * s ^ 36
    - 634029674484 * s ^ 35
    + 1834042560544 * s ^ 34
    - 3858447847945 * s ^ 33
    + 5537051289235 * s ^ 32
    - 2764305567994 * s ^ 31
    - 12459878408901 * s ^ 30
    + 49564504556830 * s ^ 29
    - 111561262281788 * s ^ 28
    + 184995968910517 * s ^ 27
    - 237170226399701 * s ^ 26
    + 229182043308336 * s ^ 25
    - 141338207621820 * s ^ 24
    - 7472576393212 * s ^ 23
    + 166638595534751 * s ^ 22
    - 285912577615009 * s ^ 21
    + 344970403724888 * s ^ 20
    - 354691657781841 * s ^ 19
    + 335061003638646 * s ^ 18
    - 296312154744594 * s ^ 17
    + 240877072474145 * s ^ 16
    - 175813295026216 * s ^ 15
    + 114146325364469 * s ^ 14
    - 65618231163821 * s ^ 13
    + 32466692037001 * s ^ 12
    - 12562650418556 * s ^ 11
    + 2619460574774 * s ^ 10
    + 892354775595 * s ^ 9
    - 1249921384813 * s ^ 8
    + 708966809028 * s ^ 7
    - 260770795057 * s ^ 6
    + 64827255799 * s ^ 5
    - 10108501983 * s ^ 4
    + 757225897 * s ^ 3
    + 6257851 * s ^ 2
    + 1727 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient23 (s : ℚ) : ℚ :=
  -s ^ 48
    + 72 * s ^ 47
    - 2332 * s ^ 46
    + 46325 * s ^ 45
    - 641627 * s ^ 44
    + 6638236 * s ^ 43
    - 53474962 * s ^ 42
    + 344302071 * s ^ 41
    - 1800479780 * s ^ 40
    + 7707014688 * s ^ 39
    - 26967568475 * s ^ 38
    + 75870333013 * s ^ 37
    - 162504899666 * s ^ 36
    + 212962522406 * s ^ 35
    + 122962951074 * s ^ 34
    - 1809913465211 * s ^ 33
    + 6734059624708 * s ^ 32
    - 17398694838746 * s ^ 31
    + 35105872964540 * s ^ 30
    - 56358202593552 * s ^ 29
    + 69491898749208 * s ^ 28
    - 55955220270951 * s ^ 27
    - 617653665022 * s ^ 26
    + 100878612293337 * s ^ 25
    - 222259826794724 * s ^ 24
    + 327722094954133 * s ^ 23
    - 388675714506266 * s ^ 22
    + 403382694408784 * s ^ 21
    - 392210281564618 * s ^ 20
    + 374425131766583 * s ^ 19
    - 351024872089040 * s ^ 18
    + 310430417249130 * s ^ 17
    - 248169948957550 * s ^ 16
    + 175786231408152 * s ^ 15
    - 109860471458372 * s ^ 14
    + 59285348041450 * s ^ 13
    - 25024580453443 * s ^ 12
    + 5149012190381 * s ^ 11
    + 3370322828441 * s ^ 10
    - 4730076425998 * s ^ 9
    + 3182374182625 * s ^ 8
    - 1464934191531 * s ^ 7
    + 485048535515 * s ^ 6
    - 112764166338 * s ^ 5
    + 16701040868 * s ^ 4
    - 1176877735 * s ^ 3
    - 14651405 * s ^ 2
    - 8395 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient24 (s : ℚ) : ℚ :=
  3 * s ^ 47
    - 177 * s ^ 46
    + 4985 * s ^ 45
    - 89466 * s ^ 44
    + 1150826 * s ^ 43
    - 11305178 * s ^ 42
    + 88211283 * s ^ 41
    - 561375084 * s ^ 40
    + 2969676388 * s ^ 39
    - 13245982542 * s ^ 38
    + 50366865019 * s ^ 37
    - 164592678153 * s ^ 36
    + 464298828104 * s ^ 35
    - 1128415650747 * s ^ 34
    + 2329325397103 * s ^ 33
    - 3916456379372 * s ^ 32
    + 4709755134394 * s ^ 31
    - 1554080665475 * s ^ 30
    - 10993246695084 * s ^ 29
    + 38926552015328 * s ^ 28
    - 84513147919868 * s ^ 27
    + 141673460474517 * s ^ 26
    - 195553868336826 * s ^ 25
    + 229652724239042 * s ^ 24
    - 237899182562066 * s ^ 23
    + 231581886065617 * s ^ 22
    - 231299286254546 * s ^ 21
    + 247924285566577 * s ^ 20
    - 270694752329559 * s ^ 19
    + 275626766402625 * s ^ 18
    - 247141319105277 * s ^ 17
    + 191423483733731 * s ^ 16
    - 128170860813906 * s ^ 15
    + 72888775765565 * s ^ 14
    - 30853992337350 * s ^ 13
    + 2793165408786 * s ^ 12
    + 11460617907879 * s ^ 11
    - 14311479198961 * s ^ 10
    + 10770008068788 * s ^ 9
    - 5897810861123 * s ^ 8
    + 2435934458327 * s ^ 7
    - 752380894726 * s ^ 6
    + 166169290076 * s ^ 5
    - 23522262362 * s ^ 4
    + 1550174214 * s ^ 3
    + 28828058 * s ^ 2
    + 30613 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient25 (s : ℚ) : ℚ :=
  -3 * s ^ 46
    + 164 * s ^ 45
    - 4337 * s ^ 44
    + 73813 * s ^ 43
    - 907285 * s ^ 42
    + 8571729 * s ^ 41
    - 64736327 * s ^ 40
    + 401810343 * s ^ 39
    - 2094888793 * s ^ 38
    + 9350814913 * s ^ 37
    - 36381491526 * s ^ 36
    + 125468924221 * s ^ 35
    - 388795284498 * s ^ 34
    + 1090407824754 * s ^ 33
    - 2764608546766 * s ^ 32
    + 6281762724472 * s ^ 31
    - 12627411327353 * s ^ 30
    + 22141305954646 * s ^ 29
    - 33379698268969 * s ^ 28
    + 42560783089785 * s ^ 27
    - 44940064020983 * s ^ 26
    + 38539257861391 * s ^ 25
    - 28368955329298 * s ^ 24
    + 26879953321939 * s ^ 23
    - 46976394323605 * s ^ 22
    + 90360593180074 * s ^ 21
    - 141545884804046 * s ^ 20
    + 175692013559936 * s ^ 19
    - 175707350529203 * s ^ 18
    + 143949945344644 * s ^ 17
    - 97479869383427 * s ^ 16
    + 52372801545022 * s ^ 15
    - 14931649388652 * s ^ 14
    - 13502614546146 * s ^ 13
    + 30498640958535 * s ^ 12
    - 34359125665981 * s ^ 11
    + 27942137325856 * s ^ 10
    - 17559860896134 * s ^ 9
    + 8666261231018 * s ^ 8
    - 3338995749222 * s ^ 7
    + 979807767682 * s ^ 6
    - 207463189863 * s ^ 5
    + 28140902759 * s ^ 4
    - 1711630448 * s ^ 3
    - 47788059 * s ^ 2
    - 86772 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient26 (s : ℚ) : ℚ :=
  s ^ 45
    - 51 * s ^ 44
    + 1247 * s ^ 43
    - 19267 * s ^ 42
    + 208739 * s ^ 41
    - 1661042 * s ^ 40
    + 9832591 * s ^ 39
    - 42221377 * s ^ 38
    + 116718553 * s ^ 37
    - 81996202 * s ^ 36
    - 1004540134 * s ^ 35
    + 5410261516 * s ^ 34
    - 11278352098 * s ^ 33
    - 18428955335 * s ^ 32
    + 243986837911 * s ^ 31
    - 1092224572684 * s ^ 30
    + 3331234550360 * s ^ 29
    - 7807285237774 * s ^ 28
    + 14622848103531 * s ^ 27
    - 21934405541010 * s ^ 26
    + 25182946331095 * s ^ 25
    - 18078485366604 * s ^ 24
    - 3739524153172 * s ^ 23
    + 37747452272041 * s ^ 22
    - 72683342654736 * s ^ 21
    + 93501951148081 * s ^ 20
    - 90869653819611 * s ^ 19
    + 67501904375872 * s ^ 18
    - 35161218946508 * s ^ 17
    + 4547987831671 * s ^ 16
    + 21385758436591 * s ^ 15
    - 43573015550131 * s ^ 14
    + 59570899022322 * s ^ 13
    - 64107063978234 * s ^ 12
    + 55667664430817 * s ^ 11
    - 39252067152021 * s ^ 10
    + 22473877165826 * s ^ 9
    - 10377435903408 * s ^ 8
    + 3801885710173 * s ^ 7
    - 1071207446711 * s ^ 6
    + 218610471062 * s ^ 5
    - 28396828638 * s ^ 4
    + 1554281496 * s ^ 3
    + 66709820 * s ^ 2
    + 195432 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient27 (s : ℚ) : ℚ :=
  -2 * s ^ 43
    + 131 * s ^ 42
    - 4044 * s ^ 41
    + 78468 * s ^ 40
    - 1077581 * s ^ 39
    + 11172339 * s ^ 38
    - 90978386 * s ^ 37
    + 596830606 * s ^ 36
    - 3206408309 * s ^ 35
    + 14253891222 * s ^ 34
    - 52740486818 * s ^ 33
    + 162764003541 * s ^ 32
    - 418067832478 * s ^ 31
    + 885602368696 * s ^ 30
    - 1508080803500 * s ^ 29
    + 1908814547010 * s ^ 28
    - 1218317152310 * s ^ 27
    - 1875909679694 * s ^ 26
    + 8600693293688 * s ^ 25
    - 18962211923972 * s ^ 24
    + 30475508163836 * s ^ 23
    - 38101153568430 * s ^ 22
    + 36533688612092 * s ^ 21
    - 23858143649779 * s ^ 20
    + 3471356817695 * s ^ 19
    + 18130444959343 * s ^ 18
    - 36506866696497 * s ^ 17
    + 52412507433730 * s ^ 16
    - 68652113909121 * s ^ 15
    + 83743304438777 * s ^ 14
    - 90919788117707 * s ^ 13
    + 84547981369230 * s ^ 12
    - 66088909411827 * s ^ 11
    + 43041262464315 * s ^ 10
    - 23175045571860 * s ^ 9
    + 10195339012939 * s ^ 8
    - 3591377643076 * s ^ 7
    + 978120807992 * s ^ 6
    - 192924945025 * s ^ 5
    + 23898311499 * s ^ 4
    - 1120202899 * s ^ 3
    - 78159387 * s ^ 2
    - 354447 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient28 (s : ℚ) : ℚ :=
  2 * s ^ 42
    - 121 * s ^ 41
    + 3480 * s ^ 40
    - 63677 * s ^ 39
    + 835020 * s ^ 38
    - 8362335 * s ^ 37
    + 66434404 * s ^ 36
    - 428931761 * s ^ 35
    + 2287142152 * s ^ 34
    - 10186686613 * s ^ 33
    + 38232453837 * s ^ 32
    - 121870078922 * s ^ 31
    + 332581907500 * s ^ 30
    - 783728600213 * s ^ 29
    + 1608016667707 * s ^ 28
    - 2885980187926 * s ^ 27
    + 4505616979047 * s ^ 26
    - 5954257378224 * s ^ 25
    + 6159482157444 * s ^ 24
    - 3682627058174 * s ^ 23
    - 2508982605564 * s ^ 22
    + 12076681639939 * s ^ 21
    - 23141260418470 * s ^ 20
    + 33551825063213 * s ^ 19
    - 42915983375058 * s ^ 18
    + 53405100102325 * s ^ 17
    - 67518947699337 * s ^ 16
    + 83947634750344 * s ^ 15
    - 96173575124772 * s ^ 14
    + 96729993235534 * s ^ 13
    - 83388064205876 * s ^ 12
    + 60967362407302 * s ^ 11
    - 37547570116166 * s ^ 10
    + 19312762077804 * s ^ 9
    - 8183283044090 * s ^ 8
    + 2792571497833 * s ^ 7
    - 738509632094 * s ^ 6
    + 140863458611 * s ^ 5
    - 16483490827 * s ^ 4
    + 591358648 * s ^ 3
    + 76366733 * s ^ 2
    + 521341 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient29 (s : ℚ) : ℚ :=
  -s ^ 41
    + 55 * s ^ 40
    - 1480 * s ^ 39
    + 25939 * s ^ 38
    - 331382 * s ^ 37
    + 3266228 * s ^ 36
    - 25645608 * s ^ 35
    + 163600161 * s ^ 34
    - 859426137 * s ^ 33
    + 3757835806 * s ^ 32
    - 13819726260 * s ^ 31
    + 43283862924 * s ^ 30
    - 117441608534 * s ^ 29
    + 282503509150 * s ^ 28
    - 618865701551 * s ^ 27
    + 1261979415300 * s ^ 26
    - 2410611487451 * s ^ 25
    + 4268261591210 * s ^ 24
    - 6893444100014 * s ^ 23
    + 10079932064654 * s ^ 22
    - 13505793565072 * s ^ 21
    + 17240255595669 * s ^ 20
    - 22294902313698 * s ^ 19
    + 30546939190863 * s ^ 18
    - 43435525442869 * s ^ 17
    + 59810466446661 * s ^ 16
    - 74878739591394 * s ^ 15
    + 82210759672669 * s ^ 14
    - 77907323334405 * s ^ 13
    + 63320993069263 * s ^ 12
    - 43967241182718 * s ^ 11
    + 25937721325351 * s ^ 10
    - 12878743386247 * s ^ 9
    + 5299519960928 * s ^ 8
    - 1762431492266 * s ^ 7
    + 453960168598 * s ^ 6
    - 83560880167 * s ^ 5
    + 9061812318 * s ^ 4
    - 170978155 * s ^ 3
    - 61595251 * s ^ 2
    - 623087 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient30 (s : ℚ) : ℚ :=
  -s ^ 39
    + 65 * s ^ 38
    - 1875 * s ^ 37
    + 32482 * s ^ 36
    - 381657 * s ^ 35
    + 3232726 * s ^ 34
    - 20324440 * s ^ 33
    + 95144878 * s ^ 32
    - 319506609 * s ^ 31
    + 647789033 * s ^ 30
    + 140484372 * s ^ 29
    - 7318852471 * s ^ 28
    + 34579241389 * s ^ 27
    - 105440158664 * s ^ 26
    + 245634381469 * s ^ 25
    - 473633397663 * s ^ 24
    + 824362164454 * s ^ 23
    - 1448173509346 * s ^ 22
    + 2771492937867 * s ^ 21
    - 5603628984812 * s ^ 20
    + 10992642134124 * s ^ 19
    - 19651855259055 * s ^ 18
    + 31042882183577 * s ^ 17
    - 42748959844827 * s ^ 16
    + 51042828225688 * s ^ 15
    - 52758768155369 * s ^ 14
    + 47197544481397 * s ^ 13
    - 36514116738509 * s ^ 12
    + 24354965105285 * s ^ 11
    - 13914213976717 * s ^ 10
    + 6733356469565 * s ^ 9
    - 2711649603526 * s ^ 8
    + 883543882654 * s ^ 7
    - 222019001361 * s ^ 6
    + 39181865945 * s ^ 5
    - 3779294160 * s ^ 4
    - 43763535 * s ^ 3
    + 40394256 * s ^ 2
    + 603371 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient31 (s : ℚ) : ℚ :=
  s ^ 38
    - 51 * s ^ 37
    + 1214 * s ^ 36
    - 17857 * s ^ 35
    + 180661 * s ^ 34
    - 1318053 * s ^ 33
    + 6999904 * s ^ 32
    - 25933913 * s ^ 31
    + 53427251 * s ^ 30
    + 58700137 * s ^ 29
    - 1021490308 * s ^ 28
    + 4747475381 * s ^ 27
    - 13699946702 * s ^ 26
    + 24350632353 * s ^ 25
    - 7651455871 * s ^ 24
    - 127019816396 * s ^ 23
    + 575151448725 * s ^ 22
    - 1660041153254 * s ^ 21
    + 3789315205707 * s ^ 20
    - 7290419654401 * s ^ 19
    + 12116092272932 * s ^ 18
    - 17558993940446 * s ^ 17
    + 22266612158175 * s ^ 16
    - 24742786270311 * s ^ 15
    + 24109666878315 * s ^ 14
    - 20593750730432 * s ^ 13
    + 15383861417724 * s ^ 12
    - 9997883375029 * s ^ 11
    + 5603073484701 * s ^ 10
    - 2671576675167 * s ^ 9
    + 1061904431398 * s ^ 8
    - 340718745388 * s ^ 7
    + 83451774606 * s ^ 6
    - 13893926878 * s ^ 5
    + 1070866409 * s ^ 4
    + 88620226 * s ^ 3
    - 21055738 * s ^ 2
    - 469625 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient32 (s : ℚ) : ℚ :=
  -2 * s ^ 36
    + 107 * s ^ 35
    - 2735 * s ^ 34
    + 44470 * s ^ 33
    - 516686 * s ^ 32
    + 4569362 * s ^ 31
    - 32002093 * s ^ 30
    + 182450619 * s ^ 29
    - 864591740 * s ^ 28
    + 3465062789 * s ^ 27
    - 11933212150 * s ^ 26
    + 35874158593 * s ^ 25
    - 95639203712 * s ^ 24
    + 229447084803 * s ^ 23
    - 500875719001 * s ^ 22
    + 999933440092 * s ^ 21
    - 1822847607254 * s ^ 20
    + 3016150206626 * s ^ 19
    - 4497047547873 * s ^ 18
    + 6006228006970 * s ^ 17
    - 7159547367497 * s ^ 16
    + 7601987084817 * s ^ 15
    - 7178040060196 * s ^ 14
    + 6010031567010 * s ^ 13
    - 4439237060456 * s ^ 12
    + 2869771456346 * s ^ 11
    - 1605416000148 * s ^ 10
    + 764876339348 * s ^ 9
    - 303087431591 * s ^ 8
    + 96163165022 * s ^ 7
    - 22795443176 * s ^ 6
    + 3429943611 * s ^ 5
    - 131184886 * s ^ 4
    - 58339152 * s ^ 3
    + 8420124 * s ^ 2
    + 289639 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient33 (s : ℚ) : ℚ :=
  s ^ 34
    - 54 * s ^ 33
    + 1402 * s ^ 32
    - 23294 * s ^ 31
    + 278081 * s ^ 30
    - 2538629 * s ^ 29
    + 18416924 * s ^ 28
    - 108933675 * s ^ 27
    + 534890642 * s ^ 26
    - 2209300233 * s ^ 25
    + 7753264229 * s ^ 24
    - 23303288277 * s ^ 23
    + 60392443102 * s ^ 22
    - 135787420297 * s ^ 21
    + 266495712818 * s ^ 20
    - 459409592011 * s ^ 19
    + 700105606682 * s ^ 18
    - 948764974154 * s ^ 17
    + 1148475173090 * s ^ 16
    - 1244085676660 * s ^ 15
    + 1204195003694 * s ^ 14
    - 1036567437767 * s ^ 13
    + 787626178673 * s ^ 12
    - 523106512878 * s ^ 11
    + 299755471867 * s ^ 10
    - 145501354771 * s ^ 9
    + 58157841684 * s ^ 8
    - 18243085643 * s ^ 7
    + 4071873644 * s ^ 6
    - 474238017 * s ^ 5
    - 38720192 * s ^ 4
    + 23508554 * s ^ 3
    - 2430189 * s ^ 2
    - 138346 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient34 (s : ℚ) : ℚ :=
  -2 * s ^ 30
    + 98 * s ^ 29
    - 2290 * s ^ 28
    + 33956 * s ^ 27
    - 358636 * s ^ 26
    + 2870895 * s ^ 25
    - 18096102 * s ^ 24
    + 92119842 * s ^ 23
    - 385442547 * s ^ 22
    + 1342345959 * s ^ 21
    - 3926863292 * s ^ 20
    + 9715155420 * s ^ 19
    - 20431796597 * s ^ 18
    + 36674704530 * s ^ 17
    - 56373444484 * s ^ 16
    + 74416104077 * s ^ 15
    - 84556582927 * s ^ 14
    + 82807413606 * s ^ 13
    - 69832725396 * s ^ 12
    + 50473614858 * s ^ 11
    - 30926648407 * s ^ 10
    + 15737458983 * s ^ 9
    - 6409067952 * s ^ 8
    + 1940656083 * s ^ 7
    - 356486376 * s ^ 6
    - 2254405 * s ^ 5
    + 22832724 * s ^ 4
    - 6035508 * s ^ 3
    + 444540 * s ^ 2
    + 49350 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient35 (s : ℚ) : ℚ :=
  s ^ 26
    - 44 * s ^ 25
    + 915 * s ^ 24
    - 11958 * s ^ 23
    + 110162 * s ^ 22
    - 760616 * s ^ 21
    + 4085492 * s ^ 20
    - 17490183 * s ^ 19
    + 60655112 * s ^ 18
    - 172254385 * s ^ 17
    + 403357517 * s ^ 16
    - 781709872 * s ^ 15
    + 1255040960 * s ^ 14
    - 1666338189 * s ^ 13
    + 1820597721 * s ^ 12
    - 1621425635 * s ^ 11
    + 1156876771 * s ^ 10
    - 639231213 * s ^ 9
    + 252781709 * s ^ 8
    - 53947192 * s ^ 7
    - 8519594 * s ^ 6
    + 12066399 * s ^ 5
    - 4729328 * s ^ 4
    + 889332 * s ^ 3
    - 31510 * s ^ 2
    - 12372 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient36 (s : ℚ) : ℚ :=
  -s ^ 19
    + 33 * s ^ 18
    - 505 * s ^ 17
    + 4756 * s ^ 16
    - 30849 * s ^ 15
    + 146128 * s ^ 14
    - 522972 * s ^ 13
    + 1442958 * s ^ 12
    - 3104054 * s ^ 11
    + 5229243 * s ^ 10
    - 6889436 * s ^ 9
    + 7047926 * s ^ 8
    - 5521886 * s ^ 7
    + 3237096 * s ^ 6
    - 1361739 * s ^ 5
    + 374348 * s ^ 4
    - 48358 * s ^ 3
    - 4632 * s ^ 2
    + 1944 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient37 (s : ℚ) : ℚ :=
  s ^ 10
    - 18 * s ^ 9
    + 140 * s ^ 8
    - 616 * s ^ 7
    + 1685 * s ^ 6
    - 2962 * s ^ 5
    + 3334 * s ^ 4
    - 2308 * s ^ 3
    + 888 * s ^ 2
    - 144 * s

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def termOne (r s : ℚ) : ℚ :=
  termOneCoefficient0 s +
    termOneCoefficient1 s * r +
    termOneCoefficient2 s * r ^ 2 +
    termOneCoefficient3 s * r ^ 3 +
    termOneCoefficient4 s * r ^ 4 +
    termOneCoefficient5 s * r ^ 5 +
    termOneCoefficient6 s * r ^ 6 +
    termOneCoefficient7 s * r ^ 7 +
    termOneCoefficient8 s * r ^ 8 +
    termOneCoefficient9 s * r ^ 9 +
    termOneCoefficient10 s * r ^ 10 +
    termOneCoefficient11 s * r ^ 11 +
    termOneCoefficient12 s * r ^ 12 +
    termOneCoefficient13 s * r ^ 13 +
    termOneCoefficient14 s * r ^ 14 +
    termOneCoefficient15 s * r ^ 15 +
    termOneCoefficient16 s * r ^ 16 +
    termOneCoefficient17 s * r ^ 17 +
    termOneCoefficient18 s * r ^ 18 +
    termOneCoefficient19 s * r ^ 19 +
    termOneCoefficient20 s * r ^ 20 +
    termOneCoefficient21 s * r ^ 21 +
    termOneCoefficient22 s * r ^ 22 +
    termOneCoefficient23 s * r ^ 23 +
    termOneCoefficient24 s * r ^ 24 +
    termOneCoefficient25 s * r ^ 25 +
    termOneCoefficient26 s * r ^ 26 +
    termOneCoefficient27 s * r ^ 27 +
    termOneCoefficient28 s * r ^ 28 +
    termOneCoefficient29 s * r ^ 29 +
    termOneCoefficient30 s * r ^ 30 +
    termOneCoefficient31 s * r ^ 31 +
    termOneCoefficient32 s * r ^ 32 +
    termOneCoefficient33 s * r ^ 33 +
    termOneCoefficient34 s * r ^ 34 +
    termOneCoefficient35 s * r ^ 35 +
    termOneCoefficient36 s * r ^ 36 +
    termOneCoefficient37 s * r ^ 37

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_0 (s : ℚ) :
    termOneCoefficient0 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient0,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_1 (s : ℚ) :
    termOneCoefficient1 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient1,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_2 (s : ℚ) :
    termOneCoefficient2 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient2,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_3 (s : ℚ) :
    termOneCoefficient3 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient3,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_4 (s : ℚ) :
    termOneCoefficient4 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient4,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_5 (s : ℚ) :
    termOneCoefficient5 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient5,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_6 (s : ℚ) :
    termOneCoefficient6 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient6,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_7 (s : ℚ) :
    termOneCoefficient7 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient7,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_8 (s : ℚ) :
    termOneCoefficient8 s =
      t1Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient8,
    t1Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_9 (s : ℚ) :
    termOneCoefficient9 s =
      t1Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient9,
    t1Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_10 (s : ℚ) :
    termOneCoefficient10 s =
      t1Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient10,
    t1Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_11 (s : ℚ) :
    termOneCoefficient11 s =
      t1Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient11,
    t1Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_12 (s : ℚ) :
    termOneCoefficient12 s =
      t1Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient12,
    t1Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_13 (s : ℚ) :
    termOneCoefficient13 s =
      t1Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient13,
    t1Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_14 (s : ℚ) :
    termOneCoefficient14 s =
      t1Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient14,
    t1Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_15 (s : ℚ) :
    termOneCoefficient15 s =
      t1Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient15,
    t1Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_16 (s : ℚ) :
    termOneCoefficient16 s =
      t1Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient16,
    t1Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_17 (s : ℚ) :
    termOneCoefficient17 s =
      t1Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient17,
    t1Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_18 (s : ℚ) :
    termOneCoefficient18 s =
      t1Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient18,
    t1Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_19 (s : ℚ) :
    termOneCoefficient19 s =
      t1Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient19,
    t1Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_20 (s : ℚ) :
    termOneCoefficient20 s =
      t1Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient20,
    t1Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_21 (s : ℚ) :
    termOneCoefficient21 s =
      t1Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient21,
    t1Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_22 (s : ℚ) :
    termOneCoefficient22 s =
      t1Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient22,
    t1Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_23 (s : ℚ) :
    termOneCoefficient23 s =
      t1Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient23,
    t1Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_24 (s : ℚ) :
    termOneCoefficient24 s =
      t1Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient24,
    t1Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_25 (s : ℚ) :
    termOneCoefficient25 s =
      t1Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient25,
    t1Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_26 (s : ℚ) :
    termOneCoefficient26 s =
      t1Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient26,
    t1Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_27 (s : ℚ) :
    termOneCoefficient27 s =
      t1Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient27,
    t1Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_28 (s : ℚ) :
    termOneCoefficient28 s =
      t1Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient28,
    t1Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_29 (s : ℚ) :
    termOneCoefficient29 s =
      t1Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termOneCoefficient29,
    t1Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient1,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_30 (s : ℚ) :
    termOneCoefficient30 s =
      t1Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient1 s := by
  simp only [termOneCoefficient30,
    t1Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient2,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_31 (s : ℚ) :
    termOneCoefficient31 s =
      t1Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient2 s := by
  simp only [termOneCoefficient31,
    t1Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient3,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_32 (s : ℚ) :
    termOneCoefficient32 s =
      t1Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient3 s := by
  simp only [termOneCoefficient32,
    t1Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient4,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_33 (s : ℚ) :
    termOneCoefficient33 s =
      t1Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient4 s := by
  simp only [termOneCoefficient33,
    t1Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient5,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_34 (s : ℚ) :
    termOneCoefficient34 s =
      t1Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient5 s := by
  simp only [termOneCoefficient34,
    t1Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient6,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_35 (s : ℚ) :
    termOneCoefficient35 s =
      t1Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient6 s := by
  simp only [termOneCoefficient35,
    t1Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient7,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_36 (s : ℚ) :
    termOneCoefficient36 s =
      t1Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient7 s := by
  simp only [termOneCoefficient36,
    t1Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient8,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termOneCoefficient_product_certificate_37 (s : ℚ) :
    termOneCoefficient37 s =
      t1Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient8 s := by
  simp only [termOneCoefficient37,
    t1Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termOne_eq_t1Step3_mul_rawUnitTwoDenominator (r s : ℚ) :
    termOne r s =
      t1Step3 r s * rawUnitTwoDenominator r s := by
  have h0 := termOneCoefficient_product_certificate_0 s
  have h1 := termOneCoefficient_product_certificate_1 s
  have h2 := termOneCoefficient_product_certificate_2 s
  have h3 := termOneCoefficient_product_certificate_3 s
  have h4 := termOneCoefficient_product_certificate_4 s
  have h5 := termOneCoefficient_product_certificate_5 s
  have h6 := termOneCoefficient_product_certificate_6 s
  have h7 := termOneCoefficient_product_certificate_7 s
  have h8 := termOneCoefficient_product_certificate_8 s
  have h9 := termOneCoefficient_product_certificate_9 s
  have h10 := termOneCoefficient_product_certificate_10 s
  have h11 := termOneCoefficient_product_certificate_11 s
  have h12 := termOneCoefficient_product_certificate_12 s
  have h13 := termOneCoefficient_product_certificate_13 s
  have h14 := termOneCoefficient_product_certificate_14 s
  have h15 := termOneCoefficient_product_certificate_15 s
  have h16 := termOneCoefficient_product_certificate_16 s
  have h17 := termOneCoefficient_product_certificate_17 s
  have h18 := termOneCoefficient_product_certificate_18 s
  have h19 := termOneCoefficient_product_certificate_19 s
  have h20 := termOneCoefficient_product_certificate_20 s
  have h21 := termOneCoefficient_product_certificate_21 s
  have h22 := termOneCoefficient_product_certificate_22 s
  have h23 := termOneCoefficient_product_certificate_23 s
  have h24 := termOneCoefficient_product_certificate_24 s
  have h25 := termOneCoefficient_product_certificate_25 s
  have h26 := termOneCoefficient_product_certificate_26 s
  have h27 := termOneCoefficient_product_certificate_27 s
  have h28 := termOneCoefficient_product_certificate_28 s
  have h29 := termOneCoefficient_product_certificate_29 s
  have h30 := termOneCoefficient_product_certificate_30 s
  have h31 := termOneCoefficient_product_certificate_31 s
  have h32 := termOneCoefficient_product_certificate_32 s
  have h33 := termOneCoefficient_product_certificate_33 s
  have h34 := termOneCoefficient_product_certificate_34 s
  have h35 := termOneCoefficient_product_certificate_35 s
  have h36 := termOneCoefficient_product_certificate_36 s
  have h37 := termOneCoefficient_product_certificate_37 s
  simp only [termOne, t1Step3, rawUnitTwoDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 +
    r ^ 32 * h32 + r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 +
    r ^ 36 * h36 + r ^ 37 * h37

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 20
    + 4 * s ^ 19
    - 11 * s ^ 18
    + 22 * s ^ 17
    - 36 * s ^ 16
    + 50 * s ^ 15
    - 60 * s ^ 14
    + 64 * s ^ 13
    - 60 * s ^ 12
    + 50 * s ^ 11
    - 36 * s ^ 10
    + 22 * s ^ 9
    - 11 * s ^ 8
    + 4 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient2 (s : ℚ) : ℚ :=
  s ^ 24
    - 7 * s ^ 23
    + 30 * s ^ 22
    - 96 * s ^ 21
    + 245 * s ^ 20
    - 503 * s ^ 19
    + 882 * s ^ 18
    - 1338 * s ^ 17
    + 1814 * s ^ 16
    - 2220 * s ^ 15
    + 2472 * s ^ 14
    - 2514 * s ^ 13
    + 2301 * s ^ 12
    - 1883 * s ^ 11
    + 1336 * s ^ 10
    - 804 * s ^ 9
    + 391 * s ^ 8
    - 139 * s ^ 7
    + 32 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient3 (s : ℚ) : ℚ :=
  -s ^ 26
    + 10 * s ^ 25
    - 53 * s ^ 24
    + 188 * s ^ 23
    - 527 * s ^ 22
    + 1223 * s ^ 21
    - 2424 * s ^ 20
    + 4253 * s ^ 19
    - 6956 * s ^ 18
    + 10691 * s ^ 17
    - 15604 * s ^ 16
    + 21139 * s ^ 15
    - 26187 * s ^ 14
    + 29144 * s ^ 13
    - 28559 * s ^ 12
    + 24374 * s ^ 11
    - 17617 * s ^ 10
    + 10549 * s ^ 9
    - 4928 * s ^ 8
    + 1591 * s ^ 7
    - 258 * s ^ 6
    - 57 * s ^ 5
    + 10 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 26
    + 19 * s ^ 25
    - 125 * s ^ 24
    + 481 * s ^ 23
    - 1234 * s ^ 22
    + 2271 * s ^ 21
    - 2445 * s ^ 20
    - 1434 * s ^ 19
    + 14656 * s ^ 18
    - 42109 * s ^ 17
    + 85747 * s ^ 16
    - 139528 * s ^ 15
    + 190879 * s ^ 14
    - 222585 * s ^ 13
    + 221693 * s ^ 12
    - 187807 * s ^ 11
    + 132046 * s ^ 10
    - 74675 * s ^ 9
    + 30813 * s ^ 8
    - 6996 * s ^ 7
    - 814 * s ^ 6
    + 1363 * s ^ 5
    - 239 * s ^ 4
    + 24 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 26
    + 29 * s ^ 25
    - 300 * s ^ 24
    + 1672 * s ^ 23
    - 6429 * s ^ 22
    + 19454 * s ^ 21
    - 50526 * s ^ 20
    + 114702 * s ^ 19
    - 228575 * s ^ 18
    + 402471 * s ^ 17
    - 631320 * s ^ 16
    + 879674 * s ^ 15
    - 1086984 * s ^ 14
    + 1176591 * s ^ 13
    - 1101049 * s ^ 12
    + 871868 * s ^ 11
    - 558440 * s ^ 10
    + 265696 * s ^ 9
    - 65193 * s ^ 8
    - 21452 * s ^ 7
    + 31014 * s ^ 6
    - 15277 * s ^ 5
    + 2636 * s ^ 4
    - 260 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 27
    + 18 * s ^ 26
    - 154 * s ^ 25
    + 811 * s ^ 24
    - 3149 * s ^ 23
    + 10755 * s ^ 22
    - 34300 * s ^ 21
    + 98170 * s ^ 20
    - 241319 * s ^ 19
    + 513240 * s ^ 18
    - 957247 * s ^ 17
    + 1570796 * s ^ 16
    - 2253165 * s ^ 15
    + 2806339 * s ^ 14
    - 2981225 * s ^ 13
    + 2639515 * s ^ 12
    - 1838403 * s ^ 11
    + 844171 * s ^ 10
    - 19314 * s ^ 9
    - 414733 * s ^ 8
    + 444006 * s ^ 7
    - 270794 * s ^ 6
    + 101129 * s ^ 5
    - 16695 * s ^ 4
    + 1511 * s ^ 3
    + 39 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient7 (s : ℚ) : ℚ :=
  3 * s ^ 26
    - 36 * s ^ 25
    + 124 * s ^ 24
    + 528 * s ^ 23
    - 6864 * s ^ 22
    + 33502 * s ^ 21
    - 109613 * s ^ 20
    + 285489 * s ^ 19
    - 642591 * s ^ 18
    + 1258842 * s ^ 17
    - 2112753 * s ^ 16
    + 2984680 * s ^ 15
    - 3462514 * s ^ 14
    + 3083604 * s ^ 13
    - 1676167 * s ^ 12
    - 481801 * s ^ 11
    + 2610407 * s ^ 10
    - 3820648 * s ^ 9
    + 3723897 * s ^ 8
    - 2609419 * s ^ 7
    + 1306656 * s ^ 6
    - 423921 * s ^ 5
    + 63396 * s ^ 4
    - 4309 * s ^ 3
    - 509 * s ^ 2
    + 17 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient8 (s : ℚ) : ℚ :=
  3 * s ^ 26
    - 62 * s ^ 25
    + 553 * s ^ 24
    - 2822 * s ^ 23
    + 9228 * s ^ 22
    - 22207 * s ^ 21
    + 50702 * s ^ 20
    - 129713 * s ^ 19
    + 314334 * s ^ 18
    - 586293 * s ^ 17
    + 736333 * s ^ 16
    - 306832 * s ^ 15
    - 1319728 * s ^ 14
    + 4617633 * s ^ 13
    - 9401258 * s ^ 12
    + 14550111 * s ^ 11
    - 18025900 * s ^ 10
    + 18055397 * s ^ 9
    - 14462304 * s ^ 8
    + 8928417 * s ^ 7
    - 4031081 * s ^ 6
    + 1159255 * s ^ 5
    - 137525 * s ^ 4
    + 523 * s ^ 3
    + 3348 * s ^ 2
    - 111 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient9 (s : ℚ) : ℚ :=
  s ^ 26
    - 30 * s ^ 25
    + 360 * s ^ 24
    - 2376 * s ^ 23
    + 9643 * s ^ 22
    - 25303 * s ^ 21
    + 47347 * s ^ 20
    - 93426 * s ^ 19
    + 294459 * s ^ 18
    - 1012118 * s ^ 17
    + 2876293 * s ^ 16
    - 6758758 * s ^ 15
    + 13556928 * s ^ 14
    - 23590841 * s ^ 13
    + 35670807 * s ^ 12
    - 46509472 * s ^ 11
    + 51397547 * s ^ 10
    - 47230340 * s ^ 9
    + 35077969 * s ^ 8
    - 20111982 * s ^ 7
    + 8286792 * s ^ 6
    - 2013024 * s ^ 5
    + 99995 * s ^ 4
    + 42402 * s ^ 3
    - 13242 * s ^ 2
    + 356 * s
    + 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient10 (s : ℚ) : ℚ :=
  -5 * s ^ 25
    + 107 * s ^ 24
    - 981 * s ^ 23
    + 4808 * s ^ 22
    - 11143 * s ^ 21
    - 11589 * s ^ 20
    + 198012 * s ^ 19
    - 881093 * s ^ 18
    + 2682952 * s ^ 17
    - 6647637 * s ^ 16
    + 14347682 * s ^ 15
    - 27455354 * s ^ 14
    + 46390693 * s ^ 13
    - 68377670 * s ^ 12
    + 86549067 * s ^ 11
    - 92363227 * s ^ 10
    + 81399786 * s ^ 9
    - 57326952 * s ^ 8
    + 30555353 * s ^ 7
    - 11069638 * s ^ 6
    + 1811322 * s ^ 5
    + 342499 * s ^ 4
    - 170437 * s ^ 3
    + 33952 * s ^ 2
    - 429 * s
    - 78

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient11 (s : ℚ) : ℚ :=
  -2 * s ^ 25
    + 58 * s ^ 24
    - 752 * s ^ 23
    + 5862 * s ^ 22
    - 31186 * s ^ 21
    + 123152 * s ^ 20
    - 392030 * s ^ 19
    + 1100537 * s ^ 18
    - 2910041 * s ^ 17
    + 7283889 * s ^ 16
    - 16629364 * s ^ 15
    + 33440393 * s ^ 14
    - 58109289 * s ^ 13
    + 86198837 * s ^ 12
    - 107887689 * s ^ 11
    + 112290036 * s ^ 10
    - 95058322 * s ^ 9
    + 62802301 * s ^ 8
    - 29871389 * s ^ 7
    + 8066511 * s ^ 6
    + 564028 * s ^ 5
    - 1294641 * s ^ 4
    + 367064 * s ^ 3
    - 57251 * s ^ 2
    - 996 * s
    + 284

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient12 (s : ℚ) : ℚ :=
  3 * s ^ 24
    - 67 * s ^ 23
    + 643 * s ^ 22
    - 3186 * s ^ 21
    + 5302 * s ^ 20
    + 38287 * s ^ 19
    - 352924 * s ^ 18
    + 1623956 * s ^ 17
    - 5306049 * s ^ 16
    + 13596995 * s ^ 15
    - 28554894 * s ^ 14
    + 50064544 * s ^ 13
    - 73521546 * s ^ 12
    + 89886304 * s ^ 11
    - 90056902 * s ^ 10
    + 71553571 * s ^ 9
    - 41970874 * s ^ 8
    + 14799671 * s ^ 7
    + 551900 * s ^ 6
    - 4148767 * s ^ 5
    + 2221791 * s ^ 4
    - 492218 * s ^ 3
    + 59573 * s ^ 2
    + 5582 * s
    - 695

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient13 (s : ℚ) : ℚ :=
  s ^ 24
    - 30 * s ^ 23
    + 421 * s ^ 22
    - 3699 * s ^ 21
    + 22995 * s ^ 20
    - 108658 * s ^ 19
    + 410767 * s ^ 18
    - 1291445 * s ^ 17
    + 3463832 * s ^ 16
    - 8007424 * s ^ 15
    + 15913053 * s ^ 14
    - 26913039 * s ^ 13
    + 38211804 * s ^ 12
    - 44680566 * s ^ 11
    + 41511278 * s ^ 10
    - 28225215 * s ^ 9
    + 10533283 * s ^ 8
    + 3100196 * s ^ 7
    - 8011907 * s ^ 6
    + 5989602 * s ^ 5
    - 2275840 * s ^ 4
    + 397750 * s ^ 3
    - 25748 * s ^ 2
    - 12608 * s
    + 1197

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient14 (s : ℚ) : ℚ :=
  -2 * s ^ 22
    + 57 * s ^ 21
    - 771 * s ^ 20
    + 6564 * s ^ 19
    - 39273 * s ^ 18
    + 174817 * s ^ 17
    - 599401 * s ^ 16
    + 1620339 * s ^ 15
    - 3504749 * s ^ 14
    + 6093195 * s ^ 13
    - 8403427 * s ^ 12
    + 8709872 * s ^ 11
    - 5549553 * s ^ 10
    - 645178 * s ^ 9
    + 6972984 * s ^ 8
    - 9968915 * s ^ 7
    + 8505355 * s ^ 6
    - 4582768 * s ^ 5
    + 1354836 * s ^ 4
    - 136924 * s ^ 3
    - 23226 * s ^ 2
    + 17645 * s
    - 1477

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient15 (s : ℚ) : ℚ :=
  2 * s ^ 19
    - 34 * s ^ 18
    + 248 * s ^ 17
    - 1136 * s ^ 16
    + 5055 * s ^ 15
    - 27692 * s ^ 14
    + 140301 * s ^ 13
    - 540363 * s ^ 12
    + 1539638 * s ^ 11
    - 3288006 * s ^ 10
    + 5341027 * s ^ 9
    - 6644583 * s ^ 8
    + 6256984 * s ^ 7
    - 4246082 * s ^ 6
    + 1820458 * s ^ 5
    - 320137 * s ^ 4
    - 68399 * s ^ 3
    + 47946 * s ^ 2
    - 16530 * s
    + 1303

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient16 (s : ℚ) : ℚ :=
  2 * s ^ 18
    - 54 * s ^ 17
    + 665 * s ^ 16
    - 4993 * s ^ 15
    + 25779 * s ^ 14
    - 97758 * s ^ 13
    + 283291 * s ^ 12
    - 642534 * s ^ 11
    + 1156064 * s ^ 10
    - 1655554 * s ^ 9
    + 1860234 * s ^ 8
    - 1560190 * s ^ 7
    + 855098 * s ^ 6
    - 173315 * s ^ 5
    - 120846 * s ^ 4
    + 102225 * s ^ 3
    - 37723 * s ^ 2
    + 10413 * s
    - 804

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient17 (s : ℚ) : ℚ :=
  -s ^ 16
    + 24 * s ^ 15
    - 261 * s ^ 14
    + 1711 * s ^ 13
    - 7582 * s ^ 12
    + 24022 * s ^ 11
    - 55447 * s ^ 10
    + 91094 * s ^ 9
    - 95721 * s ^ 8
    + 35834 * s ^ 7
    + 64175 * s ^ 6
    - 123343 * s ^ 5
    + 101146 * s ^ 4
    - 47832 * s ^ 3
    + 16089 * s ^ 2
    - 4238 * s
    + 330

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient18 (s : ℚ) : ℚ :=
  s ^ 13
    - 23 * s ^ 12
    + 236 * s ^ 11
    - 1423 * s ^ 10
    + 5593 * s ^ 9
    - 15033 * s ^ 8
    + 28196 * s ^ 7
    - 36950 * s ^ 6
    + 33393 * s ^ 5
    - 20615 * s ^ 4
    + 9240 * s ^ 3
    - 3539 * s ^ 2
    + 1005 * s
    - 81

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient19 (s : ℚ) : ℚ :=
  -s ^ 7
    + 14 * s ^ 6
    - 79 * s ^ 5
    + 229 * s ^ 4
    - 359 * s ^ 3
    + 292 * s ^ 2
    - 105 * s
    + 9

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t2Step1 (r s : ℚ) : ℚ :=
  t2Step1Coefficient0 s +
    t2Step1Coefficient1 s * r +
    t2Step1Coefficient2 s * r ^ 2 +
    t2Step1Coefficient3 s * r ^ 3 +
    t2Step1Coefficient4 s * r ^ 4 +
    t2Step1Coefficient5 s * r ^ 5 +
    t2Step1Coefficient6 s * r ^ 6 +
    t2Step1Coefficient7 s * r ^ 7 +
    t2Step1Coefficient8 s * r ^ 8 +
    t2Step1Coefficient9 s * r ^ 9 +
    t2Step1Coefficient10 s * r ^ 10 +
    t2Step1Coefficient11 s * r ^ 11 +
    t2Step1Coefficient12 s * r ^ 12 +
    t2Step1Coefficient13 s * r ^ 13 +
    t2Step1Coefficient14 s * r ^ 14 +
    t2Step1Coefficient15 s * r ^ 15 +
    t2Step1Coefficient16 s * r ^ 16 +
    t2Step1Coefficient17 s * r ^ 17 +
    t2Step1Coefficient18 s * r ^ 18 +
    t2Step1Coefficient19 s * r ^ 19

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_0 (s : ℚ) :
    t2Step1Coefficient0 s =
      rawUnitNineNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient0,
    rawUnitNineNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_1 (s : ℚ) :
    t2Step1Coefficient1 s =
      rawUnitNineNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient1,
    rawUnitNineNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_2 (s : ℚ) :
    t2Step1Coefficient2 s =
      rawUnitNineNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient2,
    rawUnitNineNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_3 (s : ℚ) :
    t2Step1Coefficient3 s =
      rawUnitNineNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient3,
    rawUnitNineNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_4 (s : ℚ) :
    t2Step1Coefficient4 s =
      rawUnitNineNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient4,
    rawUnitNineNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_5 (s : ℚ) :
    t2Step1Coefficient5 s =
      rawUnitNineNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient5,
    rawUnitNineNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_6 (s : ℚ) :
    t2Step1Coefficient6 s =
      rawUnitNineNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient6,
    rawUnitNineNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_7 (s : ℚ) :
    t2Step1Coefficient7 s =
      rawUnitNineNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient7,
    rawUnitNineNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_8 (s : ℚ) :
    t2Step1Coefficient8 s =
      rawUnitNineNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient8 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient8,
    rawUnitNineNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient8,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_9 (s : ℚ) :
    t2Step1Coefficient9 s =
      rawUnitNineNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient8 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient9 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient9,
    rawUnitNineNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient8,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient9,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_10 (s : ℚ) :
    t2Step1Coefficient10 s =
      rawUnitNineNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient8 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient9 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient10 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient10,
    rawUnitNineNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient8,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient9,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient10,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_11 (s : ℚ) :
    t2Step1Coefficient11 s =
      rawUnitNineNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient8 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient9 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient10 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient11 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient11,
    rawUnitNineNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient8,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient9,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient10,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient11,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_12 (s : ℚ) :
    t2Step1Coefficient12 s =
      rawUnitNineNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient8 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient9 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient10 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient11 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitNineNumeratorCoefficient12 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step1Coefficient12,
    rawUnitNineNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient8,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient9,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient10,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient11,
    rawUnitOneDenominatorCoefficient1,
    rawUnitNineNumeratorCoefficient12,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_13 (s : ℚ) :
    t2Step1Coefficient13 s =
      rawUnitNineNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient8 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient9 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient10 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient11 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitNineNumeratorCoefficient12 s *
          rawUnitOneDenominatorCoefficient1 s := by
  simp only [t2Step1Coefficient13,
    rawUnitNineNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient8,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient9,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient10,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient11,
    rawUnitOneDenominatorCoefficient2,
    rawUnitNineNumeratorCoefficient12,
    rawUnitOneDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_14 (s : ℚ) :
    t2Step1Coefficient14 s =
      rawUnitNineNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient8 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient9 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient10 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient11 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitNineNumeratorCoefficient12 s *
          rawUnitOneDenominatorCoefficient2 s := by
  simp only [t2Step1Coefficient14,
    rawUnitNineNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient8,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient9,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient10,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient11,
    rawUnitOneDenominatorCoefficient3,
    rawUnitNineNumeratorCoefficient12,
    rawUnitOneDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_15 (s : ℚ) :
    t2Step1Coefficient15 s =
      rawUnitNineNumeratorCoefficient8 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient9 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient10 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient11 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitNineNumeratorCoefficient12 s *
          rawUnitOneDenominatorCoefficient3 s := by
  simp only [t2Step1Coefficient15,
    rawUnitNineNumeratorCoefficient8,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient9,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient10,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient11,
    rawUnitOneDenominatorCoefficient4,
    rawUnitNineNumeratorCoefficient12,
    rawUnitOneDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_16 (s : ℚ) :
    t2Step1Coefficient16 s =
      rawUnitNineNumeratorCoefficient9 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient10 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient11 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitNineNumeratorCoefficient12 s *
          rawUnitOneDenominatorCoefficient4 s := by
  simp only [t2Step1Coefficient16,
    rawUnitNineNumeratorCoefficient9,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient10,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient11,
    rawUnitOneDenominatorCoefficient5,
    rawUnitNineNumeratorCoefficient12,
    rawUnitOneDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_17 (s : ℚ) :
    t2Step1Coefficient17 s =
      rawUnitNineNumeratorCoefficient10 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient11 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitNineNumeratorCoefficient12 s *
          rawUnitOneDenominatorCoefficient5 s := by
  simp only [t2Step1Coefficient17,
    rawUnitNineNumeratorCoefficient10,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient11,
    rawUnitOneDenominatorCoefficient6,
    rawUnitNineNumeratorCoefficient12,
    rawUnitOneDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_18 (s : ℚ) :
    t2Step1Coefficient18 s =
      rawUnitNineNumeratorCoefficient11 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitNineNumeratorCoefficient12 s *
          rawUnitOneDenominatorCoefficient6 s := by
  simp only [t2Step1Coefficient18,
    rawUnitNineNumeratorCoefficient11,
    rawUnitOneDenominatorCoefficient7,
    rawUnitNineNumeratorCoefficient12,
    rawUnitOneDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step1Coefficient_product_certificate_19 (s : ℚ) :
    t2Step1Coefficient19 s =
      rawUnitNineNumeratorCoefficient12 s *
          rawUnitOneDenominatorCoefficient7 s := by
  simp only [t2Step1Coefficient19,
    rawUnitNineNumeratorCoefficient12,
    rawUnitOneDenominatorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step1_eq_rawUnitNineNumerator_mul_rawUnitOneDenominator (r s : ℚ) :
    t2Step1 r s =
      rawUnitNineNumerator r s * rawUnitOneDenominator r s := by
  have h0 := t2Step1Coefficient_product_certificate_0 s
  have h1 := t2Step1Coefficient_product_certificate_1 s
  have h2 := t2Step1Coefficient_product_certificate_2 s
  have h3 := t2Step1Coefficient_product_certificate_3 s
  have h4 := t2Step1Coefficient_product_certificate_4 s
  have h5 := t2Step1Coefficient_product_certificate_5 s
  have h6 := t2Step1Coefficient_product_certificate_6 s
  have h7 := t2Step1Coefficient_product_certificate_7 s
  have h8 := t2Step1Coefficient_product_certificate_8 s
  have h9 := t2Step1Coefficient_product_certificate_9 s
  have h10 := t2Step1Coefficient_product_certificate_10 s
  have h11 := t2Step1Coefficient_product_certificate_11 s
  have h12 := t2Step1Coefficient_product_certificate_12 s
  have h13 := t2Step1Coefficient_product_certificate_13 s
  have h14 := t2Step1Coefficient_product_certificate_14 s
  have h15 := t2Step1Coefficient_product_certificate_15 s
  have h16 := t2Step1Coefficient_product_certificate_16 s
  have h17 := t2Step1Coefficient_product_certificate_17 s
  have h18 := t2Step1Coefficient_product_certificate_18 s
  have h19 := t2Step1Coefficient_product_certificate_19 s
  simp only [t2Step1, rawUnitNineNumerator, rawUnitOneDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 30
    + 8 * s ^ 29
    - 37 * s ^ 28
    + 124 * s ^ 27
    - 331 * s ^ 26
    + 740 * s ^ 25
    - 1428 * s ^ 24
    + 2428 * s ^ 23
    - 3689 * s ^ 22
    + 5060 * s ^ 21
    - 6311 * s ^ 20
    + 7192 * s ^ 19
    - 7510 * s ^ 18
    + 7192 * s ^ 17
    - 6311 * s ^ 16
    + 5060 * s ^ 15
    - 3689 * s ^ 14
    + 2428 * s ^ 13
    - 1428 * s ^ 12
    + 740 * s ^ 11
    - 331 * s ^ 10
    + 124 * s ^ 9
    - 37 * s ^ 8
    + 8 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient3 (s : ℚ) : ℚ :=
  s ^ 34
    - 11 * s ^ 33
    + 68 * s ^ 32
    - 304 * s ^ 31
    + 1080 * s ^ 30
    - 3184 * s ^ 29
    + 8035 * s ^ 28
    - 17729 * s ^ 27
    + 34781 * s ^ 26
    - 61463 * s ^ 25
    + 98842 * s ^ 24
    - 145826 * s ^ 23
    + 198561 * s ^ 22
    - 250587 * s ^ 21
    + 293823 * s ^ 20
    - 320345 * s ^ 19
    + 324500 * s ^ 18
    - 304700 * s ^ 17
    + 264233 * s ^ 16
    - 210523 * s ^ 15
    + 153067 * s ^ 14
    - 100681 * s ^ 13
    + 59234 * s ^ 12
    - 30706 * s ^ 11
    + 13730 * s ^ 10
    - 5134 * s ^ 9
    + 1525 * s ^ 8
    - 327 * s ^ 7
    + 40 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 36
    + 14 * s ^ 35
    - 103 * s ^ 34
    + 516 * s ^ 33
    - 2000 * s ^ 32
    + 6395 * s ^ 31
    - 17530 * s ^ 30
    + 42325 * s ^ 29
    - 92063 * s ^ 28
    + 183508 * s ^ 27
    - 339561 * s ^ 26
    + 587889 * s ^ 25
    - 955783 * s ^ 24
    + 1459622 * s ^ 23
    - 2089737 * s ^ 22
    + 2796571 * s ^ 21
    - 3486068 * s ^ 20
    + 4033487 * s ^ 19
    - 4315816 * s ^ 18
    + 4253650 * s ^ 17
    - 3844503 * s ^ 16
    + 3169245 * s ^ 15
    - 2367081 * s ^ 14
    + 1587963 * s ^ 13
    - 945802 * s ^ 12
    + 492152 * s ^ 11
    - 218456 * s ^ 10
    + 79673 * s ^ 9
    - 22274 * s ^ 8
    + 4058 * s ^ 7
    - 196 * s ^ 6
    - 107 * s ^ 5
    + 14 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 36
    + 25 * s ^ 35
    - 231 * s ^ 34
    + 1281 * s ^ 33
    - 4964 * s ^ 32
    + 14537 * s ^ 31
    - 32627 * s ^ 30
    + 52318 * s ^ 29
    - 36291 * s ^ 28
    - 116269 * s ^ 27
    + 606289 * s ^ 26
    - 1749460 * s ^ 25
    + 3938868 * s ^ 24
    - 7529468 * s ^ 23
    + 12653856 * s ^ 22
    - 19030245 * s ^ 21
    + 25859008 * s ^ 20
    - 31914581 * s ^ 19
    + 35854327 * s ^ 18
    - 36666893 * s ^ 17
    + 34068822 * s ^ 16
    - 28648087 * s ^ 15
    + 21669265 * s ^ 14
    - 14610450 * s ^ 13
    + 8665775 * s ^ 12
    - 4431711 * s ^ 11
    + 1891055 * s ^ 10
    - 633504 * s ^ 9
    + 142826 * s ^ 8
    - 8078 * s ^ 7
    - 8334 * s ^ 6
    + 3353 * s ^ 5
    - 443 * s ^ 4
    + 32 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 36
    + 37 * s ^ 35
    - 499 * s ^ 34
    + 3710 * s ^ 33
    - 18965 * s ^ 32
    + 74875 * s ^ 31
    - 246257 * s ^ 30
    + 704776 * s ^ 29
    - 1801586 * s ^ 28
    + 4181664 * s ^ 27
    - 8907651 * s ^ 26
    + 17513819 * s ^ 25
    - 31867145 * s ^ 24
    + 53674836 * s ^ 23
    - 83610956 * s ^ 22
    + 120267582 * s ^ 21
    - 159427210 * s ^ 20
    + 194313014 * s ^ 19
    - 217127357 * s ^ 18
    + 221628467 * s ^ 17
    - 205666275 * s ^ 16
    + 172393116 * s ^ 15
    - 129365972 * s ^ 14
    + 85787575 * s ^ 13
    - 49285429 * s ^ 12
    + 23716149 * s ^ 11
    - 8925124 * s ^ 10
    + 2146168 * s ^ 9
    + 57695 * s ^ 8
    - 350783 * s ^ 7
    + 181633 * s ^ 6
    - 50049 * s ^ 5
    + 6620 * s ^ 4
    - 476 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient7 (s : ℚ) : ℚ :=
  -s ^ 37
    + 22 * s ^ 36
    - 232 * s ^ 35
    + 1512 * s ^ 34
    - 7099 * s ^ 33
    + 28039 * s ^ 32
    - 103751 * s ^ 31
    + 367791 * s ^ 30
    - 1208431 * s ^ 29
    + 3593224 * s ^ 28
    - 9602532 * s ^ 27
    + 23092499 * s ^ 26
    - 50152934 * s ^ 25
    + 98776261 * s ^ 24
    - 177009457 * s ^ 23
    + 289368162 * s ^ 22
    - 432172498 * s ^ 21
    + 589860351 * s ^ 20
    - 735107049 * s ^ 19
    + 834591943 * s ^ 18
    - 859918380 * s ^ 17
    + 799296340 * s ^ 16
    - 664207488 * s ^ 15
    + 486603720 * s ^ 14
    - 307022544 * s ^ 13
    + 159592514 * s ^ 12
    - 61210356 * s ^ 11
    + 10036257 * s ^ 10
    + 7860756 * s ^ 9
    - 8920778 * s ^ 8
    + 5072694 * s ^ 7
    - 1904383 * s ^ 6
    + 461852 * s ^ 5
    - 60197 * s ^ 4
    + 4123 * s ^ 3
    + 51 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient8 (s : ℚ) : ℚ :=
  5 * s ^ 36
    - 82 * s ^ 35
    + 518 * s ^ 34
    - 617 * s ^ 33
    - 12769 * s ^ 32
    + 111520 * s ^ 31
    - 556551 * s ^ 30
    + 2111293 * s ^ 29
    - 6729872 * s ^ 28
    + 18804218 * s ^ 27
    - 46930151 * s ^ 26
    + 105583155 * s ^ 25
    - 215250380 * s ^ 24
    + 398807961 * s ^ 23
    - 672583426 * s ^ 22
    + 1032686752 * s ^ 21
    - 1442013817 * s ^ 20
    + 1826692859 * s ^ 19
    - 2089935327 * s ^ 18
    + 2144287289 * s ^ 17
    - 1950023322 * s ^ 16
    + 1540514862 * s ^ 15
    - 1016484116 * s ^ 14
    + 507830798 * s ^ 13
    - 121864196 * s ^ 12
    - 95108920 * s ^ 11
    + 162230475 * s ^ 10
    - 138127684 * s ^ 9
    + 84020001 * s ^ 8
    - 38344399 * s ^ 7
    + 12846163 * s ^ 6
    - 2903155 * s ^ 5
    + 363422 * s ^ 4
    - 21587 * s ^ 3
    - 945 * s ^ 2
    + 25 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient9 (s : ℚ) : ℚ :=
  5 * s ^ 36
    - 131 * s ^ 35
    + 1514 * s ^ 34
    - 10485 * s ^ 33
    + 50104 * s ^ 32
    - 188225 * s ^ 31
    + 638697 * s ^ 30
    - 2129870 * s ^ 29
    + 6894450 * s ^ 28
    - 20631900 * s ^ 27
    + 55621429 * s ^ 26
    - 134310916 * s ^ 25
    + 290923839 * s ^ 24
    - 566546395 * s ^ 23
    + 993090033 * s ^ 22
    - 1565512937 * s ^ 21
    + 2212515716 * s ^ 20
    - 2784763381 * s ^ 19
    + 3082288919 * s ^ 18
    - 2927195950 * s ^ 17
    + 2255842516 * s ^ 16
    - 1182118802 * s ^ 15
    - 20069692 * s ^ 14
    + 1021323154 * s ^ 13
    - 1579176519 * s ^ 12
    + 1638625171 * s ^ 11
    - 1329508960 * s ^ 10
    + 873557574 * s ^ 9
    - 464253742 * s ^ 8
    + 194688658 * s ^ 7
    - 61262866 * s ^ 6
    + 13052149 * s ^ 5
    - 1501712 * s ^ 4
    + 59261 * s ^ 3
    + 9566 * s ^ 2
    - 271 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient10 (s : ℚ) : ℚ :=
  s ^ 36
    - 48 * s ^ 35
    + 770 * s ^ 34
    - 6413 * s ^ 33
    + 31435 * s ^ 32
    - 87548 * s ^ 31
    + 64144 * s ^ 30
    + 632759 * s ^ 29
    - 3835290 * s ^ 28
    + 14108095 * s ^ 27
    - 41550087 * s ^ 26
    + 105354257 * s ^ 25
    - 234972581 * s ^ 24
    + 462464200 * s ^ 23
    - 798938417 * s ^ 22
    + 1194496581 * s ^ 21
    - 1497665621 * s ^ 20
    + 1446280316 * s ^ 19
    - 730549584 * s ^ 18
    - 861820369 * s ^ 17
    + 3269532474 * s ^ 16
    - 6055939212 * s ^ 15
    + 8494315652 * s ^ 14
    - 9844498326 * s ^ 13
    + 9698007083 * s ^ 12
    - 8185237292 * s ^ 11
    + 5899479203 * s ^ 10
    - 3588218759 * s ^ 9
    + 1802078173 * s ^ 8
    - 720653878 * s ^ 7
    + 215899849 * s ^ 6
    - 42876112 * s ^ 5
    + 4134025 * s ^ 4
    + 31287 * s ^ 3
    - 62482 * s ^ 2
    + 1694 * s
    + 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient11 (s : ℚ) : ℚ :=
  -14 * s ^ 35
    + 390 * s ^ 34
    - 4766 * s ^ 33
    + 34056 * s ^ 32
    - 158642 * s ^ 31
    + 509122 * s ^ 30
    - 1176022 * s ^ 29
    + 2090504 * s ^ 28
    - 3276106 * s ^ 27
    + 5216567 * s ^ 26
    - 6949973 * s ^ 25
    - 2555679 * s ^ 24
    + 66005719 * s ^ 23
    - 296633095 * s ^ 22
    + 927780480 * s ^ 21
    - 2344387782 * s ^ 20
    + 5042138840 * s ^ 19
    - 9452525345 * s ^ 18
    + 15638781556 * s ^ 17
    - 22979922836 * s ^ 16
    + 30068215096 * s ^ 15
    - 35029464143 * s ^ 14
    + 36236394249 * s ^ 13
    - 33106968758 * s ^ 12
    + 26490567712 * s ^ 11
    - 18332113304 * s ^ 10
    + 10775800924 * s ^ 9
    - 5237326175 * s ^ 8
    + 2017766223 * s ^ 7
    - 573002932 * s ^ 6
    + 102143637 * s ^ 5
    - 6153808 * s ^ 4
    - 1105324 * s ^ 3
    + 286436 * s ^ 2
    - 6597 * s
    - 210

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient12 (s : ℚ) : ℚ :=
  -4 * s ^ 35
    + 160 * s ^ 34
    - 2624 * s ^ 33
    + 24507 * s ^ 32
    - 149112 * s ^ 31
    + 637796 * s ^ 30
    - 2048566 * s ^ 29
    + 5426954 * s ^ 28
    - 13697368 * s ^ 27
    + 37412121 * s ^ 26
    - 109600799 * s ^ 25
    + 315604195 * s ^ 24
    - 845295357 * s ^ 23
    + 2068842829 * s ^ 22
    - 4614734981 * s ^ 21
    + 9385260045 * s ^ 20
    - 17399454814 * s ^ 19
    + 29367656123 * s ^ 18
    - 45044011006 * s ^ 17
    + 62623477095 * s ^ 16
    - 78654351049 * s ^ 15
    + 88855464269 * s ^ 14
    - 89749289514 * s ^ 13
    + 80410249078 * s ^ 12
    - 63221893377 * s ^ 11
    + 42985108580 * s ^ 10
    - 24758975711 * s ^ 9
    + 11715792657 * s ^ 8
    - 4334070274 * s ^ 7
    + 1141166146 * s ^ 6
    - 165047503 * s ^ 5
    - 4232241 * s ^ 4
    + 5679643 * s ^ 3
    - 964024 * s ^ 2
    + 14800 * s
    + 1326

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient13 (s : ℚ) : ℚ :=
  22 * s ^ 34
    - 640 * s ^ 33
    + 8258 * s ^ 32
    - 62022 * s ^ 31
    + 293361 * s ^ 30
    - 831535 * s ^ 29
    + 680559 * s ^ 28
    + 6435952 * s ^ 27
    - 42654033 * s ^ 26
    + 169712154 * s ^ 25
    - 540013021 * s ^ 24
    + 1493966913 * s ^ 23
    - 3707623393 * s ^ 22
    + 8346690244 * s ^ 21
    - 17097948325 * s ^ 20
    + 31874665931 * s ^ 19
    - 54031266607 * s ^ 18
    + 83158967351 * s ^ 17
    - 115941621866 * s ^ 16
    + 145942165881 * s ^ 15
    - 165073598501 * s ^ 14
    + 166688524549 * s ^ 13
    - 148966843702 * s ^ 12
    + 116445090713 * s ^ 11
    - 78337121765 * s ^ 10
    + 44314322830 * s ^ 9
    - 20330751586 * s ^ 8
    + 7101617708 * s ^ 7
    - 1637502087 * s ^ 6
    + 126503314 * s ^ 5
    + 53796556 * s ^ 4
    - 18023636 * s ^ 3
    + 2431243 * s ^ 2
    - 4907 * s
    - 5913

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient14 (s : ℚ) : ℚ :=
  6 * s ^ 34
    - 236 * s ^ 33
    + 4056 * s ^ 32
    - 41437 * s ^ 31
    + 287125 * s ^ 30
    - 1464441 * s ^ 29
    + 5901666 * s ^ 28
    - 20313009 * s ^ 27
    + 64641017 * s ^ 26
    - 199634157 * s ^ 25
    + 596904972 * s ^ 24
    - 1678888864 * s ^ 23
    + 4337720770 * s ^ 22
    - 10180560569 * s ^ 21
    + 21630396517 * s ^ 20
    - 41590031359 * s ^ 19
    + 72376795350 * s ^ 18
    - 113921530166 * s ^ 17
    + 161870789382 * s ^ 16
    - 206933381165 * s ^ 15
    + 236820745399 * s ^ 14
    - 240950062758 * s ^ 13
    + 215914552173 * s ^ 12
    - 168221832013 * s ^ 11
    + 111892600589 * s ^ 10
    - 61813233358 * s ^ 9
    + 27076644521 * s ^ 8
    - 8559953298 * s ^ 7
    + 1440403854 * s ^ 6
    + 177960176 * s ^ 5
    - 171674352 * s ^ 4
    + 40920153 * s ^ 3
    - 4584814 * s ^ 2
    - 101467 * s
    + 19737

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient15 (s : ℚ) : ℚ :=
  -17 * s ^ 33
    + 516 * s ^ 32
    - 7002 * s ^ 31
    + 55226 * s ^ 30
    - 267373 * s ^ 29
    + 669555 * s ^ 28
    + 843969 * s ^ 27
    - 17548749 * s ^ 26
    + 101372399 * s ^ 25
    - 409433124 * s ^ 24
    + 1340681402 * s ^ 23
    - 3770889040 * s ^ 22
    + 9360926414 * s ^ 21
    - 20777896446 * s ^ 20
    + 41482103148 * s ^ 19
    - 74634710491 * s ^ 18
    + 120953072656 * s ^ 17
    - 176163517860 * s ^ 16
    + 229724338792 * s ^ 15
    - 266767947779 * s ^ 14
    + 273813371260 * s ^ 13
    - 245861155799 * s ^ 12
    + 190307424679 * s ^ 11
    - 124226477348 * s ^ 10
    + 65959680344 * s ^ 9
    - 26559950222 * s ^ 8
    + 6695248752 * s ^ 7
    - 17805427 * s ^ 6
    - 820587865 * s ^ 5
    + 350953586 * s ^ 4
    - 69169420 * s ^ 3
    + 6219608 * s ^ 2
    + 452662 * s
    - 51006

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient16 (s : ℚ) : ℚ :=
  -4 * s ^ 33
    + 159 * s ^ 32
    - 2866 * s ^ 31
    + 31618 * s ^ 30
    - 242985 * s ^ 29
    + 1409066 * s ^ 28
    - 6570754 * s ^ 27
    + 26116163 * s ^ 26
    - 92975747 * s ^ 25
    + 305486788 * s ^ 24
    - 931802150 * s ^ 23
    + 2615746824 * s ^ 22
    - 6686011800 * s ^ 21
    + 15449303906 * s ^ 20
    - 32140423958 * s ^ 19
    + 60041049811 * s ^ 18
    - 100477747758 * s ^ 17
    + 150198875027 * s ^ 16
    - 199753259219 * s ^ 15
    + 234996490555 * s ^ 14
    - 242554614619 * s ^ 13
    + 217033664692 * s ^ 12
    - 165301455825 * s ^ 11
    + 103994066094 * s ^ 10
    - 51022171111 * s ^ 9
    + 16832587272 * s ^ 8
    - 1339193989 * s ^ 7
    - 2346940793 * s ^ 6
    + 1595117760 * s ^ 5
    - 517112192 * s ^ 4
    + 86848281 * s ^ 3
    - 5192592 * s ^ 2
    - 1179784 * s
    + 104130

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient17 (s : ℚ) : ℚ :=
  5 * s ^ 32
    - 153 * s ^ 31
    + 2062 * s ^ 30
    - 15357 * s ^ 29
    + 57188 * s ^ 28
    + 70655 * s ^ 27
    - 2467850 * s ^ 26
    + 18748097 * s ^ 25
    - 95054429 * s ^ 24
    + 376722170 * s ^ 23
    - 1243354788 * s ^ 22
    + 3529913720 * s ^ 21
    - 8770131159 * s ^ 20
    + 19236562533 * s ^ 19
    - 37400353724 * s ^ 18
    + 64524683628 * s ^ 17
    - 98659151938 * s ^ 16
    + 133219420436 * s ^ 15
    - 157872038702 * s ^ 14
    + 162559852233 * s ^ 13
    - 143132854885 * s ^ 12
    + 104879250568 * s ^ 11
    - 60656002520 * s ^ 10
    + 24107456961 * s ^ 9
    - 2652853478 * s ^ 8
    - 4792329165 * s ^ 7
    + 4395881592 * s ^ 6
    - 2058502896 * s ^ 5
    + 561309616 * s ^ 4
    - 77036852 * s ^ 3
    + 179722 * s ^ 2
    + 2206558 * s
    - 169848

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient18 (s : ℚ) : ℚ :=
  s ^ 32
    - 40 * s ^ 31
    + 748 * s ^ 30
    - 8795 * s ^ 29
    + 73937 * s ^ 28
    - 480687 * s ^ 27
    + 2559867 * s ^ 26
    - 11667192 * s ^ 25
    + 46851538 * s ^ 24
    - 167954594 * s ^ 23
    + 538160983 * s ^ 22
    - 1535866400 * s ^ 21
    + 3891542241 * s ^ 20
    - 8740685936 * s ^ 19
    + 17388870295 * s ^ 18
    - 30595485157 * s ^ 17
    + 47460534601 * s ^ 16
    - 64543318980 * s ^ 15
    + 76232630134 * s ^ 14
    - 76979602224 * s ^ 13
    + 64620432137 * s ^ 12
    - 42541309583 * s ^ 11
    + 18527549161 * s ^ 10
    - 516087443 * s ^ 9
    - 7778378408 * s ^ 8
    + 8058043022 * s ^ 7
    - 4853030257 * s ^ 6
    + 1889632959 * s ^ 5
    - 436642911 * s ^ 4
    + 39304526 * s ^ 3
    + 7251373 * s ^ 2
    - 3141316 * s
    + 222400

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient19 (s : ℚ) : ℚ :=
  -4 * s ^ 30
    + 155 * s ^ 29
    - 2854 * s ^ 28
    + 33340 * s ^ 27
    - 278341 * s ^ 26
    + 1774748 * s ^ 25
    - 9030089 * s ^ 24
    + 37868511 * s ^ 23
    - 134195867 * s ^ 22
    + 409463459 * s ^ 21
    - 1089344260 * s ^ 20
    + 2543796862 * s ^ 19
    - 5222563603 * s ^ 18
    + 9405420975 * s ^ 17
    - 14771957237 * s ^ 16
    + 20021578205 * s ^ 15
    - 22979011720 * s ^ 14
    + 21511842701 * s ^ 13
    - 14983223529 * s ^ 12
    + 5210353121 * s ^ 11
    + 4131949681 * s ^ 10
    - 9600350028 * s ^ 9
    + 10086868216 * s ^ 8
    - 7193876628 * s ^ 7
    + 3626611059 * s ^ 6
    - 1215550031 * s ^ 5
    + 216429267 * s ^ 4
    + 5181341 * s ^ 3
    - 13030149 * s ^ 2
    + 3476261 * s
    - 233562

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient20 (s : ℚ) : ℚ :=
  5 * s ^ 28
    - 186 * s ^ 27
    + 3321 * s ^ 26
    - 37837 * s ^ 25
    + 308101 * s ^ 24
    - 1903555 * s ^ 23
    + 9257465 * s ^ 22
    - 36341721 * s ^ 21
    + 117293553 * s ^ 20
    - 315353434 * s ^ 19
    + 711704097 * s ^ 18
    - 1348709731 * s ^ 17
    + 2121493749 * s ^ 16
    - 2673130181 * s ^ 15
    + 2424516272 * s ^ 14
    - 859066292 * s ^ 13
    - 2013349880 * s ^ 12
    + 5365091641 * s ^ 11
    - 7820973031 * s ^ 10
    + 8280526153 * s ^ 9
    - 6701383836 * s ^ 8
    + 4114095696 * s ^ 7
    - 1813999945 * s ^ 6
    + 491728465 * s ^ 5
    - 31548010 * s ^ 4
    - 31347597 * s ^ 3
    + 13933453 * s ^ 2
    - 3002173 * s
    + 195438

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient21 (s : ℚ) : ℚ :=
  -5 * s ^ 25
    + 110 * s ^ 24
    - 951 * s ^ 23
    + 3451 * s ^ 22
    + 1072 * s ^ 21
    - 32730 * s ^ 20
    - 257552 * s ^ 19
    + 4061360 * s ^ 18
    - 25719301 * s ^ 17
    + 107122978 * s ^ 16
    - 332524059 * s ^ 15
    + 813216154 * s ^ 14
    - 1614268026 * s ^ 13
    + 2642411969 * s ^ 12
    - 3586634495 * s ^ 11
    + 4022516238 * s ^ 10
    - 3679214475 * s ^ 9
    + 2672552249 * s ^ 8
    - 1461109558 * s ^ 7
    + 527150055 * s ^ 6
    - 65915346 * s ^ 5
    - 46916535 * s ^ 4
    + 32075255 * s ^ 3
    - 10397274 * s ^ 2
    + 2008017 * s
    - 128601

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient22 (s : ℚ) : ℚ :=
  -5 * s ^ 24
    + 180 * s ^ 23
    - 3010 * s ^ 22
    + 31263 * s ^ 21
    - 227702 * s ^ 20
    + 1245682 * s ^ 19
    - 5354843 * s ^ 18
    + 18675300 * s ^ 17
    - 54081082 * s ^ 16
    + 132184355 * s ^ 15
    - 275448539 * s ^ 14
    + 491107326 * s ^ 13
    - 746799914 * s ^ 12
    + 958984617 * s ^ 11
    - 1021980951 * s ^ 10
    + 877803942 * s ^ 9
    - 574244852 * s ^ 8
    + 246944345 * s ^ 7
    - 26014559 * s ^ 6
    - 52315617 * s ^ 5
    + 44211602 * s ^ 4
    - 19330539 * s ^ 3
    + 5568486 * s ^ 2
    - 1020582 * s
    + 65097

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient23 (s : ℚ) : ℚ :=
  4 * s ^ 22
    - 135 * s ^ 21
    + 2122 * s ^ 20
    - 20710 * s ^ 19
    + 141193 * s ^ 18
    - 717074 * s ^ 17
    + 2822213 * s ^ 16
    - 8824971 * s ^ 15
    + 22249240 * s ^ 14
    - 45522898 * s ^ 13
    + 75492866 * s ^ 12
    - 100288880 * s ^ 11
    + 103312315 * s ^ 10
    - 75282671 * s ^ 9
    + 25443715 * s ^ 8
    + 21015157 * s ^ 7
    - 41827834 * s ^ 6
    + 35874043 * s ^ 5
    - 19658262 * s ^ 4
    + 7539132 * s ^ 3
    - 2105046 * s ^ 2
    + 380943 * s
    - 24462

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient24 (s : ℚ) : ℚ :=
  -s ^ 20
    + 30 * s ^ 19
    - 411 * s ^ 18
    + 3405 * s ^ 17
    - 19019 * s ^ 16
    + 75321 * s ^ 15
    - 214152 * s ^ 14
    + 417589 * s ^ 13
    - 418174 * s ^ 12
    - 499761 * s ^ 11
    + 3315557 * s ^ 10
    - 8307389 * s ^ 9
    + 13838903 * s ^ 8
    - 16713281 * s ^ 7
    + 14908150 * s ^ 6
    - 9848641 * s ^ 5
    + 4864393 * s ^ 4
    - 1842709 * s ^ 3
    + 532152 * s ^ 2
    - 98388 * s
    + 6426

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient25 (s : ℚ) : ℚ :=
  s ^ 17
    - 31 * s ^ 16
    + 442 * s ^ 15
    - 3841 * s ^ 14
    + 22732 * s ^ 13
    - 97000 * s ^ 12
    + 308252 * s ^ 11
    - 743107 * s ^ 10
    + 1371596 * s ^ 9
    - 1943528 * s ^ 8
    + 2111610 * s ^ 7
    - 1759151 * s ^ 6
    + 1136160 * s ^ 5
    - 586388 * s ^ 4
    + 247728 * s ^ 3
    - 80109 * s ^ 2
    + 15687 * s
    - 1053

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient26 (s : ℚ) : ℚ :=
  -s ^ 11
    + 22 * s ^ 10
    - 213 * s ^ 9
    + 1193 * s ^ 8
    - 4274 * s ^ 7
    + 10224 * s ^ 6
    - 16546 * s ^ 5
    + 17950 * s ^ 4
    - 12621 * s ^ 3
    + 5346 * s ^ 2
    - 1161 * s
    + 81

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t2Step2 (r s : ℚ) : ℚ :=
  t2Step2Coefficient0 s +
    t2Step2Coefficient1 s * r +
    t2Step2Coefficient2 s * r ^ 2 +
    t2Step2Coefficient3 s * r ^ 3 +
    t2Step2Coefficient4 s * r ^ 4 +
    t2Step2Coefficient5 s * r ^ 5 +
    t2Step2Coefficient6 s * r ^ 6 +
    t2Step2Coefficient7 s * r ^ 7 +
    t2Step2Coefficient8 s * r ^ 8 +
    t2Step2Coefficient9 s * r ^ 9 +
    t2Step2Coefficient10 s * r ^ 10 +
    t2Step2Coefficient11 s * r ^ 11 +
    t2Step2Coefficient12 s * r ^ 12 +
    t2Step2Coefficient13 s * r ^ 13 +
    t2Step2Coefficient14 s * r ^ 14 +
    t2Step2Coefficient15 s * r ^ 15 +
    t2Step2Coefficient16 s * r ^ 16 +
    t2Step2Coefficient17 s * r ^ 17 +
    t2Step2Coefficient18 s * r ^ 18 +
    t2Step2Coefficient19 s * r ^ 19 +
    t2Step2Coefficient20 s * r ^ 20 +
    t2Step2Coefficient21 s * r ^ 21 +
    t2Step2Coefficient22 s * r ^ 22 +
    t2Step2Coefficient23 s * r ^ 23 +
    t2Step2Coefficient24 s * r ^ 24 +
    t2Step2Coefficient25 s * r ^ 25 +
    t2Step2Coefficient26 s * r ^ 26

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_0 (s : ℚ) :
    t2Step2Coefficient0 s =
      t2Step1Coefficient0 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient0,
    t2Step1Coefficient0,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_1 (s : ℚ) :
    t2Step2Coefficient1 s =
      t2Step1Coefficient0 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient1 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient1,
    t2Step1Coefficient0,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_2 (s : ℚ) :
    t2Step2Coefficient2 s =
      t2Step1Coefficient0 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient1 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient2 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient2,
    t2Step1Coefficient0,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient1,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient2,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_3 (s : ℚ) :
    t2Step2Coefficient3 s =
      t2Step1Coefficient0 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient1 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient2 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient3 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient3,
    t2Step1Coefficient0,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient1,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient2,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient3,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_4 (s : ℚ) :
    t2Step2Coefficient4 s =
      t2Step1Coefficient0 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient1 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient2 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient3 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient4 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient4,
    t2Step1Coefficient0,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient1,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient2,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient3,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient4,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_5 (s : ℚ) :
    t2Step2Coefficient5 s =
      t2Step1Coefficient0 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient1 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient2 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient3 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient4 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient5 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient5,
    t2Step1Coefficient0,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient1,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient2,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient3,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient4,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient5,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_6 (s : ℚ) :
    t2Step2Coefficient6 s =
      t2Step1Coefficient0 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient1 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient2 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient3 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient4 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient5 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient6 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient6,
    t2Step1Coefficient0,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient1,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient2,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient3,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient4,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient5,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient6,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_7 (s : ℚ) :
    t2Step2Coefficient7 s =
      t2Step1Coefficient0 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient1 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient2 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient3 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient4 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient5 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient6 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient7 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient7,
    t2Step1Coefficient0,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient1,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient2,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient3,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient4,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient5,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient6,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient7,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_8 (s : ℚ) :
    t2Step2Coefficient8 s =
      t2Step1Coefficient1 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient2 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient3 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient4 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient5 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient6 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient7 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient8 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient8,
    t2Step1Coefficient1,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient2,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient3,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient4,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient5,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient6,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient7,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient8,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_9 (s : ℚ) :
    t2Step2Coefficient9 s =
      t2Step1Coefficient2 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient3 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient4 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient5 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient6 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient7 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient8 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient9 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient9,
    t2Step1Coefficient2,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient3,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient4,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient5,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient6,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient7,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient8,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient9,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_10 (s : ℚ) :
    t2Step2Coefficient10 s =
      t2Step1Coefficient3 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient4 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient5 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient6 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient7 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient8 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient9 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient10 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient10,
    t2Step1Coefficient3,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient4,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient5,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient6,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient7,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient8,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient9,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient10,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_11 (s : ℚ) :
    t2Step2Coefficient11 s =
      t2Step1Coefficient4 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient5 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient6 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient7 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient8 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient9 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient10 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient11 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient11,
    t2Step1Coefficient4,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient5,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient6,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient7,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient8,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient9,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient10,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient11,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_12 (s : ℚ) :
    t2Step2Coefficient12 s =
      t2Step1Coefficient5 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient6 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient7 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient8 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient9 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient10 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient11 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient12 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient12,
    t2Step1Coefficient5,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient6,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient7,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient8,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient9,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient10,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient11,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient12,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_13 (s : ℚ) :
    t2Step2Coefficient13 s =
      t2Step1Coefficient6 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient7 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient8 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient9 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient10 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient11 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient12 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient13 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient13,
    t2Step1Coefficient6,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient7,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient8,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient9,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient10,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient11,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient12,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient13,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_14 (s : ℚ) :
    t2Step2Coefficient14 s =
      t2Step1Coefficient7 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient8 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient9 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient10 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient11 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient12 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient13 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient14 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient14,
    t2Step1Coefficient7,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient8,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient9,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient10,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient11,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient12,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient13,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient14,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_15 (s : ℚ) :
    t2Step2Coefficient15 s =
      t2Step1Coefficient8 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient9 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient10 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient11 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient12 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient13 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient14 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient15 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient15,
    t2Step1Coefficient8,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient9,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient10,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient11,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient12,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient13,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient14,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient15,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_16 (s : ℚ) :
    t2Step2Coefficient16 s =
      t2Step1Coefficient9 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient10 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient11 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient12 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient13 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient14 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient15 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient16 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient16,
    t2Step1Coefficient9,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient10,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient11,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient12,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient13,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient14,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient15,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient16,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_17 (s : ℚ) :
    t2Step2Coefficient17 s =
      t2Step1Coefficient10 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient11 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient12 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient13 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient14 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient15 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient16 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient17 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient17,
    t2Step1Coefficient10,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient11,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient12,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient13,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient14,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient15,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient16,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient17,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_18 (s : ℚ) :
    t2Step2Coefficient18 s =
      t2Step1Coefficient11 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient12 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient13 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient14 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient15 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient16 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient17 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient18 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient18,
    t2Step1Coefficient11,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient12,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient13,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient14,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient15,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient16,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient17,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient18,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_19 (s : ℚ) :
    t2Step2Coefficient19 s =
      t2Step1Coefficient12 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient13 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient14 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient15 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient16 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient17 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient18 s *
          rawUnitOneDenominatorCoefficient1 s +
        t2Step1Coefficient19 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [t2Step2Coefficient19,
    t2Step1Coefficient12,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient13,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient14,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient15,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient16,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient17,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient18,
    rawUnitOneDenominatorCoefficient1,
    t2Step1Coefficient19,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_20 (s : ℚ) :
    t2Step2Coefficient20 s =
      t2Step1Coefficient13 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient14 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient15 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient16 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient17 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient18 s *
          rawUnitOneDenominatorCoefficient2 s +
        t2Step1Coefficient19 s *
          rawUnitOneDenominatorCoefficient1 s := by
  simp only [t2Step2Coefficient20,
    t2Step1Coefficient13,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient14,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient15,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient16,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient17,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient18,
    rawUnitOneDenominatorCoefficient2,
    t2Step1Coefficient19,
    rawUnitOneDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_21 (s : ℚ) :
    t2Step2Coefficient21 s =
      t2Step1Coefficient14 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient15 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient16 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient17 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient18 s *
          rawUnitOneDenominatorCoefficient3 s +
        t2Step1Coefficient19 s *
          rawUnitOneDenominatorCoefficient2 s := by
  simp only [t2Step2Coefficient21,
    t2Step1Coefficient14,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient15,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient16,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient17,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient18,
    rawUnitOneDenominatorCoefficient3,
    t2Step1Coefficient19,
    rawUnitOneDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_22 (s : ℚ) :
    t2Step2Coefficient22 s =
      t2Step1Coefficient15 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient16 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient17 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient18 s *
          rawUnitOneDenominatorCoefficient4 s +
        t2Step1Coefficient19 s *
          rawUnitOneDenominatorCoefficient3 s := by
  simp only [t2Step2Coefficient22,
    t2Step1Coefficient15,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient16,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient17,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient18,
    rawUnitOneDenominatorCoefficient4,
    t2Step1Coefficient19,
    rawUnitOneDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_23 (s : ℚ) :
    t2Step2Coefficient23 s =
      t2Step1Coefficient16 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient17 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient18 s *
          rawUnitOneDenominatorCoefficient5 s +
        t2Step1Coefficient19 s *
          rawUnitOneDenominatorCoefficient4 s := by
  simp only [t2Step2Coefficient23,
    t2Step1Coefficient16,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient17,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient18,
    rawUnitOneDenominatorCoefficient5,
    t2Step1Coefficient19,
    rawUnitOneDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_24 (s : ℚ) :
    t2Step2Coefficient24 s =
      t2Step1Coefficient17 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient18 s *
          rawUnitOneDenominatorCoefficient6 s +
        t2Step1Coefficient19 s *
          rawUnitOneDenominatorCoefficient5 s := by
  simp only [t2Step2Coefficient24,
    t2Step1Coefficient17,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient18,
    rawUnitOneDenominatorCoefficient6,
    t2Step1Coefficient19,
    rawUnitOneDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_25 (s : ℚ) :
    t2Step2Coefficient25 s =
      t2Step1Coefficient18 s *
          rawUnitOneDenominatorCoefficient7 s +
        t2Step1Coefficient19 s *
          rawUnitOneDenominatorCoefficient6 s := by
  simp only [t2Step2Coefficient25,
    t2Step1Coefficient18,
    rawUnitOneDenominatorCoefficient7,
    t2Step1Coefficient19,
    rawUnitOneDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step2Coefficient_product_certificate_26 (s : ℚ) :
    t2Step2Coefficient26 s =
      t2Step1Coefficient19 s *
          rawUnitOneDenominatorCoefficient7 s := by
  simp only [t2Step2Coefficient26,
    t2Step1Coefficient19,
    rawUnitOneDenominatorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step2_eq_t2Step1_mul_rawUnitOneDenominator (r s : ℚ) :
    t2Step2 r s =
      t2Step1 r s * rawUnitOneDenominator r s := by
  have h0 := t2Step2Coefficient_product_certificate_0 s
  have h1 := t2Step2Coefficient_product_certificate_1 s
  have h2 := t2Step2Coefficient_product_certificate_2 s
  have h3 := t2Step2Coefficient_product_certificate_3 s
  have h4 := t2Step2Coefficient_product_certificate_4 s
  have h5 := t2Step2Coefficient_product_certificate_5 s
  have h6 := t2Step2Coefficient_product_certificate_6 s
  have h7 := t2Step2Coefficient_product_certificate_7 s
  have h8 := t2Step2Coefficient_product_certificate_8 s
  have h9 := t2Step2Coefficient_product_certificate_9 s
  have h10 := t2Step2Coefficient_product_certificate_10 s
  have h11 := t2Step2Coefficient_product_certificate_11 s
  have h12 := t2Step2Coefficient_product_certificate_12 s
  have h13 := t2Step2Coefficient_product_certificate_13 s
  have h14 := t2Step2Coefficient_product_certificate_14 s
  have h15 := t2Step2Coefficient_product_certificate_15 s
  have h16 := t2Step2Coefficient_product_certificate_16 s
  have h17 := t2Step2Coefficient_product_certificate_17 s
  have h18 := t2Step2Coefficient_product_certificate_18 s
  have h19 := t2Step2Coefficient_product_certificate_19 s
  have h20 := t2Step2Coefficient_product_certificate_20 s
  have h21 := t2Step2Coefficient_product_certificate_21 s
  have h22 := t2Step2Coefficient_product_certificate_22 s
  have h23 := t2Step2Coefficient_product_certificate_23 s
  have h24 := t2Step2Coefficient_product_certificate_24 s
  have h25 := t2Step2Coefficient_product_certificate_25 s
  have h26 := t2Step2Coefficient_product_certificate_26 s
  simp only [t2Step2, t2Step1, rawUnitOneDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient2 (s : ℚ) : ℚ :=
  s ^ 33
    - 8 * s ^ 32
    + 37 * s ^ 31
    - 124 * s ^ 30
    + 331 * s ^ 29
    - 740 * s ^ 28
    + 1428 * s ^ 27
    - 2428 * s ^ 26
    + 3689 * s ^ 25
    - 5060 * s ^ 24
    + 6311 * s ^ 23
    - 7192 * s ^ 22
    + 7510 * s ^ 21
    - 7192 * s ^ 20
    + 6311 * s ^ 19
    - 5060 * s ^ 18
    + 3689 * s ^ 17
    - 2428 * s ^ 16
    + 1428 * s ^ 15
    - 740 * s ^ 14
    + 331 * s ^ 13
    - 124 * s ^ 12
    + 37 * s ^ 11
    - 8 * s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient3 (s : ℚ) : ℚ :=
  -s ^ 37
    + 11 * s ^ 36
    - 68 * s ^ 35
    + 304 * s ^ 34
    - 1079 * s ^ 33
    + 3170 * s ^ 32
    - 7947 * s ^ 31
    + 17358 * s ^ 30
    - 33587 * s ^ 29
    + 58328 * s ^ 28
    - 91857 * s ^ 27
    + 132279 * s ^ 26
    - 175280 * s ^ 25
    + 214681 * s ^ 24
    - 243657 * s ^ 23
    + 256418 * s ^ 22
    - 249845 * s ^ 21
    + 224561 * s ^ 20
    - 185048 * s ^ 19
    + 138511 * s ^ 18
    - 92893 * s ^ 17
    + 54628 * s ^ 16
    - 27111 * s ^ 15
    + 10425 * s ^ 14
    - 2247 * s ^ 13
    - 624 * s ^ 12
    + 989 * s ^ 11
    - 606 * s ^ 10
    + 244 * s ^ 9
    - 67 * s ^ 8
    + 11 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient4 (s : ℚ) : ℚ :=
  s ^ 39
    - 14 * s ^ 38
    + 102 * s ^ 37
    - 499 * s ^ 36
    + 1863 * s ^ 35
    - 5648 * s ^ 34
    + 14398 * s ^ 33
    - 31595 * s ^ 32
    + 60995 * s ^ 31
    - 105619 * s ^ 30
    + 167442 * s ^ 29
    - 247841 * s ^ 28
    + 348291 * s ^ 27
    - 469271 * s ^ 26
    + 605682 * s ^ 25
    - 740918 * s ^ 24
    + 843315 * s ^ 23
    - 871995 * s ^ 22
    + 792356 * s ^ 21
    - 595841 * s ^ 20
    + 312458 * s ^ 19
    - 5148 * s ^ 18
    - 252564 * s ^ 17
    + 406553 * s ^ 16
    - 441850 * s ^ 15
    + 383041 * s ^ 14
    - 276900 * s ^ 13
    + 168645 * s ^ 12
    - 86064 * s ^ 11
    + 36083 * s ^ 10
    - 11988 * s ^ 9
    + 2968 * s ^ 8
    - 481 * s ^ 7
    + 43 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient5 (s : ℚ) : ℚ :=
  2 * s ^ 39
    - 46 * s ^ 38
    + 437 * s ^ 37
    - 2590 * s ^ 36
    + 11130 * s ^ 35
    - 37841 * s ^ 34
    + 106657 * s ^ 33
    - 256035 * s ^ 32
    + 532777 * s ^ 31
    - 974760 * s ^ 30
    + 1586279 * s ^ 29
    - 2324591 * s ^ 28
    + 3114349 * s ^ 27
    - 3901094 * s ^ 26
    + 4723711 * s ^ 25
    - 5755620 * s ^ 24
    + 7268386 * s ^ 23
    - 9488555 * s ^ 22
    + 12409017 * s ^ 21
    - 15651752 * s ^ 20
    + 18498386 * s ^ 19
    - 20124031 * s ^ 18
    + 19934692 * s ^ 17
    - 17849348 * s ^ 16
    + 14349672 * s ^ 15
    - 10279136 * s ^ 14
    + 6496546 * s ^ 13
    - 3572648 * s ^ 12
    + 1676236 * s ^ 11
    - 650826 * s ^ 10
    + 199008 * s ^ 9
    - 43625 * s ^ 8
    + 5255 * s ^ 7
    + 97 * s ^ 6
    - 155 * s ^ 5
    + 17 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient6 (s : ℚ) : ℚ :=
  s ^ 40
    - 17 * s ^ 39
    + 114 * s ^ 38
    - 278 * s ^ 37
    - 888 * s ^ 36
    + 10854 * s ^ 35
    - 53494 * s ^ 34
    + 185706 * s ^ 33
    - 510325 * s ^ 32
    + 1156241 * s ^ 31
    - 2181614 * s ^ 30
    + 3371587 * s ^ 29
    - 3936639 * s ^ 28
    + 2223854 * s ^ 27
    + 4397862 * s ^ 26
    - 19227999 * s ^ 25
    + 45338523 * s ^ 24
    - 84161288 * s ^ 23
    + 133922388 * s ^ 22
    - 188743839 * s ^ 21
    + 239122143 * s ^ 20
    - 274206660 * s ^ 19
    + 285307474 * s ^ 18
    - 269201759 * s ^ 17
    + 229671113 * s ^ 16
    - 176229094 * s ^ 15
    + 120641342 * s ^ 14
    - 72825108 * s ^ 13
    + 38100763 * s ^ 12
    - 16827740 * s ^ 11
    + 5997670 * s ^ 10
    - 1574720 * s ^ 9
    + 227272 * s ^ 8
    + 22672 * s ^ 7
    - 20734 * s ^ 6
    + 5154 * s ^ 5
    - 571 * s ^ 4
    + 34 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 40
    - 51 * s ^ 39
    + 554 * s ^ 38
    - 3453 * s ^ 37
    + 13832 * s ^ 36
    - 37126 * s ^ 35
    + 58928 * s ^ 34
    + 20133 * s ^ 33
    - 559877 * s ^ 32
    + 2561429 * s ^ 31
    - 8353252 * s ^ 30
    + 22634521 * s ^ 29
    - 53780695 * s ^ 28
    + 114888565 * s ^ 27
    - 223618344 * s ^ 26
    + 399314082 * s ^ 25
    - 656498801 * s ^ 24
    + 995295863 * s ^ 23
    - 1391859660 * s ^ 22
    + 1794425560 * s ^ 21
    - 2129795119 * s ^ 20
    + 2322110013 * s ^ 19
    - 2318417176 * s ^ 18
    + 2110400522 * s ^ 17
    - 1741122391 * s ^ 16
    + 1291306512 * s ^ 15
    - 851136060 * s ^ 14
    + 490275764 * s ^ 13
    - 240325581 * s ^ 12
    + 95575150 * s ^ 11
    - 27591441 * s ^ 10
    + 3536799 * s ^ 9
    + 1540015 * s ^ 8
    - 1187945 * s ^ 7
    + 401884 * s ^ 6
    - 81688 * s ^ 5
    + 9071 * s ^ 4
    - 538 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient8 (s : ℚ) : ℚ :=
  2 * s ^ 40
    - 75 * s ^ 39
    + 1142 * s ^ 38
    - 10031 * s ^ 37
    + 59661 * s ^ 36
    - 267767 * s ^ 35
    + 990198 * s ^ 34
    - 3216897 * s ^ 33
    + 9517421 * s ^ 32
    - 25973881 * s ^ 31
    + 65659978 * s ^ 30
    - 154016271 * s ^ 29
    + 335424229 * s ^ 28
    - 678068647 * s ^ 27
    + 1271676671 * s ^ 26
    - 2210964759 * s ^ 25
    + 3561135576 * s ^ 24
    - 5309175731 * s ^ 23
    + 7317945365 * s ^ 22
    - 9310409088 * s ^ 21
    + 10908284554 * s ^ 20
    - 11732096907 * s ^ 19
    + 11532768685 * s ^ 18
    - 10299916338 * s ^ 17
    + 8288223758 * s ^ 16
    - 5937011906 * s ^ 15
    + 3716171951 * s ^ 14
    - 1968873399 * s ^ 13
    + 826808542 * s ^ 12
    - 225494573 * s ^ 11
    - 7927802 * s ^ 10
    + 53537675 * s ^ 9
    - 36391113 * s ^ 8
    + 15157767 * s ^ 7
    - 4267412 * s ^ 6
    + 802285 * s ^ 5
    - 87862 * s ^ 4
    + 4944 * s ^ 3
    + 56 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient9 (s : ℚ) : ℚ :=
  s ^ 41
    - 27 * s ^ 40
    + 341 * s ^ 39
    - 2631 * s ^ 38
    + 14298 * s ^ 37
    - 63654 * s ^ 36
    + 271713 * s ^ 35
    - 1168356 * s ^ 34
    + 4735873 * s ^ 33
    - 17103603 * s ^ 32
    + 54482425 * s ^ 31
    - 154701718 * s ^ 30
    + 395967690 * s ^ 29
    - 920767255 * s ^ 28
    + 1955444034 * s ^ 27
    - 3806549643 * s ^ 26
    + 6808698606 * s ^ 25
    - 11206842428 * s ^ 24
    + 16981304536 * s ^ 23
    - 23674563681 * s ^ 22
    + 30319427283 * s ^ 21
    - 35568587530 * s ^ 20
    + 38059252872 * s ^ 19
    - 36908626169 * s ^ 18
    + 32130559358 * s ^ 17
    - 24734854177 * s ^ 16
    + 16407591507 * s ^ 15
    - 8897762188 * s ^ 14
    + 3401464803 * s ^ 13
    - 253998112 * s ^ 12
    - 964474207 * s ^ 11
    + 1034389515 * s ^ 10
    - 676733847 * s ^ 9
    + 323680113 * s ^ 8
    - 115739007 * s ^ 7
    + 30098630 * s ^ 6
    - 5382956 * s ^ 5
    + 565801 * s ^ 4
    - 27110 * s ^ 3
    - 1127 * s ^ 2
    + 27 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient10 (s : ℚ) : ℚ :=
  -5 * s ^ 40
    + 101 * s ^ 39
    - 764 * s ^ 38
    + 879 * s ^ 37
    + 31086 * s ^ 36
    - 316930 * s ^ 35
    + 1836446 * s ^ 34
    - 7947657 * s ^ 33
    + 28739025 * s ^ 32
    - 91950906 * s ^ 31
    + 266364966 * s ^ 30
    - 702498339 * s ^ 29
    + 1689282737 * s ^ 28
    - 3709552769 * s ^ 27
    + 7451341478 * s ^ 26
    - 13707708714 * s ^ 25
    + 23103326854 * s ^ 24
    - 35649646006 * s ^ 23
    + 50270012202 * s ^ 22
    - 64563180631 * s ^ 21
    + 75111092823 * s ^ 20
    - 78457631976 * s ^ 19
    + 72497869956 * s ^ 18
    - 57665153652 * s ^ 17
    + 37175733604 * s ^ 16
    - 16008664284 * s ^ 15
    - 1002588314 * s ^ 14
    + 11015752909 * s ^ 13
    - 13969292077 * s ^ 12
    + 12010196008 * s ^ 11
    - 8037422510 * s ^ 10
    + 4312243454 * s ^ 9
    - 1846905989 * s ^ 8
    + 615271073 * s ^ 7
    - 152107250 * s ^ 6
    + 25877150 * s ^ 5
    - 2488281 * s ^ 4
    + 72209 * s ^ 3
    + 12414 * s ^ 2
    - 319 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient11 (s : ℚ) : ℚ :=
  -5 * s ^ 40
    + 155 * s ^ 39
    - 2146 * s ^ 38
    + 17803 * s ^ 37
    - 100740 * s ^ 36
    + 433019 * s ^ 35
    - 1620399 * s ^ 34
    + 6038877 * s ^ 33
    - 22935744 * s ^ 32
    + 82577098 * s ^ 31
    - 266862266 * s ^ 30
    + 765174713 * s ^ 29
    - 1959982033 * s ^ 28
    + 4520929726 * s ^ 27
    - 9435471495 * s ^ 26
    + 17848409712 * s ^ 25
    - 30579447080 * s ^ 24
    + 47309531617 * s ^ 23
    - 65696403550 * s ^ 22
    + 80963536733 * s ^ 21
    - 86635286570 * s ^ 20
    + 76708867445 * s ^ 19
    - 48696573444 * s ^ 18
    + 6068542285 * s ^ 17
    + 41687584054 * s ^ 16
    - 82098856903 * s ^ 15
    + 104754694078 * s ^ 14
    - 105737559725 * s ^ 13
    + 88851623790 * s ^ 12
    - 63046110089 * s ^ 11
    + 37707960698 * s ^ 10
    - 18775095664 * s ^ 9
    + 7609581744 * s ^ 8
    - 2421400655 * s ^ 7
    + 571789010 * s ^ 6
    - 90813968 * s ^ 5
    + 7186617 * s ^ 4
    + 129675 * s ^ 3
    - 88590 * s ^ 2
    + 2194 * s
    + 23

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient12 (s : ℚ) : ℚ :=
  -s ^ 40
    + 53 * s ^ 39
    - 1001 * s ^ 38
    + 10065 * s ^ 37
    - 60847 * s ^ 36
    + 217142 * s ^ 35
    - 283699 * s ^ 34
    - 1601730 * s ^ 33
    + 12848133 * s ^ 32
    - 54995527 * s ^ 31
    + 183203303 * s ^ 30
    - 528546953 * s ^ 29
    + 1366461055 * s ^ 28
    - 3174238017 * s ^ 27
    + 6576173327 * s ^ 26
    - 12011734576 * s ^ 25
    + 18977903175 * s ^ 24
    - 24890590492 * s ^ 23
    + 24020909691 * s ^ 22
    - 7453972890 * s ^ 21
    - 34791446763 * s ^ 20
    + 109149312506 * s ^ 19
    - 212765968443 * s ^ 18
    + 329855944692 * s ^ 17
    - 433724776578 * s ^ 16
    + 495454472570 * s ^ 15
    - 496143557483 * s ^ 14
    + 436102810059 * s ^ 13
    - 335142801579 * s ^ 12
    + 223295276827 * s ^ 11
    - 127286384273 * s ^ 10
    + 60892781616 * s ^ 9
    - 23778377396 * s ^ 8
    + 7266142546 * s ^ 7
    - 1622485330 * s ^ 6
    + 229395491 * s ^ 5
    - 10201250 * s ^ 4
    - 2273712 * s ^ 3
    + 446084 * s ^ 2
    - 9542 * s
    - 253

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient13 (s : ℚ) : ℚ :=
  14 * s ^ 39
    - 456 * s ^ 38
    + 6636 * s ^ 37
    - 57215 * s ^ 36
    + 324363 * s ^ 35
    - 1261702 * s ^ 34
    + 3386779 * s ^ 33
    - 6045237 * s ^ 32
    + 6117639 * s ^ 31
    + 536813 * s ^ 30
    - 21407143 * s ^ 29
    + 110616418 * s ^ 28
    - 533837481 * s ^ 27
    + 2181047820 * s ^ 26
    - 7385370901 * s ^ 25
    + 21219741667 * s ^ 24
    - 52997727138 * s ^ 23
    + 117017556201 * s ^ 22
    - 230822906864 * s ^ 21
    + 409280828904 * s ^ 20
    - 654613306472 * s ^ 19
    + 945872209356 * s ^ 18
    - 1234679140006 * s ^ 17
    + 1453836436641 * s ^ 16
    - 1539623072035 * s ^ 15
    + 1459588121563 * s ^ 14
    - 1230556022533 * s ^ 13
    + 914410799548 * s ^ 12
    - 591797545800 * s ^ 11
    + 328253923350 * s ^ 10
    - 152630618996 * s ^ 9
    + 57625238340 * s ^ 8
    - 16794572546 * s ^ 7
    + 3443310679 * s ^ 6
    - 380132066 * s ^ 5
    - 17655561 * s ^ 4
    + 12111104 * s ^ 3
    - 1660320 * s ^ 2
    + 24870 * s
    + 1767

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient14 (s : ℚ) : ℚ :=
  4 * s ^ 39
    - 180 * s ^ 38
    + 3432 * s ^ 37
    - 38075 * s ^ 36
    + 279677 * s ^ 35
    - 1459396 * s ^ 34
    + 5700032 * s ^ 33
    - 17770888 * s ^ 32
    + 49446458 * s ^ 31
    - 142953904 * s ^ 30
    + 458322158 * s ^ 29
    - 1508499647 * s ^ 28
    + 4679269661 * s ^ 27
    - 13250714910 * s ^ 26
    + 34164731062 * s ^ 25
    - 80527249701 * s ^ 24
    + 174054867981 * s ^ 23
    - 345345547922 * s ^ 22
    + 628718677631 * s ^ 21
    - 1049012147305 * s ^ 20
    + 1601472610880 * s ^ 19
    - 2232269079556 * s ^ 18
    + 2833026163585 * s ^ 17
    - 3261648328597 * s ^ 16
    + 3390161918870 * s ^ 15
    - 3161687860964 * s ^ 14
    + 2624761649702 * s ^ 13
    - 1920017624757 * s ^ 12
    + 1221215103797 * s ^ 11
    - 663398148918 * s ^ 10
    + 300147815742 * s ^ 9
    - 108861773895 * s ^ 8
    + 29600179683 * s ^ 7
    - 5165202038 * s ^ 6
    + 218483373 * s ^ 5
    + 156339432 * s ^ 4
    - 41807907 * s ^ 3
    + 4672236 * s ^ 2
    - 18061 * s
    - 8775

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient15 (s : ℚ) : ℚ :=
  -22 * s ^ 38
    + 744 * s ^ 37
    - 11367 * s ^ 36
    + 103150 * s ^ 35
    - 606748 * s ^ 34
    + 2284849 * s ^ 33
    - 4135649 * s ^ 32
    - 10661645 * s ^ 31
    + 124993180 * s ^ 30
    - 626708908 * s ^ 29
    + 2355218285 * s ^ 28
    - 7518139658 * s ^ 27
    + 21422324732 * s ^ 26
    - 55570100604 * s ^ 25
    + 132051038310 * s ^ 24
    - 287776257166 * s ^ 23
    + 574926691568 * s ^ 22
    - 1052241225667 * s ^ 21
    + 1762727398707 * s ^ 20
    - 2699311704401 * s ^ 19
    + 3770900247954 * s ^ 18
    - 4791851426077 * s ^ 17
    + 5517079334076 * s ^ 16
    - 5725458497263 * s ^ 15
    + 5320093582160 * s ^ 14
    - 4388690296088 * s ^ 13
    + 3178849965715 * s ^ 12
    - 1992340571198 * s ^ 11
    + 1058695870666 * s ^ 10
    - 462764685972 * s ^ 9
    + 158141560686 * s ^ 8
    - 37931520486 * s ^ 7
    + 4250191630 * s ^ 6
    + 908375295 * s ^ 5
    - 528114596 * s ^ 4
    + 105563547 * s ^ 3
    - 9954912 * s ^ 2
    - 159716 * s
    + 32889

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient16 (s : ℚ) : ℚ :=
  -6 * s ^ 38
    + 266 * s ^ 37
    - 5269 * s ^ 36
    + 63088 * s ^ 35
    - 518733 * s ^ 34
    + 3158634 * s ^ 33
    - 15110362 * s ^ 32
    + 60315121 * s ^ 31
    - 214858249 * s ^ 30
    + 725580696 * s ^ 29
    - 2384771217 * s ^ 28
    + 7531418121 * s ^ 27
    - 22261926475 * s ^ 26
    + 60464666950 * s ^ 25
    - 149753790897 * s ^ 24
    + 337717186332 * s ^ 23
    - 693968554155 * s ^ 22
    + 1300526081917 * s ^ 21
    - 2223096258891 * s ^ 20
    + 3463212323008 * s ^ 19
    - 4907241848825 * s ^ 18
    + 6305500521661 * s ^ 17
    - 7316671277395 * s ^ 16
    + 7625172968303 * s ^ 15
    - 7087129035749 * s ^ 14
    + 5820993381162 * s ^ 13
    - 4173939295869 * s ^ 12
    + 2569193734957 * s ^ 11
    - 1324126501883 * s ^ 10
    + 548486776148 * s ^ 9
    - 168153072209 * s ^ 8
    + 29473502672 * s ^ 7
    + 2479786479 * s ^ 6
    - 3596710585 * s ^ 5
    + 1198068742 * s ^ 4
    - 202356706 * s ^ 3
    + 15572956 * s ^ 2
    + 882655 * s
    - 96393

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient17 (s : ℚ) : ℚ :=
  17 * s ^ 37
    - 597 * s ^ 36
    + 9547 * s ^ 35
    - 90957 * s ^ 34
    + 557026 * s ^ 33
    - 2071631 * s ^ 32
    + 2081750 * s ^ 31
    + 30564848 * s ^ 30
    - 262506360 * s ^ 29
    + 1334218248 * s ^ 28
    - 5245600640 * s ^ 27
    + 17357466389 * s ^ 26
    - 50294256730 * s ^ 25
    + 130250498966 * s ^ 24
    - 304638017101 * s ^ 23
    + 646642965836 * s ^ 22
    - 1247996715977 * s ^ 21
    + 2189825816336 * s ^ 20
    - 3488882444643 * s ^ 19
    + 5035521191465 * s ^ 18
    - 6562372286207 * s ^ 17
    + 7688367080780 * s ^ 16
    - 8051358623284 * s ^ 15
    + 7479408656752 * s ^ 14
    - 6100682724888 * s ^ 13
    + 4307080353442 * s ^ 12
    - 2576471128288 * s ^ 11
    + 1260905504059 * s ^ 10
    - 471102110632 * s ^ 9
    + 109915805522 * s ^ 8
    + 2415693151 * s ^ 7
    - 15561764388 * s ^ 6
    + 7548677300 * s ^ 5
    - 2013760721 * s ^ 4
    + 295221508 * s ^ 3
    - 15782788 * s ^ 2
    - 2702989 * s
    + 225879

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient18 (s : ℚ) : ℚ :=
  4 * s ^ 37
    - 179 * s ^ 36
    + 3691 * s ^ 35
    - 47172 * s ^ 34
    + 423753 * s ^ 33
    - 2882831 * s ^ 32
    + 15698545 * s ^ 31
    - 71830184 * s ^ 30
    + 288693201 * s ^ 29
    - 1055885365 * s ^ 28
    + 3582633620 * s ^ 27
    - 11303629020 * s ^ 26
    + 32929674524 * s ^ 25
    - 87848096609 * s ^ 24
    + 213393180458 * s ^ 23
    - 470483094142 * s ^ 22
    + 939748143897 * s ^ 21
    - 1698006401779 * s ^ 20
    + 2770758857294 * s ^ 19
    - 4073785880730 * s ^ 18
    + 5379478539271 * s ^ 17
    - 6351479353039 * s ^ 16
    + 6663385202994 * s ^ 15
    - 6157470380508 * s ^ 14
    + 4949125236927 * s ^ 13
    - 3394322337383 * s ^ 12
    + 1923511502833 * s ^ 11
    - 844306816708 * s ^ 10
    + 237826486900 * s ^ 9
    + 2301560913 * s ^ 8
    - 47498253545 * s ^ 7
    + 30126971226 * s ^ 6
    - 11097773809 * s ^ 5
    + 2567734634 * s ^ 4
    - 316886866 * s ^ 3
    + 3489446 * s ^ 2
    + 5944852 * s
    - 429114

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient19 (s : ℚ) : ℚ :=
  -5 * s ^ 36
    + 177 * s ^ 35
    - 2826 * s ^ 34
    + 26073 * s ^ 33
    - 139745 * s ^ 32
    + 233049 * s ^ 31
    + 3190601 * s ^ 30
    - 37103015 * s ^ 29
    + 239350518 * s ^ 28
    - 1153295541 * s ^ 27
    + 4537256504 * s ^ 26
    - 15211791333 * s ^ 25
    + 44518461336 * s ^ 24
    - 115314941374 * s ^ 23
    + 266428360803 * s ^ 22
    - 551302794352 * s ^ 21
    + 1023458455951 * s ^ 20
    - 1704621081825 * s ^ 19
    + 2543302274242 * s ^ 18
    - 3388549173687 * s ^ 17
    + 4011129356883 * s ^ 16
    - 4186018481323 * s ^ 15
    + 3806452912306 * s ^ 14
    - 2960254718273 * s ^ 13
    + 1905436631020 * s ^ 12
    - 946651989447 * s ^ 11
    + 289795427511 * s ^ 10
    + 29714099507 * s ^ 9
    - 109192552800 * s ^ 8
    + 81414246896 * s ^ 7
    - 37996138554 * s ^ 6
    + 12090553360 * s ^ 5
    - 2449676888 * s ^ 4
    + 219646284 * s ^ 3
    + 22812549 * s ^ 2
    - 10080808 * s
    + 666226

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient20 (s : ℚ) : ℚ :=
  -s ^ 36
    + 45 * s ^ 35
    - 957 * s ^ 34
    + 12903 * s ^ 33
    - 124980 * s ^ 32
    + 936237 * s ^ 31
    - 5714096 * s ^ 30
    + 29574468 * s ^ 29
    - 133749566 * s ^ 28
    + 538727348 * s ^ 27
    - 1949602222 * s ^ 26
    + 6348765777 * s ^ 25
    - 18575831531 * s ^ 24
    + 48755757604 * s ^ 23
    - 114706417730 * s ^ 22
    + 241824962457 * s ^ 21
    - 456566580134 * s ^ 20
    + 770773250992 * s ^ 19
    - 1160073089359 * s ^ 18
    + 1548995673424 * s ^ 17
    - 1820729150104 * s ^ 16
    + 1860722712196 * s ^ 15
    - 1619063019934 * s ^ 14
    + 1152439060088 * s ^ 13
    - 608591719678 * s ^ 12
    + 153593837833 * s ^ 11
    + 111907190418 * s ^ 10
    - 189487878785 * s ^ 9
    + 152850141465 * s ^ 8
    - 85101643197 * s ^ 7
    + 34377534408 * s ^ 6
    - 9733336101 * s ^ 5
    + 1632852467 * s ^ 4
    - 32089090 * s ^ 3
    - 53750192 * s ^ 2
    + 13555737 * s
    - 848210

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient21 (s : ℚ) : ℚ :=
  4 * s ^ 34
    - 175 * s ^ 33
    + 3666 * s ^ 32
    - 49066 * s ^ 31
    + 472319 * s ^ 30
    - 3491486 * s ^ 29
    + 20680234 * s ^ 28
    - 101197801 * s ^ 27
    + 418894708 * s ^ 26
    - 1494240823 * s ^ 25
    + 4658714323 * s ^ 24
    - 12821151476 * s ^ 23
    + 31327707738 * s ^ 22
    - 68120689547 * s ^ 21
    + 131755560217 * s ^ 20
    - 226020028075 * s ^ 19
    + 341982649303 * s ^ 18
    - 452084965691 * s ^ 17
    + 513605620651 * s ^ 16
    - 485965716183 * s ^ 15
    + 356150010785 * s ^ 14
    - 155399271411 * s ^ 13
    - 49483648473 * s ^ 12
    + 190137150098 * s ^ 11
    - 234039399100 * s ^ 10
    + 197481682182 * s ^ 9
    - 126014784018 * s ^ 8
    + 61554086653 * s ^ 7
    - 22356580106 * s ^ 6
    + 5465941748 * s ^ 5
    - 566800218 * s ^ 4
    - 146860742 * s ^ 3
    + 73431373 * s ^ 2
    - 14616573 * s
    + 884962

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient22 (s : ℚ) : ℚ :=
  -5 * s ^ 32
    + 211 * s ^ 31
    - 4300 * s ^ 30
    + 56291 * s ^ 29
    - 530778 * s ^ 28
    + 3831454 * s ^ 27
    - 21983034 * s ^ 26
    + 102837385 * s ^ 25
    - 399588520 * s ^ 24
    + 1307857729 * s ^ 23
    - 3643375200 * s ^ 22
    + 8696579668 * s ^ 21
    - 17823572292 * s ^ 20
    + 31220507289 * s ^ 19
    - 46000124804 * s ^ 18
    + 54748634510 * s ^ 17
    - 46702940708 * s ^ 16
    + 13012266510 * s ^ 15
    + 45640412648 * s ^ 14
    - 114556486502 * s ^ 13
    + 169335438090 * s ^ 12
    - 188777249994 * s ^ 11
    + 167902571674 * s ^ 10
    - 120520191198 * s ^ 9
    + 69099220728 * s ^ 8
    - 30665363304 * s ^ 7
    + 9765437628 * s ^ 6
    - 1698286613 * s ^ 5
    - 192985860 * s ^ 4
    + 226985777 * s ^ 3
    - 71857620 * s ^ 2
    + 12656179 * s
    - 753039

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient23 (s : ℚ) : ℚ :=
  5 * s ^ 29
    - 130 * s ^ 28
    + 1365 * s ^ 27
    - 6105 * s ^ 26
    - 8544 * s ^ 25
    + 261375 * s ^ 24
    - 1381227 * s ^ 23
    + 1512318 * s ^ 22
    + 25271395 * s ^ 21
    - 209994950 * s ^ 20
    + 981640648 * s ^ 19
    - 3348465697 * s ^ 18
    + 9031510085 * s ^ 17
    - 20004455737 * s ^ 16
    + 37148370103 * s ^ 15
    - 58484650312 * s ^ 14
    + 78414707162 * s ^ 13
    - 89474143306 * s ^ 12
    + 86405778920 * s ^ 11
    - 69837352884 * s ^ 10
    + 46330862703 * s ^ 9
    - 24372660923 * s ^ 8
    + 9458036196 * s ^ 7
    - 2130945764 * s ^ 6
    - 211175762 * s ^ 5
    + 430584006 * s ^ 4
    - 198002485 * s ^ 3
    + 52938292 * s ^ 2
    - 8748484 * s
    + 517737

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient24 (s : ℚ) : ℚ :=
  5 * s ^ 28
    - 205 * s ^ 27
    + 3955 * s ^ 26
    - 47962 * s ^ 25
    + 412106 * s ^ 24
    - 2681853 * s ^ 23
    + 13800915 * s ^ 22
    - 57904458 * s ^ 21
    + 202681650 * s ^ 20
    - 602385680 * s ^ 19
    + 1540547641 * s ^ 18
    - 3421572072 * s ^ 17
    + 6633293832 * s ^ 16
    - 11235421817 * s ^ 15
    + 16579209569 * s ^ 14
    - 21182615232 * s ^ 13
    + 23212866842 * s ^ 12
    - 21512136085 * s ^ 11
    + 16484154602 * s ^ 10
    - 10030661240 * s ^ 9
    + 4422566515 * s ^ 8
    - 971290596 * s ^ 7
    - 403304852 * s ^ 6
    + 560056674 * s ^ 5
    - 323134765 * s ^ 4
    + 118678964 * s ^ 3
    - 29597094 * s ^ 2
    + 4763898 * s
    - 283257

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient25 (s : ℚ) : ℚ :=
  -4 * s ^ 26
    + 155 * s ^ 25
    - 2838 * s ^ 24
    + 32732 * s ^ 23
    - 267435 * s ^ 22
    + 1650044 * s ^ 21
    - 7999069 * s ^ 20
    + 31282319 * s ^ 19
    - 100480040 * s ^ 18
    + 268322518 * s ^ 17
    - 600346123 * s ^ 16
    + 1130029034 * s ^ 15
    - 1790015574 * s ^ 14
    + 2374669847 * s ^ 13
    - 2602698827 * s ^ 12
    + 2284372953 * s ^ 11
    - 1485953268 * s ^ 10
    + 532741735 * s ^ 9
    + 196547456 * s ^ 8
    - 515901716 * s ^ 7
    + 493097757 * s ^ 6
    - 317405229 * s ^ 5
    + 148227378 * s ^ 4
    - 50414650 * s ^ 3
    + 12388380 * s ^ 2
    - 1997982 * s
    + 120447

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient26 (s : ℚ) : ℚ :=
  s ^ 24
    - 35 * s ^ 23
    + 574 * s ^ 22
    - 5869 * s ^ 21
    + 41986 * s ^ 20
    - 223438 * s ^ 19
    + 916932 * s ^ 18
    - 2959611 * s ^ 17
    + 7547887 * s ^ 16
    - 14936274 * s ^ 15
    + 21334816 * s ^ 14
    - 15741420 * s ^ 13
    - 17737472 * s ^ 12
    + 87356651 * s ^ 11
    - 178199436 * s ^ 10
    + 253117406 * s ^ 9
    - 277321041 * s ^ 8
    + 243651223 * s ^ 7
    - 173484998 * s ^ 6
    + 98828881 * s ^ 5
    - 43870370 * s ^ 4
    + 14853929 * s ^ 3
    - 3754224 * s ^ 2
    + 622269 * s
    - 38367

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient27 (s : ℚ) : ℚ :=
  -s ^ 21
    + 35 * s ^ 20
    - 576 * s ^ 19
    + 5923 * s ^ 18
    - 42636 * s ^ 17
    + 228040 * s ^ 16
    - 938767 * s ^ 15
    + 3041826 * s ^ 14
    - 7877302 * s ^ 13
    + 16498653 * s ^ 12
    - 28264845 * s ^ 11
    + 40109201 * s ^ 10
    - 47800758 * s ^ 9
    + 48363851 * s ^ 8
    - 41530385 * s ^ 7
    + 29747516 * s ^ 6
    - 17263765 * s ^ 5
    + 7917600 * s ^ 4
    - 2840755 * s ^ 3
    + 773910 * s ^ 2
    - 135378 * s
    + 8613

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient28 (s : ℚ) : ℚ :=
  s ^ 17
    - 31 * s ^ 16
    + 443 * s ^ 15
    - 3868 * s ^ 14
    + 23064 * s ^ 13
    - 99460 * s ^ 12
    + 320498 * s ^ 11
    - 786334 * s ^ 10
    + 1482926 * s ^ 9
    - 2155706 * s ^ 8
    + 2412339 * s ^ 7
    - 2075784 * s ^ 6
    + 1382532 * s ^ 5
    - 726772 * s ^ 4
    + 305208 * s ^ 3
    - 96174 * s ^ 2
    + 18333 * s
    - 1215

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient29 (s : ℚ) : ℚ :=
  -s ^ 11
    + 22 * s ^ 10
    - 213 * s ^ 9
    + 1193 * s ^ 8
    - 4274 * s ^ 7
    + 10224 * s ^ 6
    - 16546 * s ^ 5
    + 17950 * s ^ 4
    - 12621 * s ^ 3
    + 5346 * s ^ 2
    - 1161 * s
    + 81

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t2Step3 (r s : ℚ) : ℚ :=
  t2Step3Coefficient0 s +
    t2Step3Coefficient1 s * r +
    t2Step3Coefficient2 s * r ^ 2 +
    t2Step3Coefficient3 s * r ^ 3 +
    t2Step3Coefficient4 s * r ^ 4 +
    t2Step3Coefficient5 s * r ^ 5 +
    t2Step3Coefficient6 s * r ^ 6 +
    t2Step3Coefficient7 s * r ^ 7 +
    t2Step3Coefficient8 s * r ^ 8 +
    t2Step3Coefficient9 s * r ^ 9 +
    t2Step3Coefficient10 s * r ^ 10 +
    t2Step3Coefficient11 s * r ^ 11 +
    t2Step3Coefficient12 s * r ^ 12 +
    t2Step3Coefficient13 s * r ^ 13 +
    t2Step3Coefficient14 s * r ^ 14 +
    t2Step3Coefficient15 s * r ^ 15 +
    t2Step3Coefficient16 s * r ^ 16 +
    t2Step3Coefficient17 s * r ^ 17 +
    t2Step3Coefficient18 s * r ^ 18 +
    t2Step3Coefficient19 s * r ^ 19 +
    t2Step3Coefficient20 s * r ^ 20 +
    t2Step3Coefficient21 s * r ^ 21 +
    t2Step3Coefficient22 s * r ^ 22 +
    t2Step3Coefficient23 s * r ^ 23 +
    t2Step3Coefficient24 s * r ^ 24 +
    t2Step3Coefficient25 s * r ^ 25 +
    t2Step3Coefficient26 s * r ^ 26 +
    t2Step3Coefficient27 s * r ^ 27 +
    t2Step3Coefficient28 s * r ^ 28 +
    t2Step3Coefficient29 s * r ^ 29

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_0 (s : ℚ) :
    t2Step3Coefficient0 s =
      t2Step2Coefficient0 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient0,
    t2Step2Coefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_1 (s : ℚ) :
    t2Step3Coefficient1 s =
      t2Step2Coefficient0 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient1 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient1,
    t2Step2Coefficient0,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_2 (s : ℚ) :
    t2Step3Coefficient2 s =
      t2Step2Coefficient0 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient1 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient2 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient2,
    t2Step2Coefficient0,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient1,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient2,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_3 (s : ℚ) :
    t2Step3Coefficient3 s =
      t2Step2Coefficient0 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient1 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient2 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient3 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient3,
    t2Step2Coefficient0,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient1,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient2,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient3,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_4 (s : ℚ) :
    t2Step3Coefficient4 s =
      t2Step2Coefficient1 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient2 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient3 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient4 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient4,
    t2Step2Coefficient1,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient2,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient3,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient4,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_5 (s : ℚ) :
    t2Step3Coefficient5 s =
      t2Step2Coefficient2 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient3 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient4 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient5 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient5,
    t2Step2Coefficient2,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient3,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient4,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient5,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_6 (s : ℚ) :
    t2Step3Coefficient6 s =
      t2Step2Coefficient3 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient4 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient5 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient6 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient6,
    t2Step2Coefficient3,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient4,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient5,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient6,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_7 (s : ℚ) :
    t2Step3Coefficient7 s =
      t2Step2Coefficient4 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient5 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient6 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient7 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient7,
    t2Step2Coefficient4,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient5,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient6,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient7,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_8 (s : ℚ) :
    t2Step3Coefficient8 s =
      t2Step2Coefficient5 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient6 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient7 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient8 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient8,
    t2Step2Coefficient5,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient6,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient7,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient8,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_9 (s : ℚ) :
    t2Step3Coefficient9 s =
      t2Step2Coefficient6 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient7 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient8 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient9 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient9,
    t2Step2Coefficient6,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient7,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient8,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient9,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_10 (s : ℚ) :
    t2Step3Coefficient10 s =
      t2Step2Coefficient7 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient8 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient9 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient10 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient10,
    t2Step2Coefficient7,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient8,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient9,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient10,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_11 (s : ℚ) :
    t2Step3Coefficient11 s =
      t2Step2Coefficient8 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient9 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient10 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient11 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient11,
    t2Step2Coefficient8,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient9,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient10,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient11,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_12 (s : ℚ) :
    t2Step3Coefficient12 s =
      t2Step2Coefficient9 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient10 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient11 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient12 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient12,
    t2Step2Coefficient9,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient10,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient11,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient12,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_13 (s : ℚ) :
    t2Step3Coefficient13 s =
      t2Step2Coefficient10 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient11 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient12 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient13 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient13,
    t2Step2Coefficient10,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient11,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient12,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient13,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_14 (s : ℚ) :
    t2Step3Coefficient14 s =
      t2Step2Coefficient11 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient12 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient13 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient14 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient14,
    t2Step2Coefficient11,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient12,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient13,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient14,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_15 (s : ℚ) :
    t2Step3Coefficient15 s =
      t2Step2Coefficient12 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient13 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient14 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient15 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient15,
    t2Step2Coefficient12,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient13,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient14,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient15,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_16 (s : ℚ) :
    t2Step3Coefficient16 s =
      t2Step2Coefficient13 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient14 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient15 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient16 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient16,
    t2Step2Coefficient13,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient14,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient15,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient16,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_17 (s : ℚ) :
    t2Step3Coefficient17 s =
      t2Step2Coefficient14 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient15 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient16 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient17 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient17,
    t2Step2Coefficient14,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient15,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient16,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient17,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_18 (s : ℚ) :
    t2Step3Coefficient18 s =
      t2Step2Coefficient15 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient16 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient17 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient18 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient18,
    t2Step2Coefficient15,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient16,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient17,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient18,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_19 (s : ℚ) :
    t2Step3Coefficient19 s =
      t2Step2Coefficient16 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient17 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient18 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient19 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient19,
    t2Step2Coefficient16,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient17,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient18,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient19,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_20 (s : ℚ) :
    t2Step3Coefficient20 s =
      t2Step2Coefficient17 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient18 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient19 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient20 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient20,
    t2Step2Coefficient17,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient18,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient19,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient20,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_21 (s : ℚ) :
    t2Step3Coefficient21 s =
      t2Step2Coefficient18 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient19 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient20 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient21 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient21,
    t2Step2Coefficient18,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient19,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient20,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient21,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_22 (s : ℚ) :
    t2Step3Coefficient22 s =
      t2Step2Coefficient19 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient20 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient21 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient22 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient22,
    t2Step2Coefficient19,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient20,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient21,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient22,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_23 (s : ℚ) :
    t2Step3Coefficient23 s =
      t2Step2Coefficient20 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient21 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient22 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient23 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient23,
    t2Step2Coefficient20,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient21,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient22,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient23,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_24 (s : ℚ) :
    t2Step3Coefficient24 s =
      t2Step2Coefficient21 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient22 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient23 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient24 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient24,
    t2Step2Coefficient21,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient22,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient23,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient24,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_25 (s : ℚ) :
    t2Step3Coefficient25 s =
      t2Step2Coefficient22 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient23 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient24 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient25 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient25,
    t2Step2Coefficient22,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient23,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient24,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient25,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_26 (s : ℚ) :
    t2Step3Coefficient26 s =
      t2Step2Coefficient23 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient24 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient25 s *
          rawUnitEightDenominatorCoefficient1 s +
        t2Step2Coefficient26 s *
          rawUnitEightDenominatorCoefficient0 s := by
  simp only [t2Step3Coefficient26,
    t2Step2Coefficient23,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient24,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient25,
    rawUnitEightDenominatorCoefficient1,
    t2Step2Coefficient26,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_27 (s : ℚ) :
    t2Step3Coefficient27 s =
      t2Step2Coefficient24 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient25 s *
          rawUnitEightDenominatorCoefficient2 s +
        t2Step2Coefficient26 s *
          rawUnitEightDenominatorCoefficient1 s := by
  simp only [t2Step3Coefficient27,
    t2Step2Coefficient24,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient25,
    rawUnitEightDenominatorCoefficient2,
    t2Step2Coefficient26,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_28 (s : ℚ) :
    t2Step3Coefficient28 s =
      t2Step2Coefficient25 s *
          rawUnitEightDenominatorCoefficient3 s +
        t2Step2Coefficient26 s *
          rawUnitEightDenominatorCoefficient2 s := by
  simp only [t2Step3Coefficient28,
    t2Step2Coefficient25,
    rawUnitEightDenominatorCoefficient3,
    t2Step2Coefficient26,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t2Step3Coefficient_product_certificate_29 (s : ℚ) :
    t2Step3Coefficient29 s =
      t2Step2Coefficient26 s *
          rawUnitEightDenominatorCoefficient3 s := by
  simp only [t2Step3Coefficient29,
    t2Step2Coefficient26,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step3_eq_t2Step2_mul_rawUnitEightDenominator (r s : ℚ) :
    t2Step3 r s =
      t2Step2 r s * rawUnitEightDenominator r s := by
  have h0 := t2Step3Coefficient_product_certificate_0 s
  have h1 := t2Step3Coefficient_product_certificate_1 s
  have h2 := t2Step3Coefficient_product_certificate_2 s
  have h3 := t2Step3Coefficient_product_certificate_3 s
  have h4 := t2Step3Coefficient_product_certificate_4 s
  have h5 := t2Step3Coefficient_product_certificate_5 s
  have h6 := t2Step3Coefficient_product_certificate_6 s
  have h7 := t2Step3Coefficient_product_certificate_7 s
  have h8 := t2Step3Coefficient_product_certificate_8 s
  have h9 := t2Step3Coefficient_product_certificate_9 s
  have h10 := t2Step3Coefficient_product_certificate_10 s
  have h11 := t2Step3Coefficient_product_certificate_11 s
  have h12 := t2Step3Coefficient_product_certificate_12 s
  have h13 := t2Step3Coefficient_product_certificate_13 s
  have h14 := t2Step3Coefficient_product_certificate_14 s
  have h15 := t2Step3Coefficient_product_certificate_15 s
  have h16 := t2Step3Coefficient_product_certificate_16 s
  have h17 := t2Step3Coefficient_product_certificate_17 s
  have h18 := t2Step3Coefficient_product_certificate_18 s
  have h19 := t2Step3Coefficient_product_certificate_19 s
  have h20 := t2Step3Coefficient_product_certificate_20 s
  have h21 := t2Step3Coefficient_product_certificate_21 s
  have h22 := t2Step3Coefficient_product_certificate_22 s
  have h23 := t2Step3Coefficient_product_certificate_23 s
  have h24 := t2Step3Coefficient_product_certificate_24 s
  have h25 := t2Step3Coefficient_product_certificate_25 s
  have h26 := t2Step3Coefficient_product_certificate_26 s
  have h27 := t2Step3Coefficient_product_certificate_27 s
  have h28 := t2Step3Coefficient_product_certificate_28 s
  have h29 := t2Step3Coefficient_product_certificate_29 s
  simp only [t2Step3, t2Step2, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient2 (s : ℚ) : ℚ :=
  s ^ 41
    - 8 * s ^ 40
    + 37 * s ^ 39
    - 124 * s ^ 38
    + 331 * s ^ 37
    - 740 * s ^ 36
    + 1428 * s ^ 35
    - 2428 * s ^ 34
    + 3689 * s ^ 33
    - 5060 * s ^ 32
    + 6311 * s ^ 31
    - 7192 * s ^ 30
    + 7510 * s ^ 29
    - 7192 * s ^ 28
    + 6311 * s ^ 27
    - 5060 * s ^ 26
    + 3689 * s ^ 25
    - 2428 * s ^ 24
    + 1428 * s ^ 23
    - 740 * s ^ 22
    + 331 * s ^ 21
    - 124 * s ^ 20
    + 37 * s ^ 19
    - 8 * s ^ 18
    + s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 45
    + 11 * s ^ 44
    - 68 * s ^ 43
    + 304 * s ^ 42
    - 1076 * s ^ 41
    + 3129 * s ^ 40
    - 7690 * s ^ 39
    + 16271 * s ^ 38
    - 30065 * s ^ 37
    + 48994 * s ^ 36
    - 70820 * s ^ 35
    + 90924 * s ^ 34
    - 103100 * s ^ 33
    + 101389 * s ^ 32
    - 82222 * s ^ 31
    + 46109 * s ^ 30
    + 1914 * s ^ 29
    - 53340 * s ^ 28
    + 98394 * s ^ 27
    - 128823 * s ^ 26
    + 140178 * s ^ 25
    - 132921 * s ^ 24
    + 111824 * s ^ 23
    - 83976 * s ^ 22
    + 56301 * s ^ 21
    - 33564 * s ^ 20
    + 17670 * s ^ 19
    - 8133 * s ^ 18
    + 3230 * s ^ 17
    - 1089 * s ^ 16
    + 304 * s ^ 15
    - 68 * s ^ 14
    + 11 * s ^ 13
    - s ^ 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient4 (s : ℚ) : ℚ :=
  s ^ 47
    - 14 * s ^ 46
    + 99 * s ^ 45
    - 448 * s ^ 44
    + 1448 * s ^ 43
    - 3358 * s ^ 42
    + 4680 * s ^ 41
    + 2052 * s ^ 40
    - 37225 * s ^ 39
    + 141952 * s ^ 38
    - 381008 * s ^ 37
    + 835312 * s ^ 36
    - 1580715 * s ^ 35
    + 2657598 * s ^ 34
    - 4042742 * s ^ 33
    + 5634584 * s ^ 32
    - 7260826 * s ^ 31
    + 8705006 * s ^ 30
    - 9747044 * s ^ 29
    + 10208180 * s ^ 28
    - 9992233 * s ^ 27
    + 9115810 * s ^ 26
    - 7713665 * s ^ 25
    + 6013876 * s ^ 24
    - 4281628 * s ^ 23
    + 2750566 * s ^ 22
    - 1567430 * s ^ 21
    + 770828 * s ^ 20
    - 310252 * s ^ 19
    + 88388 * s ^ 18
    - 5506 * s ^ 17
    - 13160 * s ^ 16
    + 10634 * s ^ 15
    - 5246 * s ^ 14
    + 1927 * s ^ 13
    - 536 * s ^ 12
    + 108 * s ^ 11
    - 14 * s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 48
    + 22 * s ^ 47
    - 260 * s ^ 46
    + 1984 * s ^ 45
    - 10908 * s ^ 44
    + 46395 * s ^ 43
    - 160987 * s ^ 42
    + 471487 * s ^ 41
    - 1192098 * s ^ 40
    + 2646340 * s ^ 39
    - 5233764 * s ^ 38
    + 9340772 * s ^ 37
    - 15228290 * s ^ 36
    + 22939956 * s ^ 35
    - 32272948 * s ^ 34
    + 42793105 * s ^ 33
    - 53826835 * s ^ 32
    + 64401182 * s ^ 31
    - 73158305 * s ^ 30
    + 78420013 * s ^ 29
    - 78523081 * s ^ 28
    + 72425589 * s ^ 27
    - 60341923 * s ^ 26
    + 44005854 * s ^ 25
    - 26331853 * s ^ 24
    + 10499473 * s ^ 23
    + 1098430 * s ^ 22
    - 7551543 * s ^ 21
    + 9463461 * s ^ 20
    - 8381037 * s ^ 19
    + 6017102 * s ^ 18
    - 3644020 * s ^ 17
    + 1884585 * s ^ 16
    - 832349 * s ^ 15
    + 310915 * s ^ 14
    - 96382 * s ^ 13
    + 23774 * s ^ 12
    - 4323 * s ^ 11
    + 492 * s ^ 10
    - 22 * s ^ 9
    - 2 * s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient6 (s : ℚ) : ℚ :=
  s ^ 50
    - 20 * s ^ 49
    + 208 * s ^ 48
    - 1464 * s ^ 47
    + 7670 * s ^ 46
    - 31136 * s ^ 45
    + 100155 * s ^ 44
    - 257795 * s ^ 43
    + 524918 * s ^ 42
    - 785636 * s ^ 41
    + 583881 * s ^ 40
    + 1071122 * s ^ 39
    - 5654527 * s ^ 38
    + 14593137 * s ^ 37
    - 28219448 * s ^ 36
    + 44747124 * s ^ 35
    - 60120070 * s ^ 34
    + 69620791 * s ^ 33
    - 71164341 * s ^ 32
    + 68782576 * s ^ 31
    - 73980916 * s ^ 30
    + 102703333 * s ^ 29
    - 168193862 * s ^ 28
    + 272471860 * s ^ 27
    - 401246552 * s ^ 26
    + 526144525 * s ^ 25
    - 614226507 * s ^ 24
    + 640956456 * s ^ 23
    - 599858386 * s ^ 22
    + 504277244 * s ^ 21
    - 380658068 * s ^ 20
    + 257401018 * s ^ 19
    - 155243267 * s ^ 18
    + 82946552 * s ^ 17
    - 38881835 * s ^ 16
    + 15763371 * s ^ 15
    - 5401690 * s ^ 14
    + 1503498 * s ^ 13
    - 310977 * s ^ 12
    + 36495 * s ^ 11
    + 1938 * s ^ 10
    - 1656 * s ^ 9
    + 298 * s ^ 8
    - 19 * s ^ 7
    + s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 50
    - 60 * s ^ 49
    + 797 * s ^ 48
    - 6766 * s ^ 47
    + 42046 * s ^ 46
    - 204093 * s ^ 45
    + 802594 * s ^ 44
    - 2625621 * s ^ 43
    + 7298823 * s ^ 42
    - 17517924 * s ^ 41
    + 36659066 * s ^ 40
    - 67292279 * s ^ 39
    + 108875631 * s ^ 38
    - 156334845 * s ^ 37
    + 202429268 * s ^ 36
    - 246801738 * s ^ 35
    + 311243294 * s ^ 34
    - 456209654 * s ^ 33
    + 787366715 * s ^ 32
    - 1439975807 * s ^ 31
    + 2535195310 * s ^ 30
    - 4115159589 * s ^ 29
    + 6082768871 * s ^ 28
    - 8178303730 * s ^ 27
    + 10020312807 * s ^ 26
    - 11209668834 * s ^ 25
    + 11461523412 * s ^ 24
    - 10710118077 * s ^ 23
    + 9134299623 * s ^ 22
    - 7091979030 * s ^ 21
    + 4992813038 * s ^ 20
    - 3169182662 * s ^ 19
    + 1799640552 * s ^ 18
    - 904175343 * s ^ 17
    + 395429344 * s ^ 16
    - 146562231 * s ^ 15
    + 43714153 * s ^ 14
    - 9186357 * s ^ 13
    + 600701 * s ^ 12
    + 471551 * s ^ 11
    - 230344 * s ^ 10
    + 54131 * s ^ 9
    - 7078 * s ^ 8
    + 336 * s ^ 7
    - s ^ 6
    - 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient8 (s : ℚ) : ℚ :=
  s ^ 51
    - 23 * s ^ 50
    + 233 * s ^ 49
    - 1252 * s ^ 48
    + 2482 * s ^ 47
    + 18201 * s ^ 46
    - 213887 * s ^ 45
    + 1260475 * s ^ 44
    - 5363223 * s ^ 43
    + 18154410 * s ^ 42
    - 51148619 * s ^ 41
    + 122708355 * s ^ 40
    - 252217845 * s ^ 39
    + 439395907 * s ^ 38
    - 621571469 * s ^ 37
    + 608702281 * s ^ 36
    - 9354952 * s ^ 35
    - 1819780610 * s ^ 34
    + 5754434549 * s ^ 33
    - 12759984112 * s ^ 32
    + 23602918715 * s ^ 31
    - 38452883759 * s ^ 30
    + 56495467222 * s ^ 29
    - 75749307842 * s ^ 28
    + 93259629604 * s ^ 27
    - 105738888042 * s ^ 26
    + 110502941252 * s ^ 25
    - 106368507370 * s ^ 24
    + 94123052154 * s ^ 23
    - 76314181551 * s ^ 22
    + 56430166085 * s ^ 21
    - 37808868542 * s ^ 20
    + 22745779799 * s ^ 19
    - 12124833999 * s ^ 18
    + 5607168595 * s ^ 17
    - 2164742084 * s ^ 16
    + 637541282 * s ^ 15
    - 99065876 * s ^ 14
    - 28436078 * s ^ 13
    + 30374115 * s ^ 12
    - 13653959 * s ^ 11
    + 3941876 * s ^ 10
    - 722194 * s ^ 9
    + 69319 * s ^ 8
    + 926 * s ^ 7
    - 614 * s ^ 6
    + 63 * s ^ 5
    + s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient9 (s : ℚ) : ℚ :=
  2 * s ^ 51
    - 65 * s ^ 50
    + 946 * s ^ 49
    - 8392 * s ^ 48
    + 51401 * s ^ 47
    - 230053 * s ^ 46
    + 750187 * s ^ 45
    - 1577697 * s ^ 44
    + 413735 * s ^ 43
    + 14123386 * s ^ 42
    - 80283388 * s ^ 41
    + 302852669 * s ^ 40
    - 930123722 * s ^ 39
    + 2482188026 * s ^ 38
    - 5936257538 * s ^ 37
    + 12953741595 * s ^ 36
    - 26087728163 * s ^ 35
    + 48834287528 * s ^ 34
    - 85319306013 * s ^ 33
    + 139396804177 * s ^ 32
    - 213105985207 * s ^ 31
    + 304746706259 * s ^ 30
    - 407273572629 * s ^ 29
    + 507985009531 * s ^ 28
    - 590282814951 * s ^ 27
    + 637598070688 * s ^ 26
    - 638400944787 * s ^ 25
    + 590412240979 * s ^ 24
    - 502048190917 * s ^ 23
    + 390147678546 * s ^ 22
    - 274786647084 * s ^ 21
    + 173291713816 * s ^ 20
    - 95983695091 * s ^ 19
    + 45076270949 * s ^ 18
    - 16537918452 * s ^ 17
    + 3447963845 * s ^ 16
    + 949894687 * s ^ 15
    - 1527093284 * s ^ 14
    + 990913142 * s ^ 13
    - 448468929 * s ^ 12
    + 149727334 * s ^ 11
    - 35321834 * s ^ 10
    + 4976252 * s ^ 9
    - 130136 * s ^ 8
    - 94100 * s ^ 7
    + 13638 * s ^ 6
    - 844 * s ^ 5
    - 42 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient10 (s : ℚ) : ℚ :=
  2 * s ^ 51
    - 91 * s ^ 50
    + 1756 * s ^ 49
    - 20279 * s ^ 48
    + 163181 * s ^ 47
    - 999487 * s ^ 46
    + 4934983 * s ^ 45
    - 20434327 * s ^ 44
    + 73225711 * s ^ 43
    - 233645852 * s ^ 42
    + 680347339 * s ^ 41
    - 1838820463 * s ^ 40
    + 4652458106 * s ^ 39
    - 11056192431 * s ^ 38
    + 24710662021 * s ^ 37
    - 51950152593 * s ^ 36
    + 102649542763 * s ^ 35
    - 190368737758 * s ^ 34
    + 330869754595 * s ^ 33
    - 538207175196 * s ^ 32
    + 818381115211 * s ^ 31
    - 1161857871046 * s ^ 30
    + 1537954393132 * s ^ 29
    - 1894849647799 * s ^ 28
    + 2167977109864 * s ^ 27
    - 2296489852052 * s ^ 26
    + 2242910270261 * s ^ 25
    - 2008261779462 * s ^ 24
    + 1635073318706 * s ^ 23
    - 1195479021234 * s ^ 22
    + 768701948985 * s ^ 21
    - 417269465199 * s ^ 20
    + 172127950282 * s ^ 19
    - 31405185319 * s ^ 18
    - 29193248789 * s ^ 17
    + 41416041359 * s ^ 16
    - 32401039933 * s ^ 15
    + 19140755673 * s ^ 14
    - 9038692899 * s ^ 13
    + 3396553610 * s ^ 12
    - 965108267 * s ^ 11
    + 180889952 * s ^ 10
    - 11134894 * s ^ 9
    - 4496479 * s ^ 8
    + 1425775 * s ^ 7
    - 146787 * s ^ 6
    + 4478 * s ^ 5
    + 892 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient11 (s : ℚ) : ℚ :=
  s ^ 52
    - 33 * s ^ 51
    + 520 * s ^ 50
    - 5129 * s ^ 49
    + 35705 * s ^ 48
    - 190907 * s ^ 47
    + 848912 * s ^ 46
    - 3415377 * s ^ 45
    + 13424288 * s ^ 44
    - 53243892 * s ^ 43
    + 207117367 * s ^ 42
    - 752266271 * s ^ 41
    + 2476030269 * s ^ 40
    - 7340835389 * s ^ 39
    + 19720164344 * s ^ 38
    - 48375909652 * s ^ 37
    + 108991397300 * s ^ 36
    - 226399990762 * s ^ 35
    + 434802576764 * s ^ 34
    - 773635529692 * s ^ 33
    + 1277015311284 * s ^ 32
    - 1956607809998 * s ^ 31
    + 2781519973528 * s ^ 30
    - 3663753604676 * s ^ 29
    + 4459944479321 * s ^ 28
    - 4997357375073 * s ^ 27
    + 5122486432830 * s ^ 26
    - 4757099264488 * s ^ 25
    + 3938120863624 * s ^ 24
    - 2818633707020 * s ^ 23
    + 1623959003169 * s ^ 22
    - 578760586486 * s ^ 21
    - 163354022772 * s ^ 20
    + 556404228274 * s ^ 19
    - 653309468025 * s ^ 18
    + 562554637199 * s ^ 17
    - 396555888073 * s ^ 16
    + 235894583391 * s ^ 15
    - 118600099661 * s ^ 14
    + 49442834863 * s ^ 13
    - 16287806097 * s ^ 12
    + 3759555883 * s ^ 11
    - 360549607 * s ^ 10
    - 121720259 * s ^ 9
    + 60874443 * s ^ 8
    - 11957197 * s ^ 7
    + 857546 * s ^ 6
    + 27728 * s ^ 5
    - 12021 * s ^ 4
    + 3 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient12 (s : ℚ) : ℚ :=
  -7 * s ^ 51
    + 194 * s ^ 50
    - 2443 * s ^ 49
    + 17505 * s ^ 48
    - 67536 * s ^ 47
    - 7129 * s ^ 46
    + 2075815 * s ^ 45
    - 17074719 * s ^ 44
    + 91468275 * s ^ 43
    - 383901304 * s ^ 42
    + 1357354887 * s ^ 41
    - 4227942743 * s ^ 40
    + 11953467768 * s ^ 39
    - 31159026681 * s ^ 38
    + 75237596094 * s ^ 37
    - 168297302179 * s ^ 36
    + 348660265845 * s ^ 35
    - 669057879479 * s ^ 34
    + 1189011668448 * s ^ 33
    - 1954784395452 * s ^ 32
    + 2966063262173 * s ^ 31
    - 4137340078196 * s ^ 30
    + 5272878282924 * s ^ 29
    - 6078661394180 * s ^ 28
    + 6228118099761 * s ^ 27
    - 5474498698931 * s ^ 26
    + 3771612693099 * s ^ 25
    - 1344865852308 * s ^ 24
    - 1339288252553 * s ^ 23
    + 3710269123278 * s ^ 22
    - 5286517715321 * s ^ 21
    + 5837663305684 * s ^ 20
    - 5439263703212 * s ^ 19
    + 4403267683497 * s ^ 18
    - 3127812830983 * s ^ 17
    + 1948341967627 * s ^ 16
    - 1053886200598 * s ^ 15
    + 483981508711 * s ^ 14
    - 180191846087 * s ^ 13
    + 48706682095 * s ^ 12
    - 5947165282 * s ^ 11
    - 2143484113 * s ^ 10
    + 1496851416 * s ^ 9
    - 429369069 * s ^ 8
    + 62933296 * s ^ 7
    - 1503315 * s ^ 6
    - 725809 * s ^ 5
    + 110715 * s ^ 4
    + 558 * s ^ 3
    - 36 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient13 (s : ℚ) : ℚ :=
  -5 * s ^ 51
    + 194 * s ^ 50
    - 3391 * s ^ 49
    + 36263 * s ^ 48
    - 269821 * s ^ 47
    + 1508267 * s ^ 46
    - 6699199 * s ^ 45
    + 24815113 * s ^ 44
    - 80862264 * s ^ 43
    + 248790001 * s ^ 42
    - 775473447 * s ^ 41
    + 2480915053 * s ^ 40
    - 7736754004 * s ^ 39
    + 22275273026 * s ^ 38
    - 57858010498 * s ^ 37
    + 135471038201 * s ^ 36
    - 287458025507 * s ^ 35
    + 554087051006 * s ^ 34
    - 967321743250 * s ^ 33
    + 1515682900780 * s ^ 32
    - 2092742552669 * s ^ 31
    + 2447730866293 * s ^ 30
    - 2172577165323 * s ^ 29
    + 764048241092 * s ^ 28
    + 2217187375087 * s ^ 27
    - 6919816685084 * s ^ 26
    + 12996280804307 * s ^ 25
    - 19541393119842 * s ^ 24
    + 25266026410580 * s ^ 23
    - 28881509185563 * s ^ 22
    + 29553264150833 * s ^ 21
    - 27211750253169 * s ^ 20
    + 22563913230297 * s ^ 19
    - 16802834528268 * s ^ 18
    + 11160771846788 * s ^ 17
    - 6528198689045 * s ^ 16
    + 3285061254645 * s ^ 15
    - 1358129983148 * s ^ 14
    + 412704312627 * s ^ 13
    - 55255858550 * s ^ 12
    - 28201846895 * s ^ 11
    + 23590946261 * s ^ 10
    - 8968680950 * s ^ 9
    + 1968397513 * s ^ 8
    - 190003685 * s ^ 7
    - 20014507 * s ^ 6
    + 6977022 * s ^ 5
    - 721033 * s ^ 4
    - 12719 * s ^ 3
    + 586 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient14 (s : ℚ) : ℚ :=
  -s ^ 51
    + 68 * s ^ 50
    - 1648 * s ^ 49
    + 22138 * s ^ 48
    - 194849 * s ^ 47
    + 1222956 * s ^ 46
    - 5729194 * s ^ 45
    + 20277485 * s ^ 44
    - 51817001 * s ^ 43
    + 73730383 * s ^ 42
    + 86835440 * s ^ 41
    - 956940144 * s ^ 40
    + 3594719916 * s ^ 39
    - 9511897085 * s ^ 38
    + 20180472120 * s ^ 37
    - 35169852403 * s ^ 36
    + 44841206538 * s ^ 35
    - 9776923826 * s ^ 34
    - 180447653066 * s ^ 33
    + 768968245606 * s ^ 32
    - 2197582755061 * s ^ 31
    + 5139296250089 * s ^ 30
    - 10440814486308 * s ^ 29
    + 18916811742669 * s ^ 28
    - 30982084338672 * s ^ 27
    + 46213644542205 * s ^ 26
    - 63042162091956 * s ^ 25
    + 78815030509349 * s ^ 24
    - 90362350231803 * s ^ 23
    + 94949236029659 * s ^ 22
    - 91264780630061 * s ^ 21
    + 79977165122611 * s ^ 20
    - 63555657563591 * s ^ 19
    + 45415350014567 * s ^ 18
    - 28778112624503 * s ^ 17
    + 15779258911006 * s ^ 16
    - 7129799709419 * s ^ 15
    + 2340960396431 * s ^ 14
    - 273747900353 * s ^ 13
    - 289588746930 * s ^ 12
    + 258589259945 * s ^ 11
    - 120394045336 * s ^ 10
    + 35508053391 * s ^ 9
    - 5828763891 * s ^ 8
    + 24641274 * s ^ 7
    + 222352454 * s ^ 6
    - 43127632 * s ^ 5
    + 3323576 * s ^ 4
    + 148700 * s ^ 3
    - 5813 * s ^ 2
    - 30 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient15 (s : ℚ) : ℚ :=
  16 * s ^ 50
    - 643 * s ^ 49
    + 11715 * s ^ 48
    - 130556 * s ^ 47
    + 1009016 * s ^ 46
    - 5797196 * s ^ 45
    + 25763609 * s ^ 44
    - 89590141 * s ^ 43
    + 235846837 * s ^ 42
    - 400456051 * s ^ 41
    + 2632834 * s ^ 40
    + 3010130804 * s ^ 39
    - 14004324029 * s ^ 38
    + 46058442215 * s ^ 37
    - 132423835382 * s ^ 36
    + 356755346317 * s ^ 35
    - 910149206958 * s ^ 34
    + 2177101143684 * s ^ 33
    - 4840163165320 * s ^ 32
    + 9969839194080 * s ^ 31
    - 19029238304487 * s ^ 30
    + 33684242620040 * s ^ 29
    - 55317165270465 * s ^ 28
    + 84257684324471 * s ^ 27
    - 118954784779544 * s ^ 26
    + 155497603541899 * s ^ 25
    - 187931047452080 * s ^ 24
    + 209558101158305 * s ^ 23
    - 214958902774527 * s ^ 22
    + 201992251667766 * s ^ 21
    - 172821591224215 * s ^ 20
    + 133388780074005 * s ^ 19
    - 91481330271604 * s ^ 18
    + 54252088576294 * s ^ 17
    - 26279494429837 * s ^ 16
    + 8815781965454 * s ^ 15
    - 303764910378 * s ^ 14
    - 2297468569431 * s ^ 13
    + 2061984703720 * s ^ 12
    - 1114187345366 * s ^ 11
    + 410283474535 * s ^ 10
    - 95390845359 * s ^ 9
    + 7689429496 * s ^ 8
    + 3196856089 * s ^ 7
    - 1294699393 * s ^ 6
    + 190685018 * s ^ 5
    - 10098915 * s ^ 4
    - 1156230 * s ^ 3
    + 39452 * s ^ 2
    + 436 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient16 (s : ℚ) : ℚ :=
  4 * s ^ 50
    - 226 * s ^ 49
    + 5328 * s ^ 48
    - 73732 * s ^ 47
    + 693966 * s ^ 46
    - 4841088 * s ^ 45
    + 26543854 * s ^ 44
    - 119233585 * s ^ 43
    + 450733931 * s ^ 42
    - 1460076984 * s ^ 41
    + 4154397037 * s ^ 40
    - 10954380604 * s ^ 39
    + 29107573230 * s ^ 38
    - 82233690469 * s ^ 37
    + 239160466497 * s ^ 36
    - 669715274341 * s ^ 35
    + 1736460136592 * s ^ 34
    - 4131822110743 * s ^ 33
    + 9056787495507 * s ^ 32
    - 18385863814012 * s ^ 31
    + 34676316206273 * s ^ 30
    - 60810633643130 * s ^ 29
    + 99111609682734 * s ^ 28
    - 149994669059789 * s ^ 27
    + 210548335079819 * s ^ 26
    - 273722611570802 * s ^ 25
    + 328877423016855 * s ^ 24
    - 364063416207171 * s ^ 23
    + 369645341807308 * s ^ 22
    - 341961148386026 * s ^ 21
    + 285269280861430 * s ^ 20
    - 210883977556098 * s ^ 19
    + 133658057169451 * s ^ 18
    - 67293294319098 * s ^ 17
    + 20408057507021 * s ^ 16
    + 5228459417775 * s ^ 15
    - 13753500431663 * s ^ 14
    + 12263345465195 * s ^ 13
    - 7417203645036 * s ^ 12
    + 3249084167722 * s ^ 11
    - 972187364522 * s ^ 10
    + 144263552563 * s ^ 9
    + 24564622612 * s ^ 8
    - 20127520390 * s ^ 7
    + 5253877058 * s ^ 6
    - 616015466 * s ^ 5
    + 12344257 * s ^ 4
    + 6587449 * s ^ 3
    - 192407 * s ^ 2
    - 4086 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient17 (s : ℚ) : ℚ :=
  -29 * s ^ 49
    + 1180 * s ^ 48
    - 22003 * s ^ 47
    + 252687 * s ^ 46
    - 2027653 * s ^ 45
    + 12230612 * s ^ 44
    - 57982292 * s ^ 43
    + 219068667 * s ^ 42
    - 633153786 * s ^ 41
    + 1128915414 * s ^ 40
    + 784156174 * s ^ 39
    - 16483173670 * s ^ 38
    + 81827402859 * s ^ 37
    - 288019215664 * s ^ 36
    + 841062461358 * s ^ 35
    - 2178461763737 * s ^ 34
    + 5176372091129 * s ^ 33
    - 11438356267981 * s ^ 32
    + 23558748535440 * s ^ 31
    - 45139377915112 * s ^ 30
    + 80283984598131 * s ^ 29
    - 132379038068557 * s ^ 28
    + 202208201731393 * s ^ 27
    - 285837507944918 * s ^ 26
    + 373205043435159 * s ^ 25
    - 448632036018666 * s ^ 24
    + 494065027750458 * s ^ 23
    - 494657609558520 * s ^ 22
    + 444688711891340 * s ^ 21
    - 351059007644122 * s ^ 20
    + 232412097785698 * s ^ 19
    - 113692299451675 * s ^ 18
    + 18081253669891 * s ^ 17
    + 40551236884282 * s ^ 16
    - 61441759249384 * s ^ 15
    + 55028777673361 * s ^ 14
    - 36477834633332 * s ^ 13
    + 18372072589150 * s ^ 12
    - 6675672297421 * s ^ 11
    + 1402008294857 * s ^ 10
    + 89723377942 * s ^ 9
    - 197059336336 * s ^ 8
    + 77375492721 * s ^ 7
    - 15873392566 * s ^ 6
    + 1384174977 * s ^ 5
    + 62818759 * s ^ 4
    - 28869310 * s ^ 3
    + 675418 * s ^ 2
    + 27676 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient18 (s : ℚ) : ℚ :=
  -6 * s ^ 49
    + 326 * s ^ 48
    - 7648 * s ^ 47
    + 107190 * s ^ 46
    - 1037318 * s ^ 45
    + 7594178 * s ^ 44
    - 45045249 * s ^ 43
    + 227546471 * s ^ 42
    - 1004805291 * s ^ 41
    + 3896153881 * s ^ 40
    - 13236613506 * s ^ 39
    + 39761630797 * s ^ 38
    - 108931789908 * s ^ 37
    + 285340829038 * s ^ 36
    - 740882701737 * s ^ 35
    + 1904496115990 * s ^ 34
    - 4710916965489 * s ^ 33
    + 10911163915856 * s ^ 32
    - 23338565595972 * s ^ 31
    + 45948617357956 * s ^ 30
    - 83368860038144 * s ^ 29
    + 139647628549101 * s ^ 28
    - 216020348318599 * s ^ 27
    + 308056907919271 * s ^ 26
    - 403446491289905 * s ^ 25
    + 482255507678506 * s ^ 24
    - 521012811072942 * s ^ 23
    + 500264090264772 * s ^ 22
    - 413039392634652 * s ^ 21
    + 270551097155110 * s ^ 20
    - 101813491026860 * s ^ 19
    - 54277865377957 * s ^ 18
    + 162460862017766 * s ^ 17
    - 204806736725058 * s ^ 16
    + 187269220565767 * s ^ 15
    - 134542347319098 * s ^ 14
    + 76101226244082 * s ^ 13
    - 32243883229597 * s ^ 12
    + 8554240627436 * s ^ 11
    + 21969817066 * s ^ 10
    - 1334841713286 * s ^ 9
    + 726471542593 * s ^ 8
    - 215898611213 * s ^ 7
    + 35807036639 * s ^ 6
    - 1596931496 * s ^ 5
    - 489981574 * s ^ 4
    + 99878563 * s ^ 3
    - 1572025 * s ^ 2
    - 143801 * s
    - 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient19 (s : ℚ) : ℚ :=
  25 * s ^ 48
    - 994 * s ^ 47
    + 17900 * s ^ 46
    - 195229 * s ^ 45
    + 1465123 * s ^ 44
    - 8287285 * s ^ 43
    + 38700992 * s ^ 42
    - 161198145 * s ^ 41
    + 598201600 * s ^ 40
    - 1738282377 * s ^ 39
    + 2474018111 * s ^ 38
    + 9161436774 * s ^ 37
    - 86174341584 * s ^ 36
    + 390152202545 * s ^ 35
    - 1306942102244 * s ^ 34
    + 3616049560292 * s ^ 33
    - 8724581901407 * s ^ 32
    + 18954348815388 * s ^ 31
    - 37746736018870 * s ^ 30
    + 69417827032566 * s ^ 29
    - 117917720006172 * s ^ 28
    + 184260664926830 * s ^ 27
    - 263128622958703 * s ^ 26
    + 340243825156192 * s ^ 25
    - 392662153843826 * s ^ 24
    + 393585870536110 * s ^ 23
    - 321571408438275 * s ^ 22
    + 171696505407900 * s ^ 21
    + 35868288983147 * s ^ 20
    - 255788360595501 * s ^ 19
    + 430135555173176 * s ^ 18
    - 511272705086556 * s ^ 17
    + 484357029166116 * s ^ 16
    - 374845388236572 * s ^ 15
    + 234161402915827 * s ^ 14
    - 112194840195129 * s ^ 13
    + 34965971014327 * s ^ 12
    - 887865904329 * s ^ 11
    - 6796802647557 * s ^ 10
    + 4726294330797 * s ^ 9
    - 1856361963164 * s ^ 8
    + 453627002933 * s ^ 7
    - 56348172215 * s ^ 6
    - 2429904282 * s ^ 5
    + 1938215435 * s ^ 4
    - 275913964 * s ^ 3
    + 1320426 * s ^ 2
    + 593572 * s
    + 276

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient20 (s : ℚ) : ℚ :=
  4 * s ^ 48
    - 201 * s ^ 47
    + 4314 * s ^ 46
    - 53579 * s ^ 45
    + 439454 * s ^ 44
    - 2651051 * s ^ 43
    + 13900574 * s ^ 42
    - 78205890 * s ^ 41
    + 479729257 * s ^ 40
    - 2716507146 * s ^ 39
    + 12788151229 * s ^ 38
    - 49102394621 * s ^ 37
    + 156655979717 * s ^ 36
    - 430087511880 * s ^ 35
    + 1061925146686 * s ^ 34
    - 2461752819308 * s ^ 33
    + 5498770131892 * s ^ 32
    - 11835228918825 * s ^ 31
    + 24120830933744 * s ^ 30
    - 45602650543374 * s ^ 29
    + 78679486900320 * s ^ 28
    - 122306448863021 * s ^ 27
    + 168886754201678 * s ^ 26
    - 202033119141893 * s ^ 25
    + 197103456657886 * s ^ 24
    - 126479734864423 * s ^ 23
    - 29454778461590 * s ^ 22
    + 267575521561584 * s ^ 21
    - 550299242589490 * s ^ 20
    + 807489587066954 * s ^ 19
    - 958972043015263 * s ^ 18
    + 951601483708084 * s ^ 17
    - 789982338772132 * s ^ 16
    + 537588842327363 * s ^ 15
    - 283702898856244 * s ^ 14
    + 97523881384857 * s ^ 13
    - 552928480082 * s ^ 12
    - 27639475702794 * s ^ 11
    + 22556809953314 * s ^ 10
    - 10947198337109 * s ^ 9
    + 3539567413009 * s ^ 8
    - 700989355466 * s ^ 7
    + 42078630183 * s ^ 6
    + 18733171909 * s ^ 5
    - 5464207607 * s ^ 4
    + 607354226 * s ^ 3
    + 7496031 * s ^ 2
    - 1989260 * s
    - 2020

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient21 (s : ℚ) : ℚ :=
  -7 * s ^ 47
    + 180 * s ^ 46
    - 392 * s ^ 45
    - 45987 * s ^ 44
    + 939319 * s ^ 43
    - 10128924 * s ^ 42
    + 72685773 * s ^ 41
    - 373900380 * s ^ 40
    + 1418606281 * s ^ 39
    - 3997667288 * s ^ 38
    + 8447722941 * s ^ 37
    - 15181458800 * s ^ 36
    + 38127865679 * s ^ 35
    - 157394364251 * s ^ 34
    + 636865183040 * s ^ 33
    - 2089200289568 * s ^ 32
    + 5585611786339 * s ^ 31
    - 12519801504321 * s ^ 30
    + 23993750436366 * s ^ 29
    - 39539184962492 * s ^ 28
    + 55133223249983 * s ^ 27
    - 60737948631057 * s ^ 26
    + 38249197142456 * s ^ 25
    + 37974334857873 * s ^ 24
    - 194689869370066 * s ^ 23
    + 445267686639722 * s ^ 22
    - 770379927805526 * s ^ 21
    + 1105658425806880 * s ^ 20
    - 1351999636267433 * s ^ 19
    + 1414435322653004 * s ^ 18
    - 1253647947765014 * s ^ 17
    + 916333692735788 * s ^ 16
    - 517408806784807 * s ^ 15
    + 180802029080331 * s ^ 14
    + 21633051471155 * s ^ 13
    - 92123358460722 * s ^ 12
    + 81768128730798 * s ^ 11
    - 46519182479091 * s ^ 10
    + 18614687244945 * s ^ 9
    - 5019054921669 * s ^ 8
    + 692228260434 * s ^ 7
    + 71211326936 * s ^ 6
    - 57399110466 * s ^ 5
    + 11842794175 * s ^ 4
    - 1042245128 * s ^ 3
    - 44554945 * s ^ 2
    + 5487394 * s
    + 10542

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient22 (s : ℚ) : ℚ :=
  -s ^ 47
    + 28 * s ^ 46
    + 130 * s ^ 45
    - 17068 * s ^ 44
    + 364249 * s ^ 43
    - 4443641 * s ^ 42
    + 36891214 * s ^ 41
    - 222316208 * s ^ 40
    + 994652010 * s ^ 39
    - 3258538078 * s ^ 38
    + 7107801179 * s ^ 37
    - 5154237944 * s ^ 36
    - 34934766075 * s ^ 35
    + 198396482101 * s ^ 34
    - 646273544213 * s ^ 33
    + 1602783378813 * s ^ 32
    - 3271680927349 * s ^ 31
    + 5632034345478 * s ^ 30
    - 7997491514126 * s ^ 29
    + 8086781793946 * s ^ 28
    - 252908476356 * s ^ 27
    - 27149441953288 * s ^ 26
    + 93955577842200 * s ^ 25
    - 226531394180069 * s ^ 24
    + 447896185013119 * s ^ 23
    - 758510000714322 * s ^ 22
    + 1115340593029271 * s ^ 21
    - 1426202991192394 * s ^ 20
    + 1575446543181914 * s ^ 19
    - 1478838508020120 * s ^ 18
    + 1138659763899029 * s ^ 17
    - 657818095591121 * s ^ 16
    + 193618363531719 * s ^ 15
    + 123134648942406 * s ^ 14
    - 248938220141303 * s ^ 13
    + 228784112589310 * s ^ 12
    - 146503494002409 * s ^ 11
    + 69243023561601 * s ^ 10
    - 23438870569595 * s ^ 9
    + 4846701828417 * s ^ 8
    - 74656355628 * s ^ 7
    - 338605738320 * s ^ 6
    + 121255057093 * s ^ 5
    - 20127694018 * s ^ 4
    + 1299498063 * s ^ 3
    + 143853947 * s ^ 2
    - 12561927 * s
    - 41664

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient23 (s : ℚ) : ℚ :=
  -2 * s ^ 46
    + 189 * s ^ 45
    - 6688 * s ^ 44
    + 133632 * s ^ 43
    - 1768404 * s ^ 42
    + 16830351 * s ^ 41
    - 120943833 * s ^ 40
    + 676738470 * s ^ 39
    - 3007848321 * s ^ 38
    + 10752126989 * s ^ 37
    - 31108153736 * s ^ 36
    + 72802234768 * s ^ 35
    - 136085497917 * s ^ 34
    + 193934532767 * s ^ 33
    - 170140700189 * s ^ 32
    - 93064424737 * s ^ 31
    + 953902023005 * s ^ 30
    - 3396596571656 * s ^ 29
    + 10143388888235 * s ^ 28
    - 27748991274250 * s ^ 27
    + 69174110421939 * s ^ 26
    - 154624545613721 * s ^ 25
    + 306784316354898 * s ^ 24
    - 537332078738055 * s ^ 23
    + 827146380955732 * s ^ 22
    - 1111798787039297 * s ^ 21
    + 1289467916592958 * s ^ 20
    - 1260497875563016 * s ^ 19
    + 985161837149028 * s ^ 18
    - 523361338764206 * s ^ 17
    + 20553987133983 * s ^ 16
    + 361880019805681 * s ^ 15
    - 529492573432216 * s ^ 14
    + 494209258033066 * s ^ 13
    - 346178119981261 * s ^ 12
    + 186739163741138 * s ^ 11
    - 75379833783589 * s ^ 10
    + 20306833785189 * s ^ 9
    - 1839753276877 * s ^ 8
    - 1279057400695 * s ^ 7
    + 732366472152 * s ^ 6
    - 193938637215 * s ^ 5
    + 26539406036 * s ^ 4
    - 868673000 * s ^ 3
    - 339355591 * s ^ 2
    + 23958984 * s
    + 129282

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient24 (s : ℚ) : ℚ :=
  14 * s ^ 45
    - 788 * s ^ 44
    + 20622 * s ^ 43
    - 335221 * s ^ 42
    + 3809326 * s ^ 41
    - 32252890 * s ^ 40
    + 211588229 * s ^ 39
    - 1103646689 * s ^ 38
    + 4659208640 * s ^ 37
    - 16122526333 * s ^ 36
    + 46161587255 * s ^ 35
    - 110265889465 * s ^ 34
    + 222429509490 * s ^ 33
    - 391618842758 * s ^ 32
    + 665753487924 * s ^ 31
    - 1339195255635 * s ^ 30
    + 3530909045837 * s ^ 29
    - 10347587161952 * s ^ 28
    + 28523163620884 * s ^ 27
    - 69542547692446 * s ^ 26
    + 148057363769761 * s ^ 25
    - 275015667327718 * s ^ 24
    + 445096878224575 * s ^ 23
    - 623544288893583 * s ^ 22
    + 743585498296860 * s ^ 21
    - 725649650342870 * s ^ 20
    + 518059870537198 * s ^ 19
    - 139442802348636 * s ^ 18
    - 309027326609517 * s ^ 17
    + 681400158702790 * s ^ 16
    - 859568806729831 * s ^ 15
    + 814499149210169 * s ^ 14
    - 613108552405884 * s ^ 13
    + 368002313456152 * s ^ 12
    - 170721943557400 * s ^ 11
    + 55519592579679 * s ^ 10
    - 7956573807314 * s ^ 9
    - 3502809817352 * s ^ 8
    + 2959002426725 * s ^ 7
    - 1099900833306 * s ^ 6
    + 239463424789 * s ^ 5
    - 25685702873 * s ^ 4
    - 692241549 * s ^ 3
    + 630111453 * s ^ 2
    - 38074090 * s
    - 322272

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient25 (s : ℚ) : ℚ :=
  s ^ 45
    - 74 * s ^ 44
    + 2400 * s ^ 43
    - 46818 * s ^ 42
    + 626707 * s ^ 41
    - 6185211 * s ^ 40
    + 47059524 * s ^ 39
    - 284412725 * s ^ 38
    + 1394600682 * s ^ 37
    - 5633388888 * s ^ 36
    + 18937089663 * s ^ 35
    - 53145417702 * s ^ 34
    + 123079329498 * s ^ 33
    - 222719646600 * s ^ 32
    + 243401904856 * s ^ 31
    + 235794921407 * s ^ 30
    - 2371352324825 * s ^ 29
    + 8689746420234 * s ^ 28
    - 23619111679823 * s ^ 27
    + 53071627792602 * s ^ 26
    - 101813942178044 * s ^ 25
    + 167826590551435 * s ^ 24
    - 235001865434498 * s ^ 23
    + 269038314958806 * s ^ 22
    - 223607678158236 * s ^ 21
    + 60753488965427 * s ^ 20
    + 220487162803281 * s ^ 19
    - 564896468607618 * s ^ 18
    + 871044423012913 * s ^ 17
    - 1034496188167283 * s ^ 16
    + 1002347983915203 * s ^ 15
    - 802621519261605 * s ^ 14
    + 525950993253612 * s ^ 13
    - 272225491835813 * s ^ 12
    + 101040384228377 * s ^ 11
    - 17324708465412 * s ^ 10
    - 8192830066292 * s ^ 9
    + 8672138859964 * s ^ 8
    - 4120433372867 * s ^ 7
    + 1234556987753 * s ^ 6
    - 223681121852 * s ^ 5
    + 14631879008 * s ^ 4
    + 3257167308 * s ^ 3
    - 947416680 * s ^ 2
    + 50203212 * s
    + 654993

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient26 (s : ℚ) : ℚ :=
  -2 * s ^ 44
    + 115 * s ^ 43
    - 3099 * s ^ 42
    + 52280 * s ^ 41
    - 621791 * s ^ 40
    + 5566239 * s ^ 39
    - 39127711 * s ^ 38
    + 222890748 * s ^ 37
    - 1057408145 * s ^ 36
    + 4294409602 * s ^ 35
    - 15388348649 * s ^ 34
    + 50203538873 * s ^ 33
    - 152992988870 * s ^ 32
    + 440427474924 * s ^ 31
    - 1191208085760 * s ^ 30
    + 2980586361794 * s ^ 29
    - 6779745769941 * s ^ 28
    + 13784631538648 * s ^ 27
    - 24566971835800 * s ^ 26
    + 37160371896589 * s ^ 25
    - 44255966649818 * s ^ 24
    + 30973878422141 * s ^ 23
    + 23881475727634 * s ^ 22
    - 140192087612417 * s ^ 21
    + 322796386736059 * s ^ 20
    - 547906191555594 * s ^ 19
    + 760644821376020 * s ^ 18
    - 891960464189685 * s ^ 17
    + 890927077742990 * s ^ 16
    - 754166577877695 * s ^ 15
    + 531033086360092 * s ^ 14
    - 298010739018330 * s ^ 13
    + 118901598191655 * s ^ 12
    - 18103216220623 * s ^ 11
    - 17985195725813 * s ^ 10
    + 19349128151697 * s ^ 9
    - 10839897014875 * s ^ 8
    + 4093041826345 * s ^ 7
    - 1036781386815 * s ^ 6
    + 144764980449 * s ^ 5
    + 3311580766 * s ^ 4
    - 5904428542 * s ^ 3
    + 1166527949 * s ^ 2
    - 54388294 * s
    - 1095340

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient27 (s : ℚ) : ℚ :=
  s ^ 43
    - 48 * s ^ 42
    + 1059 * s ^ 41
    - 14017 * s ^ 40
    + 119643 * s ^ 39
    - 616418 * s ^ 38
    + 757816 * s ^ 37
    + 18893904 * s ^ 36
    - 214078167 * s ^ 35
    + 1412332929 * s ^ 34
    - 6911316232 * s ^ 33
    + 26971091502 * s ^ 32
    - 86637569010 * s ^ 31
    + 231869737245 * s ^ 30
    - 513005271432 * s ^ 29
    + 893357621735 * s ^ 28
    - 988191310427 * s ^ 27
    - 478412478902 * s ^ 26
    + 6510601804742 * s ^ 25
    - 22651789580050 * s ^ 24
    + 56921181193362 * s ^ 23
    - 117682111323058 * s ^ 22
    + 208777250053100 * s ^ 21
    - 323161260019569 * s ^ 20
    + 438896407708975 * s ^ 19
    - 522478097144173 * s ^ 18
    + 541464174601210 * s ^ 17
    - 481581176265330 * s ^ 16
    + 357626542924732 * s ^ 15
    - 208864320911268 * s ^ 14
    + 79728670876402 * s ^ 13
    + 1806812450717 * s ^ 12
    - 33760123249840 * s ^ 11
    + 33117118598556 * s ^ 10
    - 20548307258739 * s ^ 9
    + 9200026429183 * s ^ 8
    - 2960675378727 * s ^ 7
    + 613510471237 * s ^ 6
    - 41308551486 * s ^ 5
    - 19639054871 * s ^ 4
    + 7383300962 * s ^ 3
    - 1178580588 * s ^ 2
    + 47488904 * s
    + 1514436

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient28 (s : ℚ) : ℚ :=
  -4 * s ^ 41
    + 209 * s ^ 40
    - 5241 * s ^ 39
    + 84003 * s ^ 38
    - 967007 * s ^ 37
    + 8521067 * s ^ 36
    - 59874216 * s ^ 35
    + 345603228 * s ^ 34
    - 1679212690 * s ^ 33
    + 7023366874 * s ^ 32
    - 25849558810 * s ^ 31
    + 85535040160 * s ^ 30
    - 259270808714 * s ^ 29
    + 729190819822 * s ^ 28
    - 1912155600543 * s ^ 27
    + 4665414388779 * s ^ 26
    - 10528438683825 * s ^ 25
    + 21826624419552 * s ^ 24
    - 41307538907468 * s ^ 23
    + 70955482360436 * s ^ 22
    - 109968545177627 * s ^ 21
    + 152685343213572 * s ^ 20
    - 188125468653737 * s ^ 19
    + 202803835321037 * s ^ 18
    - 186801811602796 * s ^ 17
    + 140255349350386 * s ^ 16
    - 75647189807009 * s ^ 15
    + 12982417401926 * s ^ 14
    + 30072962184286 * s ^ 13
    - 46659952422626 * s ^ 12
    + 42080195042269 * s ^ 11
    - 27912480806075 * s ^ 10
    + 14216679071543 * s ^ 9
    - 5479392510209 * s ^ 8
    + 1474722148226 * s ^ 7
    - 196054174425 * s ^ 6
    - 35948462154 * s ^ 5
    + 26788596653 * s ^ 4
    - 7018258071 * s ^ 3
    + 972427411 * s ^ 2
    - 32135020 * s
    - 1733172

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient29 (s : ℚ) : ℚ :=
  5 * s ^ 39
    - 266 * s ^ 38
    + 6866 * s ^ 37
    - 114344 * s ^ 36
    + 1378128 * s ^ 35
    - 12786370 * s ^ 34
    + 94908815 * s ^ 33
    - 578768397 * s ^ 32
    + 2957855716 * s ^ 31
    - 12871902569 * s ^ 30
    + 48344712508 * s ^ 29
    - 158556855427 * s ^ 28
    + 458734804173 * s ^ 27
    - 1180615780164 * s ^ 26
    + 2719297346439 * s ^ 25
    - 5623383020356 * s ^ 24
    + 10439843566853 * s ^ 23
    - 17334821030649 * s ^ 22
    + 25535117841024 * s ^ 21
    - 32882203896062 * s ^ 20
    + 36007719029388 * s ^ 19
    - 31531823839210 * s ^ 18
    + 18061248235657 * s ^ 17
    + 2125893369046 * s ^ 16
    - 23189911188491 * s ^ 15
    + 38214274732417 * s ^ 14
    - 42803740700181 * s ^ 13
    + 37336235141596 * s ^ 12
    - 26216441819149 * s ^ 11
    + 14819296312046 * s ^ 10
    - 6576365707325 * s ^ 9
    + 2131086874800 * s ^ 8
    - 386055640849 * s ^ 7
    - 46120976277 * s ^ 6
    + 62455099033 * s ^ 5
    - 23673724577 * s ^ 4
    + 5207208466 * s ^ 3
    - 647590582 * s ^ 2
    + 15280268 * s
    + 1638001

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient30 (s : ℚ) : ℚ :=
  5 * s ^ 36
    - 341 * s ^ 35
    + 10120 * s ^ 34
    - 180732 * s ^ 33
    + 2222470 * s ^ 32
    - 20250550 * s ^ 31
    + 143084937 * s ^ 30
    - 808137401 * s ^ 29
    + 3725751811 * s ^ 28
    - 14224019090 * s ^ 27
    + 45372551627 * s ^ 26
    - 121325677247 * s ^ 25
    + 270692876677 * s ^ 24
    - 493979406304 * s ^ 23
    + 693789372941 * s ^ 22
    - 585971369372 * s ^ 21
    - 338514646045 * s ^ 20
    + 2694471464426 * s ^ 19
    - 6863880289509 * s ^ 18
    + 12542870140004 * s ^ 17
    - 18490222840352 * s ^ 16
    + 22823877529651 * s ^ 15
    - 23890100532957 * s ^ 14
    + 21222064076004 * s ^ 13
    - 15879017407995 * s ^ 12
    + 9840255028678 * s ^ 11
    - 4883271997359 * s ^ 10
    + 1791491178720 * s ^ 9
    - 358347326563 * s ^ 8
    - 75508935775 * s ^ 7
    + 104231031103 * s ^ 6
    - 50337407915 * s ^ 5
    + 15226623040 * s ^ 4
    - 3018782527 * s ^ 3
    + 340809225 * s ^ 2
    - 3272629 * s
    - 1270776

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient31 (s : ℚ) : ℚ :=
  -5 * s ^ 35
    + 252 * s ^ 34
    - 6045 * s ^ 33
    + 92054 * s ^ 32
    - 1001640 * s ^ 31
    + 8313236 * s ^ 30
    - 54885417 * s ^ 29
    + 296995225 * s ^ 28
    - 1347832455 * s ^ 27
    + 5227695158 * s ^ 26
    - 17611592910 * s ^ 25
    + 52262751528 * s ^ 24
    - 138216338011 * s ^ 23
    + 328580899158 * s ^ 22
    - 705578084767 * s ^ 21
    + 1369784546499 * s ^ 20
    - 2398197893435 * s ^ 19
    + 3768465405424 * s ^ 18
    - 5282223134390 * s ^ 17
    + 6557062341510 * s ^ 16
    - 7146011303022 * s ^ 15
    + 6760340357733 * s ^ 14
    - 5463770499700 * s ^ 13
    + 3678818597147 * s ^ 12
    - 1966976419821 * s ^ 11
    + 734956237438 * s ^ 10
    - 82946836819 * s ^ 9
    - 132466045614 * s ^ 8
    + 129582589025 * s ^ 7
    - 70797526929 * s ^ 6
    + 26887075200 * s ^ 5
    - 7283610327 * s ^ 4
    + 1346765796 * s ^ 3
    - 136495094 * s ^ 2
    - 1956976 * s
    + 800994

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient32 (s : ℚ) : ℚ :=
  4 * s ^ 33
    - 197 * s ^ 32
    + 4641 * s ^ 31
    - 69713 * s ^ 30
    + 750907 * s ^ 29
    - 6184138 * s ^ 28
    + 40539493 * s ^ 27
    - 217411271 * s ^ 26
    + 972730289 * s ^ 25
    - 3683531619 * s ^ 24
    + 11933681226 * s ^ 23
    - 33345777510 * s ^ 22
    + 80852153707 * s ^ 21
    - 170846595832 * s ^ 20
    + 315443870806 * s ^ 19
    - 509187633805 * s ^ 18
    + 716928175873 * s ^ 17
    - 874823121323 * s ^ 16
    + 913394337828 * s ^ 15
    - 796626399731 * s ^ 14
    + 551972592332 * s ^ 13
    - 263203733702 * s ^ 12
    + 24698412487 * s ^ 11
    + 108951017755 * s ^ 10
    - 140662857702 * s ^ 9
    + 111009528419 * s ^ 8
    - 64854015329 * s ^ 7
    + 29118266222 * s ^ 6
    - 10006584922 * s ^ 5
    + 2554507520 * s ^ 4
    - 447282552 * s ^ 3
    + 38530533 * s ^ 2
    + 2503008 * s
    - 403704

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient33 (s : ℚ) : ℚ :=
  -s ^ 31
    + 46 * s ^ 30
    - 1009 * s ^ 29
    + 14062 * s ^ 28
    - 139993 * s ^ 27
    + 1061234 * s ^ 26
    - 6375492 * s ^ 25
    + 31177656 * s ^ 24
    - 126386375 * s ^ 23
    + 429630082 * s ^ 22
    - 1231306944 * s ^ 21
    + 2971143481 * s ^ 20
    - 5974150662 * s ^ 19
    + 9754093049 * s ^ 18
    - 12124707669 * s ^ 17
    + 9110121908 * s ^ 16
    + 3180645456 * s ^ 15
    - 25093516034 * s ^ 14
    + 51195729663 * s ^ 13
    - 72174336887 * s ^ 12
    + 80142292241 * s ^ 11
    - 73151427740 * s ^ 10
    + 55640594137 * s ^ 9
    - 35204456856 * s ^ 8
    + 18316441698 * s ^ 7
    - 7692248914 * s ^ 6
    + 2538075720 * s ^ 5
    - 628303498 * s ^ 4
    + 103731972 * s ^ 3
    - 6121731 * s ^ 2
    - 1431414 * s
    + 158814

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient34 (s : ℚ) : ℚ :=
  s ^ 28
    - 46 * s ^ 27
    + 1009 * s ^ 26
    - 14042 * s ^ 25
    + 139148 * s ^ 24
    - 1044421 * s ^ 23
    + 6166422 * s ^ 22
    - 29360253 * s ^ 21
    + 114691818 * s ^ 20
    - 372168671 * s ^ 19
    + 1012670827 * s ^ 18
    - 2328472105 * s ^ 17
    + 4556412084 * s ^ 16
    - 7643161610 * s ^ 15
    + 11076517320 * s ^ 14
    - 13976740826 * s ^ 13
    + 15449184321 * s ^ 12
    - 14981551917 * s ^ 11
    + 12678162883 * s ^ 10
    - 9249355158 * s ^ 9
    + 5719749852 * s ^ 8
    - 2940557503 * s ^ 7
    + 1229081802 * s ^ 6
    - 404813369 * s ^ 5
    + 98695196 * s ^ 4
    - 14530608 * s ^ 3
    - 176679 * s ^ 2
    + 521505 * s
    - 46980

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient35 (s : ℚ) : ℚ :=
  -s ^ 24
    + 42 * s ^ 23
    - 832 * s ^ 22
    + 10333 * s ^ 21
    - 90217 * s ^ 20
    + 588585 * s ^ 19
    - 2977543 * s ^ 18
    + 11963190 * s ^ 17
    - 38789022 * s ^ 16
    + 102570992 * s ^ 15
    - 222672822 * s ^ 14
    + 398301264 * s ^ 13
    - 587813888 * s ^ 12
    + 715505846 * s ^ 11
    - 717357465 * s ^ 10
    + 591210386 * s ^ 9
    - 399380117 * s ^ 8
    + 219874518 * s ^ 7
    - 97262208 * s ^ 6
    + 33297307 * s ^ 5
    - 7853423 * s ^ 4
    + 654449 * s ^ 3
    + 334782 * s ^ 2
    - 123984 * s
    + 9828

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient36 (s : ℚ) : ℚ :=
  s ^ 18
    - 32 * s ^ 17
    + 472 * s ^ 16
    - 4254 * s ^ 15
    + 26184 * s ^ 14
    - 116534 * s ^ 13
    + 387280 * s ^ 12
    - 978513 * s ^ 11
    + 1895600 * s ^ 10
    - 2818224 * s ^ 9
    + 3195176 * s ^ 8
    - 2716604 * s ^ 7
    + 1661644 * s ^ 6
    - 639330 * s ^ 5
    + 50800 * s ^ 4
    + 110307 * s ^ 3
    - 70389 * s ^ 2
    + 17712 * s
    - 1296

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient37 (s : ℚ) : ℚ :=
  -s ^ 11
    + 22 * s ^ 10
    - 213 * s ^ 9
    + 1193 * s ^ 8
    - 4274 * s ^ 7
    + 10224 * s ^ 6
    - 16546 * s ^ 5
    + 17950 * s ^ 4
    - 12621 * s ^ 3
    + 5346 * s ^ 2
    - 1161 * s
    + 81

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def termTwo (r s : ℚ) : ℚ :=
  termTwoCoefficient0 s +
    termTwoCoefficient1 s * r +
    termTwoCoefficient2 s * r ^ 2 +
    termTwoCoefficient3 s * r ^ 3 +
    termTwoCoefficient4 s * r ^ 4 +
    termTwoCoefficient5 s * r ^ 5 +
    termTwoCoefficient6 s * r ^ 6 +
    termTwoCoefficient7 s * r ^ 7 +
    termTwoCoefficient8 s * r ^ 8 +
    termTwoCoefficient9 s * r ^ 9 +
    termTwoCoefficient10 s * r ^ 10 +
    termTwoCoefficient11 s * r ^ 11 +
    termTwoCoefficient12 s * r ^ 12 +
    termTwoCoefficient13 s * r ^ 13 +
    termTwoCoefficient14 s * r ^ 14 +
    termTwoCoefficient15 s * r ^ 15 +
    termTwoCoefficient16 s * r ^ 16 +
    termTwoCoefficient17 s * r ^ 17 +
    termTwoCoefficient18 s * r ^ 18 +
    termTwoCoefficient19 s * r ^ 19 +
    termTwoCoefficient20 s * r ^ 20 +
    termTwoCoefficient21 s * r ^ 21 +
    termTwoCoefficient22 s * r ^ 22 +
    termTwoCoefficient23 s * r ^ 23 +
    termTwoCoefficient24 s * r ^ 24 +
    termTwoCoefficient25 s * r ^ 25 +
    termTwoCoefficient26 s * r ^ 26 +
    termTwoCoefficient27 s * r ^ 27 +
    termTwoCoefficient28 s * r ^ 28 +
    termTwoCoefficient29 s * r ^ 29 +
    termTwoCoefficient30 s * r ^ 30 +
    termTwoCoefficient31 s * r ^ 31 +
    termTwoCoefficient32 s * r ^ 32 +
    termTwoCoefficient33 s * r ^ 33 +
    termTwoCoefficient34 s * r ^ 34 +
    termTwoCoefficient35 s * r ^ 35 +
    termTwoCoefficient36 s * r ^ 36 +
    termTwoCoefficient37 s * r ^ 37

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_0 (s : ℚ) :
    termTwoCoefficient0 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient0,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_1 (s : ℚ) :
    termTwoCoefficient1 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient1,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_2 (s : ℚ) :
    termTwoCoefficient2 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient2,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_3 (s : ℚ) :
    termTwoCoefficient3 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient3,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_4 (s : ℚ) :
    termTwoCoefficient4 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient4,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_5 (s : ℚ) :
    termTwoCoefficient5 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient5,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_6 (s : ℚ) :
    termTwoCoefficient6 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient6,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_7 (s : ℚ) :
    termTwoCoefficient7 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient7,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_8 (s : ℚ) :
    termTwoCoefficient8 s =
      t2Step3Coefficient0 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient8,
    t2Step3Coefficient0,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_9 (s : ℚ) :
    termTwoCoefficient9 s =
      t2Step3Coefficient1 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient9,
    t2Step3Coefficient1,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_10 (s : ℚ) :
    termTwoCoefficient10 s =
      t2Step3Coefficient2 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient10,
    t2Step3Coefficient2,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_11 (s : ℚ) :
    termTwoCoefficient11 s =
      t2Step3Coefficient3 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient11,
    t2Step3Coefficient3,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_12 (s : ℚ) :
    termTwoCoefficient12 s =
      t2Step3Coefficient4 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient12,
    t2Step3Coefficient4,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_13 (s : ℚ) :
    termTwoCoefficient13 s =
      t2Step3Coefficient5 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient13,
    t2Step3Coefficient5,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_14 (s : ℚ) :
    termTwoCoefficient14 s =
      t2Step3Coefficient6 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient14,
    t2Step3Coefficient6,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_15 (s : ℚ) :
    termTwoCoefficient15 s =
      t2Step3Coefficient7 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient15,
    t2Step3Coefficient7,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_16 (s : ℚ) :
    termTwoCoefficient16 s =
      t2Step3Coefficient8 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient16,
    t2Step3Coefficient8,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_17 (s : ℚ) :
    termTwoCoefficient17 s =
      t2Step3Coefficient9 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient17,
    t2Step3Coefficient9,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_18 (s : ℚ) :
    termTwoCoefficient18 s =
      t2Step3Coefficient10 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient18,
    t2Step3Coefficient10,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_19 (s : ℚ) :
    termTwoCoefficient19 s =
      t2Step3Coefficient11 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient19,
    t2Step3Coefficient11,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_20 (s : ℚ) :
    termTwoCoefficient20 s =
      t2Step3Coefficient12 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient20,
    t2Step3Coefficient12,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_21 (s : ℚ) :
    termTwoCoefficient21 s =
      t2Step3Coefficient13 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient21,
    t2Step3Coefficient13,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_22 (s : ℚ) :
    termTwoCoefficient22 s =
      t2Step3Coefficient14 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient22,
    t2Step3Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_23 (s : ℚ) :
    termTwoCoefficient23 s =
      t2Step3Coefficient15 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient23,
    t2Step3Coefficient15,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_24 (s : ℚ) :
    termTwoCoefficient24 s =
      t2Step3Coefficient16 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient24,
    t2Step3Coefficient16,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_25 (s : ℚ) :
    termTwoCoefficient25 s =
      t2Step3Coefficient17 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient25,
    t2Step3Coefficient17,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_26 (s : ℚ) :
    termTwoCoefficient26 s =
      t2Step3Coefficient18 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient26,
    t2Step3Coefficient18,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_27 (s : ℚ) :
    termTwoCoefficient27 s =
      t2Step3Coefficient19 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient27,
    t2Step3Coefficient19,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_28 (s : ℚ) :
    termTwoCoefficient28 s =
      t2Step3Coefficient20 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient28,
    t2Step3Coefficient20,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_29 (s : ℚ) :
    termTwoCoefficient29 s =
      t2Step3Coefficient21 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient1 s +
        t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [termTwoCoefficient29,
    t2Step3Coefficient21,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient1,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_30 (s : ℚ) :
    termTwoCoefficient30 s =
      t2Step3Coefficient22 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient2 s +
        t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient1 s := by
  simp only [termTwoCoefficient30,
    t2Step3Coefficient22,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient2,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_31 (s : ℚ) :
    termTwoCoefficient31 s =
      t2Step3Coefficient23 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient3 s +
        t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient2 s := by
  simp only [termTwoCoefficient31,
    t2Step3Coefficient23,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient3,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_32 (s : ℚ) :
    termTwoCoefficient32 s =
      t2Step3Coefficient24 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient4 s +
        t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient3 s := by
  simp only [termTwoCoefficient32,
    t2Step3Coefficient24,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient4,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_33 (s : ℚ) :
    termTwoCoefficient33 s =
      t2Step3Coefficient25 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient5 s +
        t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient4 s := by
  simp only [termTwoCoefficient33,
    t2Step3Coefficient25,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient5,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_34 (s : ℚ) :
    termTwoCoefficient34 s =
      t2Step3Coefficient26 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient6 s +
        t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient5 s := by
  simp only [termTwoCoefficient34,
    t2Step3Coefficient26,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient6,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_35 (s : ℚ) :
    termTwoCoefficient35 s =
      t2Step3Coefficient27 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient7 s +
        t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient6 s := by
  simp only [termTwoCoefficient35,
    t2Step3Coefficient27,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient7,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_36 (s : ℚ) :
    termTwoCoefficient36 s =
      t2Step3Coefficient28 s *
          rawUnitTwoDenominatorCoefficient8 s +
        t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient7 s := by
  simp only [termTwoCoefficient36,
    t2Step3Coefficient28,
    rawUnitTwoDenominatorCoefficient8,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termTwoCoefficient_product_certificate_37 (s : ℚ) :
    termTwoCoefficient37 s =
      t2Step3Coefficient29 s *
          rawUnitTwoDenominatorCoefficient8 s := by
  simp only [termTwoCoefficient37,
    t2Step3Coefficient29,
    rawUnitTwoDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termTwo_eq_t2Step3_mul_rawUnitTwoDenominator (r s : ℚ) :
    termTwo r s =
      t2Step3 r s * rawUnitTwoDenominator r s := by
  have h0 := termTwoCoefficient_product_certificate_0 s
  have h1 := termTwoCoefficient_product_certificate_1 s
  have h2 := termTwoCoefficient_product_certificate_2 s
  have h3 := termTwoCoefficient_product_certificate_3 s
  have h4 := termTwoCoefficient_product_certificate_4 s
  have h5 := termTwoCoefficient_product_certificate_5 s
  have h6 := termTwoCoefficient_product_certificate_6 s
  have h7 := termTwoCoefficient_product_certificate_7 s
  have h8 := termTwoCoefficient_product_certificate_8 s
  have h9 := termTwoCoefficient_product_certificate_9 s
  have h10 := termTwoCoefficient_product_certificate_10 s
  have h11 := termTwoCoefficient_product_certificate_11 s
  have h12 := termTwoCoefficient_product_certificate_12 s
  have h13 := termTwoCoefficient_product_certificate_13 s
  have h14 := termTwoCoefficient_product_certificate_14 s
  have h15 := termTwoCoefficient_product_certificate_15 s
  have h16 := termTwoCoefficient_product_certificate_16 s
  have h17 := termTwoCoefficient_product_certificate_17 s
  have h18 := termTwoCoefficient_product_certificate_18 s
  have h19 := termTwoCoefficient_product_certificate_19 s
  have h20 := termTwoCoefficient_product_certificate_20 s
  have h21 := termTwoCoefficient_product_certificate_21 s
  have h22 := termTwoCoefficient_product_certificate_22 s
  have h23 := termTwoCoefficient_product_certificate_23 s
  have h24 := termTwoCoefficient_product_certificate_24 s
  have h25 := termTwoCoefficient_product_certificate_25 s
  have h26 := termTwoCoefficient_product_certificate_26 s
  have h27 := termTwoCoefficient_product_certificate_27 s
  have h28 := termTwoCoefficient_product_certificate_28 s
  have h29 := termTwoCoefficient_product_certificate_29 s
  have h30 := termTwoCoefficient_product_certificate_30 s
  have h31 := termTwoCoefficient_product_certificate_31 s
  have h32 := termTwoCoefficient_product_certificate_32 s
  have h33 := termTwoCoefficient_product_certificate_33 s
  have h34 := termTwoCoefficient_product_certificate_34 s
  have h35 := termTwoCoefficient_product_certificate_35 s
  have h36 := termTwoCoefficient_product_certificate_36 s
  have h37 := termTwoCoefficient_product_certificate_37 s
  simp only [termTwo, t2Step3, rawUnitTwoDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 +
    r ^ 32 * h32 + r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 +
    r ^ 36 * h36 + r ^ 37 * h37

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient2 (s : ℚ) : ℚ :=
  s ^ 19
    - 7 * s ^ 18
    + 26 * s ^ 17
    - 68 * s ^ 16
    + 139 * s ^ 15
    - 235 * s ^ 14
    + 340 * s ^ 13
    - 430 * s ^ 12
    + 482 * s ^ 11
    - 482 * s ^ 10
    + 430 * s ^ 9
    - 340 * s ^ 8
    + 235 * s ^ 7
    - 139 * s ^ 6
    + 68 * s ^ 5
    - 26 * s ^ 4
    + 7 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient3 (s : ℚ) : ℚ :=
  s ^ 20
    - 8 * s ^ 19
    + 25 * s ^ 18
    - 50 * s ^ 17
    + 91 * s ^ 16
    - 198 * s ^ 15
    + 485 * s ^ 14
    - 1082 * s ^ 13
    + 2026 * s ^ 12
    - 3164 * s ^ 11
    + 4150 * s ^ 10
    - 4602 * s ^ 9
    + 4319 * s ^ 8
    - 3410 * s ^ 7
    + 2233 * s ^ 6
    - 1178 * s ^ 5
    + 475 * s ^ 4
    - 132 * s ^ 3
    + 19 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient4 (s : ℚ) : ℚ :=
  s ^ 20
    - 16 * s ^ 19
    + 77 * s ^ 18
    - 137 * s ^ 17
    - 98 * s ^ 16
    + 1261 * s ^ 15
    - 4234 * s ^ 14
    + 9740 * s ^ 13
    - 17776 * s ^ 12
    + 27076 * s ^ 11
    - 35078 * s ^ 10
    + 38902 * s ^ 9
    - 36847 * s ^ 8
    + 29528 * s ^ 7
    - 19663 * s ^ 6
    + 10531 * s ^ 5
    - 4292 * s ^ 4
    + 1195 * s ^ 3
    - 170 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient5 (s : ℚ) : ℚ :=
  2 * s ^ 20
    - 40 * s ^ 19
    + 338 * s ^ 18
    - 1594 * s ^ 17
    + 5089 * s ^ 16
    - 12794 * s ^ 15
    + 27466 * s ^ 14
    - 51934 * s ^ 13
    + 87107 * s ^ 12
    - 128856 * s ^ 11
    + 166760 * s ^ 10
    - 187400 * s ^ 9
    + 181044 * s ^ 8
    - 148244 * s ^ 7
    + 100636 * s ^ 6
    - 54632 * s ^ 5
    + 22359 * s ^ 4
    - 6138 * s ^ 3
    + 816 * s ^ 2
    + 16 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient6 (s : ℚ) : ℚ :=
  s ^ 21
    - 17 * s ^ 20
    + 133 * s ^ 19
    - 629 * s ^ 18
    + 2139 * s ^ 17
    - 6386 * s ^ 16
    + 18336 * s ^ 15
    - 47746 * s ^ 14
    + 107013 * s ^ 13
    - 203880 * s ^ 12
    + 330679 * s ^ 11
    - 458857 * s ^ 10
    + 545243 * s ^ 9
    - 551331 * s ^ 8
    + 468149 * s ^ 7
    - 326145 * s ^ 6
    + 179461 * s ^ 5
    - 73170 * s ^ 4
    + 19307 * s ^ 3
    - 2123 * s ^ 2
    - 189 * s
    + 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient7 (s : ℚ) : ℚ :=
  -2 * s ^ 20
    + 22 * s ^ 19
    - 53 * s ^ 18
    - 522 * s ^ 17
    + 5089 * s ^ 16
    - 22964 * s ^ 15
    + 70829 * s ^ 14
    - 171150 * s ^ 13
    + 343542 * s ^ 12
    - 586556 * s ^ 11
    + 858667 * s ^ 10
    - 1074002 * s ^ 9
    + 1135392 * s ^ 8
    - 997780 * s ^ 7
    + 710015 * s ^ 6
    - 392426 * s ^ 5
    + 156396 * s ^ 4
    - 37554 * s ^ 3
    + 2110 * s ^ 2
    + 1012 * s
    - 65

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient8 (s : ℚ) : ℚ :=
  -2 * s ^ 20
    + 41 * s ^ 19
    - 380 * s ^ 18
    + 2146 * s ^ 17
    - 8495 * s ^ 16
    + 26488 * s ^ 15
    - 71703 * s ^ 14
    + 174409 * s ^ 13
    - 374617 * s ^ 12
    + 695496 * s ^ 11
    - 1100093 * s ^ 10
    + 1464121 * s ^ 9
    - 1619779 * s ^ 8
    + 1465034 * s ^ 7
    - 1053523 * s ^ 6
    + 574209 * s ^ 5
    - 214699 * s ^ 4
    + 39925 * s ^ 3
    + 4427 * s ^ 2
    - 3213 * s
    + 208

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient9 (s : ℚ) : ℚ :=
  2 * s ^ 19
    - 28 * s ^ 18
    + 130 * s ^ 17
    + 149 * s ^ 16
    - 4844 * s ^ 15
    + 28930 * s ^ 14
    - 105370 * s ^ 13
    + 280917 * s ^ 12
    - 590280 * s ^ 11
    + 1006188 * s ^ 10
    - 1402814 * s ^ 9
    + 1595483 * s ^ 8
    - 1457744 * s ^ 7
    + 1034846 * s ^ 6
    - 533482 * s ^ 5
    + 165547 * s ^ 4
    - 3630 * s ^ 3
    - 20208 * s ^ 2
    + 6640 * s
    - 432

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient10 (s : ℚ) : ℚ :=
  s ^ 19
    - 23 * s ^ 18
    + 244 * s ^ 17
    - 1603 * s ^ 16
    + 7406 * s ^ 15
    - 26132 * s ^ 14
    + 74934 * s ^ 13
    - 180729 * s ^ 12
    + 367779 * s ^ 11
    - 624459 * s ^ 10
    + 874704 * s ^ 9
    - 995209 * s ^ 8
    + 892318 * s ^ 7
    - 593960 * s ^ 6
    + 250616 * s ^ 5
    - 18333 * s ^ 4
    - 55512 * s ^ 3
    + 36582 * s ^ 2
    - 9226 * s
    + 602

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient11 (s : ℚ) : ℚ :=
  -2 * s ^ 17
    + 44 * s ^ 16
    - 454 * s ^ 15
    + 2892 * s ^ 14
    - 12608 * s ^ 13
    + 39800 * s ^ 12
    - 94900 * s ^ 11
    + 176525 * s ^ 10
    - 259104 * s ^ 9
    + 293563 * s ^ 8
    - 238570 * s ^ 7
    + 107314 * s ^ 6
    + 29180 * s ^ 5
    - 97998 * s ^ 4
    + 85060 * s ^ 3
    - 38763 * s ^ 2
    + 8582 * s
    - 561

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient12 (s : ℚ) : ℚ :=
  16 * s ^ 13
    - 230 * s ^ 12
    + 1343 * s ^ 11
    - 3928 * s ^ 10
    + 4820 * s ^ 9
    + 5271 * s ^ 8
    - 33851 * s ^ 7
    + 73703 * s ^ 6
    - 102093 * s ^ 5
    + 97515 * s ^ 4
    - 62672 * s ^ 3
    + 24901 * s ^ 2
    - 5131 * s
    + 336

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient13 (s : ℚ) : ℚ :=
  2 * s ^ 13
    - 40 * s ^ 12
    + 350 * s ^ 11
    - 1788 * s ^ 10
    + 6048 * s ^ 9
    - 14703 * s ^ 8
    + 27330 * s ^ 7
    - 40182 * s ^ 6
    + 46320 * s ^ 5
    - 39908 * s ^ 4
    + 23896 * s ^ 3
    - 8990 * s ^ 2
    + 1782 * s
    - 117

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient14 (s : ℚ) : ℚ :=
  -s ^ 11
    + 19 * s ^ 10
    - 158 * s ^ 9
    + 757 * s ^ 8
    - 2315 * s ^ 7
    + 4729 * s ^ 6
    - 6557 * s ^ 5
    + 6133 * s ^ 4
    - 3752 * s ^ 3
    + 1400 * s ^ 2
    - 273 * s
    + 18

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def differenceLeft (r s : ℚ) : ℚ :=
  differenceLeftCoefficient0 s +
    differenceLeftCoefficient1 s * r +
    differenceLeftCoefficient2 s * r ^ 2 +
    differenceLeftCoefficient3 s * r ^ 3 +
    differenceLeftCoefficient4 s * r ^ 4 +
    differenceLeftCoefficient5 s * r ^ 5 +
    differenceLeftCoefficient6 s * r ^ 6 +
    differenceLeftCoefficient7 s * r ^ 7 +
    differenceLeftCoefficient8 s * r ^ 8 +
    differenceLeftCoefficient9 s * r ^ 9 +
    differenceLeftCoefficient10 s * r ^ 10 +
    differenceLeftCoefficient11 s * r ^ 11 +
    differenceLeftCoefficient12 s * r ^ 12 +
    differenceLeftCoefficient13 s * r ^ 13 +
    differenceLeftCoefficient14 s * r ^ 14

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_0 (s : ℚ) :
    differenceLeftCoefficient0 s =
      rawUnitTwoNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [differenceLeftCoefficient0,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_1 (s : ℚ) :
    differenceLeftCoefficient1 s =
      rawUnitTwoNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitTwoNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [differenceLeftCoefficient1,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_2 (s : ℚ) :
    differenceLeftCoefficient2 s =
      rawUnitTwoNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitTwoNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitTwoNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [differenceLeftCoefficient2,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_3 (s : ℚ) :
    differenceLeftCoefficient3 s =
      rawUnitTwoNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitTwoNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitTwoNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitTwoNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [differenceLeftCoefficient3,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient3,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_4 (s : ℚ) :
    differenceLeftCoefficient4 s =
      rawUnitTwoNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitTwoNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitTwoNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitTwoNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitTwoNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [differenceLeftCoefficient4,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient4,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient1,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_5 (s : ℚ) :
    differenceLeftCoefficient5 s =
      rawUnitTwoNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitTwoNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitTwoNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitTwoNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitTwoNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitTwoNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [differenceLeftCoefficient5,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient5,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient4,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient1,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_6 (s : ℚ) :
    differenceLeftCoefficient6 s =
      rawUnitTwoNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitTwoNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitTwoNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitTwoNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitTwoNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitTwoNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitTwoNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [differenceLeftCoefficient6,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient6,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient5,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient2,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient1,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_7 (s : ℚ) :
    differenceLeftCoefficient7 s =
      rawUnitTwoNumeratorCoefficient0 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitTwoNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitTwoNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitTwoNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitTwoNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitTwoNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitTwoNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient1 s +
        rawUnitTwoNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient0 s := by
  simp only [differenceLeftCoefficient7,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient6,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient5,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient2,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient1,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_8 (s : ℚ) :
    differenceLeftCoefficient8 s =
      rawUnitTwoNumeratorCoefficient1 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitTwoNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitTwoNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitTwoNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitTwoNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitTwoNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient2 s +
        rawUnitTwoNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient1 s := by
  simp only [differenceLeftCoefficient8,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient6,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient3,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient2,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_9 (s : ℚ) :
    differenceLeftCoefficient9 s =
      rawUnitTwoNumeratorCoefficient2 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitTwoNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitTwoNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitTwoNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitTwoNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient3 s +
        rawUnitTwoNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient2 s := by
  simp only [differenceLeftCoefficient9,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient6,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient3,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_10 (s : ℚ) :
    differenceLeftCoefficient10 s =
      rawUnitTwoNumeratorCoefficient3 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitTwoNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitTwoNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitTwoNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient4 s +
        rawUnitTwoNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient3 s := by
  simp only [differenceLeftCoefficient10,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient4,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_11 (s : ℚ) :
    differenceLeftCoefficient11 s =
      rawUnitTwoNumeratorCoefficient4 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitTwoNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitTwoNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient5 s +
        rawUnitTwoNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient4 s := by
  simp only [differenceLeftCoefficient11,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_12 (s : ℚ) :
    differenceLeftCoefficient12 s =
      rawUnitTwoNumeratorCoefficient5 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitTwoNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient6 s +
        rawUnitTwoNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient5 s := by
  simp only [differenceLeftCoefficient12,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_13 (s : ℚ) :
    differenceLeftCoefficient13 s =
      rawUnitTwoNumeratorCoefficient6 s *
          rawUnitOneDenominatorCoefficient7 s +
        rawUnitTwoNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient6 s := by
  simp only [differenceLeftCoefficient13,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_14 (s : ℚ) :
    differenceLeftCoefficient14 s =
      rawUnitTwoNumeratorCoefficient7 s *
          rawUnitOneDenominatorCoefficient7 s := by
  simp only [differenceLeftCoefficient14,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitOneDenominatorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem differenceLeft_eq_rawUnitTwoNumerator_mul_rawUnitOneDenominator (r s : ℚ) :
    differenceLeft r s =
      rawUnitTwoNumerator r s * rawUnitOneDenominator r s := by
  have h0 := differenceLeftCoefficient_product_certificate_0 s
  have h1 := differenceLeftCoefficient_product_certificate_1 s
  have h2 := differenceLeftCoefficient_product_certificate_2 s
  have h3 := differenceLeftCoefficient_product_certificate_3 s
  have h4 := differenceLeftCoefficient_product_certificate_4 s
  have h5 := differenceLeftCoefficient_product_certificate_5 s
  have h6 := differenceLeftCoefficient_product_certificate_6 s
  have h7 := differenceLeftCoefficient_product_certificate_7 s
  have h8 := differenceLeftCoefficient_product_certificate_8 s
  have h9 := differenceLeftCoefficient_product_certificate_9 s
  have h10 := differenceLeftCoefficient_product_certificate_10 s
  have h11 := differenceLeftCoefficient_product_certificate_11 s
  have h12 := differenceLeftCoefficient_product_certificate_12 s
  have h13 := differenceLeftCoefficient_product_certificate_13 s
  have h14 := differenceLeftCoefficient_product_certificate_14 s
  simp only [differenceLeft, rawUnitTwoNumerator, rawUnitOneDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 15

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient1 (s : ℚ) : ℚ :=
  -6 * s ^ 15
    + 33 * s ^ 14
    - 19 * s ^ 13
    + 10 * s ^ 12
    - 4 * s ^ 11
    + s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 18
    + 7 * s ^ 17
    - 28 * s ^ 16
    + 62 * s ^ 15
    + 26 * s ^ 14
    - 385 * s ^ 13
    + 398 * s ^ 12
    - 303 * s ^ 11
    + 182 * s ^ 10
    - 85 * s ^ 9
    + 28 * s ^ 8
    - 7 * s ^ 7
    + s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient3 (s : ℚ) : ℚ :=
  -3 * s ^ 18
    + 40 * s ^ 17
    - 229 * s ^ 16
    + 852 * s ^ 15
    - 2017 * s ^ 14
    + 2329 * s ^ 13
    - 208 * s ^ 12
    - 994 * s ^ 11
    + 1361 * s ^ 10
    - 1194 * s ^ 9
    + 798 * s ^ 8
    - 400 * s ^ 7
    + 159 * s ^ 6
    - 47 * s ^ 5
    + 9 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient4 (s : ℚ) : ℚ :=
  s ^ 20
    - 13 * s ^ 19
    + 85 * s ^ 18
    - 338 * s ^ 17
    + 813 * s ^ 16
    - 775 * s ^ 15
    - 2565 * s ^ 14
    + 11965 * s ^ 13
    - 20860 * s ^ 12
    + 18417 * s ^ 11
    - 13669 * s ^ 10
    + 9039 * s ^ 9
    - 5122 * s ^ 8
    + 2317 * s ^ 7
    - 847 * s ^ 6
    + 208 * s ^ 5
    - 18 * s ^ 4
    - 5 * s ^ 3
    + 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient5 (s : ℚ) : ℚ :=
  s ^ 20
    - 22 * s ^ 19
    + 208 * s ^ 18
    - 1230 * s ^ 17
    + 5100 * s ^ 16
    - 15479 * s ^ 15
    + 33989 * s ^ 14
    - 49663 * s ^ 13
    + 41438 * s ^ 12
    - 17231 * s ^ 11
    + 11167 * s ^ 10
    - 9639 * s ^ 9
    + 6406 * s ^ 8
    - 2807 * s ^ 7
    + 777 * s ^ 6
    + 164 * s ^ 5
    - 253 * s ^ 4
    + 95 * s ^ 3
    - 17 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient6 (s : ℚ) : ℚ :=
  s ^ 21
    - 17 * s ^ 20
    + 142 * s ^ 19
    - 761 * s ^ 18
    + 2877 * s ^ 17
    - 7756 * s ^ 16
    + 13751 * s ^ 15
    - 9949 * s ^ 14
    - 19973 * s ^ 13
    + 62150 * s ^ 12
    - 59367 * s ^ 11
    + 9546 * s ^ 10
    + 10245 * s ^ 9
    - 7230 * s ^ 8
    + 841 * s ^ 7
    + 2047 * s ^ 6
    - 2720 * s ^ 5
    + 1541 * s ^ 4
    - 433 * s ^ 3
    + 47 * s ^ 2
    + 13 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient7 (s : ℚ) : ℚ :=
  -2 * s ^ 20
    + 31 * s ^ 19
    - 257 * s ^ 18
    + 1493 * s ^ 17
    - 6544 * s ^ 16
    + 21466 * s ^ 15
    - 49912 * s ^ 14
    + 71779 * s ^ 13
    - 35552 * s ^ 12
    - 63535 * s ^ 11
    + 114536 * s ^ 10
    - 60601 * s ^ 9
    + 9526 * s ^ 8
    + 10804 * s ^ 7
    - 13708 * s ^ 6
    + 10657 * s ^ 5
    - 4660 * s ^ 4
    + 953 * s ^ 3
    + 39 * s ^ 2
    - 78 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 19
    + 21 * s ^ 18
    - 129 * s ^ 17
    + 45 * s ^ 16
    + 3725 * s ^ 15
    - 24682 * s ^ 14
    + 84147 * s ^ 13
    - 169237 * s ^ 12
    + 187117 * s ^ 11
    - 68966 * s ^ 10
    - 65625 * s ^ 9
    + 84225 * s ^ 8
    - 60684 * s ^ 7
    + 39898 * s ^ 6
    - 22901 * s ^ 5
    + 7347 * s ^ 4
    - 284 * s ^ 3
    - 739 * s ^ 2
    + 288 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 19
    + 26 * s ^ 18
    - 293 * s ^ 17
    + 1899 * s ^ 16
    - 7777 * s ^ 15
    + 19802 * s ^ 14
    - 24394 * s ^ 13
    - 20256 * s ^ 12
    + 138199 * s ^ 11
    - 244302 * s ^ 10
    + 214742 * s ^ 9
    - 105454 * s ^ 8
    + 55647 * s ^ 7
    - 39517 * s ^ 6
    + 20335 * s ^ 5
    - 1274 * s ^ 4
    - 4374 * s ^ 3
    + 2705 * s ^ 2
    - 707 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient10 (s : ℚ) : ℚ :=
  2 * s ^ 18
    - 46 * s ^ 17
    + 489 * s ^ 16
    - 3182 * s ^ 15
    + 13950 * s ^ 14
    - 42149 * s ^ 13
    + 85360 * s ^ 12
    - 104481 * s ^ 11
    + 50262 * s ^ 10
    + 40152 * s ^ 9
    - 57992 * s ^ 8
    + 6429 * s ^ 7
    + 13565 * s ^ 6
    + 1590 * s ^ 5
    - 15402 * s ^ 4
    + 12742 * s ^ 3
    - 5471 * s ^ 2
    + 1172 * s
    + 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 17
    + 23 * s ^ 16
    - 258 * s ^ 15
    + 1827 * s ^ 14
    - 8786 * s ^ 13
    + 29089 * s ^ 12
    - 65119 * s ^ 11
    + 92959 * s ^ 10
    - 71473 * s ^ 9
    + 8459 * s ^ 8
    + 24468 * s ^ 7
    - 1017 * s ^ 6
    - 26960 * s ^ 5
    + 31284 * s ^ 4
    - 18732 * s ^ 3
    + 6919 * s ^ 2
    - 1296 * s
    - 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient12 (s : ℚ) : ℚ :=
  -2 * s ^ 15
    + 49 * s ^ 14
    - 519 * s ^ 13
    + 3140 * s ^ 12
    - 11969 * s ^ 11
    + 29591 * s ^ 10
    - 46193 * s ^ 9
    + 39380 * s ^ 8
    - 3364 * s ^ 7
    - 32713 * s ^ 6
    + 42500 * s ^ 5
    - 32005 * s ^ 4
    + 16146 * s ^ 3
    - 5433 * s ^ 2
    + 902 * s
    + 35

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient13 (s : ℚ) : ℚ :=
  s ^ 14
    - 22 * s ^ 13
    + 218 * s ^ 12
    - 1282 * s ^ 11
    + 4957 * s ^ 10
    - 13197 * s ^ 9
    + 24720 * s ^ 8
    - 33070 * s ^ 7
    + 32483 * s ^ 6
    - 24797 * s ^ 5
    + 15384 * s ^ 4
    - 7280 * s ^ 3
    + 2359 * s ^ 2
    - 335 * s
    - 34

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient14 (s : ℚ) : ℚ :=
  -s ^ 10
    + 17 * s ^ 9
    - 124 * s ^ 8
    + 506 * s ^ 7
    - 1264 * s ^ 6
    + 1988 * s ^ 5
    - 1954 * s ^ 4
    + 1172 * s ^ 3
    - 405 * s ^ 2
    + 32 * s
    + 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient15 (s : ℚ) : ℚ :=
  s ^ 3
    - 6 * s ^ 2
    + 10 * s
    - 4

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def differenceRight (r s : ℚ) : ℚ :=
  differenceRightCoefficient0 s +
    differenceRightCoefficient1 s * r +
    differenceRightCoefficient2 s * r ^ 2 +
    differenceRightCoefficient3 s * r ^ 3 +
    differenceRightCoefficient4 s * r ^ 4 +
    differenceRightCoefficient5 s * r ^ 5 +
    differenceRightCoefficient6 s * r ^ 6 +
    differenceRightCoefficient7 s * r ^ 7 +
    differenceRightCoefficient8 s * r ^ 8 +
    differenceRightCoefficient9 s * r ^ 9 +
    differenceRightCoefficient10 s * r ^ 10 +
    differenceRightCoefficient11 s * r ^ 11 +
    differenceRightCoefficient12 s * r ^ 12 +
    differenceRightCoefficient13 s * r ^ 13 +
    differenceRightCoefficient14 s * r ^ 14 +
    differenceRightCoefficient15 s * r ^ 15

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_0 (s : ℚ) :
    differenceRightCoefficient0 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [differenceRightCoefficient0,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_1 (s : ℚ) :
    differenceRightCoefficient1 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [differenceRightCoefficient1,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_2 (s : ℚ) :
    differenceRightCoefficient2 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [differenceRightCoefficient2,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_3 (s : ℚ) :
    differenceRightCoefficient3 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [differenceRightCoefficient3,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_4 (s : ℚ) :
    differenceRightCoefficient4 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [differenceRightCoefficient4,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_5 (s : ℚ) :
    differenceRightCoefficient5 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [differenceRightCoefficient5,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_6 (s : ℚ) :
    differenceRightCoefficient6 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [differenceRightCoefficient6,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_7 (s : ℚ) :
    differenceRightCoefficient7 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient1 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient0 s := by
  simp only [differenceRightCoefficient7,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_8 (s : ℚ) :
    differenceRightCoefficient8 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitTwoDenominatorCoefficient8 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient2 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient1 s := by
  simp only [differenceRightCoefficient8,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_9 (s : ℚ) :
    differenceRightCoefficient9 s =
      rawUnitOneNumeratorCoefficient1 s *
          rawUnitTwoDenominatorCoefficient8 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient3 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient2 s := by
  simp only [differenceRightCoefficient9,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_10 (s : ℚ) :
    differenceRightCoefficient10 s =
      rawUnitOneNumeratorCoefficient2 s *
          rawUnitTwoDenominatorCoefficient8 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient4 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient3 s := by
  simp only [differenceRightCoefficient10,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_11 (s : ℚ) :
    differenceRightCoefficient11 s =
      rawUnitOneNumeratorCoefficient3 s *
          rawUnitTwoDenominatorCoefficient8 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient5 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient4 s := by
  simp only [differenceRightCoefficient11,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_12 (s : ℚ) :
    differenceRightCoefficient12 s =
      rawUnitOneNumeratorCoefficient4 s *
          rawUnitTwoDenominatorCoefficient8 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient6 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient5 s := by
  simp only [differenceRightCoefficient12,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_13 (s : ℚ) :
    differenceRightCoefficient13 s =
      rawUnitOneNumeratorCoefficient5 s *
          rawUnitTwoDenominatorCoefficient8 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient7 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient6 s := by
  simp only [differenceRightCoefficient13,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_14 (s : ℚ) :
    differenceRightCoefficient14 s =
      rawUnitOneNumeratorCoefficient6 s *
          rawUnitTwoDenominatorCoefficient8 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient7 s := by
  simp only [differenceRightCoefficient14,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem differenceRightCoefficient_product_certificate_15 (s : ℚ) :
    differenceRightCoefficient15 s =
      rawUnitOneNumeratorCoefficient7 s *
          rawUnitTwoDenominatorCoefficient8 s := by
  simp only [differenceRightCoefficient15,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem differenceRight_eq_rawUnitOneNumerator_mul_rawUnitTwoDenominator (r s : ℚ) :
    differenceRight r s =
      rawUnitOneNumerator r s * rawUnitTwoDenominator r s := by
  have h0 := differenceRightCoefficient_product_certificate_0 s
  have h1 := differenceRightCoefficient_product_certificate_1 s
  have h2 := differenceRightCoefficient_product_certificate_2 s
  have h3 := differenceRightCoefficient_product_certificate_3 s
  have h4 := differenceRightCoefficient_product_certificate_4 s
  have h5 := differenceRightCoefficient_product_certificate_5 s
  have h6 := differenceRightCoefficient_product_certificate_6 s
  have h7 := differenceRightCoefficient_product_certificate_7 s
  have h8 := differenceRightCoefficient_product_certificate_8 s
  have h9 := differenceRightCoefficient_product_certificate_9 s
  have h10 := differenceRightCoefficient_product_certificate_10 s
  have h11 := differenceRightCoefficient_product_certificate_11 s
  have h12 := differenceRightCoefficient_product_certificate_12 s
  have h13 := differenceRightCoefficient_product_certificate_13 s
  have h14 := differenceRightCoefficient_product_certificate_14 s
  have h15 := differenceRightCoefficient_product_certificate_15 s
  simp only [differenceRight, rawUnitOneNumerator, rawUnitTwoDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient0 (s : ℚ) : ℚ :=
  s ^ 15

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient1 (s : ℚ) : ℚ :=
  6 * s ^ 15
    - 33 * s ^ 14
    + 19 * s ^ 13
    - 10 * s ^ 12
    + 4 * s ^ 11
    - s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient2 (s : ℚ) : ℚ :=
  s ^ 19
    - 6 * s ^ 18
    + 19 * s ^ 17
    - 40 * s ^ 16
    + 77 * s ^ 15
    - 261 * s ^ 14
    + 725 * s ^ 13
    - 828 * s ^ 12
    + 785 * s ^ 11
    - 664 * s ^ 10
    + 515 * s ^ 9
    - 368 * s ^ 8
    + 242 * s ^ 7
    - 140 * s ^ 6
    + 68 * s ^ 5
    - 26 * s ^ 4
    + 7 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient3 (s : ℚ) : ℚ :=
  s ^ 20
    - 8 * s ^ 19
    + 28 * s ^ 18
    - 90 * s ^ 17
    + 320 * s ^ 16
    - 1050 * s ^ 15
    + 2502 * s ^ 14
    - 3411 * s ^ 13
    + 2234 * s ^ 12
    - 2170 * s ^ 11
    + 2789 * s ^ 10
    - 3408 * s ^ 9
    + 3521 * s ^ 8
    - 3010 * s ^ 7
    + 2074 * s ^ 6
    - 1131 * s ^ 5
    + 466 * s ^ 4
    - 131 * s ^ 3
    + 19 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient4 (s : ℚ) : ℚ :=
  -3 * s ^ 19
    - 8 * s ^ 18
    + 201 * s ^ 17
    - 911 * s ^ 16
    + 2036 * s ^ 15
    - 1669 * s ^ 14
    - 2225 * s ^ 13
    + 3084 * s ^ 12
    + 8659 * s ^ 11
    - 21409 * s ^ 10
    + 29863 * s ^ 9
    - 31725 * s ^ 8
    + 27211 * s ^ 7
    - 18816 * s ^ 6
    + 10323 * s ^ 5
    - 4274 * s ^ 4
    + 1200 * s ^ 3
    - 172 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient5 (s : ℚ) : ℚ :=
  s ^ 20
    - 18 * s ^ 19
    + 130 * s ^ 18
    - 364 * s ^ 17
    - 11 * s ^ 16
    + 2685 * s ^ 15
    - 6523 * s ^ 14
    - 2271 * s ^ 13
    + 45669 * s ^ 12
    - 111625 * s ^ 11
    + 155593 * s ^ 10
    - 177761 * s ^ 9
    + 174638 * s ^ 8
    - 145437 * s ^ 7
    + 99859 * s ^ 6
    - 54796 * s ^ 5
    + 22612 * s ^ 4
    - 6233 * s ^ 3
    + 833 * s ^ 2
    + 17 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient6 (s : ℚ) : ℚ :=
  -9 * s ^ 19
    + 132 * s ^ 18
    - 738 * s ^ 17
    + 1370 * s ^ 16
    + 4585 * s ^ 15
    - 37797 * s ^ 14
    + 126986 * s ^ 13
    - 266030 * s ^ 12
    + 390046 * s ^ 11
    - 468403 * s ^ 10
    + 534998 * s ^ 9
    - 544101 * s ^ 8
    + 467308 * s ^ 7
    - 328192 * s ^ 6
    + 182181 * s ^ 5
    - 74711 * s ^ 4
    + 19740 * s ^ 3
    - 2170 * s ^ 2
    - 202 * s
    + 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient7 (s : ℚ) : ℚ :=
  -9 * s ^ 19
    + 204 * s ^ 18
    - 2015 * s ^ 17
    + 11633 * s ^ 16
    - 44430 * s ^ 15
    + 120741 * s ^ 14
    - 242929 * s ^ 13
    + 379094 * s ^ 12
    - 523021 * s ^ 11
    + 744131 * s ^ 10
    - 1013401 * s ^ 9
    + 1125866 * s ^ 8
    - 1008584 * s ^ 7
    + 723723 * s ^ 6
    - 403083 * s ^ 5
    + 161056 * s ^ 4
    - 38507 * s ^ 3
    + 2071 * s ^ 2
    + 1090 * s
    - 65

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient8 (s : ℚ) : ℚ :=
  -2 * s ^ 20
    + 42 * s ^ 19
    - 401 * s ^ 18
    + 2275 * s ^ 17
    - 8540 * s ^ 16
    + 22763 * s ^ 15
    - 47021 * s ^ 14
    + 90262 * s ^ 13
    - 205380 * s ^ 12
    + 508379 * s ^ 11
    - 1031127 * s ^ 10
    + 1529746 * s ^ 9
    - 1704004 * s ^ 8
    + 1525718 * s ^ 7
    - 1093421 * s ^ 6
    + 597110 * s ^ 5
    - 222046 * s ^ 4
    + 40209 * s ^ 3
    + 5166 * s ^ 2
    - 3501 * s
    + 208

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient9 (s : ℚ) : ℚ :=
  3 * s ^ 19
    - 54 * s ^ 18
    + 423 * s ^ 17
    - 1750 * s ^ 16
    + 2933 * s ^ 15
    + 9128 * s ^ 14
    - 80976 * s ^ 13
    + 301173 * s ^ 12
    - 728479 * s ^ 11
    + 1250490 * s ^ 10
    - 1617556 * s ^ 9
    + 1700937 * s ^ 8
    - 1513391 * s ^ 7
    + 1074363 * s ^ 6
    - 553817 * s ^ 5
    + 166821 * s ^ 4
    + 744 * s ^ 3
    - 22913 * s ^ 2
    + 7347 * s
    - 431

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient10 (s : ℚ) : ℚ :=
  s ^ 19
    - 25 * s ^ 18
    + 290 * s ^ 17
    - 2092 * s ^ 16
    + 10588 * s ^ 15
    - 40082 * s ^ 14
    + 117083 * s ^ 13
    - 266089 * s ^ 12
    + 472260 * s ^ 11
    - 674721 * s ^ 10
    + 834552 * s ^ 9
    - 937217 * s ^ 8
    + 885889 * s ^ 7
    - 607525 * s ^ 6
    + 249026 * s ^ 5
    - 2931 * s ^ 4
    - 68254 * s ^ 3
    + 42053 * s ^ 2
    - 10398 * s
    + 595

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 17
    + 21 * s ^ 16
    - 196 * s ^ 15
    + 1065 * s ^ 14
    - 3822 * s ^ 13
    + 10711 * s ^ 12
    - 29781 * s ^ 11
    + 83566 * s ^ 10
    - 187631 * s ^ 9
    + 285104 * s ^ 8
    - 263038 * s ^ 7
    + 108331 * s ^ 6
    + 56140 * s ^ 5
    - 129282 * s ^ 4
    + 103792 * s ^ 3
    - 45682 * s ^ 2
    + 9878 * s
    - 540

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient12 (s : ℚ) : ℚ :=
  2 * s ^ 15
    - 49 * s ^ 14
    + 535 * s ^ 13
    - 3370 * s ^ 12
    + 13312 * s ^ 11
    - 33519 * s ^ 10
    + 51013 * s ^ 9
    - 34109 * s ^ 8
    - 30487 * s ^ 7
    + 106416 * s ^ 6
    - 144593 * s ^ 5
    + 129520 * s ^ 4
    - 78818 * s ^ 3
    + 30334 * s ^ 2
    - 6033 * s
    + 301

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient13 (s : ℚ) : ℚ :=
  -s ^ 14
    + 24 * s ^ 13
    - 258 * s ^ 12
    + 1632 * s ^ 11
    - 6745 * s ^ 10
    + 19245 * s ^ 9
    - 39423 * s ^ 8
    + 60400 * s ^ 7
    - 72665 * s ^ 6
    + 71117 * s ^ 5
    - 55292 * s ^ 4
    + 31176 * s ^ 3
    - 11349 * s ^ 2
    + 2117 * s
    - 83

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient14 (s : ℚ) : ℚ :=
  -s ^ 11
    + 20 * s ^ 10
    - 175 * s ^ 9
    + 881 * s ^ 8
    - 2821 * s ^ 7
    + 5993 * s ^ 6
    - 8545 * s ^ 5
    + 8087 * s ^ 4
    - 4924 * s ^ 3
    + 1805 * s ^ 2
    - 305 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient15 (s : ℚ) : ℚ :=
  -s ^ 3
    + 6 * s ^ 2
    - 10 * s
    + 4

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def difference (r s : ℚ) : ℚ :=
  differenceCoefficient0 s +
    differenceCoefficient1 s * r +
    differenceCoefficient2 s * r ^ 2 +
    differenceCoefficient3 s * r ^ 3 +
    differenceCoefficient4 s * r ^ 4 +
    differenceCoefficient5 s * r ^ 5 +
    differenceCoefficient6 s * r ^ 6 +
    differenceCoefficient7 s * r ^ 7 +
    differenceCoefficient8 s * r ^ 8 +
    differenceCoefficient9 s * r ^ 9 +
    differenceCoefficient10 s * r ^ 10 +
    differenceCoefficient11 s * r ^ 11 +
    differenceCoefficient12 s * r ^ 12 +
    differenceCoefficient13 s * r ^ 13 +
    differenceCoefficient14 s * r ^ 14 +
    differenceCoefficient15 s * r ^ 15

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_0 (s : ℚ) :
    differenceCoefficient0 s =
      differenceLeftCoefficient0 s
        - differenceRightCoefficient0 s := by
  simp only [differenceCoefficient0,
    differenceLeftCoefficient0,
    differenceRightCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_1 (s : ℚ) :
    differenceCoefficient1 s =
      differenceLeftCoefficient1 s
        - differenceRightCoefficient1 s := by
  simp only [differenceCoefficient1,
    differenceLeftCoefficient1,
    differenceRightCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_2 (s : ℚ) :
    differenceCoefficient2 s =
      differenceLeftCoefficient2 s
        - differenceRightCoefficient2 s := by
  simp only [differenceCoefficient2,
    differenceLeftCoefficient2,
    differenceRightCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_3 (s : ℚ) :
    differenceCoefficient3 s =
      differenceLeftCoefficient3 s
        - differenceRightCoefficient3 s := by
  simp only [differenceCoefficient3,
    differenceLeftCoefficient3,
    differenceRightCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_4 (s : ℚ) :
    differenceCoefficient4 s =
      differenceLeftCoefficient4 s
        - differenceRightCoefficient4 s := by
  simp only [differenceCoefficient4,
    differenceLeftCoefficient4,
    differenceRightCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_5 (s : ℚ) :
    differenceCoefficient5 s =
      differenceLeftCoefficient5 s
        - differenceRightCoefficient5 s := by
  simp only [differenceCoefficient5,
    differenceLeftCoefficient5,
    differenceRightCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_6 (s : ℚ) :
    differenceCoefficient6 s =
      differenceLeftCoefficient6 s
        - differenceRightCoefficient6 s := by
  simp only [differenceCoefficient6,
    differenceLeftCoefficient6,
    differenceRightCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_7 (s : ℚ) :
    differenceCoefficient7 s =
      differenceLeftCoefficient7 s
        - differenceRightCoefficient7 s := by
  simp only [differenceCoefficient7,
    differenceLeftCoefficient7,
    differenceRightCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_8 (s : ℚ) :
    differenceCoefficient8 s =
      differenceLeftCoefficient8 s
        - differenceRightCoefficient8 s := by
  simp only [differenceCoefficient8,
    differenceLeftCoefficient8,
    differenceRightCoefficient8]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_9 (s : ℚ) :
    differenceCoefficient9 s =
      differenceLeftCoefficient9 s
        - differenceRightCoefficient9 s := by
  simp only [differenceCoefficient9,
    differenceLeftCoefficient9,
    differenceRightCoefficient9]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_10 (s : ℚ) :
    differenceCoefficient10 s =
      differenceLeftCoefficient10 s
        - differenceRightCoefficient10 s := by
  simp only [differenceCoefficient10,
    differenceLeftCoefficient10,
    differenceRightCoefficient10]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_11 (s : ℚ) :
    differenceCoefficient11 s =
      differenceLeftCoefficient11 s
        - differenceRightCoefficient11 s := by
  simp only [differenceCoefficient11,
    differenceLeftCoefficient11,
    differenceRightCoefficient11]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_12 (s : ℚ) :
    differenceCoefficient12 s =
      differenceLeftCoefficient12 s
        - differenceRightCoefficient12 s := by
  simp only [differenceCoefficient12,
    differenceLeftCoefficient12,
    differenceRightCoefficient12]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_13 (s : ℚ) :
    differenceCoefficient13 s =
      differenceLeftCoefficient13 s
        - differenceRightCoefficient13 s := by
  simp only [differenceCoefficient13,
    differenceLeftCoefficient13,
    differenceRightCoefficient13]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_14 (s : ℚ) :
    differenceCoefficient14 s =
      differenceLeftCoefficient14 s
        - differenceRightCoefficient14 s := by
  simp only [differenceCoefficient14,
    differenceLeftCoefficient14,
    differenceRightCoefficient14]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem differenceCoefficient_linear_certificate_15 (s : ℚ) :
    differenceCoefficient15 s =
      -differenceRightCoefficient15 s := by
  simp only [differenceCoefficient15,
    differenceRightCoefficient15]
  ring

/-- Checked staged polynomial-sum identity. -/
theorem difference_eq_linearCombination (r s : ℚ) :
    difference r s =
      differenceLeft r s
        - differenceRight r s := by
  have h0 := differenceCoefficient_linear_certificate_0 s
  have h1 := differenceCoefficient_linear_certificate_1 s
  have h2 := differenceCoefficient_linear_certificate_2 s
  have h3 := differenceCoefficient_linear_certificate_3 s
  have h4 := differenceCoefficient_linear_certificate_4 s
  have h5 := differenceCoefficient_linear_certificate_5 s
  have h6 := differenceCoefficient_linear_certificate_6 s
  have h7 := differenceCoefficient_linear_certificate_7 s
  have h8 := differenceCoefficient_linear_certificate_8 s
  have h9 := differenceCoefficient_linear_certificate_9 s
  have h10 := differenceCoefficient_linear_certificate_10 s
  have h11 := differenceCoefficient_linear_certificate_11 s
  have h12 := differenceCoefficient_linear_certificate_12 s
  have h13 := differenceCoefficient_linear_certificate_13 s
  have h14 := differenceCoefficient_linear_certificate_14 s
  have h15 := differenceCoefficient_linear_certificate_15 s
  simp only [difference, differenceLeft, differenceRight]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient0 (s : ℚ) : ℚ :=
  s ^ 11
    - s ^ 10
    + s ^ 9
    - s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient1 (s : ℚ) : ℚ :=
  3 * s ^ 11
    - 21 * s ^ 10
    + 27 * s ^ 9
    - 30 * s ^ 8
    + 31 * s ^ 7
    - 14 * s ^ 6
    + 5 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 13
    + 8 * s ^ 12
    - 29 * s ^ 11
    + 35 * s ^ 10
    + 49 * s ^ 9
    - 79 * s ^ 8
    + 113 * s ^ 7
    - 176 * s ^ 6
    + 130 * s ^ 5
    - 73 * s ^ 4
    + 29 * s ^ 3
    - 7 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient3 (s : ℚ) : ℚ :=
  -s ^ 13
    + 17 * s ^ 12
    - 105 * s ^ 11
    + 352 * s ^ 10
    - 643 * s ^ 9
    + 693 * s ^ 8
    - 934 * s ^ 7
    + 1045 * s ^ 6
    - 680 * s ^ 5
    + 369 * s ^ 4
    - 139 * s ^ 3
    + 29 * s ^ 2
    - 2 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 14
    + 12 * s ^ 13
    - 66 * s ^ 12
    + 204 * s ^ 11
    - 373 * s ^ 10
    + 442 * s ^ 9
    - 797 * s ^ 8
    + 1876 * s ^ 7
    - 1978 * s ^ 6
    + 1131 * s ^ 5
    - 630 * s ^ 4
    + 192 * s ^ 3
    - 21 * s
    + 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient5 (s : ℚ) : ℚ :=
  2 * s ^ 13
    - 20 * s ^ 12
    + 84 * s ^ 11
    - 130 * s ^ 10
    - 270 * s ^ 9
    + 1613 * s ^ 8
    - 2707 * s ^ 7
    + 1602 * s ^ 6
    - 434 * s ^ 5
    + 239 * s ^ 4
    + 173 * s ^ 3
    - 240 * s ^ 2
    + 124 * s
    - 36

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient6 (s : ℚ) : ℚ :=
  s ^ 13
    - 16 * s ^ 12
    + 113 * s ^ 11
    - 467 * s ^ 10
    + 1174 * s ^ 9
    - 1592 * s ^ 8
    + 457 * s ^ 7
    + 1386 * s ^ 6
    - 1285 * s ^ 5
    + 735 * s ^ 4
    - 974 * s ^ 3
    + 703 * s ^ 2
    - 318 * s
    + 83

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient7 (s : ℚ) : ℚ :=
  -s ^ 12
    + 15 * s ^ 11
    - 109 * s ^ 10
    + 487 * s ^ 9
    - 1375 * s ^ 8
    + 2332 * s ^ 7
    - 2085 * s ^ 6
    + 933 * s ^ 5
    - 1023 * s ^ 4
    + 1511 * s ^ 3
    - 1040 * s ^ 2
    + 474 * s
    - 119

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient8 (s : ℚ) : ℚ :=
  -s ^ 10
    + 19 * s ^ 9
    - 133 * s ^ 8
    + 452 * s ^ 7
    - 727 * s ^ 6
    + 199 * s ^ 5
    + 1000 * s ^ 4
    - 1405 * s ^ 3
    + 921 * s ^ 2
    - 431 * s
    + 106

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient9 (s : ℚ) : ℚ :=
  s ^ 9
    - 15 * s ^ 8
    + 96 * s ^ 7
    - 340 * s ^ 6
    + 717 * s ^ 5
    - 912 * s ^ 4
    + 728 * s ^ 3
    - 441 * s ^ 2
    + 220 * s
    - 54

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient10 (s : ℚ) : ℚ :=
  -s ^ 5
    + 10 * s ^ 4
    - 37 * s ^ 3
    + 62 * s ^ 2
    - 46 * s
    + 12

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t3Step1 (r s : ℚ) : ℚ :=
  t3Step1Coefficient0 s +
    t3Step1Coefficient1 s * r +
    t3Step1Coefficient2 s * r ^ 2 +
    t3Step1Coefficient3 s * r ^ 3 +
    t3Step1Coefficient4 s * r ^ 4 +
    t3Step1Coefficient5 s * r ^ 5 +
    t3Step1Coefficient6 s * r ^ 6 +
    t3Step1Coefficient7 s * r ^ 7 +
    t3Step1Coefficient8 s * r ^ 8 +
    t3Step1Coefficient9 s * r ^ 9 +
    t3Step1Coefficient10 s * r ^ 10

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_0 (s : ℚ) :
    t3Step1Coefficient0 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitEightNumeratorCoefficient0 s := by
  simp only [t3Step1Coefficient0,
    rawUnitOneNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_1 (s : ℚ) :
    t3Step1Coefficient1 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitEightNumeratorCoefficient1 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitEightNumeratorCoefficient0 s := by
  simp only [t3Step1Coefficient1,
    rawUnitOneNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_2 (s : ℚ) :
    t3Step1Coefficient2 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitEightNumeratorCoefficient2 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitEightNumeratorCoefficient1 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitEightNumeratorCoefficient0 s := by
  simp only [t3Step1Coefficient2,
    rawUnitOneNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_3 (s : ℚ) :
    t3Step1Coefficient3 s =
      rawUnitOneNumeratorCoefficient0 s *
          rawUnitEightNumeratorCoefficient3 s +
        rawUnitOneNumeratorCoefficient1 s *
          rawUnitEightNumeratorCoefficient2 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitEightNumeratorCoefficient1 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitEightNumeratorCoefficient0 s := by
  simp only [t3Step1Coefficient3,
    rawUnitOneNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_4 (s : ℚ) :
    t3Step1Coefficient4 s =
      rawUnitOneNumeratorCoefficient1 s *
          rawUnitEightNumeratorCoefficient3 s +
        rawUnitOneNumeratorCoefficient2 s *
          rawUnitEightNumeratorCoefficient2 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitEightNumeratorCoefficient1 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitEightNumeratorCoefficient0 s := by
  simp only [t3Step1Coefficient4,
    rawUnitOneNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient4,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_5 (s : ℚ) :
    t3Step1Coefficient5 s =
      rawUnitOneNumeratorCoefficient2 s *
          rawUnitEightNumeratorCoefficient3 s +
        rawUnitOneNumeratorCoefficient3 s *
          rawUnitEightNumeratorCoefficient2 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitEightNumeratorCoefficient1 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitEightNumeratorCoefficient0 s := by
  simp only [t3Step1Coefficient5,
    rawUnitOneNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient4,
    rawUnitEightNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient5,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_6 (s : ℚ) :
    t3Step1Coefficient6 s =
      rawUnitOneNumeratorCoefficient3 s *
          rawUnitEightNumeratorCoefficient3 s +
        rawUnitOneNumeratorCoefficient4 s *
          rawUnitEightNumeratorCoefficient2 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitEightNumeratorCoefficient1 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitEightNumeratorCoefficient0 s := by
  simp only [t3Step1Coefficient6,
    rawUnitOneNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitEightNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient5,
    rawUnitEightNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient6,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_7 (s : ℚ) :
    t3Step1Coefficient7 s =
      rawUnitOneNumeratorCoefficient4 s *
          rawUnitEightNumeratorCoefficient3 s +
        rawUnitOneNumeratorCoefficient5 s *
          rawUnitEightNumeratorCoefficient2 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitEightNumeratorCoefficient1 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitEightNumeratorCoefficient0 s := by
  simp only [t3Step1Coefficient7,
    rawUnitOneNumeratorCoefficient4,
    rawUnitEightNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient5,
    rawUnitEightNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient6,
    rawUnitEightNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient7,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_8 (s : ℚ) :
    t3Step1Coefficient8 s =
      rawUnitOneNumeratorCoefficient5 s *
          rawUnitEightNumeratorCoefficient3 s +
        rawUnitOneNumeratorCoefficient6 s *
          rawUnitEightNumeratorCoefficient2 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitEightNumeratorCoefficient1 s := by
  simp only [t3Step1Coefficient8,
    rawUnitOneNumeratorCoefficient5,
    rawUnitEightNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient6,
    rawUnitEightNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient7,
    rawUnitEightNumeratorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_9 (s : ℚ) :
    t3Step1Coefficient9 s =
      rawUnitOneNumeratorCoefficient6 s *
          rawUnitEightNumeratorCoefficient3 s +
        rawUnitOneNumeratorCoefficient7 s *
          rawUnitEightNumeratorCoefficient2 s := by
  simp only [t3Step1Coefficient9,
    rawUnitOneNumeratorCoefficient6,
    rawUnitEightNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient7,
    rawUnitEightNumeratorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step1Coefficient_product_certificate_10 (s : ℚ) :
    t3Step1Coefficient10 s =
      rawUnitOneNumeratorCoefficient7 s *
          rawUnitEightNumeratorCoefficient3 s := by
  simp only [t3Step1Coefficient10,
    rawUnitOneNumeratorCoefficient7,
    rawUnitEightNumeratorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t3Step1_eq_rawUnitOneNumerator_mul_rawUnitEightNumerator (r s : ℚ) :
    t3Step1 r s =
      rawUnitOneNumerator r s * rawUnitEightNumerator r s := by
  have h0 := t3Step1Coefficient_product_certificate_0 s
  have h1 := t3Step1Coefficient_product_certificate_1 s
  have h2 := t3Step1Coefficient_product_certificate_2 s
  have h3 := t3Step1Coefficient_product_certificate_3 s
  have h4 := t3Step1Coefficient_product_certificate_4 s
  have h5 := t3Step1Coefficient_product_certificate_5 s
  have h6 := t3Step1Coefficient_product_certificate_6 s
  have h7 := t3Step1Coefficient_product_certificate_7 s
  have h8 := t3Step1Coefficient_product_certificate_8 s
  have h9 := t3Step1Coefficient_product_certificate_9 s
  have h10 := t3Step1Coefficient_product_certificate_10 s
  simp only [t3Step1, rawUnitOneNumerator, rawUnitEightNumerator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient0 (s : ℚ) : ℚ :=
  s ^ 26
    - s ^ 25
    + s ^ 24
    - s ^ 23

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient1 (s : ℚ) : ℚ :=
  9 * s ^ 26
    - 60 * s ^ 25
    + 85 * s ^ 24
    - 98 * s ^ 23
    + 97 * s ^ 22
    - 48 * s ^ 21
    + 20 * s ^ 20
    - 6 * s ^ 19
    + s ^ 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient2 (s : ℚ) : ℚ :=
  s ^ 30
    - 7 * s ^ 29
    + 25 * s ^ 28
    - 58 * s ^ 27
    + 131 * s ^ 26
    - 587 * s ^ 25
    + 2064 * s ^ 24
    - 3470 * s ^ 23
    + 4623 * s ^ 22
    - 5212 * s ^ 21
    + 4432 * s ^ 20
    - 3299 * s ^ 19
    + 2240 * s ^ 18
    - 1428 * s ^ 17
    + 863 * s ^ 16
    - 485 * s ^ 15
    + 242 * s ^ 14
    - 102 * s ^ 13
    + 34 * s ^ 12
    - 8 * s ^ 11
    + s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient3 (s : ℚ) : ℚ :=
  s ^ 31
    - 6 * s ^ 30
    - 2 * s ^ 29
    + 76 * s ^ 28
    - 167 * s ^ 27
    - 255 * s ^ 26
    + 1393 * s ^ 25
    + 2191 * s ^ 24
    - 19816 * s ^ 23
    + 42687 * s ^ 22
    - 66929 * s ^ 21
    + 86483 * s ^ 20
    - 87907 * s ^ 19
    + 76569 * s ^ 18
    - 59788 * s ^ 17
    + 43208 * s ^ 16
    - 29467 * s ^ 15
    + 18972 * s ^ 14
    - 11295 * s ^ 13
    + 6031 * s ^ 12
    - 2788 * s ^ 11
    + 1072 * s ^ 10
    - 327 * s ^ 9
    + 75 * s ^ 8
    - 12 * s ^ 7
    + s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 32
    + 17 * s ^ 31
    - 144 * s ^ 30
    + 674 * s ^ 29
    - 2001 * s ^ 28
    + 5158 * s ^ 27
    - 16180 * s ^ 26
    + 55178 * s ^ 25
    - 146061 * s ^ 24
    + 251448 * s ^ 23
    - 278591 * s ^ 22
    + 245561 * s ^ 21
    - 145028 * s ^ 20
    - 7712 * s ^ 19
    + 99703 * s ^ 18
    - 113292 * s ^ 17
    + 79689 * s ^ 16
    - 40017 * s ^ 15
    + 18117 * s ^ 14
    - 14744 * s ^ 13
    + 18413 * s ^ 12
    - 19586 * s ^ 11
    + 15904 * s ^ 10
    - 9927 * s ^ 9
    + 4791 * s ^ 8
    - 1785 * s ^ 7
    + 507 * s ^ 6
    - 104 * s ^ 5
    + 14 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 33
    + 15 * s ^ 32
    - 97 * s ^ 31
    + 327 * s ^ 30
    - 556 * s ^ 29
    + 1506 * s ^ 28
    - 11616 * s ^ 27
    + 49478 * s ^ 26
    - 96069 * s ^ 25
    - 27967 * s ^ 24
    + 626794 * s ^ 23
    - 1625724 * s ^ 22
    + 2497867 * s ^ 21
    - 3163686 * s ^ 20
    + 3338340 * s ^ 19
    - 2774188 * s ^ 18
    + 1998150 * s ^ 17
    - 1425253 * s ^ 16
    + 1185838 * s ^ 15
    - 1166042 * s ^ 14
    + 1163437 * s ^ 13
    - 1043257 * s ^ 12
    + 801218 * s ^ 11
    - 517271 * s ^ 10
    + 276960 * s ^ 9
    - 121063 * s ^ 8
    + 42365 * s ^ 7
    - 11499 * s ^ 6
    + 2260 * s ^ 5
    - 281 * s ^ 4
    + 14 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient6 (s : ℚ) : ℚ :=
  -2 * s ^ 33
    + 46 * s ^ 32
    - 439 * s ^ 31
    + 2364 * s ^ 30
    - 8075 * s ^ 29
    + 21230 * s ^ 28
    - 72754 * s ^ 27
    + 332796 * s ^ 26
    - 1250300 * s ^ 25
    + 3300621 * s ^ 24
    - 5969556 * s ^ 23
    + 7442637 * s ^ 22
    - 7123086 * s ^ 21
    + 6418581 * s ^ 20
    - 5071991 * s ^ 19
    + 4260900 * s ^ 18
    - 6506025 * s ^ 17
    + 11118876 * s ^ 16
    - 15943711 * s ^ 15
    + 18801226 * s ^ 14
    - 18558939 * s ^ 13
    + 15530795 * s ^ 12
    - 11068547 * s ^ 11
    + 6693420 * s ^ 10
    - 3397638 * s ^ 9
    + 1423350 * s ^ 8
    - 480239 * s ^ 7
    + 125071 * s ^ 6
    - 22959 * s ^ 5
    + 2371 * s ^ 4
    + 5 * s ^ 3
    - 28 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient7 (s : ℚ) : ℚ :=
  -s ^ 34
    + 19 * s ^ 33
    - 159 * s ^ 32
    + 780 * s ^ 31
    - 3108 * s ^ 30
    + 16532 * s ^ 29
    - 101893 * s ^ 28
    + 483967 * s ^ 27
    - 1567403 * s ^ 26
    + 3321474 * s ^ 25
    - 4018174 * s ^ 24
    + 687376 * s ^ 23
    + 5790754 * s ^ 22
    - 7444429 * s ^ 21
    - 1358144 * s ^ 20
    + 19879407 * s ^ 19
    - 53896138 * s ^ 18
    + 102460225 * s ^ 17
    - 149592861 * s ^ 16
    + 180399165 * s ^ 15
    - 186024911 * s ^ 14
    + 166324827 * s ^ 13
    - 129344410 * s ^ 12
    + 87157841 * s ^ 11
    - 50391407 * s ^ 10
    + 24615087 * s ^ 9
    - 9941788 * s ^ 8
    + 3213681 * s ^ 7
    - 781333 * s ^ 6
    + 122382 * s ^ 5
    - 5635 * s ^ 4
    - 2125 * s ^ 3
    + 403 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient8 (s : ℚ) : ℚ :=
  4 * s ^ 33
    - 19 * s ^ 32
    - 568 * s ^ 31
    + 8813 * s ^ 30
    - 60541 * s ^ 29
    + 237281 * s ^ 28
    - 480229 * s ^ 27
    - 122923 * s ^ 26
    + 3880242 * s ^ 25
    - 11725363 * s ^ 24
    + 15163040 * s ^ 23
    + 7614629 * s ^ 22
    - 75450074 * s ^ 21
    + 187744139 * s ^ 20
    - 348565380 * s ^ 19
    + 569989786 * s ^ 18
    - 810204737 * s ^ 17
    + 995715284 * s ^ 16
    - 1078408374 * s ^ 15
    + 1036275986 * s ^ 14
    - 882175116 * s ^ 13
    + 661243125 * s ^ 12
    - 432051926 * s ^ 11
    + 242528842 * s ^ 10
    - 114656812 * s ^ 9
    + 44362770 * s ^ 8
    - 13367756 * s ^ 7
    + 2787273 * s ^ 6
    - 238278 * s ^ 5
    - 66793 * s ^ 4
    + 27174 * s ^ 3
    - 3497 * s ^ 2
    - 3 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient9 (s : ℚ) : ℚ :=
  -s ^ 34
    + 31 * s ^ 33
    - 424 * s ^ 32
    + 3061 * s ^ 31
    - 10554 * s ^ 30
    - 8749 * s ^ 29
    + 278056 * s ^ 28
    - 1399011 * s ^ 27
    + 3351983 * s ^ 26
    - 519214 * s ^ 25
    - 27158933 * s ^ 24
    + 115664753 * s ^ 23
    - 297290194 * s ^ 22
    + 582860398 * s ^ 21
    - 997355961 * s ^ 20
    + 1605076768 * s ^ 19
    - 2384158955 * s ^ 18
    + 3139110192 * s ^ 17
    - 3672186542 * s ^ 16
    + 3863197151 * s ^ 15
    - 3643174651 * s ^ 14
    + 3054946037 * s ^ 13
    - 2254212221 * s ^ 12
    + 1443839109 * s ^ 11
    - 787877542 * s ^ 10
    + 356553392 * s ^ 9
    - 127836829 * s ^ 8
    + 32640975 * s ^ 7
    - 3680988 * s ^ 6
    - 1255330 * s ^ 5
    + 771334 * s ^ 4
    - 186902 * s ^ 3
    + 19495 * s ^ 2
    + 287 * s
    - 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient10 (s : ℚ) : ℚ :=
  13 * s ^ 33
    - 349 * s ^ 32
    + 4121 * s ^ 31
    - 26344 * s ^ 30
    + 78348 * s ^ 29
    + 158073 * s ^ 28
    - 2972466 * s ^ 27
    + 17039855 * s ^ 26
    - 63252323 * s ^ 25
    + 174144158 * s ^ 24
    - 383200801 * s ^ 23
    + 730834192 * s ^ 22
    - 1323288038 * s ^ 21
    + 2363232037 * s ^ 20
    - 3958797038 * s ^ 19
    + 5857840923 * s ^ 18
    - 7608111461 * s ^ 17
    + 8887119879 * s ^ 16
    - 9393634447 * s ^ 15
    + 8875406855 * s ^ 14
    - 7407428892 * s ^ 13
    + 5390302538 * s ^ 12
    - 3359775030 * s ^ 11
    + 1746045938 * s ^ 10
    - 721282021 * s ^ 9
    + 210595233 * s ^ 8
    - 23025631 * s ^ 7
    - 16712455 * s ^ 6
    + 12169804 * s ^ 5
    - 4230398 * s ^ 4
    + 839740 * s ^ 3
    - 70664 * s ^ 2
    - 3558 * s
    + 209

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient11 (s : ℚ) : ℚ :=
  12 * s ^ 33
    - 443 * s ^ 32
    + 7438 * s ^ 31
    - 76113 * s ^ 30
    + 533962 * s ^ 29
    - 2732325 * s ^ 28
    + 10589837 * s ^ 27
    - 32040314 * s ^ 26
    + 78965650 * s ^ 25
    - 172431836 * s ^ 24
    + 378572825 * s ^ 23
    - 886739600 * s ^ 22
    + 2033677623 * s ^ 21
    - 4089896714 * s ^ 20
    + 6909557742 * s ^ 19
    - 9997232376 * s ^ 18
    + 12971395540 * s ^ 17
    - 15435763714 * s ^ 16
    + 16557066152 * s ^ 15
    - 15657630194 * s ^ 14
    + 12885765020 * s ^ 13
    - 9073375654 * s ^ 12
    + 5308937303 * s ^ 11
    - 2434432353 * s ^ 10
    + 738458204 * s ^ 9
    - 11067483 * s ^ 8
    - 159598947 * s ^ 7
    + 119472667 * s ^ 6
    - 52743409 * s ^ 5
    + 15204581 * s ^ 4
    - 2615830 * s ^ 3
    + 149739 * s ^ 2
    + 24318 * s
    - 1308

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient12 (s : ℚ) : ℚ :=
  2 * s ^ 34
    - 66 * s ^ 33
    + 1005 * s ^ 32
    - 9232 * s ^ 31
    + 56203 * s ^ 30
    - 233972 * s ^ 29
    + 665409 * s ^ 28
    - 1372801 * s ^ 27
    + 3758583 * s ^ 26
    - 21848229 * s ^ 25
    + 118475680 * s ^ 24
    - 462837727 * s ^ 23
    + 1336937541 * s ^ 22
    - 2982619210 * s ^ 21
    + 5377581163 * s ^ 20
    - 8330562798 * s ^ 19
    + 11889748180 * s ^ 18
    - 16084334480 * s ^ 17
    + 19888298162 * s ^ 16
    - 21451807306 * s ^ 15
    + 19814792570 * s ^ 14
    - 15489043354 * s ^ 13
    + 9886543134 * s ^ 12
    - 4692708941 * s ^ 11
    + 1097062942 * s ^ 10
    + 644573367 * s ^ 9
    - 1028091029 * s ^ 8
    + 771038903 * s ^ 7
    - 401776292 * s ^ 6
    + 150977686 * s ^ 5
    - 38737914 * s ^ 4
    + 5618570 * s ^ 3
    - 39361 * s ^ 2
    - 112146 * s
    + 5758

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient13 (s : ℚ) : ℚ :=
  -7 * s ^ 33
    + 204 * s ^ 32
    - 2680 * s ^ 31
    + 19977 * s ^ 30
    - 80336 * s ^ 29
    + 12760 * s ^ 28
    + 2149985 * s ^ 27
    - 16416110 * s ^ 26
    + 75458766 * s ^ 25
    - 251083501 * s ^ 24
    + 643188412 * s ^ 23
    - 1319678898 * s ^ 22
    + 2293096605 * s ^ 21
    - 3718589249 * s ^ 20
    + 6182727976 * s ^ 19
    - 10302176641 * s ^ 18
    + 15398240230 * s ^ 17
    - 19123720396 * s ^ 16
    + 19403448766 * s ^ 15
    - 16078994666 * s ^ 14
    + 10317103846 * s ^ 13
    - 3899719023 * s ^ 12
    - 1234179123 * s ^ 11
    + 3941529077 * s ^ 10
    - 4325240486 * s ^ 9
    + 3325927572 * s ^ 8
    - 1973537730 * s ^ 7
    + 908007043 * s ^ 6
    - 310191851 * s ^ 5
    + 70679760 * s ^ 4
    - 7338438 * s ^ 3
    - 1001722 * s ^ 2
    + 378769 * s
    - 18891

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient14 (s : ℚ) : ℚ :=
  -3 * s ^ 33
    + 117 * s ^ 32
    - 2114 * s ^ 31
    + 23637 * s ^ 30
    - 183378 * s ^ 29
    + 1044825 * s ^ 28
    - 4495528 * s ^ 27
    + 14725512 * s ^ 26
    - 36397605 * s ^ 25
    + 66609488 * s ^ 24
    - 93937849 * s ^ 23
    + 159357756 * s ^ 22
    - 529066063 * s ^ 21
    + 1822420617 * s ^ 20
    - 4628205509 * s ^ 19
    + 8486649666 * s ^ 18
    - 11448978032 * s ^ 17
    + 11529919062 * s ^ 16
    - 8472602720 * s ^ 15
    + 3280029266 * s ^ 14
    + 2899606874 * s ^ 13
    - 8465045974 * s ^ 12
    + 11658998256 * s ^ 11
    - 11801255519 * s ^ 10
    + 9582308133 * s ^ 9
    - 6391579725 * s ^ 8
    + 3475334881 * s ^ 7
    - 1485679171 * s ^ 6
    + 462725633 * s ^ 5
    - 86747510 * s ^ 4
    + 1063063 * s ^ 3
    + 4289657 * s ^ 2
    - 977479 * s
    + 47736

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient15 (s : ℚ) : ℚ :=
  7 * s ^ 32
    - 243 * s ^ 31
    + 4006 * s ^ 30
    - 41554 * s ^ 29
    + 302013 * s ^ 28
    - 1613157 * s ^ 27
    + 6400728 * s ^ 26
    - 18203411 * s ^ 25
    + 31041325 * s ^ 24
    + 7504261 * s ^ 23
    - 256249055 * s ^ 22
    + 976170059 * s ^ 21
    - 2290173708 * s ^ 20
    + 3721675895 * s ^ 19
    - 4087150477 * s ^ 18
    + 2369566095 * s ^ 17
    + 1240823374 * s ^ 16
    - 5841619735 * s ^ 15
    + 11022231185 * s ^ 14
    - 16291557304 * s ^ 13
    + 20059824004 * s ^ 12
    - 20760517627 * s ^ 11
    + 18250536109 * s ^ 10
    - 13671162789 * s ^ 9
    + 8630993142 * s ^ 8
    - 4453910703 * s ^ 7
    + 1769215072 * s ^ 6
    - 475299761 * s ^ 5
    + 49222467 * s ^ 4
    + 20947989 * s ^ 3
    - 10836672 * s ^ 2
    + 1973121 * s
    - 94656

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient16 (s : ℚ) : ℚ :=
  s ^ 32
    - 44 * s ^ 31
    + 902 * s ^ 30
    - 11604 * s ^ 29
    + 105754 * s ^ 28
    - 727326 * s ^ 27
    + 3910504 * s ^ 26
    - 16737659 * s ^ 25
    + 57306078 * s ^ 24
    - 155432904 * s ^ 23
    + 322848712 * s ^ 22
    - 464548394 * s ^ 21
    + 275481591 * s ^ 20
    + 689805584 * s ^ 19
    - 2638792060 * s ^ 18
    + 5243464696 * s ^ 17
    - 8115025814 * s ^ 16
    + 11566778198 * s ^ 15
    - 16024210317 * s ^ 14
    + 20535632300 * s ^ 13
    - 23091664841 * s ^ 12
    + 22502427260 * s ^ 11
    - 19042351652 * s ^ 10
    + 13872693136 * s ^ 9
    - 8474325178 * s ^ 8
    + 4123967169 * s ^ 7
    - 1440971403 * s ^ 6
    + 253948552 * s ^ 5
    + 58172972 * s ^ 4
    - 58404424 * s ^ 3
    + 19664461 * s ^ 2
    - 3152858 * s
    + 148608

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient17 (s : ℚ) : ℚ :=
  -s ^ 31
    + 39 * s ^ 30
    - 742 * s ^ 29
    + 9197 * s ^ 28
    - 83332 * s ^ 27
    + 585033 * s ^ 26
    - 3284596 * s ^ 25
    + 15000446 * s ^ 24
    - 56176523 * s ^ 23
    + 172855397 * s ^ 22
    - 436005773 * s ^ 21
    + 898695951 * s ^ 20
    - 1522886261 * s ^ 19
    + 2213274018 * s ^ 18
    - 3104462252 * s ^ 17
    + 4814770467 * s ^ 16
    - 7966456787 * s ^ 15
    + 12134096836 * s ^ 14
    - 15753608198 * s ^ 13
    + 17428901690 * s ^ 12
    - 16785362066 * s ^ 11
    + 14116984407 * s ^ 10
    - 10119975922 * s ^ 9
    + 5886835952 * s ^ 8
    - 2522000435 * s ^ 7
    + 580651959 * s ^ 6
    + 130533049 * s ^ 5
    - 196096142 * s ^ 4
    + 96474357 * s ^ 3
    - 27086892 * s ^ 2
    + 4002030 * s
    - 184906

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient18 (s : ℚ) : ℚ :=
  13 * s ^ 28
    - 460 * s ^ 27
    + 7732 * s ^ 26
    - 81947 * s ^ 25
    + 611855 * s ^ 24
    - 3396271 * s ^ 23
    + 14343505 * s ^ 22
    - 45955036 * s ^ 21
    + 107031312 * s ^ 20
    - 153262608 * s ^ 19
    - 2622984 * s ^ 18
    + 712068757 * s ^ 17
    - 2260447505 * s ^ 16
    + 4470148673 * s ^ 15
    - 6665639540 * s ^ 14
    + 8218466683 * s ^ 13
    - 8917775359 * s ^ 12
    + 8662462164 * s ^ 11
    - 7287967651 * s ^ 10
    + 4984766768 * s ^ 9
    - 2479124626 * s ^ 8
    + 589777719 * s ^ 7
    + 317991705 * s ^ 6
    - 458869324 * s ^ 5
    + 285834157 * s ^ 4
    - 113338201 * s ^ 3
    + 28808319 * s ^ 2
    - 4018917 * s
    + 181067

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient19 (s : ℚ) : ℚ :=
  s ^ 28
    - 42 * s ^ 27
    + 840 * s ^ 26
    - 10697 * s ^ 25
    + 97635 * s ^ 24
    - 679866 * s ^ 23
    + 3741507 * s ^ 22
    - 16582596 * s ^ 21
    + 59654354 * s ^ 20
    - 174322083 * s ^ 19
    + 412744147 * s ^ 18
    - 791088020 * s ^ 17
    + 1239332525 * s ^ 16
    - 1646385752 * s ^ 15
    + 2003270335 * s ^ 14
    - 2410124713 * s ^ 13
    + 2815647929 * s ^ 12
    - 2875325383 * s ^ 11
    + 2284549196 * s ^ 10
    - 1176388707 * s ^ 9
    + 48530060 * s ^ 8
    + 637142196 * s ^ 7
    - 764170800 * s ^ 6
    + 548117187 * s ^ 5
    - 275914810 * s ^ 4
    + 98765062 * s ^ 3
    - 23615993 * s ^ 2
    + 3153702 * s
    - 137214

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient20 (s : ℚ) : ℚ :=
  -5 * s ^ 25
    + 205 * s ^ 24
    - 3905 * s ^ 23
    + 45711 * s ^ 22
    - 366108 * s ^ 21
    + 2112478 * s ^ 20
    - 8993110 * s ^ 19
    + 28341640 * s ^ 18
    - 64684555 * s ^ 17
    + 98680130 * s ^ 16
    - 68738620 * s ^ 15
    - 92702246 * s ^ 14
    + 356228102 * s ^ 13
    - 544031821 * s ^ 12
    + 456310884 * s ^ 11
    - 68994505 * s ^ 10
    - 430144118 * s ^ 9
    + 788405508 * s ^ 8
    - 859405344 * s ^ 7
    + 680725504 * s ^ 6
    - 410214563 * s ^ 5
    + 188406553 * s ^ 4
    - 63841951 * s ^ 3
    + 14675508 * s ^ 2
    - 1889311 * s
    + 77939

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient21 (s : ℚ) : ℚ :=
  3 * s ^ 24
    - 121 * s ^ 23
    + 2275 * s ^ 22
    - 26404 * s ^ 21
    + 211228 * s ^ 20
    - 1231933 * s ^ 19
    + 5402136 * s ^ 18
    - 18091275 * s ^ 17
    + 46430703 * s ^ 16
    - 90321323 * s ^ 15
    + 127966786 * s ^ 14
    - 114440575 * s ^ 13
    + 10509136 * s ^ 12
    + 177816760 * s ^ 11
    - 392058604 * s ^ 10
    + 552621889 * s ^ 9
    - 598680418 * s ^ 8
    + 519898944 * s ^ 7
    - 364421259 * s ^ 6
    + 204827099 * s ^ 5
    - 90331646 * s ^ 4
    + 29796881 * s ^ 3
    - 6678828 * s ^ 2
    + 829746 * s
    - 31200

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient22 (s : ℚ) : ℚ :=
  -s ^ 23
    + 39 * s ^ 22
    - 713 * s ^ 21
    + 8105 * s ^ 20
    - 64113 * s ^ 19
    + 374515 * s ^ 18
    - 1674841 * s ^ 17
    + 5875377 * s ^ 16
    - 16476950 * s ^ 15
    + 37611209 * s ^ 14
    - 71342248 * s ^ 13
    + 115276156 * s ^ 12
    - 162669873 * s ^ 11
    + 203432309 * s ^ 10
    - 224579232 * s ^ 9
    + 214842042 * s ^ 8
    - 174417526 * s ^ 7
    + 118133582 * s ^ 6
    - 65511430 * s ^ 5
    + 28797556 * s ^ 4
    - 9462065 * s ^ 3
    + 2088548 * s ^ 2
    - 248064 * s
    + 7618

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient23 (s : ℚ) : ℚ :=
  -s ^ 20
    + 36 * s ^ 19
    - 605 * s ^ 18
    + 6301 * s ^ 17
    - 45515 * s ^ 16
    + 241781 * s ^ 15
    - 977430 * s ^ 14
    + 3071787 * s ^ 13
    - 7609816 * s ^ 12
    + 15008664 * s ^ 11
    - 23768281 * s ^ 10
    + 30502779 * s ^ 9
    - 32062443 * s ^ 8
    + 27869877 * s ^ 7
    - 20057484 * s ^ 6
    + 11756613 * s ^ 5
    - 5394413 * s ^ 4
    + 1810470 * s ^ 3
    - 394656 * s ^ 2
    + 42908 * s
    - 572

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient24 (s : ℚ) : ℚ :=
  s ^ 16
    - 30 * s ^ 15
    + 412 * s ^ 14
    - 3433 * s ^ 13
    + 19391 * s ^ 12
    - 78561 * s ^ 11
    + 235568 * s ^ 10
    - 531736 * s ^ 9
    + 910086 * s ^ 8
    - 1180586 * s ^ 7
    + 1152193 * s ^ 6
    - 832868 * s ^ 5
    + 432949 * s ^ 4
    - 152332 * s ^ 3
    + 31402 * s ^ 2
    - 2240 * s
    - 216

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient25 (s : ℚ) : ℚ :=
  s ^ 8
    - 16 * s ^ 7
    + 107 * s ^ 6
    - 388 * s ^ 5
    + 828 * s ^ 4
    - 1056 * s ^ 3
    + 780 * s ^ 2
    - 304 * s
    + 48

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t3Step2 (r s : ℚ) : ℚ :=
  t3Step2Coefficient0 s +
    t3Step2Coefficient1 s * r +
    t3Step2Coefficient2 s * r ^ 2 +
    t3Step2Coefficient3 s * r ^ 3 +
    t3Step2Coefficient4 s * r ^ 4 +
    t3Step2Coefficient5 s * r ^ 5 +
    t3Step2Coefficient6 s * r ^ 6 +
    t3Step2Coefficient7 s * r ^ 7 +
    t3Step2Coefficient8 s * r ^ 8 +
    t3Step2Coefficient9 s * r ^ 9 +
    t3Step2Coefficient10 s * r ^ 10 +
    t3Step2Coefficient11 s * r ^ 11 +
    t3Step2Coefficient12 s * r ^ 12 +
    t3Step2Coefficient13 s * r ^ 13 +
    t3Step2Coefficient14 s * r ^ 14 +
    t3Step2Coefficient15 s * r ^ 15 +
    t3Step2Coefficient16 s * r ^ 16 +
    t3Step2Coefficient17 s * r ^ 17 +
    t3Step2Coefficient18 s * r ^ 18 +
    t3Step2Coefficient19 s * r ^ 19 +
    t3Step2Coefficient20 s * r ^ 20 +
    t3Step2Coefficient21 s * r ^ 21 +
    t3Step2Coefficient22 s * r ^ 22 +
    t3Step2Coefficient23 s * r ^ 23 +
    t3Step2Coefficient24 s * r ^ 24 +
    t3Step2Coefficient25 s * r ^ 25

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_0 (s : ℚ) :
    t3Step2Coefficient0 s =
      t3Step1Coefficient0 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient0,
    t3Step1Coefficient0,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_1 (s : ℚ) :
    t3Step2Coefficient1 s =
      t3Step1Coefficient0 s *
          differenceCoefficient1 s +
        t3Step1Coefficient1 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient1,
    t3Step1Coefficient0,
    differenceCoefficient1,
    t3Step1Coefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_2 (s : ℚ) :
    t3Step2Coefficient2 s =
      t3Step1Coefficient0 s *
          differenceCoefficient2 s +
        t3Step1Coefficient1 s *
          differenceCoefficient1 s +
        t3Step1Coefficient2 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient2,
    t3Step1Coefficient0,
    differenceCoefficient2,
    t3Step1Coefficient1,
    differenceCoefficient1,
    t3Step1Coefficient2,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_3 (s : ℚ) :
    t3Step2Coefficient3 s =
      t3Step1Coefficient0 s *
          differenceCoefficient3 s +
        t3Step1Coefficient1 s *
          differenceCoefficient2 s +
        t3Step1Coefficient2 s *
          differenceCoefficient1 s +
        t3Step1Coefficient3 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient3,
    t3Step1Coefficient0,
    differenceCoefficient3,
    t3Step1Coefficient1,
    differenceCoefficient2,
    t3Step1Coefficient2,
    differenceCoefficient1,
    t3Step1Coefficient3,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_4 (s : ℚ) :
    t3Step2Coefficient4 s =
      t3Step1Coefficient0 s *
          differenceCoefficient4 s +
        t3Step1Coefficient1 s *
          differenceCoefficient3 s +
        t3Step1Coefficient2 s *
          differenceCoefficient2 s +
        t3Step1Coefficient3 s *
          differenceCoefficient1 s +
        t3Step1Coefficient4 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient4,
    t3Step1Coefficient0,
    differenceCoefficient4,
    t3Step1Coefficient1,
    differenceCoefficient3,
    t3Step1Coefficient2,
    differenceCoefficient2,
    t3Step1Coefficient3,
    differenceCoefficient1,
    t3Step1Coefficient4,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_5 (s : ℚ) :
    t3Step2Coefficient5 s =
      t3Step1Coefficient0 s *
          differenceCoefficient5 s +
        t3Step1Coefficient1 s *
          differenceCoefficient4 s +
        t3Step1Coefficient2 s *
          differenceCoefficient3 s +
        t3Step1Coefficient3 s *
          differenceCoefficient2 s +
        t3Step1Coefficient4 s *
          differenceCoefficient1 s +
        t3Step1Coefficient5 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient5,
    t3Step1Coefficient0,
    differenceCoefficient5,
    t3Step1Coefficient1,
    differenceCoefficient4,
    t3Step1Coefficient2,
    differenceCoefficient3,
    t3Step1Coefficient3,
    differenceCoefficient2,
    t3Step1Coefficient4,
    differenceCoefficient1,
    t3Step1Coefficient5,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_6 (s : ℚ) :
    t3Step2Coefficient6 s =
      t3Step1Coefficient0 s *
          differenceCoefficient6 s +
        t3Step1Coefficient1 s *
          differenceCoefficient5 s +
        t3Step1Coefficient2 s *
          differenceCoefficient4 s +
        t3Step1Coefficient3 s *
          differenceCoefficient3 s +
        t3Step1Coefficient4 s *
          differenceCoefficient2 s +
        t3Step1Coefficient5 s *
          differenceCoefficient1 s +
        t3Step1Coefficient6 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient6,
    t3Step1Coefficient0,
    differenceCoefficient6,
    t3Step1Coefficient1,
    differenceCoefficient5,
    t3Step1Coefficient2,
    differenceCoefficient4,
    t3Step1Coefficient3,
    differenceCoefficient3,
    t3Step1Coefficient4,
    differenceCoefficient2,
    t3Step1Coefficient5,
    differenceCoefficient1,
    t3Step1Coefficient6,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_7 (s : ℚ) :
    t3Step2Coefficient7 s =
      t3Step1Coefficient0 s *
          differenceCoefficient7 s +
        t3Step1Coefficient1 s *
          differenceCoefficient6 s +
        t3Step1Coefficient2 s *
          differenceCoefficient5 s +
        t3Step1Coefficient3 s *
          differenceCoefficient4 s +
        t3Step1Coefficient4 s *
          differenceCoefficient3 s +
        t3Step1Coefficient5 s *
          differenceCoefficient2 s +
        t3Step1Coefficient6 s *
          differenceCoefficient1 s +
        t3Step1Coefficient7 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient7,
    t3Step1Coefficient0,
    differenceCoefficient7,
    t3Step1Coefficient1,
    differenceCoefficient6,
    t3Step1Coefficient2,
    differenceCoefficient5,
    t3Step1Coefficient3,
    differenceCoefficient4,
    t3Step1Coefficient4,
    differenceCoefficient3,
    t3Step1Coefficient5,
    differenceCoefficient2,
    t3Step1Coefficient6,
    differenceCoefficient1,
    t3Step1Coefficient7,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_8 (s : ℚ) :
    t3Step2Coefficient8 s =
      t3Step1Coefficient0 s *
          differenceCoefficient8 s +
        t3Step1Coefficient1 s *
          differenceCoefficient7 s +
        t3Step1Coefficient2 s *
          differenceCoefficient6 s +
        t3Step1Coefficient3 s *
          differenceCoefficient5 s +
        t3Step1Coefficient4 s *
          differenceCoefficient4 s +
        t3Step1Coefficient5 s *
          differenceCoefficient3 s +
        t3Step1Coefficient6 s *
          differenceCoefficient2 s +
        t3Step1Coefficient7 s *
          differenceCoefficient1 s +
        t3Step1Coefficient8 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient8,
    t3Step1Coefficient0,
    differenceCoefficient8,
    t3Step1Coefficient1,
    differenceCoefficient7,
    t3Step1Coefficient2,
    differenceCoefficient6,
    t3Step1Coefficient3,
    differenceCoefficient5,
    t3Step1Coefficient4,
    differenceCoefficient4,
    t3Step1Coefficient5,
    differenceCoefficient3,
    t3Step1Coefficient6,
    differenceCoefficient2,
    t3Step1Coefficient7,
    differenceCoefficient1,
    t3Step1Coefficient8,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_9 (s : ℚ) :
    t3Step2Coefficient9 s =
      t3Step1Coefficient0 s *
          differenceCoefficient9 s +
        t3Step1Coefficient1 s *
          differenceCoefficient8 s +
        t3Step1Coefficient2 s *
          differenceCoefficient7 s +
        t3Step1Coefficient3 s *
          differenceCoefficient6 s +
        t3Step1Coefficient4 s *
          differenceCoefficient5 s +
        t3Step1Coefficient5 s *
          differenceCoefficient4 s +
        t3Step1Coefficient6 s *
          differenceCoefficient3 s +
        t3Step1Coefficient7 s *
          differenceCoefficient2 s +
        t3Step1Coefficient8 s *
          differenceCoefficient1 s +
        t3Step1Coefficient9 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient9,
    t3Step1Coefficient0,
    differenceCoefficient9,
    t3Step1Coefficient1,
    differenceCoefficient8,
    t3Step1Coefficient2,
    differenceCoefficient7,
    t3Step1Coefficient3,
    differenceCoefficient6,
    t3Step1Coefficient4,
    differenceCoefficient5,
    t3Step1Coefficient5,
    differenceCoefficient4,
    t3Step1Coefficient6,
    differenceCoefficient3,
    t3Step1Coefficient7,
    differenceCoefficient2,
    t3Step1Coefficient8,
    differenceCoefficient1,
    t3Step1Coefficient9,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_10 (s : ℚ) :
    t3Step2Coefficient10 s =
      t3Step1Coefficient0 s *
          differenceCoefficient10 s +
        t3Step1Coefficient1 s *
          differenceCoefficient9 s +
        t3Step1Coefficient2 s *
          differenceCoefficient8 s +
        t3Step1Coefficient3 s *
          differenceCoefficient7 s +
        t3Step1Coefficient4 s *
          differenceCoefficient6 s +
        t3Step1Coefficient5 s *
          differenceCoefficient5 s +
        t3Step1Coefficient6 s *
          differenceCoefficient4 s +
        t3Step1Coefficient7 s *
          differenceCoefficient3 s +
        t3Step1Coefficient8 s *
          differenceCoefficient2 s +
        t3Step1Coefficient9 s *
          differenceCoefficient1 s +
        t3Step1Coefficient10 s *
          differenceCoefficient0 s := by
  simp only [t3Step2Coefficient10,
    t3Step1Coefficient0,
    differenceCoefficient10,
    t3Step1Coefficient1,
    differenceCoefficient9,
    t3Step1Coefficient2,
    differenceCoefficient8,
    t3Step1Coefficient3,
    differenceCoefficient7,
    t3Step1Coefficient4,
    differenceCoefficient6,
    t3Step1Coefficient5,
    differenceCoefficient5,
    t3Step1Coefficient6,
    differenceCoefficient4,
    t3Step1Coefficient7,
    differenceCoefficient3,
    t3Step1Coefficient8,
    differenceCoefficient2,
    t3Step1Coefficient9,
    differenceCoefficient1,
    t3Step1Coefficient10,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_11 (s : ℚ) :
    t3Step2Coefficient11 s =
      t3Step1Coefficient0 s *
          differenceCoefficient11 s +
        t3Step1Coefficient1 s *
          differenceCoefficient10 s +
        t3Step1Coefficient2 s *
          differenceCoefficient9 s +
        t3Step1Coefficient3 s *
          differenceCoefficient8 s +
        t3Step1Coefficient4 s *
          differenceCoefficient7 s +
        t3Step1Coefficient5 s *
          differenceCoefficient6 s +
        t3Step1Coefficient6 s *
          differenceCoefficient5 s +
        t3Step1Coefficient7 s *
          differenceCoefficient4 s +
        t3Step1Coefficient8 s *
          differenceCoefficient3 s +
        t3Step1Coefficient9 s *
          differenceCoefficient2 s +
        t3Step1Coefficient10 s *
          differenceCoefficient1 s := by
  simp only [t3Step2Coefficient11,
    t3Step1Coefficient0,
    differenceCoefficient11,
    t3Step1Coefficient1,
    differenceCoefficient10,
    t3Step1Coefficient2,
    differenceCoefficient9,
    t3Step1Coefficient3,
    differenceCoefficient8,
    t3Step1Coefficient4,
    differenceCoefficient7,
    t3Step1Coefficient5,
    differenceCoefficient6,
    t3Step1Coefficient6,
    differenceCoefficient5,
    t3Step1Coefficient7,
    differenceCoefficient4,
    t3Step1Coefficient8,
    differenceCoefficient3,
    t3Step1Coefficient9,
    differenceCoefficient2,
    t3Step1Coefficient10,
    differenceCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_12 (s : ℚ) :
    t3Step2Coefficient12 s =
      t3Step1Coefficient0 s *
          differenceCoefficient12 s +
        t3Step1Coefficient1 s *
          differenceCoefficient11 s +
        t3Step1Coefficient2 s *
          differenceCoefficient10 s +
        t3Step1Coefficient3 s *
          differenceCoefficient9 s +
        t3Step1Coefficient4 s *
          differenceCoefficient8 s +
        t3Step1Coefficient5 s *
          differenceCoefficient7 s +
        t3Step1Coefficient6 s *
          differenceCoefficient6 s +
        t3Step1Coefficient7 s *
          differenceCoefficient5 s +
        t3Step1Coefficient8 s *
          differenceCoefficient4 s +
        t3Step1Coefficient9 s *
          differenceCoefficient3 s +
        t3Step1Coefficient10 s *
          differenceCoefficient2 s := by
  simp only [t3Step2Coefficient12,
    t3Step1Coefficient0,
    differenceCoefficient12,
    t3Step1Coefficient1,
    differenceCoefficient11,
    t3Step1Coefficient2,
    differenceCoefficient10,
    t3Step1Coefficient3,
    differenceCoefficient9,
    t3Step1Coefficient4,
    differenceCoefficient8,
    t3Step1Coefficient5,
    differenceCoefficient7,
    t3Step1Coefficient6,
    differenceCoefficient6,
    t3Step1Coefficient7,
    differenceCoefficient5,
    t3Step1Coefficient8,
    differenceCoefficient4,
    t3Step1Coefficient9,
    differenceCoefficient3,
    t3Step1Coefficient10,
    differenceCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_13 (s : ℚ) :
    t3Step2Coefficient13 s =
      t3Step1Coefficient0 s *
          differenceCoefficient13 s +
        t3Step1Coefficient1 s *
          differenceCoefficient12 s +
        t3Step1Coefficient2 s *
          differenceCoefficient11 s +
        t3Step1Coefficient3 s *
          differenceCoefficient10 s +
        t3Step1Coefficient4 s *
          differenceCoefficient9 s +
        t3Step1Coefficient5 s *
          differenceCoefficient8 s +
        t3Step1Coefficient6 s *
          differenceCoefficient7 s +
        t3Step1Coefficient7 s *
          differenceCoefficient6 s +
        t3Step1Coefficient8 s *
          differenceCoefficient5 s +
        t3Step1Coefficient9 s *
          differenceCoefficient4 s +
        t3Step1Coefficient10 s *
          differenceCoefficient3 s := by
  simp only [t3Step2Coefficient13,
    t3Step1Coefficient0,
    differenceCoefficient13,
    t3Step1Coefficient1,
    differenceCoefficient12,
    t3Step1Coefficient2,
    differenceCoefficient11,
    t3Step1Coefficient3,
    differenceCoefficient10,
    t3Step1Coefficient4,
    differenceCoefficient9,
    t3Step1Coefficient5,
    differenceCoefficient8,
    t3Step1Coefficient6,
    differenceCoefficient7,
    t3Step1Coefficient7,
    differenceCoefficient6,
    t3Step1Coefficient8,
    differenceCoefficient5,
    t3Step1Coefficient9,
    differenceCoefficient4,
    t3Step1Coefficient10,
    differenceCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_14 (s : ℚ) :
    t3Step2Coefficient14 s =
      t3Step1Coefficient0 s *
          differenceCoefficient14 s +
        t3Step1Coefficient1 s *
          differenceCoefficient13 s +
        t3Step1Coefficient2 s *
          differenceCoefficient12 s +
        t3Step1Coefficient3 s *
          differenceCoefficient11 s +
        t3Step1Coefficient4 s *
          differenceCoefficient10 s +
        t3Step1Coefficient5 s *
          differenceCoefficient9 s +
        t3Step1Coefficient6 s *
          differenceCoefficient8 s +
        t3Step1Coefficient7 s *
          differenceCoefficient7 s +
        t3Step1Coefficient8 s *
          differenceCoefficient6 s +
        t3Step1Coefficient9 s *
          differenceCoefficient5 s +
        t3Step1Coefficient10 s *
          differenceCoefficient4 s := by
  simp only [t3Step2Coefficient14,
    t3Step1Coefficient0,
    differenceCoefficient14,
    t3Step1Coefficient1,
    differenceCoefficient13,
    t3Step1Coefficient2,
    differenceCoefficient12,
    t3Step1Coefficient3,
    differenceCoefficient11,
    t3Step1Coefficient4,
    differenceCoefficient10,
    t3Step1Coefficient5,
    differenceCoefficient9,
    t3Step1Coefficient6,
    differenceCoefficient8,
    t3Step1Coefficient7,
    differenceCoefficient7,
    t3Step1Coefficient8,
    differenceCoefficient6,
    t3Step1Coefficient9,
    differenceCoefficient5,
    t3Step1Coefficient10,
    differenceCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_15 (s : ℚ) :
    t3Step2Coefficient15 s =
      t3Step1Coefficient0 s *
          differenceCoefficient15 s +
        t3Step1Coefficient1 s *
          differenceCoefficient14 s +
        t3Step1Coefficient2 s *
          differenceCoefficient13 s +
        t3Step1Coefficient3 s *
          differenceCoefficient12 s +
        t3Step1Coefficient4 s *
          differenceCoefficient11 s +
        t3Step1Coefficient5 s *
          differenceCoefficient10 s +
        t3Step1Coefficient6 s *
          differenceCoefficient9 s +
        t3Step1Coefficient7 s *
          differenceCoefficient8 s +
        t3Step1Coefficient8 s *
          differenceCoefficient7 s +
        t3Step1Coefficient9 s *
          differenceCoefficient6 s +
        t3Step1Coefficient10 s *
          differenceCoefficient5 s := by
  simp only [t3Step2Coefficient15,
    t3Step1Coefficient0,
    differenceCoefficient15,
    t3Step1Coefficient1,
    differenceCoefficient14,
    t3Step1Coefficient2,
    differenceCoefficient13,
    t3Step1Coefficient3,
    differenceCoefficient12,
    t3Step1Coefficient4,
    differenceCoefficient11,
    t3Step1Coefficient5,
    differenceCoefficient10,
    t3Step1Coefficient6,
    differenceCoefficient9,
    t3Step1Coefficient7,
    differenceCoefficient8,
    t3Step1Coefficient8,
    differenceCoefficient7,
    t3Step1Coefficient9,
    differenceCoefficient6,
    t3Step1Coefficient10,
    differenceCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_16 (s : ℚ) :
    t3Step2Coefficient16 s =
      t3Step1Coefficient1 s *
          differenceCoefficient15 s +
        t3Step1Coefficient2 s *
          differenceCoefficient14 s +
        t3Step1Coefficient3 s *
          differenceCoefficient13 s +
        t3Step1Coefficient4 s *
          differenceCoefficient12 s +
        t3Step1Coefficient5 s *
          differenceCoefficient11 s +
        t3Step1Coefficient6 s *
          differenceCoefficient10 s +
        t3Step1Coefficient7 s *
          differenceCoefficient9 s +
        t3Step1Coefficient8 s *
          differenceCoefficient8 s +
        t3Step1Coefficient9 s *
          differenceCoefficient7 s +
        t3Step1Coefficient10 s *
          differenceCoefficient6 s := by
  simp only [t3Step2Coefficient16,
    t3Step1Coefficient1,
    differenceCoefficient15,
    t3Step1Coefficient2,
    differenceCoefficient14,
    t3Step1Coefficient3,
    differenceCoefficient13,
    t3Step1Coefficient4,
    differenceCoefficient12,
    t3Step1Coefficient5,
    differenceCoefficient11,
    t3Step1Coefficient6,
    differenceCoefficient10,
    t3Step1Coefficient7,
    differenceCoefficient9,
    t3Step1Coefficient8,
    differenceCoefficient8,
    t3Step1Coefficient9,
    differenceCoefficient7,
    t3Step1Coefficient10,
    differenceCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_17 (s : ℚ) :
    t3Step2Coefficient17 s =
      t3Step1Coefficient2 s *
          differenceCoefficient15 s +
        t3Step1Coefficient3 s *
          differenceCoefficient14 s +
        t3Step1Coefficient4 s *
          differenceCoefficient13 s +
        t3Step1Coefficient5 s *
          differenceCoefficient12 s +
        t3Step1Coefficient6 s *
          differenceCoefficient11 s +
        t3Step1Coefficient7 s *
          differenceCoefficient10 s +
        t3Step1Coefficient8 s *
          differenceCoefficient9 s +
        t3Step1Coefficient9 s *
          differenceCoefficient8 s +
        t3Step1Coefficient10 s *
          differenceCoefficient7 s := by
  simp only [t3Step2Coefficient17,
    t3Step1Coefficient2,
    differenceCoefficient15,
    t3Step1Coefficient3,
    differenceCoefficient14,
    t3Step1Coefficient4,
    differenceCoefficient13,
    t3Step1Coefficient5,
    differenceCoefficient12,
    t3Step1Coefficient6,
    differenceCoefficient11,
    t3Step1Coefficient7,
    differenceCoefficient10,
    t3Step1Coefficient8,
    differenceCoefficient9,
    t3Step1Coefficient9,
    differenceCoefficient8,
    t3Step1Coefficient10,
    differenceCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_18 (s : ℚ) :
    t3Step2Coefficient18 s =
      t3Step1Coefficient3 s *
          differenceCoefficient15 s +
        t3Step1Coefficient4 s *
          differenceCoefficient14 s +
        t3Step1Coefficient5 s *
          differenceCoefficient13 s +
        t3Step1Coefficient6 s *
          differenceCoefficient12 s +
        t3Step1Coefficient7 s *
          differenceCoefficient11 s +
        t3Step1Coefficient8 s *
          differenceCoefficient10 s +
        t3Step1Coefficient9 s *
          differenceCoefficient9 s +
        t3Step1Coefficient10 s *
          differenceCoefficient8 s := by
  simp only [t3Step2Coefficient18,
    t3Step1Coefficient3,
    differenceCoefficient15,
    t3Step1Coefficient4,
    differenceCoefficient14,
    t3Step1Coefficient5,
    differenceCoefficient13,
    t3Step1Coefficient6,
    differenceCoefficient12,
    t3Step1Coefficient7,
    differenceCoefficient11,
    t3Step1Coefficient8,
    differenceCoefficient10,
    t3Step1Coefficient9,
    differenceCoefficient9,
    t3Step1Coefficient10,
    differenceCoefficient8]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_19 (s : ℚ) :
    t3Step2Coefficient19 s =
      t3Step1Coefficient4 s *
          differenceCoefficient15 s +
        t3Step1Coefficient5 s *
          differenceCoefficient14 s +
        t3Step1Coefficient6 s *
          differenceCoefficient13 s +
        t3Step1Coefficient7 s *
          differenceCoefficient12 s +
        t3Step1Coefficient8 s *
          differenceCoefficient11 s +
        t3Step1Coefficient9 s *
          differenceCoefficient10 s +
        t3Step1Coefficient10 s *
          differenceCoefficient9 s := by
  simp only [t3Step2Coefficient19,
    t3Step1Coefficient4,
    differenceCoefficient15,
    t3Step1Coefficient5,
    differenceCoefficient14,
    t3Step1Coefficient6,
    differenceCoefficient13,
    t3Step1Coefficient7,
    differenceCoefficient12,
    t3Step1Coefficient8,
    differenceCoefficient11,
    t3Step1Coefficient9,
    differenceCoefficient10,
    t3Step1Coefficient10,
    differenceCoefficient9]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_20 (s : ℚ) :
    t3Step2Coefficient20 s =
      t3Step1Coefficient5 s *
          differenceCoefficient15 s +
        t3Step1Coefficient6 s *
          differenceCoefficient14 s +
        t3Step1Coefficient7 s *
          differenceCoefficient13 s +
        t3Step1Coefficient8 s *
          differenceCoefficient12 s +
        t3Step1Coefficient9 s *
          differenceCoefficient11 s +
        t3Step1Coefficient10 s *
          differenceCoefficient10 s := by
  simp only [t3Step2Coefficient20,
    t3Step1Coefficient5,
    differenceCoefficient15,
    t3Step1Coefficient6,
    differenceCoefficient14,
    t3Step1Coefficient7,
    differenceCoefficient13,
    t3Step1Coefficient8,
    differenceCoefficient12,
    t3Step1Coefficient9,
    differenceCoefficient11,
    t3Step1Coefficient10,
    differenceCoefficient10]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_21 (s : ℚ) :
    t3Step2Coefficient21 s =
      t3Step1Coefficient6 s *
          differenceCoefficient15 s +
        t3Step1Coefficient7 s *
          differenceCoefficient14 s +
        t3Step1Coefficient8 s *
          differenceCoefficient13 s +
        t3Step1Coefficient9 s *
          differenceCoefficient12 s +
        t3Step1Coefficient10 s *
          differenceCoefficient11 s := by
  simp only [t3Step2Coefficient21,
    t3Step1Coefficient6,
    differenceCoefficient15,
    t3Step1Coefficient7,
    differenceCoefficient14,
    t3Step1Coefficient8,
    differenceCoefficient13,
    t3Step1Coefficient9,
    differenceCoefficient12,
    t3Step1Coefficient10,
    differenceCoefficient11]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_22 (s : ℚ) :
    t3Step2Coefficient22 s =
      t3Step1Coefficient7 s *
          differenceCoefficient15 s +
        t3Step1Coefficient8 s *
          differenceCoefficient14 s +
        t3Step1Coefficient9 s *
          differenceCoefficient13 s +
        t3Step1Coefficient10 s *
          differenceCoefficient12 s := by
  simp only [t3Step2Coefficient22,
    t3Step1Coefficient7,
    differenceCoefficient15,
    t3Step1Coefficient8,
    differenceCoefficient14,
    t3Step1Coefficient9,
    differenceCoefficient13,
    t3Step1Coefficient10,
    differenceCoefficient12]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_23 (s : ℚ) :
    t3Step2Coefficient23 s =
      t3Step1Coefficient8 s *
          differenceCoefficient15 s +
        t3Step1Coefficient9 s *
          differenceCoefficient14 s +
        t3Step1Coefficient10 s *
          differenceCoefficient13 s := by
  simp only [t3Step2Coefficient23,
    t3Step1Coefficient8,
    differenceCoefficient15,
    t3Step1Coefficient9,
    differenceCoefficient14,
    t3Step1Coefficient10,
    differenceCoefficient13]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_24 (s : ℚ) :
    t3Step2Coefficient24 s =
      t3Step1Coefficient9 s *
          differenceCoefficient15 s +
        t3Step1Coefficient10 s *
          differenceCoefficient14 s := by
  simp only [t3Step2Coefficient24,
    t3Step1Coefficient9,
    differenceCoefficient15,
    t3Step1Coefficient10,
    differenceCoefficient14]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem t3Step2Coefficient_product_certificate_25 (s : ℚ) :
    t3Step2Coefficient25 s =
      t3Step1Coefficient10 s *
          differenceCoefficient15 s := by
  simp only [t3Step2Coefficient25,
    t3Step1Coefficient10,
    differenceCoefficient15]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t3Step2_eq_t3Step1_mul_difference (r s : ℚ) :
    t3Step2 r s =
      t3Step1 r s * difference r s := by
  have h0 := t3Step2Coefficient_product_certificate_0 s
  have h1 := t3Step2Coefficient_product_certificate_1 s
  have h2 := t3Step2Coefficient_product_certificate_2 s
  have h3 := t3Step2Coefficient_product_certificate_3 s
  have h4 := t3Step2Coefficient_product_certificate_4 s
  have h5 := t3Step2Coefficient_product_certificate_5 s
  have h6 := t3Step2Coefficient_product_certificate_6 s
  have h7 := t3Step2Coefficient_product_certificate_7 s
  have h8 := t3Step2Coefficient_product_certificate_8 s
  have h9 := t3Step2Coefficient_product_certificate_9 s
  have h10 := t3Step2Coefficient_product_certificate_10 s
  have h11 := t3Step2Coefficient_product_certificate_11 s
  have h12 := t3Step2Coefficient_product_certificate_12 s
  have h13 := t3Step2Coefficient_product_certificate_13 s
  have h14 := t3Step2Coefficient_product_certificate_14 s
  have h15 := t3Step2Coefficient_product_certificate_15 s
  have h16 := t3Step2Coefficient_product_certificate_16 s
  have h17 := t3Step2Coefficient_product_certificate_17 s
  have h18 := t3Step2Coefficient_product_certificate_18 s
  have h19 := t3Step2Coefficient_product_certificate_19 s
  have h20 := t3Step2Coefficient_product_certificate_20 s
  have h21 := t3Step2Coefficient_product_certificate_21 s
  have h22 := t3Step2Coefficient_product_certificate_22 s
  have h23 := t3Step2Coefficient_product_certificate_23 s
  have h24 := t3Step2Coefficient_product_certificate_24 s
  have h25 := t3Step2Coefficient_product_certificate_25 s
  simp only [t3Step2, t3Step1, difference]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient0 (s : ℚ) : ℚ :=
  s ^ 34
    - s ^ 33
    + s ^ 32
    - s ^ 31

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 40
    + 4 * s ^ 39
    - 10 * s ^ 38
    + 20 * s ^ 37
    - 34 * s ^ 36
    + 54 * s ^ 35
    - 64 * s ^ 34
    + 2 * s ^ 33
    + 38 * s ^ 32
    - 74 * s ^ 31
    + 98 * s ^ 30
    - 48 * s ^ 29
    + 20 * s ^ 28
    - 6 * s ^ 27
    + s ^ 26

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient2 (s : ℚ) : ℚ :=
  -2 * s ^ 41
    + 2 * s ^ 40
    + 62 * s ^ 39
    - 265 * s ^ 38
    + 682 * s ^ 37
    - 1389 * s ^ 36
    + 2475 * s ^ 35
    - 4129 * s ^ 34
    + 5521 * s ^ 33
    - 4370 * s ^ 32
    + 2290 * s ^ 31
    + 592 * s ^ 30
    - 3465 * s ^ 29
    + 3799 * s ^ 28
    - 3139 * s ^ 27
    + 2220 * s ^ 26
    - 1429 * s ^ 25
    + 863 * s ^ 24
    - 485 * s ^ 23
    + 242 * s ^ 22
    - 102 * s ^ 21
    + 34 * s ^ 20
    - 8 * s ^ 19
    + s ^ 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 44
    + 10 * s ^ 43
    - 53 * s ^ 42
    + 173 * s ^ 41
    - 344 * s ^ 40
    + 866 * s ^ 39
    - 3775 * s ^ 38
    + 11881 * s ^ 37
    - 28061 * s ^ 36
    + 55545 * s ^ 35
    - 100714 * s ^ 34
    + 175167 * s ^ 33
    - 263745 * s ^ 32
    + 311340 * s ^ 31
    - 314154 * s ^ 30
    + 261035 * s ^ 29
    - 163366 * s ^ 28
    + 83522 * s ^ 27
    - 32248 * s ^ 26
    + 5231 * s ^ 25
    + 6677 * s ^ 24
    - 10641 * s ^ 23
    + 10453 * s ^ 22
    - 8074 * s ^ 21
    + 5084 * s ^ 20
    - 2599 * s ^ 19
    + 1055 * s ^ 18
    - 328 * s ^ 17
    + 75 * s ^ 16
    - 12 * s ^ 15
    + s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient4 (s : ℚ) : ℚ :=
  -3 * s ^ 45
    + 32 * s ^ 44
    - 149 * s ^ 43
    + 421 * s ^ 42
    - 943 * s ^ 41
    + 3399 * s ^ 40
    - 15588 * s ^ 39
    + 45366 * s ^ 38
    - 77778 * s ^ 37
    + 89996 * s ^ 36
    - 70676 * s ^ 35
    + 2277 * s ^ 34
    + 265710 * s ^ 33
    - 1131513 * s ^ 32
    + 2701333 * s ^ 31
    - 4375157 * s ^ 30
    + 5789721 * s ^ 29
    - 6377519 * s ^ 28
    + 5798595 * s ^ 27
    - 4654728 * s ^ 26
    + 3428017 * s ^ 25
    - 2375850 * s ^ 24
    + 1560689 * s ^ 23
    - 955887 * s ^ 22
    + 526536 * s ^ 21
    - 248731 * s ^ 20
    + 93843 * s ^ 19
    - 24048 * s ^ 18
    + 1258 * s ^ 17
    + 2422 * s ^ 16
    - 1434 * s ^ 15
    + 480 * s ^ 14
    - 104 * s ^ 13
    + 14 * s ^ 12
    - s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient5 (s : ℚ) : ℚ :=
  -2 * s ^ 46
    + 13 * s ^ 45
    + 78 * s ^ 44
    - 1110 * s ^ 43
    + 5475 * s ^ 42
    - 16672 * s ^ 41
    + 42611 * s ^ 40
    - 140963 * s ^ 39
    + 529471 * s ^ 38
    - 1546818 * s ^ 37
    + 3402615 * s ^ 36
    - 6434362 * s ^ 35
    + 11692911 * s ^ 34
    - 20936426 * s ^ 33
    + 34069624 * s ^ 32
    - 45528722 * s ^ 31
    + 48916707 * s ^ 30
    - 43522468 * s ^ 29
    + 29278381 * s ^ 28
    - 11853226 * s ^ 27
    - 68691 * s ^ 26
    + 5534825 * s ^ 25
    - 6876265 * s ^ 24
    + 6705448 * s ^ 23
    - 6325275 * s ^ 22
    + 5803769 * s ^ 21
    - 4869343 * s ^ 20
    + 3561181 * s ^ 19
    - 2210690 * s ^ 18
    + 1145284 * s ^ 17
    - 488333 * s ^ 16
    + 169310 * s ^ 15
    - 47002 * s ^ 14
    + 10123 * s ^ 13
    - 1636 * s ^ 12
    + 193 * s ^ 11
    - 16 * s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient6 (s : ℚ) : ℚ :=
  2 * s ^ 47
    - 51 * s ^ 46
    + 595 * s ^ 45
    - 3864 * s ^ 44
    + 15888 * s ^ 43
    - 49806 * s ^ 42
    + 157062 * s ^ 41
    - 560917 * s ^ 40
    + 1861515 * s ^ 39
    - 4765275 * s ^ 38
    + 9098829 * s ^ 37
    - 14721264 * s ^ 36
    + 24964042 * s ^ 35
    - 43955561 * s ^ 34
    + 64002958 * s ^ 33
    - 52614445 * s ^ 32
    - 27934788 * s ^ 31
    + 168811875 * s ^ 30
    - 322848757 * s ^ 29
    + 448902718 * s ^ 28
    - 491525237 * s ^ 27
    + 441593121 * s ^ 26
    - 358006831 * s ^ 25
    + 284293497 * s ^ 24
    - 232972305 * s ^ 23
    + 194505919 * s ^ 22
    - 155794181 * s ^ 21
    + 112794033 * s ^ 20
    - 70813279 * s ^ 19
    + 37259832 * s ^ 18
    - 15721761 * s ^ 17
    + 4856358 * s ^ 16
    - 762513 * s ^ 15
    - 219370 * s ^ 14
    + 230045 * s ^ 13
    - 104430 * s ^ 12
    + 33003 * s ^ 11
    - 7951 * s ^ 10
    + 1485 * s ^ 9
    - 210 * s ^ 8
    + 20 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient7 (s : ℚ) : ℚ :=
  3 * s ^ 48
    - 60 * s ^ 47
    + 536 * s ^ 46
    - 2614 * s ^ 45
    + 6796 * s ^ 44
    - 9819 * s ^ 43
    + 39783 * s ^ 42
    - 280461 * s ^ 41
    + 958574 * s ^ 40
    - 910221 * s ^ 39
    - 4942968 * s ^ 38
    + 23048988 * s ^ 37
    - 52093885 * s ^ 36
    + 97396977 * s ^ 35
    - 227653472 * s ^ 34
    + 598982752 * s ^ 33
    - 1346513011 * s ^ 32
    + 2357051001 * s ^ 31
    - 3243956331 * s ^ 30
    + 3698893820 * s ^ 29
    - 3624176727 * s ^ 28
    + 3049146334 * s ^ 27
    - 2386811118 * s ^ 26
    + 2065363788 * s ^ 25
    - 2043337573 * s ^ 24
    + 2060579770 * s ^ 23
    - 1890521683 * s ^ 22
    + 1483975687 * s ^ 21
    - 956821446 * s ^ 20
    + 475521625 * s ^ 19
    - 147614469 * s ^ 18
    - 13238895 * s ^ 17
    + 57165133 * s ^ 16
    - 47285234 * s ^ 15
    + 26337316 * s ^ 14
    - 11307034 * s ^ 13
    + 3882195 * s ^ 12
    - 1077698 * s ^ 11
    + 240761 * s ^ 10
    - 42077 * s ^ 9
    + 5345 * s ^ 8
    - 391 * s ^ 7
    + s ^ 6
    + 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient8 (s : ℚ) : ℚ :=
  s ^ 49
    - 14 * s ^ 48
    + 9 * s ^ 47
    + 1148 * s ^ 46
    - 11588 * s ^ 45
    + 58627 * s ^ 44
    - 188923 * s ^ 43
    + 559935 * s ^ 42
    - 2473404 * s ^ 41
    + 11861743 * s ^ 40
    - 43149673 * s ^ 39
    + 113890503 * s ^ 38
    - 237070650 * s ^ 37
    + 482902824 * s ^ 36
    - 1147549461 * s ^ 35
    + 2758504138 * s ^ 34
    - 5560431627 * s ^ 33
    + 8777118929 * s ^ 32
    - 10660336761 * s ^ 31
    + 10027702213 * s ^ 30
    - 7519567052 * s ^ 29
    + 4638591083 * s ^ 28
    - 3174432696 * s ^ 27
    + 5058182906 * s ^ 26
    - 9507673604 * s ^ 25
    + 13222044622 * s ^ 24
    - 13796489459 * s ^ 23
    + 10903209330 * s ^ 22
    - 6019387678 * s ^ 21
    + 1245510967 * s ^ 20
    + 1915826066 * s ^ 19
    - 3099058136 * s ^ 18
    + 2834784429 * s ^ 17
    - 1952471972 * s ^ 16
    + 1084930148 * s ^ 15
    - 498666598 * s ^ 14
    + 191029949 * s ^ 13
    - 60793277 * s ^ 12
    + 15902593 * s ^ 11
    - 3336356 * s ^ 10
    + 528830 * s ^ 9
    - 53451 * s ^ 8
    + 861 * s ^ 7
    + 589 * s ^ 6
    - 62 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient9 (s : ℚ) : ℚ :=
  5 * s ^ 49
    - 129 * s ^ 48
    + 1430 * s ^ 47
    - 8917 * s ^ 46
    + 35572 * s ^ 45
    - 122679 * s ^ 44
    + 640077 * s ^ 43
    - 3942593 * s ^ 42
    + 18323909 * s ^ 41
    - 59707195 * s ^ 40
    + 143882177 * s ^ 39
    - 305161184 * s ^ 38
    + 764682834 * s ^ 37
    - 2229674425 * s ^ 36
    + 5639227898 * s ^ 35
    - 10532017917 * s ^ 34
    + 13291139605 * s ^ 33
    - 8560088585 * s ^ 32
    - 5211901782 * s ^ 31
    + 21290621756 * s ^ 30
    - 28908905578 * s ^ 29
    + 21190343688 * s ^ 28
    + 3855006311 * s ^ 27
    - 39419741412 * s ^ 26
    + 65017812386 * s ^ 25
    - 62919850844 * s ^ 24
    + 33242851510 * s ^ 23
    + 10422205466 * s ^ 22
    - 50088631698 * s ^ 21
    + 72629415421 * s ^ 20
    - 74718007486 * s ^ 19
    + 61694159783 * s ^ 18
    - 42549929900 * s ^ 17
    + 24886826860 * s ^ 16
    - 12407038318 * s ^ 15
    + 5268914356 * s ^ 14
    - 1893699325 * s ^ 13
    + 568117932 * s ^ 12
    - 138871819 * s ^ 11
    + 26252230 * s ^ 10
    - 3305114 * s ^ 9
    + 93980 * s ^ 8
    + 64270 * s ^ 7
    - 13456 * s ^ 6
    + 860 * s ^ 5
    + 40 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient10 (s : ℚ) : ℚ :=
  s ^ 50
    - 21 * s ^ 49
    + 146 * s ^ 48
    - 117 * s ^ 47
    - 1891 * s ^ 46
    - 24236 * s ^ 45
    + 459814 * s ^ 44
    - 3236546 * s ^ 43
    + 13223548 * s ^ 42
    - 34465852 * s ^ 41
    + 65084436 * s ^ 40
    - 160116686 * s ^ 39
    + 678980391 * s ^ 38
    - 2445237656 * s ^ 37
    + 5526412641 * s ^ 36
    - 5645111618 * s ^ 35
    - 8087608863 * s ^ 34
    + 46116529722 * s ^ 33
    - 102255694593 * s ^ 32
    + 145167311306 * s ^ 31
    - 135941233421 * s ^ 30
    + 61432004571 * s ^ 29
    + 55978870486 * s ^ 28
    - 167533253339 * s ^ 27
    + 192069150234 * s ^ 26
    - 51252327624 * s ^ 25
    - 245148579097 * s ^ 24
    + 597435065114 * s ^ 23
    - 885577232055 * s ^ 22
    + 1022246020089 * s ^ 21
    - 984518247054 * s ^ 20
    + 812877725732 * s ^ 19
    - 581758580019 * s ^ 18
    + 361958615249 * s ^ 17
    - 195490704914 * s ^ 16
    + 91241371182 * s ^ 15
    - 36502223367 * s ^ 14
    + 12335054530 * s ^ 13
    - 3429414091 * s ^ 12
    + 744199956 * s ^ 11
    - 108237880 * s ^ 10
    + 2703753 * s ^ 9
    + 3734463 * s ^ 8
    - 1133810 * s ^ 7
    + 153610 * s ^ 6
    - 5381 * s ^ 5
    - 845 * s ^ 4
    + 2 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient11 (s : ℚ) : ℚ :=
  s ^ 50
    - 27 * s ^ 49
    + 162 * s ^ 48
    + 2179 * s ^ 47
    - 43880 * s ^ 46
    + 342204 * s ^ 45
    - 1432484 * s ^ 44
    + 2578914 * s ^ 43
    + 4552117 * s ^ 42
    - 33502977 * s ^ 41
    + 32345953 * s ^ 40
    + 226814180 * s ^ 39
    - 600646278 * s ^ 38
    - 2301987208 * s ^ 37
    + 20185731886 * s ^ 36
    - 72202766393 * s ^ 35
    + 164938191571 * s ^ 34
    - 259881364878 * s ^ 33
    + 270973292388 * s ^ 32
    - 127720754488 * s ^ 31
    - 132816629156 * s ^ 30
    + 341235649561 * s ^ 29
    - 260515791605 * s ^ 28
    - 368897659257 * s ^ 27
    + 1762709102291 * s ^ 26
    - 3844205366323 * s ^ 25
    + 6104780657649 * s ^ 24
    - 7883297086841 * s ^ 23
    + 8695589770189 * s ^ 22
    - 8377309530052 * s ^ 21
    + 7116444711480 * s ^ 20
    - 5345486260205 * s ^ 19
    + 3545254386122 * s ^ 18
    - 2066861525318 * s ^ 17
    + 1052003922752 * s ^ 16
    - 462919021797 * s ^ 15
    + 173353012252 * s ^ 14
    - 53670858412 * s ^ 13
    + 12918083277 * s ^ 12
    - 2001043756 * s ^ 11
    - 28272446 * s ^ 10
    + 140016312 * s ^ 9
    - 50851079 * s ^ 8
    + 10261846 * s ^ 7
    - 1028758 * s ^ 6
    - 13242 * s ^ 5
    + 11613 * s ^ 4
    - 38 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient12 (s : ℚ) : ℚ :=
  3 * s ^ 50
    - 103 * s ^ 49
    + 1444 * s ^ 48
    - 9062 * s ^ 47
    - 2855 * s ^ 46
    + 507273 * s ^ 45
    - 4362537 * s ^ 44
    + 20372831 * s ^ 43
    - 59494395 * s ^ 42
    + 127856244 * s ^ 41
    - 448784548 * s ^ 40
    + 2834370212 * s ^ 39
    - 14325383370 * s ^ 38
    + 50280271149 * s ^ 37
    - 124482236520 * s ^ 36
    + 213651135838 * s ^ 35
    - 221312809625 * s ^ 34
    + 21245813988 * s ^ 33
    + 371538805521 * s ^ 32
    - 609646958332 * s ^ 31
    + 2355867102 * s ^ 30
    + 2274734867142 * s ^ 29
    - 6966782844357 * s ^ 28
    + 14562598420722 * s ^ 27
    - 24734650479171 * s ^ 26
    + 35686266538776 * s ^ 25
    - 44661134337634 * s ^ 24
    + 49357056548241 * s ^ 23
    - 48721321420704 * s ^ 22
    + 43114216731095 * s ^ 21
    - 34171562352330 * s ^ 20
    + 24165856282396 * s ^ 19
    - 15154421036881 * s ^ 18
    + 8355015645440 * s ^ 17
    - 4002328554070 * s ^ 16
    + 1635820164570 * s ^ 15
    - 551385622772 * s ^ 14
    + 141460583535 * s ^ 13
    - 20349144878 * s ^ 12
    - 3318712538 * s ^ 11
    + 3564249628 * s ^ 10
    - 1420819934 * s ^ 9
    + 364922502 * s ^ 8
    - 58546502 * s ^ 7
    + 3462514 * s ^ 6
    + 606647 * s ^ 5
    - 111837 * s ^ 4
    + 108 * s ^ 3
    + 34 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient13 (s : ℚ) : ℚ :=
  6 * s ^ 50
    - 258 * s ^ 49
    + 4986 * s ^ 48
    - 56724 * s ^ 47
    + 417358 * s ^ 46
    - 2060875 * s ^ 45
    + 7136358 * s ^ 44
    - 22853655 * s ^ 43
    + 123264223 * s ^ 42
    - 838451803 * s ^ 41
    + 4444423661 * s ^ 40
    - 16830604721 * s ^ 39
    + 44828577484 * s ^ 38
    - 77514271788 * s ^ 37
    + 51808143609 * s ^ 36
    + 142372097835 * s ^ 35
    - 504850180762 * s ^ 34
    + 584130146174 * s ^ 33
    + 827066905899 * s ^ 32
    - 5631524464091 * s ^ 31
    + 15999161520056 * s ^ 30
    - 33933972939634 * s ^ 29
    + 60838265969729 * s ^ 28
    - 96237942993375 * s ^ 27
    + 135744511081574 * s ^ 26
    - 171098116158783 * s ^ 25
    + 193791008527421 * s ^ 24
    - 198589073027889 * s ^ 23
    + 184479470893006 * s ^ 22
    - 154854636735624 * s ^ 21
    + 116792421491290 * s ^ 20
    - 78535794386899 * s ^ 19
    + 46601258442434 * s ^ 18
    - 24050832032901 * s ^ 17
    + 10551271996707 * s ^ 16
    - 3759931271624 * s ^ 15
    + 960168989506 * s ^ 14
    - 77339596838 * s ^ 13
    - 85795876745 * s ^ 12
    + 62698832735 * s ^ 11
    - 26539655576 * s ^ 10
    + 8049890768 * s ^ 9
    - 1717647761 * s ^ 8
    + 206198038 * s ^ 7
    + 6061485 * s ^ 6
    - 6534990 * s ^ 5
    + 786946 * s ^ 4
    + 4586 * s ^ 3
    - 558 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient14 (s : ℚ) : ℚ :=
  s ^ 51
    - 36 * s ^ 50
    + 560 * s ^ 49
    - 4672 * s ^ 48
    + 20788 * s ^ 47
    - 59602 * s ^ 46
    + 752470 * s ^ 45
    - 12139791 * s ^ 44
    + 112247743 * s ^ 43
    - 666771170 * s ^ 42
    + 2687756077 * s ^ 41
    - 7060861749 * s ^ 40
    + 8466250825 * s ^ 39
    + 18873323006 * s ^ 38
    - 122029645686 * s ^ 37
    + 275819606996 * s ^ 36
    - 79757661636 * s ^ 35
    - 1737803493541 * s ^ 34
    + 7701078273334 * s ^ 33
    - 21497341355261 * s ^ 32
    + 47553606625247 * s ^ 31
    - 90734021358071 * s ^ 30
    + 155682013753459 * s ^ 29
    - 244004499767217 * s ^ 28
    + 349054192200427 * s ^ 27
    - 453367364496063 * s ^ 26
    + 534412411526933 * s ^ 25
    - 574103860318532 * s ^ 24
    + 563158043007795 * s ^ 23
    - 502281894772078 * s ^ 22
    + 404068308446505 * s ^ 21
    - 290374332683579 * s ^ 20
    + 184064638766934 * s ^ 19
    - 101008538572542 * s ^ 18
    + 46446715192978 * s ^ 17
    - 16616399584159 * s ^ 16
    + 3493439172669 * s ^ 15
    + 691639703048 * s ^ 14
    - 1215275862917 * s ^ 13
    + 770558880257 * s ^ 12
    - 344320107553 * s ^ 11
    + 118485825370 * s ^ 10
    - 30886478341 * s ^ 9
    + 5345261708 * s ^ 8
    - 254297365 * s ^ 7
    - 156565474 * s ^ 6
    + 44472104 * s ^ 5
    - 4135021 * s ^ 4
    - 81063 * s ^ 3
    + 5885 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient15 (s : ℚ) : ℚ :=
  -4 * s ^ 50
    + 28 * s ^ 49
    + 2391 * s ^ 48
    - 68536 * s ^ 47
    + 941051 * s ^ 46
    - 8107221 * s ^ 45
    + 46577558 * s ^ 44
    - 169645302 * s ^ 43
    + 246089469 * s ^ 42
    + 1233905736 * s ^ 41
    - 9778331909 * s ^ 40
    + 31774177978 * s ^ 39
    - 31169176032 * s ^ 38
    - 233215029324 * s ^ 37
    + 1571393597087 * s ^ 36
    - 5874196934031 * s ^ 35
    + 16519330322570 * s ^ 34
    - 38525527680463 * s ^ 33
    + 78850380329875 * s ^ 32
    - 147154688717046 * s ^ 31
    + 255451364828661 * s ^ 30
    - 413087676659279 * s ^ 29
    + 616276703659151 * s ^ 28
    - 839869985747018 * s ^ 27
    + 1042594427851228 * s ^ 26
    - 1183272434778218 * s ^ 25
    + 1231360474072684 * s ^ 24
    - 1169698180234235 * s ^ 23
    + 1003158671382185 * s ^ 22
    - 766423176537659 * s ^ 21
    + 513047950425454 * s ^ 20
    - 292844929281678 * s ^ 19
    + 134710712567656 * s ^ 18
    - 42013089269305 * s ^ 17
    - 60323338080 * s ^ 16
    + 12107491392852 * s ^ 15
    - 11021638636000 * s ^ 14
    + 6693125216229 * s ^ 13
    - 3170548998272 * s ^ 12
    + 1211926739548 * s ^ 11
    - 368006431336 * s ^ 10
    + 81026673941 * s ^ 9
    - 8483624702 * s ^ 8
    - 1956244536 * s ^ 7
    + 1106566170 * s ^ 6
    - 220740573 * s ^ 5
    + 16173863 * s ^ 4
    + 762192 * s ^ 3
    - 44798 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient16 (s : ℚ) : ℚ :=
  s ^ 51
    - 51 * s ^ 50
    + 1182 * s ^ 49
    - 15807 * s ^ 48
    + 125955 * s ^ 47
    - 464990 * s ^ 46
    - 1823525 * s ^ 45
    + 37642777 * s ^ 44
    - 261584976 * s ^ 43
    + 967212763 * s ^ 42
    - 533418460 * s ^ 41
    - 18216753704 * s ^ 40
    + 140782560513 * s ^ 39
    - 661398563162 * s ^ 38
    + 2348228245270 * s ^ 37
    - 6801514438453 * s ^ 36
    + 16857733497722 * s ^ 35
    - 37276350932195 * s ^ 34
    + 76359126773088 * s ^ 33
    - 148467984910060 * s ^ 32
    + 274599142868654 * s ^ 31
    - 475779227904564 * s ^ 30
    + 757936994224987 * s ^ 29
    - 1097802155962105 * s ^ 28
    + 1444871428887671 * s ^ 27
    - 1739406012735673 * s ^ 26
    + 1925021003884424 * s ^ 25
    - 1948751207803715 * s ^ 24
    + 1776440111659876 * s ^ 23
    - 1428177921448423 * s ^ 22
    + 986379169571841 * s ^ 21
    - 557049946465222 * s ^ 20
    + 222677536373290 * s ^ 19
    - 17109568692453 * s ^ 18
    - 73196187042225 * s ^ 17
    + 87952607812173 * s ^ 16
    - 68157122170498 * s ^ 15
    + 41591686087734 * s ^ 14
    - 20977143623450 * s ^ 13
    + 8813053862334 * s ^ 12
    - 3028325563442 * s ^ 11
    + 793591123296 * s ^ 10
    - 118979691863 * s ^ 9
    - 14909322608 * s ^ 8
    + 16141707315 * s ^ 7
    - 5163619382 * s ^ 6
    + 840022312 * s ^ 5
    - 44447280 * s ^ 4
    - 5008923 * s ^ 3
    + 262030 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient17 (s : ℚ) : ℚ :=
  -16 * s ^ 50
    + 706 * s ^ 49
    - 14172 * s ^ 48
    + 164078 * s ^ 47
    - 1075967 * s ^ 46
    + 1527841 * s ^ 45
    + 50161226 * s ^ 44
    - 660274901 * s ^ 43
    + 5006597211 * s ^ 42
    - 27777438222 * s ^ 41
    + 121539090954 * s ^ 40
    - 436037337428 * s ^ 39
    + 1321750592054 * s ^ 38
    - 3499161273745 * s ^ 37
    + 8441277999385 * s ^ 36
    - 19445189620759 * s ^ 35
    + 44046238573056 * s ^ 34
    - 97377147562531 * s ^ 33
    + 203238726938995 * s ^ 32
    - 387703704333216 * s ^ 31
    + 664330883114564 * s ^ 30
    - 1020422937568304 * s ^ 29
    + 1417833418625522 * s ^ 28
    - 1806184732810167 * s ^ 27
    + 2125073994477279 * s ^ 26
    - 2288757343986474 * s ^ 25
    + 2198539032254046 * s ^ 24
    - 1814313705925553 * s ^ 23
    + 1215435284154850 * s ^ 22
    - 567263258931527 * s ^ 21
    + 30516905203058 * s ^ 20
    + 302705956300657 * s ^ 19
    - 425930321339304 * s ^ 18
    + 397408419805503 * s ^ 17
    - 296553679554308 * s ^ 16
    + 186553653358749 * s ^ 15
    - 100424990109083 * s ^ 14
    + 46050380011251 * s ^ 13
    - 17582950386790 * s ^ 12
    + 5248907656604 * s ^ 11
    - 962697623154 * s ^ 10
    - 90856044656 * s ^ 9
    + 161228481746 * s ^ 8
    - 71242359359 * s ^ 7
    + 18137800879 * s ^ 6
    - 2483735303 * s ^ 5
    + 62440600 * s ^ 4
    + 25197903 * s ^ 3
    - 1223751 * s ^ 2
    - 27 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient18 (s : ℚ) : ℚ :=
  -18 * s ^ 50
    + 996 * s ^ 49
    - 26143 * s ^ 48
    + 433175 * s ^ 47
    - 5082024 * s ^ 46
    + 44863244 * s ^ 45
    - 309115155 * s ^ 44
    + 1702502952 * s ^ 43
    - 7626756738 * s ^ 42
    + 28258299020 * s ^ 41
    - 88837873843 * s ^ 40
    + 249325197396 * s ^ 39
    - 682574015916 * s ^ 38
    + 1986518506558 * s ^ 37
    - 6109778276498 * s ^ 36
    + 18237820405412 * s ^ 35
    - 49083491504741 * s ^ 34
    + 115211133270610 * s ^ 33
    - 234383646177443 * s ^ 32
    + 416703821940485 * s ^ 31
    - 659042521490875 * s ^ 30
    + 949684708291183 * s ^ 29
    - 1274177323087684 * s ^ 28
    + 1598157738006193 * s ^ 27
    - 1827099586664884 * s ^ 26
    + 1804744420946939 * s ^ 25
    - 1410931447408979 * s ^ 24
    + 688891204349878 * s ^ 23
    + 151718374059542 * s ^ 22
    - 865414045436737 * s ^ 21
    + 1290482383483999 * s ^ 20
    - 1386666260918247 * s ^ 19
    + 1221639184316235 * s ^ 18
    - 921512157556155 * s ^ 17
    + 605902108460744 * s ^ 16
    - 348317938302692 * s ^ 15
    + 173207474657663 * s ^ 14
    - 72431282778805 * s ^ 13
    + 23794218409569 * s ^ 12
    - 4753150220173 * s ^ 11
    - 673337145735 * s ^ 10
    + 1214868299981 * s ^ 9
    - 663673473949 * s ^ 8
    + 228108513805 * s ^ 7
    - 50043258381 * s ^ 6
    + 5584464444 * s ^ 5
    + 131758228 * s ^ 4
    - 101546178 * s ^ 3
    + 4679394 * s ^ 2
    + 348 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient19 (s : ℚ) : ℚ :=
  -2 * s ^ 51
    + 102 * s ^ 50
    - 2457 * s ^ 49
    + 36851 * s ^ 48
    - 381271 * s ^ 47
    + 2836311 * s ^ 46
    - 15183846 * s ^ 45
    + 55292143 * s ^ 44
    - 107336902 * s ^ 43
    - 64670304 * s ^ 42
    + 458979116 * s ^ 41
    + 7619759698 * s ^ 40
    - 90230285804 * s ^ 39
    + 547444005092 * s ^ 38
    - 2356404508190 * s ^ 37
    + 7909086626869 * s ^ 36
    - 21605024442732 * s ^ 35
    + 49273849749051 * s ^ 34
    - 95881916277996 * s ^ 33
    + 163599580251958 * s ^ 32
    - 254717155023953 * s ^ 31
    + 379276130394045 * s ^ 30
    - 553233544959769 * s ^ 29
    + 765877578377320 * s ^ 28
    - 924389953745087 * s ^ 27
    + 843492052694667 * s ^ 26
    - 353011354217504 * s ^ 25
    - 532984145172925 * s ^ 24
    + 1572181371408694 * s ^ 23
    - 2446135400738467 * s ^ 22
    + 2936708801755307 * s ^ 21
    - 2977010524761687 * s ^ 20
    + 2629355998984315 * s ^ 19
    - 2049449717094770 * s ^ 18
    + 1418028532351394 * s ^ 17
    - 869215009499918 * s ^ 16
    + 465097476904043 * s ^ 15
    - 209543691218123 * s ^ 14
    + 72748199491709 * s ^ 13
    - 13268929853642 * s ^ 12
    - 5425333795511 * s ^ 11
    + 7265822907222 * s ^ 10
    - 4488652913883 * s ^ 9
    + 1908524823675 * s ^ 8
    - 571183391752 * s ^ 7
    + 109294239661 * s ^ 6
    - 8587096016 * s ^ 5
    - 1257103848 * s ^ 4
    + 336708552 * s ^ 3
    - 14898589 * s ^ 2
    - 2847 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient20 (s : ℚ) : ℚ :=
  9 * s ^ 50
    - 423 * s ^ 49
    + 9368 * s ^ 48
    - 127920 * s ^ 47
    + 1171838 * s ^ 46
    - 7117291 * s ^ 45
    + 22381128 * s ^ 44
    + 64878962 * s ^ 43
    - 1428317148 * s ^ 42
    + 11133787056 * s ^ 41
    - 59755766170 * s ^ 40
    + 247541764164 * s ^ 39
    - 823653567536 * s ^ 38
    + 2235392603823 * s ^ 37
    - 4968941251657 * s ^ 36
    + 9057530306261 * s ^ 35
    - 13789665569116 * s ^ 34
    + 19318763863327 * s ^ 33
    - 31565051275121 * s ^ 32
    + 66635539916090 * s ^ 31
    - 141980423123629 * s ^ 30
    + 241332181611896 * s ^ 29
    - 266937321019372 * s ^ 28
    + 37439812285267 * s ^ 27
    + 608943422849735 * s ^ 26
    - 1650625158378196 * s ^ 25
    + 2828429067544667 * s ^ 24
    - 3798310290991395 * s ^ 23
    + 4333841028871274 * s ^ 22
    - 4373071588672050 * s ^ 21
    + 3959609021898114 * s ^ 20
    - 3221122373433166 * s ^ 19
    + 2350072191101914 * s ^ 18
    - 1528967439783343 * s ^ 17
    + 869620278218871 * s ^ 16
    - 410671028062737 * s ^ 15
    + 138777029642141 * s ^ 14
    - 9089220515560 * s ^ 13
    - 33466476849919 * s ^ 12
    + 34709242544043 * s ^ 11
    - 22895677991548 * s ^ 10
    + 11365169681739 * s ^ 9
    - 4267055640600 * s ^ 8
    + 1143878331825 * s ^ 7
    - 184061838165 * s ^ 6
    + 4140017787 * s ^ 5
    + 5058272155 * s ^ 4
    - 934215318 * s ^ 3
    + 39937347 * s ^ 2
    + 16579 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient21 (s : ℚ) : ℚ :=
  3 * s ^ 50
    - 178 * s ^ 49
    + 4978 * s ^ 48
    - 87680 * s ^ 47
    + 1092718 * s ^ 46
    - 10234955 * s ^ 45
    + 74508821 * s ^ 44
    - 428555778 * s ^ 43
    + 1948939534 * s ^ 42
    - 6851999436 * s ^ 41
    + 17171763083 * s ^ 40
    - 20517122860 * s ^ 39
    - 59224294652 * s ^ 38
    + 452784265144 * s ^ 37
    - 1557350559069 * s ^ 36
    + 3457487767957 * s ^ 35
    - 4394857101371 * s ^ 34
    - 1369505043245 * s ^ 33
    + 22696257332573 * s ^ 32
    - 60564643573952 * s ^ 31
    + 82971587990350 * s ^ 30
    + 564723492792 * s ^ 29
    - 326963221510658 * s ^ 28
    + 997312322691256 * s ^ 27
    - 1960980650844593 * s ^ 26
    + 2987014357670570 * s ^ 25
    - 3798198413293085 * s ^ 24
    + 4244251700682179 * s ^ 23
    - 4316387906932749 * s ^ 22
    + 4039152218281766 * s ^ 21
    - 3447051307833597 * s ^ 20
    + 2648004255220646 * s ^ 19
    - 1807478919599248 * s ^ 18
    + 1062798948145528 * s ^ 17
    - 488873939584698 * s ^ 16
    + 111926031113020 * s ^ 15
    + 82690077725217 * s ^ 14
    - 143297992948437 * s ^ 13
    + 129686406178534 * s ^ 12
    - 89451498857148 * s ^ 11
    + 49947056287231 * s ^ 10
    - 22354290997267 * s ^ 9
    + 7658149994428 * s ^ 8
    - 1818510457944 * s ^ 7
    + 214107934877 * s ^ 6
    + 24829105823 * s ^ 5
    - 14558117570 * s ^ 4
    + 2192182778 * s ^ 3
    - 90748601 * s ^ 2
    - 73035 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient22 (s : ℚ) : ℚ :=
  -10 * s ^ 49
    + 537 * s ^ 48
    - 13916 * s ^ 47
    + 231288 * s ^ 46
    - 2762090 * s ^ 45
    + 25148583 * s ^ 44
    - 180603572 * s ^ 43
    + 1042247767 * s ^ 42
    - 4863372958 * s ^ 41
    + 18187740159 * s ^ 40
    - 52487956163 * s ^ 39
    + 102426312907 * s ^ 38
    - 42611501967 * s ^ 37
    - 643169970443 * s ^ 36
    + 3242504705461 * s ^ 35
    - 9641120028628 * s ^ 34
    + 19821580125645 * s ^ 33
    - 24767483845470 * s ^ 32
    - 4605775894889 * s ^ 31
    + 123626291563223 * s ^ 30
    - 397818914884530 * s ^ 29
    + 854736790717162 * s ^ 28
    - 1430125497231289 * s ^ 27
    + 1973824298029675 * s ^ 26
    - 2348598081857799 * s ^ 25
    + 2533619576731601 * s ^ 24
    - 2592355615464117 * s ^ 23
    + 2536632390932538 * s ^ 22
    - 2296321539021551 * s ^ 21
    + 1844592205437280 * s ^ 20
    - 1268412204335806 * s ^ 19
    + 689402846230157 * s ^ 18
    - 189983058619864 * s ^ 17
    - 177017277120676 * s ^ 16
    + 379800884969320 * s ^ 15
    - 427631075592749 * s ^ 14
    + 370260162790693 * s ^ 13
    - 267876697711489 * s ^ 12
    + 165011749607163 * s ^ 11
    - 85197864141858 * s ^ 10
    + 35403112479417 * s ^ 9
    - 11028938058790 * s ^ 8
    + 2181576781030 * s ^ 7
    - 78806715532 * s ^ 6
    - 103379905506 * s ^ 5
    + 33196467590 * s ^ 4
    - 4378251762 * s ^ 3
    + 175361760 * s ^ 2
    + 252468 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient23 (s : ℚ) : ℚ :=
  -s ^ 49
    + 69 * s ^ 48
    - 2210 * s ^ 47
    + 44436 * s ^ 46
    - 635089 * s ^ 45
    + 6899169 * s ^ 44
    - 59343742 * s ^ 43
    + 414983651 * s ^ 42
    - 2399697802 * s ^ 41
    + 11588086259 * s ^ 40
    - 46861130829 * s ^ 39
    + 157677601821 * s ^ 38
    - 431224471373 * s ^ 37
    + 894667058280 * s ^ 36
    - 1054963186552 * s ^ 35
    - 1341504148418 * s ^ 34
    + 12513982340252 * s ^ 33
    - 44724065607502 * s ^ 32
    + 114749294434750 * s ^ 31
    - 234067397281084 * s ^ 30
    + 391166557935120 * s ^ 29
    - 540429218901413 * s ^ 28
    + 622717823621929 * s ^ 27
    - 621227913016708 * s ^ 26
    + 597977722103434 * s ^ 25
    - 637339257192483 * s ^ 24
    + 729144133293864 * s ^ 23
    - 748255912615993 * s ^ 22
    + 589700866425418 * s ^ 21
    - 280593534266755 * s ^ 20
    - 79616797804767 * s ^ 19
    + 422953499842292 * s ^ 18
    - 707981304983829 * s ^ 17
    + 881332584262536 * s ^ 16
    - 905041240529691 * s ^ 15
    + 795699861822367 * s ^ 14
    - 611400290200939 * s ^ 13
    + 412633244454380 * s ^ 12
    - 240941601719116 * s ^ 11
    + 117504069217627 * s ^ 10
    - 45200926663238 * s ^ 9
    + 12310454428262 * s ^ 8
    - 1609655011801 * s ^ 7
    - 357984112486 * s ^ 6
    + 250751754226 * s ^ 5
    - 62263979070 * s ^ 4
    + 7464774409 * s ^ 3
    - 288180677 * s ^ 2
    - 700983 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient24 (s : ℚ) : ℚ :=
  2 * s ^ 48
    - 119 * s ^ 47
    + 3438 * s ^ 46
    - 64283 * s ^ 45
    + 874225 * s ^ 44
    - 9211287 * s ^ 43
    + 78205454 * s ^ 42
    - 549356733 * s ^ 41
    + 3252908651 * s ^ 40
    - 16455596194 * s ^ 39
    + 71797504823 * s ^ 38
    - 271874406340 * s ^ 37
    + 896248352215 * s ^ 36
    - 2570847304642 * s ^ 35
    + 6383176902938 * s ^ 34
    - 13545706082178 * s ^ 33
    + 23919061400798 * s ^ 32
    - 33059782351577 * s ^ 31
    + 29505948768534 * s ^ 30
    + 2413428621677 * s ^ 29
    - 68418171245036 * s ^ 28
    + 143865760638244 * s ^ 27
    - 173090032148723 * s ^ 26
    + 115135780698974 * s ^ 25
    - 9051825762412 * s ^ 24
    - 28960409029730 * s ^ 23
    - 89758169120452 * s ^ 22
    + 337485537810370 * s ^ 21
    - 621213165561299 * s ^ 20
    + 890551183612073 * s ^ 19
    - 1137389031638628 * s ^ 18
    + 1322674719329403 * s ^ 17
    - 1378600821658679 * s ^ 16
    + 1277495420288876 * s ^ 15
    - 1056295510859223 * s ^ 14
    + 780837386662345 * s ^ 13
    - 510055489508410 * s ^ 12
    + 285795626981533 * s ^ 11
    - 130848450739212 * s ^ 10
    + 45088739301885 * s ^ 9
    - 9396838113661 * s ^ 8
    - 345841178225 * s ^ 7
    + 1135556859795 * s ^ 6
    - 456896489124 * s ^ 5
    + 97634673006 * s ^ 4
    - 10865953600 * s ^ 3
    + 401393672 * s ^ 2
    + 1586836 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient25 (s : ℚ) : ℚ :=
  -s ^ 47
    + 57 * s ^ 46
    - 1596 * s ^ 45
    + 29182 * s ^ 44
    - 391061 * s ^ 43
    + 4090183 * s ^ 42
    - 34746346 * s ^ 41
    + 246454016 * s ^ 40
    - 1489389445 * s ^ 39
    + 7786286557 * s ^ 38
    - 35614160795 * s ^ 37
    + 143654931610 * s ^ 36
    - 513325427784 * s ^ 35
    + 1626497484425 * s ^ 34
    - 4556056783765 * s ^ 33
    + 11195703812983 * s ^ 32
    - 23803329383232 * s ^ 31
    + 42787781870923 * s ^ 30
    - 62458997282991 * s ^ 29
    + 68174263791455 * s ^ 28
    - 43292788846494 * s ^ 27
    - 9006215023407 * s ^ 26
    + 44847031520143 * s ^ 25
    + 4639242601411 * s ^ 24
    - 173306638109055 * s ^ 23
    + 418955687269730 * s ^ 22
    - 668941247239308 * s ^ 21
    + 901613805085659 * s ^ 20
    - 1141609572696588 * s ^ 19
    + 1375690639774379 * s ^ 18
    - 1526943284173199 * s ^ 17
    + 1526327196358699 * s ^ 16
    - 1371986352160253 * s ^ 15
    + 1112999145517397 * s ^ 14
    - 808932867525846 * s ^ 13
    + 513839168746054 * s ^ 12
    - 273311846037578 * s ^ 11
    + 113615945842387 * s ^ 10
    - 31562345030346 * s ^ 9
    + 1890697038760 * s ^ 8
    + 3442272652375 * s ^ 7
    - 2086339588121 * s ^ 6
    + 667387399555 * s ^ 5
    - 128809063741 * s ^ 4
    + 13467815072 * s ^ 3
    - 470356582 * s ^ 2
    - 2955478 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient26 (s : ℚ) : ℚ :=
  -5 * s ^ 44
    + 280 * s ^ 43
    - 7277 * s ^ 42
    + 117347 * s ^ 41
    - 1314341 * s ^ 40
    + 10737620 * s ^ 39
    - 64214559 * s ^ 38
    + 260803427 * s ^ 37
    - 424123333 * s ^ 36
    - 3419260186 * s ^ 35
    + 38334228728 * s ^ 34
    - 228320562665 * s ^ 33
    + 998861617296 * s ^ 32
    - 3456217192557 * s ^ 31
    + 9662471075550 * s ^ 30
    - 21745392797814 * s ^ 29
    + 38246309114343 * s ^ 28
    - 48110046644110 * s ^ 27
    + 28629673960216 * s ^ 26
    + 42861580243693 * s ^ 25
    - 166007194979343 * s ^ 24
    + 309976107225470 * s ^ 23
    - 445447206226115 * s ^ 22
    + 586177289683217 * s ^ 21
    - 774697306829012 * s ^ 20
    + 1013546465769542 * s ^ 19
    - 1234018944075753 * s ^ 18
    + 1350758743948868 * s ^ 17
    - 1328404578723403 * s ^ 16
    + 1184499260476730 * s ^ 15
    - 955523055987167 * s ^ 14
    + 682529197012753 * s ^ 13
    - 414884076566515 * s ^ 12
    + 201574087661143 * s ^ 11
    - 68621529761265 * s ^ 10
    + 8261098463663 * s ^ 9
    + 7788232812594 * s ^ 8
    - 6583237367856 * s ^ 7
    + 2853300441044 * s ^ 6
    - 799610084240 * s ^ 5
    + 143013002319 * s ^ 4
    - 14133818940 * s ^ 3
    + 457591390 * s ^ 2
    + 4549223 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient27 (s : ℚ) : ℚ :=
  -s ^ 44
    + 65 * s ^ 43
    - 1992 * s ^ 42
    + 38680 * s ^ 41
    - 537671 * s ^ 40
    + 5715331 * s ^ 39
    - 48343852 * s ^ 38
    + 333548270 * s ^ 37
    - 1904694627 * s ^ 36
    + 9059463435 * s ^ 35
    - 35810812682 * s ^ 34
    + 115914485239 * s ^ 33
    - 294876696144 * s ^ 32
    + 519401237228 * s ^ 31
    - 251495156838 * s ^ 30
    - 2297621876364 * s ^ 29
    + 10828343405135 * s ^ 28
    - 29969702208948 * s ^ 27
    + 61295520036283 * s ^ 26
    - 98993718159259 * s ^ 25
    + 133408518447862 * s ^ 24
    - 166636679868830 * s ^ 23
    + 225214817142774 * s ^ 22
    - 344325060555340 * s ^ 21
    + 527347306307827 * s ^ 20
    - 727150655889835 * s ^ 19
    + 878917612993984 * s ^ 18
    - 946228946274906 * s ^ 17
    + 927021264534594 * s ^ 16
    - 829382744256446 * s ^ 15
    + 663447604039314 * s ^ 14
    - 455596747681133 * s ^ 13
    + 252421618614726 * s ^ 12
    - 99289824916598 * s ^ 11
    + 14506682904439 * s ^ 10
    + 14856104672879 * s ^ 9
    - 15404655663030 * s ^ 8
    + 8366392406778 * s ^ 7
    - 3086005369163 * s ^ 6
    + 790946618784 * s ^ 5
    - 133024612287 * s ^ 4
    + 12443810556 * s ^ 3
    - 361058923 * s ^ 2
    - 5789314 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient28 (s : ℚ) : ℚ :=
  s ^ 43
    - 58 * s ^ 42
    + 1650 * s ^ 41
    - 30732 * s ^ 40
    + 421180 * s ^ 39
    - 4516936 * s ^ 38
    + 39306742 * s ^ 37
    - 283873551 * s ^ 36
    + 1725851999 * s ^ 35
    - 8909643179 * s ^ 34
    + 39224827145 * s ^ 33
    - 147310978498 * s ^ 32
    + 470074902166 * s ^ 31
    - 1263082416569 * s ^ 30
    + 2812857104162 * s ^ 29
    - 5059194452099 * s ^ 28
    + 7057453376449 * s ^ 27
    - 7291409976541 * s ^ 26
    + 6431235336206 * s ^ 25
    - 12075866568212 * s ^ 24
    + 39998524302482 * s ^ 23
    - 105119403542546 * s ^ 22
    + 205877327361018 * s ^ 21
    - 319251934500545 * s ^ 20
    + 416666405042266 * s ^ 19
    - 483700156232933 * s ^ 18
    + 518741035550076 * s ^ 17
    - 516062759694249 * s ^ 16
    + 462512479889314 * s ^ 15
    - 355719037229150 * s ^ 14
    + 219231026884236 * s ^ 13
    - 93347782665541 * s ^ 12
    + 9759616093171 * s ^ 11
    + 25503861581269 * s ^ 10
    - 27867751749394 * s ^ 9
    + 17716143176200 * s ^ 8
    - 8039941331265 * s ^ 7
    + 2686060865458 * s ^ 6
    - 644137401667 * s ^ 5
    + 102710688487 * s ^ 4
    - 9062645671 * s ^ 3
    + 220819261 * s ^ 2
    + 6068398 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient29 (s : ℚ) : ℚ :=
  s ^ 41
    - 74 * s ^ 40
    + 2492 * s ^ 39
    - 51961 * s ^ 38
    + 762880 * s ^ 37
    - 8462001 * s ^ 36
    + 74066789 * s ^ 35
    - 526195266 * s ^ 34
    + 3089181757 * s ^ 33
    - 15139626879 * s ^ 32
    + 62142015776 * s ^ 31
    - 212802555966 * s ^ 30
    + 599878531645 * s ^ 29
    - 1349277364243 * s ^ 28
    + 2235332192280 * s ^ 27
    - 1956604247245 * s ^ 26
    - 2525646517437 * s ^ 25
    + 15350235616088 * s ^ 24
    - 38941298585355 * s ^ 23
    + 70830289508353 * s ^ 22
    - 104450418764158 * s ^ 21
    + 135106062112273 * s ^ 20
    - 164355301718137 * s ^ 19
    + 194918571289674 * s ^ 18
    - 220307011616980 * s ^ 17
    + 223604088381683 * s ^ 16
    - 190776590444293 * s ^ 15
    + 125622245903134 * s ^ 14
    - 50436680850346 * s ^ 13
    - 8504947657319 * s ^ 12
    + 37272528264839 * s ^ 11
    - 39271713559756 * s ^ 10
    + 27699602402142 * s ^ 9
    - 14717817650919 * s ^ 8
    + 6030151790067 * s ^ 7
    - 1880407154291 * s ^ 6
    + 427517232724 * s ^ 5
    - 64860086213 * s ^ 4
    + 5342592598 * s ^ 3
    - 93543312 * s ^ 2
    - 5195044 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient30 (s : ℚ) : ℚ :=
  -s ^ 40
    + 60 * s ^ 39
    - 1744 * s ^ 38
    + 32813 * s ^ 37
    - 450304 * s ^ 36
    + 4810337 * s ^ 35
    - 41614075 * s ^ 34
    + 298835953 * s ^ 33
    - 1808110215 * s ^ 32
    + 9292679913 * s ^ 31
    - 40707416072 * s ^ 30
    + 152029804941 * s ^ 29
    - 483111647342 * s ^ 28
    + 1301560263546 * s ^ 27
    - 2958945255624 * s ^ 26
    + 5650188316808 * s ^ 25
    - 9055994850707 * s ^ 24
    + 12366141456664 * s ^ 23
    - 15261814468886 * s ^ 22
    + 19374388693108 * s ^ 21
    - 28143582943327 * s ^ 20
    + 43492923010517 * s ^ 19
    - 61504867924090 * s ^ 18
    + 72259725947250 * s ^ 17
    - 65998185855641 * s ^ 16
    + 40977028314123 * s ^ 15
    - 5926485388051 * s ^ 14
    - 25185080223097 * s ^ 13
    + 41776130843185 * s ^ 12
    - 42053524999731 * s ^ 11
    + 31846353465159 * s ^ 10
    - 19127868878865 * s ^ 9
    + 9218260232689 * s ^ 8
    - 3531053252875 * s ^ 7
    + 1045531653136 * s ^ 6
    - 227085199872 * s ^ 5
    + 32741719307 * s ^ 4
    - 2460885430 * s ^ 3
    + 15707579 * s ^ 2
    + 3578861 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient31 (s : ℚ) : ℚ :=
  8 * s ^ 37
    - 495 * s ^ 36
    + 14554 * s ^ 35
    - 270420 * s ^ 34
    + 3561461 * s ^ 33
    - 35341967 * s ^ 32
    + 274180308 * s ^ 31
    - 1702447703 * s ^ 30
    + 8588082292 * s ^ 29
    - 35499364634 * s ^ 28
    + 120572225788 * s ^ 27
    - 335150062869 * s ^ 26
    + 751372512629 * s ^ 25
    - 1308745634035 * s ^ 24
    + 1586758289878 * s ^ 23
    - 694514871342 * s ^ 22
    - 2343218002963 * s ^ 21
    + 7588329542200 * s ^ 20
    - 13236188033225 * s ^ 19
    + 15856706302160 * s ^ 18
    - 12247939547873 * s ^ 17
    + 1772897369317 * s ^ 16
    + 12656835063838 * s ^ 15
    - 25845801878573 * s ^ 14
    + 33079886952727 * s ^ 13
    - 32594346554671 * s ^ 12
    + 26127482202060 * s ^ 11
    - 17350355672292 * s ^ 10
    + 9564653082328 * s ^ 9
    - 4337130661650 * s ^ 8
    + 1584838661079 * s ^ 7
    - 450430396413 * s ^ 6
    + 93765910991 * s ^ 5
    - 12744660333 * s ^ 4
    + 829060732 * s ^ 3
    + 12323112 * s ^ 2
    - 1936004 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient32 (s : ℚ) : ℚ :=
  -4 * s ^ 36
    + 240 * s ^ 35
    - 6869 * s ^ 34
    + 124754 * s ^ 33
    - 1613547 * s ^ 32
    + 15810778 * s ^ 31
    - 121911556 * s ^ 30
    + 758421897 * s ^ 29
    - 3872270879 * s ^ 28
    + 16417216442 * s ^ 27
    - 58246620173 * s ^ 26
    + 173693146975 * s ^ 25
    - 435798111448 * s ^ 24
    + 917031632252 * s ^ 23
    - 1601749712192 * s ^ 22
    + 2262546656596 * s ^ 21
    - 2401271786953 * s ^ 20
    + 1377522106679 * s ^ 19
    + 1264878901373 * s ^ 18
    - 5438945967857 * s ^ 17
    + 10355796594996 * s ^ 16
    - 14704659531284 * s ^ 15
    + 17151158266196 * s ^ 14
    - 16956584810153 * s ^ 13
    + 14361334935409 * s ^ 12
    - 10435478430611 * s ^ 11
    + 6477915505147 * s ^ 10
    - 3401295131300 * s ^ 9
    + 1485089951179 * s ^ 8
    - 525038641508 * s ^ 7
    + 144198394991 * s ^ 6
    - 28701943771 * s ^ 5
    + 3593453756 * s ^ 4
    - 172905129 * s ^ 3
    - 12512832 * s ^ 2
    + 788406 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient33 (s : ℚ) : ℚ :=
  s ^ 35
    - 58 * s ^ 34
    + 1611 * s ^ 33
    - 28510 * s ^ 32
    + 360851 * s ^ 31
    - 3476550 * s ^ 30
    + 26498390 * s ^ 29
    - 163993974 * s ^ 28
    + 839536893 * s ^ 27
    - 3605185124 * s ^ 26
    + 13132221364 * s ^ 25
    - 40968220194 * s ^ 24
    + 110460994787 * s ^ 23
    - 259856983467 * s ^ 22
    + 538937427424 * s ^ 21
    - 996582136297 * s ^ 20
    + 1661285988492 * s ^ 19
    - 2517995183835 * s ^ 18
    + 3483104431948 * s ^ 17
    - 4387990897675 * s ^ 16
    + 5000691077108 * s ^ 15
    - 5110040835478 * s ^ 14
    + 4641002255806 * s ^ 13
    - 3715379236056 * s ^ 12
    + 2599204370897 * s ^ 11
    - 1571746815453 * s ^ 10
    + 809066401312 * s ^ 9
    - 346843584283 * s ^ 8
    + 119965586057 * s ^ 7
    - 31888224710 * s ^ 6
    + 5977655327 * s ^ 5
    - 642029624 * s ^ 4
    + 6342088 * s ^ 3
    + 5903240 * s ^ 2
    - 222308 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient34 (s : ℚ) : ℚ :=
  s ^ 32
    - 55 * s ^ 31
    + 1447 * s ^ 30
    - 24238 * s ^ 29
    + 290239 * s ^ 28
    - 2644530 * s ^ 27
    + 19054705 * s ^ 26
    - 111399390 * s ^ 25
    + 538048897 * s ^ 24
    - 2175192380 * s ^ 23
    + 7432442367 * s ^ 22
    - 21623908612 * s ^ 21
    + 53879166482 * s ^ 20
    - 115518520922 * s ^ 19
    + 214005613474 * s ^ 18
    - 343897633516 * s ^ 17
    + 481197257139 * s ^ 16
    - 588438361263 * s ^ 15
    + 630763063265 * s ^ 14
    - 593448145679 * s ^ 13
    + 489170508708 * s ^ 12
    - 351032204843 * s ^ 11
    + 216718092100 * s ^ 10
    - 113043661591 * s ^ 9
    + 48552177885 * s ^ 8
    - 16534440964 * s ^ 7
    + 4194227091 * s ^ 6
    - 693597061 * s ^ 5
    + 43229304 * s ^ 4
    + 8184356 * s ^ 3
    - 1656656 * s ^ 2
    + 34240 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient35 (s : ℚ) : ℚ :=
  -s ^ 28
    + 49 * s ^ 27
    - 1140 * s ^ 26
    + 16756 * s ^ 25
    - 174652 * s ^ 24
    + 1373679 * s ^ 23
    - 8469904 * s ^ 22
    + 41987568 * s ^ 21
    - 170283477 * s ^ 20
    + 571916557 * s ^ 19
    - 1604304123 * s ^ 18
    + 3780017307 * s ^ 17
    - 7506245609 * s ^ 16
    + 12580309405 * s ^ 15
    - 17788230096 * s ^ 14
    + 21173527579 * s ^ 13
    - 21127069369 * s ^ 12
    + 17551671087 * s ^ 11
    - 12012883784 * s ^ 10
    + 6660967219 * s ^ 9
    - 2908044297 * s ^ 8
    + 946298762 * s ^ 7
    - 200359408 * s ^ 6
    + 13145220 * s ^ 5
    + 6917976 * s ^ 4
    - 2337096 * s ^ 3
    + 252864 * s ^ 2
    + 928 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient36 (s : ℚ) : ℚ :=
  -s ^ 20
    + 36 * s ^ 19
    - 603 * s ^ 18
    + 6240 * s ^ 17
    - 44675 * s ^ 16
    + 234832 * s ^ 15
    - 938585 * s ^ 14
    + 2914565 * s ^ 13
    - 7123524 * s ^ 12
    + 13797547 * s ^ 11
    - 21218228 * s ^ 10
    + 25840039 * s ^ 9
    - 24743546 * s ^ 8
    + 18399217 * s ^ 7
    - 10411640 * s ^ 6
    + 4331686 * s ^ 5
    - 1239872 * s ^ 4
    + 208832 * s ^ 3
    - 10880 * s ^ 2
    - 1440 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient37 (s : ℚ) : ℚ :=
  s ^ 11
    - 20 * s ^ 10
    + 175 * s ^ 9
    - 880 * s ^ 8
    + 2808 * s ^ 7
    - 5920 * s ^ 6
    + 8316 * s ^ 5
    - 7648 * s ^ 4
    + 4384 * s ^ 3
    - 1408 * s ^ 2
    + 192 * s

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def termThree (r s : ℚ) : ℚ :=
  termThreeCoefficient0 s +
    termThreeCoefficient1 s * r +
    termThreeCoefficient2 s * r ^ 2 +
    termThreeCoefficient3 s * r ^ 3 +
    termThreeCoefficient4 s * r ^ 4 +
    termThreeCoefficient5 s * r ^ 5 +
    termThreeCoefficient6 s * r ^ 6 +
    termThreeCoefficient7 s * r ^ 7 +
    termThreeCoefficient8 s * r ^ 8 +
    termThreeCoefficient9 s * r ^ 9 +
    termThreeCoefficient10 s * r ^ 10 +
    termThreeCoefficient11 s * r ^ 11 +
    termThreeCoefficient12 s * r ^ 12 +
    termThreeCoefficient13 s * r ^ 13 +
    termThreeCoefficient14 s * r ^ 14 +
    termThreeCoefficient15 s * r ^ 15 +
    termThreeCoefficient16 s * r ^ 16 +
    termThreeCoefficient17 s * r ^ 17 +
    termThreeCoefficient18 s * r ^ 18 +
    termThreeCoefficient19 s * r ^ 19 +
    termThreeCoefficient20 s * r ^ 20 +
    termThreeCoefficient21 s * r ^ 21 +
    termThreeCoefficient22 s * r ^ 22 +
    termThreeCoefficient23 s * r ^ 23 +
    termThreeCoefficient24 s * r ^ 24 +
    termThreeCoefficient25 s * r ^ 25 +
    termThreeCoefficient26 s * r ^ 26 +
    termThreeCoefficient27 s * r ^ 27 +
    termThreeCoefficient28 s * r ^ 28 +
    termThreeCoefficient29 s * r ^ 29 +
    termThreeCoefficient30 s * r ^ 30 +
    termThreeCoefficient31 s * r ^ 31 +
    termThreeCoefficient32 s * r ^ 32 +
    termThreeCoefficient33 s * r ^ 33 +
    termThreeCoefficient34 s * r ^ 34 +
    termThreeCoefficient35 s * r ^ 35 +
    termThreeCoefficient36 s * r ^ 36 +
    termThreeCoefficient37 s * r ^ 37

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_0 (s : ℚ) :
    termThreeCoefficient0 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient0,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_1 (s : ℚ) :
    termThreeCoefficient1 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient1,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_2 (s : ℚ) :
    termThreeCoefficient2 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient2,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_3 (s : ℚ) :
    termThreeCoefficient3 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient3,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_4 (s : ℚ) :
    termThreeCoefficient4 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient4,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_5 (s : ℚ) :
    termThreeCoefficient5 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient5,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_6 (s : ℚ) :
    termThreeCoefficient6 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient6,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_7 (s : ℚ) :
    termThreeCoefficient7 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient7,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_8 (s : ℚ) :
    termThreeCoefficient8 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient8,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_9 (s : ℚ) :
    termThreeCoefficient9 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient9,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_10 (s : ℚ) :
    termThreeCoefficient10 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient10,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_11 (s : ℚ) :
    termThreeCoefficient11 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient11,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_12 (s : ℚ) :
    termThreeCoefficient12 s =
      t3Step2Coefficient0 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient12,
    t3Step2Coefficient0,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_13 (s : ℚ) :
    termThreeCoefficient13 s =
      t3Step2Coefficient1 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient13,
    t3Step2Coefficient1,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_14 (s : ℚ) :
    termThreeCoefficient14 s =
      t3Step2Coefficient2 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient14,
    t3Step2Coefficient2,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_15 (s : ℚ) :
    termThreeCoefficient15 s =
      t3Step2Coefficient3 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient15,
    t3Step2Coefficient3,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_16 (s : ℚ) :
    termThreeCoefficient16 s =
      t3Step2Coefficient4 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient16,
    t3Step2Coefficient4,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_17 (s : ℚ) :
    termThreeCoefficient17 s =
      t3Step2Coefficient5 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient17,
    t3Step2Coefficient5,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_18 (s : ℚ) :
    termThreeCoefficient18 s =
      t3Step2Coefficient6 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient18,
    t3Step2Coefficient6,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_19 (s : ℚ) :
    termThreeCoefficient19 s =
      t3Step2Coefficient7 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient19,
    t3Step2Coefficient7,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_20 (s : ℚ) :
    termThreeCoefficient20 s =
      t3Step2Coefficient8 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient20,
    t3Step2Coefficient8,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_21 (s : ℚ) :
    termThreeCoefficient21 s =
      t3Step2Coefficient9 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient21,
    t3Step2Coefficient9,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_22 (s : ℚ) :
    termThreeCoefficient22 s =
      t3Step2Coefficient10 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient22,
    t3Step2Coefficient10,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_23 (s : ℚ) :
    termThreeCoefficient23 s =
      t3Step2Coefficient11 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient23,
    t3Step2Coefficient11,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_24 (s : ℚ) :
    termThreeCoefficient24 s =
      t3Step2Coefficient12 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient24,
    t3Step2Coefficient12,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_25 (s : ℚ) :
    termThreeCoefficient25 s =
      t3Step2Coefficient13 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient1 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient0 s := by
  simp only [termThreeCoefficient25,
    t3Step2Coefficient13,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient1,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_26 (s : ℚ) :
    termThreeCoefficient26 s =
      t3Step2Coefficient14 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient2 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient1 s := by
  simp only [termThreeCoefficient26,
    t3Step2Coefficient14,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient2,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_27 (s : ℚ) :
    termThreeCoefficient27 s =
      t3Step2Coefficient15 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient3 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient2 s := by
  simp only [termThreeCoefficient27,
    t3Step2Coefficient15,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient3,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_28 (s : ℚ) :
    termThreeCoefficient28 s =
      t3Step2Coefficient16 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient4 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient3 s := by
  simp only [termThreeCoefficient28,
    t3Step2Coefficient16,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient4,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_29 (s : ℚ) :
    termThreeCoefficient29 s =
      t3Step2Coefficient17 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient5 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient4 s := by
  simp only [termThreeCoefficient29,
    t3Step2Coefficient17,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient5,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_30 (s : ℚ) :
    termThreeCoefficient30 s =
      t3Step2Coefficient18 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient6 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient5 s := by
  simp only [termThreeCoefficient30,
    t3Step2Coefficient18,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient6,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_31 (s : ℚ) :
    termThreeCoefficient31 s =
      t3Step2Coefficient19 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient7 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient6 s := by
  simp only [termThreeCoefficient31,
    t3Step2Coefficient19,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient7,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_32 (s : ℚ) :
    termThreeCoefficient32 s =
      t3Step2Coefficient20 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient8 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient7 s := by
  simp only [termThreeCoefficient32,
    t3Step2Coefficient20,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient8,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_33 (s : ℚ) :
    termThreeCoefficient33 s =
      t3Step2Coefficient21 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient9 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient8 s := by
  simp only [termThreeCoefficient33,
    t3Step2Coefficient21,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient9,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient8]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_34 (s : ℚ) :
    termThreeCoefficient34 s =
      t3Step2Coefficient22 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient10 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient9 s := by
  simp only [termThreeCoefficient34,
    t3Step2Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient10,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient9]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_35 (s : ℚ) :
    termThreeCoefficient35 s =
      t3Step2Coefficient23 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient11 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient10 s := by
  simp only [termThreeCoefficient35,
    t3Step2Coefficient23,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient11,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient10]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_36 (s : ℚ) :
    termThreeCoefficient36 s =
      t3Step2Coefficient24 s *
          rawUnitNineDenominatorCoefficient12 s +
        t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient11 s := by
  simp only [termThreeCoefficient36,
    t3Step2Coefficient24,
    rawUnitNineDenominatorCoefficient12,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient11]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem termThreeCoefficient_product_certificate_37 (s : ℚ) :
    termThreeCoefficient37 s =
      t3Step2Coefficient25 s *
          rawUnitNineDenominatorCoefficient12 s := by
  simp only [termThreeCoefficient37,
    t3Step2Coefficient25,
    rawUnitNineDenominatorCoefficient12]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termThree_eq_t3Step2_mul_rawUnitNineDenominator (r s : ℚ) :
    termThree r s =
      t3Step2 r s * rawUnitNineDenominator r s := by
  have h0 := termThreeCoefficient_product_certificate_0 s
  have h1 := termThreeCoefficient_product_certificate_1 s
  have h2 := termThreeCoefficient_product_certificate_2 s
  have h3 := termThreeCoefficient_product_certificate_3 s
  have h4 := termThreeCoefficient_product_certificate_4 s
  have h5 := termThreeCoefficient_product_certificate_5 s
  have h6 := termThreeCoefficient_product_certificate_6 s
  have h7 := termThreeCoefficient_product_certificate_7 s
  have h8 := termThreeCoefficient_product_certificate_8 s
  have h9 := termThreeCoefficient_product_certificate_9 s
  have h10 := termThreeCoefficient_product_certificate_10 s
  have h11 := termThreeCoefficient_product_certificate_11 s
  have h12 := termThreeCoefficient_product_certificate_12 s
  have h13 := termThreeCoefficient_product_certificate_13 s
  have h14 := termThreeCoefficient_product_certificate_14 s
  have h15 := termThreeCoefficient_product_certificate_15 s
  have h16 := termThreeCoefficient_product_certificate_16 s
  have h17 := termThreeCoefficient_product_certificate_17 s
  have h18 := termThreeCoefficient_product_certificate_18 s
  have h19 := termThreeCoefficient_product_certificate_19 s
  have h20 := termThreeCoefficient_product_certificate_20 s
  have h21 := termThreeCoefficient_product_certificate_21 s
  have h22 := termThreeCoefficient_product_certificate_22 s
  have h23 := termThreeCoefficient_product_certificate_23 s
  have h24 := termThreeCoefficient_product_certificate_24 s
  have h25 := termThreeCoefficient_product_certificate_25 s
  have h26 := termThreeCoefficient_product_certificate_26 s
  have h27 := termThreeCoefficient_product_certificate_27 s
  have h28 := termThreeCoefficient_product_certificate_28 s
  have h29 := termThreeCoefficient_product_certificate_29 s
  have h30 := termThreeCoefficient_product_certificate_30 s
  have h31 := termThreeCoefficient_product_certificate_31 s
  have h32 := termThreeCoefficient_product_certificate_32 s
  have h33 := termThreeCoefficient_product_certificate_33 s
  have h34 := termThreeCoefficient_product_certificate_34 s
  have h35 := termThreeCoefficient_product_certificate_35 s
  have h36 := termThreeCoefficient_product_certificate_36 s
  have h37 := termThreeCoefficient_product_certificate_37 s
  simp only [termThree, t3Step2, rawUnitNineDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 +
    r ^ 32 * h32 + r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 +
    r ^ 36 * h36 + r ^ 37 * h37

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 34
    + s ^ 33
    - s ^ 32
    + s ^ 31

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient1 (s : ℚ) : ℚ :=
  s ^ 40
    - 4 * s ^ 39
    + 10 * s ^ 38
    - 20 * s ^ 37
    + 35 * s ^ 36
    - 58 * s ^ 35
    + 74 * s ^ 34
    - 20 * s ^ 33
    - 13 * s ^ 32
    + 46 * s ^ 31
    - 73 * s ^ 30
    + 30 * s ^ 29
    - 10 * s ^ 28
    + 2 * s ^ 27

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 42
    + 8 * s ^ 41
    - 22 * s ^ 40
    - 17 * s ^ 39
    + 195 * s ^ 38
    - 619 * s ^ 37
    + 1430 * s ^ 36
    - 2862 * s ^ 35
    + 5276 * s ^ 34
    - 7986 * s ^ 33
    + 8658 * s ^ 32
    - 8578 * s ^ 31
    + 7364 * s ^ 30
    - 5310 * s ^ 29
    + 4744 * s ^ 28
    - 4257 * s ^ 27
    + 3520 * s ^ 26
    - 2595 * s ^ 25
    + 1689 * s ^ 24
    - 980 * s ^ 23
    + 506 * s ^ 22
    - 230 * s ^ 21
    + 90 * s ^ 20
    - 29 * s ^ 19
    + 7 * s ^ 18
    - s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient3 (s : ℚ) : ℚ :=
  s ^ 45
    - 10 * s ^ 44
    + 56 * s ^ 43
    - 241 * s ^ 42
    + 923 * s ^ 41
    - 3072 * s ^ 40
    + 8129 * s ^ 39
    - 16524 * s ^ 38
    + 28093 * s ^ 37
    - 41943 * s ^ 36
    + 54674 * s ^ 35
    - 54940 * s ^ 34
    + 20831 * s ^ 33
    + 47146 * s ^ 32
    - 106887 * s ^ 31
    + 159006 * s ^ 30
    - 184353 * s ^ 29
    + 174855 * s ^ 28
    - 171446 * s ^ 27
    + 169167 * s ^ 26
    - 159178 * s ^ 25
    + 137796 * s ^ 24
    - 108041 * s ^ 23
    + 76736 * s ^ 22
    - 49428 * s ^ 21
    + 28832 * s ^ 20
    - 15148 * s ^ 19
    + 7090 * s ^ 18
    - 2903 * s ^ 17
    + 1014 * s ^ 16
    - 292 * s ^ 15
    + 67 * s ^ 14
    - 11 * s ^ 13
    + s ^ 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 47
    + 14 * s ^ 46
    - 97 * s ^ 45
    + 429 * s ^ 44
    - 1410 * s ^ 43
    + 3651 * s ^ 42
    - 6803 * s ^ 41
    + 3487 * s ^ 40
    + 33512 * s ^ 39
    - 155311 * s ^ 38
    + 419100 * s ^ 37
    - 899904 * s ^ 36
    + 1701863 * s ^ 35
    - 2915941 * s ^ 34
    + 4434574 * s ^ 33
    - 5777361 * s ^ 32
    + 6575921 * s ^ 31
    - 7018643 * s ^ 30
    + 7019955 * s ^ 29
    - 6818701 * s ^ 28
    + 6689645 * s ^ 27
    - 6226602 * s ^ 26
    + 5321645 * s ^ 25
    - 4120892 * s ^ 24
    + 2879280 * s ^ 23
    - 1813688 * s ^ 22
    + 1021946 * s ^ 21
    - 504266 * s ^ 20
    + 207116 * s ^ 19
    - 60878 * s ^ 18
    + 3278 * s ^ 17
    + 10936 * s ^ 16
    - 9227 * s ^ 15
    + 4768 * s ^ 14
    - 1823 * s ^ 13
    + 522 * s ^ 12
    - 107 * s ^ 11
    + 14 * s ^ 10
    - s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient5 (s : ℚ) : ℚ :=
  s ^ 48
    - 22 * s ^ 47
    + 260 * s ^ 46
    - 1970 * s ^ 45
    + 10658 * s ^ 44
    - 44661 * s ^ 43
    + 155218 * s ^ 42
    - 465583 * s ^ 41
    + 1216314 * s ^ 40
    - 2743353 * s ^ 39
    + 5340495 * s ^ 38
    - 9219706 * s ^ 37
    + 14685521 * s ^ 36
    - 21769345 * s ^ 35
    + 29337142 * s ^ 34
    - 34670972 * s ^ 33
    + 35835222 * s ^ 32
    - 35462462 * s ^ 31
    + 37071242 * s ^ 30
    - 39666489 * s ^ 29
    + 43609168 * s ^ 28
    - 45484531 * s ^ 27
    + 39693446 * s ^ 26
    - 28215174 * s ^ 25
    + 15358696 * s ^ 24
    - 4719277 * s ^ 23
    - 2130333 * s ^ 22
    + 5416669 * s ^ 21
    - 6125777 * s ^ 20
    + 5339926 * s ^ 19
    - 3940602 * s ^ 18
    + 2520098 * s ^ 17
    - 1395476 * s ^ 16
    + 661267 * s ^ 15
    - 263298 * s ^ 14
    + 86135 * s ^ 13
    - 22123 * s ^ 12
    + 4129 * s ^ 11
    - 476 * s ^ 10
    + 21 * s ^ 9
    + 2 * s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 50
    + 20 * s ^ 49
    - 208 * s ^ 48
    + 1462 * s ^ 47
    - 7632 * s ^ 46
    + 30818 * s ^ 45
    - 99037 * s ^ 44
    + 259517 * s ^ 43
    - 556527 * s ^ 42
    + 905660 * s ^ 41
    - 723670 * s ^ 40
    - 1565231 * s ^ 39
    + 8221051 * s ^ 38
    - 20608627 * s ^ 37
    + 39331164 * s ^ 36
    - 68094145 * s ^ 35
    + 113013335 * s ^ 34
    - 171348759 * s ^ 33
    + 217530524 * s ^ 32
    - 219291915 * s ^ 31
    + 183897994 * s ^ 30
    - 147887215 * s ^ 29
    + 134864562 * s ^ 28
    - 182669738 * s ^ 27
    + 289435425 * s ^ 26
    - 391874284 * s ^ 25
    + 446968555 * s ^ 24
    - 444063528 * s ^ 23
    + 396084124 * s ^ 22
    - 323959663 * s ^ 21
    + 245156141 * s ^ 20
    - 171480616 * s ^ 19
    + 109932306 * s ^ 18
    - 63678029 * s ^ 17
    + 32722230 * s ^ 16
    - 14603354 * s ^ 15
    + 5521552 * s ^ 14
    - 1713402 * s ^ 13
    + 412175 * s ^ 12
    - 69095 * s ^ 11
    + 5977 * s ^ 10
    + 173 * s ^ 9
    - 88 * s ^ 8
    - s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient7 (s : ℚ) : ℚ :=
  -2 * s ^ 50
    + 60 * s ^ 49
    - 798 * s ^ 48
    + 6778 * s ^ 47
    - 42032 * s ^ 46
    + 202913 * s ^ 45
    - 792689 * s ^ 44
    + 2592975 * s ^ 43
    - 7337886 * s ^ 42
    + 18344954 * s ^ 41
    - 40437669 * s ^ 40
    + 77145325 * s ^ 39
    - 125973966 * s ^ 38
    + 181972243 * s ^ 37
    - 255813485 * s ^ 36
    + 375209742 * s ^ 35
    - 535976492 * s ^ 34
    + 663736640 * s ^ 33
    - 690958449 * s ^ 32
    + 747973266 * s ^ 31
    - 1164524225 * s ^ 30
    + 2130420972 * s ^ 29
    - 3594278792 * s ^ 28
    + 5383074931 * s ^ 27
    - 6954134936 * s ^ 26
    + 7751838213 * s ^ 25
    - 7707710968 * s ^ 24
    + 7021795534 * s ^ 23
    - 5964633098 * s ^ 22
    + 4759111730 * s ^ 21
    - 3556465106 * s ^ 20
    + 2465167022 * s ^ 19
    - 1563062906 * s ^ 18
    + 891511756 * s ^ 17
    - 448790403 * s ^ 16
    + 195140963 * s ^ 15
    - 71366753 * s ^ 14
    + 21119615 * s ^ 13
    - 4697343 * s ^ 12
    + 663463 * s ^ 11
    - 22643 * s ^ 10
    - 10004 * s ^ 9
    + 1474 * s ^ 8
    + 77 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 51
    + 23 * s ^ 50
    - 233 * s ^ 49
    + 1249 * s ^ 48
    - 2421 * s ^ 47
    - 18469 * s ^ 46
    + 210086 * s ^ 45
    - 1196561 * s ^ 44
    + 4901094 * s ^ 43
    - 16163815 * s ^ 42
    + 45949426 * s ^ 41
    - 116128553 * s ^ 40
    + 256404969 * s ^ 39
    - 468467979 * s ^ 38
    + 655904538 * s ^ 37
    - 615996690 * s ^ 36
    + 189567786 * s ^ 35
    + 649484915 * s ^ 34
    - 2158759995 * s ^ 33
    + 5430715746 * s ^ 32
    - 12254087783 * s ^ 31
    + 23559366146 * s ^ 30
    - 38196269313 * s ^ 29
    + 53855702461 * s ^ 28
    - 67551679869 * s ^ 27
    + 75678143165 * s ^ 26
    - 77059432043 * s ^ 25
    + 73346784879 * s ^ 24
    - 66291030682 * s ^ 23
    + 57076599871 * s ^ 22
    - 46491127246 * s ^ 21
    + 35360844998 * s ^ 20
    - 24743745369 * s ^ 19
    + 15684784208 * s ^ 18
    - 8859484071 * s ^ 17
    + 4378371511 * s ^ 16
    - 1852168538 * s ^ 15
    + 650892625 * s ^ 14
    - 180775318 * s ^ 13
    + 35599851 * s ^ 12
    - 3463734 * s ^ 11
    - 377333 * s ^ 10
    + 161367 * s ^ 9
    - 13099 * s ^ 8
    - 1796 * s ^ 7
    - 5 * s ^ 6
    + 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient9 (s : ℚ) : ℚ :=
  -2 * s ^ 51
    + 65 * s ^ 50
    - 944 * s ^ 49
    + 8327 * s ^ 48
    - 50334 * s ^ 47
    + 219282 * s ^ 46
    - 681264 * s ^ 45
    + 1321253 * s ^ 44
    - 193385 * s ^ 43
    - 10767231 * s ^ 42
    + 58349568 * s ^ 41
    - 229586585 * s ^ 40
    + 773877488 * s ^ 39
    - 2227574236 * s ^ 38
    + 5359566688 * s ^ 37
    - 10838600033 * s ^ 36
    + 19288344751 * s ^ 35
    - 32734137116 * s ^ 34
    + 56422721272 * s ^ 33
    - 97566119091 * s ^ 32
    + 159662618151 * s ^ 31
    - 237388605206 * s ^ 30
    + 319481075281 * s ^ 29
    - 394679943993 * s ^ 28
    + 451286881634 * s ^ 27
    - 481557892049 * s ^ 26
    + 490222833054 * s ^ 25
    - 483725244734 * s ^ 24
    + 460157080394 * s ^ 23
    - 415652933167 * s ^ 22
    + 350482579544 * s ^ 21
    - 271672671914 * s ^ 20
    + 191021408414 * s ^ 19
    - 120241313915 * s ^ 18
    + 66767355395 * s ^ 17
    - 32125397195 * s ^ 16
    + 13075592714 * s ^ 15
    - 4335064181 * s ^ 14
    + 1087013370 * s ^ 13
    - 167049891 * s ^ 12
    - 1176673 * s ^ 11
    + 7661587 * s ^ 10
    - 1585086 * s ^ 9
    + 56505 * s ^ 8
    + 22796 * s ^ 7
    + 751 * s ^ 6
    - 58 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient10 (s : ℚ) : ℚ :=
  -2 * s ^ 51
    + 92 * s ^ 50
    - 1779 * s ^ 49
    + 20475 * s ^ 48
    - 163035 * s ^ 47
    + 977700 * s ^ 46
    - 4666758 * s ^ 45
    + 18522640 * s ^ 44
    - 64051876 * s ^ 43
    + 203102041 * s ^ 42
    - 610149883 * s ^ 41
    + 1716984206 * s ^ 40
    - 4346138937 * s ^ 39
    + 9609025196 * s ^ 38
    - 18776911732 * s ^ 37
    + 34690036063 * s ^ 36
    - 66271385071 * s ^ 35
    + 132669148437 * s ^ 34
    - 257984056969 * s ^ 33
    + 454629838754 * s ^ 32
    - 710899598720 * s ^ 31
    + 1000898052848 * s ^ 30
    - 1306727572050 * s ^ 29
    + 1617503294266 * s ^ 28
    - 1917339544137 * s ^ 27
    + 2202522729312 * s ^ 26
    - 2471948746388 * s ^ 25
    + 2671626307951 * s ^ 24
    - 2713501630542 * s ^ 23
    + 2545475159665 * s ^ 22
    - 2180062346721 * s ^ 21
    + 1689461064031 * s ^ 20
    - 1174214712748 * s ^ 19
    + 723931204380 * s ^ 18
    - 390221839206 * s ^ 17
    + 180262615604 * s ^ 16
    - 69198227285 * s ^ 15
    + 20846012438 * s ^ 14
    - 4260468524 * s ^ 13
    + 237119292 * s ^ 12
    + 194864531 * s ^ 11
    - 74242729 * s ^ 10
    + 10411212 * s ^ 9
    + 168839 * s ^ 8
    - 190434 * s ^ 7
    - 15204 * s ^ 6
    + 718 * s ^ 5
    + 39 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 52
    + 33 * s ^ 51
    - 515 * s ^ 50
    + 4960 * s ^ 49
    - 32987 * s ^ 48
    + 163541 * s ^ 47
    - 660996 * s ^ 46
    + 2528947 * s ^ 45
    - 10749306 * s ^ 44
    + 49396349 * s ^ 43
    - 207741361 * s ^ 42
    + 716459434 * s ^ 41
    - 1966992383 * s ^ 40
    + 4470719113 * s ^ 39
    - 9741235751 * s ^ 38
    + 24816477288 * s ^ 37
    - 71644021545 * s ^ 36
    + 193138970174 * s ^ 35
    - 439704671734 * s ^ 34
    + 837730490739 * s ^ 33
    - 1378677305996 * s ^ 32
    + 2062593194673 * s ^ 31
    - 2956625380579 * s ^ 30
    + 4176490794612 * s ^ 29
    - 5790592016982 * s ^ 28
    + 7784064395041 * s ^ 27
    - 10056110891019 * s ^ 26
    + 12276341951871 * s ^ 25
    - 13847739539640 * s ^ 24
    + 14239754284632 * s ^ 23
    - 13284355918753 * s ^ 22
    + 11200807961739 * s ^ 21
    - 8490097006329 * s ^ 20
    + 5738379624013 * s ^ 19
    - 3416645242114 * s ^ 18
    + 1760727981608 * s ^ 17
    - 764338726198 * s ^ 16
    + 266104526021 * s ^ 15
    - 65972574877 * s ^ 14
    + 6445726709 * s ^ 13
    + 3289776720 * s ^ 12
    - 1919849910 * s ^ 11
    + 472648388 * s ^ 10
    - 44013655 * s ^ 9
    - 4728355 * s ^ 8
    + 1048561 * s ^ 7
    + 181319 * s ^ 6
    - 4796 * s ^ 5
    - 702 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient12 (s : ℚ) : ℚ :=
  8 * s ^ 51
    - 223 * s ^ 50
    + 2797 * s ^ 49
    - 19509 * s ^ 48
    + 66493 * s ^ 47
    + 114501 * s ^ 46
    - 2893983 * s ^ 45
    + 19238872 * s ^ 44
    - 79447576 * s ^ 43
    + 225221906 * s ^ 42
    - 470747802 * s ^ 41
    + 1113891800 * s ^ 40
    - 5118631650 * s ^ 39
    + 25557673936 * s ^ 38
    - 97283582757 * s ^ 37
    + 279871996318 * s ^ 36
    - 634863849784 * s ^ 35
    + 1196314591232 * s ^ 34
    - 2009785705963 * s ^ 33
    + 3280469415804 * s ^ 32
    - 5506465602253 * s ^ 31
    + 9383815857394 * s ^ 30
    - 15477375015022 * s ^ 29
    + 23955370639255 * s ^ 28
    - 34492436037913 * s ^ 27
    + 45933311634190 * s ^ 26
    - 55944324077652 * s ^ 25
    + 61782130581242 * s ^ 24
    - 61784795827878 * s ^ 23
    + 55964103331254 * s ^ 22
    - 45764630746194 * s ^ 21
    + 33552760367201 * s ^ 20
    - 21811211021096 * s ^ 19
    + 12362764968991 * s ^ 18
    - 5953083771806 * s ^ 17
    + 2323590862018 * s ^ 16
    - 655957568773 * s ^ 15
    + 75981979568 * s ^ 14
    + 43963215266 * s ^ 13
    - 32801673710 * s ^ 12
    + 11281689412 * s ^ 11
    - 2077652669 * s ^ 10
    + 81561743 * s ^ 9
    + 39533680 * s ^ 8
    - 3081908 * s ^ 7
    - 1488934 * s ^ 6
    + 1073 * s ^ 5
    + 9137 * s ^ 4
    - 38 * s ^ 3
    + 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient13 (s : ℚ) : ℚ :=
  6 * s ^ 51
    - 232 * s ^ 50
    + 3984 * s ^ 49
    - 40662 * s ^ 48
    + 271601 * s ^ 47
    - 1186270 * s ^ 46
    + 2799772 * s ^ 45
    + 1856097 * s ^ 44
    - 36610404 * s ^ 43
    + 37574647 * s ^ 42
    + 986578246 * s ^ 41
    - 8160532804 * s ^ 40
    + 37890874341 * s ^ 39
    - 125421148394 * s ^ 38
    + 320527737104 * s ^ 37
    - 669187047141 * s ^ 36
    + 1236295160125 * s ^ 35
    - 2281789587357 * s ^ 34
    + 4605241274415 * s ^ 33
    - 9790179149218 * s ^ 32
    + 19965081194302 * s ^ 31
    - 37102160383572 * s ^ 30
    + 62366702380336 * s ^ 29
    - 95682075550662 * s ^ 28
    + 134749488347476 * s ^ 27
    - 173581295788635 * s ^ 26
    + 203235540888690 * s ^ 25
    - 215939483330548 * s ^ 24
    + 208558816328627 * s ^ 23
    - 182805903818704 * s ^ 22
    + 144400298186106 * s ^ 21
    - 101623513784167 * s ^ 20
    + 62633913383890 * s ^ 19
    - 32898137483314 * s ^ 18
    + 13997777097764 * s ^ 17
    - 4232734155549 * s ^ 16
    + 395979545391 * s ^ 15
    + 506095927617 * s ^ 14
    - 402978889327 * s ^ 13
    + 171580075451 * s ^ 12
    - 45223032116 * s ^ 11
    + 5863447874 * s ^ 10
    + 360631631 * s ^ 9
    - 205172874 * s ^ 8
    - 3703803 * s ^ 7
    + 8529492 * s ^ 6
    + 393488 * s ^ 5
    - 93751 * s ^ 4
    + 1060 * s ^ 3
    - 28 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient14 (s : ℚ) : ℚ :=
  3 * s ^ 51
    - 153 * s ^ 50
    + 3313 * s ^ 49
    - 41360 * s ^ 48
    + 327939 * s ^ 47
    - 1578077 * s ^ 46
    + 2107845 * s ^ 45
    + 37503138 * s ^ 44
    - 403737553 * s ^ 43
    + 2445613877 * s ^ 42
    - 10693905067 * s ^ 41
    + 36039785504 * s ^ 40
    - 96498194737 * s ^ 39
    + 213061174766 * s ^ 38
    - 425589087739 * s ^ 37
    + 920012488148 * s ^ 36
    - 2388987037220 * s ^ 35
    + 6580868642629 * s ^ 34
    - 16643590262097 * s ^ 33
    + 36805992219596 * s ^ 32
    - 71536690359092 * s ^ 31
    + 124821888511363 * s ^ 30
    - 199329254398950 * s ^ 29
    + 293780564052313 * s ^ 28
    - 398384996329576 * s ^ 27
    + 493432305856909 * s ^ 26
    - 556355206848806 * s ^ 25
    + 571926352016561 * s ^ 24
    - 535939106716555 * s ^ 23
    + 454540876611521 * s ^ 22
    - 344258789718090 * s ^ 21
    + 228367562268140 * s ^ 20
    - 128568989543884 * s ^ 19
    + 57654672046066 * s ^ 18
    - 16992621782335 * s ^ 17
    - 518815569889 * s ^ 16
    + 4745341485535 * s ^ 15
    - 3689311191029 * s ^ 14
    + 1797610794695 * s ^ 13
    - 598325196892 * s ^ 12
    + 121170598522 * s ^ 11
    - 5873875482 * s ^ 10
    - 3829326125 * s ^ 9
    + 716904551 * s ^ 8
    + 89611995 * s ^ 7
    - 31478507 * s ^ 6
    - 5177086 * s ^ 5
    + 741274 * s ^ 4
    - 9861 * s ^ 3
    - 71 * s ^ 2
    + 30 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient15 (s : ℚ) : ℚ :=
  5 * s ^ 51
    - 256 * s ^ 50
    + 6281 * s ^ 49
    - 97509 * s ^ 48
    + 1074365 * s ^ 47
    - 8939626 * s ^ 46
    + 58190105 * s ^ 45
    - 301546289 * s ^ 44
    + 1249370770 * s ^ 43
    - 4116905392 * s ^ 42
    + 10730374479 * s ^ 41
    - 22995967135 * s ^ 40
    + 51402136674 * s ^ 39
    - 175140288129 * s ^ 38
    + 748200453577 * s ^ 37
    - 2839820271958 * s ^ 36
    + 8819522244353 * s ^ 35
    - 22735896622753 * s ^ 34
    + 50243488339945 * s ^ 33
    - 98480976008238 * s ^ 32
    + 176383110202029 * s ^ 31
    - 294018170549955 * s ^ 30
    + 457445797843505 * s ^ 29
    - 658491322179266 * s ^ 28
    + 867662840939312 * s ^ 27
    - 1041550637933327 * s ^ 26
    + 1141131844453118 * s ^ 25
    - 1142644294691874 * s ^ 24
    + 1038288488499054 * s ^ 23
    - 841781443647583 * s ^ 22
    + 593767416938160 * s ^ 21
    - 349498278064460 * s ^ 20
    + 155621101204743 * s ^ 19
    - 33711061285587 * s ^ 18
    - 21934401359021 * s ^ 17
    + 33559814019852 * s ^ 16
    - 25260940960022 * s ^ 15
    + 13482814437632 * s ^ 14
    - 5281487860625 * s ^ 13
    + 1400490607790 * s ^ 12
    - 167830730734 * s ^ 11
    - 35097583077 * s ^ 10
    + 17831743641 * s ^ 9
    - 1595527601 * s ^ 8
    - 461405225 * s ^ 7
    + 41395686 * s ^ 6
    + 40335419 * s ^ 5
    - 4419460 * s ^ 4
    + 29728 * s ^ 3
    + 5315 * s ^ 2
    - 436 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient16 (s : ℚ) : ℚ :=
  s ^ 52
    - 45 * s ^ 51
    + 973 * s ^ 50
    - 13286 * s ^ 49
    + 126438 * s ^ 48
    - 867418 * s ^ 47
    + 4196667 * s ^ 46
    - 12276656 * s ^ 45
    + 1204812 * s ^ 44
    + 186082856 * s ^ 43
    - 807044399 * s ^ 42
    - 554304755 * s ^ 41
    + 26594397406 * s ^ 40
    - 186830876779 * s ^ 39
    + 850505857037 * s ^ 38
    - 2961189389387 * s ^ 37
    + 8428003338924 * s ^ 36
    - 20485133966058 * s ^ 35
    + 44220862960492 * s ^ 34
    - 87969770537375 * s ^ 33
    + 165603413648254 * s ^ 32
    - 296815527562539 * s ^ 31
    + 499975323709241 * s ^ 30
    - 776392484104747 * s ^ 29
    + 1096637334658599 * s ^ 28
    - 1404973464218250 * s ^ 27
    + 1640909560412938 * s ^ 26
    - 1753839820230224 * s ^ 25
    + 1702068089862865 * s ^ 24
    - 1465174622883819 * s ^ 23
    + 1076685476599879 * s ^ 22
    - 629551256498602 * s ^ 21
    + 233508131804577 * s ^ 20
    + 35545970605077 * s ^ 19
    - 159944266467147 * s ^ 18
    + 172784236100836 * s ^ 17
    - 128532216768543 * s ^ 16
    + 73574145279532 * s ^ 15
    - 32520291605447 * s ^ 14
    + 10359236360637 * s ^ 13
    - 1801724880905 * s ^ 12
    - 196619131090 * s ^ 11
    + 220821959133 * s ^ 10
    - 54245967328 * s ^ 9
    + 1771017859 * s ^ 8
    + 1033177450 * s ^ 7
    + 339986240 * s ^ 6
    - 223436884 * s ^ 5
    + 19484631 * s ^ 4
    + 263405 * s ^ 3
    - 69161 * s ^ 2
    + 4085 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient17 (s : ℚ) : ℚ :=
  -5 * s ^ 51
    + 215 * s ^ 50
    - 4450 * s ^ 49
    + 57790 * s ^ 48
    - 508488 * s ^ 47
    + 2926545 * s ^ 46
    - 7215848 * s ^ 45
    - 56147017 * s ^ 44
    + 870392365 * s ^ 43
    - 6618907670 * s ^ 42
    + 36167837486 * s ^ 41
    - 155441859863 * s ^ 40
    + 547142586816 * s ^ 39
    - 1622827321194 * s ^ 38
    + 4182260137608 * s ^ 37
    - 9756730772124 * s ^ 36
    + 21639796263818 * s ^ 35
    - 47312040468649 * s ^ 34
    + 101815095003292 * s ^ 33
    - 208556146591812 * s ^ 32
    + 391996817170544 * s ^ 31
    - 661517323417632 * s ^ 30
    + 997288180019144 * s ^ 29
    - 1353261832123978 * s ^ 28
    + 1674501950214298 * s ^ 27
    - 1902373710956328 * s ^ 26
    + 1959285238311870 * s ^ 25
    - 1759931257067494 * s ^ 24
    + 1282929047993510 * s ^ 23
    - 631183225997584 * s ^ 22
    - 8196790840468 * s ^ 21
    + 467137583808971 * s ^ 20
    - 669257461550810 * s ^ 19
    + 642537534181492 * s ^ 18
    - 482669510804399 * s ^ 17
    + 293342274377445 * s ^ 16
    - 142395677934390 * s ^ 15
    + 51634041856049 * s ^ 14
    - 10952141737732 * s ^ 13
    - 965271561339 * s ^ 12
    + 1824043835174 * s ^ 11
    - 699206143142 * s ^ 10
    + 117079376521 * s ^ 9
    - 1616838746 * s ^ 8
    + 1874610489 * s ^ 7
    - 2970811655 * s ^ 6
    + 930010417 * s ^ 5
    - 59922510 * s ^ 4
    - 3982809 * s ^ 3
    + 543927 * s ^ 2
    - 27649 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient18 (s : ℚ) : ℚ :=
  -2 * s ^ 51
    + 120 * s ^ 50
    - 3432 * s ^ 49
    + 62806 * s ^ 48
    - 826651 * s ^ 47
    + 8307872 * s ^ 46
    - 65951206 * s ^ 45
    + 421890021 * s ^ 44
    - 2200994646 * s ^ 43
    + 9437762511 * s ^ 42
    - 33527190638 * s ^ 41
    + 100333198971 * s ^ 40
    - 264469009034 * s ^ 39
    + 677267277090 * s ^ 38
    - 1897482087355 * s ^ 37
    + 5858423042230 * s ^ 36
    - 17850831251290 * s ^ 35
    + 48843979462378 * s ^ 34
    - 115459464958321 * s ^ 33
    + 234306273510833 * s ^ 32
    - 411764164408792 * s ^ 31
    + 637974508082294 * s ^ 30
    - 893259780491245 * s ^ 29
    + 1157155474384929 * s ^ 28
    - 1392899301044024 * s ^ 27
    + 1506469579215777 * s ^ 26
    - 1345943599681504 * s ^ 25
    + 805650288626261 * s ^ 24
    + 39224880161491 * s ^ 23
    - 933620653299382 * s ^ 22
    + 1594920995349912 * s ^ 21
    - 1858838264253122 * s ^ 20
    + 1725430076827744 * s ^ 19
    - 1327727330492565 * s ^ 18
    + 851006925099295 * s ^ 17
    - 444244088869077 * s ^ 16
    + 175619519960048 * s ^ 15
    - 40042527723645 * s ^ 14
    - 6368167389414 * s ^ 13
    + 11205789092685 * s ^ 12
    - 5546920177639 * s ^ 11
    + 1500260653901 * s ^ 10
    - 202657151626 * s ^ 9
    + 26855428809 * s ^ 8
    - 26574169209 * s ^ 7
    + 13593814484 * s ^ 6
    - 2942087281 * s ^ 5
    + 96984008 * s ^ 4
    + 28248326 * s ^ 3
    - 3077173 * s ^ 2
    + 143453 * s
    + 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient19 (s : ℚ) : ℚ :=
  2 * s ^ 51
    - 95 * s ^ 50
    + 2151 * s ^ 49
    - 30401 * s ^ 48
    + 293422 * s ^ 47
    - 1960507 * s ^ 46
    + 8318653 * s ^ 45
    - 11092276 * s ^ 44
    - 131524210 * s ^ 43
    + 1150512903 * s ^ 42
    - 4549051559 * s ^ 41
    + 4711545618 * s ^ 40
    + 62704099010 * s ^ 39
    - 513179807603 * s ^ 38
    + 2393988383164 * s ^ 37
    - 8257666724875 * s ^ 36
    + 22682625431969 * s ^ 35
    - 51342997623934 * s ^ 34
    + 98029778360663 * s ^ 33
    - 162058829289924 * s ^ 32
    + 241318308737339 * s ^ 31
    - 341183135884655 * s ^ 30
    + 473819203982378 * s ^ 29
    - 624249293426377 * s ^ 28
    + 691825752547140 * s ^ 27
    - 481622235786961 * s ^ 26
    - 175416651690683 * s ^ 25
    + 1235676155951907 * s ^ 24
    - 2394666080924323 * s ^ 23
    + 3263541404451590 * s ^ 22
    - 3588787690879837 * s ^ 21
    + 3332403275973102 * s ^ 20
    - 2640985532073751 * s ^ 19
    + 1769916521719079 * s ^ 18
    - 971120290933154 * s ^ 17
    + 397444307503901 * s ^ 16
    - 79047098110009 * s ^ 15
    - 41473299302537 * s ^ 14
    + 53303643021220 * s ^ 13
    - 30452741586368 * s ^ 12
    + 10883558337753 * s ^ 11
    - 2439519801641 * s ^ 10
    + 426979197727 * s ^ 9
    - 201880240348 * s ^ 8
    + 125347855292 * s ^ 7
    - 43509461175 * s ^ 6
    + 6860297497 * s ^ 5
    + 166649155 * s ^ 4
    - 138794320 * s ^ 3
    + 13419890 * s ^ 2
    - 590726 * s
    - 276

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient20 (s : ℚ) : ℚ :=
  -8 * s ^ 50
    + 370 * s ^ 49
    - 8081 * s ^ 48
    + 108311 * s ^ 47
    - 955285 * s ^ 46
    + 5212768 * s ^ 45
    - 8133671 * s ^ 44
    - 158676169 * s ^ 43
    + 1972427350 * s ^ 42
    - 13864846228 * s ^ 41
    + 71357820918 * s ^ 40
    - 288419360871 * s ^ 39
    + 940399273028 * s ^ 38
    - 2494864862340 * s ^ 37
    + 5369342819667 * s ^ 36
    - 9261857606738 * s ^ 35
    + 12660701531012 * s ^ 34
    - 14470576221905 * s ^ 33
    + 19356932552785 * s ^ 32
    - 42672319828795 * s ^ 31
    + 100796868655913 * s ^ 30
    - 172549179738533 * s ^ 29
    + 147083702784701 * s ^ 28
    + 176136102767695 * s ^ 27
    - 968902342631060 * s ^ 26
    + 2187268702149081 * s ^ 25
    - 3506173249961221 * s ^ 24
    + 4492775238897337 * s ^ 23
    - 4857992915781775 * s ^ 22
    + 4548259739909901 * s ^ 21
    - 3692690667886742 * s ^ 20
    + 2545359923608582 * s ^ 19
    - 1412667723916902 * s ^ 18
    + 535948307734016 * s ^ 17
    - 13421163188454 * s ^ 16
    - 191902358231254 * s ^ 15
    + 195127916556884 * s ^ 14
    - 120995399021931 * s ^ 13
    + 52205968685326 * s ^ 12
    - 15782205803202 * s ^ 11
    + 3759589517500 * s ^ 10
    - 1392484945827 * s ^ 9
    + 846068375620 * s ^ 8
    - 387842318179 * s ^ 7
    + 102361542942 * s ^ 6
    - 10192252828 * s ^ 5
    - 1883588180 * s ^ 4
    + 521634167 * s ^ 3
    - 46774419 * s ^ 2
    + 1972704 * s
    + 2020

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient21 (s : ℚ) : ℚ :=
  -3 * s ^ 50
    + 177 * s ^ 49
    - 4955 * s ^ 48
    + 87739 * s ^ 47
    - 1101682 * s ^ 46
    + 10398099 * s ^ 45
    - 76118489 * s ^ 44
    + 438058234 * s ^ 43
    - 1973465077 * s ^ 42
    + 6723465475 * s ^ 41
    - 15238698292 * s ^ 40
    + 7624469049 * s ^ 39
    + 119151291401 * s ^ 38
    - 666742432119 * s ^ 37
    + 2165401979613 * s ^ 36
    - 4849430947448 * s ^ 35
    + 6952953384941 * s ^ 34
    - 2352285596224 * s ^ 33
    - 18365162891323 * s ^ 32
    + 55374520689045 * s ^ 31
    - 71254330458606 * s ^ 30
    - 37487072569883 * s ^ 29
    + 425596849401247 * s ^ 28
    - 1203364948758036 * s ^ 27
    + 2300644242473925 * s ^ 26
    - 3427392591979554 * s ^ 25
    + 4223056510939531 * s ^ 24
    - 4471469904274177 * s ^ 23
    + 4159465454410750 * s ^ 22
    - 3383574835622336 * s ^ 21
    + 2302889516749719 * s ^ 20
    - 1157784897309028 * s ^ 19
    + 209325094659329 * s ^ 18
    + 380185709725482 * s ^ 17
    - 595473534620986 * s ^ 16
    + 535972221624977 * s ^ 15
    - 352370231593376 * s ^ 14
    + 174996576275312 * s ^ 13
    - 65626635543645 * s ^ 12
    + 20174076217453 * s ^ 11
    - 7664278065695 * s ^ 10
    + 4479785201167 * s ^ 9
    - 2403678225038 * s ^ 8
    + 867855023560 * s ^ 7
    - 170514204382 * s ^ 6
    + 1152744600 * s ^ 5
    + 7932910816 * s ^ 4
    - 1565346674 * s ^ 3
    + 133070539 * s ^ 2
    - 5414610 * s
    - 10542

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient22 (s : ℚ) : ℚ :=
  10 * s ^ 49
    - 544 * s ^ 48
    + 14314 * s ^ 47
    - 241824 * s ^ 46
    + 2935536 * s ^ 45
    - 27142076 * s ^ 44
    + 197574580 * s ^ 43
    - 1152661574 * s ^ 42
    + 5418789519 * s ^ 41
    - 20324195373 * s ^ 40
    + 58408802000 * s ^ 39
    - 111385821273 * s ^ 38
    + 29312085895 * s ^ 37
    + 791909532520 * s ^ 36
    - 3841599613870 * s ^ 35
    + 11276766107071 * s ^ 34
    - 23033754429377 * s ^ 33
    + 28701751755892 * s ^ 32
    + 5113151254244 * s ^ 31
    - 141718204317602 * s ^ 30
    + 455380910955486 * s ^ 29
    - 974384834792896 * s ^ 28
    + 1615374374618162 * s ^ 27
    - 2183845082476088 * s ^ 26
    + 2483824547323935 * s ^ 25
    - 2448426390173352 * s ^ 24
    + 2136986854057786 * s ^ 23
    - 1611483794683465 * s ^ 22
    + 895068368377271 * s ^ 21
    - 73418810519998 * s ^ 20
    - 661725996627949 * s ^ 19
    + 1124496665428609 * s ^ 18
    - 1244988860023759 * s ^ 17
    + 1075712445185942 * s ^ 16
    - 749232543527255 * s ^ 15
    + 418642752014812 * s ^ 14
    - 186940173813211 * s ^ 13
    + 71559277159180 * s ^ 12
    - 31070906023310 * s ^ 11
    + 18574301155031 * s ^ 10
    - 11071887134227 * s ^ 9
    + 4932314845560 * s ^ 8
    - 1397953616374 * s ^ 7
    + 156641658795 * s ^ 6
    + 46952104212 * s ^ 5
    - 23177275555 * s ^ 4
    + 3835979596 * s ^ 3
    - 312957856 * s ^ 2
    + 12311186 * s
    + 41664

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient23 (s : ℚ) : ℚ :=
  s ^ 49
    - 70 * s ^ 48
    + 2282 * s ^ 47
    - 46766 * s ^ 46
    + 681225 * s ^ 45
    - 7534108 * s ^ 44
    + 65848346 * s ^ 43
    - 466690209 * s ^ 42
    + 2727169522 * s ^ 41
    - 13267622206 * s ^ 40
    + 53891407047 * s ^ 39
    - 181637321975 * s ^ 38
    + 496342677397 * s ^ 37
    - 1026063804210 * s ^ 36
    + 1195123474190 * s ^ 35
    + 1600552597409 * s ^ 34
    - 14517830338230 * s ^ 33
    + 51628265932399 * s ^ 32
    - 132054924848759 * s ^ 31
    + 268219368222619 * s ^ 30
    - 444128163957016 * s ^ 29
    + 599777728762386 * s ^ 28
    - 650924052618630 * s ^ 27
    + 551436148929747 * s ^ 26
    - 342474564196376 * s ^ 25
    + 108295114042861 * s ^ 24
    + 135910040398324 * s ^ 23
    - 467566182846005 * s ^ 22
    + 925480615022663 * s ^ 21
    - 1401084663890821 * s ^ 20
    + 1714539805134366 * s ^ 19
    - 1759140209080360 * s ^ 18
    + 1541773060997165 * s ^ 17
    - 1150056520354069 * s ^ 16
    + 718947452132162 * s ^ 15
    - 376067759848523 * s ^ 14
    + 176476380209323 * s ^ 13
    - 91479704926562 * s ^ 12
    + 59351450168359 * s ^ 11
    - 38753912605597 * s ^ 10
    + 20164016452051 * s ^ 9
    - 7288326968760 * s ^ 8
    + 1423778220965 * s ^ 7
    + 110666175849 * s ^ 6
    - 169577283349 * s ^ 5
    + 52425613902 * s ^ 4
    - 7772979144 * s ^ 3
    + 612884863 * s ^ 2
    - 23266396 * s
    - 129282

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient24 (s : ℚ) : ℚ :=
  -2 * s ^ 48
    + 122 * s ^ 47
    - 3615 * s ^ 46
    + 69254 * s ^ 45
    - 962903 * s ^ 44
    + 10341491 * s ^ 43
    - 89175411 * s ^ 42
    + 633758690 * s ^ 41
    - 3782030845 * s ^ 40
    + 19213684353 * s ^ 39
    - 83939840676 * s ^ 38
    + 317582062719 * s ^ 37
    - 1044718504035 * s ^ 36
    + 2988984545491 * s ^ 35
    - 7401326664220 * s ^ 34
    + 15652601969791 * s ^ 33
    - 27443898937412 * s ^ 32
    + 37103783998047 * s ^ 31
    - 29720834178374 * s ^ 30
    - 16937584362598 * s ^ 29
    + 117692310422316 * s ^ 28
    - 256902072178996 * s ^ 27
    + 384306040315686 * s ^ 26
    - 458747012805561 * s ^ 25
    + 513720217329172 * s ^ 24
    - 654035651756911 * s ^ 23
    + 944884344079652 * s ^ 22
    - 1312370322361776 * s ^ 21
    + 1594787101470746 * s ^ 20
    - 1679305806478830 * s ^ 19
    + 1552458600389889 * s ^ 18
    - 1260788711825163 * s ^ 17
    + 888624146689620 * s ^ 16
    - 546097474372951 * s ^ 15
    + 314685137414619 * s ^ 14
    - 198582826593811 * s ^ 13
    + 144846341461044 * s ^ 12
    - 103613065516254 * s ^ 11
    + 61017378960572 * s ^ 10
    - 26362157425783 * s ^ 9
    + 7001837069890 * s ^ 8
    - 177226790173 * s ^ 7
    - 788036921215 * s ^ 6
    + 383602354411 * s ^ 5
    - 95471232495 * s ^ 4
    + 13108369363 * s ^ 3
    - 1002677067 * s ^ 2
    + 36517867 * s
    + 322272

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient25 (s : ℚ) : ℚ :=
  s ^ 47
    - 60 * s ^ 46
    + 1759 * s ^ 45
    - 33445 * s ^ 44
    + 462474 * s ^ 43
    - 4950650 * s ^ 42
    + 42691368 * s ^ 41
    - 305005132 * s ^ 40
    + 1844140264 * s ^ 39
    - 9596762625 * s ^ 38
    + 43570375026 * s ^ 37
    - 174403034248 * s ^ 36
    + 619857262342 * s ^ 35
    - 1962147351221 * s ^ 34
    + 5523385279021 * s ^ 33
    - 13737592713149 * s ^ 32
    + 29841690202848 * s ^ 31
    - 55650988119683 * s ^ 30
    + 86971655562462 * s ^ 29
    - 110243708480658 * s ^ 28
    + 109472683616102 * s ^ 27
    - 89005476790178 * s ^ 26
    + 95506168519292 * s ^ 25
    - 200834788482144 * s ^ 24
    + 435188456865492 * s ^ 23
    - 734970396552141 * s ^ 22
    + 982909518577618 * s ^ 21
    - 1103913178855132 * s ^ 20
    + 1096814423453243 * s ^ 19
    - 986501521695964 * s ^ 18
    + 799848806504930 * s ^ 17
    - 589310877574843 * s ^ 16
    + 422011169790072 * s ^ 15
    - 325309275644444 * s ^ 14
    + 269479259726088 * s ^ 13
    - 211115035951706 * s ^ 12
    + 137912336143220 * s ^ 11
    - 68349100051119 * s ^ 10
    + 22195314200504 * s ^ 9
    - 1896574667706 * s ^ 8
    - 2660835028730 * s ^ 7
    + 1831590368050 * s ^ 6
    - 651169467566 * s ^ 5
    + 142318087492 * s ^ 4
    - 18436612828 * s ^ 3
    + 1369985203 * s ^ 2
    - 47334506 * s
    - 654993

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient26 (s : ℚ) : ℚ :=
  s ^ 45
    - 44 * s ^ 44
    + 852 * s ^ 43
    - 8891 * s ^ 42
    + 39112 * s ^ 41
    + 275090 * s ^ 40
    - 6471268 * s ^ 39
    + 61120893 * s ^ 38
    - 366975622 * s ^ 37
    + 1399535276 * s ^ 36
    - 1879689550 * s ^ 35
    - 17535618563 * s ^ 34
    + 166838671694 * s ^ 33
    - 864297583761 * s ^ 32
    + 3259776555544 * s ^ 31
    - 9563487562474 * s ^ 30
    + 22096040986380 * s ^ 29
    - 39273848582176 * s ^ 28
    + 48948263208993 * s ^ 27
    - 25997107665426 * s ^ 26
    - 54839005809187 * s ^ 25
    + 192184676262557 * s ^ 24
    - 344689509800783 * s ^ 23
    + 459313182770522 * s ^ 22
    - 518668544725536 * s ^ 21
    + 545402871241034 * s ^ 20
    - 556509928033559 * s ^ 19
    + 540876027075605 * s ^ 18
    - 493959498705691 * s ^ 17
    + 442025488812084 * s ^ 16
    - 408946924162444 * s ^ 15
    + 380916954076944 * s ^ 14
    - 324947558972101 * s ^ 13
    + 231875414396626 * s ^ 12
    - 127803207009703 * s ^ 11
    + 47354658335057 * s ^ 10
    - 5136349449534 * s ^ 9
    - 7325771701127 * s ^ 8
    + 6292081251684 * s ^ 7
    - 2887726500940 * s ^ 6
    + 873455574853 * s ^ 5
    - 174721411723 * s ^ 4
    + 21592528978 * s ^ 3
    - 1557409519 * s ^ 2
    + 50034503 * s
    + 1095340

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient27 (s : ℚ) : ℚ :=
  s ^ 44
    - 68 * s ^ 43
    + 2171 * s ^ 42
    - 43783 * s ^ 41
    + 630156 * s ^ 40
    - 6912555 * s ^ 39
    + 60132609 * s ^ 38
    - 425284472 * s ^ 37
    + 2482631329 * s ^ 36
    - 12051793577 * s ^ 35
    + 48652370975 * s ^ 34
    - 161743655825 * s ^ 33
    + 430669608183 * s ^ 32
    - 850831500696 * s ^ 31
    + 905227788289 * s ^ 30
    + 1302546344296 * s ^ 29
    - 9812886479860 * s ^ 28
    + 29739576367065 * s ^ 27
    - 62693017237075 * s ^ 26
    + 101083809648205 * s ^ 25
    - 129718940791784 * s ^ 24
    + 140191006839304 * s ^ 23
    - 145633859388146 * s ^ 22
    + 172081499114332 * s ^ 21
    - 228044189938037 * s ^ 20
    + 291725604998555 * s ^ 19
    - 338309070890468 * s ^ 18
    + 368257904977199 * s ^ 17
    - 393027580835534 * s ^ 16
    + 403104087422593 * s ^ 15
    - 370839978689269 * s ^ 14
    + 284948288687024 * s ^ 13
    - 169680449696213 * s ^ 12
    + 66961038754611 * s ^ 11
    - 4582539038680 * s ^ 10
    - 17482842986000 * s ^ 9
    + 16399968246786 * s ^ 8
    - 8997094671127 * s ^ 7
    + 3450615705918 * s ^ 6
    - 942563012323 * s ^ 5
    + 176561978657 * s ^ 4
    - 20947314417 * s ^ 3
    + 1461480124 * s ^ 2
    - 42054037 * s
    - 1514436

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient28 (s : ℚ) : ℚ :=
  -s ^ 43
    + 60 * s ^ 42
    - 1767 * s ^ 41
    + 34003 * s ^ 40
    - 479616 * s ^ 39
    + 5267953 * s ^ 38
    - 46702070 * s ^ 37
    + 341786888 * s ^ 36
    - 2094909544 * s ^ 35
    + 10851182103 * s ^ 34
    - 47732301068 * s ^ 33
    + 178520065461 * s ^ 32
    - 566095422278 * s ^ 31
    + 1510129283909 * s ^ 30
    - 3337314895661 * s ^ 29
    + 5938020299984 * s ^ 28
    - 8031277963832 * s ^ 27
    + 7131612566809 * s ^ 26
    - 1857054030605 * s ^ 25
    - 3591275693896 * s ^ 24
    - 2373612453188 * s ^ 23
    + 31654938576546 * s ^ 22
    - 83832100543452 * s ^ 21
    + 143425330868503 * s ^ 20
    - 194989111325316 * s ^ 19
    + 237980337536838 * s ^ 18
    - 278534123844955 * s ^ 17
    + 308288462644526 * s ^ 16
    - 302917655331961 * s ^ 15
    + 246563044702452 * s ^ 14
    - 152573995832988 * s ^ 13
    + 56619670882291 * s ^ 12
    + 9127551271862 * s ^ 11
    - 35138950891360 * s ^ 10
    + 32963834755655 * s ^ 9
    - 20420033710081 * s ^ 8
    + 9357790680872 * s ^ 7
    - 3228516323127 * s ^ 6
    + 820949322432 * s ^ 5
    - 145982775967 * s ^ 4
    + 16672262390 * s ^ 3
    - 1116879939 * s ^ 2
    + 26587963 * s
    + 1733172

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient29 (s : ℚ) : ℚ :=
  -2 * s ^ 41
    + 129 * s ^ 40
    - 3977 * s ^ 39
    + 78166 * s ^ 38
    - 1101128 * s ^ 37
    + 11842573 * s ^ 36
    - 101090525 * s ^ 35
    + 702581797 * s ^ 34
    - 4043516709 * s ^ 33
    + 19476231082 * s ^ 32
    - 78919597752 * s ^ 31
    + 268958321459 * s ^ 30
    - 765664852687 * s ^ 29
    + 1790337728820 * s ^ 28
    - 3312932698004 * s ^ 27
    + 4399199442709 * s ^ 26
    - 2604262316453 * s ^ 25
    - 5458591004522 * s ^ 24
    + 21608010918488 * s ^ 23
    - 43415536413050 * s ^ 22
    + 65409507358062 * s ^ 21
    - 84983602620542 * s ^ 20
    + 106052680375051 * s ^ 19
    - 132839808259601 * s ^ 18
    + 158810237938454 * s ^ 17
    - 165919515304068 * s ^ 16
    + 139087762041390 * s ^ 15
    - 81625760962882 * s ^ 14
    + 15333098216122 * s ^ 13
    + 34489705584986 * s ^ 12
    - 55023327628408 * s ^ 11
    + 50390138573061 * s ^ 10
    - 34001980081064 * s ^ 9
    + 17886250737047 * s ^ 8
    - 7406527641484 * s ^ 7
    + 2380488299166 * s ^ 6
    - 573533211924 * s ^ 5
    + 97595623108 * s ^ 4
    - 10720779219 * s ^ 3
    + 679538643 * s ^ 2
    - 10708311 * s
    - 1638001

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient30 (s : ℚ) : ℚ :=
  s ^ 40
    - 61 * s ^ 39
    + 1809 * s ^ 38
    - 34688 * s ^ 37
    + 482781 * s ^ 36
    - 5191653 * s ^ 35
    + 44836681 * s ^ 34
    - 318979661 * s ^ 33
    + 1901032623 * s ^ 32
    - 9591935972 * s ^ 31
    + 41212120168 * s ^ 30
    - 151081183168 * s ^ 29
    + 472067043060 * s ^ 28
    - 1252757003067 * s ^ 27
    + 2808132545333 * s ^ 26
    - 5283228258092 * s ^ 25
    + 8311668576367 * s ^ 24
    - 11047799885906 * s ^ 23
    + 13119851586599 * s ^ 22
    - 16016924385869 * s ^ 21
    + 22878468604560 * s ^ 20
    - 35194752340819 * s ^ 19
    + 48716892954544 * s ^ 18
    - 53759713903677 * s ^ 17
    + 41739448851166 * s ^ 16
    - 12758077618086 * s ^ 15
    - 22942182234361 * s ^ 14
    + 51160560628490 * s ^ 13
    - 62411230173699 * s ^ 12
    + 56568235076338 * s ^ 11
    - 40877295444517 * s ^ 10
    + 24069734169710 * s ^ 9
    - 11571562509652 * s ^ 8
    + 4490106071304 * s ^ 7
    - 1371781685600 * s ^ 6
    + 316604473732 * s ^ 5
    - 51747636507 * s ^ 4
    + 5435904422 * s ^ 3
    - 316122548 * s ^ 2
    + 297139 * s
    + 1270776

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient31 (s : ℚ) : ℚ :=
  s ^ 38
    - 59 * s ^ 37
    + 1709 * s ^ 36
    - 32406 * s ^ 35
    + 450829 * s ^ 34
    - 4873469 * s ^ 33
    + 42249817 * s ^ 32
    - 299112581 * s ^ 31
    + 1747561718 * s ^ 30
    - 8474496738 * s ^ 29
    + 34180879101 * s ^ 28
    - 114476917952 * s ^ 27
    + 316222421009 * s ^ 26
    - 709410287366 * s ^ 25
    + 1248831426636 * s ^ 24
    - 1575561768263 * s ^ 23
    + 941085420909 * s ^ 22
    + 1388754934476 * s ^ 21
    - 5168798882992 * s ^ 20
    + 8343966272259 * s ^ 19
    - 7509079434652 * s ^ 18
    - 28831258183 * s ^ 17
    + 13936652447348 * s ^ 16
    - 30253610031127 * s ^ 15
    + 43195128399155 * s ^ 14
    - 48209867183459 * s ^ 13
    + 44299389375248 * s ^ 12
    - 34158389157268 * s ^ 11
    + 22218472919555 * s ^ 10
    - 12153282920676 * s ^ 9
    + 5531501138662 * s ^ 8
    - 2055139995492 * s ^ 7
    + 604679697948 * s ^ 6
    - 134546913069 * s ^ 5
    + 21099137069 * s ^ 4
    - 2087206302 * s ^ 3
    + 103116244 * s ^ 2
    + 3423355 * s
    - 800994

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient32 (s : ℚ) : ℚ :=
  2 * s ^ 36
    - 133 * s ^ 35
    + 4134 * s ^ 34
    - 80288 * s ^ 33
    + 1097058 * s ^ 32
    - 11246057 * s ^ 31
    + 89979176 * s ^ 30
    - 576722185 * s ^ 29
    + 3013863277 * s ^ 28
    - 12992693146 * s ^ 27
    + 46530819294 * s ^ 26
    - 138791718671 * s ^ 25
    + 343842439355 * s ^ 24
    - 699518228675 * s ^ 23
    + 1134219770701 * s ^ 22
    - 1343465370211 * s ^ 21
    + 749270775531 * s ^ 20
    + 1323184229141 * s ^ 19
    - 5252738815441 * s ^ 18
    + 10728245798954 * s ^ 17
    - 16640520841170 * s ^ 16
    + 21393252278273 * s ^ 15
    - 23532571926661 * s ^ 14
    + 22414643784831 * s ^ 13
    - 18537368262163 * s ^ 12
    + 13280551474470 * s ^ 11
    - 8192282523050 * s ^ 10
    + 4306834328350 * s ^ 9
    - 1899186911189 * s ^ 8
    + 686055821859 * s ^ 7
    - 196112104389 * s ^ 6
    + 42138472304 * s ^ 5
    - 6279146162 * s ^ 4
    + 561848529 * s ^ 3
    - 17597577 * s ^ 2
    - 3001775 * s
    + 403704

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient33 (s : ℚ) : ℚ :=
  -s ^ 35
    + 59 * s ^ 34
    - 1665 * s ^ 33
    + 29912 * s ^ 32
    - 384144 * s ^ 31
    + 3754585 * s ^ 30
    - 29036010 * s ^ 29
    + 182396836 * s ^ 28
    - 948330575 * s ^ 27
    + 4139014532 * s ^ 26
    - 15335146105 * s ^ 25
    + 48690306767 * s ^ 24
    - 133637896689 * s ^ 23
    + 319819796487 * s ^ 22
    - 673493540777 * s ^ 21
    + 1260106705634 * s ^ 20
    - 2114721429841 * s ^ 19
    + 3208346697468 * s ^ 18
    - 4419744698433 * s ^ 17
    + 5527355948857 * s ^ 16
    - 6247957399224 * s ^ 15
    + 6339329355206 * s ^ 14
    - 5728765423236 * s ^ 13
    + 4575179751616 * s ^ 12
    - 3202453176016 * s ^ 11
    + 1944653715060 * s ^ 10
    - 1010208350220 * s ^ 9
    + 440205882823 * s ^ 8
    - 156525113398 * s ^ 7
    + 43652347268 * s ^ 6
    - 8989969064 * s ^ 5
    + 1231612930 * s ^ 4
    - 86565506 * s ^ 3
    - 2211698 * s ^ 2
    + 1515376 * s
    - 158814

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient34 (s : ℚ) : ℚ :=
  -s ^ 32
    + 55 * s ^ 31
    - 1449 * s ^ 30
    + 24336 * s ^ 29
    - 292530 * s ^ 28
    + 2678532 * s ^ 27
    - 19414350 * s ^ 26
    + 114284327 * s ^ 25
    - 556284147 * s ^ 24
    + 2268356643 * s ^ 23
    - 7824051336 * s ^ 22
    + 22995614824 * s ^ 21
    - 57920721592 * s ^ 20
    + 125605845013 * s ^ 19
    - 235450080898 * s ^ 18
    + 382900810151 * s ^ 17
    - 542127113707 * s ^ 16
    + 670497626950 * s ^ 15
    - 726396163512 * s ^ 14
    + 690232300111 * s ^ 13
    - 574452418425 * s ^ 12
    + 416487371618 * s ^ 11
    - 260322903390 * s ^ 10
    + 138030475732 * s ^ 9
    - 60680995689 * s ^ 8
    + 21415654550 * s ^ 7
    - 5779795269 * s ^ 6
    + 1096156025 * s ^ 5
    - 119091776 * s ^ 4
    + 310744 * s ^ 3
    + 2277875 * s ^ 2
    - 506395 * s
    + 46980

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient35 (s : ℚ) : ℚ :=
  s ^ 28
    - 49 * s ^ 27
    + 1141 * s ^ 26
    - 16800 * s ^ 25
    + 175568 * s ^ 24
    - 1385679 * s ^ 23
    + 8580898 * s ^ 22
    - 42758517 * s ^ 21
    + 174459186 * s ^ 20
    - 589995325 * s ^ 19
    + 1667936778 * s ^ 18
    - 3964234882 * s ^ 17
    + 7948392148 * s ^ 16
    - 13464590269 * s ^ 15
    + 19265943878 * s ^ 14
    - 23238167032 * s ^ 13
    + 23535480978 * s ^ 12
    - 19888602568 * s ^ 11
    + 13887118020 * s ^ 10
    - 7891408818 * s ^ 9
    + 3560206123 * s ^ 8
    - 1220120472 * s ^ 7
    + 289102022 * s ^ 6
    - 34376128 * s ^ 5
    - 3793881 * s ^ 4
    + 2571979 * s ^ 3
    - 619156 * s ^ 2
    + 110684 * s
    - 9828

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient36 (s : ℚ) : ℚ :=
  s ^ 20
    - 37 * s ^ 19
    + 635 * s ^ 18
    - 6713 * s ^ 17
    + 48959 * s ^ 16
    - 261427 * s ^ 15
    + 1058529 * s ^ 14
    - 3321003 * s ^ 13
    + 8179202 * s ^ 12
    - 15923088 * s ^ 11
    + 24551871 * s ^ 10
    - 29911251 * s ^ 9
    + 28596296 * s ^ 8
    - 21204499 * s ^ 7
    + 11987092 * s ^ 6
    - 5054095 * s ^ 5
    + 1563420 * s ^ 4
    - 367497 * s ^ 3
    + 76637 * s ^ 2
    - 14328 * s
    + 1296

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient37 (s : ℚ) : ℚ :=
  -s ^ 10
    + 20 * s ^ 9
    - 173 * s ^ 8
    + 850 * s ^ 7
    - 2619 * s ^ 6
    + 5268 * s ^ 5
    - 6968 * s ^ 4
    + 5929 * s ^ 3
    - 3050 * s ^ 2
    + 825 * s
    - 81

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def structuralNumerator (r s : ℚ) : ℚ :=
  structuralNumeratorCoefficient0 s +
    structuralNumeratorCoefficient1 s * r +
    structuralNumeratorCoefficient2 s * r ^ 2 +
    structuralNumeratorCoefficient3 s * r ^ 3 +
    structuralNumeratorCoefficient4 s * r ^ 4 +
    structuralNumeratorCoefficient5 s * r ^ 5 +
    structuralNumeratorCoefficient6 s * r ^ 6 +
    structuralNumeratorCoefficient7 s * r ^ 7 +
    structuralNumeratorCoefficient8 s * r ^ 8 +
    structuralNumeratorCoefficient9 s * r ^ 9 +
    structuralNumeratorCoefficient10 s * r ^ 10 +
    structuralNumeratorCoefficient11 s * r ^ 11 +
    structuralNumeratorCoefficient12 s * r ^ 12 +
    structuralNumeratorCoefficient13 s * r ^ 13 +
    structuralNumeratorCoefficient14 s * r ^ 14 +
    structuralNumeratorCoefficient15 s * r ^ 15 +
    structuralNumeratorCoefficient16 s * r ^ 16 +
    structuralNumeratorCoefficient17 s * r ^ 17 +
    structuralNumeratorCoefficient18 s * r ^ 18 +
    structuralNumeratorCoefficient19 s * r ^ 19 +
    structuralNumeratorCoefficient20 s * r ^ 20 +
    structuralNumeratorCoefficient21 s * r ^ 21 +
    structuralNumeratorCoefficient22 s * r ^ 22 +
    structuralNumeratorCoefficient23 s * r ^ 23 +
    structuralNumeratorCoefficient24 s * r ^ 24 +
    structuralNumeratorCoefficient25 s * r ^ 25 +
    structuralNumeratorCoefficient26 s * r ^ 26 +
    structuralNumeratorCoefficient27 s * r ^ 27 +
    structuralNumeratorCoefficient28 s * r ^ 28 +
    structuralNumeratorCoefficient29 s * r ^ 29 +
    structuralNumeratorCoefficient30 s * r ^ 30 +
    structuralNumeratorCoefficient31 s * r ^ 31 +
    structuralNumeratorCoefficient32 s * r ^ 32 +
    structuralNumeratorCoefficient33 s * r ^ 33 +
    structuralNumeratorCoefficient34 s * r ^ 34 +
    structuralNumeratorCoefficient35 s * r ^ 35 +
    structuralNumeratorCoefficient36 s * r ^ 36 +
    structuralNumeratorCoefficient37 s * r ^ 37

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_0 (s : ℚ) :
    structuralNumeratorCoefficient0 s =
      termOneCoefficient0 s
        - termTwoCoefficient0 s
        - termThreeCoefficient0 s := by
  simp only [structuralNumeratorCoefficient0,
    termOneCoefficient0,
    termTwoCoefficient0,
    termThreeCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_1 (s : ℚ) :
    structuralNumeratorCoefficient1 s =
      termOneCoefficient1 s
        - termTwoCoefficient1 s
        - termThreeCoefficient1 s := by
  simp only [structuralNumeratorCoefficient1,
    termOneCoefficient1,
    termTwoCoefficient1,
    termThreeCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_2 (s : ℚ) :
    structuralNumeratorCoefficient2 s =
      termOneCoefficient2 s
        - termTwoCoefficient2 s
        - termThreeCoefficient2 s := by
  simp only [structuralNumeratorCoefficient2,
    termOneCoefficient2,
    termTwoCoefficient2,
    termThreeCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_3 (s : ℚ) :
    structuralNumeratorCoefficient3 s =
      termOneCoefficient3 s
        - termTwoCoefficient3 s
        - termThreeCoefficient3 s := by
  simp only [structuralNumeratorCoefficient3,
    termOneCoefficient3,
    termTwoCoefficient3,
    termThreeCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_4 (s : ℚ) :
    structuralNumeratorCoefficient4 s =
      termOneCoefficient4 s
        - termTwoCoefficient4 s
        - termThreeCoefficient4 s := by
  simp only [structuralNumeratorCoefficient4,
    termOneCoefficient4,
    termTwoCoefficient4,
    termThreeCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_5 (s : ℚ) :
    structuralNumeratorCoefficient5 s =
      termOneCoefficient5 s
        - termTwoCoefficient5 s
        - termThreeCoefficient5 s := by
  simp only [structuralNumeratorCoefficient5,
    termOneCoefficient5,
    termTwoCoefficient5,
    termThreeCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_6 (s : ℚ) :
    structuralNumeratorCoefficient6 s =
      termOneCoefficient6 s
        - termTwoCoefficient6 s
        - termThreeCoefficient6 s := by
  simp only [structuralNumeratorCoefficient6,
    termOneCoefficient6,
    termTwoCoefficient6,
    termThreeCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_7 (s : ℚ) :
    structuralNumeratorCoefficient7 s =
      termOneCoefficient7 s
        - termTwoCoefficient7 s
        - termThreeCoefficient7 s := by
  simp only [structuralNumeratorCoefficient7,
    termOneCoefficient7,
    termTwoCoefficient7,
    termThreeCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_8 (s : ℚ) :
    structuralNumeratorCoefficient8 s =
      termOneCoefficient8 s
        - termTwoCoefficient8 s
        - termThreeCoefficient8 s := by
  simp only [structuralNumeratorCoefficient8,
    termOneCoefficient8,
    termTwoCoefficient8,
    termThreeCoefficient8]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_9 (s : ℚ) :
    structuralNumeratorCoefficient9 s =
      termOneCoefficient9 s
        - termTwoCoefficient9 s
        - termThreeCoefficient9 s := by
  simp only [structuralNumeratorCoefficient9,
    termOneCoefficient9,
    termTwoCoefficient9,
    termThreeCoefficient9]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_10 (s : ℚ) :
    structuralNumeratorCoefficient10 s =
      termOneCoefficient10 s
        - termTwoCoefficient10 s
        - termThreeCoefficient10 s := by
  simp only [structuralNumeratorCoefficient10,
    termOneCoefficient10,
    termTwoCoefficient10,
    termThreeCoefficient10]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_11 (s : ℚ) :
    structuralNumeratorCoefficient11 s =
      termOneCoefficient11 s
        - termTwoCoefficient11 s
        - termThreeCoefficient11 s := by
  simp only [structuralNumeratorCoefficient11,
    termOneCoefficient11,
    termTwoCoefficient11,
    termThreeCoefficient11]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_12 (s : ℚ) :
    structuralNumeratorCoefficient12 s =
      termOneCoefficient12 s
        - termTwoCoefficient12 s
        - termThreeCoefficient12 s := by
  simp only [structuralNumeratorCoefficient12,
    termOneCoefficient12,
    termTwoCoefficient12,
    termThreeCoefficient12]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_13 (s : ℚ) :
    structuralNumeratorCoefficient13 s =
      termOneCoefficient13 s
        - termTwoCoefficient13 s
        - termThreeCoefficient13 s := by
  simp only [structuralNumeratorCoefficient13,
    termOneCoefficient13,
    termTwoCoefficient13,
    termThreeCoefficient13]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_14 (s : ℚ) :
    structuralNumeratorCoefficient14 s =
      termOneCoefficient14 s
        - termTwoCoefficient14 s
        - termThreeCoefficient14 s := by
  simp only [structuralNumeratorCoefficient14,
    termOneCoefficient14,
    termTwoCoefficient14,
    termThreeCoefficient14]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_15 (s : ℚ) :
    structuralNumeratorCoefficient15 s =
      termOneCoefficient15 s
        - termTwoCoefficient15 s
        - termThreeCoefficient15 s := by
  simp only [structuralNumeratorCoefficient15,
    termOneCoefficient15,
    termTwoCoefficient15,
    termThreeCoefficient15]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_16 (s : ℚ) :
    structuralNumeratorCoefficient16 s =
      termOneCoefficient16 s
        - termTwoCoefficient16 s
        - termThreeCoefficient16 s := by
  simp only [structuralNumeratorCoefficient16,
    termOneCoefficient16,
    termTwoCoefficient16,
    termThreeCoefficient16]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_17 (s : ℚ) :
    structuralNumeratorCoefficient17 s =
      termOneCoefficient17 s
        - termTwoCoefficient17 s
        - termThreeCoefficient17 s := by
  simp only [structuralNumeratorCoefficient17,
    termOneCoefficient17,
    termTwoCoefficient17,
    termThreeCoefficient17]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_18 (s : ℚ) :
    structuralNumeratorCoefficient18 s =
      termOneCoefficient18 s
        - termTwoCoefficient18 s
        - termThreeCoefficient18 s := by
  simp only [structuralNumeratorCoefficient18,
    termOneCoefficient18,
    termTwoCoefficient18,
    termThreeCoefficient18]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_19 (s : ℚ) :
    structuralNumeratorCoefficient19 s =
      termOneCoefficient19 s
        - termTwoCoefficient19 s
        - termThreeCoefficient19 s := by
  simp only [structuralNumeratorCoefficient19,
    termOneCoefficient19,
    termTwoCoefficient19,
    termThreeCoefficient19]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_20 (s : ℚ) :
    structuralNumeratorCoefficient20 s =
      termOneCoefficient20 s
        - termTwoCoefficient20 s
        - termThreeCoefficient20 s := by
  simp only [structuralNumeratorCoefficient20,
    termOneCoefficient20,
    termTwoCoefficient20,
    termThreeCoefficient20]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_21 (s : ℚ) :
    structuralNumeratorCoefficient21 s =
      termOneCoefficient21 s
        - termTwoCoefficient21 s
        - termThreeCoefficient21 s := by
  simp only [structuralNumeratorCoefficient21,
    termOneCoefficient21,
    termTwoCoefficient21,
    termThreeCoefficient21]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_22 (s : ℚ) :
    structuralNumeratorCoefficient22 s =
      termOneCoefficient22 s
        - termTwoCoefficient22 s
        - termThreeCoefficient22 s := by
  simp only [structuralNumeratorCoefficient22,
    termOneCoefficient22,
    termTwoCoefficient22,
    termThreeCoefficient22]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_23 (s : ℚ) :
    structuralNumeratorCoefficient23 s =
      termOneCoefficient23 s
        - termTwoCoefficient23 s
        - termThreeCoefficient23 s := by
  simp only [structuralNumeratorCoefficient23,
    termOneCoefficient23,
    termTwoCoefficient23,
    termThreeCoefficient23]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_24 (s : ℚ) :
    structuralNumeratorCoefficient24 s =
      termOneCoefficient24 s
        - termTwoCoefficient24 s
        - termThreeCoefficient24 s := by
  simp only [structuralNumeratorCoefficient24,
    termOneCoefficient24,
    termTwoCoefficient24,
    termThreeCoefficient24]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_25 (s : ℚ) :
    structuralNumeratorCoefficient25 s =
      termOneCoefficient25 s
        - termTwoCoefficient25 s
        - termThreeCoefficient25 s := by
  simp only [structuralNumeratorCoefficient25,
    termOneCoefficient25,
    termTwoCoefficient25,
    termThreeCoefficient25]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_26 (s : ℚ) :
    structuralNumeratorCoefficient26 s =
      termOneCoefficient26 s
        - termTwoCoefficient26 s
        - termThreeCoefficient26 s := by
  simp only [structuralNumeratorCoefficient26,
    termOneCoefficient26,
    termTwoCoefficient26,
    termThreeCoefficient26]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_27 (s : ℚ) :
    structuralNumeratorCoefficient27 s =
      termOneCoefficient27 s
        - termTwoCoefficient27 s
        - termThreeCoefficient27 s := by
  simp only [structuralNumeratorCoefficient27,
    termOneCoefficient27,
    termTwoCoefficient27,
    termThreeCoefficient27]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_28 (s : ℚ) :
    structuralNumeratorCoefficient28 s =
      termOneCoefficient28 s
        - termTwoCoefficient28 s
        - termThreeCoefficient28 s := by
  simp only [structuralNumeratorCoefficient28,
    termOneCoefficient28,
    termTwoCoefficient28,
    termThreeCoefficient28]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_29 (s : ℚ) :
    structuralNumeratorCoefficient29 s =
      termOneCoefficient29 s
        - termTwoCoefficient29 s
        - termThreeCoefficient29 s := by
  simp only [structuralNumeratorCoefficient29,
    termOneCoefficient29,
    termTwoCoefficient29,
    termThreeCoefficient29]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_30 (s : ℚ) :
    structuralNumeratorCoefficient30 s =
      termOneCoefficient30 s
        - termTwoCoefficient30 s
        - termThreeCoefficient30 s := by
  simp only [structuralNumeratorCoefficient30,
    termOneCoefficient30,
    termTwoCoefficient30,
    termThreeCoefficient30]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_31 (s : ℚ) :
    structuralNumeratorCoefficient31 s =
      termOneCoefficient31 s
        - termTwoCoefficient31 s
        - termThreeCoefficient31 s := by
  simp only [structuralNumeratorCoefficient31,
    termOneCoefficient31,
    termTwoCoefficient31,
    termThreeCoefficient31]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_32 (s : ℚ) :
    structuralNumeratorCoefficient32 s =
      termOneCoefficient32 s
        - termTwoCoefficient32 s
        - termThreeCoefficient32 s := by
  simp only [structuralNumeratorCoefficient32,
    termOneCoefficient32,
    termTwoCoefficient32,
    termThreeCoefficient32]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_33 (s : ℚ) :
    structuralNumeratorCoefficient33 s =
      termOneCoefficient33 s
        - termTwoCoefficient33 s
        - termThreeCoefficient33 s := by
  simp only [structuralNumeratorCoefficient33,
    termOneCoefficient33,
    termTwoCoefficient33,
    termThreeCoefficient33]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_34 (s : ℚ) :
    structuralNumeratorCoefficient34 s =
      termOneCoefficient34 s
        - termTwoCoefficient34 s
        - termThreeCoefficient34 s := by
  simp only [structuralNumeratorCoefficient34,
    termOneCoefficient34,
    termTwoCoefficient34,
    termThreeCoefficient34]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_35 (s : ℚ) :
    structuralNumeratorCoefficient35 s =
      termOneCoefficient35 s
        - termTwoCoefficient35 s
        - termThreeCoefficient35 s := by
  simp only [structuralNumeratorCoefficient35,
    termOneCoefficient35,
    termTwoCoefficient35,
    termThreeCoefficient35]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_36 (s : ℚ) :
    structuralNumeratorCoefficient36 s =
      termOneCoefficient36 s
        - termTwoCoefficient36 s
        - termThreeCoefficient36 s := by
  simp only [structuralNumeratorCoefficient36,
    termOneCoefficient36,
    termTwoCoefficient36,
    termThreeCoefficient36]
  ring

/-- Checked coefficient identity for a staged polynomial sum. -/
theorem structuralNumeratorCoefficient_linear_certificate_37 (s : ℚ) :
    structuralNumeratorCoefficient37 s =
      termOneCoefficient37 s
        - termTwoCoefficient37 s
        - termThreeCoefficient37 s := by
  simp only [structuralNumeratorCoefficient37,
    termOneCoefficient37,
    termTwoCoefficient37,
    termThreeCoefficient37]
  ring

/-- Checked staged polynomial-sum identity. -/
theorem structuralNumerator_eq_linearCombination (r s : ℚ) :
    structuralNumerator r s =
      termOne r s
        - termTwo r s
        - termThree r s := by
  have h0 := structuralNumeratorCoefficient_linear_certificate_0 s
  have h1 := structuralNumeratorCoefficient_linear_certificate_1 s
  have h2 := structuralNumeratorCoefficient_linear_certificate_2 s
  have h3 := structuralNumeratorCoefficient_linear_certificate_3 s
  have h4 := structuralNumeratorCoefficient_linear_certificate_4 s
  have h5 := structuralNumeratorCoefficient_linear_certificate_5 s
  have h6 := structuralNumeratorCoefficient_linear_certificate_6 s
  have h7 := structuralNumeratorCoefficient_linear_certificate_7 s
  have h8 := structuralNumeratorCoefficient_linear_certificate_8 s
  have h9 := structuralNumeratorCoefficient_linear_certificate_9 s
  have h10 := structuralNumeratorCoefficient_linear_certificate_10 s
  have h11 := structuralNumeratorCoefficient_linear_certificate_11 s
  have h12 := structuralNumeratorCoefficient_linear_certificate_12 s
  have h13 := structuralNumeratorCoefficient_linear_certificate_13 s
  have h14 := structuralNumeratorCoefficient_linear_certificate_14 s
  have h15 := structuralNumeratorCoefficient_linear_certificate_15 s
  have h16 := structuralNumeratorCoefficient_linear_certificate_16 s
  have h17 := structuralNumeratorCoefficient_linear_certificate_17 s
  have h18 := structuralNumeratorCoefficient_linear_certificate_18 s
  have h19 := structuralNumeratorCoefficient_linear_certificate_19 s
  have h20 := structuralNumeratorCoefficient_linear_certificate_20 s
  have h21 := structuralNumeratorCoefficient_linear_certificate_21 s
  have h22 := structuralNumeratorCoefficient_linear_certificate_22 s
  have h23 := structuralNumeratorCoefficient_linear_certificate_23 s
  have h24 := structuralNumeratorCoefficient_linear_certificate_24 s
  have h25 := structuralNumeratorCoefficient_linear_certificate_25 s
  have h26 := structuralNumeratorCoefficient_linear_certificate_26 s
  have h27 := structuralNumeratorCoefficient_linear_certificate_27 s
  have h28 := structuralNumeratorCoefficient_linear_certificate_28 s
  have h29 := structuralNumeratorCoefficient_linear_certificate_29 s
  have h30 := structuralNumeratorCoefficient_linear_certificate_30 s
  have h31 := structuralNumeratorCoefficient_linear_certificate_31 s
  have h32 := structuralNumeratorCoefficient_linear_certificate_32 s
  have h33 := structuralNumeratorCoefficient_linear_certificate_33 s
  have h34 := structuralNumeratorCoefficient_linear_certificate_34 s
  have h35 := structuralNumeratorCoefficient_linear_certificate_35 s
  have h36 := structuralNumeratorCoefficient_linear_certificate_36 s
  have h37 := structuralNumeratorCoefficient_linear_certificate_37 s
  simp only [structuralNumerator, termOne, termTwo, termThree]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 +
    r ^ 32 * h32 + r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 +
    r ^ 36 * h36 + r ^ 37 * h37

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 24
    + s ^ 23
    - s ^ 22
    + s ^ 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient1 (s : ℚ) : ℚ :=
  s ^ 30
    - 4 * s ^ 29
    + 10 * s ^ 28
    - 20 * s ^ 27
    + 35 * s ^ 26
    - 58 * s ^ 25
    + 80 * s ^ 24
    - 54 * s ^ 23
    + 42 * s ^ 22
    - 24 * s ^ 21
    + s ^ 20
    - 22 * s ^ 19
    + 24 * s ^ 18
    - 18 * s ^ 17
    + 10 * s ^ 16
    - 4 * s ^ 15
    + s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 32
    + 8 * s ^ 31
    - 28 * s ^ 30
    + 36 * s ^ 29
    - 5 * s ^ 28
    - 92 * s ^ 27
    + 296 * s ^ 26
    - 709 * s ^ 25
    + 1576 * s ^ 24
    - 2727 * s ^ 23
    + 3091 * s ^ 22
    - 3345 * s ^ 21
    + 3142 * s ^ 20
    - 2399 * s ^ 19
    + 2254 * s ^ 18
    - 2040 * s ^ 17
    + 1653 * s ^ 16
    - 1153 * s ^ 15
    + 677 * s ^ 14
    - 327 * s ^ 13
    + 123 * s ^ 12
    - 37 * s ^ 11
    + 8 * s ^ 10
    - s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient3 (s : ℚ) : ℚ :=
  s ^ 33
    - 15 * s ^ 32
    + 132 * s ^ 31
    - 676 * s ^ 30
    + 2214 * s ^ 29
    - 5046 * s ^ 28
    + 9694 * s ^ 27
    - 17051 * s ^ 26
    + 27876 * s ^ 25
    - 40591 * s ^ 24
    + 48234 * s ^ 23
    - 47835 * s ^ 22
    + 49102 * s ^ 21
    - 45971 * s ^ 20
    + 42756 * s ^ 19
    - 44276 * s ^ 18
    + 37834 * s ^ 17
    - 26310 * s ^ 16
    + 14128 * s ^ 15
    - 4941 * s ^ 14
    - 25 * s ^ 13
    + 1579 * s ^ 12
    - 1298 * s ^ 11
    + 684 * s ^ 10
    - 257 * s ^ 9
    + 68 * s ^ 8
    - 11 * s ^ 7
    + s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 35
    + 14 * s ^ 34
    - 104 * s ^ 33
    + 513 * s ^ 32
    - 1771 * s ^ 31
    + 4032 * s ^ 30
    - 5326 * s ^ 29
    + 2538 * s ^ 28
    + 1950 * s ^ 27
    - 5708 * s ^ 26
    + 15065 * s ^ 25
    - 49780 * s ^ 24
    + 116422 * s ^ 23
    - 155312 * s ^ 22
    + 123501 * s ^ 21
    - 92306 * s ^ 20
    + 31867 * s ^ 19
    + 7515 * s ^ 18
    + 63637 * s ^ 17
    - 155486 * s ^ 16
    + 212651 * s ^ 15
    - 213486 * s ^ 14
    + 169971 * s ^ 13
    - 109304 * s ^ 12
    + 56322 * s ^ 11
    - 23453 * s ^ 10
    + 7572 * s ^ 9
    - 1761 * s ^ 8
    + 242 * s ^ 7
    - 12 * s ^ 6
    - 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 35
    + 31 * s ^ 34
    - 337 * s ^ 33
    + 2243 * s ^ 32
    - 10488 * s ^ 31
    + 35717 * s ^ 30
    - 87672 * s ^ 29
    + 156226 * s ^ 28
    - 222706 * s ^ 27
    + 327891 * s ^ 26
    - 550871 * s ^ 25
    + 902612 * s ^ 24
    - 1185538 * s ^ 23
    + 1164114 * s ^ 22
    - 1129721 * s ^ 21
    + 1486807 * s ^ 20
    - 2019911 * s ^ 19
    + 3091189 * s ^ 18
    - 4501820 * s ^ 17
    + 5204164 * s ^ 16
    - 4995267 * s ^ 15
    + 4056323 * s ^ 14
    - 2794074 * s ^ 13
    + 1613481 * s ^ 12
    - 766994 * s ^ 11
    + 295940 * s ^ 10
    - 87038 * s ^ 9
    + 17220 * s ^ 8
    - 1391 * s ^ 7
    - 191 * s ^ 6
    + 61 * s ^ 5
    + s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 36
    + 19 * s ^ 35
    - 164 * s ^ 34
    + 770 * s ^ 33
    - 1704 * s ^ 32
    - 3469 * s ^ 31
    + 46182 * s ^ 30
    - 199635 * s ^ 29
    + 503388 * s ^ 28
    - 760105 * s ^ 27
    + 545831 * s ^ 26
    + 287266 * s ^ 25
    - 1431366 * s ^ 24
    + 2699972 * s ^ 23
    - 5459418 * s ^ 22
    + 12259465 * s ^ 21
    - 22975727 * s ^ 20
    + 35641700 * s ^ 19
    - 49685905 * s ^ 18
    + 59411989 * s ^ 17
    - 59423754 * s ^ 16
    + 51370136 * s ^ 15
    - 38513873 * s ^ 14
    + 24821038 * s ^ 13
    - 13495856 * s ^ 12
    + 6052436 * s ^ 11
    - 2170963 * s ^ 10
    + 563968 * s ^ 9
    - 80673 * s ^ 8
    - 5050 * s ^ 7
    + 4138 * s ^ 6
    - 577 * s ^ 5
    - 59 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 36
    + 33 * s ^ 35
    - 437 * s ^ 34
    + 3360 * s ^ 33
    - 16947 * s ^ 32
    + 56984 * s ^ 31
    - 104393 * s ^ 30
    - 79548 * s ^ 29
    + 1246449 * s ^ 28
    - 4481878 * s ^ 27
    + 10158123 * s ^ 26
    - 17859229 * s ^ 25
    + 29355586 * s ^ 24
    - 51497115 * s ^ 23
    + 94673149 * s ^ 22
    - 162367129 * s ^ 21
    + 244774645 * s ^ 20
    - 330798166 * s ^ 19
    + 403564289 * s ^ 18
    - 428301403 * s ^ 17
    + 394454056 * s ^ 16
    - 321470089 * s ^ 15
    + 229581072 * s ^ 14
    - 141121546 * s ^ 13
    + 72840021 * s ^ 12
    - 30615029 * s ^ 11
    + 9874967 * s ^ 10
    - 1987549 * s ^ 9
    + 14101 * s ^ 8
    + 136261 * s ^ 7
    - 35748 * s ^ 6
    + 2262 * s ^ 5
    + 838 * s ^ 4
    + 13 * s ^ 3
    - 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient8 (s : ℚ) : ℚ :=
  21 * s ^ 35
    - 532 * s ^ 34
    + 6389 * s ^ 33
    - 49056 * s ^ 32
    + 270170 * s ^ 31
    - 1121248 * s ^ 30
    + 3561469 * s ^ 29
    - 8743834 * s ^ 28
    + 17271030 * s ^ 27
    - 31178034 * s ^ 26
    + 61874178 * s ^ 25
    - 136649635 * s ^ 24
    + 290069691 * s ^ 23
    - 541340757 * s ^ 22
    + 873423949 * s ^ 21
    - 1246534420 * s ^ 20
    + 1609265943 * s ^ 19
    - 1852763555 * s ^ 18
    + 1861085211 * s ^ 17
    - 1652889435 * s ^ 16
    + 1310608524 * s ^ 15
    - 906648168 * s ^ 14
    + 533276477 * s ^ 13
    - 258007791 * s ^ 12
    + 97371103 * s ^ 11
    - 24512576 * s ^ 10
    + 850863 * s ^ 9
    + 2414599 * s ^ 8
    - 1089104 * s ^ 7
    + 182742 * s ^ 6
    + 2182 * s ^ 5
    - 5939 * s ^ 4
    - 491 * s ^ 3
    + 33 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 37
    + 29 * s ^ 36
    - 419 * s ^ 35
    + 3873 * s ^ 34
    - 25278 * s ^ 33
    + 122471 * s ^ 32
    - 449893 * s ^ 31
    + 1262364 * s ^ 30
    - 2826020 * s ^ 29
    + 6328419 * s ^ 28
    - 19735239 * s ^ 27
    + 71466131 * s ^ 26
    - 220432343 * s ^ 25
    + 540591844 * s ^ 24
    - 1084816587 * s ^ 23
    + 1861628135 * s ^ 22
    - 2839247318 * s ^ 21
    + 3945414882 * s ^ 20
    - 4964443233 * s ^ 19
    + 5510558005 * s ^ 18
    - 5377260755 * s ^ 17
    + 4711183896 * s ^ 16
    - 3671178414 * s ^ 15
    + 2442689655 * s ^ 14
    - 1338308109 * s ^ 13
    + 568537876 * s ^ 12
    - 157887111 * s ^ 11
    - 2678 * s ^ 10
    + 29736269 * s ^ 9
    - 17427702 * s ^ 8
    + 5103198 * s ^ 7
    - 538343 * s ^ 6
    - 76636 * s ^ 5
    + 23768 * s ^ 4
    + 5478 * s ^ 3
    - 189 * s ^ 2
    - 25 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient10 (s : ℚ) : ℚ :=
  s ^ 37
    - 22 * s ^ 36
    + 223 * s ^ 35
    - 1288 * s ^ 34
    + 4120 * s ^ 33
    - 4443 * s ^ 32
    + 3171 * s ^ 31
    - 324620 * s ^ 30
    + 3641298 * s ^ 29
    - 21943939 * s ^ 28
    + 89820411 * s ^ 27
    - 273540779 * s ^ 26
    + 657936186 * s ^ 25
    - 1323642060 * s ^ 24
    + 2357252444 * s ^ 23
    - 3872536845 * s ^ 22
    + 5935729069 * s ^ 21
    - 8327395490 * s ^ 20
    + 10338422150 * s ^ 19
    - 11204365883 * s ^ 18
    + 10834970610 * s ^ 17
    - 9466457139 * s ^ 16
    + 7136236122 * s ^ 15
    - 4344230316 * s ^ 14
    + 1980090841 * s ^ 13
    - 505656256 * s ^ 12
    - 133421641 * s ^ 11
    + 258407100 * s ^ 10
    - 173686772 * s ^ 9
    + 68873355 * s ^ 8
    - 14968058 * s ^ 7
    + 402936 * s ^ 6
    + 460460 * s ^ 5
    - 40486 * s ^ 4
    - 34542 * s ^ 3
    - 219 * s ^ 2
    + 301 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient11 (s : ℚ) : ℚ :=
  -3 * s ^ 36
    + 47 * s ^ 35
    - 104 * s ^ 34
    - 4659 * s ^ 33
    + 74087 * s ^ 32
    - 640037 * s ^ 31
    + 3847549 * s ^ 30
    - 17318391 * s ^ 29
    + 60381629 * s ^ 28
    - 167664347 * s ^ 27
    + 386410502 * s ^ 26
    - 790810190 * s ^ 25
    + 1550921126 * s ^ 24
    - 2994435462 * s ^ 23
    + 5468173905 * s ^ 22
    - 8926194371 * s ^ 21
    + 12558326202 * s ^ 20
    - 15131040431 * s ^ 19
    + 16098028504 * s ^ 18
    - 15631830021 * s ^ 17
    + 13312483665 * s ^ 16
    - 8866053472 * s ^ 15
    + 3892271324 * s ^ 14
    - 317168342 * s ^ 13
    - 1351529602 * s ^ 12
    + 1580948848 * s ^ 11
    - 1122891394 * s ^ 10
    + 551310863 * s ^ 9
    - 171812936 * s ^ 8
    + 23733543 * s ^ 7
    + 3980597 * s ^ 6
    - 1532586 * s ^ 5
    - 111746 * s ^ 4
    + 136852 * s ^ 3
    + 11171 * s ^ 2
    - 2320 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient12 (s : ℚ) : ℚ :=
  -4 * s ^ 36
    + 137 * s ^ 35
    - 2213 * s ^ 34
    + 22653 * s ^ 33
    - 164066 * s ^ 32
    + 883018 * s ^ 31
    - 3611707 * s ^ 30
    + 11420424 * s ^ 29
    - 29196821 * s ^ 28
    + 69008206 * s ^ 27
    - 184464513 * s ^ 26
    + 556112716 * s ^ 25
    - 1557349000 * s ^ 24
    + 3608499379 * s ^ 23
    - 6758359191 * s ^ 22
    + 10345790825 * s ^ 21
    - 13312181983 * s ^ 20
    + 15188427667 * s ^ 19
    - 16227843206 * s ^ 18
    + 15513421013 * s ^ 17
    - 10908698500 * s ^ 16
    + 3167373799 * s ^ 15
    + 3517834074 * s ^ 14
    - 6605207281 * s ^ 13
    + 6593147856 * s ^ 12
    - 4879093769 * s ^ 11
    + 2771103336 * s ^ 10
    - 1115399813 * s ^ 9
    + 249945861 * s ^ 8
    + 5684256 * s ^ 7
    - 20487280 * s ^ 6
    + 2845492 * s ^ 5
    + 924212 * s ^ 4
    - 305289 * s ^ 3
    - 93088 * s ^ 2
    + 12799 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient13 (s : ℚ) : ℚ :=
  2 * s ^ 36
    - 51 * s ^ 35
    + 585 * s ^ 34
    - 3687 * s ^ 33
    + 10608 * s ^ 32
    + 20841 * s ^ 31
    - 289656 * s ^ 30
    + 532308 * s ^ 29
    + 6183244 * s ^ 28
    - 57223982 * s ^ 27
    + 266093247 * s ^ 26
    - 840817836 * s ^ 25
    + 1968386928 * s ^ 24
    - 3568845591 * s ^ 23
    + 5210418593 * s ^ 22
    - 6506016659 * s ^ 21
    + 7733973536 * s ^ 20
    - 9498853127 * s ^ 19
    + 10542294457 * s ^ 18
    - 6843363579 * s ^ 17
    - 3220017164 * s ^ 16
    + 14152138836 * s ^ 15
    - 19376448505 * s ^ 14
    + 18486615361 * s ^ 13
    - 14313174581 * s ^ 12
    + 9066805255 * s ^ 11
    - 4391943880 * s ^ 10
    + 1333461387 * s ^ 9
    - 62021687 * s ^ 8
    - 136916994 * s ^ 7
    + 52608386 * s ^ 6
    - 1535034 * s ^ 5
    - 2453415 * s ^ 4
    - 43411 * s ^ 3
    + 478761 * s ^ 2
    - 53477 * s
    - 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient14 (s : ℚ) : ℚ :=
  -5 * s ^ 35
    + 112 * s ^ 34
    - 907 * s ^ 33
    - 683 * s ^ 32
    + 87178 * s ^ 31
    - 988097 * s ^ 30
    + 6601447 * s ^ 29
    - 30667441 * s ^ 28
    + 104160340 * s ^ 27
    - 261696881 * s ^ 26
    + 479526471 * s ^ 25
    - 612627236 * s ^ 24
    + 506239094 * s ^ 23
    - 363824111 * s ^ 22
    + 964411020 * s ^ 21
    - 2879553745 * s ^ 20
    + 4407780443 * s ^ 19
    - 644194544 * s ^ 18
    - 11819889872 * s ^ 17
    + 27697939037 * s ^ 16
    - 36500220471 * s ^ 15
    + 34930717148 * s ^ 14
    - 27879713086 * s ^ 13
    + 19304075958 * s ^ 12
    - 10760977359 * s ^ 11
    + 4000450512 * s ^ 10
    - 300201880 * s ^ 9
    - 644472927 * s ^ 8
    + 381959845 * s ^ 7
    - 83582686 * s ^ 6
    - 3377395 * s ^ 5
    + 230082 * s ^ 4
    + 3420647 * s ^ 3
    - 1784821 * s ^ 2
    + 174642 * s
    + 171

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient15 (s : ℚ) : ℚ :=
  -3 * s ^ 35
    + 113 * s ^ 34
    - 1954 * s ^ 33
    + 20572 * s ^ 32
    - 145072 * s ^ 31
    + 698519 * s ^ 30
    - 2144316 * s ^ 29
    + 2559542 * s ^ 28
    + 11874215 * s ^ 27
    - 80460223 * s ^ 26
    + 249731205 * s ^ 25
    - 459859602 * s ^ 24
    + 372733703 * s ^ 23
    + 545307422 * s ^ 22
    - 2236404690 * s ^ 21
    + 2661547295 * s ^ 20
    + 2543833129 * s ^ 19
    - 16487056503 * s ^ 18
    + 34653190626 * s ^ 17
    - 45692293816 * s ^ 16
    + 43741955329 * s ^ 15
    - 34675024088 * s ^ 14
    + 25284169749 * s ^ 13
    - 15928322249 * s ^ 12
    + 6674418220 * s ^ 11
    - 106647530 * s ^ 10
    - 2267241434 * s ^ 9
    + 1709283311 * s ^ 8
    - 611106882 * s ^ 7
    + 94495319 * s ^ 6
    - 10795109 * s ^ 5
    + 22850304 * s ^ 4
    - 15821787 * s ^ 3
    + 5111427 * s ^ 2
    - 453777 * s
    - 965

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient16 (s : ℚ) : ℚ :=
  9 * s ^ 34
    - 315 * s ^ 33
    + 5220 * s ^ 32
    - 53863 * s ^ 31
    + 381499 * s ^ 30
    - 1918314 * s ^ 29
    + 6736211 * s ^ 28
    - 14534817 * s ^ 27
    + 4468295 * s ^ 26
    + 103354142 * s ^ 25
    - 460180096 * s ^ 24
    + 1133177820 * s ^ 23
    - 1644025518 * s ^ 22
    + 382925243 * s ^ 21
    + 5241735481 * s ^ 20
    - 16607933543 * s ^ 19
    + 30132292430 * s ^ 18
    - 37308610056 * s ^ 17
    + 33144318247 * s ^ 16
    - 23392782534 * s ^ 15
    + 16499614164 * s ^ 14
    - 11906511483 * s ^ 13
    + 5151977514 * s ^ 12
    + 2238227162 * s ^ 11
    - 5899098082 * s ^ 10
    + 5048228143 * s ^ 9
    - 2425102250 * s ^ 8
    + 675377984 * s ^ 7
    - 157537964 * s ^ 6
    + 120110673 * s ^ 5
    - 99560762 * s ^ 4
    + 45519358 * s ^ 3
    - 11550336 * s ^ 2
    + 946526 * s
    + 3812

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient17 (s : ℚ) : ℚ :=
  s ^ 34
    - 50 * s ^ 33
    + 1115 * s ^ 32
    - 15141 * s ^ 31
    + 141474 * s ^ 30
    - 965742 * s ^ 29
    + 4961492 * s ^ 28
    - 19340870 * s ^ 27
    + 56121954 * s ^ 26
    - 110940825 * s ^ 25
    + 86427033 * s ^ 24
    + 351010550 * s ^ 23
    - 1878012575 * s ^ 22
    + 5283659633 * s ^ 21
    - 10513682464 * s ^ 20
    + 15267470099 * s ^ 19
    - 15295917032 * s ^ 18
    + 8757861961 * s ^ 17
    - 683451210 * s ^ 16
    - 1701014612 * s ^ 15
    - 572417029 * s ^ 14
    - 259271499 * s ^ 13
    + 6022824935 * s ^ 12
    - 10663086597 * s ^ 11
    + 10038838602 * s ^ 10
    - 5964287050 * s ^ 9
    + 2304630378 * s ^ 8
    - 766648147 * s ^ 7
    + 506650424 * s ^ 6
    - 432822176 * s ^ 5
    + 257786344 * s ^ 4
    - 95765358 * s ^ 3
    + 20851982 * s ^ 2
    - 1588452 * s
    - 11148

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient18 (s : ℚ) : ℚ :=
  -2 * s ^ 33
    + 85 * s ^ 32
    - 1726 * s ^ 31
    + 22236 * s ^ 30
    - 203243 * s ^ 29
    + 1397592 * s ^ 28
    - 7492379 * s ^ 27
    + 32061881 * s ^ 26
    - 111303675 * s ^ 25
    + 316483070 * s ^ 24
    - 736589800 * s ^ 23
    + 1370647046 * s ^ 22
    - 1872173529 * s ^ 21
    + 1278556292 * s ^ 20
    + 1628223677 * s ^ 19
    - 6609743654 * s ^ 18
    + 10325417784 * s ^ 17
    - 8774181110 * s ^ 16
    + 3423413978 * s ^ 15
    - 1467120012 * s ^ 14
    + 6351999597 * s ^ 13
    - 12575510117 * s ^ 12
    + 13589083265 * s ^ 11
    - 9499009176 * s ^ 10
    + 4634758790 * s ^ 9
    - 2025119941 * s ^ 8
    + 1466609694 * s ^ 7
    - 1358299056 * s ^ 6
    + 967162633 * s ^ 5
    - 475717081 * s ^ 4
    + 154652059 * s ^ 3
    - 30185947 * s ^ 2
    + 2135871 * s
    + 24898

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient19 (s : ℚ) : ℚ :=
  s ^ 32
    - 42 * s ^ 31
    + 851 * s ^ 30
    - 10960 * s ^ 29
    + 100177 * s ^ 28
    - 691094 * s ^ 27
    + 3753644 * s ^ 26
    - 16608943 * s ^ 25
    + 61721460 * s ^ 24
    - 197480001 * s ^ 23
    + 549744961 * s ^ 22
    - 1313239252 * s ^ 21
    + 2581573818 * s ^ 20
    - 3880204956 * s ^ 19
    + 3855291246 * s ^ 18
    - 1357893274 * s ^ 17
    - 2112414951 * s ^ 16
    + 2251716039 * s ^ 15
    + 3177915751 * s ^ 14
    - 10235365848 * s ^ 13
    + 12901662649 * s ^ 12
    - 10138399863 * s ^ 11
    + 5767659006 * s ^ 10
    - 3224975537 * s ^ 9
    + 2850254764 * s ^ 8
    - 3012342509 * s ^ 7
    + 2514681868 * s ^ 6
    - 1523477929 * s ^ 5
    + 659232098 * s ^ 4
    - 194816137 * s ^ 3
    + 34930687 * s ^ 2
    - 2274538 * s
    - 43186

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient20 (s : ℚ) : ℚ :=
  s ^ 30
    - 26 * s ^ 29
    + 221 * s ^ 28
    + 471 * s ^ 27
    - 27363 * s ^ 26
    + 288671 * s ^ 25
    - 1712773 * s ^ 24
    + 6042611 * s ^ 23
    - 8048540 * s ^ 22
    - 40590365 * s ^ 21
    + 300336944 * s ^ 20
    - 1027991724 * s ^ 19
    + 2213407050 * s ^ 18
    - 2941393073 * s ^ 17
    + 1525127330 * s ^ 16
    + 2644706185 * s ^ 15
    - 7332252224 * s ^ 14
    + 9106171780 * s ^ 13
    - 7232510508 * s ^ 12
    + 4353021426 * s ^ 11
    - 3128903069 * s ^ 10
    + 3768977503 * s ^ 9
    - 4709967797 * s ^ 8
    + 4559247592 * s ^ 7
    - 3282401139 * s ^ 6
    + 1763479471 * s ^ 5
    - 696478925 * s ^ 4
    + 191529201 * s ^ 3
    - 31992486 * s ^ 2
    + 1874977 * s
    + 58578

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient21 (s : ℚ) : ℚ :=
  s ^ 29
    - 51 * s ^ 28
    + 1169 * s ^ 27
    - 16377 * s ^ 26
    + 158681 * s ^ 25
    - 1129668 * s ^ 24
    + 6077635 * s ^ 23
    - 24859310 * s ^ 22
    + 76010148 * s ^ 21
    - 163523556 * s ^ 20
    + 195904852 * s ^ 19
    + 107562039 * s ^ 18
    - 1102192340 * s ^ 17
    + 2724223222 * s ^ 16
    - 4082561632 * s ^ 15
    + 4058998649 * s ^ 14
    - 2689515630 * s ^ 13
    + 1463586017 * s ^ 12
    - 1776522500 * s ^ 11
    + 3487406003 * s ^ 10
    - 5240767601 * s ^ 9
    + 5763529791 * s ^ 8
    - 4794616763 * s ^ 7
    + 3069119736 * s ^ 6
    - 1512039057 * s ^ 5
    + 558962833 * s ^ 4
    - 145361473 * s ^ 3
    + 22771218 * s ^ 2
    - 1143978 * s
    - 62058

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient22 (s : ℚ) : ℚ :=
  -s ^ 28
    + 43 * s ^ 27
    - 899 * s ^ 26
    + 12128 * s ^ 25
    - 117484 * s ^ 24
    + 858729 * s ^ 23
    - 4851348 * s ^ 22
    + 21409587 * s ^ 21
    - 73932534 * s ^ 20
    + 198409035 * s ^ 19
    - 405938544 * s ^ 18
    + 605978380 * s ^ 17
    - 587729323 * s ^ 16
    + 210344126 * s ^ 15
    + 283174892 * s ^ 14
    - 267069736 * s ^ 13
    - 729897904 * s ^ 12
    + 2486866313 * s ^ 11
    - 4192811656 * s ^ 10
    + 5030173763 * s ^ 9
    - 4679755534 * s ^ 8
    + 3460477830 * s ^ 7
    - 2040163835 * s ^ 6
    + 947486784 * s ^ 5
    - 334455200 * s ^ 4
    + 83229932 * s ^ 3
    - 12213470 * s ^ 2
    + 465058 * s
    + 50868

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient23 (s : ℚ) : ℚ :=
  -2 * s ^ 26
    + 93 * s ^ 25
    - 1981 * s ^ 24
    + 25762 * s ^ 23
    - 229516 * s ^ 22
    + 1487343 * s ^ 21
    - 7252006 * s ^ 20
    + 27083672 * s ^ 19
    - 77852111 * s ^ 18
    + 170362806 * s ^ 17
    - 271850450 * s ^ 16
    + 269652080 * s ^ 15
    - 1925408 * s ^ 14
    - 619761719 * s ^ 13
    + 1494625471 * s ^ 12
    - 2350668236 * s ^ 11
    + 2881668279 * s ^ 10
    - 2895016950 * s ^ 9
    + 2410756451 * s ^ 8
    - 1658403921 * s ^ 7
    + 932511736 * s ^ 6
    - 419076961 * s ^ 5
    + 143836123 * s ^ 4
    - 34535527 * s ^ 3
    + 4678106 * s ^ 2
    - 81490 * s
    - 31644

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient24 (s : ℚ) : ℚ :=
  s ^ 25
    - 42 * s ^ 24
    + 828 * s ^ 23
    - 10182 * s ^ 22
    + 87555 * s ^ 21
    - 559523 * s ^ 20
    + 2758130 * s ^ 19
    - 10753371 * s ^ 18
    + 33782925 * s ^ 17
    - 86896635 * s ^ 16
    + 185986881 * s ^ 15
    - 337347817 * s ^ 14
    + 529050013 * s ^ 13
    - 730038562 * s ^ 12
    + 893453968 * s ^ 11
    - 964475161 * s ^ 10
    + 904715263 * s ^ 9
    - 725315189 * s ^ 8
    + 489664578 * s ^ 7
    - 273469438 * s ^ 6
    + 122501643 * s ^ 5
    - 41638023 * s ^ 4
    + 9667000 * s ^ 3
    - 1147808 * s ^ 2
    - 31479 * s
    + 14445

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient25 (s : ℚ) : ℚ :=
  s ^ 22
    - 38 * s ^ 21
    + 680 * s ^ 20
    - 7608 * s ^ 19
    + 59583 * s ^ 18
    - 346557 * s ^ 17
    + 1550477 * s ^ 16
    - 5455478 * s ^ 15
    + 15319086 * s ^ 14
    - 34678740 * s ^ 13
    + 63779132 * s ^ 12
    - 95966933 * s ^ 11
    + 119030456 * s ^ 10
    - 122683939 * s ^ 9
    + 105709383 * s ^ 8
    - 75985242 * s ^ 7
    + 44773580 * s ^ 6
    - 20812734 * s ^ 5
    + 7136528 * s ^ 4
    - 1572311 * s ^ 3
    + 129333 * s ^ 2
    + 25904 * s
    - 4563

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient26 (s : ℚ) : ℚ :=
  -s ^ 18
    + 32 * s ^ 17
    - 474 * s ^ 16
    + 4312 * s ^ 15
    - 26949 * s ^ 14
    + 122618 * s ^ 13
    - 419882 * s ^ 12
    + 1103049 * s ^ 11
    - 2245274 * s ^ 10
    + 3551417 * s ^ 9
    - 4350712 * s ^ 8
    + 4088199 * s ^ 7
    - 2893152 * s ^ 6
    + 1489267 * s ^ 5
    - 514527 * s ^ 4
    + 89856 * s ^ 3
    + 8698 * s ^ 2
    - 7368 * s
    + 891

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient27 (s : ℚ) : ℚ :=
  -s ^ 10
    + 20 * s ^ 9
    - 173 * s ^ 8
    + 850 * s ^ 7
    - 2619 * s ^ 6
    + 5268 * s ^ 5
    - 6968 * s ^ 4
    + 5929 * s ^ 3
    - 3050 * s ^ 2
    + 825 * s
    - 81

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def multiplier (r s : ℚ) : ℚ :=
  multiplierCoefficient0 s +
    multiplierCoefficient1 s * r +
    multiplierCoefficient2 s * r ^ 2 +
    multiplierCoefficient3 s * r ^ 3 +
    multiplierCoefficient4 s * r ^ 4 +
    multiplierCoefficient5 s * r ^ 5 +
    multiplierCoefficient6 s * r ^ 6 +
    multiplierCoefficient7 s * r ^ 7 +
    multiplierCoefficient8 s * r ^ 8 +
    multiplierCoefficient9 s * r ^ 9 +
    multiplierCoefficient10 s * r ^ 10 +
    multiplierCoefficient11 s * r ^ 11 +
    multiplierCoefficient12 s * r ^ 12 +
    multiplierCoefficient13 s * r ^ 13 +
    multiplierCoefficient14 s * r ^ 14 +
    multiplierCoefficient15 s * r ^ 15 +
    multiplierCoefficient16 s * r ^ 16 +
    multiplierCoefficient17 s * r ^ 17 +
    multiplierCoefficient18 s * r ^ 18 +
    multiplierCoefficient19 s * r ^ 19 +
    multiplierCoefficient20 s * r ^ 20 +
    multiplierCoefficient21 s * r ^ 21 +
    multiplierCoefficient22 s * r ^ 22 +
    multiplierCoefficient23 s * r ^ 23 +
    multiplierCoefficient24 s * r ^ 24 +
    multiplierCoefficient25 s * r ^ 25 +
    multiplierCoefficient26 s * r ^ 26 +
    multiplierCoefficient27 s * r ^ 27

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_0 (s : ℚ) :
    structuralNumeratorCoefficient0 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient0,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_1 (s : ℚ) :
    structuralNumeratorCoefficient1 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient1,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_2 (s : ℚ) :
    structuralNumeratorCoefficient2 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient2,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_3 (s : ℚ) :
    structuralNumeratorCoefficient3 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient3,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_4 (s : ℚ) :
    structuralNumeratorCoefficient4 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient4,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_5 (s : ℚ) :
    structuralNumeratorCoefficient5 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient5,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_6 (s : ℚ) :
    structuralNumeratorCoefficient6 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient6,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_7 (s : ℚ) :
    structuralNumeratorCoefficient7 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient7,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_8 (s : ℚ) :
    structuralNumeratorCoefficient8 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient8,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_9 (s : ℚ) :
    structuralNumeratorCoefficient9 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient9,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_10 (s : ℚ) :
    structuralNumeratorCoefficient10 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient1 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient0 s := by
  simp only [structuralNumeratorCoefficient10,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient1,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_11 (s : ℚ) :
    structuralNumeratorCoefficient11 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient2 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient1 s := by
  simp only [structuralNumeratorCoefficient11,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient2,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient1]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_12 (s : ℚ) :
    structuralNumeratorCoefficient12 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient3 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient2 s := by
  simp only [structuralNumeratorCoefficient12,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient3,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient2]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_13 (s : ℚ) :
    structuralNumeratorCoefficient13 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient4 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient3 s := by
  simp only [structuralNumeratorCoefficient13,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient4,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient3]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_14 (s : ℚ) :
    structuralNumeratorCoefficient14 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient5 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient4 s := by
  simp only [structuralNumeratorCoefficient14,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient5,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient4]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_15 (s : ℚ) :
    structuralNumeratorCoefficient15 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient6 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient5 s := by
  simp only [structuralNumeratorCoefficient15,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient6,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient5]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_16 (s : ℚ) :
    structuralNumeratorCoefficient16 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient7 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient6 s := by
  simp only [structuralNumeratorCoefficient16,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient7,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient6]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_17 (s : ℚ) :
    structuralNumeratorCoefficient17 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient8 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient7 s := by
  simp only [structuralNumeratorCoefficient17,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient8,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient7]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_18 (s : ℚ) :
    structuralNumeratorCoefficient18 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient9 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient8 s := by
  simp only [structuralNumeratorCoefficient18,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient8]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_19 (s : ℚ) :
    structuralNumeratorCoefficient19 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient10 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient9 s := by
  simp only [structuralNumeratorCoefficient19,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient10,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient9]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_20 (s : ℚ) :
    structuralNumeratorCoefficient20 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient11 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient10 s := by
  simp only [structuralNumeratorCoefficient20,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient11,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient10]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_21 (s : ℚ) :
    structuralNumeratorCoefficient21 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient12 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient11 s := by
  simp only [structuralNumeratorCoefficient21,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient12,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient11]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_22 (s : ℚ) :
    structuralNumeratorCoefficient22 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient13 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient12 s := by
  simp only [structuralNumeratorCoefficient22,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient13,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient12]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_23 (s : ℚ) :
    structuralNumeratorCoefficient23 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient14 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient13 s := by
  simp only [structuralNumeratorCoefficient23,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient14,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient13]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_24 (s : ℚ) :
    structuralNumeratorCoefficient24 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient15 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient14 s := by
  simp only [structuralNumeratorCoefficient24,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient15,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient14]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_25 (s : ℚ) :
    structuralNumeratorCoefficient25 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient16 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient15 s := by
  simp only [structuralNumeratorCoefficient25,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient16,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient15]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_26 (s : ℚ) :
    structuralNumeratorCoefficient26 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient17 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient16 s := by
  simp only [structuralNumeratorCoefficient26,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient17,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient16]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_27 (s : ℚ) :
    structuralNumeratorCoefficient27 s =
      sutherlandPolynomialCoefficient0 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient18 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient17 s := by
  simp only [structuralNumeratorCoefficient27,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient18,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient17]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_28 (s : ℚ) :
    structuralNumeratorCoefficient28 s =
      sutherlandPolynomialCoefficient1 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient19 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient18 s := by
  simp only [structuralNumeratorCoefficient28,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient19,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient18]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_29 (s : ℚ) :
    structuralNumeratorCoefficient29 s =
      sutherlandPolynomialCoefficient2 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient20 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient19 s := by
  simp only [structuralNumeratorCoefficient29,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient20,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient19]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_30 (s : ℚ) :
    structuralNumeratorCoefficient30 s =
      sutherlandPolynomialCoefficient3 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient21 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient20 s := by
  simp only [structuralNumeratorCoefficient30,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient21,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient20]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_31 (s : ℚ) :
    structuralNumeratorCoefficient31 s =
      sutherlandPolynomialCoefficient4 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient22 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient21 s := by
  simp only [structuralNumeratorCoefficient31,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient22,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient21]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_32 (s : ℚ) :
    structuralNumeratorCoefficient32 s =
      sutherlandPolynomialCoefficient5 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient23 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient22 s := by
  simp only [structuralNumeratorCoefficient32,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient23,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient22]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_33 (s : ℚ) :
    structuralNumeratorCoefficient33 s =
      sutherlandPolynomialCoefficient6 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient24 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient23 s := by
  simp only [structuralNumeratorCoefficient33,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient24,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient23]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_34 (s : ℚ) :
    structuralNumeratorCoefficient34 s =
      sutherlandPolynomialCoefficient7 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient25 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient24 s := by
  simp only [structuralNumeratorCoefficient34,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient25,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_35 (s : ℚ) :
    structuralNumeratorCoefficient35 s =
      sutherlandPolynomialCoefficient8 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient26 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient25 s := by
  simp only [structuralNumeratorCoefficient35,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient26,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient25]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_36 (s : ℚ) :
    structuralNumeratorCoefficient36 s =
      sutherlandPolynomialCoefficient9 s *
          multiplierCoefficient27 s +
        sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient26 s := by
  simp only [structuralNumeratorCoefficient36,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient27,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient26]
  ring

/-- Checked coefficient identity for a staged polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_37 (s : ℚ) :
    structuralNumeratorCoefficient37 s =
      sutherlandPolynomialCoefficient10 s *
          multiplierCoefficient27 s := by
  simp only [structuralNumeratorCoefficient37,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient27]
  ring

/-- Checked staged polynomial-product identity. -/
theorem structuralNumerator_eq_sutherlandPolynomial_mul_multiplier (r s : ℚ) :
    structuralNumerator r s =
      sutherlandPolynomial r s * multiplier r s := by
  have h0 := structuralNumeratorCoefficient_product_certificate_0 s
  have h1 := structuralNumeratorCoefficient_product_certificate_1 s
  have h2 := structuralNumeratorCoefficient_product_certificate_2 s
  have h3 := structuralNumeratorCoefficient_product_certificate_3 s
  have h4 := structuralNumeratorCoefficient_product_certificate_4 s
  have h5 := structuralNumeratorCoefficient_product_certificate_5 s
  have h6 := structuralNumeratorCoefficient_product_certificate_6 s
  have h7 := structuralNumeratorCoefficient_product_certificate_7 s
  have h8 := structuralNumeratorCoefficient_product_certificate_8 s
  have h9 := structuralNumeratorCoefficient_product_certificate_9 s
  have h10 := structuralNumeratorCoefficient_product_certificate_10 s
  have h11 := structuralNumeratorCoefficient_product_certificate_11 s
  have h12 := structuralNumeratorCoefficient_product_certificate_12 s
  have h13 := structuralNumeratorCoefficient_product_certificate_13 s
  have h14 := structuralNumeratorCoefficient_product_certificate_14 s
  have h15 := structuralNumeratorCoefficient_product_certificate_15 s
  have h16 := structuralNumeratorCoefficient_product_certificate_16 s
  have h17 := structuralNumeratorCoefficient_product_certificate_17 s
  have h18 := structuralNumeratorCoefficient_product_certificate_18 s
  have h19 := structuralNumeratorCoefficient_product_certificate_19 s
  have h20 := structuralNumeratorCoefficient_product_certificate_20 s
  have h21 := structuralNumeratorCoefficient_product_certificate_21 s
  have h22 := structuralNumeratorCoefficient_product_certificate_22 s
  have h23 := structuralNumeratorCoefficient_product_certificate_23 s
  have h24 := structuralNumeratorCoefficient_product_certificate_24 s
  have h25 := structuralNumeratorCoefficient_product_certificate_25 s
  have h26 := structuralNumeratorCoefficient_product_certificate_26 s
  have h27 := structuralNumeratorCoefficient_product_certificate_27 s
  have h28 := structuralNumeratorCoefficient_product_certificate_28 s
  have h29 := structuralNumeratorCoefficient_product_certificate_29 s
  have h30 := structuralNumeratorCoefficient_product_certificate_30 s
  have h31 := structuralNumeratorCoefficient_product_certificate_31 s
  have h32 := structuralNumeratorCoefficient_product_certificate_32 s
  have h33 := structuralNumeratorCoefficient_product_certificate_33 s
  have h34 := structuralNumeratorCoefficient_product_certificate_34 s
  have h35 := structuralNumeratorCoefficient_product_certificate_35 s
  have h36 := structuralNumeratorCoefficient_product_certificate_36 s
  have h37 := structuralNumeratorCoefficient_product_certificate_37 s
  simp only [structuralNumerator, sutherlandPolynomial, multiplier]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 +
    r ^ 16 * h16 + r ^ 17 * h17 + r ^ 18 * h18 + r ^ 19 * h19 +
    r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 + r ^ 23 * h23 +
    r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 +
    r ^ 32 * h32 + r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 +
    r ^ 36 * h36 + r ^ 37 * h37

/-- The normalized cyclic unit relation vanishes on the raw curve. -/
theorem relation_eq_zero
    (r s : ℚ)
    (hCurve : sutherlandPolynomial r s = 0)
    (hA : rawUnitOneDenominator r s ≠ 0)
    (hB : rawUnitNineDenominator r s ≠ 0)
    (hC : rawUnitEightDenominator r s ≠ 0)
    (hD : rawUnitTwoDenominator r s ≠ 0) :
    rawUnitOneNumerator r s / rawUnitOneDenominator r s -
        rawUnitNineNumerator r s / rawUnitNineDenominator r s -
      (rawUnitOneNumerator r s / rawUnitOneDenominator r s) *
        (rawUnitEightNumerator r s / rawUnitEightDenominator r s) *
        (rawUnitTwoNumerator r s / rawUnitTwoDenominator r s -
          rawUnitOneNumerator r s / rawUnitOneDenominator r s) =
      0 := by
  have hStructural := structuralNumerator_eq_sutherlandPolynomial_mul_multiplier r s
  simp only [structuralNumerator_eq_linearCombination,
    t1Step1_eq_rawUnitOneNumerator_mul_rawUnitOneDenominator,
    t1Step2_eq_t1Step1_mul_rawUnitNineDenominator,
    t1Step3_eq_t1Step2_mul_rawUnitEightDenominator,
    termOne_eq_t1Step3_mul_rawUnitTwoDenominator,
    t2Step1_eq_rawUnitNineNumerator_mul_rawUnitOneDenominator,
    t2Step2_eq_t2Step1_mul_rawUnitOneDenominator,
    t2Step3_eq_t2Step2_mul_rawUnitEightDenominator,
    termTwo_eq_t2Step3_mul_rawUnitTwoDenominator,
    t3Step1_eq_rawUnitOneNumerator_mul_rawUnitEightNumerator,
    t3Step2_eq_t3Step1_mul_difference,
    termThree_eq_t3Step2_mul_rawUnitNineDenominator,
    difference_eq_linearCombination,
    differenceLeft_eq_rawUnitTwoNumerator_mul_rawUnitOneDenominator,
    differenceRight_eq_rawUnitOneNumerator_mul_rawUnitTwoDenominator] at hStructural
  rw [hCurve, zero_mul] at hStructural
  field_simp [hA, hB, hC, hD]
  linear_combination hStructural

end RelationZeroCertificate

end MazurTorsion.Kubert.OrderTwentyFiveRawOrbitData
