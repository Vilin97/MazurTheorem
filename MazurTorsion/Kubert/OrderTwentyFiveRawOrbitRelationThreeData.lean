/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveRawOrbitData

/-!
# Fourth exact raw-orbit certificate for order twenty-five

This coefficientwise certificate proves the fourth cyclic unit relation
used by the order-twenty-five Tate bridge. Exact polynomial division over
`ℚ` discovered the quotient; Lean checks every coefficient and staged
polynomial product.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawOrbitRelationThreeData

open OrderTwentyFiveRawOrbitData

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient0 (s : ℚ) : ℚ :=
  s ^ 7
    - s ^ 6
    + s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient1 (s : ℚ) : ℚ :=
  s ^ 7
    - 9 * s ^ 6
    + 9 * s ^ 5
    - 9 * s ^ 4
    + 11 * s ^ 3
    - 4 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient2 (s : ℚ) : ℚ :=
  s ^ 8
    - 6 * s ^ 7
    + 12 * s ^ 6
    - 3 * s ^ 5
    + 21 * s ^ 4
    - 30 * s ^ 3
    + 7 * s ^ 2
    - s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 7
    + 8 * s ^ 6
    + s ^ 5
    - 49 * s ^ 4
    + 36 * s ^ 3
    + 8 * s ^ 2
    - 7 * s
    + 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 7
    + 10 * s ^ 6
    - 34 * s ^ 5
    + 41 * s ^ 4
    + 16 * s ^ 3
    - 43 * s ^ 2
    + 21 * s
    - 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient5 (s : ℚ) : ℚ :=
  s ^ 6
    - 9 * s ^ 5
    + 32 * s ^ 4
    - 54 * s ^ 3
    + 40 * s ^ 2
    - 19 * s
    + 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 2
    + 4 * s
    - 3

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def t1Step1 (r s : ℚ) : ℚ :=
  t1Step1Coefficient0 s +
    t1Step1Coefficient1 s * r +
    t1Step1Coefficient2 s * r ^ 2 +
    t1Step1Coefficient3 s * r ^ 3 +
    t1Step1Coefficient4 s * r ^ 4 +
    t1Step1Coefficient5 s * r ^ 5 +
    t1Step1Coefficient6 s * r ^ 6

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_0 (s : ℚ) :
    t1Step1Coefficient0 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient0,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_1 (s : ℚ) :
    t1Step1Coefficient1 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient1,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_2 (s : ℚ) :
    t1Step1Coefficient2 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient2,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_3 (s : ℚ) :
    t1Step1Coefficient3 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient3,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_4 (s : ℚ) :
    t1Step1Coefficient4 s =
    rawUnitEightNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient1 s
    := by
  simp only [t1Step1Coefficient4,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_5 (s : ℚ) :
    t1Step1Coefficient5 s =
    rawUnitEightNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient2 s
    := by
  simp only [t1Step1Coefficient5,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_6 (s : ℚ) :
    t1Step1Coefficient6 s =
    rawUnitEightNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient3 s
    := by
  simp only [t1Step1Coefficient6,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step1_eq_rawUnitEightNumerator_mul_rawUnitEightDenominator (r s : ℚ) :
    t1Step1 r s = rawUnitEightNumerator r s * rawUnitEightDenominator r s := by
  have h0 := t1Step1Coefficient_product_certificate_0 s
  have h1 := t1Step1Coefficient_product_certificate_1 s
  have h2 := t1Step1Coefficient_product_certificate_2 s
  have h3 := t1Step1Coefficient_product_certificate_3 s
  have h4 := t1Step1Coefficient_product_certificate_4 s
  have h5 := t1Step1Coefficient_product_certificate_5 s
  have h6 := t1Step1Coefficient_product_certificate_6 s
  simp only [t1Step1, rawUnitEightNumerator, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient0 (s : ℚ) : ℚ :=
  s ^ 13
    - s ^ 12
    + s ^ 11
    - s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient1 (s : ℚ) : ℚ :=
  -2 * s ^ 15
    + 8 * s ^ 14
    - 13 * s ^ 13
    - 5 * s ^ 12
    + 13 * s ^ 11
    - 22 * s ^ 10
    + 31 * s ^ 9
    - 14 * s ^ 8
    + 5 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient2 (s : ℚ) : ℚ :=
  s ^ 17
    - 7 * s ^ 16
    + 17 * s ^ 15
    + 20 * s ^ 14
    - 170 * s ^ 13
    + 370 * s ^ 12
    - 371 * s ^ 11
    + 361 * s ^ 10
    - 231 * s ^ 9
    - 32 * s ^ 8
    + 84 * s ^ 7
    - 65 * s ^ 6
    + 29 * s ^ 5
    - 7 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient3 (s : ℚ) : ℚ :=
  5 * s ^ 17
    - 61 * s ^ 16
    + 317 * s ^ 15
    - 914 * s ^ 14
    + 1469 * s ^ 13
    - 1180 * s ^ 12
    + 7 * s ^ 11
    + 902 * s ^ 10
    - 2283 * s ^ 9
    + 3080 * s ^ 8
    - 2140 * s ^ 7
    + 1135 * s ^ 6
    - 417 * s ^ 5
    + 91 * s ^ 4
    - 10 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 19
    + 14 * s ^ 18
    - 92 * s ^ 17
    + 328 * s ^ 16
    - 530 * s ^ 15
    - 498 * s ^ 14
    + 4634 * s ^ 13
    - 11508 * s ^ 12
    + 17860 * s ^ 11
    - 22217 * s ^ 10
    + 25984 * s ^ 9
    - 22631 * s ^ 8
    + 13223 * s ^ 7
    - 6249 * s ^ 6
    + 1993 * s ^ 5
    - 320 * s ^ 4
    - 9 * s ^ 3
    + 19 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 19
    + 25 * s ^ 18
    - 254 * s ^ 17
    + 1509 * s ^ 16
    - 5884 * s ^ 15
    + 15917 * s ^ 14
    - 31095 * s ^ 13
    + 46728 * s ^ 12
    - 61209 * s ^ 11
    + 76520 * s ^ 10
    - 82707 * s ^ 9
    + 61530 * s ^ 8
    - 31466 * s ^ 7
    + 13265 * s ^ 6
    - 2754 * s ^ 5
    - 444 * s ^ 4
    + 458 * s ^ 3
    - 136 * s ^ 2
    - 2 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 20
    + 18 * s ^ 19
    - 155 * s ^ 18
    + 824 * s ^ 17
    - 2969 * s ^ 16
    + 7579 * s ^ 15
    - 14490 * s ^ 14
    + 23986 * s ^ 13
    - 42978 * s ^ 12
    + 80682 * s ^ 11
    - 120671 * s ^ 10
    + 118497 * s ^ 9
    - 66391 * s ^ 8
    + 22713 * s ^ 7
    - 4194 * s ^ 6
    - 6359 * s ^ 5
    + 5697 * s ^ 4
    - 2291 * s ^ 3
    + 476 * s ^ 2
    + 27 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 19
    - 32 * s ^ 18
    + 238 * s ^ 17
    - 1014 * s ^ 16
    + 2332 * s ^ 15
    - 470 * s ^ 14
    - 16093 * s ^ 13
    + 58951 * s ^ 12
    - 111603 * s ^ 11
    + 119926 * s ^ 10
    - 56666 * s ^ 9
    - 17379 * s ^ 8
    + 35536 * s ^ 7
    - 32376 * s ^ 6
    + 30999 * s ^ 5
    - 16945 * s ^ 4
    + 5601 * s ^ 3
    - 860 * s ^ 2
    - 146 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient8 (s : ℚ) : ℚ :=
  s ^ 19
    - 22 * s ^ 18
    + 226 * s ^ 17
    - 1443 * s ^ 16
    + 6313 * s ^ 15
    - 19530 * s ^ 14
    + 42139 * s ^ 13
    - 58277 * s ^ 12
    + 33833 * s ^ 11
    + 43823 * s ^ 10
    - 120853 * s ^ 9
    + 127908 * s ^ 8
    - 86969 * s ^ 7
    + 69420 * s ^ 6
    - 56834 * s ^ 5
    + 26964 * s ^ 4
    - 7683 * s ^ 3
    + 542 * s ^ 2
    + 433 * s
    + 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient9 (s : ℚ) : ℚ :=
  -s ^ 18
    + 21 * s ^ 17
    - 218 * s ^ 16
    + 1458 * s ^ 15
    - 6854 * s ^ 14
    + 23413 * s ^ 13
    - 58540 * s ^ 12
    + 105856 * s ^ 11
    - 133833 * s ^ 10
    + 112268 * s ^ 9
    - 65072 * s ^ 8
    + 52671 * s ^ 7
    - 72353 * s ^ 6
    + 60654 * s ^ 5
    - 24739 * s ^ 4
    + 5139 * s ^ 3
    + 944 * s ^ 2
    - 778 * s
    - 36

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient10 (s : ℚ) : ℚ :=
  -s ^ 16
    + 27 * s ^ 15
    - 300 * s ^ 14
    + 1912 * s ^ 13
    - 7900 * s ^ 12
    + 22106 * s ^ 11
    - 41392 * s ^ 10
    + 46486 * s ^ 9
    - 14931 * s ^ 8
    - 39996 * s ^ 7
    + 65785 * s ^ 6
    - 41449 * s ^ 5
    + 10549 * s ^ 4
    + 700 * s ^ 3
    - 2525 * s ^ 2
    + 846 * s
    + 83

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient11 (s : ℚ) : ℚ :=
  s ^ 15
    - 21 * s ^ 14
    + 205 * s ^ 13
    - 1240 * s ^ 12
    + 5168 * s ^ 11
    - 15499 * s ^ 10
    + 33774 * s ^ 9
    - 52546 * s ^ 8
    + 55406 * s ^ 7
    - 34794 * s ^ 6
    + 7893 * s ^ 5
    + 4011 * s ^ 4
    - 4281 * s ^ 3
    + 2524 * s ^ 2
    - 482 * s
    - 119

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient12 (s : ℚ) : ℚ :=
  -2 * s ^ 12
    + 35 * s ^ 11
    - 275 * s ^ 10
    + 1281 * s ^ 9
    - 3897 * s ^ 8
    + 7995 * s ^ 7
    - 11003 * s ^ 6
    + 9831 * s ^ 5
    - 5684 * s ^ 4
    + 2651 * s ^ 3
    - 1063 * s ^ 2
    + 25 * s
    + 106

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient13 (s : ℚ) : ℚ :=
  s ^ 9
    - 13 * s ^ 8
    + 70 * s ^ 7
    - 198 * s ^ 6
    + 291 * s ^ 5
    - 152 * s ^ 4
    - 68 * s ^ 3
    - s ^ 2
    + 124 * s
    - 54

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient14 (s : ℚ) : ℚ :=
  -s ^ 5
    + 10 * s ^ 4
    - 37 * s ^ 3
    + 62 * s ^ 2
    - 46 * s
    + 12

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
    t1Step2Coefficient14 s * r ^ 14

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_0 (s : ℚ) :
    t1Step2Coefficient0 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient0,
    t1Step1Coefficient0,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_1 (s : ℚ) :
    t1Step2Coefficient1 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient1 s
      + t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient1,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_2 (s : ℚ) :
    t1Step2Coefficient2 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient2 s
      + t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient1 s
      + t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient2,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_3 (s : ℚ) :
    t1Step2Coefficient3 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient3 s
      + t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient2 s
      + t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient1 s
      + t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient3,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_4 (s : ℚ) :
    t1Step2Coefficient4 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient4 s
      + t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient3 s
      + t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient2 s
      + t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient1 s
      + t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient4,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_5 (s : ℚ) :
    t1Step2Coefficient5 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient5 s
      + t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient4 s
      + t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient3 s
      + t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient2 s
      + t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient1 s
      + t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient5,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_6 (s : ℚ) :
    t1Step2Coefficient6 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient6 s
      + t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient5 s
      + t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient4 s
      + t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient3 s
      + t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient2 s
      + t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient1 s
      + t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient6,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_7 (s : ℚ) :
    t1Step2Coefficient7 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient7 s
      + t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient6 s
      + t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient5 s
      + t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient4 s
      + t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient3 s
      + t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient2 s
      + t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient1 s
    := by
  simp only [t1Step2Coefficient7,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_8 (s : ℚ) :
    t1Step2Coefficient8 s =
    t1Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient8 s
      + t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient7 s
      + t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient6 s
      + t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient5 s
      + t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient4 s
      + t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient3 s
      + t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient2 s
    := by
  simp only [t1Step2Coefficient8,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_9 (s : ℚ) :
    t1Step2Coefficient9 s =
    t1Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient8 s
      + t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient7 s
      + t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient6 s
      + t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient5 s
      + t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient4 s
      + t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient3 s
    := by
  simp only [t1Step2Coefficient9,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_10 (s : ℚ) :
    t1Step2Coefficient10 s =
    t1Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient8 s
      + t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient7 s
      + t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient6 s
      + t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient5 s
      + t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient4 s
    := by
  simp only [t1Step2Coefficient10,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_11 (s : ℚ) :
    t1Step2Coefficient11 s =
    t1Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient8 s
      + t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient7 s
      + t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient6 s
      + t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient5 s
    := by
  simp only [t1Step2Coefficient11,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_12 (s : ℚ) :
    t1Step2Coefficient12 s =
    t1Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient8 s
      + t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient7 s
      + t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient6 s
    := by
  simp only [t1Step2Coefficient12,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_13 (s : ℚ) :
    t1Step2Coefficient13 s =
    t1Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient8 s
      + t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient7 s
    := by
  simp only [t1Step2Coefficient13,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_14 (s : ℚ) :
    t1Step2Coefficient14 s =
    t1Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient8 s
    := by
  simp only [t1Step2Coefficient14,
    t1Step1Coefficient6,
    rawUnitFourDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step2_eq_t1Step1_mul_rawUnitFourDenominator (r s : ℚ) :
    t1Step2 r s = t1Step1 r s * rawUnitFourDenominator r s := by
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
  simp only [t1Step2, t1Step1, rawUnitFourDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient0 (s : ℚ) : ℚ :=
  s ^ 21
    - s ^ 20
    + s ^ 19
    - s ^ 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient1 (s : ℚ) : ℚ :=
  -2 * s ^ 23
    + 8 * s ^ 22
    - 10 * s ^ 21
    - 25 * s ^ 20
    + 43 * s ^ 19
    - 58 * s ^ 18
    + 67 * s ^ 17
    - 34 * s ^ 16
    + 15 * s ^ 15
    - 5 * s ^ 14
    + s ^ 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient2 (s : ℚ) : ℚ :=
  s ^ 25
    - 6 * s ^ 24
    + 4 * s ^ 23
    + 106 * s ^ 22
    - 443 * s ^ 21
    + 805 * s ^ 20
    - 562 * s ^ 19
    + 243 * s ^ 18
    + 278 * s ^ 17
    - 889 * s ^ 16
    + 813 * s ^ 15
    - 553 * s ^ 14
    + 296 * s ^ 13
    - 122 * s ^ 12
    + 36 * s ^ 11
    - 8 * s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 26
    + 28 * s ^ 25
    - 202 * s ^ 24
    + 836 * s ^ 23
    - 1958 * s ^ 22
    + 1709 * s ^ 21
    + 2963 * s ^ 20
    - 11046 * s ^ 19
    + 15885 * s ^ 18
    - 18986 * s ^ 17
    + 16959 * s ^ 16
    - 8648 * s ^ 15
    + 2680 * s ^ 14
    + 422 * s ^ 13
    - 1336 * s ^ 12
    + 1090 * s ^ 11
    - 558 * s ^ 10
    + 213 * s ^ 9
    - 58 * s ^ 8
    + 10 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient4 (s : ℚ) : ℚ :=
  s ^ 28
    - 14 * s ^ 27
    + 94 * s ^ 26
    - 352 * s ^ 25
    + 503 * s ^ 24
    + 2224 * s ^ 23
    - 16067 * s ^ 22
    + 49881 * s ^ 21
    - 92519 * s ^ 20
    + 109381 * s ^ 19
    - 85214 * s ^ 18
    + 44530 * s ^ 17
    + 23203 * s ^ 16
    - 83187 * s ^ 15
    + 89717 * s ^ 14
    - 71778 * s ^ 13
    + 46495 * s ^ 12
    - 24262 * s ^ 11
    + 9915 * s ^ 10
    - 3171 * s ^ 9
    + 692 * s ^ 8
    - 69 * s ^ 7
    - 6 * s ^ 6
    + 3 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient5 (s : ℚ) : ℚ :=
  5 * s ^ 28
    - 97 * s ^ 27
    + 895 * s ^ 26
    - 5261 * s ^ 25
    + 21672 * s ^ 24
    - 63936 * s ^ 23
    + 130211 * s ^ 22
    - 158225 * s ^ 21
    + 30045 * s ^ 20
    + 288286 * s ^ 19
    - 661715 * s ^ 18
    + 975664 * s ^ 17
    - 1227956 * s ^ 16
    + 1195956 * s ^ 15
    - 885889 * s ^ 14
    + 575220 * s ^ 13
    - 321306 * s ^ 12
    + 146151 * s ^ 11
    - 50722 * s ^ 10
    + 12190 * s ^ 9
    - 620 * s ^ 8
    - 822 * s ^ 7
    + 301 * s ^ 6
    - 44 * s ^ 5
    - 3 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 30
    + 20 * s ^ 29
    - 198 * s ^ 28
    + 1229 * s ^ 27
    - 5087 * s ^ 26
    + 13278 * s ^ 25
    - 11729 * s ^ 24
    - 73684 * s ^ 23
    + 428198 * s ^ 22
    - 1276081 * s ^ 21
    + 2584316 * s ^ 20
    - 3889420 * s ^ 19
    + 4782568 * s ^ 18
    - 5312505 * s ^ 17
    + 5270904 * s ^ 16
    - 4072382 * s ^ 15
    + 2543578 * s ^ 14
    - 1529394 * s ^ 13
    + 773152 * s ^ 12
    - 274871 * s ^ 11
    + 40163 * s ^ 10
    + 24891 * s ^ 9
    - 25907 * s ^ 8
    + 11086 * s ^ 7
    - 2309 * s ^ 6
    + 116 * s ^ 5
    + 68 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient7 (s : ℚ) : ℚ :=
  -s ^ 30
    + 33 * s ^ 29
    - 465 * s ^ 28
    + 4030 * s ^ 27
    - 24552 * s ^ 26
    + 112237 * s ^ 25
    - 397592 * s ^ 24
    + 1102976 * s ^ 23
    - 2386844 * s ^ 22
    + 3992736 * s ^ 21
    - 5205240 * s ^ 20
    + 5719928 * s ^ 19
    - 6276399 * s ^ 18
    + 6955758 * s ^ 17
    - 5922231 * s ^ 16
    + 2988766 * s ^ 15
    - 1368378 * s ^ 14
    + 1060656 * s ^ 13
    - 275433 * s ^ 12
    - 337076 * s ^ 11
    + 461791 * s ^ 10
    - 326525 * s ^ 9
    + 165145 * s ^ 8
    - 49234 * s ^ 7
    + 5007 * s ^ 6
    + 1553 * s ^ 5
    - 616 * s ^ 4
    - 30 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient8 (s : ℚ) : ℚ :=
  -s ^ 31
    + 24 * s ^ 30
    - 282 * s ^ 29
    + 2124 * s ^ 28
    - 11375 * s ^ 27
    + 45224 * s ^ 26
    - 133933 * s ^ 25
    + 280723 * s ^ 24
    - 332892 * s ^ 23
    - 129996 * s ^ 22
    + 1429322 * s ^ 21
    - 2717224 * s ^ 20
    + 1867518 * s ^ 19
    + 1343078 * s ^ 18
    - 2586515 * s ^ 17
    - 972327 * s ^ 16
    + 3700993 * s ^ 15
    - 1074486 * s ^ 14
    - 365049 * s ^ 13
    - 1688174 * s ^ 12
    + 2650226 * s ^ 11
    - 2110198 * s ^ 10
    + 1195840 * s ^ 9
    - 486558 * s ^ 8
    + 83718 * s ^ 7
    + 22166 * s ^ 6
    - 15117 * s ^ 5
    + 2802 * s ^ 4
    + 367 * s ^ 3
    + 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient9 (s : ℚ) : ℚ :=
  4 * s ^ 30
    - 89 * s ^ 29
    + 985 * s ^ 28
    - 7143 * s ^ 27
    + 37711 * s ^ 26
    - 151260 * s ^ 25
    + 461751 * s ^ 24
    - 1022137 * s ^ 23
    + 1366183 * s ^ 22
    + 46677 * s ^ 21
    - 4898844 * s ^ 20
    + 11270462 * s ^ 19
    - 11765970 * s ^ 18
    + 2264736 * s ^ 17
    + 6785648 * s ^ 16
    - 2724725 * s ^ 15
    - 4971304 * s ^ 14
    - 24021 * s ^ 13
    + 8477539 * s ^ 12
    - 8825015 * s ^ 11
    + 5554964 * s ^ 10
    - 2569606 * s ^ 9
    + 673705 * s ^ 8
    + 159278 * s ^ 7
    - 195151 * s ^ 6
    + 63631 * s ^ 5
    - 5454 * s ^ 4
    - 2512 * s ^ 3
    - 43 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient10 (s : ℚ) : ℚ :=
  s ^ 30
    - 31 * s ^ 29
    + 432 * s ^ 28
    - 3830 * s ^ 27
    + 24866 * s ^ 26
    - 126540 * s ^ 25
    + 517457 * s ^ 24
    - 1689973 * s ^ 23
    + 4264489 * s ^ 22
    - 7730818 * s ^ 21
    + 8178230 * s ^ 20
    + 849528 * s ^ 19
    - 18835838 * s ^ 18
    + 28946835 * s ^ 17
    - 13987028 * s ^ 16
    - 10205722 * s ^ 15
    + 7381537 * s ^ 14
    + 18791178 * s ^ 13
    - 28972556 * s ^ 12
    + 18758202 * s ^ 11
    - 8349771 * s ^ 10
    + 2263682 * s ^ 9
    + 774765 * s ^ 8
    - 1401395 * s ^ 7
    + 694573 * s ^ 6
    - 143889 * s ^ 5
    - 9772 * s ^ 4
    + 10980 * s ^ 3
    + 407 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient11 (s : ℚ) : ℚ :=
  -2 * s ^ 29
    + 45 * s ^ 28
    - 500 * s ^ 27
    + 3996 * s ^ 26
    - 27203 * s ^ 25
    + 162140 * s ^ 24
    - 804552 * s ^ 23
    + 3154314 * s ^ 22
    - 9405720 * s ^ 21
    + 20450646 * s ^ 20
    - 29737354 * s ^ 19
    + 21006894 * s ^ 18
    + 14299327 * s ^ 17
    - 48930360 * s ^ 16
    + 34849026 * s ^ 15
    + 25729817 * s ^ 14
    - 64586462 * s ^ 13
    + 46361114 * s ^ 12
    - 14470070 * s ^ 11
    + 353335 * s ^ 10
    + 4752676 * s ^ 9
    - 6113264 * s ^ 8
    + 4169326 * s ^ 7
    - 1376209 * s ^ 6
    + 92236 * s ^ 5
    + 101371 * s ^ 4
    - 32240 * s ^ 3
    - 2311 * s ^ 2
    - 16 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient12 (s : ℚ) : ℚ :=
  -3 * s ^ 28
    + 104 * s ^ 27
    - 1504 * s ^ 26
    + 12301 * s ^ 25
    - 61683 * s ^ 24
    + 171469 * s ^ 23
    - 7819 * s ^ 22
    - 2306276 * s ^ 21
    + 11702077 * s ^ 20
    - 33736492 * s ^ 19
    + 62612447 * s ^ 18
    - 68691401 * s ^ 17
    + 17437908 * s ^ 16
    + 74335207 * s ^ 15
    - 124995824 * s ^ 14
    + 83563073 * s ^ 13
    - 8242146 * s ^ 12
    - 23731190 * s ^ 11
    + 21537036 * s ^ 10
    - 18201424 * s ^ 9
    + 13979613 * s ^ 8
    - 6726262 * s ^ 7
    + 1123639 * s ^ 6
    + 499095 * s ^ 5
    - 343032 * s ^ 4
    + 62094 * s ^ 3
    + 8871 * s ^ 2
    + 122 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient13 (s : ℚ) : ℚ :=
  -s ^ 28
    + 43 * s ^ 27
    - 802 * s ^ 26
    + 8844 * s ^ 25
    - 65354 * s ^ 24
    + 342718 * s ^ 23
    - 1294797 * s ^ 22
    + 3407308 * s ^ 21
    - 5260460 * s ^ 20
    - 619291 * s ^ 19
    + 28620600 * s ^ 18
    - 85509366 * s ^ 17
    + 143068510 * s ^ 16
    - 140296042 * s ^ 15
    + 50859355 * s ^ 14
    + 57597562 * s ^ 13
    - 92988289 * s ^ 12
    + 61101160 * s ^ 11
    - 33201336 * s ^ 10
    + 25973490 * s ^ 9
    - 16827456 * s ^ 8
    + 4735898 * s ^ 7
    + 1637554 * s ^ 6
    - 1882576 * s ^ 5
    + 682260 * s ^ 4
    - 64818 * s ^ 3
    - 24124 * s ^ 2
    - 590 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient14 (s : ℚ) : ℚ :=
  3 * s ^ 27
    - 106 * s ^ 26
    + 1749 * s ^ 25
    - 18008 * s ^ 24
    + 129722 * s ^ 23
    - 690678 * s ^ 22
    + 2785256 * s ^ 21
    - 8529684 * s ^ 20
    + 19395571 * s ^ 19
    - 30343155 * s ^ 18
    + 23586059 * s ^ 17
    + 22813439 * s ^ 16
    - 102899326 * s ^ 15
    + 162090195 * s ^ 14
    - 143580398 * s ^ 13
    + 67523722 * s ^ 12
    - 14288739 * s ^ 11
    + 13006832 * s ^ 10
    - 19569362 * s ^ 9
    + 8620928 * s ^ 8
    + 3868520 * s ^ 7
    - 6486679 * s ^ 6
    + 3369058 * s ^ 5
    - 818706 * s ^ 4
    - 15097 * s ^ 3
    + 46899 * s ^ 2
    + 1984 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient15 (s : ℚ) : ℚ :=
  -3 * s ^ 26
    + 100 * s ^ 25
    - 1607 * s ^ 24
    + 16538 * s ^ 23
    - 121500 * s ^ 22
    + 670838 * s ^ 21
    - 2853835 * s ^ 20
    + 9441812 * s ^ 19
    - 24211347 * s ^ 18
    + 47204811 * s ^ 17
    - 66619219 * s ^ 16
    + 59136946 * s ^ 15
    - 12718315 * s ^ 14
    - 44904909 * s ^ 13
    + 62328300 * s ^ 12
    - 28099834 * s ^ 11
    - 9439818 * s ^ 10
    + 11084410 * s ^ 9
    + 6227626 * s ^ 8
    - 13941592 * s ^ 7
    + 9723415 * s ^ 6
    - 3469419 * s ^ 5
    + 439001 * s ^ 4
    + 176146 * s ^ 3
    - 63744 * s ^ 2
    - 4791 * s
    - 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient16 (s : ℚ) : ℚ :=
  s ^ 25
    - 35 * s ^ 24
    + 611 * s ^ 23
    - 6920 * s ^ 22
    + 55859 * s ^ 21
    - 336302 * s ^ 20
    + 1548792 * s ^ 19
    - 5529516 * s ^ 18
    + 15355036 * s ^ 17
    - 32895142 * s ^ 16
    + 52982586 * s ^ 15
    - 60213334 * s ^ 14
    + 39705383 * s ^ 13
    + 1097818 * s ^ 12
    - 29631545 * s ^ 11
    + 22652092 * s ^ 10
    + 4238722 * s ^ 9
    - 20037938 * s ^ 8
    + 17205561 * s ^ 7
    - 7884150 * s ^ 6
    + 1646443 * s ^ 5
    + 285933 * s ^ 4
    - 304304 * s ^ 3
    + 55935 * s ^ 2
    + 8369 * s
    + 45

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient17 (s : ℚ) : ℚ :=
  3 * s ^ 23
    - 104 * s ^ 22
    + 1669 * s ^ 21
    - 16565 * s ^ 20
    + 114255 * s ^ 19
    - 581564 * s ^ 18
    + 2257204 * s ^ 17
    - 6785867 * s ^ 16
    + 15834016 * s ^ 15
    - 28310151 * s ^ 14
    + 37376187 * s ^ 13
    - 32988390 * s ^ 12
    + 12381286 * s ^ 11
    + 12478713 * s ^ 10
    - 24723168 * s ^ 9
    + 20514044 * s ^ 8
    - 9930240 * s ^ 7
    + 2295640 * s ^ 6
    + 565011 * s ^ 5
    - 723846 * s ^ 4
    + 275248 * s ^ 3
    - 22793 * s ^ 2
    - 10469 * s
    - 119

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient18 (s : ℚ) : ℚ :=
  -s ^ 22
    + 32 * s ^ 21
    - 488 * s ^ 20
    + 4726 * s ^ 19
    - 32581 * s ^ 18
    + 169410 * s ^ 17
    - 685411 * s ^ 16
    + 2192123 * s ^ 15
    - 5572777 * s ^ 14
    + 11231167 * s ^ 13
    - 17757148 * s ^ 12
    + 21593020 * s ^ 11
    - 19522557 * s ^ 10
    + 12307934 * s ^ 9
    - 4501466 * s ^ 8
    - 163818 * s ^ 7
    + 1531393 * s ^ 6
    - 1213540 * s ^ 5
    + 542147 * s ^ 4
    - 121380 * s ^ 3
    - 10073 * s ^ 2
    + 9086 * s
    + 202

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient19 (s : ℚ) : ℚ :=
  2 * s ^ 19
    - 57 * s ^ 18
    + 758 * s ^ 17
    - 6246 * s ^ 16
    + 35666 * s ^ 15
    - 149317 * s ^ 14
    + 472346 * s ^ 13
    - 1145893 * s ^ 12
    + 2141960 * s ^ 11
    - 3080343 * s ^ 10
    + 3400020 * s ^ 9
    - 2899976 * s ^ 8
    + 1966064 * s ^ 7
    - 1098310 * s ^ 6
    + 486767 * s ^ 5
    - 135710 * s ^ 4
    - 1538 * s ^ 3
    + 19121 * s ^ 2
    - 5089 * s
    - 225

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient20 (s : ℚ) : ℚ :=
  -s ^ 16
    + 24 * s ^ 15
    - 261 * s ^ 14
    + 1695 * s ^ 13
    - 7273 * s ^ 12
    + 21462 * s ^ 11
    - 43715 * s ^ 10
    + 59510 * s ^ 9
    - 49387 * s ^ 8
    + 19634 * s ^ 7
    - 4363 * s ^ 6
    + 16035 * s ^ 5
    - 28208 * s ^ 4
    + 23141 * s ^ 3
    - 9986 * s ^ 2
    + 1533 * s
    + 160

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient21 (s : ℚ) : ℚ :=
  s ^ 12
    - 21 * s ^ 11
    + 195 * s ^ 10
    - 1053 * s ^ 9
    + 3662 * s ^ 8
    - 8588 * s ^ 7
    + 13841 * s ^ 6
    - 15389 * s ^ 5
    + 11756 * s ^ 4
    - 6021 * s ^ 3
    + 1777 * s ^ 2
    - 94 * s
    - 66

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient22 (s : ℚ) : ℚ :=
  -s ^ 5
    + 10 * s ^ 4
    - 37 * s ^ 3
    + 62 * s ^ 2
    - 46 * s
    + 12

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
    t1Step3Coefficient22 s * r ^ 22

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_0 (s : ℚ) :
    t1Step3Coefficient0 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient0,
    t1Step2Coefficient0,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_1 (s : ℚ) :
    t1Step3Coefficient1 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient1,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_2 (s : ℚ) :
    t1Step3Coefficient2 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient2,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_3 (s : ℚ) :
    t1Step3Coefficient3 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient3,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_4 (s : ℚ) :
    t1Step3Coefficient4 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient4,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_5 (s : ℚ) :
    t1Step3Coefficient5 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient5,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_6 (s : ℚ) :
    t1Step3Coefficient6 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient6,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_7 (s : ℚ) :
    t1Step3Coefficient7 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient7,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_8 (s : ℚ) :
    t1Step3Coefficient8 s =
    t1Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient8,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_9 (s : ℚ) :
    t1Step3Coefficient9 s =
    t1Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient9,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_10 (s : ℚ) :
    t1Step3Coefficient10 s =
    t1Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient10,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_11 (s : ℚ) :
    t1Step3Coefficient11 s =
    t1Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient11,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_12 (s : ℚ) :
    t1Step3Coefficient12 s =
    t1Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient12,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_13 (s : ℚ) :
    t1Step3Coefficient13 s =
    t1Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient13,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_14 (s : ℚ) :
    t1Step3Coefficient14 s =
    t1Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient14,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_15 (s : ℚ) :
    t1Step3Coefficient15 s =
    t1Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient1 s
    := by
  simp only [t1Step3Coefficient15,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_16 (s : ℚ) :
    t1Step3Coefficient16 s =
    t1Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient2 s
    := by
  simp only [t1Step3Coefficient16,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_17 (s : ℚ) :
    t1Step3Coefficient17 s =
    t1Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient3 s
    := by
  simp only [t1Step3Coefficient17,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_18 (s : ℚ) :
    t1Step3Coefficient18 s =
    t1Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient4 s
    := by
  simp only [t1Step3Coefficient18,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_19 (s : ℚ) :
    t1Step3Coefficient19 s =
    t1Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient5 s
    := by
  simp only [t1Step3Coefficient19,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_20 (s : ℚ) :
    t1Step3Coefficient20 s =
    t1Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient6 s
    := by
  simp only [t1Step3Coefficient20,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_21 (s : ℚ) :
    t1Step3Coefficient21 s =
    t1Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient7 s
    := by
  simp only [t1Step3Coefficient21,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_22 (s : ℚ) :
    t1Step3Coefficient22 s =
    t1Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient8 s
    := by
  simp only [t1Step3Coefficient22,
    t1Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step3_eq_t1Step2_mul_rawUnitTwoDenominator (r s : ℚ) :
    t1Step3 r s = t1Step2 r s * rawUnitTwoDenominator r s := by
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
  simp only [t1Step3, t1Step2, rawUnitTwoDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient0 (s : ℚ) : ℚ :=
  s ^ 29
    - s ^ 28
    + s ^ 27
    - s ^ 26

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 35
    + 4 * s ^ 34
    - 10 * s ^ 33
    + 20 * s ^ 32
    - 36 * s ^ 31
    + 62 * s ^ 30
    - 83 * s ^ 29
    + 37 * s ^ 28
    - 4 * s ^ 27
    - 34 * s ^ 26
    + 68 * s ^ 25
    - 34 * s ^ 24
    + 15 * s ^ 23
    - 5 * s ^ 22
    + s ^ 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient2 (s : ℚ) : ℚ :=
  2 * s ^ 37
    - 16 * s ^ 36
    + 57 * s ^ 35
    - 98 * s ^ 34
    + 106 * s ^ 33
    - 49 * s ^ 32
    - 139 * s ^ 31
    + 715 * s ^ 30
    - 2174 * s ^ 29
    + 4091 * s ^ 28
    - 4438 * s ^ 27
    + 4089 * s ^ 26
    - 2636 * s ^ 25
    + 408 * s ^ 24
    + 314 * s ^ 23
    - 413 * s ^ 22
    + 275 * s ^ 21
    - 123 * s ^ 20
    + 36 * s ^ 19
    - 8 * s ^ 18
    + s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 39
    + 13 * s ^ 38
    - 63 * s ^ 37
    + 78 * s ^ 36
    + 449 * s ^ 35
    - 2445 * s ^ 34
    + 6265 * s ^ 33
    - 12563 * s ^ 32
    + 23113 * s ^ 31
    - 39287 * s ^ 30
    + 53991 * s ^ 29
    - 46080 * s ^ 28
    + 8273 * s ^ 27
    + 30698 * s ^ 26
    - 67423 * s ^ 25
    + 79805 * s ^ 24
    - 55670 * s ^ 23
    + 30391 * s ^ 22
    - 12597 * s ^ 21
    + 3394 * s ^ 20
    - 172 * s ^ 19
    - 305 * s ^ 18
    + 185 * s ^ 17
    - 58 * s ^ 16
    + 10 * s ^ 15
    - s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient4 (s : ℚ) : ℚ :=
  -11 * s ^ 39
    + 204 * s ^ 38
    - 1647 * s ^ 37
    + 7558 * s ^ 36
    - 21717 * s ^ 35
    + 41793 * s ^ 34
    - 59556 * s ^ 33
    + 74929 * s ^ 32
    - 74227 * s ^ 31
    - 18951 * s ^ 30
    + 351378 * s ^ 29
    - 961971 * s ^ 28
    + 1548106 * s ^ 27
    - 1759486 * s ^ 26
    + 1604247 * s ^ 25
    - 1002501 * s ^ 24
    + 267959 * s ^ 23
    + 118859 * s ^ 22
    - 232853 * s ^ 21
    + 195863 * s ^ 20
    - 114755 * s ^ 19
    + 50417 * s ^ 18
    - 17451 * s ^ 17
    + 4555 * s ^ 16
    - 847 * s ^ 15
    + 114 * s ^ 14
    - 10 * s ^ 13
    + s ^ 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 42
    + 20 * s ^ 41
    - 205 * s ^ 40
    + 1381 * s ^ 39
    - 6350 * s ^ 38
    + 18864 * s ^ 37
    - 28344 * s ^ 36
    - 22182 * s ^ 35
    + 232429 * s ^ 34
    - 680187 * s ^ 33
    + 1495735 * s ^ 32
    - 3174215 * s ^ 31
    + 6401920 * s ^ 30
    - 10935850 * s ^ 29
    + 14320998 * s ^ 28
    - 13257845 * s ^ 27
    + 7484186 * s ^ 26
    + 616633 * s ^ 25
    - 8869516 * s ^ 24
    + 12733120 * s ^ 23
    - 10971627 * s ^ 22
    + 7321537 * s ^ 21
    - 3871213 * s ^ 20
    + 1546440 * s ^ 19
    - 398165 * s ^ 18
    + 11971 * s ^ 17
    + 55507 * s ^ 16
    - 35429 * s ^ 15
    + 13496 * s ^ 14
    - 3805 * s ^ 13
    + 822 * s ^ 12
    - 140 * s ^ 11
    + 16 * s ^ 10
    - s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient6 (s : ℚ) : ℚ :=
  -2 * s ^ 43
    + 34 * s ^ 42
    - 255 * s ^ 41
    + 916 * s ^ 40
    + 736 * s ^ 39
    - 29456 * s ^ 38
    + 190042 * s ^ 37
    - 740442 * s ^ 36
    + 2025826 * s ^ 35
    - 4261539 * s ^ 34
    + 7857607 * s ^ 33
    - 14506422 * s ^ 32
    + 26047729 * s ^ 31
    - 38205411 * s ^ 30
    + 35723112 * s ^ 29
    - 351227 * s ^ 28
    - 67361998 * s ^ 27
    + 141208490 * s ^ 26
    - 193459258 * s ^ 25
    + 204416813 * s ^ 24
    - 161255340 * s ^ 23
    + 92906757 * s ^ 22
    - 38669849 * s ^ 21
    + 6339123 * s ^ 20
    + 6921028 * s ^ 19
    - 8467407 * s ^ 18
    + 5661022 * s ^ 17
    - 2815541 * s ^ 16
    + 1088320 * s ^ 15
    - 329715 * s ^ 14
    + 78874 * s ^ 13
    - 14246 * s ^ 12
    + 1737 * s ^ 11
    - 35 * s ^ 10
    - 27 * s ^ 9
    + 4 * s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient7 (s : ℚ) : ℚ :=
  -14 * s ^ 43
    + 342 * s ^ 42
    - 3941 * s ^ 41
    + 28758 * s ^ 40
    - 148168 * s ^ 39
    + 561498 * s ^ 38
    - 1571874 * s ^ 37
    + 3200310 * s ^ 36
    - 4718254 * s ^ 35
    + 5758049 * s ^ 34
    - 8425452 * s ^ 33
    + 10461117 * s ^ 32
    + 18788856 * s ^ 31
    - 152548980 * s ^ 30
    + 459730830 * s ^ 29
    - 908182350 * s ^ 28
    + 1325475874 * s ^ 27
    - 1514654688 * s ^ 26
    + 1386797221 * s ^ 25
    - 947492628 * s ^ 24
    + 338486569 * s ^ 23
    + 135548569 * s ^ 22
    - 336327457 * s ^ 21
    + 350305880 * s ^ 20
    - 267194692 * s ^ 19
    + 162091424 * s ^ 18
    - 80323219 * s ^ 17
    + 32845863 * s ^ 16
    - 10759155 * s ^ 15
    + 2710947 * s ^ 14
    - 484914 * s ^ 13
    + 37784 * s ^ 12
    + 10088 * s ^ 11
    - 5033 * s ^ 10
    + 900 * s ^ 9
    - 54 * s ^ 8
    - 6 * s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient8 (s : ℚ) : ℚ :=
  2 * s ^ 45
    - 54 * s ^ 44
    + 702 * s ^ 43
    - 5638 * s ^ 42
    + 30270 * s ^ 41
    - 107970 * s ^ 40
    + 209626 * s ^ 39
    + 179556 * s ^ 38
    - 3021721 * s ^ 37
    + 12267841 * s ^ 36
    - 32104267 * s ^ 35
    + 68871305 * s ^ 34
    - 161338415 * s ^ 33
    + 448589418 * s ^ 32
    - 1182472128 * s ^ 31
    + 2526722632 * s ^ 30
    - 4203259879 * s ^ 29
    + 5396919002 * s ^ 28
    - 5227342140 * s ^ 27
    + 3414805520 * s ^ 26
    - 353282363 * s ^ 25
    - 3126945894 * s ^ 24
    + 5675936855 * s ^ 23
    - 6216824829 * s ^ 22
    + 5217757577 * s ^ 21
    - 3721465740 * s ^ 20
    + 2268053606 * s ^ 19
    - 1165694896 * s ^ 18
    + 498370933 * s ^ 17
    - 172013038 * s ^ 16
    + 43091453 * s ^ 15
    - 5546429 * s ^ 14
    - 1044183 * s ^ 13
    + 917948 * s ^ 12
    - 317465 * s ^ 11
    + 70065 * s ^ 10
    - 7013 * s ^ 9
    - 419 * s ^ 8
    + 166 * s ^ 7
    + 4 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient9 (s : ℚ) : ℚ :=
  s ^ 46
    - 22 * s ^ 45
    + 189 * s ^ 44
    - 400 * s ^ 43
    - 7541 * s ^ 42
    + 96173 * s ^ 41
    - 638311 * s ^ 40
    + 2922216 * s ^ 39
    - 9996860 * s ^ 38
    + 26846464 * s ^ 37
    - 62164008 * s ^ 36
    + 151532621 * s ^ 35
    - 442162762 * s ^ 34
    + 1313700589 * s ^ 33
    - 3284762331 * s ^ 32
    + 6364779130 * s ^ 31
    - 9119649527 * s ^ 30
    + 8653994723 * s ^ 29
    - 2328683894 * s ^ 28
    - 10027997615 * s ^ 27
    + 25749821887 * s ^ 26
    - 40792038631 * s ^ 25
    + 50335223735 * s ^ 24
    - 50027192660 * s ^ 23
    + 40676055771 * s ^ 22
    - 28467342130 * s ^ 21
    + 17727561079 * s ^ 20
    - 9484863228 * s ^ 19
    + 4174713309 * s ^ 18
    - 1416174943 * s ^ 17
    + 290954435 * s ^ 16
    + 34470572 * s ^ 15
    - 61680842 * s ^ 14
    + 30943542 * s ^ 13
    - 10356141 * s ^ 12
    + 2446979 * s ^ 11
    - 351480 * s ^ 10
    - 12654 * s ^ 9
    + 14491 * s ^ 8
    - 1781 * s ^ 7
    - 144 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient10 (s : ℚ) : ℚ :=
  4 * s ^ 46
    - 127 * s ^ 45
    + 1874 * s ^ 44
    - 17101 * s ^ 43
    + 107567 * s ^ 42
    - 489936 * s ^ 41
    + 1656075 * s ^ 40
    - 4326602 * s ^ 39
    + 10602778 * s ^ 38
    - 37040590 * s ^ 37
    + 171237048 * s ^ 36
    - 695213496 * s ^ 35
    + 2133621882 * s ^ 34
    - 4734641389 * s ^ 33
    + 6929953654 * s ^ 32
    - 3668241326 * s ^ 31
    - 12698412351 * s ^ 30
    + 47516018719 * s ^ 29
    - 98407829191 * s ^ 28
    + 155052495913 * s ^ 27
    - 203941831438 * s ^ 26
    + 231323250913 * s ^ 25
    - 224594880201 * s ^ 24
    + 183005843168 * s ^ 23
    - 126761153222 * s ^ 22
    + 78641154398 * s ^ 21
    - 43403144875 * s ^ 20
    + 18902612591 * s ^ 19
    - 5161937635 * s ^ 18
    - 388049250 * s ^ 17
    + 1581646505 * s ^ 16
    - 1181717911 * s ^ 15
    + 558537519 * s ^ 14
    - 190722776 * s ^ 13
    + 48209730 * s ^ 12
    - 7544140 * s ^ 11
    - 211573 * s ^ 10
    + 586333 * s ^ 9
    - 140869 * s ^ 8
    + 6988 * s ^ 7
    + 2295 * s ^ 6
    + 45 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient11 (s : ℚ) : ℚ :=
  s ^ 47
    - 27 * s ^ 46
    + 310 * s ^ 45
    - 1765 * s ^ 44
    + 2351 * s ^ 43
    + 39007 * s ^ 42
    - 301998 * s ^ 41
    + 729210 * s ^ 40
    + 3638118 * s ^ 39
    - 43939682 * s ^ 38
    + 229030270 * s ^ 37
    - 767724700 * s ^ 36
    + 1638827453 * s ^ 35
    - 1250581996 * s ^ 34
    - 6112723628 * s ^ 33
    + 31996074071 * s ^ 32
    - 90271389731 * s ^ 31
    + 187136910976 * s ^ 30
    - 312284828686 * s ^ 29
    + 441476672472 * s ^ 28
    - 547374103770 * s ^ 27
    + 603327652096 * s ^ 26
    - 581208691418 * s ^ 25
    + 470522239810 * s ^ 24
    - 312881535384 * s ^ 23
    + 179347434064 * s ^ 22
    - 94598539734 * s ^ 21
    + 35730531450 * s ^ 20
    + 4222865409 * s ^ 19
    - 19682032140 * s ^ 18
    + 18715286270 * s ^ 17
    - 12163424096 * s ^ 16
    + 5984825880 * s ^ 15
    - 2166130809 * s ^ 14
    + 557584209 * s ^ 13
    - 81936919 * s ^ 12
    - 11395693 * s ^ 11
    + 13017089 * s ^ 10
    - 4780899 * s ^ 9
    + 687557 * s ^ 8
    + 37296 * s ^ 7
    - 21402 * s ^ 6
    - 890 * s ^ 5
    - 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient12 (s : ℚ) : ℚ :=
  s ^ 47
    - 36 * s ^ 46
    + 529 * s ^ 45
    - 3822 * s ^ 44
    + 6598 * s ^ 43
    + 147151 * s ^ 42
    - 1768327 * s ^ 41
    + 11160206 * s ^ 40
    - 45734540 * s ^ 39
    + 110706210 * s ^ 38
    + 8365950 * s ^ 37
    - 1546459394 * s ^ 36
    + 8667762536 * s ^ 35
    - 31031587536 * s ^ 34
    + 83931641535 * s ^ 33
    - 181376759009 * s ^ 32
    + 323123742259 * s ^ 31
    - 488086629265 * s ^ 30
    + 645515641335 * s ^ 29
    - 770686997577 * s ^ 28
    + 836814116174 * s ^ 27
    - 794389485534 * s ^ 26
    + 601965890182 * s ^ 25
    - 314661481424 * s ^ 24
    + 84929270036 * s ^ 23
    + 7792540926 * s ^ 22
    - 46679412966 * s ^ 21
    + 105145374036 * s ^ 20
    - 139822846089 * s ^ 19
    + 120233880892 * s ^ 18
    - 77910875205 * s ^ 17
    + 40221162924 * s ^ 16
    - 15753553339 * s ^ 15
    + 3968974414 * s ^ 14
    - 291902605 * s ^ 13
    - 301296054 * s ^ 12
    + 212454047 * s ^ 11
    - 85471773 * s ^ 10
    + 21122347 * s ^ 9
    - 1156394 * s ^ 8
    - 677639 * s ^ 7
    + 127637 * s ^ 6
    + 10533 * s ^ 5
    + 70 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient13 (s : ℚ) : ℚ :=
  2 * s ^ 47
    - 81 * s ^ 46
    + 1495 * s ^ 45
    - 16227 * s ^ 44
    + 108647 * s ^ 43
    - 364116 * s ^ 42
    - 996209 * s ^ 41
    + 23069761 * s ^ 40
    - 180983777 * s ^ 39
    + 971965362 * s ^ 38
    - 4025899518 * s ^ 37
    + 13410018372 * s ^ 36
    - 36533048154 * s ^ 35
    + 81918007446 * s ^ 34
    - 151622908054 * s ^ 33
    + 233285454160 * s ^ 32
    - 305614656889 * s ^ 31
    + 360999077816 * s ^ 30
    - 414095738039 * s ^ 29
    + 458047848498 * s ^ 28
    - 408075560855 * s ^ 27
    + 156499364932 * s ^ 26
    + 242760876097 * s ^ 25
    - 517796691157 * s ^ 24
    + 482077049529 * s ^ 23
    - 333304584799 * s ^ 22
    + 365510916647 * s ^ 21
    - 501524198995 * s ^ 20
    + 491894190147 * s ^ 19
    - 338881311179 * s ^ 18
    + 180835004853 * s ^ 17
    - 73524820435 * s ^ 16
    + 17023782549 * s ^ 15
    + 2671279628 * s ^ 14
    - 4464371698 * s ^ 13
    + 2481072440 * s ^ 12
    - 1021562255 * s ^ 11
    + 312654366 * s ^ 10
    - 50298975 * s ^ 9
    - 7855684 * s ^ 8
    + 4685203 * s ^ 7
    - 474847 * s ^ 6
    - 84865 * s ^ 5
    - 1141 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient14 (s : ℚ) : ℚ :=
  4 * s ^ 47
    - 187 * s ^ 46
    + 4198 * s ^ 45
    - 60076 * s ^ 44
    + 614835 * s ^ 43
    - 4789683 * s ^ 42
    + 29499409 * s ^ 41
    - 147008187 * s ^ 40
    + 599998248 * s ^ 39
    - 2009359447 * s ^ 38
    + 5466772145 * s ^ 37
    - 11745915738 * s ^ 36
    + 18597320732 * s ^ 35
    - 17254702915 * s ^ 34
    - 4939312876 * s ^ 33
    + 47191536146 * s ^ 32
    - 73748216124 * s ^ 31
    + 32731857383 * s ^ 30
    + 54853540627 * s ^ 29
    - 21254188491 * s ^ 28
    - 328042161015 * s ^ 27
    + 902396475191 * s ^ 26
    - 1227576876564 * s ^ 25
    + 951968432354 * s ^ 24
    - 465788643046 * s ^ 23
    + 523997274977 * s ^ 22
    - 1113385462692 * s ^ 21
    + 1426958429110 * s ^ 20
    - 1107542495351 * s ^ 19
    + 581898206054 * s ^ 18
    - 216130642213 * s ^ 17
    + 27891230523 * s ^ 16
    + 40157473833 * s ^ 15
    - 40021115499 * s ^ 14
    + 21062293305 * s ^ 13
    - 8469870016 * s ^ 12
    + 2881555237 * s ^ 11
    - 672336692 * s ^ 10
    - 3206403 * s ^ 9
    + 72947182 * s ^ 8
    - 20336690 * s ^ 7
    + 728336 * s ^ 6
    + 498412 * s ^ 5
    + 11635 * s ^ 4
    + 29 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient15 (s : ℚ) : ℚ :=
  s ^ 48
    - 42 * s ^ 47
    + 850 * s ^ 46
    - 10941 * s ^ 45
    + 99539 * s ^ 44
    - 670931 * s ^ 43
    + 3383786 * s ^ 42
    - 12231510 * s ^ 41
    + 24979173 * s ^ 40
    + 33737279 * s ^ 39
    - 575312613 * s ^ 38
    + 2979979916 * s ^ 37
    - 10257605658 * s ^ 36
    + 25565689454 * s ^ 35
    - 44391543356 * s ^ 34
    + 40755349628 * s ^ 33
    + 33088622039 * s ^ 32
    - 196021279917 * s ^ 31
    + 338501524720 * s ^ 30
    - 196693852437 * s ^ 29
    - 423076370664 * s ^ 28
    + 1250772107811 * s ^ 27
    - 1527411818723 * s ^ 26
    + 800287577325 * s ^ 25
    + 144655025333 * s ^ 24
    + 179637996556 * s ^ 23
    - 1936142414086 * s ^ 22
    + 3325252060895 * s ^ 21
    - 2907924928565 * s ^ 20
    + 1430182718639 * s ^ 19
    - 309458134013 * s ^ 18
    - 152780075989 * s ^ 17
    + 273019280070 * s ^ 16
    - 229654069249 * s ^ 15
    + 127383166145 * s ^ 14
    - 50778414700 * s ^ 13
    + 17174744695 * s ^ 12
    - 4839345925 * s ^ 11
    + 393731356 * s ^ 10
    + 573887867 * s ^ 9
    - 327331888 * s ^ 8
    + 58640125 * s ^ 7
    + 3407038 * s ^ 6
    - 2214848 * s ^ 5
    - 83779 * s ^ 4
    - 406 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient16 (s : ℚ) : ℚ :=
  -5 * s ^ 47
    + 200 * s ^ 46
    - 3901 * s ^ 45
    + 49167 * s ^ 44
    - 447505 * s ^ 43
    + 3110081 * s ^ 42
    - 16950058 * s ^ 41
    + 72582229 * s ^ 40
    - 235641780 * s ^ 39
    + 499623555 * s ^ 38
    - 96371787 * s ^ 37
    - 4718031764 * s ^ 36
    + 24590259046 * s ^ 35
    - 77612299472 * s ^ 34
    + 171263897298 * s ^ 33
    - 251928092396 * s ^ 32
    + 154398002313 * s ^ 31
    + 333527644984 * s ^ 30
    - 1192167014483 * s ^ 29
    + 1859634846159 * s ^ 28
    - 1442879629540 * s ^ 27
    - 232159413999 * s ^ 26
    + 1641807257184 * s ^ 25
    - 494521214392 * s ^ 24
    - 3359696219469 * s ^ 23
    + 6648248566258 * s ^ 22
    - 6083591632915 * s ^ 21
    + 2536532097231 * s ^ 20
    + 455534782899 * s ^ 19
    - 1373627543285 * s ^ 18
    + 1223699416517 * s ^ 17
    - 891854641379 * s ^ 16
    + 522386788404 * s ^ 15
    - 219555820205 * s ^ 14
    + 67173165725 * s ^ 13
    - 18114560633 * s ^ 12
    + 2139797839 * s ^ 11
    + 3146011777 * s ^ 10
    - 2744704653 * s ^ 9
    + 980625723 * s ^ 8
    - 95390515 * s ^ 7
    - 30920782 * s ^ 6
    + 7562291 * s ^ 5
    + 454379 * s ^ 4
    + 3659 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient17 (s : ℚ) : ℚ :=
  -s ^ 47
    + 53 * s ^ 46
    - 1295 * s ^ 45
    + 19945 * s ^ 44
    - 220469 * s ^ 43
    + 1876606 * s ^ 42
    - 12825019 * s ^ 41
    + 72046325 * s ^ 40
    - 335619031 * s ^ 39
    + 1288916942 * s ^ 38
    - 3977630211 * s ^ 37
    + 9207023681 * s ^ 36
    - 12402461390 * s ^ 35
    - 10449153012 * s ^ 34
    + 121140026804 * s ^ 33
    - 407089560814 * s ^ 32
    + 875838199947 * s ^ 31
    - 1255386315124 * s ^ 30
    + 918310126144 * s ^ 29
    + 670995115291 * s ^ 28
    - 2943059774903 * s ^ 27
    + 3653370603344 * s ^ 26
    - 354533855728 * s ^ 25
    - 6307666378097 * s ^ 24
    + 11292825338459 * s ^ 23
    - 9534721799296 * s ^ 22
    + 2212194456576 * s ^ 21
    + 4118919142751 * s ^ 20
    - 5468441295436 * s ^ 19
    + 3841695301801 * s ^ 18
    - 2309037908805 * s ^ 17
    + 1367315243435 * s ^ 16
    - 625552243706 * s ^ 15
    + 166189642958 * s ^ 14
    - 15614643771 * s ^ 13
    - 6832134259 * s ^ 12
    + 14692089414 * s ^ 11
    - 15026290169 * s ^ 10
    + 8033058874 * s ^ 9
    - 2012720638 * s ^ 8
    - 47474801 * s ^ 7
    + 133694764 * s ^ 6
    - 19666499 * s ^ 5
    - 1927810 * s ^ 4
    - 23829 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient18 (s : ℚ) : ℚ :=
  3 * s ^ 46
    - 130 * s ^ 45
    + 2762 * s ^ 44
    - 38851 * s ^ 43
    + 411389 * s ^ 42
    - 3517122 * s ^ 41
    + 25199407 * s ^ 40
    - 153545052 * s ^ 39
    + 795753453 * s ^ 38
    - 3479734035 * s ^ 37
    + 12668479170 * s ^ 36
    - 37592798599 * s ^ 35
    + 87308884187 * s ^ 34
    - 142831478746 * s ^ 33
    + 95007370931 * s ^ 32
    + 307024529525 * s ^ 31
    - 1344060655017 * s ^ 30
    + 2884571702099 * s ^ 29
    - 3783816506217 * s ^ 28
    + 1954981807955 * s ^ 27
    + 3921785096633 * s ^ 26
    - 11673829139521 * s ^ 25
    + 15205337183184 * s ^ 24
    - 9382084024685 * s ^ 23
    - 3216259872654 * s ^ 22
    + 12994495715853 * s ^ 21
    - 13463927361425 * s ^ 20
    + 7977119513670 * s ^ 19
    - 3467934283217 * s ^ 18
    + 1784538398845 * s ^ 17
    - 954786707158 * s ^ 16
    + 180437329376 * s ^ 15
    + 150175674051 * s ^ 14
    - 122387327657 * s ^ 13
    + 67189906768 * s ^ 12
    - 57487681140 * s ^ 11
    + 40862954877 * s ^ 10
    - 16542979787 * s ^ 9
    + 2326071158 * s ^ 8
    + 882905467 * s ^ 7
    - 400740069 * s ^ 6
    + 36837897 * s ^ 5
    + 6543296 * s ^ 4
    + 119102 * s ^ 3
    + 24 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient19 (s : ℚ) : ℚ :=
  s ^ 45
    - 74 * s ^ 44
    + 2029 * s ^ 43
    - 30579 * s ^ 42
    + 283425 * s ^ 41
    - 1523944 * s ^ 40
    + 1467435 * s ^ 39
    + 56945495 * s ^ 38
    - 634159236 * s ^ 37
    + 4153461955 * s ^ 36
    - 19863698260 * s ^ 35
    + 73684481419 * s ^ 34
    - 215691577918 * s ^ 33
    + 492767406663 * s ^ 32
    - 829463295753 * s ^ 31
    + 808365336812 * s ^ 30
    + 453641303735 * s ^ 29
    - 3872885255709 * s ^ 28
    + 9094475805417 * s ^ 27
    - 13074115594607 * s ^ 26
    + 10756659873759 * s ^ 25
    + 540284113705 * s ^ 24
    - 16015316764968 * s ^ 23
    + 24888127438278 * s ^ 22
    - 20635651031278 * s ^ 21
    + 8784601500459 * s ^ 20
    - 339394876034 * s ^ 19
    - 1060700479876 * s ^ 18
    + 43915147758 * s ^ 17
    - 176521095598 * s ^ 16
    + 689053666436 * s ^ 15
    - 577250919584 * s ^ 14
    + 269335852183 * s ^ 13
    - 160098896597 * s ^ 12
    + 136591939403 * s ^ 11
    - 79923111400 * s ^ 10
    + 22937912393 * s ^ 9
    + 1288541510 * s ^ 8
    - 3267963946 * s ^ 7
    + 894934963 * s ^ 6
    - 38690788 * s ^ 5
    - 17975730 * s ^ 4
    - 473081 * s ^ 3
    - 273 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient20 (s : ℚ) : ℚ :=
  s ^ 45
    - 64 * s ^ 44
    + 1876 * s ^ 43
    - 33877 * s ^ 42
    + 425432 * s ^ 41
    - 3957310 * s ^ 40
    + 28217254 * s ^ 39
    - 156515210 * s ^ 38
    + 671301994 * s ^ 37
    - 2128787842 * s ^ 36
    + 4137240948 * s ^ 35
    + 1563201797 * s ^ 34
    - 52402256564 * s ^ 33
    + 255024418528 * s ^ 32
    - 814104025050 * s ^ 31
    + 1947210065463 * s ^ 30
    - 3541114366249 * s ^ 29
    + 4576295522354 * s ^ 28
    - 2862345833171 * s ^ 27
    - 3876298901331 * s ^ 26
    + 15170310266623 * s ^ 25
    - 25395732973167 * s ^ 24
    + 26144997912488 * s ^ 23
    - 14300127029555 * s ^ 22
    - 2250548437320 * s ^ 21
    + 11054843247895 * s ^ 20
    - 8527025186764 * s ^ 19
    + 2460409293394 * s ^ 18
    - 249551873387 * s ^ 17
    + 1102650301856 * s ^ 16
    - 1422786803810 * s ^ 15
    + 779534066058 * s ^ 14
    - 346409960426 * s ^ 13
    + 300068685712 * s ^ 12
    - 249167178205 * s ^ 11
    + 112361757742 * s ^ 10
    - 12818396744 * s ^ 9
    - 13710844326 * s ^ 8
    + 7799911212 * s ^ 7
    - 1485944230 * s ^ 6
    - 28129052 * s ^ 5
    + 40068194 * s ^ 4
    + 1524874 * s ^ 3
    + 1959 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient21 (s : ℚ) : ℚ :=
  -4 * s ^ 44
    + 221 * s ^ 43
    - 5830 * s ^ 42
    + 97914 * s ^ 41
    - 1175949 * s ^ 40
    + 10741182 * s ^ 39
    - 77398144 * s ^ 38
    + 449952651 * s ^ 37
    - 2137304268 * s ^ 36
    + 8328879110 * s ^ 35
    - 26450066718 * s ^ 34
    + 66667977574 * s ^ 33
    - 122902229742 * s ^ 32
    + 112060114674 * s ^ 31
    + 237698339749 * s ^ 30
    - 1474569619912 * s ^ 29
    + 4256112494075 * s ^ 28
    - 8636576000075 * s ^ 27
    + 12929987668970 * s ^ 26
    - 13324798426782 * s ^ 25
    + 6087098619952 * s ^ 24
    + 7796831329752 * s ^ 23
    - 20290954617887 * s ^ 22
    + 21935079105325 * s ^ 21
    - 12071685635353 * s ^ 20
    + 667834981253 * s ^ 19
    + 3025313313364 * s ^ 18
    - 267992005104 * s ^ 17
    - 2113099079540 * s ^ 16
    + 1673212539412 * s ^ 15
    - 632378204705 * s ^ 14
    + 428581445573 * s ^ 13
    - 509070775015 * s ^ 12
    + 344648469265 * s ^ 11
    - 90200512729 * s ^ 10
    - 32747353406 * s ^ 9
    + 37377605970 * s ^ 8
    - 13501748025 * s ^ 7
    + 1687609600 * s ^ 6
    + 236794577 * s ^ 5
    - 71873862 * s ^ 4
    - 4037155 * s ^ 3
    - 9958 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient22 (s : ℚ) : ℚ :=
  6 * s ^ 43
    - 314 * s ^ 42
    + 7965 * s ^ 41
    - 130271 * s ^ 40
    + 1541054 * s ^ 39
    - 14020119 * s ^ 38
    + 101842168 * s ^ 37
    - 605395414 * s ^ 36
    + 2994658998 * s ^ 35
    - 12465626090 * s ^ 34
    + 43954072916 * s ^ 33
    - 131492364070 * s ^ 32
    + 331892450469 * s ^ 31
    - 693559262364 * s ^ 30
    + 1140571478509 * s ^ 29
    - 1250053999193 * s ^ 28
    + 62314283492 * s ^ 27
    + 3646044764458 * s ^ 26
    - 10148342747889 * s ^ 25
    + 17048373848697 * s ^ 24
    - 19228824067507 * s ^ 23
    + 12669473980335 * s ^ 22
    + 66448049877 * s ^ 21
    - 9878493834009 * s ^ 20
    + 9741316148981 * s ^ 19
    - 2525984496906 * s ^ 18
    - 3077244371184 * s ^ 17
    + 3210340361457 * s ^ 16
    - 1131161555664 * s ^ 15
    + 343290991358 * s ^ 14
    - 658669685493 * s ^ 13
    + 702422113682 * s ^ 12
    - 300648425697 * s ^ 11
    - 39703361645 * s ^ 10
    + 117623861930 * s ^ 9
    - 65534778199 * s ^ 8
    + 16938148559 * s ^ 7
    - 802073181 * s ^ 6
    - 612412836 * s ^ 5
    + 101135966 * s ^ 4
    + 8829065 * s ^ 3
    + 38102 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient23 (s : ℚ) : ℚ :=
  -4 * s ^ 42
    + 206 * s ^ 41
    - 5176 * s ^ 40
    + 84252 * s ^ 39
    - 995925 * s ^ 38
    + 9093209 * s ^ 37
    - 66655927 * s ^ 36
    + 402882774 * s ^ 35
    - 2047976278 * s ^ 34
    + 8890980050 * s ^ 33
    - 33360208318 * s ^ 32
    + 109076350728 * s ^ 31
    - 311783238486 * s ^ 30
    + 776111419391 * s ^ 29
    - 1659493297371 * s ^ 28
    + 2961246372815 * s ^ 27
    - 4154966446294 * s ^ 26
    + 3897386342768 * s ^ 25
    - 526598755911 * s ^ 24
    - 6155292903727 * s ^ 23
    + 13032940805775 * s ^ 22
    - 14754259221633 * s ^ 21
    + 8716943864487 * s ^ 20
    + 940668585653 * s ^ 19
    - 6661214138842 * s ^ 18
    + 5521670736631 * s ^ 17
    - 1604671837486 * s ^ 16
    - 221089359271 * s ^ 15
    - 347384232481 * s ^ 14
    + 968600502935 * s ^ 13
    - 632388581659 * s ^ 12
    + 4786604911 * s ^ 11
    + 267355060977 * s ^ 10
    - 207759755064 * s ^ 9
    + 80644618539 * s ^ 8
    - 13839571038 * s ^ 7
    - 1437789429 * s ^ 6
    + 1041144397 * s ^ 5
    - 104415682 * s ^ 4
    - 15950939 * s ^ 3
    - 113541 * s ^ 2
    - 16 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient24 (s : ℚ) : ℚ :=
  s ^ 41
    - 52 * s ^ 40
    + 1303 * s ^ 39
    - 20863 * s ^ 38
    + 239499 * s ^ 37
    - 2102416 * s ^ 36
    + 14749913 * s ^ 35
    - 85804028 * s ^ 34
    + 429292596 * s ^ 33
    - 1918103607 * s ^ 32
    + 7896418978 * s ^ 31
    - 30301531942 * s ^ 30
    + 106952258890 * s ^ 29
    - 337421668121 * s ^ 28
    + 922468702534 * s ^ 27
    - 2123915381532 * s ^ 26
    + 3997092701398 * s ^ 25
    - 5887574536972 * s ^ 24
    + 6184624035269 * s ^ 23
    - 3209859923063 * s ^ 22
    - 2745861120436 * s ^ 21
    + 8317612342418 * s ^ 20
    - 9365524412392 * s ^ 19
    + 5310905630126 * s ^ 18
    - 175555463214 * s ^ 17
    - 1811049780313 * s ^ 16
    + 586766031871 * s ^ 15
    + 928271613107 * s ^ 14
    - 955019787160 * s ^ 13
    + 105360642313 * s ^ 12
    + 466617900679 * s ^ 11
    - 471173399167 * s ^ 10
    + 240214127857 * s ^ 9
    - 66372309029 * s ^ 8
    + 3409644527 * s ^ 7
    + 4184752851 * s ^ 6
    - 1271900189 * s ^ 5
    + 62213805 * s ^ 4
    + 23676102 * s ^ 3
    + 268341 * s ^ 2
    + 118 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient25 (s : ℚ) : ℚ :=
  -2 * s ^ 39
    + 128 * s ^ 38
    - 3766 * s ^ 37
    + 68940 * s ^ 36
    - 889039 * s ^ 35
    + 8621985 * s ^ 34
    - 65278965 * s ^ 33
    + 394056174 * s ^ 32
    - 1914354779 * s ^ 31
    + 7471028622 * s ^ 30
    - 23010632047 * s ^ 29
    + 53027745387 * s ^ 28
    - 75539978736 * s ^ 27
    - 17113816560 * s ^ 26
    + 478929952052 * s ^ 25
    - 1640010343091 * s ^ 24
    + 3550255251296 * s ^ 23
    - 5475221490533 * s ^ 22
    + 5909258220662 * s ^ 21
    - 3718485785871 * s ^ 20
    - 294316492738 * s ^ 19
    + 3429175673971 * s ^ 18
    - 3506828529976 * s ^ 17
    + 1165822568858 * s ^ 16
    + 966961706407 * s ^ 15
    - 1229355601882 * s ^ 14
    + 213461709390 * s ^ 13
    + 663921032871 * s ^ 12
    - 801712089794 * s ^ 11
    + 493145606390 * s ^ 10
    - 178888109914 * s ^ 9
    + 26368409012 * s ^ 8
    + 8922119381 * s ^ 7
    - 5743884290 * s ^ 6
    + 1094785289 * s ^ 5
    + 17763508 * s ^ 4
    - 28531038 * s ^ 3
    - 506771 * s ^ 2
    - 531 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient26 (s : ℚ) : ℚ :=
  3 * s ^ 38
    - 165 * s ^ 37
    + 4401 * s ^ 36
    - 75825 * s ^ 35
    + 945966 * s ^ 34
    - 9065922 * s ^ 33
    + 69066960 * s ^ 32
    - 427037082 * s ^ 31
    + 2169743676 * s ^ 30
    - 9117751222 * s ^ 29
    + 31718275483 * s ^ 28
    - 90833069530 * s ^ 27
    + 210764027297 * s ^ 26
    - 381694223724 * s ^ 25
    + 487019086421 * s ^ 24
    - 259556916931 * s ^ 23
    - 591551279750 * s ^ 22
    + 2022279630058 * s ^ 21
    - 3343532723629 * s ^ 20
    + 3500471192553 * s ^ 19
    - 2032413644889 * s ^ 18
    - 204439772174 * s ^ 17
    + 1624256150149 * s ^ 16
    - 1406241345915 * s ^ 15
    + 181294198180 * s ^ 14
    + 837956877916 * s ^ 13
    - 1060026143956 * s ^ 12
    + 722795917812 * s ^ 11
    - 306654680253 * s ^ 10
    + 63108346528 * s ^ 9
    + 13402444290 * s ^ 8
    - 15191570761 * s ^ 7
    + 5019110704 * s ^ 6
    - 568725804 * s ^ 5
    - 95096573 * s ^ 4
    + 27339723 * s ^ 3
    + 764360 * s ^ 2
    + 1625 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient27 (s : ℚ) : ℚ :=
  -s ^ 37
    + 57 * s ^ 36
    - 1609 * s ^ 35
    + 29606 * s ^ 34
    - 394737 * s ^ 33
    + 4028475 * s ^ 32
    - 32531456 * s ^ 31
    + 212496173 * s ^ 30
    - 1139791726 * s ^ 29
    + 5070842259 * s ^ 28
    - 18819901873 * s ^ 27
    + 58359466621 * s ^ 26
    - 150692346730 * s ^ 25
    + 320646376810 * s ^ 24
    - 549451798751 * s ^ 23
    + 719508469011 * s ^ 22
    - 615352105043 * s ^ 21
    + 64815434113 * s ^ 20
    + 821863520654 * s ^ 19
    - 1564104316163 * s ^ 18
    + 1608521254753 * s ^ 17
    - 837526309430 * s ^ 16
    - 257739224440 * s ^ 15
    + 999550445619 * s ^ 14
    - 1093464622369 * s ^ 13
    + 745758769925 * s ^ 12
    - 331084128381 * s ^ 11
    + 69934494411 * s ^ 10
    + 23709102707 * s ^ 9
    - 28527304695 * s ^ 8
    + 12544746163 * s ^ 7
    - 2688699483 * s ^ 6
    + 19209104 * s ^ 5
    + 125805798 * s ^ 4
    - 20098037 * s ^ 3
    - 913771 * s ^ 2
    - 3564 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient28 (s : ℚ) : ℚ :=
  -4 * s ^ 35
    + 216 * s ^ 34
    - 5554 * s ^ 33
    + 90695 * s ^ 32
    - 1057755 * s ^ 31
    + 9388289 * s ^ 30
    - 65937813 * s ^ 29
    + 375937795 * s ^ 28
    - 1769786256 * s ^ 27
    + 6955569871 * s ^ 26
    - 22965862713 * s ^ 25
    + 63835516683 * s ^ 24
    - 149012146652 * s ^ 23
    + 289737838894 * s ^ 22
    - 461086009544 * s ^ 21
    + 578494035127 * s ^ 20
    - 519387121105 * s ^ 19
    + 210902682821 * s ^ 18
    + 272140434786 * s ^ 17
    - 711736154746 * s ^ 16
    + 892616822940 * s ^ 15
    - 766128424366 * s ^ 14
    + 467118739448 * s ^ 13
    - 180596529194 * s ^ 12
    + 9872156291 * s ^ 11
    + 46606292301 * s ^ 10
    - 40710997891 * s ^ 9
    + 19763655077 * s ^ 8
    - 5664767111 * s ^ 7
    + 531943185 * s ^ 6
    + 253785077 * s ^ 5
    - 101518111 * s ^ 4
    + 10570952 * s ^ 3
    + 852623 * s ^ 2
    + 5744 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient29 (s : ℚ) : ℚ :=
  s ^ 34
    - 51 * s ^ 33
    + 1256 * s ^ 32
    - 19912 * s ^ 31
    + 228418 * s ^ 30
    - 2019126 * s ^ 29
    + 14291764 * s ^ 28
    - 83046219 * s ^ 27
    + 402781397 * s ^ 26
    - 1648556709 * s ^ 25
    + 5733765284 * s ^ 24
    - 17011623799 * s ^ 23
    + 43109357154 * s ^ 22
    - 93207471500 * s ^ 21
    + 171349471114 * s ^ 20
    - 266171401334 * s ^ 19
    + 345875400491 * s ^ 18
    - 369824556659 * s ^ 17
    + 315694452255 * s ^ 16
    - 200672404216 * s ^ 15
    + 73300819363 * s ^ 14
    + 19590011406 * s ^ 13
    - 60041452555 * s ^ 12
    + 59154831936 * s ^ 11
    - 39413763595 * s ^ 10
    + 18990719894 * s ^ 9
    - 6089517652 * s ^ 8
    + 759876690 * s ^ 7
    + 372382318 * s ^ 6
    - 232064082 * s ^ 5
    + 53422510 * s ^ 4
    - 3303892 * s ^ 3
    - 605099 * s ^ 2
    - 6851 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient30 (s : ℚ) : ℚ :=
  -2 * s ^ 31
    + 95 * s ^ 30
    - 2158 * s ^ 29
    + 31211 * s ^ 28
    - 322739 * s ^ 27
    + 2539472 * s ^ 26
    - 15795981 * s ^ 25
    + 79636562 * s ^ 24
    - 330964779 * s ^ 23
    + 1146943840 * s ^ 22
    - 3339688276 * s ^ 21
    + 8210165576 * s ^ 20
    - 17086700272 * s ^ 19
    + 30144362024 * s ^ 18
    - 45114536029 * s ^ 17
    + 57340176363 * s ^ 16
    - 62044364221 * s ^ 15
    + 57406234704 * s ^ 14
    - 45639171726 * s ^ 13
    + 31148565892 * s ^ 12
    - 17882869800 * s ^ 11
    + 8080883344 * s ^ 10
    - 2320273143 * s ^ 9
    - 96264967 * s ^ 8
    + 553002389 * s ^ 7
    - 330716774 * s ^ 6
    + 105647297 * s ^ 5
    - 16906927 * s ^ 4
    + 70156 * s ^ 3
    + 312873 * s ^ 2
    + 5996 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient31 (s : ℚ) : ℚ :=
  s ^ 28
    - 43 * s ^ 27
    + 875 * s ^ 26
    - 11200 * s ^ 25
    + 101080 * s ^ 24
    - 683113 * s ^ 23
    + 3582452 * s ^ 22
    - 14903169 * s ^ 21
    + 49834794 * s ^ 20
    - 134879025 * s ^ 19
    + 296038307 * s ^ 18
    - 525823083 * s ^ 17
    + 752619754 * s ^ 16
    - 867834642 * s ^ 15
    + 826451173 * s ^ 14
    - 720936228 * s ^ 13
    + 701249313 * s ^ 12
    - 797691262 * s ^ 11
    + 873856582 * s ^ 10
    - 786996908 * s ^ 9
    + 546757382 * s ^ 8
    - 282973381 * s ^ 7
    + 103691553 * s ^ 6
    - 23911260 * s ^ 5
    + 2134612 * s ^ 4
    + 438288 * s ^ 3
    - 109102 * s ^ 2
    - 3750 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient32 (s : ℚ) : ℚ :=
  -s ^ 24
    + 40 * s ^ 23
    - 752 * s ^ 22
    + 8831 * s ^ 21
    - 72622 * s ^ 20
    + 444388 * s ^ 19
    - 2098941 * s ^ 18
    + 7834479 * s ^ 17
    - 23470977 * s ^ 16
    + 57010406 * s ^ 15
    - 112970811 * s ^ 14
    + 183199816 * s ^ 13
    - 243243272 * s ^ 12
    + 263844915 * s ^ 11
    - 232453554 * s ^ 10
    + 164403893 * s ^ 9
    - 91207107 * s ^ 8
    + 37844334 * s ^ 7
    - 10476783 * s ^ 6
    + 1196918 * s ^ 5
    + 361208 * s ^ 4
    - 177630 * s ^ 3
    + 21634 * s ^ 2
    + 1588 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient33 (s : ℚ) : ℚ :=
  s ^ 17
    - 29 * s ^ 16
    + 386 * s ^ 15
    - 3125 * s ^ 14
    + 17191 * s ^ 13
    - 67990 * s ^ 12
    + 199464 * s ^ 11
    - 441415 * s ^ 10
    + 741919 * s ^ 9
    - 945972 * s ^ 8
    + 907180 * s ^ 7
    - 643753 * s ^ 6
    + 329027 * s ^ 5
    - 114922 * s ^ 4
    + 23614 * s ^ 3
    - 1168 * s ^ 2
    - 408 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient34 (s : ℚ) : ℚ :=
  -s ^ 8
    + 14 * s ^ 7
    - 81 * s ^ 6
    + 250 * s ^ 5
    - 442 * s ^ 4
    + 444 * s ^ 3
    - 232 * s ^ 2
    + 48 * s

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
    termOneCoefficient34 s * r ^ 34

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_0 (s : ℚ) :
    termOneCoefficient0 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient0,
    t1Step3Coefficient0,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_1 (s : ℚ) :
    termOneCoefficient1 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient1,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_2 (s : ℚ) :
    termOneCoefficient2 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient2,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_3 (s : ℚ) :
    termOneCoefficient3 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient3,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_4 (s : ℚ) :
    termOneCoefficient4 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient4,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_5 (s : ℚ) :
    termOneCoefficient5 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient5,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_6 (s : ℚ) :
    termOneCoefficient6 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient6,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_7 (s : ℚ) :
    termOneCoefficient7 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient7,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_8 (s : ℚ) :
    termOneCoefficient8 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient8,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_9 (s : ℚ) :
    termOneCoefficient9 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient9,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_10 (s : ℚ) :
    termOneCoefficient10 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient10,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_11 (s : ℚ) :
    termOneCoefficient11 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient11,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_12 (s : ℚ) :
    termOneCoefficient12 s =
    t1Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient12,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_13 (s : ℚ) :
    termOneCoefficient13 s =
    t1Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient13,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_14 (s : ℚ) :
    termOneCoefficient14 s =
    t1Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient14,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_15 (s : ℚ) :
    termOneCoefficient15 s =
    t1Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient15,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_16 (s : ℚ) :
    termOneCoefficient16 s =
    t1Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient16,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_17 (s : ℚ) :
    termOneCoefficient17 s =
    t1Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient17,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_18 (s : ℚ) :
    termOneCoefficient18 s =
    t1Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient18,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_19 (s : ℚ) :
    termOneCoefficient19 s =
    t1Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient19,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_20 (s : ℚ) :
    termOneCoefficient20 s =
    t1Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient20,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_21 (s : ℚ) :
    termOneCoefficient21 s =
    t1Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient21,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_22 (s : ℚ) :
    termOneCoefficient22 s =
    t1Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient1 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient22,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_23 (s : ℚ) :
    termOneCoefficient23 s =
    t1Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient2 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient1 s
    := by
  simp only [termOneCoefficient23,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_24 (s : ℚ) :
    termOneCoefficient24 s =
    t1Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient3 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient2 s
    := by
  simp only [termOneCoefficient24,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_25 (s : ℚ) :
    termOneCoefficient25 s =
    t1Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient4 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient3 s
    := by
  simp only [termOneCoefficient25,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_26 (s : ℚ) :
    termOneCoefficient26 s =
    t1Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient5 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient4 s
    := by
  simp only [termOneCoefficient26,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_27 (s : ℚ) :
    termOneCoefficient27 s =
    t1Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient6 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient5 s
    := by
  simp only [termOneCoefficient27,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_28 (s : ℚ) :
    termOneCoefficient28 s =
    t1Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient7 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient6 s
    := by
  simp only [termOneCoefficient28,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_29 (s : ℚ) :
    termOneCoefficient29 s =
    t1Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient8 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient7 s
    := by
  simp only [termOneCoefficient29,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_30 (s : ℚ) :
    termOneCoefficient30 s =
    t1Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient9 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient8 s
    := by
  simp only [termOneCoefficient30,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_31 (s : ℚ) :
    termOneCoefficient31 s =
    t1Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient10 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient9 s
    := by
  simp only [termOneCoefficient31,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_32 (s : ℚ) :
    termOneCoefficient32 s =
    t1Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient11 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient10 s
    := by
  simp only [termOneCoefficient32,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_33 (s : ℚ) :
    termOneCoefficient33 s =
    t1Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient12 s
      + t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient11 s
    := by
  simp only [termOneCoefficient33,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_34 (s : ℚ) :
    termOneCoefficient34 s =
    t1Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient12 s
    := by
  simp only [termOneCoefficient34,
    t1Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termOne_eq_t1Step3_mul_rawUnitNineDenominator (r s : ℚ) :
    termOne r s = t1Step3 r s * rawUnitNineDenominator r s := by
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
  simp only [termOne, t1Step3, rawUnitNineDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient1 (s : ℚ) : ℚ :=
  s ^ 12
    - 3 * s ^ 11
    + 6 * s ^ 10
    - 8 * s ^ 9
    + 8 * s ^ 8
    - 6 * s ^ 7
    + 3 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient2 (s : ℚ) : ℚ :=
  s ^ 15
    - 6 * s ^ 14
    + 21 * s ^ 13
    - 50 * s ^ 12
    + 79 * s ^ 11
    - 95 * s ^ 10
    + 79 * s ^ 9
    - 41 * s ^ 8
    - 3 * s ^ 7
    + 32 * s ^ 6
    - 33 * s ^ 5
    + 21 * s ^ 4
    - 6 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient3 (s : ℚ) : ℚ :=
  s ^ 15
    - 13 * s ^ 14
    + 60 * s ^ 13
    - 190 * s ^ 12
    + 441 * s ^ 11
    - 762 * s ^ 10
    + 1089 * s ^ 9
    - 1276 * s ^ 8
    + 1269 * s ^ 7
    - 1037 * s ^ 6
    + 658 * s ^ 5
    - 312 * s ^ 4
    + 86 * s ^ 3
    - 14 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient4 (s : ℚ) : ℚ :=
  s ^ 16
    - 11 * s ^ 15
    + 58 * s ^ 14
    - 201 * s ^ 13
    + 549 * s ^ 12
    - 1176 * s ^ 11
    + 2092 * s ^ 10
    - 3239 * s ^ 9
    + 4172 * s ^ 8
    - 4491 * s ^ 7
    + 3799 * s ^ 6
    - 2410 * s ^ 5
    + 1069 * s ^ 4
    - 236 * s ^ 3
    + 13 * s ^ 2
    + 12 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 15
    + 3 * s ^ 14
    + 24 * s ^ 13
    - 200 * s ^ 12
    + 754 * s ^ 11
    - 2081 * s ^ 10
    + 4239 * s ^ 9
    - 6390 * s ^ 8
    + 7416 * s ^ 7
    - 6226 * s ^ 6
    + 3616 * s ^ 5
    - 1146 * s ^ 4
    - 145 * s ^ 3
    + 220 * s ^ 2
    - 91 * s
    + 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 15
    + 13 * s ^ 14
    - 75 * s ^ 13
    + 291 * s ^ 12
    - 909 * s ^ 11
    + 2274 * s ^ 10
    - 4195 * s ^ 9
    + 5809 * s ^ 8
    - 5928 * s ^ 7
    + 3673 * s ^ 6
    - 557 * s ^ 5
    - 1674 * s ^ 4
    + 1982 * s ^ 3
    - 978 * s ^ 2
    + 303 * s
    - 28

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient7 (s : ℚ) : ℚ :=
  5 * s ^ 13
    - 55 * s ^ 12
    + 247 * s ^ 11
    - 589 * s ^ 10
    + 792 * s ^ 9
    - 422 * s ^ 8
    - 1154 * s ^ 7
    + 3852 * s ^ 6
    - 5944 * s ^ 5
    + 6284 * s ^ 4
    - 4437 * s ^ 3
    + 1931 * s ^ 2
    - 565 * s
    + 55

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient8 (s : ℚ) : ℚ :=
  s ^ 13
    - 16 * s ^ 12
    + 107 * s ^ 11
    - 413 * s ^ 10
    + 1106 * s ^ 9
    - 2401 * s ^ 8
    + 4488 * s ^ 7
    - 6745 * s ^ 6
    + 7926 * s ^ 5
    - 7300 * s ^ 4
    + 4775 * s ^ 3
    - 2092 * s ^ 2
    + 629 * s
    - 65

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient9 (s : ℚ) : ℚ :=
  -2 * s ^ 11
    + 30 * s ^ 10
    - 194 * s ^ 9
    + 720 * s ^ 8
    - 1731 * s ^ 7
    + 2950 * s ^ 6
    - 3851 * s ^ 5
    + 3801 * s ^ 4
    - 2610 * s ^ 3
    + 1255 * s ^ 2
    - 414 * s
    + 46

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient10 (s : ℚ) : ℚ :=
  s ^ 9
    - 14 * s ^ 8
    + 85 * s ^ 7
    - 290 * s ^ 6
    + 596 * s ^ 5
    - 752 * s ^ 4
    + 620 * s ^ 3
    - 376 * s ^ 2
    + 148 * s
    - 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient11 (s : ℚ) : ℚ :=
  -s ^ 5
    + 9 * s ^ 4
    - 29 * s ^ 3
    + 40 * s ^ 2
    - 22 * s
    + 3

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
    t2Step1Coefficient11 s * r ^ 11

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_0 (s : ℚ) :
    t2Step1Coefficient0 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient0,
    rawUnitFourNumeratorCoefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_1 (s : ℚ) :
    t2Step1Coefficient1 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient1,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_2 (s : ℚ) :
    t2Step1Coefficient2 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient2,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_3 (s : ℚ) :
    t2Step1Coefficient3 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient3,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_4 (s : ℚ) :
    t2Step1Coefficient4 s =
    rawUnitFourNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient4,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_5 (s : ℚ) :
    t2Step1Coefficient5 s =
    rawUnitFourNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient5,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_6 (s : ℚ) :
    t2Step1Coefficient6 s =
    rawUnitFourNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient6,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_7 (s : ℚ) :
    t2Step1Coefficient7 s =
    rawUnitFourNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient7,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_8 (s : ℚ) :
    t2Step1Coefficient8 s =
    rawUnitFourNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient8,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_9 (s : ℚ) :
    t2Step1Coefficient9 s =
    rawUnitFourNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient1 s
    := by
  simp only [t2Step1Coefficient9,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_10 (s : ℚ) :
    t2Step1Coefficient10 s =
    rawUnitFourNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient2 s
    := by
  simp only [t2Step1Coefficient10,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_11 (s : ℚ) :
    t2Step1Coefficient11 s =
    rawUnitFourNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient3 s
    := by
  simp only [t2Step1Coefficient11,
    rawUnitFourNumeratorCoefficient8,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step1_eq_rawUnitFourNumerator_mul_rawUnitEightDenominator (r s : ℚ) :
    t2Step1 r s = rawUnitFourNumerator r s * rawUnitEightDenominator r s := by
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
  simp only [t2Step1, rawUnitFourNumerator, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 15
    + 3 * s ^ 14
    - 6 * s ^ 13
    + 8 * s ^ 12
    - 8 * s ^ 11
    + 6 * s ^ 10
    - 3 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 18
    + 6 * s ^ 17
    - 21 * s ^ 16
    + 49 * s ^ 15
    - 70 * s ^ 14
    + 68 * s ^ 13
    - 25 * s ^ 12
    - 36 * s ^ 11
    + 87 * s ^ 10
    - 103 * s ^ 9
    + 78 * s ^ 8
    - 42 * s ^ 7
    + 12 * s ^ 6
    - 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 18
    + 25 * s ^ 17
    - 121 * s ^ 16
    + 393 * s ^ 15
    - 919 * s ^ 14
    + 1571 * s ^ 13
    - 2141 * s ^ 12
    + 2303 * s ^ 11
    - 1993 * s ^ 10
    + 1307 * s ^ 9
    - 537 * s ^ 8
    + 27 * s ^ 7
    + 167 * s ^ 6
    - 117 * s ^ 5
    + 45 * s ^ 4
    - 9 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient4 (s : ℚ) : ℚ :=
  -2 * s ^ 19
    + 21 * s ^ 18
    - 99 * s ^ 17
    + 273 * s ^ 16
    - 503 * s ^ 15
    + 438 * s ^ 14
    + 439 * s ^ 13
    - 2227 * s ^ 12
    + 4911 * s ^ 11
    - 7629 * s ^ 10
    + 9659 * s ^ 9
    - 9949 * s ^ 8
    + 8107 * s ^ 7
    - 5146 * s ^ 6
    + 2319 * s ^ 5
    - 741 * s ^ 4
    + 145 * s ^ 3
    - 16 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient5 (s : ℚ) : ℚ :=
  -2 * s ^ 19
    + 36 * s ^ 18
    - 264 * s ^ 17
    + 1170 * s ^ 16
    - 3724 * s ^ 15
    + 9314 * s ^ 14
    - 18642 * s ^ 13
    + 31302 * s ^ 12
    - 45969 * s ^ 11
    + 58567 * s ^ 10
    - 64741 * s ^ 9
    + 59755 * s ^ 8
    - 44528 * s ^ 7
    + 25814 * s ^ 6
    - 10707 * s ^ 5
    + 3049 * s ^ 4
    - 444 * s ^ 3
    + 15 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 20
    + 16 * s ^ 19
    - 120 * s ^ 18
    + 572 * s ^ 17
    - 2050 * s ^ 16
    + 6028 * s ^ 15
    - 14960 * s ^ 14
    + 31896 * s ^ 13
    - 60179 * s ^ 12
    + 98675 * s ^ 11
    - 136330 * s ^ 10
    + 156537 * s ^ 9
    - 143947 * s ^ 8
    + 103328 * s ^ 7
    - 54876 * s ^ 6
    + 18873 * s ^ 5
    - 3053 * s ^ 4
    - 834 * s ^ 3
    + 558 * s ^ 2
    - 143 * s
    + 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient7 (s : ℚ) : ℚ :=
  s ^ 19
    - 7 * s ^ 18
    - 19 * s ^ 17
    + 441 * s ^ 16
    - 2693 * s ^ 15
    + 10445 * s ^ 14
    - 30566 * s ^ 13
    + 70344 * s ^ 12
    - 126813 * s ^ 11
    + 180821 * s ^ 10
    - 203482 * s ^ 9
    + 174008 * s ^ 8
    - 107255 * s ^ 7
    + 37839 * s ^ 6
    + 3674 * s ^ 5
    - 12888 * s ^ 4
    + 8500 * s ^ 3
    - 2918 * s ^ 2
    + 613 * s
    - 45

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient8 (s : ℚ) : ℚ :=
  s ^ 19
    - 18 * s ^ 18
    + 149 * s ^ 17
    - 793 * s ^ 16
    + 3193 * s ^ 15
    - 10460 * s ^ 14
    + 27738 * s ^ 13
    - 57896 * s ^ 12
    + 93985 * s ^ 11
    - 117834 * s ^ 10
    + 106166 * s ^ 9
    - 51718 * s ^ 8
    - 18733 * s ^ 7
    + 69204 * s ^ 6
    - 76254 * s ^ 5
    + 51592 * s ^ 4
    - 24498 * s ^ 3
    + 7596 * s ^ 2
    - 1539 * s
    + 119

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient9 (s : ℚ) : ℚ :=
  -5 * s ^ 17
    + 79 * s ^ 16
    - 546 * s ^ 15
    + 2148 * s ^ 14
    - 5191 * s ^ 13
    + 7345 * s ^ 12
    - 2180 * s ^ 11
    - 20098 * s ^ 10
    + 67155 * s ^ 9
    - 129045 * s ^ 8
    + 176919 * s ^ 7
    - 184967 * s ^ 6
    + 145933 * s ^ 5
    - 86641 * s ^ 4
    + 38784 * s ^ 3
    - 11964 * s ^ 2
    + 2477 * s
    - 203

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient10 (s : ℚ) : ℚ :=
  -s ^ 17
    + 21 * s ^ 16
    - 196 * s ^ 15
    + 1098 * s ^ 14
    - 4237 * s ^ 13
    + 12432 * s ^ 12
    - 30028 * s ^ 11
    + 62033 * s ^ 10
    - 108467 * s ^ 9
    + 156835 * s ^ 8
    - 186455 * s ^ 7
    + 180012 * s ^ 6
    - 136853 * s ^ 5
    + 81449 * s ^ 4
    - 37228 * s ^ 3
    + 11989 * s ^ 2
    - 2635 * s
    + 231

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient11 (s : ℚ) : ℚ :=
  2 * s ^ 15
    - 40 * s ^ 14
    + 363 * s ^ 13
    - 1985 * s ^ 12
    + 7328 * s ^ 11
    - 19506 * s ^ 10
    + 39397 * s ^ 9
    - 62975 * s ^ 8
    + 81298 * s ^ 7
    - 83744 * s ^ 6
    + 67919 * s ^ 5
    - 43747 * s ^ 4
    + 21622 * s ^ 3
    - 7600 * s ^ 2
    + 1843 * s
    - 175

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient12 (s : ℚ) : ℚ :=
  -s ^ 13
    + 19 * s ^ 12
    - 166 * s ^ 11
    + 875 * s ^ 10
    - 3063 * s ^ 9
    + 7431 * s ^ 8
    - 12820 * s ^ 7
    + 16244 * s ^ 6
    - 15901 * s ^ 5
    + 12285 * s ^ 4
    - 7060 * s ^ 3
    + 2885 * s ^ 2
    - 813 * s
    + 85

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient13 (s : ℚ) : ℚ :=
  2 * s ^ 9
    - 28 * s ^ 8
    + 168 * s ^ 7
    - 560 * s ^ 6
    + 1117 * s ^ 5
    - 1359 * s ^ 4
    + 1051 * s ^ 3
    - 571 * s ^ 2
    + 204 * s
    - 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient14 (s : ℚ) : ℚ :=
  -s ^ 5
    + 9 * s ^ 4
    - 29 * s ^ 3
    + 40 * s ^ 2
    - 22 * s
    + 3

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
    t2Step2Coefficient14 s * r ^ 14

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_0 (s : ℚ) :
    t2Step2Coefficient0 s =
    t2Step1Coefficient0 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient0,
    t2Step1Coefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_1 (s : ℚ) :
    t2Step2Coefficient1 s =
    t2Step1Coefficient0 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient1 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient1,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_2 (s : ℚ) :
    t2Step2Coefficient2 s =
    t2Step1Coefficient0 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient1 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient2 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient2,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_3 (s : ℚ) :
    t2Step2Coefficient3 s =
    t2Step1Coefficient0 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient1 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient2 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient3 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient3,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_4 (s : ℚ) :
    t2Step2Coefficient4 s =
    t2Step1Coefficient1 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient2 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient3 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient4 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient4,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_5 (s : ℚ) :
    t2Step2Coefficient5 s =
    t2Step1Coefficient2 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient3 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient4 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient5 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient5,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_6 (s : ℚ) :
    t2Step2Coefficient6 s =
    t2Step1Coefficient3 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient4 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient5 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient6 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient6,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_7 (s : ℚ) :
    t2Step2Coefficient7 s =
    t2Step1Coefficient4 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient5 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient6 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient7 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient7,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_8 (s : ℚ) :
    t2Step2Coefficient8 s =
    t2Step1Coefficient5 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient6 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient7 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient8 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient8,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_9 (s : ℚ) :
    t2Step2Coefficient9 s =
    t2Step1Coefficient6 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient7 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient8 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient9 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient9,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_10 (s : ℚ) :
    t2Step2Coefficient10 s =
    t2Step1Coefficient7 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient8 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient9 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient10 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient10,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_11 (s : ℚ) :
    t2Step2Coefficient11 s =
    t2Step1Coefficient8 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient9 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient10 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step1Coefficient11 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient11,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_12 (s : ℚ) :
    t2Step2Coefficient12 s =
    t2Step1Coefficient9 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient10 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step1Coefficient11 s *
        rawUnitEightDenominatorCoefficient1 s
    := by
  simp only [t2Step2Coefficient12,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_13 (s : ℚ) :
    t2Step2Coefficient13 s =
    t2Step1Coefficient10 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step1Coefficient11 s *
        rawUnitEightDenominatorCoefficient2 s
    := by
  simp only [t2Step2Coefficient13,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_14 (s : ℚ) :
    t2Step2Coefficient14 s =
    t2Step1Coefficient11 s *
        rawUnitEightDenominatorCoefficient3 s
    := by
  simp only [t2Step2Coefficient14,
    t2Step1Coefficient11,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step2_eq_t2Step1_mul_rawUnitEightDenominator (r s : ℚ) :
    t2Step2 r s = t2Step1 r s * rawUnitEightDenominator r s := by
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
  simp only [t2Step2, t2Step1, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 23
    + 3 * s ^ 22
    - 6 * s ^ 21
    + 8 * s ^ 20
    - 8 * s ^ 19
    + 6 * s ^ 18
    - 3 * s ^ 17
    + s ^ 16

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 26
    + 6 * s ^ 25
    - 21 * s ^ 24
    + 46 * s ^ 23
    - 44 * s ^ 22
    - 11 * s ^ 21
    + 137 * s ^ 20
    - 277 * s ^ 19
    + 367 * s ^ 18
    - 363 * s ^ 17
    + 270 * s ^ 16
    - 157 * s ^ 15
    + 66 * s ^ 14
    - 23 * s ^ 13
    + 6 * s ^ 12
    - s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient3 (s : ℚ) : ℚ :=
  -6 * s ^ 26
    + 69 * s ^ 25
    - 341 * s ^ 24
    + 1120 * s ^ 23
    - 2603 * s ^ 22
    + 4302 * s ^ 21
    - 5407 * s ^ 20
    + 4934 * s ^ 19
    - 2935 * s ^ 18
    + 191 * s ^ 17
    + 2073 * s ^ 16
    - 2926 * s ^ 15
    + 2569 * s ^ 14
    - 1598 * s ^ 13
    + 791 * s ^ 12
    - 310 * s ^ 11
    + 93 * s ^ 10
    - 18 * s ^ 9
    + 2 * s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 29
    + 12 * s ^ 28
    - 80 * s ^ 27
    + 366 * s ^ 26
    - 1153 * s ^ 25
    + 2377 * s ^ 24
    - 2545 * s ^ 23
    - 2656 * s ^ 22
    + 18388 * s ^ 21
    - 44574 * s ^ 20
    + 75212 * s ^ 19
    - 97676 * s ^ 18
    + 102880 * s ^ 17
    - 88061 * s ^ 16
    + 59882 * s ^ 15
    - 31148 * s ^ 14
    + 10485 * s ^ 13
    - 828 * s ^ 12
    - 1981 * s ^ 11
    + 1790 * s ^ 10
    - 956 * s ^ 9
    + 338 * s ^ 8
    - 82 * s ^ 7
    + 12 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient5 (s : ℚ) : ℚ :=
  -2 * s ^ 29
    + 39 * s ^ 28
    - 342 * s ^ 27
    + 2012 * s ^ 26
    - 8768 * s ^ 25
    + 29068 * s ^ 24
    - 74975 * s ^ 23
    + 153096 * s ^ 22
    - 246021 * s ^ 21
    + 310429 * s ^ 20
    - 304120 * s ^ 19
    + 203670 * s ^ 18
    - 35133 * s ^ 17
    - 150450 * s ^ 16
    + 284995 * s ^ 15
    - 324185 * s ^ 14
    + 278849 * s ^ 13
    - 190224 * s ^ 12
    + 108449 * s ^ 11
    - 51616 * s ^ 10
    + 19971 * s ^ 9
    - 5779 * s ^ 8
    + 1152 * s ^ 7
    - 116 * s ^ 6
    - s ^ 5
    + 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient6 (s : ℚ) : ℚ :=
  -2 * s ^ 30
    + 33 * s ^ 29
    - 264 * s ^ 28
    + 1351 * s ^ 27
    - 4841 * s ^ 26
    + 11542 * s ^ 25
    - 12707 * s ^ 24
    - 27948 * s ^ 23
    + 190033 * s ^ 22
    - 577739 * s ^ 21
    + 1233449 * s ^ 20
    - 2082487 * s ^ 19
    + 2962584 * s ^ 18
    - 3636195 * s ^ 17
    + 3912103 * s ^ 16
    - 3656303 * s ^ 15
    + 2942628 * s ^ 14
    - 2034409 * s ^ 13
    + 1202604 * s ^ 12
    - 617095 * s ^ 11
    + 264453 * s ^ 10
    - 86879 * s ^ 9
    + 16911 * s ^ 8
    + 201 * s ^ 7
    - 1359 * s ^ 6
    + 388 * s ^ 5
    - 52 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient7 (s : ℚ) : ℚ :=
  -2 * s ^ 30
    + 52 * s ^ 29
    - 585 * s ^ 28
    + 4144 * s ^ 27
    - 21425 * s ^ 26
    + 86269 * s ^ 25
    - 277523 * s ^ 24
    + 727312 * s ^ 23
    - 1582519 * s ^ 22
    + 2902757 * s ^ 21
    - 4580975 * s ^ 20
    + 6432786 * s ^ 19
    - 8197747 * s ^ 18
    + 9419226 * s ^ 17
    - 9623668 * s ^ 16
    + 8491372 * s ^ 15
    - 6414456 * s ^ 14
    + 4156986 * s ^ 13
    - 2310060 * s ^ 12
    + 1091604 * s ^ 11
    - 353728 * s ^ 10
    + 9417 * s ^ 9
    + 75401 * s ^ 8
    - 48676 * s ^ 7
    + 16783 * s ^ 6
    - 2971 * s ^ 5
    + 186 * s ^ 4
    + 42 * s ^ 3
    - 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient8 (s : ℚ) : ℚ :=
  -s ^ 31
    + 22 * s ^ 30
    - 233 * s ^ 29
    + 1590 * s ^ 28
    - 7971 * s ^ 27
    + 31164 * s ^ 26
    - 97163 * s ^ 25
    + 245297 * s ^ 24
    - 516796 * s ^ 23
    + 950894 * s ^ 22
    - 1632504 * s ^ 21
    + 2815025 * s ^ 20
    - 4822518 * s ^ 19
    + 7371712 * s ^ 18
    - 9346932 * s ^ 17
    + 9592864 * s ^ 16
    - 7804390 * s ^ 15
    + 5213400 * s ^ 14
    - 2917293 * s ^ 13
    + 1240512 * s ^ 12
    - 47703 * s ^ 11
    - 780624 * s ^ 10
    + 945764 * s ^ 9
    - 639317 * s ^ 8
    + 264869 * s ^ 7
    - 65848 * s ^ 6
    + 5168 * s ^ 5
    + 1533 * s ^ 4
    - 538 * s ^ 3
    + 16 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient9 (s : ℚ) : ℚ :=
  3 * s ^ 30
    - 54 * s ^ 29
    + 471 * s ^ 28
    - 2719 * s ^ 27
    + 11868 * s ^ 26
    - 40036 * s ^ 25
    + 98228 * s ^ 24
    - 144883 * s ^ 23
    - 21587 * s ^ 22
    + 852886 * s ^ 21
    - 2844285 * s ^ 20
    + 5707179 * s ^ 19
    - 7798681 * s ^ 18
    + 7455712 * s ^ 17
    - 4683262 * s ^ 16
    + 1331731 * s ^ 15
    + 466793 * s ^ 14
    - 1328537 * s ^ 13
    + 2577272 * s ^ 12
    - 4318886 * s ^ 11
    + 5241559 * s ^ 10
    - 4162229 * s ^ 9
    + 2182146 * s ^ 8
    - 680054 * s ^ 7
    + 77639 * s ^ 6
    + 35121 * s ^ 5
    - 16344 * s ^ 4
    + 2942 * s ^ 3
    + 24 * s ^ 2
    - 17 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient10 (s : ℚ) : ℚ :=
  s ^ 30
    - 25 * s ^ 29
    + 275 * s ^ 28
    - 1943 * s ^ 27
    + 10661 * s ^ 26
    - 49233 * s ^ 25
    + 189552 * s ^ 24
    - 590883 * s ^ 23
    + 1469541 * s ^ 22
    - 2859833 * s ^ 21
    + 4078528 * s ^ 20
    - 3500849 * s ^ 19
    + 17231 * s ^ 18
    + 4841474 * s ^ 17
    - 7789454 * s ^ 16
    + 6921992 * s ^ 15
    - 4560231 * s ^ 14
    + 5950658 * s ^ 13
    - 11520689 * s ^ 12
    + 16700724 * s ^ 11
    - 16395931 * s ^ 10
    + 10476939 * s ^ 9
    - 4067932 * s ^ 8
    + 494807 * s ^ 7
    + 386569 * s ^ 6
    - 263074 * s ^ 5
    + 69912 * s ^ 4
    - 7986 * s ^ 3
    - 937 * s ^ 2
    + 136 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient11 (s : ℚ) : ℚ :=
  -s ^ 29
    + 8 * s ^ 28
    + 60 * s ^ 27
    - 1010 * s ^ 26
    + 4771 * s ^ 25
    - 3830 * s ^ 24
    - 68568 * s ^ 23
    + 452250 * s ^ 22
    - 1689747 * s ^ 21
    + 4451010 * s ^ 20
    - 8433938 * s ^ 19
    + 11028852 * s ^ 18
    - 8824775 * s ^ 17
    + 2082055 * s ^ 16
    + 3196770 * s ^ 15
    + 1619953 * s ^ 14
    - 18483157 * s ^ 13
    + 36493912 * s ^ 12
    - 42492702 * s ^ 11
    + 32137098 * s ^ 10
    - 14251295 * s ^ 9
    + 1414849 * s ^ 8
    + 2898722 * s ^ 7
    - 2239517 * s ^ 6
    + 859297 * s ^ 5
    - 159824 * s ^ 4
    + 2964 * s ^ 3
    + 6474 * s ^ 2
    - 681 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient12 (s : ℚ) : ℚ :=
  -5 * s ^ 28
    + 145 * s ^ 27
    - 1796 * s ^ 26
    + 12922 * s ^ 25
    - 61603 * s ^ 24
    + 209304 * s ^ 23
    - 520016 * s ^ 22
    + 871675 * s ^ 21
    - 474601 * s ^ 20
    - 2455471 * s ^ 19
    + 9215324 * s ^ 18
    - 17041164 * s ^ 17
    + 17789109 * s ^ 16
    - 2561952 * s ^ 15
    - 29548292 * s ^ 14
    + 64028355 * s ^ 13
    - 78556257 * s ^ 12
    + 63359162 * s ^ 11
    - 28801010 * s ^ 10
    - 1962204 * s ^ 9
    + 14247325 * s ^ 8
    - 11985548 * s ^ 7
    + 5615472 * s ^ 6
    - 1538746 * s ^ 5
    + 120351 * s ^ 4
    + 63180 * s ^ 3
    - 26018 * s ^ 2
    + 2358 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient13 (s : ℚ) : ℚ :=
  -s ^ 28
    + 38 * s ^ 27
    - 603 * s ^ 26
    + 5515 * s ^ 25
    - 33704 * s ^ 24
    + 151722 * s ^ 23
    - 540582 * s ^ 22
    + 1581151 * s ^ 21
    - 3737781 * s ^ 20
    + 6641418 * s ^ 19
    - 7319241 * s ^ 18
    - 206995 * s ^ 17
    + 21355522 * s ^ 16
    - 54733869 * s ^ 15
    + 87212011 * s ^ 14
    - 97274447 * s ^ 13
    + 72174671 * s ^ 12
    - 22093193 * s ^ 11
    - 26074411 * s ^ 10
    + 47469750 * s ^ 9
    - 40340807 * s ^ 8
    + 21929591 * s ^ 7
    - 7370497 * s ^ 6
    + 968494 * s ^ 5
    + 445857 * s ^ 4
    - 274709 * s ^ 3
    + 70989 * s ^ 2
    - 5878 * s
    - 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient14 (s : ℚ) : ℚ :=
  2 * s ^ 27
    - 55 * s ^ 26
    + 665 * s ^ 25
    - 4786 * s ^ 24
    + 24221 * s ^ 23
    - 101769 * s ^ 22
    + 406689 * s ^ 21
    - 1536132 * s ^ 20
    + 4975877 * s ^ 19
    - 12968724 * s ^ 18
    + 26807369 * s ^ 17
    - 44037443 * s ^ 16
    + 56399147 * s ^ 15
    - 51106674 * s ^ 14
    + 19390748 * s ^ 13
    + 31662954 * s ^ 12
    - 79339518 * s ^ 11
    + 99547863 * s ^ 10
    - 84284172 * s ^ 9
    + 49677208 * s ^ 8
    - 18745774 * s ^ 7
    + 2206007 * s ^ 6
    + 2291259 * s ^ 5
    - 1786968 * s ^ 4
    + 649539 * s ^ 3
    - 138280 * s ^ 2
    + 10692 * s
    + 55

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient15 (s : ℚ) : ℚ :=
  -17 * s ^ 25
    + 467 * s ^ 24
    - 5800 * s ^ 23
    + 43103 * s ^ 22
    - 213599 * s ^ 21
    + 743439 * s ^ 20
    - 1855730 * s ^ 19
    + 3262495 * s ^ 18
    - 3430912 * s ^ 17
    - 914718 * s ^ 16
    + 14437528 * s ^ 15
    - 40383792 * s ^ 14
    + 75017754 * s ^ 13
    - 105289127 * s ^ 12
    + 115280968 * s ^ 11
    - 96950131 * s ^ 10
    + 58403771 * s ^ 9
    - 20104155 * s ^ 8
    - 2849784 * s ^ 7
    + 9453259 * s ^ 6
    - 7146963 * s ^ 5
    + 3336986 * s ^ 4
    - 1016182 * s ^ 3
    + 195442 * s ^ 2
    - 14138 * s
    - 164

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient16 (s : ℚ) : ℚ :=
  -2 * s ^ 25
    + 69 * s ^ 24
    - 1068 * s ^ 23
    + 9930 * s ^ 22
    - 62595 * s ^ 21
    + 286863 * s ^ 20
    - 1006611 * s ^ 19
    + 2837172 * s ^ 18
    - 6728312 * s ^ 17
    + 13893338 * s ^ 16
    - 25161873 * s ^ 15
    + 39236314 * s ^ 14
    - 51207356 * s ^ 13
    + 54034682 * s ^ 12
    - 42849992 * s ^ 11
    + 19495656 * s ^ 10
    + 5973497 * s ^ 9
    - 21841405 * s ^ 8
    + 24358315 * s ^ 7
    - 18029400 * s ^ 6
    + 9756029 * s ^ 5
    - 3907725 * s ^ 4
    + 1100869 * s ^ 3
    - 200008 * s ^ 2
    + 13291 * s
    + 322

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient17 (s : ℚ) : ℚ :=
  s ^ 24
    - 28 * s ^ 23
    + 348 * s ^ 22
    - 2499 * s ^ 21
    + 11135 * s ^ 20
    - 29225 * s ^ 19
    + 25614 * s ^ 18
    + 118729 * s ^ 17
    - 553505 * s ^ 16
    + 1108117 * s ^ 15
    - 845476 * s ^ 14
    - 1833771 * s ^ 13
    + 8297073 * s ^ 12
    - 18347245 * s ^ 11
    + 28979057 * s ^ 10
    - 35137387 * s ^ 9
    + 33659545 * s ^ 8
    - 25957730 * s ^ 7
    + 16127509 * s ^ 6
    - 7950692 * s ^ 5
    + 3020942 * s ^ 4
    - 827238 * s ^ 3
    + 145561 * s ^ 2
    - 8401 * s
    - 434

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient18 (s : ℚ) : ℚ :=
  -2 * s ^ 22
    + 60 * s ^ 21
    - 837 * s ^ 20
    + 7212 * s ^ 19
    - 43026 * s ^ 18
    + 189147 * s ^ 17
    - 638896 * s ^ 16
    + 1716969 * s ^ 15
    - 3798800 * s ^ 14
    + 7148142 * s ^ 13
    - 11688494 * s ^ 12
    + 16634628 * s ^ 11
    - 20321525 * s ^ 10
    + 21025788 * s ^ 9
    - 18346645 * s ^ 8
    + 13452434 * s ^ 7
    - 8161868 * s ^ 6
    + 3999058 * s ^ 5
    - 1524294 * s ^ 4
    + 419940 * s ^ 3
    - 72439 * s ^ 2
    + 3042 * s
    + 406

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient19 (s : ℚ) : ℚ :=
  s ^ 20
    - 30 * s ^ 19
    + 423 * s ^ 18
    - 3714 * s ^ 17
    + 22668 * s ^ 16
    - 101696 * s ^ 15
    + 346226 * s ^ 14
    - 912660 * s ^ 13
    + 1891203 * s ^ 12
    - 3128264 * s ^ 11
    + 4209131 * s ^ 10
    - 4704127 * s ^ 9
    + 4426248 * s ^ 8
    - 3490750 * s ^ 7
    + 2263562 * s ^ 6
    - 1178820 * s ^ 5
    + 473722 * s ^ 4
    - 135450 * s ^ 3
    + 22752 * s ^ 2
    - 165 * s
    - 260

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient20 (s : ℚ) : ℚ :=
  -2 * s ^ 16
    + 50 * s ^ 15
    - 572 * s ^ 14
    + 3959 * s ^ 13
    - 18462 * s ^ 12
    + 61144 * s ^ 11
    - 147878 * s ^ 10
    + 265263 * s ^ 9
    - 356825 * s ^ 8
    + 364507 * s ^ 7
    - 287088 * s ^ 6
    + 174830 * s ^ 5
    - 79300 * s ^ 4
    + 24337 * s ^ 3
    - 3694 * s ^ 2
    - 378 * s
    + 109

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient21 (s : ℚ) : ℚ :=
  s ^ 12
    - 20 * s ^ 11
    + 176 * s ^ 10
    - 894 * s ^ 9
    + 2892 * s ^ 8
    - 6200 * s ^ 7
    + 8881 * s ^ 6
    - 8375 * s ^ 5
    + 5007 * s ^ 4
    - 1681 * s ^ 3
    + 80 * s ^ 2
    + 160 * s
    - 27

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient22 (s : ℚ) : ℚ :=
  -s ^ 5
    + 9 * s ^ 4
    - 29 * s ^ 3
    + 40 * s ^ 2
    - 22 * s
    + 3

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
    t2Step3Coefficient22 s * r ^ 22

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_0 (s : ℚ) :
    t2Step3Coefficient0 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient0,
    t2Step2Coefficient0,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_1 (s : ℚ) :
    t2Step3Coefficient1 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient1,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_2 (s : ℚ) :
    t2Step3Coefficient2 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient2,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_3 (s : ℚ) :
    t2Step3Coefficient3 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient3,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_4 (s : ℚ) :
    t2Step3Coefficient4 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient4,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_5 (s : ℚ) :
    t2Step3Coefficient5 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient5,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_6 (s : ℚ) :
    t2Step3Coefficient6 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient6,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_7 (s : ℚ) :
    t2Step3Coefficient7 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient7,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_8 (s : ℚ) :
    t2Step3Coefficient8 s =
    t2Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient8,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_9 (s : ℚ) :
    t2Step3Coefficient9 s =
    t2Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient9,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_10 (s : ℚ) :
    t2Step3Coefficient10 s =
    t2Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient10,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_11 (s : ℚ) :
    t2Step3Coefficient11 s =
    t2Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient11,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_12 (s : ℚ) :
    t2Step3Coefficient12 s =
    t2Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient12,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_13 (s : ℚ) :
    t2Step3Coefficient13 s =
    t2Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient13,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_14 (s : ℚ) :
    t2Step3Coefficient14 s =
    t2Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient14,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_15 (s : ℚ) :
    t2Step3Coefficient15 s =
    t2Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient1 s
    := by
  simp only [t2Step3Coefficient15,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_16 (s : ℚ) :
    t2Step3Coefficient16 s =
    t2Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient2 s
    := by
  simp only [t2Step3Coefficient16,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_17 (s : ℚ) :
    t2Step3Coefficient17 s =
    t2Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient3 s
    := by
  simp only [t2Step3Coefficient17,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_18 (s : ℚ) :
    t2Step3Coefficient18 s =
    t2Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient4 s
    := by
  simp only [t2Step3Coefficient18,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_19 (s : ℚ) :
    t2Step3Coefficient19 s =
    t2Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient5 s
    := by
  simp only [t2Step3Coefficient19,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_20 (s : ℚ) :
    t2Step3Coefficient20 s =
    t2Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient6 s
    := by
  simp only [t2Step3Coefficient20,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_21 (s : ℚ) :
    t2Step3Coefficient21 s =
    t2Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient7 s
    := by
  simp only [t2Step3Coefficient21,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_22 (s : ℚ) :
    t2Step3Coefficient22 s =
    t2Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient8 s
    := by
  simp only [t2Step3Coefficient22,
    t2Step2Coefficient14,
    rawUnitTwoDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step3_eq_t2Step2_mul_rawUnitTwoDenominator (r s : ℚ) :
    t2Step3 r s = t2Step2 r s * rawUnitTwoDenominator r s := by
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
  simp only [t2Step3, t2Step2, rawUnitTwoDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 31
    + 3 * s ^ 30
    - 6 * s ^ 29
    + 8 * s ^ 28
    - 8 * s ^ 27
    + 6 * s ^ 26
    - 3 * s ^ 25
    + s ^ 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient2 (s : ℚ) : ℚ :=
  s ^ 37
    - 6 * s ^ 36
    + 21 * s ^ 35
    - 55 * s ^ 34
    + 119 * s ^ 33
    - 227 * s ^ 32
    + 379 * s ^ 31
    - 502 * s ^ 30
    + 521 * s ^ 29
    - 367 * s ^ 28
    + 108 * s ^ 27
    + 141 * s ^ 26
    - 271 * s ^ 25
    + 248 * s ^ 24
    - 158 * s ^ 23
    + 66 * s ^ 22
    - 23 * s ^ 21
    + 6 * s ^ 20
    - s ^ 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient3 (s : ℚ) : ℚ :=
  s ^ 40
    - 9 * s ^ 39
    + 47 * s ^ 38
    - 170 * s ^ 37
    + 436 * s ^ 36
    - 860 * s ^ 35
    + 1345 * s ^ 34
    - 1609 * s ^ 33
    + 1034 * s ^ 32
    + 1645 * s ^ 31
    - 7753 * s ^ 30
    + 16557 * s ^ 29
    - 25332 * s ^ 28
    + 29628 * s ^ 27
    - 27390 * s ^ 26
    + 19630 * s ^ 25
    - 10172 * s ^ 24
    + 3159 * s ^ 23
    + 284 * s ^ 22
    - 891 * s ^ 21
    + 632 * s ^ 20
    - 290 * s ^ 19
    + 94 * s ^ 18
    - 18 * s ^ 17
    + 2 * s ^ 16

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient4 (s : ℚ) : ℚ :=
  2 * s ^ 41
    - 15 * s ^ 40
    + 24 * s ^ 39
    + 183 * s ^ 38
    - 1571 * s ^ 37
    + 6675 * s ^ 36
    - 19707 * s ^ 35
    + 46398 * s ^ 34
    - 93563 * s ^ 33
    + 167904 * s ^ 32
    - 268884 * s ^ 31
    + 370882 * s ^ 30
    - 419306 * s ^ 29
    + 364784 * s ^ 28
    - 196633 * s ^ 27
    - 25605 * s ^ 26
    + 215121 * s ^ 25
    - 300947 * s ^ 24
    + 273985 * s ^ 23
    - 186725 * s ^ 22
    + 96844 * s ^ 21
    - 39822 * s ^ 20
    + 12172 * s ^ 19
    - 2193 * s ^ 18
    - 167 * s ^ 17
    + 226 * s ^ 16
    - 72 * s ^ 15
    + 11 * s ^ 14
    - s ^ 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient5 (s : ℚ) : ℚ :=
  s ^ 43
    - 14 * s ^ 42
    + 123 * s ^ 41
    - 830 * s ^ 40
    + 4119 * s ^ 39
    - 15224 * s ^ 38
    + 43563 * s ^ 37
    - 98332 * s ^ 36
    + 179998 * s ^ 35
    - 277791 * s ^ 34
    + 358462 * s ^ 33
    - 322835 * s ^ 32
    - 75678 * s ^ 31
    + 1220086 * s ^ 30
    - 3323037 * s ^ 29
    + 6043652 * s ^ 28
    - 8478326 * s ^ 27
    + 9528004 * s ^ 26
    - 8677788 * s ^ 25
    + 6258220 * s ^ 24
    - 3339962 * s ^ 23
    + 1031767 * s ^ 22
    + 203151 * s ^ 21
    - 527918 * s ^ 20
    + 434358 * s ^ 19
    - 247355 * s ^ 18
    + 107557 * s ^ 17
    - 35485 * s ^ 16
    + 8997 * s ^ 15
    - 1714 * s ^ 14
    + 256 * s ^ 13
    - 27 * s ^ 12
    + 2 * s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient6 (s : ℚ) : ℚ :=
  2 * s ^ 44
    - 31 * s ^ 43
    + 244 * s ^ 42
    - 1294 * s ^ 41
    + 4625 * s ^ 40
    - 9154 * s ^ 39
    - 4030 * s ^ 38
    + 105579 * s ^ 37
    - 458848 * s ^ 36
    + 1329400 * s ^ 35
    - 3120504 * s ^ 34
    + 6600790 * s ^ 33
    - 13151193 * s ^ 32
    + 24359373 * s ^ 31
    - 40104262 * s ^ 30
    + 56159022 * s ^ 29
    - 64711579 * s ^ 28
    + 58569745 * s ^ 27
    - 36187218 * s ^ 26
    + 4423987 * s ^ 25
    + 25127408 * s ^ 24
    - 41899707 * s ^ 23
    + 42809834 * s ^ 22
    - 32885235 * s ^ 21
    + 19976836 * s ^ 20
    - 9860006 * s ^ 19
    + 3838968 * s ^ 18
    - 1052270 * s ^ 17
    + 102262 * s ^ 16
    + 74521 * s ^ 15
    - 52656 * s ^ 14
    + 19902 * s ^ 13
    - 5491 * s ^ 12
    + 1140 * s ^ 11
    - 177 * s ^ 10
    + 18 * s ^ 9
    - s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient7 (s : ℚ) : ℚ :=
  s ^ 45
    - 11 * s ^ 44
    + 4 * s ^ 43
    + 701 * s ^ 42
    - 7370 * s ^ 41
    + 45905 * s ^ 40
    - 203577 * s ^ 39
    + 685872 * s ^ 38
    - 1846140 * s ^ 37
    + 4185692 * s ^ 36
    - 8575084 * s ^ 35
    + 17140953 * s ^ 34
    - 33791575 * s ^ 33
    + 60967019 * s ^ 32
    - 90752657 * s ^ 31
    + 95832606 * s ^ 30
    - 35576908 * s ^ 29
    - 116450265 * s ^ 28
    + 344032890 * s ^ 27
    - 582203090 * s ^ 26
    + 742606095 * s ^ 25
    - 762395846 * s ^ 24
    + 637872791 * s ^ 23
    - 430779747 * s ^ 22
    + 226178194 * s ^ 21
    - 81284753 * s ^ 20
    + 7181025 * s ^ 19
    + 17900730 * s ^ 18
    - 18477219 * s ^ 17
    + 11593342 * s ^ 16
    - 5385770 * s ^ 15
    + 1964914 * s ^ 14
    - 570548 * s ^ 13
    + 132540 * s ^ 12
    - 23372 * s ^ 11
    + 2796 * s ^ 10
    - 123 * s ^ 9
    - 18 * s ^ 8
    + 3 * s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient8 (s : ℚ) : ℚ :=
  7 * s ^ 45
    - 155 * s ^ 44
    + 1579 * s ^ 43
    - 10042 * s ^ 42
    + 44694 * s ^ 41
    - 141734 * s ^ 40
    + 299329 * s ^ 39
    - 310963 * s ^ 38
    - 304526 * s ^ 37
    + 1673404 * s ^ 36
    - 2331802 * s ^ 35
    + 1729690 * s ^ 34
    - 16492623 * s ^ 33
    + 111310330 * s ^ 32
    - 415850460 * s ^ 31
    + 1078349369 * s ^ 30
    - 2138889328 * s ^ 29
    + 3410152049 * s ^ 28
    - 4490561235 * s ^ 27
    + 4925877763 * s ^ 26
    - 4447396205 * s ^ 25
    + 3152692616 * s ^ 24
    - 1485551979 * s ^ 23
    + 28322150 * s ^ 22
    + 834152574 * s ^ 21
    - 1072650485 * s ^ 20
    + 910865839 * s ^ 19
    - 615637266 * s ^ 18
    + 345566957 * s ^ 17
    - 161538918 * s ^ 16
    + 61936408 * s ^ 15
    - 19237324 * s ^ 14
    + 4679226 * s ^ 13
    - 824469 * s ^ 12
    + 67288 * s ^ 11
    + 13652 * s ^ 10
    - 6413 * s ^ 9
    + 1083 * s ^ 8
    - 78 * s ^ 7
    - 2 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient9 (s : ℚ) : ℚ :=
  2 * s ^ 46
    - 35 * s ^ 45
    + 188 * s ^ 44
    + 579 * s ^ 43
    - 15168 * s ^ 42
    + 118197 * s ^ 41
    - 589150 * s ^ 40
    + 2121385 * s ^ 39
    - 5777248 * s ^ 38
    + 12773516 * s ^ 37
    - 28037588 * s ^ 36
    + 80165796 * s ^ 35
    - 274138938 * s ^ 34
    + 860817127 * s ^ 33
    - 2227836270 * s ^ 32
    + 4686130979 * s ^ 31
    - 8061623832 * s ^ 30
    + 11374333169 * s ^ 29
    - 13019051624 * s ^ 28
    + 11485258025 * s ^ 27
    - 6211745337 * s ^ 26
    - 1845643166 * s ^ 25
    + 10348969625 * s ^ 24
    - 16551924454 * s ^ 23
    + 18664354324 * s ^ 22
    - 16839157001 * s ^ 21
    + 12738301901 * s ^ 20
    - 8284932053 * s ^ 19
    + 4689264214 * s ^ 18
    - 2278825817 * s ^ 17
    + 922139908 * s ^ 16
    - 295484736 * s ^ 15
    + 68669016 * s ^ 14
    - 7729409 * s ^ 13
    - 2025323 * s ^ 12
    + 1524525 * s ^ 11
    - 494478 * s ^ 10
    + 99196 * s ^ 9
    - 10110 * s ^ 8
    - 65 * s ^ 7
    + 132 * s ^ 6
    - 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient10 (s : ℚ) : ℚ :=
  6 * s ^ 46
    - 167 * s ^ 45
    + 2061 * s ^ 44
    - 15109 * s ^ 43
    + 73791 * s ^ 42
    - 251667 * s ^ 41
    + 613888 * s ^ 40
    - 1349598 * s ^ 39
    + 5784451 * s ^ 38
    - 36609044 * s ^ 37
    + 184872373 * s ^ 36
    - 698105351 * s ^ 35
    + 2036711081 * s ^ 34
    - 4694441466 * s ^ 33
    + 8578156390 * s ^ 32
    - 12119248217 * s ^ 31
    + 11855682303 * s ^ 30
    - 3353550332 * s ^ 29
    - 16538197532 * s ^ 28
    + 47397216563 * s ^ 27
    - 84115814710 * s ^ 26
    + 117553207662 * s ^ 25
    - 137568734809 * s ^ 24
    + 137721746019 * s ^ 23
    - 119009577637 * s ^ 22
    + 89484593567 * s ^ 21
    - 58997972184 * s ^ 20
    + 34230075273 * s ^ 19
    - 17253332643 * s ^ 18
    + 7172442697 * s ^ 17
    - 2196738468 * s ^ 16
    + 318680748 * s ^ 15
    + 121606613 * s ^ 14
    - 116988871 * s ^ 13
    + 53169142 * s ^ 12
    - 17025107 * s ^ 11
    + 3813319 * s ^ 10
    - 501142 * s ^ 9
    - 6199 * s ^ 8
    + 14348 * s ^ 7
    - 2027 * s ^ 6
    - 18 * s ^ 5
    + 3 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient11 (s : ℚ) : ℚ :=
  s ^ 47
    - 22 * s ^ 46
    + 169 * s ^ 45
    - 130 * s ^ 44
    - 6591 * s ^ 43
    + 45138 * s ^ 42
    - 32039 * s ^ 41
    - 1554675 * s ^ 40
    + 14451233 * s ^ 39
    - 78751314 * s ^ 38
    + 309474020 * s ^ 37
    - 925575578 * s ^ 36
    + 2105820548 * s ^ 35
    - 3383274122 * s ^ 34
    + 2424385796 * s ^ 33
    + 6256089827 * s ^ 32
    - 31220806917 * s ^ 31
    + 81412588046 * s ^ 30
    - 161280408728 * s ^ 29
    + 266271179128 * s ^ 28
    - 381075006986 * s ^ 27
    + 480971106970 * s ^ 26
    - 537638095024 * s ^ 25
    + 530884487967 * s ^ 24
    - 460961983636 * s ^ 23
    + 351203014839 * s ^ 22
    - 235335869294 * s ^ 21
    + 138558369281 * s ^ 20
    - 70070365505 * s ^ 19
    + 27647020497 * s ^ 18
    - 5428554512 * s ^ 17
    - 2792746841 * s ^ 16
    + 3642156000 * s ^ 15
    - 2215171398 * s ^ 14
    + 955887702 * s ^ 13
    - 314147323 * s ^ 12
    + 77420141 * s ^ 11
    - 11275842 * s ^ 10
    - 449526 * s ^ 9
    + 729039 * s ^ 8
    - 164074 * s ^ 7
    + 12655 * s ^ 6
    + 1147 * s ^ 5
    - 66 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient12 (s : ℚ) : ℚ :=
  s ^ 47
    - 27 * s ^ 46
    + 212 * s ^ 45
    + 1199 * s ^ 44
    - 40412 * s ^ 43
    + 433890 * s ^ 42
    - 2940474 * s ^ 41
    + 14261843 * s ^ 40
    - 50516365 * s ^ 39
    + 119981468 * s ^ 38
    - 92733172 * s ^ 37
    - 753988651 * s ^ 36
    + 4779386827 * s ^ 35
    - 17570654580 * s ^ 34
    + 49159869297 * s ^ 33
    - 113074429989 * s ^ 32
    + 222053907307 * s ^ 31
    - 381613820573 * s ^ 30
    + 584351034419 * s ^ 29
    - 806734143208 * s ^ 28
    + 1007771246392 * s ^ 27
    - 1132813865512 * s ^ 26
    + 1132449687492 * s ^ 25
    - 993692732769 * s ^ 24
    + 757293151477 * s ^ 23
    - 498137907578 * s ^ 22
    + 279251830531 * s ^ 21
    - 123058856485 * s ^ 20
    + 23662208384 * s ^ 19
    + 30188646338 * s ^ 18
    - 46980277974 * s ^ 17
    + 38914098956 * s ^ 16
    - 22824147487 * s ^ 15
    + 10113453913 * s ^ 14
    - 3472257144 * s ^ 13
    + 882175733 * s ^ 12
    - 124707877 * s ^ 11
    - 21995568 * s ^ 10
    + 19977176 * s ^ 9
    - 6202661 * s ^ 8
    + 887292 * s ^ 7
    - 5888 * s ^ 6
    - 16376 * s ^ 5
    + 593 * s ^ 4
    + 30 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient13 (s : ℚ) : ℚ :=
  3 * s ^ 47
    - 106 * s ^ 46
    + 1692 * s ^ 45
    - 15512 * s ^ 44
    + 81445 * s ^ 43
    - 113938 * s ^ 42
    - 2141476 * s ^ 41
    + 24089683 * s ^ 40
    - 155764638 * s ^ 39
    + 751327090 * s ^ 38
    - 2915056594 * s ^ 37
    + 9419556333 * s ^ 36
    - 25885915454 * s ^ 35
    + 61430166170 * s ^ 34
    - 127616245159 * s ^ 33
    + 235489368133 * s ^ 32
    - 392180336366 * s ^ 31
    + 597887195036 * s ^ 30
    - 840212053487 * s ^ 29
    + 1082422346511 * s ^ 28
    - 1253937187187 * s ^ 27
    + 1268876318596 * s ^ 26
    - 1083681440177 * s ^ 25
    + 747540073142 * s ^ 24
    - 381835764760 * s ^ 23
    + 93295444894 * s ^ 22
    + 94152515393 * s ^ 21
    - 213878261956 * s ^ 20
    + 284339849626 * s ^ 19
    - 293083963173 * s ^ 18
    + 235712117980 * s ^ 17
    - 145467613802 * s ^ 16
    + 68382536660 * s ^ 15
    - 23995573580 * s ^ 14
    + 5768011189 * s ^ 13
    - 376699368 * s ^ 12
    - 516390832 * s ^ 11
    + 352563733 * s ^ 10
    - 128198014 * s ^ 9
    + 27517550 * s ^ 8
    - 1970303 * s ^ 7
    - 501935 * s ^ 6
    + 129408 * s ^ 5
    - 2017 * s ^ 4
    - 433 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient14 (s : ℚ) : ℚ :=
  5 * s ^ 47
    - 218 * s ^ 46
    + 4519 * s ^ 45
    - 59467 * s ^ 44
    + 560299 * s ^ 43
    - 4046467 * s ^ 42
    + 23404632 * s ^ 41
    - 111592698 * s ^ 40
    + 446731088 * s ^ 39
    - 1519142976 * s ^ 38
    + 4426876016 * s ^ 37
    - 11155289714 * s ^ 36
    + 24608119084 * s ^ 35
    - 48435994877 * s ^ 34
    + 87558853459 * s ^ 33
    - 150344682670 * s ^ 32
    + 249697790306 * s ^ 31
    - 394141622138 * s ^ 30
    + 562791912022 * s ^ 29
    - 680102442111 * s ^ 28
    + 633078392235 * s ^ 27
    - 356518052960 * s ^ 26
    - 77532287648 * s ^ 25
    + 486192274943 * s ^ 24
    - 728492145359 * s ^ 23
    + 828647923172 * s ^ 22
    - 914310318494 * s ^ 21
    + 1029107189929 * s ^ 20
    - 1068512598886 * s ^ 19
    + 922598907721 * s ^ 18
    - 620808087032 * s ^ 17
    + 310054084307 * s ^ 16
    - 106598345002 * s ^ 15
    + 17692044039 * s ^ 14
    + 6091512313 * s ^ 13
    - 7269644879 * s ^ 12
    + 4121524382 * s ^ 11
    - 1672919816 * s ^ 10
    + 457543080 * s ^ 9
    - 63525977 * s ^ 8
    - 6615185 * s ^ 7
    + 4432979 * s ^ 6
    - 659100 * s ^ 5
    - 10862 * s ^ 4
    + 4006 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient15 (s : ℚ) : ℚ :=
  s ^ 48
    - 40 * s ^ 47
    + 767 * s ^ 46
    - 9358 * s ^ 45
    + 81469 * s ^ 44
    - 538238 * s ^ 43
    + 2795976 * s ^ 42
    - 11602508 * s ^ 41
    + 38261661 * s ^ 40
    - 96755908 * s ^ 39
    + 168807773 * s ^ 38
    - 125458258 * s ^ 37
    - 251080410 * s ^ 36
    + 592220406 * s ^ 35
    + 2261459355 * s ^ 34
    - 17672962159 * s ^ 33
    + 61011501864 * s ^ 32
    - 140040558047 * s ^ 31
    + 224546170718 * s ^ 30
    - 222442020012 * s ^ 29
    + 11497129190 * s ^ 28
    + 450757528469 * s ^ 27
    - 1021994801616 * s ^ 26
    + 1436713145264 * s ^ 25
    - 1555883169984 * s ^ 24
    + 1550529291775 * s ^ 23
    - 1747908451077 * s ^ 22
    + 2230882761661 * s ^ 21
    - 2652444772596 * s ^ 20
    + 2561923788572 * s ^ 19
    - 1882086525940 * s ^ 18
    + 977673491097 * s ^ 17
    - 290499941401 * s ^ 16
    - 24912538438 * s ^ 15
    + 89096132187 * s ^ 14
    - 64493187302 * s ^ 13
    + 33643355911 * s ^ 12
    - 14288543352 * s ^ 11
    + 4698067384 * s ^ 10
    - 920169630 * s ^ 9
    - 21526963 * s ^ 8
    + 78323584 * s ^ 7
    - 22027819 * s ^ 6
    + 2165584 * s ^ 5
    + 187051 * s ^ 4
    - 26662 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient16 (s : ℚ) : ℚ :=
  -4 * s ^ 47
    + 145 * s ^ 46
    - 2541 * s ^ 45
    + 28653 * s ^ 44
    - 233747 * s ^ 43
    + 1467902 * s ^ 42
    - 7317620 * s ^ 41
    + 28988042 * s ^ 40
    - 87362075 * s ^ 39
    + 167738081 * s ^ 38
    + 24516447 * s ^ 37
    - 1788313640 * s ^ 36
    + 8702346148 * s ^ 35
    - 27177549267 * s ^ 34
    + 62170998157 * s ^ 33
    - 102605499078 * s ^ 32
    + 99468545360 * s ^ 31
    + 38496723134 * s ^ 30
    - 392620220190 * s ^ 29
    + 924293652652 * s ^ 28
    - 1405693029563 * s ^ 27
    + 1552302958699 * s ^ 26
    - 1358492011858 * s ^ 25
    + 1296808460806 * s ^ 24
    - 1994665765357 * s ^ 23
    + 3529096877362 * s ^ 22
    - 5067773810234 * s ^ 21
    + 5442487806026 * s ^ 20
    - 4223288586636 * s ^ 19
    + 2126081184902 * s ^ 18
    - 325188160583 * s ^ 17
    - 527150466150 * s ^ 16
    + 599532111442 * s ^ 15
    - 385213341785 * s ^ 14
    + 191636022971 * s ^ 13
    - 83006130127 * s ^ 12
    + 30431749991 * s ^ 11
    - 7664677724 * s ^ 10
    + 173261762 * s ^ 9
    + 820110957 * s ^ 8
    - 371853546 * s ^ 7
    + 73397749 * s ^ 6
    - 3419944 * s ^ 5
    - 1331368 * s ^ 4
    + 135624 * s ^ 3
    + 25 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient17 (s : ℚ) : ℚ :=
  -s ^ 47
    + 46 * s ^ 46
    - 980 * s ^ 45
    + 13206 * s ^ 44
    - 128898 * s ^ 43
    + 986000 * s ^ 42
    - 6205665 * s ^ 41
    + 32956157 * s ^ 40
    - 148582492 * s ^ 39
    + 564608943 * s ^ 38
    - 1777558833 * s ^ 37
    + 4483263258 * s ^ 36
    - 8308310443 * s ^ 35
    + 7606652161 * s ^ 34
    + 16360639335 * s ^ 33
    - 100896626030 * s ^ 32
    + 287424411493 * s ^ 31
    - 569425395926 * s ^ 30
    + 823425857855 * s ^ 29
    - 816081569292 * s ^ 28
    + 402387889077 * s ^ 27
    + 132909254209 * s ^ 26
    + 43308660823 * s ^ 25
    - 1790587328578 * s ^ 24
    + 5015174986833 * s ^ 23
    - 8179929080835 * s ^ 22
    + 9149313048837 * s ^ 21
    - 6953828965246 * s ^ 20
    + 2775733849975 * s ^ 19
    + 1004604807276 * s ^ 18
    - 2747671543860 * s ^ 17
    + 2551333724764 * s ^ 16
    - 1577726132438 * s ^ 15
    + 759383883755 * s ^ 14
    - 320339264616 * s ^ 13
    + 124376654606 * s ^ 12
    - 36490000416 * s ^ 11
    + 1469753056 * s ^ 10
    + 6069272462 * s ^ 9
    - 3737688300 * s ^ 8
    + 1152497988 * s ^ 7
    - 161124071 * s ^ 6
    - 8061333 * s ^ 5
    + 6442746 * s ^ 4
    - 546311 * s ^ 3
    - 297 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient18 (s : ℚ) : ℚ :=
  2 * s ^ 46
    - 69 * s ^ 45
    + 1127 * s ^ 44
    - 12082 * s ^ 43
    + 102868 * s ^ 42
    - 799715 * s ^ 41
    + 5898161 * s ^ 40
    - 39199084 * s ^ 39
    + 222113452 * s ^ 38
    - 1047683903 * s ^ 37
    + 4098764561 * s ^ 36
    - 13311251699 * s ^ 35
    + 35694432640 * s ^ 34
    - 77362584234 * s ^ 33
    + 127811940212 * s ^ 32
    - 131790361436 * s ^ 31
    - 24650388882 * s ^ 30
    + 450357303086 * s ^ 29
    - 1055402679188 * s ^ 28
    + 1311753537602 * s ^ 27
    - 279726986828 * s ^ 26
    - 2768765482170 * s ^ 25
    + 7331886042079 * s ^ 24
    - 11229097887481 * s ^ 23
    + 11653983810595 * s ^ 22
    - 7374266155173 * s ^ 21
    + 190548851208 * s ^ 20
    + 6107598375868 * s ^ 19
    - 8623319044177 * s ^ 18
    + 7327596559151 * s ^ 17
    - 4403237188895 * s ^ 16
    + 1990132493161 * s ^ 15
    - 749285410984 * s ^ 14
    + 274706775466 * s ^ 13
    - 86410183858 * s ^ 12
    - 4916432656 * s ^ 11
    + 33291459313 * s ^ 10
    - 25330258140 * s ^ 9
    + 10526105319 * s ^ 8
    - 2471152282 * s ^ 7
    + 158614950 * s ^ 6
    + 79857002 * s ^ 5
    - 23677637 * s ^ 4
    + 1780520 * s ^ 3
    + 2230 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient19 (s : ℚ) : ℚ :=
  4 * s ^ 45
    - 206 * s ^ 44
    + 4753 * s ^ 43
    - 66497 * s ^ 42
    + 636670 * s ^ 41
    - 4428140 * s ^ 40
    + 22965986 * s ^ 39
    - 88121079 * s ^ 38
    + 228989596 * s ^ 37
    - 205057692 * s ^ 36
    - 1652314467 * s ^ 35
    + 11736489237 * s ^ 34
    - 47262805980 * s ^ 33
    + 140489500744 * s ^ 32
    - 323578023838 * s ^ 31
    + 565648648268 * s ^ 30
    - 654994959102 * s ^ 29
    + 105865932102 * s ^ 28
    + 1710156896612 * s ^ 27
    - 5024983357692 * s ^ 26
    + 8916205136936 * s ^ 25
    - 11085326769843 * s ^ 24
    + 8938940670769 * s ^ 23
    - 1693532709973 * s ^ 22
    - 8169098438182 * s ^ 21
    + 15921194351662 * s ^ 20
    - 17866398374554 * s ^ 19
    + 14058860785137 * s ^ 18
    - 7860305846849 * s ^ 17
    + 2916965279226 * s ^ 16
    - 587414458623 * s ^ 15
    + 19863833123 * s ^ 14
    + 31953819113 * s ^ 13
    - 89978587978 * s ^ 12
    + 140061020259 * s ^ 11
    - 119358766059 * s ^ 10
    + 63260729952 * s ^ 9
    - 20671387904 * s ^ 8
    + 3258591435 * s ^ 7
    + 403164539 * s ^ 6
    - 327363821 * s ^ 5
    + 69158792 * s ^ 4
    - 4754561 * s ^ 3
    - 11875 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient20 (s : ℚ) : ℚ :=
  s ^ 45
    - 61 * s ^ 44
    + 1667 * s ^ 43
    - 27755 * s ^ 42
    + 320363 * s ^ 41
    - 2754357 * s ^ 40
    + 18473661 * s ^ 39
    - 99850088 * s ^ 38
    + 444949376 * s ^ 37
    - 1655360954 * s ^ 36
    + 5130530293 * s ^ 35
    - 12884857633 * s ^ 34
    + 23927064556 * s ^ 33
    - 20853270020 * s ^ 32
    - 59764679010 * s ^ 31
    + 364680447743 * s ^ 30
    - 1121253987149 * s ^ 29
    + 2503158156112 * s ^ 28
    - 4302675126124 * s ^ 27
    + 5552045928916 * s ^ 26
    - 4545119992974 * s ^ 25
    - 282986737541 * s ^ 24
    + 8828826154196 * s ^ 23
    - 18329556779697 * s ^ 22
    + 24299147537927 * s ^ 21
    - 23424860353323 * s ^ 20
    + 16249994087467 * s ^ 19
    - 6960566769098 * s ^ 18
    + 186418454053 * s ^ 17
    + 2260323470208 * s ^ 16
    - 1809117386778 * s ^ 15
    + 822221140850 * s ^ 14
    - 419202252657 * s ^ 13
    + 419744499167 * s ^ 12
    - 399582579902 * s ^ 11
    + 260188287334 * s ^ 10
    - 110909316428 * s ^ 9
    + 26742651238 * s ^ 8
    - 219196702 * s ^ 7
    - 2482551099 * s ^ 6
    + 935343536 * s ^ 5
    - 164180166 * s ^ 4
    + 10463199 * s ^ 3
    + 47652 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient21 (s : ℚ) : ℚ :=
  -3 * s ^ 44
    + 147 * s ^ 43
    - 3397 * s ^ 42
    + 49567 * s ^ 41
    - 516289 * s ^ 40
    + 4124372 * s ^ 39
    - 26597943 * s ^ 38
    + 144224659 * s ^ 37
    - 678265767 * s ^ 36
    + 2817180334 * s ^ 35
    - 10373901320 * s ^ 34
    + 33624542626 * s ^ 33
    - 94691893187 * s ^ 32
    + 227783426237 * s ^ 31
    - 455728133418 * s ^ 30
    + 715566262004 * s ^ 29
    - 727712942013 * s ^ 28
    - 110691660869 * s ^ 27
    + 2605387894842 * s ^ 26
    - 7226663654161 * s ^ 25
    + 13298096357572 * s ^ 24
    - 18571775119933 * s ^ 23
    + 19982556237956 * s ^ 22
    - 15635951731325 * s ^ 21
    + 6710579289186 * s ^ 20
    + 2694942475384 * s ^ 19
    - 8243501843873 * s ^ 18
    + 8441811632364 * s ^ 17
    - 5327691895975 * s ^ 16
    + 2210584661968 * s ^ 15
    - 842551828160 * s ^ 14
    + 792982204669 * s ^ 13
    - 935433681271 * s ^ 12
    + 758050114093 * s ^ 11
    - 404134286061 * s ^ 10
    + 131128975435 * s ^ 9
    - 12052113703 * s ^ 8
    - 11839427864 * s ^ 7
    + 7199812870 * s ^ 6
    - 2061043184 * s ^ 5
    + 320195441 * s ^ 4
    - 18972782 * s ^ 3
    - 149211 * s ^ 2
    - 17 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient22 (s : ℚ) : ℚ :=
  2 * s ^ 43
    - 74 * s ^ 42
    + 1186 * s ^ 41
    - 9867 * s ^ 40
    + 27990 * s ^ 39
    + 316122 * s ^ 38
    - 4668837 * s ^ 37
    + 31477530 * s ^ 36
    - 125747868 * s ^ 35
    + 213382807 * s ^ 34
    + 962508912 * s ^ 33
    - 10039979838 * s ^ 32
    + 50552560209 * s ^ 31
    - 185617421980 * s ^ 30
    + 546122879906 * s ^ 29
    - 1332190451401 * s ^ 28
    + 2722447022653 * s ^ 27
    - 4641035247687 * s ^ 26
    + 6464564201998 * s ^ 25
    - 6952856055514 * s ^ 24
    + 4734290815798 * s ^ 23
    + 652826306452 * s ^ 22
    - 7809158949231 * s ^ 21
    + 13679633308360 * s ^ 20
    - 15342094020278 * s ^ 19
    + 12204128967432 * s ^ 18
    - 6592243154990 * s ^ 17
    + 1959135657627 * s ^ 16
    - 215416380747 * s ^ 15
    + 690819952756 * s ^ 14
    - 1527381946138 * s ^ 13
    + 1610906802199 * s ^ 12
    - 1050074985481 * s ^ 11
    + 423395058034 * s ^ 10
    - 65091280699 * s ^ 9
    - 41405641969 * s ^ 8
    + 36328361033 * s ^ 7
    - 14765400972 * s ^ 6
    + 3627837480 * s ^ 5
    - 514632648 * s ^ 4
    + 28157652 * s ^ 3
    + 371947 * s ^ 2
    + 134 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient23 (s : ℚ) : ℚ :=
  2 * s ^ 42
    - 123 * s ^ 41
    + 3454 * s ^ 40
    - 59925 * s ^ 39
    + 727042 * s ^ 38
    - 6594682 * s ^ 37
    + 46626018 * s ^ 36
    - 264531264 * s ^ 35
    + 1231230449 * s ^ 34
    - 4785023290 * s ^ 33
    + 15737537012 * s ^ 32
    - 44120037038 * s ^ 31
    + 105101124168 * s ^ 30
    - 208201067955 * s ^ 29
    + 322136772037 * s ^ 28
    - 310436682772 * s ^ 27
    - 126980067389 * s ^ 26
    + 1414483711961 * s ^ 25
    - 3867573038483 * s ^ 24
    + 7289898015568 * s ^ 23
    - 10657046317986 * s ^ 22
    + 12319825686180 * s ^ 21
    - 10947083634474 * s ^ 20
    + 6701671213362 * s ^ 19
    - 1558005359375 * s ^ 18
    - 1854643682115 * s ^ 17
    + 2151345561505 * s ^ 16
    - 176968525799 * s ^ 15
    - 1931471283102 * s ^ 14
    + 2657934860290 * s ^ 13
    - 2025888048187 * s ^ 12
    + 949430891590 * s ^ 11
    - 177666999818 * s ^ 10
    - 120257663784 * s ^ 9
    + 132773790134 * s ^ 8
    - 68975581076 * s ^ 7
    + 23275367061 * s ^ 6
    - 5164193028 * s ^ 5
    + 679695303 * s ^ 4
    - 33675071 * s ^ 3
    - 745751 * s ^ 2
    - 649 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient24 (s : ℚ) : ℚ :=
  -3 * s ^ 41
    + 154 * s ^ 40
    - 3776 * s ^ 39
    + 58764 * s ^ 38
    - 650793 * s ^ 37
    + 5459464 * s ^ 36
    - 36154949 * s ^ 35
    + 195239941 * s ^ 34
    - 885284496 * s ^ 33
    + 3466413330 * s ^ 32
    - 12012252534 * s ^ 31
    + 37435492854 * s ^ 30
    - 105321955373 * s ^ 29
    + 265691382428 * s ^ 28
    - 593833027245 * s ^ 27
    + 1160803133592 * s ^ 26
    - 1956252703209 * s ^ 25
    + 2781089965597 * s ^ 24
    - 3190064274925 * s ^ 23
    + 2615533220689 * s ^ 22
    - 746506886264 * s ^ 21
    - 2011523178210 * s ^ 20
    + 4442282578474 * s ^ 19
    - 5121172613392 * s ^ 18
    + 3447693931009 * s ^ 17
    - 275357523596 * s ^ 16
    - 2577901726794 * s ^ 15
    + 3684721271303 * s ^ 14
    - 2984576203520 * s ^ 13
    + 1490012035369 * s ^ 12
    - 251035812795 * s ^ 11
    - 316735890555 * s ^ 10
    + 368945140380 * s ^ 9
    - 226947046226 * s ^ 8
    + 95961539785 * s ^ 7
    - 28923921376 * s ^ 6
    + 5948867489 * s ^ 5
    - 731288091 * s ^ 4
    + 31458642 * s ^ 3
    + 1206701 * s ^ 2
    + 2157 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient25 (s : ℚ) : ℚ :=
  s ^ 40
    - 46 * s ^ 39
    + 977 * s ^ 38
    - 12384 * s ^ 37
    + 99611 * s ^ 36
    - 465444 * s ^ 35
    + 316251 * s ^ 34
    + 14010321 * s ^ 33
    - 129729904 * s ^ 32
    + 695526576 * s ^ 31
    - 2622447780 * s ^ 30
    + 7179171806 * s ^ 29
    - 13340421787 * s ^ 28
    + 9791449046 * s ^ 27
    + 39222770716 * s ^ 26
    - 207780940097 * s ^ 25
    + 603803159980 * s ^ 24
    - 1317996335416 * s ^ 23
    + 2310593355968 * s ^ 22
    - 3285604784840 * s ^ 21
    + 3692332901620 * s ^ 20
    - 2980252036966 * s ^ 19
    + 1033640646264 * s ^ 18
    + 1535358129283 * s ^ 17
    - 3589775494680 * s ^ 16
    + 4178759049981 * s ^ 15
    - 3221302838368 * s ^ 14
    + 1506415502365 * s ^ 13
    - 17906212088 * s ^ 12
    - 725700515107 * s ^ 11
    + 794462797733 * s ^ 10
    - 542297893750 * s ^ 9
    + 270864695332 * s ^ 8
    - 101974098448 * s ^ 7
    + 28446909401 * s ^ 6
    - 5504292489 * s ^ 5
    + 631018418 * s ^ 4
    - 21414481 * s ^ 3
    - 1572373 * s ^ 2
    - 5202 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient26 (s : ℚ) : ℚ :=
  -4 * s ^ 38
    + 231 * s ^ 37
    - 6217 * s ^ 36
    + 103850 * s ^ 35
    - 1210485 * s ^ 34
    + 10497193 * s ^ 33
    - 70530154 * s ^ 32
    + 377735656 * s ^ 31
    - 1647808849 * s ^ 30
    + 5961159498 * s ^ 29
    - 18171705323 * s ^ 28
    + 47348084004 * s ^ 27
    - 106618099502 * s ^ 26
    + 208287980935 * s ^ 25
    - 349677705151 * s ^ 24
    + 487567382526 * s ^ 23
    - 513289932596 * s ^ 22
    + 263357794296 * s ^ 21
    + 398295227938 * s ^ 20
    - 1441283781603 * s ^ 19
    + 2566932941353 * s ^ 18
    - 3271471929720 * s ^ 17
    + 3120547155706 * s ^ 16
    - 2080415946795 * s ^ 15
    + 603999871301 * s ^ 14
    + 661699809264 * s ^ 13
    - 1297629990950 * s ^ 12
    + 1299079503745 * s ^ 11
    - 942858167692 * s ^ 10
    + 533003934732 * s ^ 9
    - 238288808931 * s ^ 8
    + 83307291241 * s ^ 7
    - 21964775373 * s ^ 6
    + 4029306188 * s ^ 5
    - 425484587 * s ^ 4
    + 8457099 * s ^ 3
    + 1637792 * s ^ 2
    + 9384 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient27 (s : ℚ) : ℚ :=
  3 * s ^ 37
    - 157 * s ^ 36
    + 3842 * s ^ 35
    - 58576 * s ^ 34
    + 625286 * s ^ 33
    - 4979629 * s ^ 32
    + 30801327 * s ^ 31
    - 152348366 * s ^ 30
    + 617556897 * s ^ 29
    - 2103368297 * s ^ 28
    + 6196084460 * s ^ 27
    - 16319567266 * s ^ 26
    + 39632037803 * s ^ 25
    - 90157133880 * s ^ 24
    + 190992752915 * s ^ 23
    - 369110104919 * s ^ 22
    + 635578639775 * s ^ 21
    - 953718154436 * s ^ 20
    + 1215204814017 * s ^ 19
    - 1256581383436 * s ^ 18
    + 938249702924 * s ^ 17
    - 258847123171 * s ^ 16
    - 587154477623 * s ^ 15
    + 1292156482722 * s ^ 14
    - 1617249972300 * s ^ 13
    + 1523547265704 * s ^ 12
    - 1155833491604 * s ^ 11
    + 721205950070 * s ^ 10
    - 370822885158 * s ^ 9
    + 155390279055 * s ^ 8
    - 51760219590 * s ^ 7
    + 13074536733 * s ^ 6
    - 2276089039 * s ^ 5
    + 214059650 * s ^ 4
    + 1122663 * s ^ 3
    - 1345541 * s ^ 2
    - 12858 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient28 (s : ℚ) : ℚ :=
  -s ^ 36
    + 45 * s ^ 35
    - 932 * s ^ 34
    + 11655 * s ^ 33
    - 96064 * s ^ 32
    + 519318 * s ^ 31
    - 1493544 * s ^ 30
    - 2467968 * s ^ 29
    + 56418648 * s ^ 28
    - 369291371 * s ^ 27
    + 1615084798 * s ^ 26
    - 5363643824 * s ^ 25
    + 14140187658 * s ^ 24
    - 30038982877 * s ^ 23
    + 50925372380 * s ^ 22
    - 64781904634 * s ^ 21
    + 45401618900 * s ^ 20
    + 44647273255 * s ^ 19
    - 237427381430 * s ^ 18
    + 530658966519 * s ^ 17
    - 865157199249 * s ^ 16
    + 1136908623761 * s ^ 15
    - 1248727550231 * s ^ 14
    + 1165834255569 * s ^ 13
    - 931911899246 * s ^ 12
    + 637943674180 * s ^ 11
    - 371826779214 * s ^ 10
    + 182354339998 * s ^ 9
    - 73786013173 * s ^ 8
    + 23850780433 * s ^ 7
    - 5818048092 * s ^ 6
    + 951957451 * s ^ 5
    - 72637366 * s ^ 4
    - 4561821 * s ^ 3
    + 853026 * s ^ 2
    + 13443 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient29 (s : ℚ) : ℚ :=
  2 * s ^ 34
    - 97 * s ^ 33
    + 2240 * s ^ 32
    - 32781 * s ^ 31
    + 341390 * s ^ 30
    - 2694075 * s ^ 29
    + 16758086 * s ^ 28
    - 84458139 * s ^ 27
    + 352274077 * s ^ 26
    - 1238502904 * s ^ 25
    + 3735324885 * s ^ 24
    - 9838954001 * s ^ 23
    + 23035563363 * s ^ 22
    - 48645481042 * s ^ 21
    + 93418594902 * s ^ 20
    - 163137893763 * s ^ 19
    + 257418674052 * s ^ 18
    - 363924742047 * s ^ 17
    + 457784606331 * s ^ 16
    - 510276737944 * s ^ 15
    + 502880073466 * s ^ 14
    - 437055500295 * s ^ 13
    + 333392712297 * s ^ 12
    - 221444248051 * s ^ 11
    + 126599305146 * s ^ 10
    - 61285268181 * s ^ 9
    + 24519632558 * s ^ 8
    - 7798914926 * s ^ 7
    + 1837736962 * s ^ 6
    - 272809137 * s ^ 5
    + 11385104 * s ^ 4
    + 3665552 * s ^ 3
    - 402361 * s ^ 2
    - 10669 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient30 (s : ℚ) : ℚ :=
  -s ^ 32
    + 49 * s ^ 31
    - 1151 * s ^ 30
    + 17244 * s ^ 29
    - 184910 * s ^ 28
    + 1509637 * s ^ 27
    - 9745565 * s ^ 26
    + 51008208 * s ^ 25
    - 220269671 * s ^ 24
    + 794824767 * s ^ 23
    - 2419964309 * s ^ 22
    + 6266370016 * s ^ 21
    - 13898879540 * s ^ 20
    + 26591463812 * s ^ 19
    - 44206750449 * s ^ 18
    + 64344939715 * s ^ 17
    - 82579674190 * s ^ 16
    + 93913373242 * s ^ 15
    - 94769144226 * s ^ 14
    + 84604149570 * s ^ 13
    - 66360938903 * s ^ 12
    + 45281480243 * s ^ 11
    - 26528425282 * s ^ 10
    + 13099266912 * s ^ 9
    - 5298093567 * s ^ 8
    + 1671997989 * s ^ 7
    - 373363364 * s ^ 6
    + 43944278 * s ^ 5
    + 2665449 * s ^ 4
    - 1714316 * s ^ 3
    + 131987 * s ^ 2
    + 6326 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient31 (s : ℚ) : ℚ :=
  2 * s ^ 28
    - 88 * s ^ 27
    + 1838 * s ^ 26
    - 24236 * s ^ 25
    + 226342 * s ^ 24
    - 1592008 * s ^ 23
    + 8755158 * s ^ 22
    - 38581056 * s ^ 21
    + 138532635 * s ^ 20
    - 410105096 * s ^ 19
    + 1009352280 * s ^ 18
    - 2078075821 * s ^ 17
    + 3595843414 * s ^ 16
    - 5249977019 * s ^ 15
    + 6489623622 * s ^ 14
    - 6810881628 * s ^ 13
    + 6076401386 * s ^ 12
    - 4597893935 * s ^ 11
    + 2925209476 * s ^ 10
    - 1535265658 * s ^ 9
    + 641244082 * s ^ 8
    - 198414627 * s ^ 7
    + 37586051 * s ^ 6
    - 449611 * s ^ 5
    - 1984890 * s ^ 4
    + 497720 * s ^ 3
    - 25616 * s ^ 2
    - 2717 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient32 (s : ℚ) : ℚ :=
  -s ^ 24
    + 39 * s ^ 23
    - 714 * s ^ 22
    + 8153 * s ^ 21
    - 65074 * s ^ 20
    + 385614 * s ^ 19
    - 1758826 * s ^ 18
    + 6317327 * s ^ 17
    - 18130390 * s ^ 16
    + 41944222 * s ^ 15
    - 78567236 * s ^ 14
    + 119229856 * s ^ 13
    - 146129084 * s ^ 12
    + 143524379 * s ^ 11
    - 111280023 * s ^ 10
    + 66107592 * s ^ 9
    - 28090646 * s ^ 8
    + 6798703 * s ^ 7
    + 482040 * s ^ 6
    - 1158266 * s ^ 5
    + 461714 * s ^ 4
    - 81334 * s ^ 3
    + 1156 * s ^ 2
    + 799 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient33 (s : ℚ) : ℚ :=
  s ^ 17
    - 28 * s ^ 16
    + 359 * s ^ 15
    - 2792 * s ^ 14
    + 14707 * s ^ 13
    - 55482 * s ^ 12
    + 154529 * s ^ 11
    - 322737 * s ^ 10
    + 507951 * s ^ 9
    - 599998 * s ^ 8
    + 524919 * s ^ 7
    - 332035 * s ^ 6
    + 145593 * s ^ 5
    - 40268 * s ^ 4
    + 4815 * s ^ 3
    + 610 * s ^ 2
    - 144 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient34 (s : ℚ) : ℚ :=
  -s ^ 8
    + 13 * s ^ 7
    - 69 * s ^ 6
    + 192 * s ^ 5
    - 298 * s ^ 4
    + 251 * s ^ 3
    - 100 * s ^ 2
    + 12 * s

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
    termTwoCoefficient34 s * r ^ 34

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_0 (s : ℚ) :
    termTwoCoefficient0 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient0,
    t2Step3Coefficient0,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_1 (s : ℚ) :
    termTwoCoefficient1 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient1,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_2 (s : ℚ) :
    termTwoCoefficient2 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient2,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_3 (s : ℚ) :
    termTwoCoefficient3 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient3,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_4 (s : ℚ) :
    termTwoCoefficient4 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient4,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_5 (s : ℚ) :
    termTwoCoefficient5 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient5,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_6 (s : ℚ) :
    termTwoCoefficient6 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient6,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_7 (s : ℚ) :
    termTwoCoefficient7 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient7,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_8 (s : ℚ) :
    termTwoCoefficient8 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient8,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_9 (s : ℚ) :
    termTwoCoefficient9 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient9,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_10 (s : ℚ) :
    termTwoCoefficient10 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient10,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_11 (s : ℚ) :
    termTwoCoefficient11 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient11,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_12 (s : ℚ) :
    termTwoCoefficient12 s =
    t2Step3Coefficient0 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient12,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_13 (s : ℚ) :
    termTwoCoefficient13 s =
    t2Step3Coefficient1 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient13,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_14 (s : ℚ) :
    termTwoCoefficient14 s =
    t2Step3Coefficient2 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient14,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_15 (s : ℚ) :
    termTwoCoefficient15 s =
    t2Step3Coefficient3 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient15,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_16 (s : ℚ) :
    termTwoCoefficient16 s =
    t2Step3Coefficient4 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient16,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_17 (s : ℚ) :
    termTwoCoefficient17 s =
    t2Step3Coefficient5 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient17,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_18 (s : ℚ) :
    termTwoCoefficient18 s =
    t2Step3Coefficient6 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient18,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_19 (s : ℚ) :
    termTwoCoefficient19 s =
    t2Step3Coefficient7 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient19,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_20 (s : ℚ) :
    termTwoCoefficient20 s =
    t2Step3Coefficient8 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient20,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_21 (s : ℚ) :
    termTwoCoefficient21 s =
    t2Step3Coefficient9 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient21,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_22 (s : ℚ) :
    termTwoCoefficient22 s =
    t2Step3Coefficient10 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient1 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient22,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_23 (s : ℚ) :
    termTwoCoefficient23 s =
    t2Step3Coefficient11 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient2 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient1 s
    := by
  simp only [termTwoCoefficient23,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_24 (s : ℚ) :
    termTwoCoefficient24 s =
    t2Step3Coefficient12 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient3 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient2 s
    := by
  simp only [termTwoCoefficient24,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_25 (s : ℚ) :
    termTwoCoefficient25 s =
    t2Step3Coefficient13 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient4 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient3 s
    := by
  simp only [termTwoCoefficient25,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_26 (s : ℚ) :
    termTwoCoefficient26 s =
    t2Step3Coefficient14 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient5 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient4 s
    := by
  simp only [termTwoCoefficient26,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_27 (s : ℚ) :
    termTwoCoefficient27 s =
    t2Step3Coefficient15 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient6 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient5 s
    := by
  simp only [termTwoCoefficient27,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_28 (s : ℚ) :
    termTwoCoefficient28 s =
    t2Step3Coefficient16 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient7 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient6 s
    := by
  simp only [termTwoCoefficient28,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_29 (s : ℚ) :
    termTwoCoefficient29 s =
    t2Step3Coefficient17 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient8 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient7 s
    := by
  simp only [termTwoCoefficient29,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_30 (s : ℚ) :
    termTwoCoefficient30 s =
    t2Step3Coefficient18 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient9 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient8 s
    := by
  simp only [termTwoCoefficient30,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_31 (s : ℚ) :
    termTwoCoefficient31 s =
    t2Step3Coefficient19 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient10 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient9 s
    := by
  simp only [termTwoCoefficient31,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_32 (s : ℚ) :
    termTwoCoefficient32 s =
    t2Step3Coefficient20 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient11 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient10 s
    := by
  simp only [termTwoCoefficient32,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_33 (s : ℚ) :
    termTwoCoefficient33 s =
    t2Step3Coefficient21 s *
        rawUnitNineDenominatorCoefficient12 s
      + t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient11 s
    := by
  simp only [termTwoCoefficient33,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_34 (s : ℚ) :
    termTwoCoefficient34 s =
    t2Step3Coefficient22 s *
        rawUnitNineDenominatorCoefficient12 s
    := by
  simp only [termTwoCoefficient34,
    t2Step3Coefficient22,
    rawUnitNineDenominatorCoefficient12]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termTwo_eq_t2Step3_mul_rawUnitNineDenominator (r s : ℚ) :
    termTwo r s = t2Step3 r s * rawUnitNineDenominator r s := by
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
  simp only [termTwo, t2Step3, rawUnitNineDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient0 (s : ℚ) : ℚ :=
  s ^ 13
    + s ^ 11
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 17
    + 3 * s ^ 16
    - 8 * s ^ 15
    + 16 * s ^ 14
    - 21 * s ^ 13
    + 4 * s ^ 12
    - 21 * s ^ 11
    + 8 * s ^ 10
    - 20 * s ^ 9
    - 7 * s ^ 8
    + 3 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient2 (s : ℚ) : ℚ :=
  s ^ 19
    - 6 * s ^ 18
    + 18 * s ^ 17
    - 27 * s ^ 16
    + 37 * s ^ 15
    - 8 * s ^ 14
    - 76 * s ^ 13
    + 107 * s ^ 12
    + 102 * s ^ 11
    - 11 * s ^ 10
    + 248 * s ^ 8
    - 97 * s ^ 7
    + 27 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient3 (s : ℚ) : ℚ :=
  2 * s ^ 19
    - 26 * s ^ 18
    + 117 * s ^ 17
    - 306 * s ^ 16
    + 536 * s ^ 15
    - 819 * s ^ 14
    + 691 * s ^ 13
    + 185 * s ^ 12
    - 697 * s ^ 11
    - 1060 * s ^ 10
    + 2220 * s ^ 9
    - 2947 * s ^ 8
    + 945 * s ^ 7
    - 167 * s ^ 6
    - 47 * s ^ 5
    + 9 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient4 (s : ℚ) : ℚ :=
  s ^ 20
    - 9 * s ^ 19
    + 18 * s ^ 18
    + 96 * s ^ 17
    - 586 * s ^ 16
    + 1596 * s ^ 15
    - 3066 * s ^ 14
    + 5074 * s ^ 13
    - 3746 * s ^ 12
    - 6298 * s ^ 11
    + 20742 * s ^ 10
    - 24204 * s ^ 9
    + 17590 * s ^ 8
    - 3172 * s ^ 7
    - 666 * s ^ 6
    + 870 * s ^ 5
    - 163 * s ^ 4
    + 18 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient5 (s : ℚ) : ℚ :=
  2 * s ^ 20
    - 31 * s ^ 19
    + 190 * s ^ 18
    - 569 * s ^ 17
    + 696 * s ^ 16
    + 776 * s ^ 15
    - 6382 * s ^ 14
    + 22924 * s ^ 13
    - 62258 * s ^ 12
    + 114778 * s ^ 11
    - 137944 * s ^ 10
    + 101803 * s ^ 9
    - 37829 * s ^ 8
    - 14451 * s ^ 7
    + 15430 * s ^ 6
    - 7308 * s ^ 5
    + 1303 * s ^ 4
    - 138 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient6 (s : ℚ) : ℚ :=
  2 * s ^ 20
    - 47 * s ^ 19
    + 452 * s ^ 18
    - 2479 * s ^ 17
    + 9149 * s ^ 16
    - 26256 * s ^ 15
    + 65914 * s ^ 14
    - 144861 * s ^ 13
    + 252864 * s ^ 12
    - 310001 * s ^ 11
    + 229532 * s ^ 10
    - 38326 * s ^ 9
    - 126537 * s ^ 8
    + 169281 * s ^ 7
    - 91384 * s ^ 6
    + 32347 * s ^ 5
    - 5098 * s ^ 4
    + 432 * s ^ 3
    + 32 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient7 (s : ℚ) : ℚ :=
  s ^ 21
    - 19 * s ^ 20
    + 169 * s ^ 19
    - 935 * s ^ 18
    + 3782 * s ^ 17
    - 12852 * s ^ 16
    + 38967 * s ^ 15
    - 98510 * s ^ 14
    + 182485 * s ^ 13
    - 204172 * s ^ 12
    + 32054 * s ^ 11
    + 333572 * s ^ 10
    - 683054 * s ^ 9
    + 771249 * s ^ 8
    - 559999 * s ^ 7
    + 240542 * s ^ 6
    - 69572 * s ^ 5
    + 7009 * s ^ 4
    + 254 * s ^ 3
    - 287 * s ^ 2
    + 11 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 20
    + 9 * s ^ 19
    + 22 * s ^ 18
    - 721 * s ^ 17
    + 4613 * s ^ 16
    - 13597 * s ^ 15
    + 8248 * s ^ 14
    + 89391 * s ^ 13
    - 400432 * s ^ 12
    + 947399 * s ^ 11
    - 1510668 * s ^ 10
    + 1740065 * s ^ 9
    - 1452456 * s ^ 8
    + 830067 * s ^ 7
    - 281196 * s ^ 6
    + 52834 * s ^ 5
    + 9269 * s ^ 4
    - 4551 * s ^ 3
    + 1042 * s ^ 2
    - 31 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 20
    + 17 * s ^ 19
    - 100 * s ^ 18
    - 37 * s ^ 17
    + 4278 * s ^ 16
    - 31800 * s ^ 15
    + 136025 * s ^ 14
    - 400301 * s ^ 13
    + 864080 * s ^ 12
    - 1411085 * s ^ 11
    + 1765946 * s ^ 10
    - 1676174 * s ^ 9
    + 1136985 * s ^ 8
    - 465403 * s ^ 7
    + 45164 * s ^ 6
    + 51780 * s ^ 5
    - 43329 * s ^ 4
    + 10761 * s ^ 3
    - 1826 * s ^ 2
    - 2 * s
    + 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 20
    + 25 * s ^ 19
    - 295 * s ^ 18
    + 2173 * s ^ 17
    - 11141 * s ^ 16
    + 42030 * s ^ 15
    - 120533 * s ^ 14
    + 268173 * s ^ 13
    - 468224 * s ^ 12
    + 640782 * s ^ 11
    - 667266 * s ^ 10
    + 472919 * s ^ 9
    - 127317 * s ^ 8
    - 152642 * s ^ 7
    + 211868 * s ^ 6
    - 129069 * s ^ 5
    + 56720 * s ^ 4
    - 10758 * s ^ 3
    + 1416 * s ^ 2
    + 170 * s
    - 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient11 (s : ℚ) : ℚ :=
  s ^ 17
    - 16 * s ^ 16
    + 118 * s ^ 15
    - 575 * s ^ 14
    + 2378 * s ^ 13
    - 9439 * s ^ 12
    + 33286 * s ^ 11
    - 92424 * s ^ 10
    + 188862 * s ^ 9
    - 273544 * s ^ 8
    + 272365 * s ^ 7
    - 183411 * s ^ 6
    + 86496 * s ^ 5
    - 31001 * s ^ 4
    + 3058 * s ^ 3
    + 94 * s ^ 2
    - 378 * s
    + 35

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient12 (s : ℚ) : ℚ :=
  s ^ 16
    - 23 * s ^ 15
    + 242 * s ^ 14
    - 1547 * s ^ 13
    + 6702 * s ^ 12
    - 20692 * s ^ 11
    + 46414 * s ^ 10
    - 75459 * s ^ 9
    + 87162 * s ^ 8
    - 69443 * s ^ 7
    + 37678 * s ^ 6
    - 14455 * s ^ 5
    + 2610 * s ^ 4
    + 2791 * s ^ 3
    - 986 * s ^ 2
    + 405 * s
    - 35

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient13 (s : ℚ) : ℚ :=
  -s ^ 13
    + 19 * s ^ 12
    - 160 * s ^ 11
    + 783 * s ^ 10
    - 2446 * s ^ 9
    + 5038 * s ^ 8
    - 6869 * s ^ 7
    + 6308 * s ^ 6
    - 4525 * s ^ 5
    + 3468 * s ^ 4
    - 2385 * s ^ 3
    + 672 * s ^ 2
    - 238 * s
    + 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient14 (s : ℚ) : ℚ :=
  s ^ 9
    - 15 * s ^ 8
    + 95 * s ^ 7
    - 328 * s ^ 6
    + 666 * s ^ 5
    - 798 * s ^ 4
    + 520 * s ^ 3
    - 162 * s ^ 2
    + 73 * s
    - 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient15 (s : ℚ) : ℚ :=
  -s ^ 3
    + 6 * s ^ 2
    - 9 * s
    + 1

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
    differenceLeftCoefficient14 s * r ^ 14 +
    differenceLeftCoefficient15 s * r ^ 15

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_0 (s : ℚ) :
    differenceLeftCoefficient0 s =
    rawUnitNineNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient0,
    rawUnitNineNumeratorCoefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_1 (s : ℚ) :
    differenceLeftCoefficient1 s =
    rawUnitNineNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient1,
    rawUnitNineNumeratorCoefficient0,
    rawUnitNineNumeratorCoefficient1,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_2 (s : ℚ) :
    differenceLeftCoefficient2 s =
    rawUnitNineNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient2,
    rawUnitNineNumeratorCoefficient0,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient2,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_3 (s : ℚ) :
    differenceLeftCoefficient3 s =
    rawUnitNineNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient3,
    rawUnitNineNumeratorCoefficient0,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_4 (s : ℚ) :
    differenceLeftCoefficient4 s =
    rawUnitNineNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient4,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient4,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_5 (s : ℚ) :
    differenceLeftCoefficient5 s =
    rawUnitNineNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient5,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient5,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_6 (s : ℚ) :
    differenceLeftCoefficient6 s =
    rawUnitNineNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient6,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient6,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_7 (s : ℚ) :
    differenceLeftCoefficient7 s =
    rawUnitNineNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient7,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient7,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_8 (s : ℚ) :
    differenceLeftCoefficient8 s =
    rawUnitNineNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient8,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_9 (s : ℚ) :
    differenceLeftCoefficient9 s =
    rawUnitNineNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient9 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient9,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient9,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_10 (s : ℚ) :
    differenceLeftCoefficient10 s =
    rawUnitNineNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient9 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient10 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient10,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient10,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_11 (s : ℚ) :
    differenceLeftCoefficient11 s =
    rawUnitNineNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient9 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient10 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient11 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient11,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient11,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_12 (s : ℚ) :
    differenceLeftCoefficient12 s =
    rawUnitNineNumeratorCoefficient9 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient10 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient11 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitNineNumeratorCoefficient12 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient12,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient12,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_13 (s : ℚ) :
    differenceLeftCoefficient13 s =
    rawUnitNineNumeratorCoefficient10 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient11 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitNineNumeratorCoefficient12 s *
        rawUnitEightDenominatorCoefficient1 s
    := by
  simp only [differenceLeftCoefficient13,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient12,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_14 (s : ℚ) :
    differenceLeftCoefficient14 s =
    rawUnitNineNumeratorCoefficient11 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitNineNumeratorCoefficient12 s *
        rawUnitEightDenominatorCoefficient2 s
    := by
  simp only [differenceLeftCoefficient14,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient12,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_15 (s : ℚ) :
    differenceLeftCoefficient15 s =
    rawUnitNineNumeratorCoefficient12 s *
        rawUnitEightDenominatorCoefficient3 s
    := by
  simp only [differenceLeftCoefficient15,
    rawUnitNineNumeratorCoefficient12,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem differenceLeft_eq_rawUnitNineNumerator_mul_rawUnitEightDenominator (r s : ℚ) :
    differenceLeft r s = rawUnitNineNumerator r s * rawUnitEightDenominator r s := by
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
  have h15 := differenceLeftCoefficient_product_certificate_15 s
  simp only [differenceLeft, rawUnitNineNumerator, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 12
    + s ^ 11
    - s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient1 (s : ℚ) : ℚ :=
  s ^ 18
    - 4 * s ^ 17
    + 10 * s ^ 16
    - 20 * s ^ 15
    + 34 * s ^ 14
    - 54 * s ^ 13
    + 73 * s ^ 12
    - 60 * s ^ 11
    + 48 * s ^ 10
    - 26 * s ^ 9
    - 2 * s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient2 (s : ℚ) : ℚ :=
  2 * s ^ 19
    - 11 * s ^ 18
    + 23 * s ^ 17
    - 48 * s ^ 16
    + 107 * s ^ 15
    - 213 * s ^ 14
    + 340 * s ^ 13
    - 329 * s ^ 12
    + 126 * s ^ 11
    - 22 * s ^ 10
    - 178 * s ^ 9
    + 264 * s ^ 8
    - 83 * s ^ 7
    + 28 * s ^ 6
    - 7 * s ^ 5
    + s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient3 (s : ℚ) : ℚ :=
  s ^ 20
    - 6 * s ^ 19
    + s ^ 18
    + 20 * s ^ 17
    + 63 * s ^ 16
    - 279 * s ^ 15
    + 448 * s ^ 14
    - 97 * s ^ 13
    - 1220 * s ^ 12
    + 2563 * s ^ 11
    - 3055 * s ^ 10
    + 3691 * s ^ 9
    - 2646 * s ^ 8
    + 703 * s ^ 7
    - 234 * s ^ 6
    + 51 * s ^ 5
    - 2 * s ^ 4
    - 2 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient4 (s : ℚ) : ℚ :=
  s ^ 20
    - 15 * s ^ 19
    + 45 * s ^ 18
    + 71 * s ^ 17
    - 368 * s ^ 16
    - 158 * s ^ 15
    + 2865 * s ^ 14
    - 8677 * s ^ 13
    + 15884 * s ^ 12
    - 19986 * s ^ 11
    + 21390 * s ^ 10
    - 20302 * s ^ 9
    + 10146 * s ^ 8
    - 1361 * s ^ 7
    + 542 * s ^ 6
    - 35 * s ^ 5
    - 68 * s ^ 4
    + 25 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient5 (s : ℚ) : ℚ :=
  s ^ 20
    - 21 * s ^ 19
    + 132 * s ^ 18
    - 79 * s ^ 17
    - 2078 * s ^ 16
    + 9441 * s ^ 15
    - 22802 * s ^ 14
    + 40128 * s ^ 13
    - 54676 * s ^ 12
    + 62208 * s ^ 11
    - 65173 * s ^ 10
    + 48942 * s ^ 9
    - 10099 * s ^ 8
    - 6179 * s ^ 7
    + 666 * s ^ 6
    - 843 * s ^ 5
    + 577 * s ^ 4
    - 129 * s ^ 3
    - 16 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient6 (s : ℚ) : ℚ :=
  3 * s ^ 20
    - 64 * s ^ 19
    + 623 * s ^ 18
    - 3386 * s ^ 17
    + 11059 * s ^ 16
    - 23818 * s ^ 15
    + 39592 * s ^ 14
    - 58181 * s ^ 13
    + 77632 * s ^ 12
    - 96854 * s ^ 11
    + 93661 * s ^ 10
    - 28061 * s ^ 9
    - 45199 * s ^ 8
    + 34253 * s ^ 7
    - 3560 * s ^ 6
    + 4158 * s ^ 5
    - 2283 * s ^ 4
    + 307 * s ^ 3
    + 118 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient7 (s : ℚ) : ℚ :=
  s ^ 21
    - 19 * s ^ 20
    + 162 * s ^ 19
    - 774 * s ^ 18
    + 2095 * s ^ 17
    - 2975 * s ^ 16
    + 2911 * s ^ 15
    - 9621 * s ^ 14
    + 33494 * s ^ 13
    - 69369 * s ^ 12
    + 85078 * s ^ 11
    - 14139 * s ^ 10
    - 128835 * s ^ 9
    + 163577 * s ^ 8
    - 52477 * s ^ 7
    - 2611 * s ^ 6
    - 11514 * s ^ 5
    + 5530 * s ^ 4
    + 17 * s ^ 3
    - 531 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient8 (s : ℚ) : ℚ :=
  -3 * s ^ 20
    + 51 * s ^ 19
    - 378 * s ^ 18
    + 1432 * s ^ 17
    - 2003 * s ^ 16
    - 5091 * s ^ 15
    + 28861 * s ^ 14
    - 59767 * s ^ 13
    + 59049 * s ^ 12
    + 30931 * s ^ 11
    - 219249 * s ^ 10
    + 329853 * s ^ 9
    - 181327 * s ^ 8
    - 21265 * s ^ 7
    + 21303 * s ^ 6
    + 26837 * s ^ 5
    - 8207 * s ^ 4
    - 2655 * s ^ 3
    + 1628 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 20
    + 25 * s ^ 19
    - 273 * s ^ 18
    + 1718 * s ^ 17
    - 6697 * s ^ 16
    + 15845 * s ^ 15
    - 18437 * s ^ 14
    - 12143 * s ^ 13
    + 105011 * s ^ 12
    - 258043 * s ^ 11
    + 360394 * s ^ 10
    - 225013 * s ^ 9
    - 68687 * s ^ 8
    + 151663 * s ^ 7
    - 2735 * s ^ 6
    - 52069 * s ^ 5
    + 2945 * s ^ 4
    + 10070 * s ^ 3
    - 3572 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient10 (s : ℚ) : ℚ :=
  2 * s ^ 19
    - 45 * s ^ 18
    + 468 * s ^ 17
    - 2931 * s ^ 16
    + 12168 * s ^ 15
    - 35543 * s ^ 14
    + 77332 * s ^ 13
    - 128474 * s ^ 12
    + 142341 * s ^ 11
    - 28622 * s ^ 10
    - 201506 * s ^ 9
    + 296823 * s ^ 8
    - 104866 * s ^ 7
    - 91954 * s ^ 6
    + 60655 * s ^ 5
    + 20342 * s ^ 4
    - 21869 * s ^ 3
    + 5670 * s ^ 2
    + 9 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 18
    + 22 * s ^ 17
    - 221 * s ^ 16
    + 1306 * s ^ 15
    - 5127 * s ^ 14
    + 15500 * s ^ 13
    - 42888 * s ^ 12
    + 108529 * s ^ 11
    - 206394 * s ^ 10
    + 233281 * s ^ 9
    - 80658 * s ^ 8
    - 125828 * s ^ 7
    + 141881 * s ^ 6
    - 7694 * s ^ 5
    - 56221 * s ^ 4
    + 30914 * s ^ 3
    - 6367 * s ^ 2
    - 34 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient12 (s : ℚ) : ℚ :=
  s ^ 16
    - 34 * s ^ 15
    + 443 * s ^ 14
    - 2982 * s ^ 13
    + 11274 * s ^ 12
    - 22389 * s ^ 11
    + 9295 * s ^ 10
    + 61588 * s ^ 9
    - 151865 * s ^ 8
    + 147769 * s ^ 7
    - 27530 * s ^ 6
    - 74328 * s ^ 5
    + 71871 * s ^ 4
    - 27935 * s ^ 3
    + 4753 * s ^ 2
    + 69 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient13 (s : ℚ) : ℚ :=
  -2 * s ^ 15
    + 51 * s ^ 14
    - 560 * s ^ 13
    + 3487 * s ^ 12
    - 13553 * s ^ 11
    + 33709 * s ^ 10
    - 51254 * s ^ 9
    + 36037 * s ^ 8
    + 21724 * s ^ 7
    - 78241 * s ^ 6
    + 83081 * s ^ 5
    - 46861 * s ^ 4
    + 14519 * s ^ 3
    - 2058 * s ^ 2
    - 79 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient14 (s : ℚ) : ℚ :=
  s ^ 14
    - 23 * s ^ 13
    + 237 * s ^ 12
    - 1444 * s ^ 11
    + 5782 * s ^ 10
    - 15993 * s ^ 9
    + 31256 * s ^ 8
    - 43373 * s ^ 7
    + 42309 * s ^ 6
    - 28274 * s ^ 5
    + 12367 * s ^ 4
    - 3239 * s ^ 3
    + 346 * s ^ 2
    + 48 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient15 (s : ℚ) : ℚ :=
  -s ^ 5
    + 8 * s ^ 4
    - 23 * s ^ 3
    + 28 * s ^ 2
    - 12 * s

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

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_0 (s : ℚ) :
    differenceRightCoefficient0 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient0,
    rawUnitEightNumeratorCoefficient0,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_1 (s : ℚ) :
    differenceRightCoefficient1 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient1,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_2 (s : ℚ) :
    differenceRightCoefficient2 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient2,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_3 (s : ℚ) :
    differenceRightCoefficient3 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient3,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_4 (s : ℚ) :
    differenceRightCoefficient4 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient4 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient1 s
    := by
  simp only [differenceRightCoefficient4,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_5 (s : ℚ) :
    differenceRightCoefficient5 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient5 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient4 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient2 s
    := by
  simp only [differenceRightCoefficient5,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_6 (s : ℚ) :
    differenceRightCoefficient6 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient6 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient5 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient4 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient3 s
    := by
  simp only [differenceRightCoefficient6,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_7 (s : ℚ) :
    differenceRightCoefficient7 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient7 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient6 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient5 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient4 s
    := by
  simp only [differenceRightCoefficient7,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_8 (s : ℚ) :
    differenceRightCoefficient8 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient8 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient7 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient6 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient5 s
    := by
  simp only [differenceRightCoefficient8,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_9 (s : ℚ) :
    differenceRightCoefficient9 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient9 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient8 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient7 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient6 s
    := by
  simp only [differenceRightCoefficient9,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_10 (s : ℚ) :
    differenceRightCoefficient10 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient10 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient9 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient8 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient7 s
    := by
  simp only [differenceRightCoefficient10,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_11 (s : ℚ) :
    differenceRightCoefficient11 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient11 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient10 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient9 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient8 s
    := by
  simp only [differenceRightCoefficient11,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_12 (s : ℚ) :
    differenceRightCoefficient12 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitNineDenominatorCoefficient12 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient11 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient10 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient9 s
    := by
  simp only [differenceRightCoefficient12,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_13 (s : ℚ) :
    differenceRightCoefficient13 s =
    rawUnitEightNumeratorCoefficient1 s *
        rawUnitNineDenominatorCoefficient12 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient11 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient10 s
    := by
  simp only [differenceRightCoefficient13,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_14 (s : ℚ) :
    differenceRightCoefficient14 s =
    rawUnitEightNumeratorCoefficient2 s *
        rawUnitNineDenominatorCoefficient12 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient11 s
    := by
  simp only [differenceRightCoefficient14,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_15 (s : ℚ) :
    differenceRightCoefficient15 s =
    rawUnitEightNumeratorCoefficient3 s *
        rawUnitNineDenominatorCoefficient12 s
    := by
  simp only [differenceRightCoefficient15,
    rawUnitEightNumeratorCoefficient3,
    rawUnitNineDenominatorCoefficient12]
  ring

/-- Checked staged polynomial-product identity. -/
theorem differenceRight_eq_rawUnitEightNumerator_mul_rawUnitNineDenominator (r s : ℚ) :
    differenceRight r s = rawUnitEightNumerator r s * rawUnitNineDenominator r s := by
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
  simp only [differenceRight, rawUnitEightNumerator, rawUnitNineDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient0 (s : ℚ) : ℚ :=
  s ^ 13
    + s ^ 12
    + s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 18
    + 3 * s ^ 17
    - 7 * s ^ 16
    + 12 * s ^ 15
    - 18 * s ^ 14
    + 33 * s ^ 13
    - 69 * s ^ 12
    + 39 * s ^ 11
    - 40 * s ^ 10
    + 6 * s ^ 9
    - 5 * s ^ 8
    + 3 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 19
    + 5 * s ^ 18
    - 5 * s ^ 17
    + 21 * s ^ 16
    - 70 * s ^ 15
    + 205 * s ^ 14
    - 416 * s ^ 13
    + 436 * s ^ 12
    - 24 * s ^ 11
    + 11 * s ^ 10
    + 178 * s ^ 9
    - 16 * s ^ 8
    - 14 * s ^ 7
    - s ^ 6
    + 7 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 20
    + 8 * s ^ 19
    - 27 * s ^ 18
    + 97 * s ^ 17
    - 369 * s ^ 16
    + 815 * s ^ 15
    - 1267 * s ^ 14
    + 788 * s ^ 13
    + 1405 * s ^ 12
    - 3260 * s ^ 11
    + 1995 * s ^ 10
    - 1471 * s ^ 9
    - 301 * s ^ 8
    + 242 * s ^ 7
    + 67 * s ^ 6
    - 98 * s ^ 5
    + 11 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient4 (s : ℚ) : ℚ :=
  6 * s ^ 19
    - 27 * s ^ 18
    + 25 * s ^ 17
    - 218 * s ^ 16
    + 1754 * s ^ 15
    - 5931 * s ^ 14
    + 13751 * s ^ 13
    - 19630 * s ^ 12
    + 13688 * s ^ 11
    - 648 * s ^ 10
    - 3902 * s ^ 9
    + 7444 * s ^ 8
    - 1811 * s ^ 7
    - 1208 * s ^ 6
    + 905 * s ^ 5
    - 95 * s ^ 4
    - 7 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient5 (s : ℚ) : ℚ :=
  s ^ 20
    - 10 * s ^ 19
    + 58 * s ^ 18
    - 490 * s ^ 17
    + 2774 * s ^ 16
    - 8665 * s ^ 15
    + 16420 * s ^ 14
    - 17204 * s ^ 13
    - 7582 * s ^ 12
    + 52570 * s ^ 11
    - 72771 * s ^ 10
    + 52861 * s ^ 9
    - 27730 * s ^ 8
    - 8272 * s ^ 7
    + 14764 * s ^ 6
    - 6465 * s ^ 5
    + 726 * s ^ 4
    - 9 * s ^ 3
    + 15 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 20
    + 17 * s ^ 19
    - 171 * s ^ 18
    + 907 * s ^ 17
    - 1910 * s ^ 16
    - 2438 * s ^ 15
    + 26322 * s ^ 14
    - 86680 * s ^ 13
    + 175232 * s ^ 12
    - 213147 * s ^ 11
    + 135871 * s ^ 10
    - 10265 * s ^ 9
    - 81338 * s ^ 8
    + 135028 * s ^ 7
    - 87824 * s ^ 6
    + 28189 * s ^ 5
    - 2815 * s ^ 4
    + 125 * s ^ 3
    - 86 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient7 (s : ℚ) : ℚ :=
  7 * s ^ 19
    - 161 * s ^ 18
    + 1687 * s ^ 17
    - 9877 * s ^ 16
    + 36056 * s ^ 15
    - 88889 * s ^ 14
    + 148991 * s ^ 13
    - 134803 * s ^ 12
    - 53024 * s ^ 11
    + 347711 * s ^ 10
    - 554219 * s ^ 9
    + 607672 * s ^ 8
    - 507522 * s ^ 7
    + 243153 * s ^ 6
    - 58058 * s ^ 5
    + 1479 * s ^ 4
    + 237 * s ^ 3
    + 244 * s ^ 2
    + 11 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient8 (s : ℚ) : ℚ :=
  2 * s ^ 20
    - 42 * s ^ 19
    + 400 * s ^ 18
    - 2153 * s ^ 17
    + 6616 * s ^ 16
    - 8506 * s ^ 15
    - 20613 * s ^ 14
    + 149158 * s ^ 13
    - 459481 * s ^ 12
    + 916468 * s ^ 11
    - 1291419 * s ^ 10
    + 1410212 * s ^ 9
    - 1271129 * s ^ 8
    + 851332 * s ^ 7
    - 302499 * s ^ 6
    + 25997 * s ^ 5
    + 17476 * s ^ 4
    - 1896 * s ^ 3
    - 586 * s ^ 2
    - 31 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient9 (s : ℚ) : ℚ :=
  -8 * s ^ 19
    + 173 * s ^ 18
    - 1755 * s ^ 17
    + 10975 * s ^ 16
    - 47645 * s ^ 15
    + 154462 * s ^ 14
    - 388158 * s ^ 13
    + 759069 * s ^ 12
    - 1153042 * s ^ 11
    + 1405552 * s ^ 10
    - 1451161 * s ^ 9
    + 1205672 * s ^ 8
    - 617066 * s ^ 7
    + 47899 * s ^ 6
    + 103849 * s ^ 5
    - 46274 * s ^ 4
    + 691 * s ^ 3
    + 1746 * s ^ 2
    - s
    + 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 20
    + 23 * s ^ 19
    - 250 * s ^ 18
    + 1705 * s ^ 17
    - 8210 * s ^ 16
    + 29862 * s ^ 15
    - 84990 * s ^ 14
    + 190841 * s ^ 13
    - 339750 * s ^ 12
    + 498441 * s ^ 11
    - 638644 * s ^ 10
    + 674425 * s ^ 9
    - 424140 * s ^ 8
    - 47776 * s ^ 7
    + 303822 * s ^ 6
    - 189724 * s ^ 5
    + 36378 * s ^ 4
    + 11111 * s ^ 3
    - 4254 * s ^ 2
    + 161 * s
    - 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient11 (s : ℚ) : ℚ :=
  s ^ 18
    - 21 * s ^ 17
    + 205 * s ^ 16
    - 1188 * s ^ 15
    + 4552 * s ^ 14
    - 13122 * s ^ 13
    + 33449 * s ^ 12
    - 75243 * s ^ 11
    + 113970 * s ^ 10
    - 44419 * s ^ 9
    - 192886 * s ^ 8
    + 398193 * s ^ 7
    - 325292 * s ^ 6
    + 94190 * s ^ 5
    + 25220 * s ^ 4
    - 27856 * s ^ 3
    + 6461 * s ^ 2
    - 344 * s
    + 35

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient12 (s : ℚ) : ℚ :=
  11 * s ^ 15
    - 201 * s ^ 14
    + 1435 * s ^ 13
    - 4572 * s ^ 12
    + 1697 * s ^ 11
    + 37119 * s ^ 10
    - 137047 * s ^ 9
    + 239027 * s ^ 8
    - 217212 * s ^ 7
    + 65208 * s ^ 6
    + 59873 * s ^ 5
    - 69261 * s ^ 4
    + 30726 * s ^ 3
    - 5739 * s ^ 2
    + 336 * s
    - 35

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient13 (s : ℚ) : ℚ :=
  2 * s ^ 15
    - 51 * s ^ 14
    + 559 * s ^ 13
    - 3468 * s ^ 12
    + 13393 * s ^ 11
    - 32926 * s ^ 10
    + 48808 * s ^ 9
    - 30999 * s ^ 8
    - 28593 * s ^ 7
    + 84549 * s ^ 6
    - 87606 * s ^ 5
    + 50329 * s ^ 4
    - 16904 * s ^ 3
    + 2730 * s ^ 2
    - 159 * s
    + 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient14 (s : ℚ) : ℚ :=
  -s ^ 14
    + 23 * s ^ 13
    - 237 * s ^ 12
    + 1444 * s ^ 11
    - 5782 * s ^ 10
    + 15994 * s ^ 9
    - 31271 * s ^ 8
    + 43468 * s ^ 7
    - 42637 * s ^ 6
    + 28940 * s ^ 5
    - 13165 * s ^ 4
    + 3759 * s ^ 3
    - 508 * s ^ 2
    + 25 * s
    - 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient15 (s : ℚ) : ℚ :=
  s ^ 5
    - 8 * s ^ 4
    + 22 * s ^ 3
    - 22 * s ^ 2
    + 3 * s
    + 1

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

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_0 (s : ℚ) :
    differenceCoefficient0 s =
      differenceLeftCoefficient0 s
        - differenceRightCoefficient0 s
      := by
  simp only [differenceCoefficient0,
    differenceLeftCoefficient0,
    differenceRightCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_1 (s : ℚ) :
    differenceCoefficient1 s =
      differenceLeftCoefficient1 s
        - differenceRightCoefficient1 s
      := by
  simp only [differenceCoefficient1,
    differenceLeftCoefficient1,
    differenceRightCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_2 (s : ℚ) :
    differenceCoefficient2 s =
      differenceLeftCoefficient2 s
        - differenceRightCoefficient2 s
      := by
  simp only [differenceCoefficient2,
    differenceLeftCoefficient2,
    differenceRightCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_3 (s : ℚ) :
    differenceCoefficient3 s =
      differenceLeftCoefficient3 s
        - differenceRightCoefficient3 s
      := by
  simp only [differenceCoefficient3,
    differenceLeftCoefficient3,
    differenceRightCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_4 (s : ℚ) :
    differenceCoefficient4 s =
      differenceLeftCoefficient4 s
        - differenceRightCoefficient4 s
      := by
  simp only [differenceCoefficient4,
    differenceLeftCoefficient4,
    differenceRightCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_5 (s : ℚ) :
    differenceCoefficient5 s =
      differenceLeftCoefficient5 s
        - differenceRightCoefficient5 s
      := by
  simp only [differenceCoefficient5,
    differenceLeftCoefficient5,
    differenceRightCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_6 (s : ℚ) :
    differenceCoefficient6 s =
      differenceLeftCoefficient6 s
        - differenceRightCoefficient6 s
      := by
  simp only [differenceCoefficient6,
    differenceLeftCoefficient6,
    differenceRightCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_7 (s : ℚ) :
    differenceCoefficient7 s =
      differenceLeftCoefficient7 s
        - differenceRightCoefficient7 s
      := by
  simp only [differenceCoefficient7,
    differenceLeftCoefficient7,
    differenceRightCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_8 (s : ℚ) :
    differenceCoefficient8 s =
      differenceLeftCoefficient8 s
        - differenceRightCoefficient8 s
      := by
  simp only [differenceCoefficient8,
    differenceLeftCoefficient8,
    differenceRightCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_9 (s : ℚ) :
    differenceCoefficient9 s =
      differenceLeftCoefficient9 s
        - differenceRightCoefficient9 s
      := by
  simp only [differenceCoefficient9,
    differenceLeftCoefficient9,
    differenceRightCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_10 (s : ℚ) :
    differenceCoefficient10 s =
      differenceLeftCoefficient10 s
        - differenceRightCoefficient10 s
      := by
  simp only [differenceCoefficient10,
    differenceLeftCoefficient10,
    differenceRightCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_11 (s : ℚ) :
    differenceCoefficient11 s =
      differenceLeftCoefficient11 s
        - differenceRightCoefficient11 s
      := by
  simp only [differenceCoefficient11,
    differenceLeftCoefficient11,
    differenceRightCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_12 (s : ℚ) :
    differenceCoefficient12 s =
      differenceLeftCoefficient12 s
        - differenceRightCoefficient12 s
      := by
  simp only [differenceCoefficient12,
    differenceLeftCoefficient12,
    differenceRightCoefficient12]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_13 (s : ℚ) :
    differenceCoefficient13 s =
      differenceLeftCoefficient13 s
        - differenceRightCoefficient13 s
      := by
  simp only [differenceCoefficient13,
    differenceLeftCoefficient13,
    differenceRightCoefficient13]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_14 (s : ℚ) :
    differenceCoefficient14 s =
      differenceLeftCoefficient14 s
        - differenceRightCoefficient14 s
      := by
  simp only [differenceCoefficient14,
    differenceLeftCoefficient14,
    differenceRightCoefficient14]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem differenceCoefficient_subtraction_certificate_15 (s : ℚ) :
    differenceCoefficient15 s =
      differenceLeftCoefficient15 s
        - differenceRightCoefficient15 s
      := by
  simp only [differenceCoefficient15,
    differenceLeftCoefficient15,
    differenceRightCoefficient15]
  ring

/-- Checked staged polynomial-combination identity. -/
theorem difference_eq_linearCombination (r s : ℚ) :
    difference r s = differenceLeft r s - differenceRight r s := by
  have h0 := differenceCoefficient_subtraction_certificate_0 s
  have h1 := differenceCoefficient_subtraction_certificate_1 s
  have h2 := differenceCoefficient_subtraction_certificate_2 s
  have h3 := differenceCoefficient_subtraction_certificate_3 s
  have h4 := differenceCoefficient_subtraction_certificate_4 s
  have h5 := differenceCoefficient_subtraction_certificate_5 s
  have h6 := differenceCoefficient_subtraction_certificate_6 s
  have h7 := differenceCoefficient_subtraction_certificate_7 s
  have h8 := differenceCoefficient_subtraction_certificate_8 s
  have h9 := differenceCoefficient_subtraction_certificate_9 s
  have h10 := differenceCoefficient_subtraction_certificate_10 s
  have h11 := differenceCoefficient_subtraction_certificate_11 s
  have h12 := differenceCoefficient_subtraction_certificate_12 s
  have h13 := differenceCoefficient_subtraction_certificate_13 s
  have h14 := differenceCoefficient_subtraction_certificate_14 s
  have h15 := differenceCoefficient_subtraction_certificate_15 s
  simp only [difference, differenceLeft, differenceRight]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 13
    + 4 * s ^ 12
    - 8 * s ^ 11
    + 12 * s ^ 10
    - 15 * s ^ 9
    + 16 * s ^ 8
    - 15 * s ^ 7
    + 12 * s ^ 6
    - 8 * s ^ 5
    + 4 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 14
    + 5 * s ^ 13
    - 4 * s ^ 12
    - 5 * s ^ 11
    + 30 * s ^ 9
    - 76 * s ^ 8
    + 117 * s ^ 7
    - 126 * s ^ 6
    + 99 * s ^ 5
    - 50 * s ^ 4
    + 10 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient3 (s : ℚ) : ℚ :=
  -s ^ 14
    + 13 * s ^ 13
    - 38 * s ^ 12
    - 14 * s ^ 11
    + 233 * s ^ 10
    - 550 * s ^ 9
    + 863 * s ^ 8
    - 1054 * s ^ 7
    + 998 * s ^ 6
    - 699 * s ^ 5
    + 295 * s ^ 4
    - 32 * s ^ 3
    - 14 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient4 (s : ℚ) : ℚ :=
  -2 * s ^ 14
    + 33 * s ^ 13
    - 221 * s ^ 12
    + 744 * s ^ 11
    - 1494 * s ^ 10
    + 2263 * s ^ 9
    - 3065 * s ^ 8
    + 3572 * s ^ 7
    - 3239 * s ^ 6
    + 2013 * s ^ 5
    - 562 * s ^ 4
    - 144 * s ^ 3
    + 103 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 15
    + 14 * s ^ 14
    - 86 * s ^ 13
    + 287 * s ^ 12
    - 569 * s ^ 11
    + 936 * s ^ 10
    - 2020 * s ^ 9
    + 4046 * s ^ 8
    - 5475 * s ^ 7
    + 4699 * s ^ 6
    - 1932 * s ^ 5
    - 670 * s ^ 4
    + 1129 * s ^ 3
    - 353 * s ^ 2
    - 6 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient6 (s : ℚ) : ℚ :=
  2 * s ^ 14
    - 23 * s ^ 13
    + 100 * s ^ 12
    - 107 * s ^ 11
    - 660 * s ^ 10
    + 2895 * s ^ 9
    - 5314 * s ^ 8
    + 5276 * s ^ 7
    - 1993 * s ^ 6
    - 2487 * s ^ 5
    + 4489 * s ^ 4
    - 2777 * s ^ 3
    + 535 * s ^ 2
    + 71 * s
    - 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient7 (s : ℚ) : ℚ :=
  s ^ 14
    - 18 * s ^ 13
    + 141 * s ^ 12
    - 624 * s ^ 11
    + 1654 * s ^ 10
    - 2521 * s ^ 9
    + 1591 * s ^ 8
    + 1778 * s ^ 7
    - 6212 * s ^ 6
    + 8952 * s ^ 5
    - 7384 * s ^ 4
    + 2938 * s ^ 3
    - 83 * s ^ 2
    - 233 * s
    + 20

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient8 (s : ℚ) : ℚ :=
  -s ^ 13
    + 17 * s ^ 12
    - 132 * s ^ 11
    + 607 * s ^ 10
    - 1819 * s ^ 9
    + 3812 * s ^ 8
    - 6060 * s ^ 7
    + 7683 * s ^ 6
    - 7237 * s ^ 5
    + 4000 * s ^ 4
    - 380 * s ^ 3
    - 826 * s ^ 2
    + 365 * s
    - 29

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient9 (s : ℚ) : ℚ :=
  -s ^ 10
    + 20 * s ^ 9
    - 142 * s ^ 8
    + 479 * s ^ 7
    - 775 * s ^ 6
    + 311 * s ^ 5
    + 881 * s ^ 4
    - 1507 * s ^ 3
    + 992 * s ^ 2
    - 279 * s
    + 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient10 (s : ℚ) : ℚ :=
  s ^ 9
    - 15 * s ^ 8
    + 95 * s ^ 7
    - 332 * s ^ 6
    + 702 * s ^ 5
    - 925 * s ^ 4
    + 751 * s ^ 3
    - 354 * s ^ 2
    + 83 * s
    - 6

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

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_0 (s : ℚ) :
    t3Step1Coefficient0 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient0,
    rawUnitEightNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_1 (s : ℚ) :
    t3Step1Coefficient1 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient1,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_2 (s : ℚ) :
    t3Step1Coefficient2 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient2,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_3 (s : ℚ) :
    t3Step1Coefficient3 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient3,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_4 (s : ℚ) :
    t3Step1Coefficient4 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient1 s
    := by
  simp only [t3Step1Coefficient4,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_5 (s : ℚ) :
    t3Step1Coefficient5 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient2 s
    := by
  simp only [t3Step1Coefficient5,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_6 (s : ℚ) :
    t3Step1Coefficient6 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient3 s
    := by
  simp only [t3Step1Coefficient6,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_7 (s : ℚ) :
    t3Step1Coefficient7 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient4 s
    := by
  simp only [t3Step1Coefficient7,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_8 (s : ℚ) :
    t3Step1Coefficient8 s =
    rawUnitEightNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient5 s
    := by
  simp only [t3Step1Coefficient8,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_9 (s : ℚ) :
    t3Step1Coefficient9 s =
    rawUnitEightNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient6 s
    := by
  simp only [t3Step1Coefficient9,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_10 (s : ℚ) :
    t3Step1Coefficient10 s =
    rawUnitEightNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient7 s
    := by
  simp only [t3Step1Coefficient10,
    rawUnitEightNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t3Step1_eq_rawUnitEightNumerator_mul_rawUnitTwoNumerator (r s : ℚ) :
    t3Step1 r s = rawUnitEightNumerator r s * rawUnitTwoNumerator r s := by
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
  simp only [t3Step1, rawUnitEightNumerator, rawUnitTwoNumerator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 26
    + 3 * s ^ 25
    - 4 * s ^ 24
    + 3 * s ^ 23
    + s ^ 22
    - 7 * s ^ 21
    + 13 * s ^ 20
    - 18 * s ^ 19
    + 20 * s ^ 18
    - 19 * s ^ 17
    + 15 * s ^ 16
    - 9 * s ^ 15
    + 4 * s ^ 14
    - s ^ 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient2 (s : ℚ) : ℚ :=
  s ^ 31
    - 7 * s ^ 30
    + 27 * s ^ 29
    - 76 * s ^ 28
    + 172 * s ^ 27
    - 342 * s ^ 26
    + 658 * s ^ 25
    - 1154 * s ^ 24
    + 1755 * s ^ 23
    - 2355 * s ^ 22
    + 2812 * s ^ 21
    - 3037 * s ^ 20
    + 3000 * s ^ 19
    - 2682 * s ^ 18
    + 2151 * s ^ 17
    - 1494 * s ^ 16
    + 865 * s ^ 15
    - 417 * s ^ 14
    + 165 * s ^ 13
    - 61 * s ^ 12
    + 25 * s ^ 11
    - 7 * s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient3 (s : ℚ) : ℚ :=
  2 * s ^ 32
    - 17 * s ^ 31
    + 59 * s ^ 30
    - 147 * s ^ 29
    + 360 * s ^ 28
    - 971 * s ^ 27
    + 2642 * s ^ 26
    - 6068 * s ^ 25
    + 10747 * s ^ 24
    - 15734 * s ^ 23
    + 20809 * s ^ 22
    - 25554 * s ^ 21
    + 29501 * s ^ 20
    - 31255 * s ^ 19
    + 29133 * s ^ 18
    - 23155 * s ^ 17
    + 14792 * s ^ 16
    - 7272 * s ^ 15
    + 2782 * s ^ 14
    - 880 * s ^ 13
    + 416 * s ^ 12
    - 226 * s ^ 11
    + 17 * s ^ 10
    + 30 * s ^ 9
    - 12 * s ^ 8
    + s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient4 (s : ℚ) : ℚ :=
  2 * s ^ 33
    - 21 * s ^ 32
    + 85 * s ^ 31
    - 258 * s ^ 30
    + 1051 * s ^ 29
    - 4006 * s ^ 28
    + 11655 * s ^ 27
    - 25555 * s ^ 26
    + 41986 * s ^ 25
    - 55176 * s ^ 24
    + 72326 * s ^ 23
    - 106097 * s ^ 22
    + 154548 * s ^ 21
    - 201192 * s ^ 20
    + 216982 * s ^ 19
    - 184778 * s ^ 18
    + 116417 * s ^ 17
    - 42631 * s ^ 16
    - 1383 * s ^ 15
    + 10613 * s ^ 14
    - 4704 * s ^ 13
    - 1107 * s ^ 12
    + 687 * s ^ 11
    + 1319 * s ^ 10
    - 1018 * s ^ 9
    + 267 * s ^ 8
    - 10 * s ^ 7
    - 2 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient5 (s : ℚ) : ℚ :=
  s ^ 34
    - 12 * s ^ 33
    + 49 * s ^ 32
    - 139 * s ^ 31
    + 813 * s ^ 30
    - 3769 * s ^ 29
    + 8985 * s ^ 28
    - 9164 * s ^ 27
    - 10737 * s ^ 26
    + 48848 * s ^ 25
    - 29063 * s ^ 24
    - 173461 * s ^ 23
    + 551555 * s ^ 22
    - 921307 * s ^ 21
    + 1056946 * s ^ 20
    - 810696 * s ^ 19
    + 274465 * s ^ 18
    + 268858 * s ^ 17
    - 542900 * s ^ 16
    + 453581 * s ^ 15
    - 202855 * s ^ 14
    + 24866 * s ^ 13
    + 20937 * s ^ 12
    + 11077 * s ^ 11
    - 29418 * s ^ 10
    + 15744 * s ^ 9
    - 3216 * s ^ 8
    - 28 * s ^ 7
    + 38 * s ^ 6
    + 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient6 (s : ℚ) : ℚ :=
  s ^ 34
    - 25 * s ^ 33
    + 180 * s ^ 32
    - 497 * s ^ 31
    + 835 * s ^ 30
    - 5278 * s ^ 29
    + 26360 * s ^ 28
    - 53572 * s ^ 27
    - 31795 * s ^ 26
    + 543166 * s ^ 25
    - 1821377 * s ^ 24
    + 3582778 * s ^ 23
    - 4617963 * s ^ 22
    + 3775961 * s ^ 21
    - 872343 * s ^ 20
    - 3157097 * s ^ 19
    + 6401902 * s ^ 18
    - 7210359 * s ^ 17
    + 5310608 * s ^ 16
    - 2115314 * s ^ 15
    - 172816 * s ^ 14
    + 709362 * s ^ 13
    - 195678 * s ^ 12
    - 356462 * s ^ 11
    + 397173 * s ^ 10
    - 165060 * s ^ 9
    + 26185 * s ^ 8
    + 1514 * s ^ 7
    - 343 * s ^ 6
    - 45 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 34
    - 58 * s ^ 33
    + 670 * s ^ 32
    - 3918 * s ^ 31
    + 14307 * s ^ 30
    - 49564 * s ^ 29
    + 212386 * s ^ 28
    - 822297 * s ^ 27
    + 2361372 * s ^ 26
    - 4829538 * s ^ 25
    + 6376581 * s ^ 24
    - 2914770 * s ^ 23
    - 8514190 * s ^ 22
    + 25631133 * s ^ 21
    - 42045424 * s ^ 20
    + 50245428 * s ^ 19
    - 44537886 * s ^ 18
    + 25920163 * s ^ 17
    - 2930602 * s ^ 16
    - 12512994 * s ^ 15
    + 13789511 * s ^ 14
    - 5668918 * s ^ 13
    - 2606767 * s ^ 12
    + 5624419 * s ^ 11
    - 3829622 * s ^ 10
    + 1249586 * s ^ 9
    - 141302 * s ^ 8
    - 20282 * s ^ 7
    + 2088 * s ^ 6
    + 458 * s ^ 5
    + 28 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient8 (s : ℚ) : ℚ :=
  s ^ 35
    - 22 * s ^ 34
    + 212 * s ^ 33
    - 1139 * s ^ 32
    + 4417 * s ^ 31
    - 21624 * s ^ 30
    + 119766 * s ^ 29
    - 444697 * s ^ 28
    + 809230 * s ^ 27
    + 630584 * s ^ 26
    - 8978926 * s ^ 25
    + 31604075 * s ^ 24
    - 70481953 * s ^ 23
    + 112818622 * s ^ 22
    - 135770399 * s ^ 21
    + 121771270 * s ^ 20
    - 64329260 * s ^ 19
    - 26448873 * s ^ 18
    + 116510573 * s ^ 17
    - 161141337 * s ^ 16
    + 133818035 * s ^ 15
    - 53889918 * s ^ 14
    - 24064620 * s ^ 13
    + 59971069 * s ^ 12
    - 52068154 * s ^ 11
    + 25499679 * s ^ 10
    - 6377218 * s ^ 9
    + 276562 * s ^ 8
    + 200237 * s ^ 7
    - 13434 * s ^ 6
    - 2358 * s ^ 5
    - 401 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient9 (s : ℚ) : ℚ :=
  -9 * s ^ 34
    + 163 * s ^ 33
    - 1225 * s ^ 32
    + 5081 * s ^ 31
    - 23272 * s ^ 30
    + 203401 * s ^ 29
    - 1465701 * s ^ 28
    + 6898300 * s ^ 27
    - 22369328 * s ^ 26
    + 52414804 * s ^ 25
    - 88531413 * s ^ 24
    + 97845282 * s ^ 23
    - 35900905 * s ^ 22
    - 116550725 * s ^ 21
    + 341286045 * s ^ 20
    - 594894457 * s ^ 19
    + 791591589 * s ^ 18
    - 807556717 * s ^ 17
    + 564149639 * s ^ 16
    - 121830110 * s ^ 15
    - 311611031 * s ^ 14
    + 527956849 * s ^ 13
    - 483594444 * s ^ 12
    + 291728925 * s ^ 11
    - 108284813 * s ^ 10
    + 17049056 * s ^ 9
    + 2891412 * s ^ 8
    - 1505706 * s ^ 7
    + 91180 * s ^ 6
    + 4683 * s ^ 5
    + 3445 * s ^ 4
    + 3 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient10 (s : ℚ) : ℚ :=
  -s ^ 35
    + 23 * s ^ 34
    - 268 * s ^ 33
    + 2712 * s ^ 32
    - 26375 * s ^ 31
    + 203466 * s ^ 30
    - 1108374 * s ^ 29
    + 4112843 * s ^ 28
    - 9887388 * s ^ 27
    + 11581721 * s ^ 26
    + 17118411 * s ^ 25
    - 127139163 * s ^ 24
    + 369178841 * s ^ 23
    - 739964283 * s ^ 22
    + 1165720444 * s ^ 21
    - 1544555472 * s ^ 20
    + 1725863234 * s ^ 19
    - 1448752099 * s ^ 18
    + 488636735 * s ^ 17
    + 1038607880 * s ^ 16
    - 2562919426 * s ^ 15
    + 3353269222 * s ^ 14
    - 3083758427 * s ^ 13
    + 2073738387 * s ^ 12
    - 961064631 * s ^ 11
    + 238684271 * s ^ 10
    + 15656250 * s ^ 9
    - 30557453 * s ^ 8
    + 7753862 * s ^ 7
    - 379067 * s ^ 6
    + 2713 * s ^ 5
    - 18290 * s ^ 4
    - 320 * s ^ 3
    + 22 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient11 (s : ℚ) : ℚ :=
  s ^ 35
    - 31 * s ^ 34
    + 522 * s ^ 33
    - 5473 * s ^ 32
    + 34682 * s ^ 31
    - 105240 * s ^ 30
    - 214548 * s ^ 29
    + 4054273 * s ^ 28
    - 22995152 * s ^ 27
    + 83768306 * s ^ 26
    - 224032602 * s ^ 25
    + 462286988 * s ^ 24
    - 750794049 * s ^ 23
    + 969174265 * s ^ 22
    - 977881363 * s ^ 21
    + 573180108 * s ^ 20
    + 693068679 * s ^ 19
    - 3359182300 * s ^ 18
    + 7343459892 * s ^ 17
    - 11431420253 * s ^ 16
    + 13716564435 * s ^ 15
    - 12892361760 * s ^ 14
    + 9365190893 * s ^ 13
    - 4955204947 * s ^ 12
    + 1538145189 * s ^ 11
    + 69606220 * s ^ 10
    - 321942121 * s ^ 9
    + 141553212 * s ^ 8
    - 24187148 * s ^ 7
    + 133107 * s ^ 6
    + 41620 * s ^ 5
    + 61160 * s ^ 4
    + 3631 * s ^ 3
    - 195 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient12 (s : ℚ) : ℚ :=
  -11 * s ^ 34
    + 418 * s ^ 33
    - 7539 * s ^ 32
    + 83006 * s ^ 31
    - 615679 * s ^ 30
    + 3236184 * s ^ 29
    - 12371616 * s ^ 28
    + 34579984 * s ^ 27
    - 68426610 * s ^ 26
    + 80249278 * s ^ 25
    + 21080375 * s ^ 24
    - 379339649 * s ^ 23
    + 1171554939 * s ^ 22
    - 2724254117 * s ^ 21
    + 5801376834 * s ^ 20
    - 11462577174 * s ^ 19
    + 19878487324 * s ^ 18
    - 29027311180 * s ^ 17
    + 35026055339 * s ^ 16
    - 34382899531 * s ^ 15
    + 26673334489 * s ^ 14
    - 15255973335 * s ^ 13
    + 5002596162 * s ^ 12
    + 831618681 * s ^ 11
    - 2166718914 * s ^ 10
    + 1284045275 * s ^ 9
    - 366188521 * s ^ 8
    + 32558454 * s ^ 7
    + 6518819 * s ^ 6
    - 524506 * s ^ 5
    - 148846 * s ^ 4
    - 19199 * s ^ 3
    + 847 * s ^ 2
    + 19 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient13 (s : ℚ) : ℚ :=
  -2 * s ^ 35
    + 70 * s ^ 34
    - 1132 * s ^ 33
    + 10841 * s ^ 32
    - 64729 * s ^ 31
    + 215204 * s ^ 30
    - 8901 * s ^ 29
    - 4288911 * s ^ 28
    + 27650751 * s ^ 27
    - 109813181 * s ^ 26
    + 328274371 * s ^ 25
    - 810283747 * s ^ 24
    + 1789797395 * s ^ 23
    - 3819482225 * s ^ 22
    + 8103535800 * s ^ 21
    - 16334822410 * s ^ 20
    + 29209120544 * s ^ 19
    - 44321281316 * s ^ 18
    + 55892333176 * s ^ 17
    - 57564654358 * s ^ 16
    + 46673568224 * s ^ 15
    - 26905942556 * s ^ 14
    + 6592097588 * s ^ 13
    + 6569467051 * s ^ 12
    - 9997639756 * s ^ 11
    + 6880068147 * s ^ 10
    - 2674547406 * s ^ 9
    + 452031709 * s ^ 8
    + 55421884 * s ^ 7
    - 32639625 * s ^ 6
    + 1409189 * s ^ 5
    + 413238 * s ^ 4
    + 57069 * s ^ 3
    - 1866 * s ^ 2
    - 129 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient14 (s : ℚ) : ℚ :=
  14 * s ^ 34
    - 486 * s ^ 33
    + 7989 * s ^ 32
    - 81928 * s ^ 31
    + 584400 * s ^ 30
    - 3078360 * s ^ 29
    + 12508869 * s ^ 28
    - 41044566 * s ^ 27
    + 115953626 * s ^ 26
    - 308135665 * s ^ 25
    + 831756522 * s ^ 24
    - 2281163900 * s ^ 23
    + 5929364632 * s ^ 22
    - 13588450796 * s ^ 21
    + 26289884554 * s ^ 20
    - 42088636409 * s ^ 19
    + 55146609623 * s ^ 18
    - 57967674048 * s ^ 17
    + 45901703177 * s ^ 16
    - 21145960151 * s ^ 15
    - 6906473804 * s ^ 14
    + 26630667263 * s ^ 13
    - 31360152821 * s ^ 12
    + 23261806911 * s ^ 11
    - 11031648746 * s ^ 10
    + 2635274242 * s ^ 9
    + 239071226 * s ^ 8
    - 348020679 * s ^ 7
    + 74872654 * s ^ 6
    + 2035001 * s ^ 5
    - 1473518 * s ^ 4
    - 107778 * s ^ 3
    + 2565 * s ^ 2
    + 373 * s
    + 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient15 (s : ℚ) : ℚ :=
  s ^ 35
    - 35 * s ^ 34
    + 564 * s ^ 33
    - 5511 * s ^ 32
    + 36293 * s ^ 31
    - 172119 * s ^ 30
    + 651062 * s ^ 29
    - 2474370 * s ^ 28
    + 11717693 * s ^ 27
    - 60239101 * s ^ 26
    + 272319296 * s ^ 25
    - 1007542796 * s ^ 24
    + 3026806380 * s ^ 23
    - 7404329399 * s ^ 22
    + 14746559342 * s ^ 21
    - 23765376261 * s ^ 20
    + 30414511689 * s ^ 19
    - 29050518028 * s ^ 18
    + 15486161476 * s ^ 17
    + 9600896259 * s ^ 16
    - 38828246358 * s ^ 15
    + 60312217051 * s ^ 14
    - 64354293113 * s ^ 13
    + 50156805542 * s ^ 12
    - 26988773164 * s ^ 11
    + 7714314667 * s ^ 10
    + 1027967849 * s ^ 9
    - 1935664240 * s ^ 8
    + 710633553 * s ^ 7
    - 65803141 * s ^ 6
    - 22550029 * s ^ 5
    + 4196927 * s ^ 4
    + 203069 * s ^ 3
    - 10987 * s ^ 2
    + 29 * s
    - 90

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient16 (s : ℚ) : ℚ :=
  -2 * s ^ 34
    + 58 * s ^ 33
    - 701 * s ^ 32
    + 3607 * s ^ 31
    + 11376 * s ^ 30
    - 356696 * s ^ 29
    + 3321545 * s ^ 28
    - 20173460 * s ^ 27
    + 91577135 * s ^ 26
    - 327527994 * s ^ 25
    + 943684402 * s ^ 24
    - 2196972619 * s ^ 23
    + 4065857482 * s ^ 22
    - 5679534480 * s ^ 21
    + 4943045009 * s ^ 20
    + 1007976776 * s ^ 19
    - 14465988527 * s ^ 18
    + 35375168536 * s ^ 17
    - 59542940654 * s ^ 16
    + 78303451126 * s ^ 15
    - 82021720972 * s ^ 14
    + 66671313741 * s ^ 13
    - 38342151005 * s ^ 12
    + 10713822637 * s ^ 11
    + 4612782847 * s ^ 10
    - 6768497721 * s ^ 9
    + 3297384668 * s ^ 8
    - 623139222 * s ^ 7
    - 99188506 * s ^ 6
    + 66595257 * s ^ 5
    - 7206315 * s ^ 4
    - 659129 * s ^ 3
    + 65467 * s ^ 2
    - 4017 * s
    + 351

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient17 (s : ℚ) : ℚ :=
  -s ^ 34
    + 41 * s ^ 33
    - 795 * s ^ 32
    + 9698 * s ^ 31
    - 83424 * s ^ 30
    + 537243 * s ^ 29
    - 2679695 * s ^ 28
    + 10519498 * s ^ 27
    - 32343488 * s ^ 26
    + 74330210 * s ^ 25
    - 104143577 * s ^ 24
    - 45911290 * s ^ 23
    + 827503063 * s ^ 22
    - 3066681103 * s ^ 21
    + 7846998912 * s ^ 20
    - 16168884671 * s ^ 19
    + 28368656645 * s ^ 18
    - 43028187392 * s ^ 17
    + 55735200544 * s ^ 16
    - 59709857036 * s ^ 15
    + 49793327272 * s ^ 14
    - 27513238879 * s ^ 13
    + 2392563407 * s ^ 12
    + 13601691101 * s ^ 11
    - 15475134133 * s ^ 10
    + 8760316680 * s ^ 9
    - 2295231203 * s ^ 8
    - 260984648 * s ^ 7
    + 390785438 * s ^ 6
    - 105483393 * s ^ 5
    + 4496551 * s ^ 4
    + 2120408 * s ^ 3
    - 226736 * s ^ 2
    + 15677 * s
    - 924

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient18 (s : ℚ) : ℚ :=
  s ^ 33
    - 39 * s ^ 32
    + 734 * s ^ 31
    - 8876 * s ^ 30
    + 77623 * s ^ 29
    - 524795 * s ^ 28
    + 2864383 * s ^ 27
    - 12991038 * s ^ 26
    + 49837434 * s ^ 25
    - 163340792 * s ^ 24
    + 460705672 * s ^ 23
    - 1130449518 * s ^ 22
    + 2457021685 * s ^ 21
    - 4827874827 * s ^ 20
    + 8642814219 * s ^ 19
    - 13840729279 * s ^ 18
    + 18984066698 * s ^ 17
    - 20845361779 * s ^ 16
    + 15897299157 * s ^ 15
    - 3467366790 * s ^ 14
    - 11992538144 * s ^ 13
    + 22481855606 * s ^ 12
    - 22335245025 * s ^ 11
    + 13601092729 * s ^ 10
    - 4024460676 * s ^ 9
    - 817869182 * s ^ 8
    + 1346140642 * s ^ 7
    - 554916095 * s ^ 6
    + 84676532 * s ^ 5
    + 9501738 * s ^ 4
    - 4737316 * s ^ 3
    + 491945 * s ^ 2
    - 34355 * s
    + 1728

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient19 (s : ℚ) : ℚ :=
  -s ^ 31
    + 39 * s ^ 30
    - 721 * s ^ 29
    + 8312 * s ^ 28
    - 66791 * s ^ 27
    + 400519 * s ^ 26
    - 1905094 * s ^ 25
    + 7701213 * s ^ 24
    - 28262696 * s ^ 23
    + 96331118 * s ^ 22
    - 293516419 * s ^ 21
    + 748907363 * s ^ 20
    - 1498369865 * s ^ 19
    + 2146532868 * s ^ 18
    - 1609821857 * s ^ 17
    - 1489373346 * s ^ 16
    + 7609261947 * s ^ 15
    - 15033064532 * s ^ 14
    + 19928221407 * s ^ 13
    - 18679235044 * s ^ 12
    + 11380815681 * s ^ 11
    - 2633763932 * s ^ 10
    - 2509706357 * s ^ 9
    + 3057470978 * s ^ 8
    - 1559714324 * s ^ 7
    + 378345065 * s ^ 6
    + 5576816 * s ^ 5
    - 29277646 * s ^ 4
    + 7174903 * s ^ 3
    - 717375 * s ^ 2
    + 50123 * s
    - 2352

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient20 (s : ℚ) : ℚ :=
  s ^ 29
    - 63 * s ^ 28
    + 1567 * s ^ 27
    - 22171 * s ^ 26
    + 205566 * s ^ 25
    - 1335532 * s ^ 24
    + 6251931 * s ^ 23
    - 20943067 * s ^ 22
    + 46571937 * s ^ 21
    - 43586122 * s ^ 20
    - 136799891 * s ^ 19
    + 792062518 * s ^ 18
    - 2254422323 * s ^ 17
    + 4570768572 * s ^ 16
    - 7129201271 * s ^ 15
    + 8573222487 * s ^ 14
    - 7419786977 * s ^ 13
    + 3414022868 * s ^ 12
    + 1547332428 * s ^ 11
    - 4589130785 * s ^ 10
    + 4473077373 * s ^ 9
    - 2521590423 * s ^ 8
    + 765099226 * s ^ 7
    - 9630004 * s ^ 6
    - 94787922 * s ^ 5
    + 39399664 * s ^ 4
    - 7452744 * s ^ 3
    + 721776 * s ^ 2
    - 50965 * s
    + 2346

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient21 (s : ℚ) : ℚ :=
  -3 * s ^ 28
    + 127 * s ^ 27
    - 2518 * s ^ 26
    + 31098 * s ^ 25
    - 268098 * s ^ 24
    + 1712718 * s ^ 23
    - 8402814 * s ^ 22
    + 32409790 * s ^ 21
    - 99933051 * s ^ 20
    + 249491526 * s ^ 19
    - 508566544 * s ^ 18
    + 844563666 * s ^ 17
    - 1105577330 * s ^ 16
    + 991917403 * s ^ 15
    - 154595820 * s ^ 14
    - 1477045834 * s ^ 13
    + 3322407261 * s ^ 12
    - 4311332703 * s ^ 11
    + 3783074625 * s ^ 10
    - 2199381185 * s ^ 9
    + 679671431 * s ^ 8
    + 86283936 * s ^ 7
    - 210536979 * s ^ 6
    + 111305008 * s ^ 5
    - 32024491 * s ^ 4
    + 5261979 * s ^ 3
    - 497744 * s ^ 2
    + 36247 * s
    - 1701

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient22 (s : ℚ) : ℚ :=
  s ^ 27
    - 40 * s ^ 26
    + 758 * s ^ 25
    - 9014 * s ^ 24
    + 75165 * s ^ 23
    - 466061 * s ^ 22
    + 2230786 * s ^ 21
    - 8490894 * s ^ 20
    + 26491873 * s ^ 19
    - 70250755 * s ^ 18
    + 164695799 * s ^ 17
    - 350673666 * s ^ 16
    + 675289282 * s ^ 15
    - 1136123489 * s ^ 14
    + 1592394883 * s ^ 13
    - 1766398110 * s ^ 12
    + 1447455120 * s ^ 11
    - 744371668 * s ^ 10
    + 49836749 * s ^ 9
    + 307552386 * s ^ 8
    - 317088174 * s ^ 7
    + 180912499 * s ^ 6
    - 67011705 * s ^ 5
    + 16155438 * s ^ 4
    - 2416117 * s ^ 3
    + 225652 * s ^ 2
    - 17572 * s
    + 874

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient23 (s : ℚ) : ℚ :=
  3 * s ^ 24
    - 124 * s ^ 23
    + 2353 * s ^ 22
    - 27291 * s ^ 21
    + 216962 * s ^ 20
    - 1254862 * s ^ 19
    + 5461321 * s ^ 18
    - 18208811 * s ^ 17
    + 46751398 * s ^ 16
    - 91516913 * s ^ 15
    + 131426978 * s ^ 14
    - 121653723 * s ^ 13
    + 25363139 * s ^ 12
    + 137126547 * s ^ 11
    - 282202900 * s ^ 10
    + 328042983 * s ^ 9
    - 266342772 * s ^ 8
    + 158360237 * s ^ 7
    - 69165695 * s ^ 6
    + 21686115 * s ^ 5
    - 4653970 * s ^ 4
    + 644565 * s ^ 3
    - 60691 * s ^ 2
    + 5453 * s
    - 302

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient24 (s : ℚ) : ℚ :=
  -s ^ 23
    + 38 * s ^ 22
    - 677 * s ^ 21
    + 7516 * s ^ 20
    - 58295 * s ^ 19
    + 335659 * s ^ 18
    - 1488279 * s ^ 17
    + 5202127 * s ^ 16
    - 14556287 * s ^ 15
    + 32926350 * s ^ 14
    - 60549439 * s ^ 13
    + 90727902 * s ^ 12
    - 110697863 * s ^ 11
    + 109587463 * s ^ 10
    - 87437077 * s ^ 9
    + 55627119 * s ^ 8
    - 27750268 * s ^ 7
    + 10570442 * s ^ 6
    - 2946383 * s ^ 5
    + 564299 * s ^ 4
    - 70756 * s ^ 3
    + 7294 * s ^ 2
    - 947 * s
    + 63

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient25 (s : ℚ) : ℚ :=
  s ^ 14
    - 23 * s ^ 13
    + 237 * s ^ 12
    - 1444 * s ^ 11
    + 5781 * s ^ 10
    - 15979 * s ^ 9
    + 31169 * s ^ 8
    - 43057 * s ^ 7
    + 41561 * s ^ 6
    - 27053 * s ^ 5
    + 10990 * s ^ 4
    - 2269 * s ^ 3
    + 27 * s ^ 2
    + 65 * s
    - 6

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

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_0 (s : ℚ) :
    t3Step2Coefficient0 s =
    t3Step1Coefficient0 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient0,
    t3Step1Coefficient0,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_1 (s : ℚ) :
    t3Step2Coefficient1 s =
    t3Step1Coefficient0 s *
        differenceCoefficient1 s
      + t3Step1Coefficient1 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient1,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_2 (s : ℚ) :
    t3Step2Coefficient2 s =
    t3Step1Coefficient0 s *
        differenceCoefficient2 s
      + t3Step1Coefficient1 s *
        differenceCoefficient1 s
      + t3Step1Coefficient2 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient2,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_3 (s : ℚ) :
    t3Step2Coefficient3 s =
    t3Step1Coefficient0 s *
        differenceCoefficient3 s
      + t3Step1Coefficient1 s *
        differenceCoefficient2 s
      + t3Step1Coefficient2 s *
        differenceCoefficient1 s
      + t3Step1Coefficient3 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient3,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_4 (s : ℚ) :
    t3Step2Coefficient4 s =
    t3Step1Coefficient0 s *
        differenceCoefficient4 s
      + t3Step1Coefficient1 s *
        differenceCoefficient3 s
      + t3Step1Coefficient2 s *
        differenceCoefficient2 s
      + t3Step1Coefficient3 s *
        differenceCoefficient1 s
      + t3Step1Coefficient4 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient4,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_5 (s : ℚ) :
    t3Step2Coefficient5 s =
    t3Step1Coefficient0 s *
        differenceCoefficient5 s
      + t3Step1Coefficient1 s *
        differenceCoefficient4 s
      + t3Step1Coefficient2 s *
        differenceCoefficient3 s
      + t3Step1Coefficient3 s *
        differenceCoefficient2 s
      + t3Step1Coefficient4 s *
        differenceCoefficient1 s
      + t3Step1Coefficient5 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient5,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_6 (s : ℚ) :
    t3Step2Coefficient6 s =
    t3Step1Coefficient0 s *
        differenceCoefficient6 s
      + t3Step1Coefficient1 s *
        differenceCoefficient5 s
      + t3Step1Coefficient2 s *
        differenceCoefficient4 s
      + t3Step1Coefficient3 s *
        differenceCoefficient3 s
      + t3Step1Coefficient4 s *
        differenceCoefficient2 s
      + t3Step1Coefficient5 s *
        differenceCoefficient1 s
      + t3Step1Coefficient6 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient6,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_7 (s : ℚ) :
    t3Step2Coefficient7 s =
    t3Step1Coefficient0 s *
        differenceCoefficient7 s
      + t3Step1Coefficient1 s *
        differenceCoefficient6 s
      + t3Step1Coefficient2 s *
        differenceCoefficient5 s
      + t3Step1Coefficient3 s *
        differenceCoefficient4 s
      + t3Step1Coefficient4 s *
        differenceCoefficient3 s
      + t3Step1Coefficient5 s *
        differenceCoefficient2 s
      + t3Step1Coefficient6 s *
        differenceCoefficient1 s
      + t3Step1Coefficient7 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient7,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_8 (s : ℚ) :
    t3Step2Coefficient8 s =
    t3Step1Coefficient0 s *
        differenceCoefficient8 s
      + t3Step1Coefficient1 s *
        differenceCoefficient7 s
      + t3Step1Coefficient2 s *
        differenceCoefficient6 s
      + t3Step1Coefficient3 s *
        differenceCoefficient5 s
      + t3Step1Coefficient4 s *
        differenceCoefficient4 s
      + t3Step1Coefficient5 s *
        differenceCoefficient3 s
      + t3Step1Coefficient6 s *
        differenceCoefficient2 s
      + t3Step1Coefficient7 s *
        differenceCoefficient1 s
      + t3Step1Coefficient8 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient8,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_9 (s : ℚ) :
    t3Step2Coefficient9 s =
    t3Step1Coefficient0 s *
        differenceCoefficient9 s
      + t3Step1Coefficient1 s *
        differenceCoefficient8 s
      + t3Step1Coefficient2 s *
        differenceCoefficient7 s
      + t3Step1Coefficient3 s *
        differenceCoefficient6 s
      + t3Step1Coefficient4 s *
        differenceCoefficient5 s
      + t3Step1Coefficient5 s *
        differenceCoefficient4 s
      + t3Step1Coefficient6 s *
        differenceCoefficient3 s
      + t3Step1Coefficient7 s *
        differenceCoefficient2 s
      + t3Step1Coefficient8 s *
        differenceCoefficient1 s
      + t3Step1Coefficient9 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient9,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_10 (s : ℚ) :
    t3Step2Coefficient10 s =
    t3Step1Coefficient0 s *
        differenceCoefficient10 s
      + t3Step1Coefficient1 s *
        differenceCoefficient9 s
      + t3Step1Coefficient2 s *
        differenceCoefficient8 s
      + t3Step1Coefficient3 s *
        differenceCoefficient7 s
      + t3Step1Coefficient4 s *
        differenceCoefficient6 s
      + t3Step1Coefficient5 s *
        differenceCoefficient5 s
      + t3Step1Coefficient6 s *
        differenceCoefficient4 s
      + t3Step1Coefficient7 s *
        differenceCoefficient3 s
      + t3Step1Coefficient8 s *
        differenceCoefficient2 s
      + t3Step1Coefficient9 s *
        differenceCoefficient1 s
      + t3Step1Coefficient10 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient10,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_11 (s : ℚ) :
    t3Step2Coefficient11 s =
    t3Step1Coefficient0 s *
        differenceCoefficient11 s
      + t3Step1Coefficient1 s *
        differenceCoefficient10 s
      + t3Step1Coefficient2 s *
        differenceCoefficient9 s
      + t3Step1Coefficient3 s *
        differenceCoefficient8 s
      + t3Step1Coefficient4 s *
        differenceCoefficient7 s
      + t3Step1Coefficient5 s *
        differenceCoefficient6 s
      + t3Step1Coefficient6 s *
        differenceCoefficient5 s
      + t3Step1Coefficient7 s *
        differenceCoefficient4 s
      + t3Step1Coefficient8 s *
        differenceCoefficient3 s
      + t3Step1Coefficient9 s *
        differenceCoefficient2 s
      + t3Step1Coefficient10 s *
        differenceCoefficient1 s
    := by
  simp only [t3Step2Coefficient11,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2,
    differenceCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_12 (s : ℚ) :
    t3Step2Coefficient12 s =
    t3Step1Coefficient0 s *
        differenceCoefficient12 s
      + t3Step1Coefficient1 s *
        differenceCoefficient11 s
      + t3Step1Coefficient2 s *
        differenceCoefficient10 s
      + t3Step1Coefficient3 s *
        differenceCoefficient9 s
      + t3Step1Coefficient4 s *
        differenceCoefficient8 s
      + t3Step1Coefficient5 s *
        differenceCoefficient7 s
      + t3Step1Coefficient6 s *
        differenceCoefficient6 s
      + t3Step1Coefficient7 s *
        differenceCoefficient5 s
      + t3Step1Coefficient8 s *
        differenceCoefficient4 s
      + t3Step1Coefficient9 s *
        differenceCoefficient3 s
      + t3Step1Coefficient10 s *
        differenceCoefficient2 s
    := by
  simp only [t3Step2Coefficient12,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3,
    differenceCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_13 (s : ℚ) :
    t3Step2Coefficient13 s =
    t3Step1Coefficient0 s *
        differenceCoefficient13 s
      + t3Step1Coefficient1 s *
        differenceCoefficient12 s
      + t3Step1Coefficient2 s *
        differenceCoefficient11 s
      + t3Step1Coefficient3 s *
        differenceCoefficient10 s
      + t3Step1Coefficient4 s *
        differenceCoefficient9 s
      + t3Step1Coefficient5 s *
        differenceCoefficient8 s
      + t3Step1Coefficient6 s *
        differenceCoefficient7 s
      + t3Step1Coefficient7 s *
        differenceCoefficient6 s
      + t3Step1Coefficient8 s *
        differenceCoefficient5 s
      + t3Step1Coefficient9 s *
        differenceCoefficient4 s
      + t3Step1Coefficient10 s *
        differenceCoefficient3 s
    := by
  simp only [t3Step2Coefficient13,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4,
    differenceCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_14 (s : ℚ) :
    t3Step2Coefficient14 s =
    t3Step1Coefficient0 s *
        differenceCoefficient14 s
      + t3Step1Coefficient1 s *
        differenceCoefficient13 s
      + t3Step1Coefficient2 s *
        differenceCoefficient12 s
      + t3Step1Coefficient3 s *
        differenceCoefficient11 s
      + t3Step1Coefficient4 s *
        differenceCoefficient10 s
      + t3Step1Coefficient5 s *
        differenceCoefficient9 s
      + t3Step1Coefficient6 s *
        differenceCoefficient8 s
      + t3Step1Coefficient7 s *
        differenceCoefficient7 s
      + t3Step1Coefficient8 s *
        differenceCoefficient6 s
      + t3Step1Coefficient9 s *
        differenceCoefficient5 s
      + t3Step1Coefficient10 s *
        differenceCoefficient4 s
    := by
  simp only [t3Step2Coefficient14,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5,
    differenceCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_15 (s : ℚ) :
    t3Step2Coefficient15 s =
    t3Step1Coefficient0 s *
        differenceCoefficient15 s
      + t3Step1Coefficient1 s *
        differenceCoefficient14 s
      + t3Step1Coefficient2 s *
        differenceCoefficient13 s
      + t3Step1Coefficient3 s *
        differenceCoefficient12 s
      + t3Step1Coefficient4 s *
        differenceCoefficient11 s
      + t3Step1Coefficient5 s *
        differenceCoefficient10 s
      + t3Step1Coefficient6 s *
        differenceCoefficient9 s
      + t3Step1Coefficient7 s *
        differenceCoefficient8 s
      + t3Step1Coefficient8 s *
        differenceCoefficient7 s
      + t3Step1Coefficient9 s *
        differenceCoefficient6 s
      + t3Step1Coefficient10 s *
        differenceCoefficient5 s
    := by
  simp only [t3Step2Coefficient15,
    t3Step1Coefficient0,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_16 (s : ℚ) :
    t3Step2Coefficient16 s =
    t3Step1Coefficient1 s *
        differenceCoefficient15 s
      + t3Step1Coefficient2 s *
        differenceCoefficient14 s
      + t3Step1Coefficient3 s *
        differenceCoefficient13 s
      + t3Step1Coefficient4 s *
        differenceCoefficient12 s
      + t3Step1Coefficient5 s *
        differenceCoefficient11 s
      + t3Step1Coefficient6 s *
        differenceCoefficient10 s
      + t3Step1Coefficient7 s *
        differenceCoefficient9 s
      + t3Step1Coefficient8 s *
        differenceCoefficient8 s
      + t3Step1Coefficient9 s *
        differenceCoefficient7 s
      + t3Step1Coefficient10 s *
        differenceCoefficient6 s
    := by
  simp only [t3Step2Coefficient16,
    t3Step1Coefficient1,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_17 (s : ℚ) :
    t3Step2Coefficient17 s =
    t3Step1Coefficient2 s *
        differenceCoefficient15 s
      + t3Step1Coefficient3 s *
        differenceCoefficient14 s
      + t3Step1Coefficient4 s *
        differenceCoefficient13 s
      + t3Step1Coefficient5 s *
        differenceCoefficient12 s
      + t3Step1Coefficient6 s *
        differenceCoefficient11 s
      + t3Step1Coefficient7 s *
        differenceCoefficient10 s
      + t3Step1Coefficient8 s *
        differenceCoefficient9 s
      + t3Step1Coefficient9 s *
        differenceCoefficient8 s
      + t3Step1Coefficient10 s *
        differenceCoefficient7 s
    := by
  simp only [t3Step2Coefficient17,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_18 (s : ℚ) :
    t3Step2Coefficient18 s =
    t3Step1Coefficient3 s *
        differenceCoefficient15 s
      + t3Step1Coefficient4 s *
        differenceCoefficient14 s
      + t3Step1Coefficient5 s *
        differenceCoefficient13 s
      + t3Step1Coefficient6 s *
        differenceCoefficient12 s
      + t3Step1Coefficient7 s *
        differenceCoefficient11 s
      + t3Step1Coefficient8 s *
        differenceCoefficient10 s
      + t3Step1Coefficient9 s *
        differenceCoefficient9 s
      + t3Step1Coefficient10 s *
        differenceCoefficient8 s
    := by
  simp only [t3Step2Coefficient18,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_19 (s : ℚ) :
    t3Step2Coefficient19 s =
    t3Step1Coefficient4 s *
        differenceCoefficient15 s
      + t3Step1Coefficient5 s *
        differenceCoefficient14 s
      + t3Step1Coefficient6 s *
        differenceCoefficient13 s
      + t3Step1Coefficient7 s *
        differenceCoefficient12 s
      + t3Step1Coefficient8 s *
        differenceCoefficient11 s
      + t3Step1Coefficient9 s *
        differenceCoefficient10 s
      + t3Step1Coefficient10 s *
        differenceCoefficient9 s
    := by
  simp only [t3Step2Coefficient19,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_20 (s : ℚ) :
    t3Step2Coefficient20 s =
    t3Step1Coefficient5 s *
        differenceCoefficient15 s
      + t3Step1Coefficient6 s *
        differenceCoefficient14 s
      + t3Step1Coefficient7 s *
        differenceCoefficient13 s
      + t3Step1Coefficient8 s *
        differenceCoefficient12 s
      + t3Step1Coefficient9 s *
        differenceCoefficient11 s
      + t3Step1Coefficient10 s *
        differenceCoefficient10 s
    := by
  simp only [t3Step2Coefficient20,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11,
    differenceCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_21 (s : ℚ) :
    t3Step2Coefficient21 s =
    t3Step1Coefficient6 s *
        differenceCoefficient15 s
      + t3Step1Coefficient7 s *
        differenceCoefficient14 s
      + t3Step1Coefficient8 s *
        differenceCoefficient13 s
      + t3Step1Coefficient9 s *
        differenceCoefficient12 s
      + t3Step1Coefficient10 s *
        differenceCoefficient11 s
    := by
  simp only [t3Step2Coefficient21,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12,
    differenceCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_22 (s : ℚ) :
    t3Step2Coefficient22 s =
    t3Step1Coefficient7 s *
        differenceCoefficient15 s
      + t3Step1Coefficient8 s *
        differenceCoefficient14 s
      + t3Step1Coefficient9 s *
        differenceCoefficient13 s
      + t3Step1Coefficient10 s *
        differenceCoefficient12 s
    := by
  simp only [t3Step2Coefficient22,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13,
    differenceCoefficient12]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_23 (s : ℚ) :
    t3Step2Coefficient23 s =
    t3Step1Coefficient8 s *
        differenceCoefficient15 s
      + t3Step1Coefficient9 s *
        differenceCoefficient14 s
      + t3Step1Coefficient10 s *
        differenceCoefficient13 s
    := by
  simp only [t3Step2Coefficient23,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14,
    differenceCoefficient13]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_24 (s : ℚ) :
    t3Step2Coefficient24 s =
    t3Step1Coefficient9 s *
        differenceCoefficient15 s
      + t3Step1Coefficient10 s *
        differenceCoefficient14 s
    := by
  simp only [t3Step2Coefficient24,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    differenceCoefficient15,
    differenceCoefficient14]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_25 (s : ℚ) :
    t3Step2Coefficient25 s =
    t3Step1Coefficient10 s *
        differenceCoefficient15 s
    := by
  simp only [t3Step2Coefficient25,
    t3Step1Coefficient10,
    differenceCoefficient15]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t3Step2_eq_t3Step1_mul_difference (r s : ℚ) :
    t3Step2 r s = t3Step1 r s * difference r s := by
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
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 32
    + 3 * s ^ 31
    - 4 * s ^ 30
    + 3 * s ^ 29
    + s ^ 28
    - 7 * s ^ 27
    + 13 * s ^ 26
    - 18 * s ^ 25
    + 20 * s ^ 24
    - 19 * s ^ 23
    + 15 * s ^ 22
    - 9 * s ^ 21
    + 4 * s ^ 20
    - s ^ 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient2 (s : ℚ) : ℚ :=
  s ^ 37
    - 7 * s ^ 36
    + 27 * s ^ 35
    - 74 * s ^ 34
    + 160 * s ^ 33
    - 310 * s ^ 32
    + 620 * s ^ 31
    - 1150 * s ^ 30
    + 1818 * s ^ 29
    - 2493 * s ^ 28
    + 2991 * s ^ 27
    - 3200 * s ^ 26
    + 3094 * s ^ 25
    - 2666 * s ^ 24
    + 2019 * s ^ 23
    - 1269 * s ^ 22
    + 603 * s ^ 21
    - 190 * s ^ 20
    + 13 * s ^ 19
    + 15 * s ^ 18
    - 2 * s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 39
    + 22 * s ^ 38
    - 119 * s ^ 37
    + 404 * s ^ 36
    - 1024 * s ^ 35
    + 2183 * s ^ 34
    - 4378 * s ^ 33
    + 8753 * s ^ 32
    - 16196 * s ^ 31
    + 24686 * s ^ 30
    - 30647 * s ^ 29
    + 32090 * s ^ 28
    - 28273 * s ^ 27
    + 20400 * s ^ 26
    - 9501 * s ^ 25
    - 3747 * s ^ 24
    + 16806 * s ^ 23
    - 26589 * s ^ 22
    + 29218 * s ^ 21
    - 24258 * s ^ 20
    + 15930 * s ^ 19
    - 8296 * s ^ 18
    + 3640 * s ^ 17
    - 1550 * s ^ 16
    + 604 * s ^ 15
    - 200 * s ^ 14
    + 53 * s ^ 13
    - 10 * s ^ 12
    + s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient4 (s : ℚ) : ℚ :=
  s ^ 41
    - 17 * s ^ 40
    + 129 * s ^ 39
    - 561 * s ^ 38
    + 1579 * s ^ 37
    - 3164 * s ^ 36
    + 5539 * s ^ 35
    - 11024 * s ^ 34
    + 24434 * s ^ 33
    - 43623 * s ^ 32
    + 40318 * s ^ 31
    + 31985 * s ^ 30
    - 183563 * s ^ 29
    + 382245 * s ^ 28
    - 595464 * s ^ 27
    + 802069 * s ^ 26
    - 1003457 * s ^ 25
    + 1181449 * s ^ 24
    - 1274198 * s ^ 23
    + 1218550 * s ^ 22
    - 991591 * s ^ 21
    + 670350 * s ^ 20
    - 376253 * s ^ 19
    + 176746 * s ^ 18
    - 75688 * s ^ 17
    + 32652 * s ^ 16
    - 12465 * s ^ 15
    + 3656 * s ^ 14
    - 646 * s ^ 13
    - 34 * s ^ 12
    + 60 * s ^ 11
    - 15 * s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient5 (s : ℚ) : ℚ :=
  2 * s ^ 42
    - 29 * s ^ 41
    + 172 * s ^ 40
    - 429 * s ^ 39
    - 397 * s ^ 38
    + 6249 * s ^ 37
    - 21740 * s ^ 36
    + 47421 * s ^ 35
    - 99126 * s ^ 34
    + 281965 * s ^ 33
    - 875759 * s ^ 32
    + 2228396 * s ^ 31
    - 4354570 * s ^ 30
    + 6791717 * s ^ 29
    - 9200710 * s ^ 28
    + 11707998 * s ^ 27
    - 14531213 * s ^ 26
    + 17511017 * s ^ 25
    - 19647539 * s ^ 24
    + 19597858 * s ^ 23
    - 16750067 * s ^ 22
    + 11842583 * s ^ 21
    - 6794690 * s ^ 20
    + 3173805 * s ^ 19
    - 1270721 * s ^ 18
    + 540263 * s ^ 17
    - 256531 * s ^ 16
    + 88140 * s ^ 15
    - 9152 * s ^ 14
    - 10383 * s ^ 13
    + 7749 * s ^ 12
    - 2731 * s ^ 11
    + 470 * s ^ 10
    - 16 * s ^ 9
    - 2 * s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient6 (s : ℚ) : ℚ :=
  s ^ 43
    - 8 * s ^ 42
    - 65 * s ^ 41
    + 1266 * s ^ 40
    - 8643 * s ^ 39
    + 35148 * s ^ 38
    - 102220 * s ^ 37
    + 266120 * s ^ 36
    - 779862 * s ^ 35
    + 2446318 * s ^ 34
    - 6773705 * s ^ 33
    + 15130248 * s ^ 32
    - 26903936 * s ^ 31
    + 39384069 * s ^ 30
    - 52018121 * s ^ 29
    + 69812678 * s ^ 28
    - 98124223 * s ^ 27
    + 134819154 * s ^ 26
    - 167842534 * s ^ 25
    + 179633487 * s ^ 24
    - 159629216 * s ^ 23
    + 113402651 * s ^ 22
    - 60439964 * s ^ 21
    + 21541609 * s ^ 20
    - 3576155 * s ^ 19
    - 106958 * s ^ 18
    - 837216 * s ^ 17
    + 815053 * s ^ 16
    + 97292 * s ^ 15
    - 499579 * s ^ 14
    + 395827 * s ^ 13
    - 183201 * s ^ 12
    + 51746 * s ^ 11
    - 7057 * s ^ 10
    - 64 * s ^ 9
    + 58 * s ^ 8
    + 2 * s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 44
    + 31 * s ^ 43
    - 438 * s ^ 42
    + 3615 * s ^ 41
    - 19679 * s ^ 40
    + 78684 * s ^ 39
    - 267199 * s ^ 38
    + 901544 * s ^ 37
    - 3071715 * s ^ 36
    + 9396810 * s ^ 35
    - 23502847 * s ^ 34
    + 46367793 * s ^ 33
    - 72274499 * s ^ 32
    + 94886289 * s ^ 31
    - 129652519 * s ^ 30
    + 227029533 * s ^ 29
    - 434162011 * s ^ 28
    + 727353269 * s ^ 27
    - 996929137 * s ^ 26
    + 1099988926 * s ^ 25
    - 948217847 * s ^ 24
    + 585587968 * s ^ 23
    - 174411589 * s ^ 22
    - 106933753 * s ^ 21
    + 183946294 * s ^ 20
    - 123536264 * s ^ 19
    + 40081282 * s ^ 18
    + 641145 * s ^ 17
    + 386019 * s ^ 16
    - 10017201 * s ^ 15
    + 10870909 * s ^ 14
    - 6554181 * s ^ 13
    + 2595437 * s ^ 12
    - 635598 * s ^ 11
    + 67273 * s ^ 10
    + 4452 * s ^ 9
    - 724 * s ^ 8
    - 70 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient8 (s : ℚ) : ℚ :=
  -2 * s ^ 45
    + 50 * s ^ 44
    - 598 * s ^ 43
    + 4483 * s ^ 42
    - 23777 * s ^ 41
    + 100040 * s ^ 40
    - 381907 * s ^ 39
    + 1419992 * s ^ 38
    - 4817916 * s ^ 37
    + 13318666 * s ^ 36
    - 27431370 * s ^ 35
    + 38414733 * s ^ 34
    - 32258707 * s ^ 33
    + 33181070 * s ^ 32
    - 181475415 * s ^ 31
    + 740093678 * s ^ 30
    - 1885646367 * s ^ 29
    + 3377962256 * s ^ 28
    - 4506721399 * s ^ 27
    + 4486027477 * s ^ 26
    - 2972356535 * s ^ 25
    + 396553699 * s ^ 24
    + 2131400278 * s ^ 23
    - 3468769262 * s ^ 22
    + 3191497637 * s ^ 21
    - 1870276409 * s ^ 20
    + 554111402 * s ^ 19
    + 101188476 * s ^ 18
    - 126339476 * s ^ 17
    - 77178678 * s ^ 16
    + 181783026 * s ^ 15
    - 148414528 * s ^ 14
    + 76605417 * s ^ 13
    - 26773512 * s ^ 12
    + 5685489 * s ^ 11
    - 418015 * s ^ 10
    - 70204 * s ^ 9
    + 5084 * s ^ 8
    + 1080 * s ^ 7
    + 44 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 46
    + 24 * s ^ 45
    - 258 * s ^ 44
    + 1627 * s ^ 43
    - 6712 * s ^ 42
    + 21277 * s ^ 41
    - 74695 * s ^ 40
    + 310581 * s ^ 39
    - 933708 * s ^ 38
    + 620636 * s ^ 37
    + 7860940 * s ^ 36
    - 34348933 * s ^ 35
    + 41003653 * s ^ 34
    + 195556528 * s ^ 33
    - 1225118701 * s ^ 32
    + 3745073641 * s ^ 31
    - 7794033371 * s ^ 30
    + 11741790487 * s ^ 29
    - 12418635630 * s ^ 28
    + 7058836164 * s ^ 27
    + 4402389462 * s ^ 26
    - 18533405638 * s ^ 25
    + 29486783378 * s ^ 24
    - 31931479843 * s ^ 23
    + 24648877982 * s ^ 22
    - 11830047246 * s ^ 21
    + 488925268 * s ^ 20
    + 4543495456 * s ^ 19
    - 3564962031 * s ^ 18
    + 217723622 * s ^ 17
    + 2102109870 * s ^ 16
    - 2366607137 * s ^ 15
    + 1524001736 * s ^ 14
    - 678362030 * s ^ 13
    + 207714857 * s ^ 12
    - 36744881 * s ^ 11
    + 935008 * s ^ 10
    + 764867 * s ^ 9
    - 26263 * s ^ 8
    - 9073 * s ^ 7
    - 912 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 46
    + 38 * s ^ 45
    - 571 * s ^ 44
    + 4741 * s ^ 43
    - 24093 * s ^ 42
    + 74249 * s ^ 41
    - 113547 * s ^ 40
    - 77904 * s ^ 39
    + 1433194 * s ^ 38
    - 12322116 * s ^ 37
    + 88329352 * s ^ 36
    - 458393544 * s ^ 35
    + 1728629155 * s ^ 34
    - 4865926088 * s ^ 33
    + 10300379052 * s ^ 32
    - 15839594218 * s ^ 31
    + 14888203537 * s ^ 30
    + 1711127971 * s ^ 29
    - 38904114868 * s ^ 28
    + 90512571837 * s ^ 27
    - 138919190950 * s ^ 26
    + 161857962932 * s ^ 25
    - 142974949776 * s ^ 24
    + 83454503757 * s ^ 23
    - 6768695328 * s ^ 22
    - 52079393100 * s ^ 21
    + 68568192527 * s ^ 20
    - 45264946577 * s ^ 19
    + 6835444048 * s ^ 18
    + 21276199670 * s ^ 17
    - 28915029853 * s ^ 16
    + 21932259011 * s ^ 15
    - 11605824262 * s ^ 14
    + 4461363029 * s ^ 13
    - 1163408017 * s ^ 12
    + 147316514 * s ^ 11
    + 14582053 * s ^ 10
    - 6795835 * s ^ 9
    + 174012 * s ^ 8
    + 38445 * s ^ 7
    + 11457 * s ^ 6
    + 68 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient11 (s : ℚ) : ℚ :=
  -2 * s ^ 46
    + 86 * s ^ 45
    - 1645 * s ^ 44
    + 18729 * s ^ 43
    - 145255 * s ^ 42
    + 842071 * s ^ 41
    - 4000065 * s ^ 40
    + 17199298 * s ^ 39
    - 71171514 * s ^ 38
    + 276117511 * s ^ 37
    - 930001592 * s ^ 36
    + 2523873245 * s ^ 35
    - 5066660737 * s ^ 34
    + 5901893816 * s ^ 33
    + 3624398506 * s ^ 32
    - 38995272497 * s ^ 31
    + 114941293472 * s ^ 30
    - 228896585333 * s ^ 29
    + 347726252400 * s ^ 28
    - 413953738821 * s ^ 27
    + 371038658142 * s ^ 26
    - 192717967053 * s ^ 25
    - 91458972042 * s ^ 24
    + 385298896280 * s ^ 23
    - 557890154942 * s ^ 22
    + 520077054914 * s ^ 21
    - 292369383160 * s ^ 20
    - 392617541 * s ^ 19
    + 215684675864 * s ^ 18
    - 284993845117 * s ^ 17
    + 234828165350 * s ^ 16
    - 140534076703 * s ^ 15
    + 63050135332 * s ^ 14
    - 20616142852 * s ^ 13
    + 4146657688 * s ^ 12
    - 76356114 * s ^ 11
    - 215633835 * s ^ 10
    + 47953588 * s ^ 9
    - 1251993 * s ^ 8
    - 11590 * s ^ 7
    - 94167 * s ^ 6
    - 1757 * s ^ 5
    + 35 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient12 (s : ℚ) : ℚ :=
  -s ^ 47
    + 34 * s ^ 46
    - 548 * s ^ 45
    + 5498 * s ^ 44
    - 38888 * s ^ 43
    + 216809 * s ^ 42
    - 1084764 * s ^ 41
    + 5277559 * s ^ 40
    - 23481471 * s ^ 39
    + 81336128 * s ^ 38
    - 158625814 * s ^ 37
    - 236509852 * s ^ 36
    + 3506840758 * s ^ 35
    - 16829418156 * s ^ 34
    + 54597856989 * s ^ 33
    - 134370193048 * s ^ 32
    + 259315579910 * s ^ 31
    - 391065376380 * s ^ 30
    + 436782705047 * s ^ 29
    - 277192728125 * s ^ 28
    - 171094127240 * s ^ 27
    + 896668343145 * s ^ 26
    - 1754712052489 * s ^ 25
    + 2452038309589 * s ^ 24
    - 2615880995790 * s ^ 23
    + 1998206364435 * s ^ 22
    - 702074207745 * s ^ 21
    - 790145155907 * s ^ 20
    + 1877630324002 * s ^ 19
    - 2212775111484 * s ^ 18
    + 1871603468667 * s ^ 17
    - 1215432444942 * s ^ 16
    + 610797716009 * s ^ 15
    - 231363611421 * s ^ 14
    + 58980969278 * s ^ 13
    - 4721779095 * s ^ 12
    - 3464766223 * s ^ 11
    + 1567729462 * s ^ 10
    - 245235316 * s ^ 9
    + 4018335 * s ^ 8
    - 659373 * s ^ 7
    + 518602 * s ^ 6
    + 24301 * s ^ 5
    - 482 * s ^ 4
    - 3 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient13 (s : ℚ) : ℚ :=
  9 * s ^ 46
    - 274 * s ^ 45
    + 3920 * s ^ 44
    - 35293 * s ^ 43
    + 238512 * s ^ 42
    - 1491669 * s ^ 41
    + 10069427 * s ^ 40
    - 68342073 * s ^ 39
    + 404139447 * s ^ 38
    - 1945313924 * s ^ 37
    + 7497282966 * s ^ 36
    - 23058538646 * s ^ 35
    + 56032673043 * s ^ 34
    - 103692784407 * s ^ 33
    + 127722154634 * s ^ 32
    - 26816799438 * s ^ 31
    - 358507044566 * s ^ 30
    + 1179514395136 * s ^ 29
    - 2472952605663 * s ^ 28
    + 4076766177280 * s ^ 27
    - 5584837510089 * s ^ 26
    + 6321076354077 * s ^ 25
    - 5444571651452 * s ^ 24
    + 2382960712799 * s ^ 23
    + 2545917797290 * s ^ 22
    - 7907298361849 * s ^ 21
    + 11745562430178 * s ^ 20
    - 12712871830784 * s ^ 19
    + 10861865284780 * s ^ 18
    - 7461383982756 * s ^ 17
    + 4081259742067 * s ^ 16
    - 1713494864774 * s ^ 15
    + 494991815357 * s ^ 14
    - 49484522869 * s ^ 13
    - 40147678493 * s ^ 12
    + 25926116564 * s ^ 11
    - 7190430950 * s ^ 10
    + 792918659 * s ^ 9
    + 23061669 * s ^ 8
    + 2557587 * s ^ 7
    - 1932431 * s ^ 6
    - 206142 * s ^ 5
    + 3049 * s ^ 4
    + 92 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient14 (s : ℚ) : ℚ :=
  s ^ 47
    - 35 * s ^ 46
    + 619 * s ^ 45
    - 7995 * s ^ 44
    + 88478 * s ^ 43
    - 855264 * s ^ 42
    + 6906251 * s ^ 41
    - 44893490 * s ^ 40
    + 230499226 * s ^ 39
    - 918893435 * s ^ 38
    + 2731188126 * s ^ 37
    - 5237100898 * s ^ 36
    + 1025472775 * s ^ 35
    + 39176315652 * s ^ 34
    - 188920874336 * s ^ 33
    + 577724420023 * s ^ 32
    - 1357609517547 * s ^ 31
    + 2605761885916 * s ^ 30
    - 4200019507654 * s ^ 29
    + 5728843466684 * s ^ 28
    - 6421190179702 * s ^ 27
    + 5049924506892 * s ^ 26
    - 27513921997 * s ^ 25
    - 9818328894570 * s ^ 24
    + 23832734407578 * s ^ 23
    - 38660273208453 * s ^ 22
    + 49229254491207 * s ^ 21
    - 51429255043919 * s ^ 20
    + 44633828048105 * s ^ 19
    - 32055680934608 * s ^ 18
    + 18663033079011 * s ^ 17
    - 8377356520611 * s ^ 16
    + 2507732407223 * s ^ 15
    - 132916747537 * s ^ 14
    - 388985590791 * s ^ 13
    + 276638877935 * s ^ 12
    - 103968382351 * s ^ 11
    + 20812772437 * s ^ 10
    - 922927965 * s ^ 9
    - 319098184 * s ^ 8
    - 2048098 * s ^ 7
    + 5169417 * s ^ 6
    + 1151011 * s ^ 5
    - 3937 * s ^ 4
    - 1186 * s ^ 3
    - 4 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient15 (s : ℚ) : ℚ :=
  -s ^ 47
    + 43 * s ^ 46
    - 967 * s ^ 45
    + 14231 * s ^ 44
    - 145433 * s ^ 43
    + 1033878 * s ^ 42
    - 4701518 * s ^ 41
    + 7008518 * s ^ 40
    + 88277039 * s ^ 39
    - 950495474 * s ^ 38
    + 5634055930 * s ^ 37
    - 24398872671 * s ^ 36
    + 83285264739 * s ^ 35
    - 231154512574 * s ^ 34
    + 528436505155 * s ^ 33
    - 995352657291 * s ^ 32
    + 1517026315971 * s ^ 31
    - 1738369428373 * s ^ 30
    + 966149132101 * s ^ 29
    + 1999022420362 * s ^ 28
    - 9142761028862 * s ^ 27
    + 23209774573318 * s ^ 26
    - 46456874784418 * s ^ 25
    + 77984245295063 * s ^ 24
    - 111504390312209 * s ^ 23
    + 136390556419240 * s ^ 22
    - 142646636528493 * s ^ 21
    + 126825886283083 * s ^ 20
    - 94507084116296 * s ^ 19
    + 57238383757783 * s ^ 18
    - 26167159224294 * s ^ 17
    + 6907000922018 * s ^ 16
    + 1366706152698 * s ^ 15
    - 2982315518288 * s ^ 14
    + 2073206594235 * s ^ 13
    - 921236851031 * s ^ 12
    + 256732154979 * s ^ 11
    - 30318790582 * s ^ 10
    - 4767815650 * s ^ 9
    + 1633875174 * s ^ 8
    + 17483300 * s ^ 7
    - 13231047 * s ^ 6
    - 4457223 * s ^ 5
    - 74526 * s ^ 4
    + 8257 * s ^ 3
    + 106 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient16 (s : ℚ) : ℚ :=
  11 * s ^ 46
    - 558 * s ^ 45
    + 13714 * s ^ 44
    - 214431 * s ^ 43
    + 2379350 * s ^ 42
    - 19866276 * s ^ 41
    + 129272595 * s ^ 40
    - 669566451 * s ^ 39
    + 2789194703 * s ^ 38
    - 9333788447 * s ^ 37
    + 24592301147 * s ^ 36
    - 47565539745 * s ^ 35
    + 48591508385 * s ^ 34
    + 80113712044 * s ^ 33
    - 598826534428 * s ^ 32
    + 2017795815249 * s ^ 31
    - 5268749724434 * s ^ 30
    + 12075505479196 * s ^ 29
    - 25496055292878 * s ^ 28
    + 49962162855930 * s ^ 27
    - 89488902025246 * s ^ 26
    + 143555082654516 * s ^ 25
    - 203000860953146 * s ^ 24
    + 250397037091815 * s ^ 23
    - 267068238864251 * s ^ 22
    + 243369160944576 * s ^ 21
    - 185261542514978 * s ^ 20
    + 112089103951113 * s ^ 19
    - 46538965085446 * s ^ 18
    + 3527492544682 * s ^ 17
    + 14891487660783 * s ^ 16
    - 16441753325681 * s ^ 15
    + 11092254094611 * s ^ 14
    - 5428052983764 * s ^ 13
    + 1858402443063 * s ^ 12
    - 340538854866 * s ^ 11
    - 26202985779 * s ^ 10
    + 29320638758 * s ^ 9
    - 4490511181 * s ^ 8
    - 314401466 * s ^ 7
    + 44960860 * s ^ 6
    + 12959674 * s ^ 5
    + 590255 * s ^ 4
    - 32377 * s ^ 3
    - 1198 * s ^ 2
    - 3 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient17 (s : ℚ) : ℚ :=
  2 * s ^ 47
    - 94 * s ^ 46
    + 2115 * s ^ 45
    - 29899 * s ^ 44
    + 292845 * s ^ 43
    - 2054346 * s ^ 42
    + 10063138 * s ^ 41
    - 28299682 * s ^ 40
    - 29914106 * s ^ 39
    + 900661540 * s ^ 38
    - 6245964429 * s ^ 37
    + 29505508739 * s ^ 36
    - 109860598732 * s ^ 35
    + 342732400538 * s ^ 34
    - 935053917025 * s ^ 33
    + 2322240554426 * s ^ 32
    - 5445371759179 * s ^ 31
    + 12312048548650 * s ^ 30
    - 26722069992936 * s ^ 29
    + 54343559685682 * s ^ 28
    - 100666513804257 * s ^ 27
    + 166149091667673 * s ^ 26
    - 240844544945956 * s ^ 25
    + 303586808297880 * s ^ 24
    - 329265584516044 * s ^ 23
    + 301630783543705 * s ^ 22
    - 223839111275694 * s ^ 21
    + 119291680628784 * s ^ 20
    - 20994493467276 * s ^ 19
    - 44613963401614 * s ^ 18
    + 69166334054955 * s ^ 17
    - 62344413534048 * s ^ 16
    + 41841442966635 * s ^ 15
    - 21881882582712 * s ^ 14
    + 8560463358861 * s ^ 13
    - 2015268743107 * s ^ 12
    - 73119824620 * s ^ 11
    + 252437731853 * s ^ 10
    - 79070793967 * s ^ 9
    + 4815526631 * s ^ 8
    + 1949641661 * s ^ 7
    - 139991777 * s ^ 6
    - 33554387 * s ^ 5
    - 2237192 * s ^ 4
    + 59129 * s ^ 3
    + 7570 * s ^ 2
    + 67 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient18 (s : ℚ) : ℚ :=
  -14 * s ^ 46
    + 658 * s ^ 45
    - 15007 * s ^ 44
    + 220265 * s ^ 43
    - 2330547 * s ^ 42
    + 18895638 * s ^ 41
    - 121982817 * s ^ 40
    + 644256739 * s ^ 39
    - 2846755633 * s ^ 38
    + 10765259345 * s ^ 37
    - 35839410420 * s ^ 36
    + 109089337286 * s ^ 35
    - 317110147042 * s ^ 34
    + 908224317925 * s ^ 33
    - 2559546671133 * s ^ 32
    + 6886787507752 * s ^ 31
    - 17056603540991 * s ^ 30
    + 37825121716205 * s ^ 29
    - 73839706971736 * s ^ 28
    + 125607073974630 * s ^ 27
    - 184785645975971 * s ^ 26
    + 232880434496975 * s ^ 25
    - 246756463023148 * s ^ 24
    + 209770129682436 * s ^ 23
    - 122554436026381 * s ^ 22
    + 6625947065830 * s ^ 21
    + 102867499841705 * s ^ 20
    - 173041817619163 * s ^ 19
    + 189095784215467 * s ^ 18
    - 159788724086807 * s ^ 17
    + 109012169167370 * s ^ 16
    - 60211265977104 * s ^ 15
    + 25720366846849 * s ^ 14
    - 6907058052321 * s ^ 13
    - 320507896426 * s ^ 12
    + 1382609286174 * s ^ 11
    - 640759320464 * s ^ 10
    + 109918066913 * s ^ 9
    + 12252553713 * s ^ 8
    - 6687700994 * s ^ 7
    + 207456057 * s ^ 6
    + 94233413 * s ^ 5
    + 5086614 * s ^ 4
    + 47869 * s ^ 3
    - 29052 * s ^ 2
    - 656 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient19 (s : ℚ) : ℚ :=
  -s ^ 47
    + 47 * s ^ 46
    - 1055 * s ^ 45
    + 15013 * s ^ 44
    - 151680 * s ^ 43
    + 1157174 * s ^ 42
    - 6962368 * s ^ 41
    + 34587343 * s ^ 40
    - 152237691 * s ^ 39
    + 659154407 * s ^ 38
    - 3045103538 * s ^ 37
    + 14634357781 * s ^ 36
    - 66984758654 * s ^ 35
    + 273756723470 * s ^ 34
    - 971925730998 * s ^ 33
    + 2974184867112 * s ^ 32
    - 7835562811411 * s ^ 31
    + 17766964165687 * s ^ 30
    - 34602397248271 * s ^ 29
    + 57543296553720 * s ^ 28
    - 80594030134526 * s ^ 27
    + 91921392739111 * s ^ 26
    - 77104351912754 * s ^ 25
    + 25824247675678 * s ^ 24
    + 61012909188761 * s ^ 23
    - 167433064431417 * s ^ 22
    + 264971725702023 * s ^ 21
    - 323066294526692 * s ^ 20
    + 323761411476595 * s ^ 19
    - 271609313136624 * s ^ 18
    + 190717782489518 * s ^ 17
    - 110255829403495 * s ^ 16
    + 49495175995600 * s ^ 15
    - 13336089251282 * s ^ 14
    - 2451017345204 * s ^ 13
    + 5376206225825 * s ^ 12
    - 3119155802614 * s ^ 11
    + 850164639813 * s ^ 10
    - 3914330085 * s ^ 9
    - 65497917800 * s ^ 8
    + 13929173770 * s ^ 7
    + 436006331 * s ^ 6
    - 271390256 * s ^ 5
    - 7877377 * s ^ 4
    - 497907 * s ^ 3
    + 65133 * s ^ 2
    + 3770 * s
    + 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient20 (s : ℚ) : ℚ :=
  2 * s ^ 46
    - 82 * s ^ 45
    + 1540 * s ^ 44
    - 16652 * s ^ 43
    + 96650 * s ^ 42
    + 55534 * s ^ 41
    - 7592052 * s ^ 40
    + 92005878 * s ^ 39
    - 718985527 * s ^ 38
    + 4289945353 * s ^ 37
    - 20737534875 * s ^ 36
    + 83550200100 * s ^ 35
    - 284723545020 * s ^ 34
    + 826043955049 * s ^ 33
    - 2039420363131 * s ^ 32
    + 4247542381580 * s ^ 31
    - 7288981950846 * s ^ 30
    + 9679634824394 * s ^ 29
    - 7806826519439 * s ^ 28
    - 4042334831473 * s ^ 27
    + 32210284675399 * s ^ 26
    - 80981626343894 * s ^ 25
    + 149489571937820 * s ^ 24
    - 229013476649796 * s ^ 23
    + 302137126139891 * s ^ 22
    - 346588334165195 * s ^ 21
    + 344931755622571 * s ^ 20
    - 295229708392804 * s ^ 19
    + 213915154552862 * s ^ 18
    - 127044133670654 * s ^ 17
    + 56239414271066 * s ^ 16
    - 10586868728303 * s ^ 15
    - 11197650909457 * s ^ 14
    + 15257943653355 * s ^ 13
    - 9995471929232 * s ^ 12
    + 3616874557791 * s ^ 11
    - 313926768043 * s ^ 10
    - 330445542175 * s ^ 9
    + 143964870144 * s ^ 8
    - 15186942703 * s ^ 7
    - 3323578005 * s ^ 6
    + 645573976 * s ^ 5
    + 14879474 * s ^ 4
    + 824404 * s ^ 3
    - 51176 * s ^ 2
    - 14147 * s
    - 152

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient21 (s : ℚ) : ℚ :=
  s ^ 46
    - 53 * s ^ 45
    + 1359 * s ^ 44
    - 22462 * s ^ 43
    + 268758 * s ^ 42
    - 2476669 * s ^ 41
    + 18245646 * s ^ 40
    - 109988427 * s ^ 39
    + 549980779 * s ^ 38
    - 2292915108 * s ^ 37
    + 7929161439 * s ^ 36
    - 22221400619 * s ^ 35
    + 47005329822 * s ^ 34
    - 55115467190 * s ^ 33
    - 84896597861 * s ^ 32
    + 758899683854 * s ^ 31
    - 2810411011834 * s ^ 30
    + 7686679127348 * s ^ 29
    - 17377065629350 * s ^ 28
    + 34095538818423 * s ^ 27
    - 59761582327216 * s ^ 26
    + 95110076138316 * s ^ 25
    - 137974761393369 * s ^ 24
    + 181121254476807 * s ^ 23
    - 212062665273727 * s ^ 22
    + 217597161705160 * s ^ 21
    - 191737482887945 * s ^ 20
    + 140821358332687 * s ^ 19
    - 80612850644118 * s ^ 18
    + 27316309276336 * s ^ 17
    + 9766186757376 * s ^ 16
    - 28561539928620 * s ^ 15
    + 30892339711243 * s ^ 14
    - 21774583291963 * s ^ 13
    + 9510128541004 * s ^ 12
    - 1379965331882 * s ^ 11
    - 1099342411989 * s ^ 10
    + 758684635699 * s ^ 9
    - 176876420080 * s ^ 8
    - 4723134575 * s ^ 7
    + 9501710012 * s ^ 6
    - 1081237846 * s ^ 5
    - 53251032 * s ^ 4
    + 1275932 * s ^ 3
    - 170645 * s ^ 2
    + 35780 * s
    + 799

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient22 (s : ℚ) : ℚ :=
  -s ^ 45
    + 51 * s ^ 44
    - 1280 * s ^ 43
    + 21039 * s ^ 42
    - 254263 * s ^ 41
    + 2404782 * s ^ 40
    - 18497167 * s ^ 39
    + 118700020 * s ^ 38
    - 646778181 * s ^ 37
    + 3029615972 * s ^ 36
    - 12307151903 * s ^ 35
    + 43637637392 * s ^ 34
    - 135776862613 * s ^ 33
    + 372899028627 * s ^ 32
    - 911615333948 * s ^ 31
    + 2010293237976 * s ^ 30
    - 4076332378808 * s ^ 29
    + 7766099426623 * s ^ 28
    - 14095403851317 * s ^ 27
    + 24266141958534 * s ^ 26
    - 38740130985230 * s ^ 25
    + 55625237738486 * s ^ 24
    - 69741262353177 * s ^ 23
    + 74249226746677 * s ^ 22
    - 64740906631467 * s ^ 21
    + 42624048010618 * s ^ 20
    - 14495359073686 * s ^ 19
    - 12032811667355 * s ^ 18
    + 31969070511860 * s ^ 17
    - 42859688755458 * s ^ 16
    + 42935484850580 * s ^ 15
    - 32264724719552 * s ^ 14
    + 16009197295687 * s ^ 13
    - 2708577620145 * s ^ 12
    - 2803774709491 * s ^ 11
    + 2529677211624 * s ^ 10
    - 896980220688 * s ^ 9
    + 76865306487 * s ^ 8
    + 50713212545 * s ^ 7
    - 16599934518 * s ^ 6
    + 1009941168 * s ^ 5
    + 173099187 * s ^ 4
    - 8789402 * s ^ 3
    + 674785 * s ^ 2
    - 58146 * s
    - 2924

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient23 (s : ℚ) : ℚ :=
  7 * s ^ 42
    - 324 * s ^ 41
    + 7357 * s ^ 40
    - 108590 * s ^ 39
    + 1163642 * s ^ 38
    - 9573067 * s ^ 37
    + 62280356 * s ^ 36
    - 324372909 * s ^ 35
    + 1345802145 * s ^ 34
    - 4300963336 * s ^ 33
    + 9395932061 * s ^ 32
    - 5765311008 * s ^ 31
    - 60888709066 * s ^ 30
    + 352390649693 * s ^ 29
    - 1198634377380 * s ^ 28
    + 3029288650228 * s ^ 27
    - 6020737456758 * s ^ 26
    + 9526627453305 * s ^ 25
    - 11813808418189 * s ^ 24
    + 10744447710589 * s ^ 23
    - 5240486787175 * s ^ 22
    - 3769127967810 * s ^ 21
    + 14060862013241 * s ^ 20
    - 23832971182541 * s ^ 19
    + 32368172084818 * s ^ 18
    - 38610489344439 * s ^ 17
    + 39566943430935 * s ^ 16
    - 31986948663408 * s ^ 15
    + 17092047908282 * s ^ 14
    - 2062872056977 * s ^ 13
    - 5819806657711 * s ^ 12
    + 5827112440030 * s ^ 11
    - 2685376399917 * s ^ 10
    + 468732242150 * s ^ 9
    + 145602458916 * s ^ 8
    - 98597997309 * s ^ 7
    + 18239851168 * s ^ 6
    + 243992062 * s ^ 5
    - 388514870 * s ^ 4
    + 19811008 * s ^ 3
    - 1069240 * s ^ 2
    + 42141 * s
    + 7890

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient24 (s : ℚ) : ℚ :=
  s ^ 42
    - 52 * s ^ 41
    + 1337 * s ^ 40
    - 22598 * s ^ 39
    + 281269 * s ^ 38
    - 2735917 * s ^ 37
    + 21539829 * s ^ 36
    - 140272411 * s ^ 35
    + 765755347 * s ^ 34
    - 3530577125 * s ^ 33
    + 13787636561 * s ^ 32
    - 45545577939 * s ^ 31
    + 126494426134 * s ^ 30
    - 291532448497 * s ^ 29
    + 542963348395 * s ^ 28
    - 768407303304 * s ^ 27
    + 670853322440 * s ^ 26
    + 158725947887 * s ^ 25
    - 1951831420103 * s ^ 24
    + 4457187289036 * s ^ 23
    - 7052091279666 * s ^ 22
    + 9404784123482 * s ^ 21
    - 12051517055899 * s ^ 20
    + 15921896449167 * s ^ 19
    - 20716846789711 * s ^ 18
    + 23641316102589 * s ^ 17
    - 20705688189585 * s ^ 16
    + 10770310369846 * s ^ 15
    + 1659857386104 * s ^ 14
    - 9474247386265 * s ^ 13
    + 9589557386923 * s ^ 12
    - 5202126590362 * s ^ 11
    + 1255437192362 * s ^ 10
    + 292150576207 * s ^ 9
    - 338163794089 * s ^ 8
    + 107158461201 * s ^ 7
    - 9651946357 * s ^ 6
    - 2518938944 * s ^ 5
    + 597684473 * s ^ 4
    - 23458910 * s ^ 3
    + 461087 * s ^ 2
    + 62269 * s
    - 16212

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient25 (s : ℚ) : ℚ :=
  2 * s ^ 40
    - 114 * s ^ 39
    + 3104 * s ^ 38
    - 54078 * s ^ 37
    + 678804 * s ^ 36
    - 6536868 * s ^ 35
    + 50126772 * s ^ 34
    - 313296506 * s ^ 33
    + 1619685461 * s ^ 32
    - 6988797873 * s ^ 31
    + 25287492523 * s ^ 30
    - 76799960537 * s ^ 29
    + 195227550244 * s ^ 28
    - 412308503708 * s ^ 27
    + 713503614152 * s ^ 26
    - 988329971035 * s ^ 25
    + 1057996087495 * s ^ 24
    - 861678517984 * s ^ 23
    + 725385672018 * s ^ 22
    - 1404457681430 * s ^ 21
    + 3582763428949 * s ^ 20
    - 6936753728565 * s ^ 19
    + 9524207475399 * s ^ 18
    - 8548773198877 * s ^ 17
    + 2724919665776 * s ^ 16
    + 5579148649659 * s ^ 15
    - 11356840017787 * s ^ 14
    + 11256635923110 * s ^ 13
    - 6669893143169 * s ^ 12
    + 1822645103496 * s ^ 11
    + 560870269082 * s ^ 10
    - 786706136365 * s ^ 9
    + 343123806287 * s ^ 8
    - 62127766693 * s ^ 7
    - 5193363800 * s ^ 6
    + 4395454545 * s ^ 5
    - 619409849 * s ^ 4
    + 7954896 * s ^ 3
    + 1673471 * s ^ 2
    - 255825 * s
    + 25818

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient26 (s : ℚ) : ℚ :=
  -s ^ 39
    + 53 * s ^ 38
    - 1397 * s ^ 37
    + 24253 * s ^ 36
    - 309117 * s ^ 35
    + 3055253 * s ^ 34
    - 24169911 * s ^ 33
    + 156119042 * s ^ 32
    - 834245695 * s ^ 31
    + 3719869052 * s ^ 30
    - 13910591890 * s ^ 29
    + 43696924338 * s ^ 28
    - 115017785567 * s ^ 27
    + 251476547603 * s ^ 26
    - 447293055819 * s ^ 25
    + 614585597279 * s ^ 24
    - 549589895265 * s ^ 23
    - 4702297100 * s ^ 22
    + 1146903076513 * s ^ 21
    - 2523464807289 * s ^ 20
    + 3190060065722 * s ^ 19
    - 1961004555336 * s ^ 18
    - 1634063514221 * s ^ 17
    + 6372073171906 * s ^ 16
    - 9582032644642 * s ^ 15
    + 9127185326564 * s ^ 14
    - 5456369286868 * s ^ 13
    + 1263068651816 * s ^ 12
    + 1079519498939 * s ^ 11
    - 1328572777175 * s ^ 10
    + 690013469197 * s ^ 9
    - 175765513110 * s ^ 8
    - 1352276556 * s ^ 7
    + 15515682854 * s ^ 6
    - 4379032168 * s ^ 5
    + 380670244 * s ^ 4
    + 23038832 * s ^ 3
    - 4447434 * s ^ 2
    + 449210 * s
    - 32109

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient27 (s : ℚ) : ℚ :=
  -3 * s ^ 37
    + 165 * s ^ 36
    - 4312 * s ^ 35
    + 71482 * s ^ 34
    - 845618 * s ^ 33
    + 7606746 * s ^ 32
    - 54106244 * s ^ 31
    + 312304169 * s ^ 30
    - 1489374838 * s ^ 29
    + 5944169601 * s ^ 28
    - 20036439126 * s ^ 27
    + 57401610695 * s ^ 26
    - 140248769059 * s ^ 25
    + 292081327688 * s ^ 24
    - 514183875263 * s ^ 23
    + 744796921538 * s ^ 22
    - 816637911436 * s ^ 21
    + 455575119489 * s ^ 20
    + 609203752362 * s ^ 19
    - 2381249287370 * s ^ 18
    + 4309753170598 * s ^ 17
    - 5349817130294 * s ^ 16
    + 4638663570120 * s ^ 15
    - 2362245208765 * s ^ 14
    - 175883597991 * s ^ 13
    + 1607573440738 * s ^ 12
    - 1613982814872 * s ^ 11
    + 899098830915 * s ^ 10
    - 269253148571 * s ^ 9
    + 1614635926 * s ^ 8
    + 35440365143 * s ^ 7
    - 14877433149 * s ^ 6
    + 2572265655 * s ^ 5
    - 36335079 * s ^ 4
    - 48376166 * s ^ 3
    + 5983975 * s ^ 2
    - 520011 * s
    + 31162

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient28 (s : ℚ) : ℚ :=
  s ^ 36
    - 51 * s ^ 35
    + 1257 * s ^ 34
    - 19916 * s ^ 33
    + 227531 * s ^ 32
    - 1993045 * s ^ 31
    + 13902209 * s ^ 30
    - 79240114 * s ^ 29
    + 376231338 * s ^ 28
    - 1511884536 * s ^ 27
    + 5218650035 * s ^ 26
    - 15710118096 * s ^ 25
    + 41913307167 * s ^ 24
    - 100615775503 * s ^ 23
    + 219493221612 * s ^ 22
    - 434750807781 * s ^ 21
    + 770394296061 * s ^ 20
    - 1187145891002 * s ^ 19
    + 1523253791696 * s ^ 18
    - 1510174363783 * s ^ 17
    + 943246371847 * s ^ 16
    + 71691155209 * s ^ 15
    - 1066023444982 * s ^ 14
    + 1521212224055 * s ^ 13
    - 1297162568884 * s ^ 12
    + 714085949885 * s ^ 11
    - 207558505295 * s ^ 10
    - 27456554921 * s ^ 9
    + 60581854042 * s ^ 8
    - 30009684721 * s ^ 7
    + 7415094155 * s ^ 6
    - 563446291 * s ^ 5
    - 177490357 * s ^ 4
    + 50379906 * s ^ 3
    - 5273981 * s ^ 2
    + 428641 * s
    - 23388

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient29 (s : ℚ) : ℚ :=
  s ^ 33
    - 67 * s ^ 32
    + 1956 * s ^ 31
    - 34438 * s ^ 30
    + 418438 * s ^ 29
    - 3773150 * s ^ 28
    + 26382577 * s ^ 27
    - 147045770 * s ^ 26
    + 664300789 * s ^ 25
    - 2452042197 * s ^ 24
    + 7388778166 * s ^ 23
    - 17937811086 * s ^ 22
    + 33774392889 * s ^ 21
    - 43907163536 * s ^ 20
    + 18580104200 * s ^ 19
    + 84991477813 * s ^ 18
    - 289462918396 * s ^ 17
    + 550570530355 * s ^ 16
    - 748479627010 * s ^ 15
    + 758616865966 * s ^ 14
    - 558952641581 * s ^ 13
    + 262163187738 * s ^ 12
    - 24220633250 * s ^ 11
    - 77752013891 * s ^ 10
    + 74501256942 * s ^ 9
    - 37487915183 * s ^ 8
    + 10955153255 * s ^ 7
    - 1198284812 * s ^ 6
    - 386169528 * s ^ 5
    + 185359131 * s ^ 4
    - 33070336 * s ^ 3
    + 3174784 * s ^ 2
    - 254088 * s
    + 13319

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient30 (s : ℚ) : ℚ :=
  -s ^ 32
    + 50 * s ^ 31
    - 1201 * s ^ 30
    + 18487 * s ^ 29
    - 205130 * s ^ 28
    + 1748373 * s ^ 27
    - 11900252 * s ^ 26
    + 66330643 * s ^ 25
    - 307806508 * s ^ 24
    + 1201797684 * s ^ 23
    - 3972156563 * s ^ 22
    + 11141041786 * s ^ 21
    - 26491741369 * s ^ 20
    + 53152943597 * s ^ 19
    - 89110872937 * s ^ 18
    + 122584559765 * s ^ 17
    - 133508753227 * s ^ 16
    + 105595872697 * s ^ 15
    - 42555168769 * s ^ 14
    - 28134337741 * s ^ 13
    + 72964857272 * s ^ 12
    - 77490821294 * s ^ 11
    + 53944606997 * s ^ 10
    - 25640942776 * s ^ 9
    + 7414177590 * s ^ 8
    - 397459290 * s ^ 7
    - 741856296 * s ^ 6
    + 378970214 * s ^ 5
    - 95567291 * s ^ 4
    + 13839049 * s ^ 3
    - 1273741 * s ^ 2
    + 105748 * s
    - 5566

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient31 (s : ℚ) : ℚ :=
  2 * s ^ 29
    - 94 * s ^ 28
    + 2105 * s ^ 27
    - 29911 * s ^ 26
    + 302962 * s ^ 25
    - 2328964 * s ^ 24
    + 14121708 * s ^ 23
    - 69270426 * s ^ 22
    + 279612845 * s ^ 21
    - 939459241 * s ^ 20
    + 2646389117 * s ^ 19
    - 6274377013 * s ^ 18
    + 12532788201 * s ^ 17
    - 21051467659 * s ^ 16
    + 29588766012 * s ^ 15
    - 34489852532 * s ^ 14
    + 32837995861 * s ^ 13
    - 24855034454 * s ^ 12
    + 14135907955 * s ^ 11
    - 5123515197 * s ^ 10
    + 152143656 * s ^ 9
    + 1282507227 * s ^ 8
    - 1006708766 * s ^ 7
    + 452685733 * s ^ 6
    - 134544839 * s ^ 5
    + 26444493 * s ^ 4
    - 3363057 * s ^ 3
    + 311772 * s ^ 2
    - 29106 * s
    + 1610

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient32 (s : ℚ) : ℚ :=
  -s ^ 26
    + 44 * s ^ 25
    - 915 * s ^ 24
    + 11962 * s ^ 23
    - 110313 * s ^ 22
    + 763297 * s ^ 21
    - 4115249 * s ^ 20
    + 17721635 * s ^ 19
    - 61995427 * s ^ 18
    + 178247203 * s ^ 17
    - 424534483 * s ^ 16
    + 841772302 * s ^ 15
    - 1393182704 * s ^ 14
    + 1925768752 * s ^ 13
    - 2220255471 * s ^ 12
    + 2128010897 * s ^ 11
    - 1686178160 * s ^ 10
    + 1095168000 * s ^ 9
    - 575551021 * s ^ 8
    + 239952142 * s ^ 7
    - 76994435 * s ^ 6
    + 18181542 * s ^ 5
    - 2988215 * s ^ 4
    + 341020 * s ^ 3
    - 36790 * s ^ 2
    + 4676 * s
    - 288

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient33 (s : ℚ) : ℚ :=
  s ^ 17
    - 29 * s ^ 16
    + 385 * s ^ 15
    - 3100 * s ^ 14
    + 16907 * s ^ 13
    - 66053 * s ^ 12
    + 190629 * s ^ 11
    - 412985 * s ^ 10
    + 675509 * s ^ 9
    - 831665 * s ^ 8
    + 761146 * s ^ 7
    - 504983 * s ^ 6
    + 231753 * s ^ 5
    - 66747 * s ^ 4
    + 8950 * s ^ 3
    + 578 * s ^ 2
    - 320 * s
    + 24

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
    termThreeCoefficient33 s * r ^ 33

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_0 (s : ℚ) :
    termThreeCoefficient0 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient0,
    t3Step2Coefficient0,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_1 (s : ℚ) :
    termThreeCoefficient1 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient1,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_2 (s : ℚ) :
    termThreeCoefficient2 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient2,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_3 (s : ℚ) :
    termThreeCoefficient3 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient3,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_4 (s : ℚ) :
    termThreeCoefficient4 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient4,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_5 (s : ℚ) :
    termThreeCoefficient5 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient5,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_6 (s : ℚ) :
    termThreeCoefficient6 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient6,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_7 (s : ℚ) :
    termThreeCoefficient7 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient7,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    t3Step2Coefficient7,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_8 (s : ℚ) :
    termThreeCoefficient8 s =
    t3Step2Coefficient0 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient8,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    t3Step2Coefficient7,
    t3Step2Coefficient8,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_9 (s : ℚ) :
    termThreeCoefficient9 s =
    t3Step2Coefficient1 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient9,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    t3Step2Coefficient7,
    t3Step2Coefficient8,
    t3Step2Coefficient9,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_10 (s : ℚ) :
    termThreeCoefficient10 s =
    t3Step2Coefficient2 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient10,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    t3Step2Coefficient7,
    t3Step2Coefficient8,
    t3Step2Coefficient9,
    t3Step2Coefficient10,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_11 (s : ℚ) :
    termThreeCoefficient11 s =
    t3Step2Coefficient3 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient11,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    t3Step2Coefficient7,
    t3Step2Coefficient8,
    t3Step2Coefficient9,
    t3Step2Coefficient10,
    t3Step2Coefficient11,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_12 (s : ℚ) :
    termThreeCoefficient12 s =
    t3Step2Coefficient4 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient12,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    t3Step2Coefficient7,
    t3Step2Coefficient8,
    t3Step2Coefficient9,
    t3Step2Coefficient10,
    t3Step2Coefficient11,
    t3Step2Coefficient12,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_13 (s : ℚ) :
    termThreeCoefficient13 s =
    t3Step2Coefficient5 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient13,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    t3Step2Coefficient7,
    t3Step2Coefficient8,
    t3Step2Coefficient9,
    t3Step2Coefficient10,
    t3Step2Coefficient11,
    t3Step2Coefficient12,
    t3Step2Coefficient13,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_14 (s : ℚ) :
    termThreeCoefficient14 s =
    t3Step2Coefficient6 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient14,
    t3Step2Coefficient6,
    t3Step2Coefficient7,
    t3Step2Coefficient8,
    t3Step2Coefficient9,
    t3Step2Coefficient10,
    t3Step2Coefficient11,
    t3Step2Coefficient12,
    t3Step2Coefficient13,
    t3Step2Coefficient14,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_15 (s : ℚ) :
    termThreeCoefficient15 s =
    t3Step2Coefficient7 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient15,
    t3Step2Coefficient7,
    t3Step2Coefficient8,
    t3Step2Coefficient9,
    t3Step2Coefficient10,
    t3Step2Coefficient11,
    t3Step2Coefficient12,
    t3Step2Coefficient13,
    t3Step2Coefficient14,
    t3Step2Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_16 (s : ℚ) :
    termThreeCoefficient16 s =
    t3Step2Coefficient8 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient16,
    t3Step2Coefficient8,
    t3Step2Coefficient9,
    t3Step2Coefficient10,
    t3Step2Coefficient11,
    t3Step2Coefficient12,
    t3Step2Coefficient13,
    t3Step2Coefficient14,
    t3Step2Coefficient15,
    t3Step2Coefficient16,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_17 (s : ℚ) :
    termThreeCoefficient17 s =
    t3Step2Coefficient9 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient17,
    t3Step2Coefficient9,
    t3Step2Coefficient10,
    t3Step2Coefficient11,
    t3Step2Coefficient12,
    t3Step2Coefficient13,
    t3Step2Coefficient14,
    t3Step2Coefficient15,
    t3Step2Coefficient16,
    t3Step2Coefficient17,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_18 (s : ℚ) :
    termThreeCoefficient18 s =
    t3Step2Coefficient10 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient18,
    t3Step2Coefficient10,
    t3Step2Coefficient11,
    t3Step2Coefficient12,
    t3Step2Coefficient13,
    t3Step2Coefficient14,
    t3Step2Coefficient15,
    t3Step2Coefficient16,
    t3Step2Coefficient17,
    t3Step2Coefficient18,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_19 (s : ℚ) :
    termThreeCoefficient19 s =
    t3Step2Coefficient11 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient19,
    t3Step2Coefficient11,
    t3Step2Coefficient12,
    t3Step2Coefficient13,
    t3Step2Coefficient14,
    t3Step2Coefficient15,
    t3Step2Coefficient16,
    t3Step2Coefficient17,
    t3Step2Coefficient18,
    t3Step2Coefficient19,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_20 (s : ℚ) :
    termThreeCoefficient20 s =
    t3Step2Coefficient12 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient20,
    t3Step2Coefficient12,
    t3Step2Coefficient13,
    t3Step2Coefficient14,
    t3Step2Coefficient15,
    t3Step2Coefficient16,
    t3Step2Coefficient17,
    t3Step2Coefficient18,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_21 (s : ℚ) :
    termThreeCoefficient21 s =
    t3Step2Coefficient13 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient21,
    t3Step2Coefficient13,
    t3Step2Coefficient14,
    t3Step2Coefficient15,
    t3Step2Coefficient16,
    t3Step2Coefficient17,
    t3Step2Coefficient18,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_22 (s : ℚ) :
    termThreeCoefficient22 s =
    t3Step2Coefficient14 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient22,
    t3Step2Coefficient14,
    t3Step2Coefficient15,
    t3Step2Coefficient16,
    t3Step2Coefficient17,
    t3Step2Coefficient18,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_23 (s : ℚ) :
    termThreeCoefficient23 s =
    t3Step2Coefficient15 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient23,
    t3Step2Coefficient15,
    t3Step2Coefficient16,
    t3Step2Coefficient17,
    t3Step2Coefficient18,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_24 (s : ℚ) :
    termThreeCoefficient24 s =
    t3Step2Coefficient16 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient24,
    t3Step2Coefficient16,
    t3Step2Coefficient17,
    t3Step2Coefficient18,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_25 (s : ℚ) :
    termThreeCoefficient25 s =
    t3Step2Coefficient17 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient1 s
      + t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient25,
    t3Step2Coefficient17,
    t3Step2Coefficient18,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_26 (s : ℚ) :
    termThreeCoefficient26 s =
    t3Step2Coefficient18 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient2 s
      + t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient1 s
    := by
  simp only [termThreeCoefficient26,
    t3Step2Coefficient18,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_27 (s : ℚ) :
    termThreeCoefficient27 s =
    t3Step2Coefficient19 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient3 s
      + t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient2 s
    := by
  simp only [termThreeCoefficient27,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_28 (s : ℚ) :
    termThreeCoefficient28 s =
    t3Step2Coefficient20 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient4 s
      + t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient3 s
    := by
  simp only [termThreeCoefficient28,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_29 (s : ℚ) :
    termThreeCoefficient29 s =
    t3Step2Coefficient21 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient5 s
      + t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient4 s
    := by
  simp only [termThreeCoefficient29,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_30 (s : ℚ) :
    termThreeCoefficient30 s =
    t3Step2Coefficient22 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient6 s
      + t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient5 s
    := by
  simp only [termThreeCoefficient30,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_31 (s : ℚ) :
    termThreeCoefficient31 s =
    t3Step2Coefficient23 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient7 s
      + t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient6 s
    := by
  simp only [termThreeCoefficient31,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_32 (s : ℚ) :
    termThreeCoefficient32 s =
    t3Step2Coefficient24 s *
        rawUnitFourDenominatorCoefficient8 s
      + t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient7 s
    := by
  simp only [termThreeCoefficient32,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_33 (s : ℚ) :
    termThreeCoefficient33 s =
    t3Step2Coefficient25 s *
        rawUnitFourDenominatorCoefficient8 s
    := by
  simp only [termThreeCoefficient33,
    t3Step2Coefficient25,
    rawUnitFourDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termThree_eq_t3Step2_mul_rawUnitFourDenominator (r s : ℚ) :
    termThree r s = t3Step2 r s * rawUnitFourDenominator r s := by
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
  simp only [termThree, t3Step2, rawUnitFourDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient0 (s : ℚ) : ℚ :=
  s ^ 29
    - s ^ 28
    + s ^ 27
    - s ^ 26

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 35
    + 4 * s ^ 34
    - 10 * s ^ 33
    + 21 * s ^ 32
    - 38 * s ^ 31
    + 63 * s ^ 30
    - 80 * s ^ 29
    + 28 * s ^ 28
    + 11 * s ^ 27
    - 53 * s ^ 26
    + 89 * s ^ 25
    - 55 * s ^ 24
    + 34 * s ^ 23
    - 20 * s ^ 22
    + 10 * s ^ 21
    - 4 * s ^ 20
    + s ^ 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient2 (s : ℚ) : ℚ :=
  -3 * s ^ 36
    + 9 * s ^ 35
    + 31 * s ^ 34
    - 173 * s ^ 33
    + 488 * s ^ 32
    - 1138 * s ^ 31
    + 2367 * s ^ 30
    - 4513 * s ^ 29
    + 6951 * s ^ 28
    - 7537 * s ^ 27
    + 7148 * s ^ 26
    - 5459 * s ^ 25
    + 2826 * s ^ 24
    - 1547 * s ^ 23
    + 790 * s ^ 22
    - 305 * s ^ 21
    + 61 * s ^ 20
    + 24 * s ^ 19
    - 23 * s ^ 18
    + 3 * s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 40
    + 10 * s ^ 39
    - 56 * s ^ 38
    + 226 * s ^ 37
    - 762 * s ^ 36
    + 2333 * s ^ 35
    - 5973 * s ^ 34
    + 12252 * s ^ 33
    - 22350 * s ^ 32
    + 37664 * s ^ 31
    - 56220 * s ^ 30
    + 68081 * s ^ 29
    - 52838 * s ^ 28
    + 6918 * s ^ 27
    + 37688 * s ^ 26
    - 77552 * s ^ 25
    + 93724 * s ^ 24
    - 75635 * s ^ 23
    + 56696 * s ^ 22
    - 40924 * s ^ 21
    + 27020 * s ^ 20
    - 15812 * s ^ 19
    + 7897 * s ^ 18
    - 3437 * s ^ 17
    + 1490 * s ^ 16
    - 594 * s ^ 15
    + 199 * s ^ 14
    - 53 * s ^ 13
    + 10 * s ^ 12
    - s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient4 (s : ℚ) : ℚ :=
  -3 * s ^ 41
    + 32 * s ^ 40
    - 164 * s ^ 39
    + 582 * s ^ 38
    - 1655 * s ^ 37
    + 4047 * s ^ 36
    - 7549 * s ^ 35
    + 6419 * s ^ 34
    + 9573 * s ^ 33
    - 49352 * s ^ 32
    + 154339 * s ^ 31
    - 421818 * s ^ 30
    + 954247 * s ^ 29
    - 1709000 * s ^ 28
    + 2340203 * s ^ 27
    - 2535950 * s ^ 26
    + 2392583 * s ^ 25
    - 1883003 * s ^ 24
    + 1268172 * s ^ 23
    - 912966 * s ^ 22
    + 661894 * s ^ 21
    - 434665 * s ^ 20
    + 249326 * s ^ 19
    - 124136 * s ^ 18
    + 58404 * s ^ 17
    - 28323 * s ^ 16
    + 11690 * s ^ 15
    - 3553 * s ^ 14
    + 637 * s ^ 13
    + 35 * s ^ 12
    - 60 * s ^ 11
    + 15 * s ^ 10
    - s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 43
    + 11 * s ^ 42
    - 74 * s ^ 41
    + 453 * s ^ 40
    - 2309 * s ^ 39
    + 9271 * s ^ 38
    - 30948 * s ^ 37
    + 91728 * s ^ 36
    - 249601 * s ^ 35
    + 609346 * s ^ 34
    - 1320614 * s ^ 33
    + 2694329 * s ^ 32
    - 5326933 * s ^ 31
    + 9536404 * s ^ 30
    - 14404530 * s ^ 29
    + 17478056 * s ^ 28
    - 16487517 * s ^ 27
    + 12487395 * s ^ 26
    - 8216596 * s ^ 25
    + 4519803 * s ^ 24
    - 3524776 * s ^ 23
    + 4746673 * s ^ 22
    - 4724197 * s ^ 21
    + 3451395 * s ^ 20
    - 2061723 * s ^ 19
    + 1119911 * s ^ 18
    - 635849 * s ^ 17
    + 347523 * s ^ 16
    - 132566 * s ^ 15
    + 24362 * s ^ 14
    + 6322 * s ^ 13
    - 6900 * s ^ 12
    + 2589 * s ^ 11
    - 454 * s ^ 10
    + 15 * s ^ 9
    + 2 * s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient6 (s : ℚ) : ℚ :=
  -2 * s ^ 44
    + 28 * s ^ 43
    - 202 * s ^ 42
    + 1104 * s ^ 41
    - 4975 * s ^ 40
    + 18533 * s ^ 39
    - 60574 * s ^ 38
    + 186683 * s ^ 37
    - 547714 * s ^ 36
    + 1476288 * s ^ 35
    - 3587353 * s ^ 34
    + 8030522 * s ^ 33
    - 16485477 * s ^ 32
    + 28592292 * s ^ 31
    - 37485218 * s ^ 30
    + 31582211 * s ^ 29
    - 5452326 * s ^ 28
    - 27807520 * s ^ 27
    + 42576554 * s ^ 26
    - 30040711 * s ^ 25
    - 344082 * s ^ 24
    + 40273583 * s ^ 23
    - 63305728 * s ^ 22
    + 54655350 * s ^ 21
    - 35179322 * s ^ 20
    + 20357189 * s ^ 19
    - 12199417 * s ^ 18
    + 7550508 * s ^ 17
    - 3732856 * s ^ 16
    + 916507 * s ^ 15
    + 222520 * s ^ 14
    - 336855 * s ^ 13
    + 174446 * s ^ 12
    - 51149 * s ^ 11
    + 7199 * s ^ 10
    + 19 * s ^ 9
    - 53 * s ^ 8
    - 2 * s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 45
    + 12 * s ^ 44
    - 49 * s ^ 43
    + 79 * s ^ 42
    - 186 * s ^ 41
    + 2532 * s ^ 40
    - 23275 * s ^ 39
    + 142825 * s ^ 38
    - 627278 * s ^ 37
    + 2086333 * s ^ 36
    - 5539980 * s ^ 35
    + 12119943 * s ^ 34
    - 21001670 * s ^ 33
    + 21768597 * s ^ 32
    + 14655224 * s ^ 31
    - 118729067 * s ^ 30
    + 268278205 * s ^ 29
    - 357570074 * s ^ 28
    + 254089715 * s ^ 27
    + 64477539 * s ^ 26
    - 455797800 * s ^ 25
    + 763121065 * s ^ 24
    - 884974190 * s ^ 23
    + 740739905 * s ^ 22
    - 455571898 * s ^ 21
    + 247644339 * s ^ 20
    - 150839453 * s ^ 19
    + 104109412 * s ^ 18
    - 62487145 * s ^ 17
    + 20866502 * s ^ 16
    + 4643816 * s ^ 15
    - 10124876 * s ^ 14
    + 6639815 * s ^ 13
    - 2690193 * s ^ 12
    + 669058 * s ^ 11
    - 75102 * s ^ 10
    - 3429 * s ^ 9
    + 688 * s ^ 8
    + 61 * s ^ 7
    + s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient8 (s : ℚ) : ℚ :=
  -3 * s ^ 45
    + 51 * s ^ 44
    - 279 * s ^ 43
    - 79 * s ^ 42
    + 9353 * s ^ 41
    - 66276 * s ^ 40
    + 292204 * s ^ 39
    - 929473 * s ^ 38
    + 2100721 * s ^ 37
    - 2724229 * s ^ 36
    - 2341095 * s ^ 35
    + 28726882 * s ^ 34
    - 112587085 * s ^ 33
    + 304098018 * s ^ 32
    - 585146253 * s ^ 31
    + 708279585 * s ^ 30
    - 178724184 * s ^ 29
    - 1391195303 * s ^ 28
    + 3769940494 * s ^ 27
    - 5997099720 * s ^ 26
    + 7066470377 * s ^ 25
    - 6676192209 * s ^ 24
    + 5030088556 * s ^ 23
    - 2776377717 * s ^ 22
    + 1192107366 * s ^ 21
    - 778538846 * s ^ 20
    + 803076365 * s ^ 19
    - 651246106 * s ^ 18
    + 279143452 * s ^ 17
    + 66704558 * s ^ 16
    - 200627981 * s ^ 15
    + 162105423 * s ^ 14
    - 82328826 * s ^ 13
    + 28515929 * s ^ 12
    - 6070242 * s ^ 11
    + 474428 * s ^ 10
    + 69604 * s ^ 9
    - 6586 * s ^ 8
    - 836 * s ^ 7
    - 38 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient9 (s : ℚ) : ℚ :=
  -11 * s ^ 45
    + 259 * s ^ 44
    - 2606 * s ^ 43
    + 14339 * s ^ 42
    - 43301 * s ^ 41
    + 25534 * s ^ 40
    + 490250 * s ^ 39
    - 3285904 * s ^ 38
    + 13452312 * s ^ 37
    - 41987360 * s ^ 36
    + 105715758 * s ^ 35
    - 209027477 * s ^ 34
    + 257326934 * s ^ 33
    + 168192640 * s ^ 32
    - 2066425490 * s ^ 31
    + 6736007676 * s ^ 30
    - 14462128933 * s ^ 29
    + 23109003360 * s ^ 28
    - 28572091804 * s ^ 27
    + 27559177762 * s ^ 26
    - 20412989827 * s ^ 25
    + 10499470732 * s ^ 24
    - 1543788363 * s ^ 23
    - 2637176535 * s ^ 22
    + 201862117 * s ^ 21
    + 4500333910 * s ^ 20
    - 5743426631 * s ^ 19
    + 3050411126 * s ^ 18
    + 644927252 * s ^ 17
    - 2733295343 * s ^ 16
    + 2696562445 * s ^ 15
    - 1654351594 * s ^ 14
    + 717034981 * s ^ 13
    - 216045675 * s ^ 12
    + 37667335 * s ^ 11
    - 792010 * s ^ 10
    - 876717 * s ^ 9
    + 50864 * s ^ 8
    + 7357 * s ^ 7
    + 636 * s ^ 6
    + 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 46
    + 2 * s ^ 45
    + 384 * s ^ 44
    - 6733 * s ^ 43
    + 57869 * s ^ 42
    - 312518 * s ^ 41
    + 1155734 * s ^ 40
    - 2899100 * s ^ 39
    + 3385133 * s ^ 38
    + 11890570 * s ^ 37
    - 101964677 * s ^ 36
    + 461285399 * s ^ 35
    - 1631718354 * s ^ 34
    + 4825726165 * s ^ 33
    - 11948581788 * s ^ 32
    + 24290601109 * s ^ 31
    - 39442298191 * s ^ 30
    + 49158441080 * s ^ 29
    - 42965516791 * s ^ 28
    + 17142707513 * s ^ 27
    + 19093174222 * s ^ 26
    - 48087919681 * s ^ 25
    + 55948804384 * s ^ 24
    - 38170406608 * s ^ 23
    - 982880257 * s ^ 22
    + 41235953931 * s ^ 21
    - 52973365218 * s ^ 20
    + 29937483895 * s ^ 19
    + 5255950960 * s ^ 18
    - 28836691617 * s ^ 17
    + 32693414826 * s ^ 16
    - 23432657670 * s ^ 15
    + 12042755168 * s ^ 14
    - 4535096934 * s ^ 13
    + 1158448605 * s ^ 12
    - 137835547 * s ^ 11
    - 18606945 * s ^ 10
    + 7883310 * s ^ 9
    - 308682 * s ^ 8
    - 45805 * s ^ 7
    - 7135 * s ^ 6
    - 5 * s ^ 5
    - 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient11 (s : ℚ) : ℚ :=
  -3 * s ^ 46
    + 55 * s ^ 45
    + 10 * s ^ 44
    - 9787 * s ^ 43
    + 139124 * s ^ 42
    - 1112030 * s ^ 41
    + 6283950 * s ^ 40
    - 28012413 * s ^ 39
    + 105983146 * s ^ 38
    - 356561261 * s ^ 37
    + 1087852470 * s ^ 36
    - 2990866340 * s ^ 35
    + 7199352863 * s ^ 34
    - 14439003240 * s ^ 33
    + 22115585738 * s ^ 32
    - 20055310317 * s ^ 31
    - 9216970542 * s ^ 30
    + 77892165375 * s ^ 29
    - 172520759056 * s ^ 28
    + 247654642037 * s ^ 27
    - 248682113016 * s ^ 26
    + 149147370659 * s ^ 25
    + 31096723885 * s ^ 24
    - 237218448028 * s ^ 23
    + 386034574167 * s ^ 22
    - 379339725354 * s ^ 21
    + 189541545329 * s ^ 20
    + 74685848455 * s ^ 19
    - 263013728501 * s ^ 18
    + 309137685899 * s ^ 17
    - 244198842605 * s ^ 16
    + 142876746583 * s ^ 15
    - 63001094743 * s ^ 14
    + 20217839359 * s ^ 13
    - 3914447284 * s ^ 12
    - 12459720 * s ^ 11
    + 239926766 * s ^ 10
    - 52284961 * s ^ 9
    + 1210511 * s ^ 8
    + 212960 * s ^ 7
    + 60110 * s ^ 6
    - 280 * s ^ 5
    + 29 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient12 (s : ℚ) : ℚ :=
  s ^ 47
    - 43 * s ^ 46
    + 865 * s ^ 45
    - 10519 * s ^ 44
    + 85898 * s ^ 43
    - 503548 * s ^ 42
    + 2256911 * s ^ 41
    - 8379196 * s ^ 40
    + 28263296 * s ^ 39
    - 90611386 * s ^ 38
    + 259724936 * s ^ 37
    - 555960891 * s ^ 36
    + 381534951 * s ^ 35
    + 3368485200 * s ^ 34
    - 19826084751 * s ^ 33
    + 66067864028 * s ^ 32
    - 158245744958 * s ^ 31
    + 284592567688 * s ^ 30
    - 375618098131 * s ^ 29
    + 313239873756 * s ^ 28
    + 136997022 * s ^ 27
    - 558243963167 * s ^ 26
    + 1224228255179 * s ^ 25
    - 1773007058244 * s ^ 24
    + 1943517114349 * s ^ 23
    - 1492275915931 * s ^ 22
    + 376142964248 * s ^ 21
    + 1018349386428 * s ^ 20
    - 2041115378475 * s ^ 19
    + 2302820346038 * s ^ 18
    - 1902534065898 * s ^ 17
    + 1216739508910 * s ^ 16
    - 603727121861 * s ^ 15
    + 225219131922 * s ^ 14
    - 55800614739 * s ^ 13
    + 3538307308 * s ^ 12
    + 3801928147 * s ^ 11
    - 1631205667 * s ^ 10
    + 246380487 * s ^ 9
    + 1027932 * s ^ 8
    - 905558 * s ^ 7
    - 385077 * s ^ 6
    + 2608 * s ^ 5
    - 41 * s ^ 4
    - 27 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient13 (s : ℚ) : ℚ :=
  -s ^ 47
    + 16 * s ^ 46
    + 77 * s ^ 45
    - 4635 * s ^ 44
    + 62495 * s ^ 43
    - 488690 * s ^ 42
    + 2636936 * s ^ 41
    - 11089349 * s ^ 40
    + 43122934 * s ^ 39
    - 183501175 * s ^ 38
    + 834471000 * s ^ 37
    - 3506820927 * s ^ 36
    + 12411405946 * s ^ 35
    - 35544831767 * s ^ 34
    + 79686121512 * s ^ 33
    - 129926068607 * s ^ 32
    + 113382478915 * s ^ 31
    + 121618927346 * s ^ 30
    - 753398079688 * s ^ 29
    + 1848578107650 * s ^ 28
    - 3230904550948 * s ^ 27
    + 4472460556425 * s ^ 26
    - 4994634037803 * s ^ 25
    + 4179234887153 * s ^ 24
    - 1519047898510 * s ^ 23
    - 2972517826983 * s ^ 22
    + 8178656763103 * s ^ 21
    - 12033208367217 * s ^ 20
    + 12920426171305 * s ^ 19
    - 10907662632786 * s ^ 18
    + 7406506869629 * s ^ 17
    - 4009316948700 * s ^ 16
    + 1662136110663 * s ^ 15
    - 468324962149 * s ^ 14
    + 39252139982 * s ^ 13
    + 43005450301 * s ^ 12
    - 26431287987 * s ^ 11
    + 7150521583 * s ^ 10
    - 715019620 * s ^ 9
    - 58434903 * s ^ 8
    + 4097919 * s ^ 7
    + 1959519 * s ^ 6
    - 8131 * s ^ 5
    - 2173 * s ^ 4
    + 340 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient14 (s : ℚ) : ℚ :=
  -2 * s ^ 47
    + 66 * s ^ 46
    - 940 * s ^ 45
    + 7386 * s ^ 44
    - 33942 * s ^ 43
    + 112048 * s ^ 42
    - 811474 * s ^ 41
    + 9478001 * s ^ 40
    - 77232066 * s ^ 39
    + 428676964 * s ^ 38
    - 1691291997 * s ^ 37
    + 4646474874 * s ^ 36
    - 7036271127 * s ^ 35
    - 7995023690 * s ^ 34
    + 96422708001 * s ^ 33
    - 380188201207 * s ^ 32
    + 1034163511117 * s ^ 31
    - 2178888406395 * s ^ 30
    + 3692081136259 * s ^ 29
    - 5069995213064 * s ^ 28
    + 5460069626452 * s ^ 27
    - 3791009978741 * s ^ 26
    - 1122530666919 * s ^ 25
    + 10284105051981 * s ^ 24
    - 23570030905265 * s ^ 23
    + 38355622560258 * s ^ 22
    - 49428329635405 * s ^ 21
    + 51827106283100 * s ^ 20
    - 44672857944570 * s ^ 19
    + 31714980232941 * s ^ 18
    - 18258355634192 * s ^ 17
    + 8095193666827 * s ^ 16
    - 2360976588388 * s ^ 15
    + 75203587999 * s ^ 14
    + 403956371783 * s ^ 13
    - 277839103072 * s ^ 12
    + 102728413206 * s ^ 11
    - 19812189313 * s ^ 10
    + 462178482 * s ^ 9
    + 455571343 * s ^ 8
    - 11673407 * s ^ 7
    - 8874060 * s ^ 6
    + 6501 * s ^ 5
    + 26434 * s ^ 4
    - 2791 * s ^ 3
    + 4 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient15 (s : ℚ) : ℚ :=
  -s ^ 47
    + 40 * s ^ 46
    - 616 * s ^ 45
    + 3839 * s ^ 44
    + 12740 * s ^ 43
    - 446068 * s ^ 42
    + 4072516 * s ^ 41
    - 20291006 * s ^ 40
    + 42216148 * s ^ 39
    + 206375088 * s ^ 38
    - 2528617756 * s ^ 37
    + 14392347423 * s ^ 36
    - 58311795691 * s ^ 35
    + 184501509863 * s ^ 34
    - 470008193368 * s ^ 33
    + 967429777466 * s ^ 32
    - 1573007037841 * s ^ 31
    + 1852324782375 * s ^ 30
    - 940400964526 * s ^ 29
    - 2433595920216 * s ^ 28
    + 9942775608204 * s ^ 27
    - 23715191590425 * s ^ 26
    + 45820449216479 * s ^ 25
    - 76283707099746 * s ^ 24
    + 110133499016990 * s ^ 23
    - 136578790382249 * s ^ 22
    + 143741005827727 * s ^ 21
    - 127081366439052 * s ^ 20
    + 93375343046363 * s ^ 19
    - 55665755365856 * s ^ 18
    + 25036705657208 * s ^ 17
    - 6343481700547 * s ^ 16
    - 1571447683509 * s ^ 15
    + 3020602552246 * s ^ 14
    - 2059491821633 * s ^ 13
    + 904768239815 * s ^ 12
    - 247282957552 * s ^ 11
    + 26014454554 * s ^ 10
    + 6261873147 * s ^ 9
    - 1939680099 * s ^ 8
    - 37166759 * s ^ 7
    + 38665904 * s ^ 6
    + 76791 * s ^ 5
    - 196304 * s ^ 4
    + 17999 * s ^ 3
    - 105 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient16 (s : ℚ) : ℚ :=
  -s ^ 47
    + 44 * s ^ 46
    - 802 * s ^ 45
    + 6800 * s ^ 44
    + 673 * s ^ 43
    - 737171 * s ^ 42
    + 10233838 * s ^ 41
    - 85678408 * s ^ 40
    + 521286746 * s ^ 39
    - 2457309229 * s ^ 38
    + 9212900213 * s ^ 37
    - 27522019271 * s ^ 36
    + 63453452643 * s ^ 35
    - 99026258590 * s ^ 34
    + 28979187097 * s ^ 33
    + 449503941110 * s ^ 32
    - 1962866358296 * s ^ 31
    + 5563780646284 * s ^ 30
    - 12875052273489 * s ^ 29
    + 26431396486385 * s ^ 28
    - 49999349455907 * s ^ 27
    + 87704439652548 * s ^ 26
    - 140554783385474 * s ^ 25
    + 201209531277948 * s ^ 24
    - 251762067545927 * s ^ 23
    + 270187390553147 * s ^ 22
    - 244384978767257 * s ^ 21
    + 182355586806183 * s ^ 20
    - 107410280581578 * s ^ 19
    + 43039256357259 * s ^ 18
    - 1978604967582 * s ^ 17
    - 15256191836012 * s ^ 16
    + 16364608002643 * s ^ 15
    - 10926596573031 * s ^ 14
    + 5303590126518 * s ^ 13
    - 1793510873569 * s ^ 12
    + 312246902714 * s ^ 11
    + 37013675280 * s ^ 10
    - 32238605173 * s ^ 9
    + 4651025947 * s ^ 8
    + 590864497 * s ^ 7
    - 149279391 * s ^ 6
    - 1977439 * s ^ 5
    + 1195492 * s ^ 4
    - 99588 * s ^ 3
    + 1173 * s ^ 2
    + 3 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient17 (s : ℚ) : ℚ :=
  -2 * s ^ 47
    + 101 * s ^ 46
    - 2430 * s ^ 45
    + 36638 * s ^ 44
    - 384416 * s ^ 43
    + 2944952 * s ^ 42
    - 16682492 * s ^ 41
    + 67389850 * s ^ 40
    - 157122433 * s ^ 39
    - 176353541 * s ^ 38
    + 4045893051 * s ^ 37
    - 24781748316 * s ^ 36
    + 105766447785 * s ^ 35
    - 360788205711 * s ^ 34
    + 1039833304494 * s ^ 33
    - 2628433489210 * s ^ 32
    + 6033785547633 * s ^ 31
    - 12998009467848 * s ^ 30
    + 26816954261225 * s ^ 29
    - 52856483001099 * s ^ 28
    + 97321066140277 * s ^ 27
    - 162628630318538 * s ^ 26
    + 240446702429405 * s ^ 25
    - 308103887347399 * s ^ 24
    + 335543234867670 * s ^ 23
    - 302985576262166 * s ^ 22
    + 216901992683433 * s ^ 21
    - 108218932520787 * s ^ 20
    + 12750318321865 * s ^ 19
    + 47451053896139 * s ^ 18
    - 68727700419900 * s ^ 17
    + 61160395052719 * s ^ 16
    - 40889269077903 * s ^ 15
    + 21288688341915 * s ^ 14
    - 8255738738016 * s ^ 13
    + 1884059954242 * s ^ 12
    + 124301914450 * s ^ 11
    - 268933775078 * s ^ 10
    + 81034580379 * s ^ 9
    - 3090558969 * s ^ 8
    - 3149614450 * s ^ 7
    + 434810612 * s ^ 6
    + 21949221 * s ^ 5
    - 6133364 * s ^ 4
    + 463353 * s ^ 3
    - 7274 * s ^ 2
    - 67 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient18 (s : ℚ) : ℚ :=
  15 * s ^ 46
    - 719 * s ^ 45
    + 16642 * s ^ 44
    - 247034 * s ^ 43
    + 2639068 * s ^ 42
    - 21613045 * s ^ 41
    + 141284063 * s ^ 40
    - 758602707 * s ^ 39
    + 3420395634 * s ^ 38
    - 13197309477 * s ^ 37
    + 44409125029 * s ^ 36
    - 133370884186 * s ^ 35
    + 368724598589 * s ^ 34
    - 973693212437 * s ^ 33
    + 2526742101852 * s ^ 32
    - 6447972616791 * s ^ 31
    + 15737193274856 * s ^ 30
    - 35390907317192 * s ^ 29
    + 71111293144707 * s ^ 28
    - 124963845704277 * s ^ 27
    + 188987158059432 * s ^ 26
    - 241785498154326 * s ^ 25
    + 254629914164253 * s ^ 24
    - 207923115819640 * s ^ 23
    + 107684192343132 * s ^ 22
    + 13742814805196 * s ^ 21
    - 116521976054338 * s ^ 20
    + 174911338756965 * s ^ 19
    - 183940399454507 * s ^ 18
    + 154245665926501 * s ^ 17
    - 105563718685633 * s ^ 16
    + 58401570813319 * s ^ 15
    - 24820905761814 * s ^ 14
    + 6509963949198 * s ^ 13
    + 474107987052 * s ^ 12
    - 1435180534658 * s ^ 11
    + 648330816028 * s ^ 10
    - 101130788560 * s ^ 9
    - 20452587874 * s ^ 8
    + 10041758743 * s ^ 7
    - 766811076 * s ^ 6
    - 137252518 * s ^ 5
    + 25134319 * s ^ 4
    - 1709287 * s ^ 3
    + 26846 * s ^ 2
    + 656 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient19 (s : ℚ) : ℚ :=
  s ^ 47
    - 47 * s ^ 46
    + 1052 * s ^ 45
    - 14881 * s ^ 44
    + 148956 * s ^ 43
    - 1121256 * s ^ 42
    + 6609123 * s ^ 41
    - 31683147 * s ^ 40
    + 130739140 * s ^ 39
    - 514087833 * s ^ 38
    + 2181954706 * s ^ 37
    - 10275838134 * s ^ 36
    + 48773374861 * s ^ 35
    - 211808731288 * s ^ 34
    + 803496959060 * s ^ 33
    - 2621906961193 * s ^ 32
    + 7329677539496 * s ^ 31
    - 17524247477143 * s ^ 30
    + 35711033511108 * s ^ 29
    - 61522047741531 * s ^ 28
    + 87978349043331 * s ^ 27
    - 99970524976026 * s ^ 26
    + 78944806649577 * s ^ 25
    - 14198636792130 * s ^ 24
    - 85967166624498 * s ^ 23
    + 194014724579668 * s ^ 22
    - 277438278295119 * s ^ 21
    + 315929701675489 * s ^ 20
    - 306234407978075 * s ^ 19
    + 256489751871611 * s ^ 18
    - 182813561494911 * s ^ 17
    + 107162343028671 * s ^ 16
    - 48218707870541 * s ^ 15
    + 12738974498575 * s ^ 14
    + 2688399378274 * s ^ 13
    - 5446326534444 * s ^ 12
    + 3115686721758 * s ^ 11
    - 810728985154 * s ^ 10
    - 36408487474 * s ^ 9
    + 87457847214 * s ^ 8
    - 20455729151 * s ^ 7
    + 55764093 * s ^ 6
    + 560063289 * s ^ 5
    - 79257145 * s ^ 4
    + 4779387 * s ^ 3
    - 53531 * s ^ 2
    - 3770 * s
    - 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient20 (s : ℚ) : ℚ :=
  -2 * s ^ 46
    + 82 * s ^ 45
    - 1543 * s ^ 44
    + 16861 * s ^ 43
    - 102772 * s ^ 42
    + 49535 * s ^ 41
    + 6389099 * s ^ 40
    - 82262285 * s ^ 39
    + 662320405 * s ^ 38
    - 4063592735 * s ^ 37
    + 20264107987 * s ^ 36
    - 84543489445 * s ^ 35
    + 299171604450 * s ^ 34
    - 902373276169 * s ^ 33
    + 2315298051679 * s ^ 32
    - 5001881727620 * s ^ 31
    + 8871511568566 * s ^ 30
    - 12099495203494 * s ^ 29
    + 9879963885681 * s ^ 28
    + 5482664124426 * s ^ 27
    - 41638629505646 * s ^ 26
    + 100697056603491 * s ^ 25
    - 174602318173446 * s ^ 24
    + 246329648408088 * s ^ 23
    - 298107696389749 * s ^ 22
    + 320038638189948 * s ^ 21
    - 310452052021353 * s ^ 20
    + 270452689118573 * s ^ 19
    - 204494178490370 * s ^ 18
    + 126608163343214 * s ^ 17
    - 57397087439418 * s ^ 16
    + 10973199311271 * s ^ 15
    + 11154963834665 * s ^ 14
    - 15185151361124 * s ^ 13
    + 9875796115777 * s ^ 12
    - 3466459156094 * s ^ 11
    + 166100238451 * s ^ 10
    + 428536461859 * s ^ 9
    - 184418365708 * s ^ 8
    + 23206050617 * s ^ 7
    + 4320184874 * s ^ 6
    - 1609046564 * s ^ 5
    + 189368886 * s ^ 4
    - 9762729 * s ^ 3
    + 5483 * s ^ 2
    + 14146 * s
    + 152

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient21 (s : ℚ) : ℚ :=
  -s ^ 46
    + 53 * s ^ 45
    - 1360 * s ^ 44
    + 22536 * s ^ 43
    - 271191 * s ^ 42
    + 2525016 * s ^ 41
    - 18905306 * s ^ 40
    + 116605237 * s ^ 39
    - 600780980 * s ^ 38
    + 2598643100 * s ^ 37
    - 9388199940 * s ^ 36
    + 27733099395 * s ^ 35
    - 63081495220 * s ^ 34
    + 88158902138 * s ^ 33
    + 56686261306 * s ^ 32
    - 874622995417 * s ^ 31
    + 3503837485001 * s ^ 30
    - 9876815009264 * s ^ 29
    + 22360891065438 * s ^ 28
    - 42621423157629 * s ^ 27
    + 70086182101344 * s ^ 26
    - 101208210910937 * s ^ 25
    + 130763763655749 * s ^ 24
    - 154752648027122 * s ^ 23
    + 171789154417884 * s ^ 22
    - 180026130868510 * s ^ 21
    + 172955217963406 * s ^ 20
    - 142848465826818 * s ^ 19
    + 91881665801355 * s ^ 18
    - 36026112913804 * s ^ 17
    - 6551593940941 * s ^ 16
    + 28024167806064 * s ^ 15
    - 30682166087788 * s ^ 14
    + 21410182532867 * s ^ 13
    - 9083765634748 * s ^ 12
    + 966563687054 * s ^ 11
    + 1413276185321 * s ^ 10
    - 922560964540 * s ^ 9
    + 226306139753 * s ^ 8
    + 3060814414 * s ^ 7
    - 15013913282 * s ^ 6
    + 3379075607 * s ^ 5
    - 338818271 * s ^ 4
    + 13659695 * s ^ 3
    + 309898 * s ^ 2
    - 35763 * s
    - 799

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient22 (s : ℚ) : ℚ :=
  s ^ 45
    - 51 * s ^ 44
    + 1284 * s ^ 43
    - 21279 * s ^ 42
    + 261042 * s ^ 41
    - 2525186 * s ^ 40
    + 20010231 * s ^ 39
    - 133036261 * s ^ 38
    + 753289186 * s ^ 37
    - 3666488916 * s ^ 36
    + 15427558769 * s ^ 35
    - 56316646289 * s ^ 34
    + 178768426617 * s ^ 33
    - 494351412859 * s ^ 32
    + 1192955224208 * s ^ 31
    - 2518235078360 * s ^ 30
    + 4670780977411 * s ^ 29
    - 7683962974415 * s ^ 28
    + 11435271112156 * s ^ 27
    - 15979061946389 * s ^ 26
    + 22127224035343 * s ^ 25
    - 31624007834275 * s ^ 24
    + 45778147469872 * s ^ 23
    - 62232579072794 * s ^ 22
    + 72616513630575 * s ^ 21
    - 66182175152987 * s ^ 20
    + 39578769242945 * s ^ 19
    - 2697301796983 * s ^ 18
    - 28454071728054 * s ^ 17
    + 44110893459288 * s ^ 16
    - 43851230025497 * s ^ 15
    + 31917195758154 * s ^ 14
    - 15140485035042 * s ^ 13
    + 1800092931628 * s ^ 12
    + 3553201269275 * s ^ 11
    - 2992775631303 * s ^ 10
    + 1079695363317 * s ^ 9
    - 100994442717 * s ^ 8
    - 70103425019 * s ^ 7
    + 30563262309 * s ^ 6
    - 5250191484 * s ^ 5
    + 442669427 * s ^ 4
    - 10539185 * s ^ 3
    - 1008630 * s ^ 2
    + 58013 * s
    + 2924

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient23 (s : ℚ) : ℚ :=
  -13 * s ^ 42
    + 653 * s ^ 41
    - 15987 * s ^ 40
    + 252767 * s ^ 39
    - 2886609 * s ^ 38
    + 25260958 * s ^ 37
    - 175562301 * s ^ 36
    + 991786947 * s ^ 35
    - 4625008872 * s ^ 34
    + 17976966676 * s ^ 33
    - 58493677391 * s ^ 32
    + 158961698774 * s ^ 31
    - 355995653588 * s ^ 30
    + 631921837653 * s ^ 29
    - 782995692028 * s ^ 28
    + 242394405359 * s ^ 27
    + 1992751077853 * s ^ 26
    - 7043724822498 * s ^ 25
    + 15154782700761 * s ^ 24
    - 24189638629884 * s ^ 23
    + 28930473910936 * s ^ 22
    - 23304956940003 * s ^ 21
    + 5603165485720 * s ^ 20
    + 18071968554832 * s ^ 19
    - 37471380864285 * s ^ 18
    + 45986803763185 * s ^ 17
    - 43322960829926 * s ^ 16
    + 31942827829936 * s ^ 15
    - 15507960857661 * s ^ 14
    + 373537699622 * s ^ 13
    + 7213306124239 * s ^ 12
    - 6771756726709 * s ^ 11
    + 3130398460712 * s ^ 10
    - 556234333430 * s ^ 9
    - 197731630511 * s ^ 8
    + 153734007347 * s ^ 7
    - 42953007658 * s ^ 6
    + 5961345363 * s ^ 5
    - 395596115 * s ^ 4
    - 2086876 * s ^ 3
    + 1701450 * s ^ 2
    - 41508 * s
    - 7890

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient24 (s : ℚ) : ℚ :=
  -s ^ 42
    + 56 * s ^ 41
    - 1543 * s ^ 40
    + 27677 * s ^ 39
    - 360896 * s ^ 38
    + 3626209 * s ^ 37
    - 29101709 * s ^ 36
    + 191177273 * s ^ 35
    - 1046799316 * s ^ 34
    + 4845154217 * s ^ 33
    - 19172153498 * s ^ 32
    + 65454249451 * s ^ 31
    - 194231450930 * s ^ 30
    + 503806662760 * s ^ 29
    - 1146076398944 * s ^ 28
    + 2284709033083 * s ^ 27
    - 3955571837564 * s ^ 26
    + 5794619456720 * s ^ 25
    - 6716833082466 * s ^ 24
    + 4917501021158 * s ^ 23
    + 1226698135914 * s ^ 22
    - 11404138357654 * s ^ 21
    + 22380652576527 * s ^ 20
    - 29729703440033 * s ^ 19
    + 31148925033229 * s ^ 18
    - 27264565496812 * s ^ 17
    + 19169995932868 * s ^ 16
    - 7605642611181 * s ^ 15
    - 4416307044300 * s ^ 14
    + 11503803802625 * s ^ 13
    - 10974208779979 * s ^ 12
    + 5919780303836 * s ^ 11
    - 1409874700974 * s ^ 10
    - 420881588730 * s ^ 9
    + 498738531286 * s ^ 8
    - 199710356459 * s ^ 7
    + 42760620584 * s ^ 6
    - 4701828734 * s ^ 5
    + 195817423 * s ^ 4
    + 15676370 * s ^ 3
    - 1399447 * s ^ 2
    - 64308 * s
    + 16212

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient25 (s : ℚ) : ℚ :=
  -3 * s ^ 40
    + 158 * s ^ 39
    - 3953 * s ^ 38
    + 62696 * s ^ 37
    - 709475 * s ^ 36
    + 6113273 * s ^ 35
    - 41821038 * s ^ 34
    + 234007220 * s ^ 33
    - 1095899383 * s ^ 32
    + 4378916518 * s ^ 31
    - 15194016121 * s ^ 30
    + 46610156684 * s ^ 29
    - 128859383070 * s ^ 28
    + 326977075926 * s ^ 27
    - 769840201428 * s ^ 26
    + 1675040863184 * s ^ 25
    - 3301809590566 * s ^ 24
    + 5729930104696 * s ^ 23
    - 8511200518519 * s ^ 22
    + 10599320686932 * s ^ 21
    - 10993582116440 * s ^ 20
    + 9622689272793 * s ^ 19
    - 7128672447692 * s ^ 18
    + 3506586539618 * s ^ 17
    + 2030678397762 * s ^ 16
    - 8790945993233 * s ^ 15
    + 13348787254273 * s ^ 14
    - 12549589716085 * s ^ 13
    + 7351720388128 * s ^ 12
    - 1898656678183 * s ^ 11
    - 862187460425 * s ^ 10
    + 1150115920201 * s ^ 9
    - 587620092607 * s ^ 8
    + 173023984522 * s ^ 7
    - 28997429891 * s ^ 6
    + 2203623233 * s ^ 5
    + 6154939 * s ^ 4
    - 15071453 * s ^ 3
    - 607869 * s ^ 2
    + 260496 * s
    - 25818

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient26 (s : ℚ) : ℚ :=
  s ^ 39
    - 46 * s ^ 38
    + 1001 * s ^ 37
    - 13635 * s ^ 36
    + 129442 * s ^ 35
    - 898802 * s ^ 34
    + 4606796 * s ^ 33
    - 16521928 * s ^ 32
    + 29472957 * s ^ 31
    + 97683473 * s ^ 30
    - 1168318830 * s ^ 29
    + 6193056468 * s ^ 28
    - 23163367967 * s ^ 27
    + 65905579196 * s ^ 26
    - 142689148840 * s ^ 25
    + 222111194293 * s ^ 24
    - 197534404192 * s ^ 23
    - 73559050054 * s ^ 22
    + 612018759249 * s ^ 21
    - 1218363144278 * s ^ 20
    + 1751694908434 * s ^ 19
    - 2638342030906 * s ^ 18
    + 4701095671767 * s ^ 17
    - 7868364177463 * s ^ 16
    + 10256207245522 * s ^ 15
    - 9549890999685 * s ^ 14
    + 5632626355520 * s ^ 13
    - 1025464804822 * s ^ 12
    - 1655803084872 * s ^ 11
    + 1964776264614 * s ^ 10
    - 1159909057401 * s ^ 9
    + 427456766331 * s ^ 8
    - 97146585446 * s ^ 7
    + 11468203223 * s ^ 6
    - 218999824 * s ^ 5
    - 50282230 * s ^ 4
    - 4156208 * s ^ 3
    + 3574002 * s ^ 2
    - 456969 * s
    + 32109

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient27 (s : ℚ) : ℚ :=
  -s ^ 37
    + 49 * s ^ 36
    - 1139 * s ^ 35
    + 16700 * s ^ 34
    - 174405 * s ^ 33
    + 1401358 * s ^ 32
    - 9226539 * s ^ 31
    + 52540370 * s ^ 30
    - 267973785 * s ^ 29
    + 1230040955 * s ^ 28
    - 4979547207 * s ^ 27
    + 17277423192 * s ^ 26
    - 50075615474 * s ^ 25
    + 118722183002 * s ^ 24
    - 226260676403 * s ^ 23
    + 343821652392 * s ^ 22
    - 434292833382 * s ^ 21
    + 562958469060 * s ^ 20
    - 1002545045725 * s ^ 19
    + 2073726354643 * s ^ 18
    - 3639481618769 * s ^ 17
    + 4771137944035 * s ^ 16
    - 4309248316937 * s ^ 15
    + 2069639171662 * s ^ 14
    + 699668947922 * s ^ 13
    - 2385361936517 * s ^ 12
    + 2438732178095 * s ^ 11
    - 1550370286574 * s ^ 10
    + 663785136436 * s ^ 9
    - 185532219676 * s ^ 8
    + 28864600610 * s ^ 7
    - 885803067 * s ^ 6
    - 276967512 * s ^ 5
    - 51918773 * s ^ 4
    + 27155466 * s ^ 3
    - 5552205 * s ^ 2
    + 529305 * s
    - 31162

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient28 (s : ℚ) : ℚ :=
  2 * s ^ 35
    - 109 * s ^ 34
    + 2707 * s ^ 33
    - 40772 * s ^ 32
    + 415972 * s ^ 31
    - 3020376 * s ^ 30
    + 15770269 * s ^ 29
    - 56712191 * s ^ 28
    + 111389651 * s ^ 27
    + 121835038 * s ^ 26
    - 1892100793 * s ^ 25
    + 7782021858 * s ^ 24
    - 18357388272 * s ^ 23
    + 19319244902 * s ^ 22
    + 38446702871 * s ^ 21
    - 237301879834 * s ^ 20
    + 623111496642 * s ^ 19
    - 1074923727445 * s ^ 18
    + 1251655832050 * s ^ 17
    - 789825327344 * s ^ 16
    - 315982956030 * s ^ 15
    + 1548622570847 * s ^ 14
    - 2219927740176 * s ^ 13
    + 2048477938936 * s ^ 12
    - 1342157467774 * s ^ 11
    + 625991576810 * s ^ 10
    - 195608782968 * s ^ 9
    + 32967814208 * s ^ 8
    + 494137177 * s ^ 7
    - 1065102878 * s ^ 6
    - 134726083 * s ^ 5
    + 148609612 * s ^ 4
    - 35247133 * s ^ 3
    + 5273578 * s ^ 2
    - 436340 * s
    + 23388

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient29 (s : ℚ) : ℚ :=
  -s ^ 34
    + 45 * s ^ 33
    - 917 * s ^ 32
    + 10913 * s ^ 31
    - 78534 * s ^ 30
    + 256511 * s ^ 29
    + 1306828 * s ^ 28
    - 24970657 * s ^ 27
    + 197553090 * s ^ 26
    - 1074354594 * s ^ 25
    + 4450482596 * s ^ 24
    - 14561447964 * s ^ 23
    + 38011604877 * s ^ 22
    - 78336383347 * s ^ 21
    + 121838039748 * s ^ 20
    - 121613611771 * s ^ 19
    + 3465248626 * s ^ 18
    + 283563103784 * s ^ 17
    - 692660684431 * s ^ 16
    + 1058083960738 * s ^ 15
    - 1188196120069 * s ^ 14
    + 1015598153282 * s ^ 13
    - 655597352590 * s ^ 12
    + 304819713237 * s ^ 11
    - 88261054850 * s ^ 10
    + 5774731133 * s ^ 9
    + 6878764973 * s ^ 8
    - 2396361639 * s ^ 7
    - 267069832 * s ^ 6
    + 426914583 * s ^ 5
    - 143321725 * s ^ 4
    + 26100892 * s ^ 3
    - 3377522 * s ^ 2
    + 257906 * s
    - 13319

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient30 (s : ℚ) : ℚ :=
  2 * s ^ 32
    - 101 * s ^ 31
    + 2447 * s ^ 30
    - 37889 * s ^ 29
    + 421251 * s ^ 28
    - 3580749 * s ^ 27
    + 24185289 * s ^ 26
    - 133134832 * s ^ 25
    + 607712741 * s ^ 24
    - 2327587230 * s ^ 23
    + 7539064712 * s ^ 22
    - 20747100078 * s ^ 21
    + 48600786485 * s ^ 20
    - 96831107681 * s ^ 19
    + 163461985410 * s ^ 18
    - 232044035509 * s ^ 17
    + 273428603780 * s ^ 16
    - 261553610160 * s ^ 15
    + 194730547699 * s ^ 14
    - 102108983555 * s ^ 13
    + 24544647523 * s ^ 12
    + 14326471251 * s ^ 11
    - 19335298371 * s ^ 10
    + 10221402721 * s ^ 9
    - 2212348990 * s ^ 8
    - 721536310 * s ^ 7
    + 784502886 * s ^ 6
    - 317267195 * s ^ 5
    + 75994915 * s ^ 4
    - 12054577 * s ^ 3
    + 1454627 * s ^ 2
    - 106078 * s
    + 5566

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient31 (s : ℚ) : ℚ :=
  -2 * s ^ 29
    + 93 * s ^ 28
    - 2060 * s ^ 27
    + 28948 * s ^ 26
    - 289926 * s ^ 25
    + 2203702 * s ^ 24
    - 13212813 * s ^ 23
    + 64097720 * s ^ 22
    - 255934958 * s ^ 21
    + 850761400 * s ^ 20
    - 2371163046 * s ^ 19
    + 5561063040 * s ^ 18
    - 10980535463 * s ^ 17
    + 18208243999 * s ^ 16
    - 25206623635 * s ^ 15
    + 28826680083 * s ^ 14
    - 26748050461 * s ^ 13
    + 19479882381 * s ^ 12
    - 10335705282 * s ^ 11
    + 3072162303 * s ^ 10
    + 596125094 * s ^ 9
    - 1376993927 * s ^ 8
    + 922150012 * s ^ 7
    - 386580231 * s ^ 6
    + 111083190 * s ^ 5
    - 22324991 * s ^ 4
    + 3303625 * s ^ 3
    - 395258 * s ^ 2
    + 28073 * s
    - 1610

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient32 (s : ℚ) : ℚ :=
  s ^ 26
    - 44 * s ^ 25
    + 915 * s ^ 24
    - 11961 * s ^ 23
    + 110275 * s ^ 22
    - 762619 * s ^ 21
    + 4107701 * s ^ 20
    - 17662861 * s ^ 19
    + 61655312 * s ^ 18
    - 176730051 * s ^ 17
    + 419193896 * s ^ 16
    - 826706118 * s ^ 15
    + 1358779129 * s ^ 14
    - 1861798792 * s ^ 13
    + 2123141283 * s ^ 12
    - 2007690361 * s ^ 11
    + 1565004629 * s ^ 10
    - 996871699 * s ^ 9
    + 512434560 * s ^ 8
    - 208906511 * s ^ 7
    + 66035612 * s ^ 6
    - 15826358 * s ^ 5
    + 2887709 * s ^ 4
    - 437316 * s ^ 3
    + 57268 * s ^ 2
    - 3887 * s
    + 288

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient33 (s : ℚ) : ℚ :=
  -s ^ 17
    + 28 * s ^ 16
    - 358 * s ^ 15
    + 2767 * s ^ 14
    - 14423 * s ^ 13
    + 53545 * s ^ 12
    - 145694 * s ^ 11
    + 294307 * s ^ 10
    - 441541 * s ^ 9
    + 485691 * s ^ 8
    - 378885 * s ^ 7
    + 193265 * s ^ 6
    - 48319 * s ^ 5
    - 7907 * s ^ 4
    + 9849 * s ^ 3
    - 2356 * s ^ 2
    + 56 * s
    - 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient34 (s : ℚ) : ℚ :=
  s ^ 7
    - 12 * s ^ 6
    + 58 * s ^ 5
    - 144 * s ^ 4
    + 193 * s ^ 3
    - 132 * s ^ 2
    + 36 * s

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
    structuralNumeratorCoefficient34 s * r ^ 34

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_0 (s : ℚ) :
    structuralNumeratorCoefficient0 s =
      termOneCoefficient0 s
        - termTwoCoefficient0 s
        - termThreeCoefficient0 s
      := by
  simp only [structuralNumeratorCoefficient0,
    termOneCoefficient0,
    termTwoCoefficient0,
    termThreeCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_1 (s : ℚ) :
    structuralNumeratorCoefficient1 s =
      termOneCoefficient1 s
        - termTwoCoefficient1 s
        - termThreeCoefficient1 s
      := by
  simp only [structuralNumeratorCoefficient1,
    termOneCoefficient1,
    termTwoCoefficient1,
    termThreeCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_2 (s : ℚ) :
    structuralNumeratorCoefficient2 s =
      termOneCoefficient2 s
        - termTwoCoefficient2 s
        - termThreeCoefficient2 s
      := by
  simp only [structuralNumeratorCoefficient2,
    termOneCoefficient2,
    termTwoCoefficient2,
    termThreeCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_3 (s : ℚ) :
    structuralNumeratorCoefficient3 s =
      termOneCoefficient3 s
        - termTwoCoefficient3 s
        - termThreeCoefficient3 s
      := by
  simp only [structuralNumeratorCoefficient3,
    termOneCoefficient3,
    termTwoCoefficient3,
    termThreeCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_4 (s : ℚ) :
    structuralNumeratorCoefficient4 s =
      termOneCoefficient4 s
        - termTwoCoefficient4 s
        - termThreeCoefficient4 s
      := by
  simp only [structuralNumeratorCoefficient4,
    termOneCoefficient4,
    termTwoCoefficient4,
    termThreeCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_5 (s : ℚ) :
    structuralNumeratorCoefficient5 s =
      termOneCoefficient5 s
        - termTwoCoefficient5 s
        - termThreeCoefficient5 s
      := by
  simp only [structuralNumeratorCoefficient5,
    termOneCoefficient5,
    termTwoCoefficient5,
    termThreeCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_6 (s : ℚ) :
    structuralNumeratorCoefficient6 s =
      termOneCoefficient6 s
        - termTwoCoefficient6 s
        - termThreeCoefficient6 s
      := by
  simp only [structuralNumeratorCoefficient6,
    termOneCoefficient6,
    termTwoCoefficient6,
    termThreeCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_7 (s : ℚ) :
    structuralNumeratorCoefficient7 s =
      termOneCoefficient7 s
        - termTwoCoefficient7 s
        - termThreeCoefficient7 s
      := by
  simp only [structuralNumeratorCoefficient7,
    termOneCoefficient7,
    termTwoCoefficient7,
    termThreeCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_8 (s : ℚ) :
    structuralNumeratorCoefficient8 s =
      termOneCoefficient8 s
        - termTwoCoefficient8 s
        - termThreeCoefficient8 s
      := by
  simp only [structuralNumeratorCoefficient8,
    termOneCoefficient8,
    termTwoCoefficient8,
    termThreeCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_9 (s : ℚ) :
    structuralNumeratorCoefficient9 s =
      termOneCoefficient9 s
        - termTwoCoefficient9 s
        - termThreeCoefficient9 s
      := by
  simp only [structuralNumeratorCoefficient9,
    termOneCoefficient9,
    termTwoCoefficient9,
    termThreeCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_10 (s : ℚ) :
    structuralNumeratorCoefficient10 s =
      termOneCoefficient10 s
        - termTwoCoefficient10 s
        - termThreeCoefficient10 s
      := by
  simp only [structuralNumeratorCoefficient10,
    termOneCoefficient10,
    termTwoCoefficient10,
    termThreeCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_11 (s : ℚ) :
    structuralNumeratorCoefficient11 s =
      termOneCoefficient11 s
        - termTwoCoefficient11 s
        - termThreeCoefficient11 s
      := by
  simp only [structuralNumeratorCoefficient11,
    termOneCoefficient11,
    termTwoCoefficient11,
    termThreeCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_12 (s : ℚ) :
    structuralNumeratorCoefficient12 s =
      termOneCoefficient12 s
        - termTwoCoefficient12 s
        - termThreeCoefficient12 s
      := by
  simp only [structuralNumeratorCoefficient12,
    termOneCoefficient12,
    termTwoCoefficient12,
    termThreeCoefficient12]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_13 (s : ℚ) :
    structuralNumeratorCoefficient13 s =
      termOneCoefficient13 s
        - termTwoCoefficient13 s
        - termThreeCoefficient13 s
      := by
  simp only [structuralNumeratorCoefficient13,
    termOneCoefficient13,
    termTwoCoefficient13,
    termThreeCoefficient13]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_14 (s : ℚ) :
    structuralNumeratorCoefficient14 s =
      termOneCoefficient14 s
        - termTwoCoefficient14 s
        - termThreeCoefficient14 s
      := by
  simp only [structuralNumeratorCoefficient14,
    termOneCoefficient14,
    termTwoCoefficient14,
    termThreeCoefficient14]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_15 (s : ℚ) :
    structuralNumeratorCoefficient15 s =
      termOneCoefficient15 s
        - termTwoCoefficient15 s
        - termThreeCoefficient15 s
      := by
  simp only [structuralNumeratorCoefficient15,
    termOneCoefficient15,
    termTwoCoefficient15,
    termThreeCoefficient15]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_16 (s : ℚ) :
    structuralNumeratorCoefficient16 s =
      termOneCoefficient16 s
        - termTwoCoefficient16 s
        - termThreeCoefficient16 s
      := by
  simp only [structuralNumeratorCoefficient16,
    termOneCoefficient16,
    termTwoCoefficient16,
    termThreeCoefficient16]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_17 (s : ℚ) :
    structuralNumeratorCoefficient17 s =
      termOneCoefficient17 s
        - termTwoCoefficient17 s
        - termThreeCoefficient17 s
      := by
  simp only [structuralNumeratorCoefficient17,
    termOneCoefficient17,
    termTwoCoefficient17,
    termThreeCoefficient17]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_18 (s : ℚ) :
    structuralNumeratorCoefficient18 s =
      termOneCoefficient18 s
        - termTwoCoefficient18 s
        - termThreeCoefficient18 s
      := by
  simp only [structuralNumeratorCoefficient18,
    termOneCoefficient18,
    termTwoCoefficient18,
    termThreeCoefficient18]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_19 (s : ℚ) :
    structuralNumeratorCoefficient19 s =
      termOneCoefficient19 s
        - termTwoCoefficient19 s
        - termThreeCoefficient19 s
      := by
  simp only [structuralNumeratorCoefficient19,
    termOneCoefficient19,
    termTwoCoefficient19,
    termThreeCoefficient19]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_20 (s : ℚ) :
    structuralNumeratorCoefficient20 s =
      termOneCoefficient20 s
        - termTwoCoefficient20 s
        - termThreeCoefficient20 s
      := by
  simp only [structuralNumeratorCoefficient20,
    termOneCoefficient20,
    termTwoCoefficient20,
    termThreeCoefficient20]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_21 (s : ℚ) :
    structuralNumeratorCoefficient21 s =
      termOneCoefficient21 s
        - termTwoCoefficient21 s
        - termThreeCoefficient21 s
      := by
  simp only [structuralNumeratorCoefficient21,
    termOneCoefficient21,
    termTwoCoefficient21,
    termThreeCoefficient21]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_22 (s : ℚ) :
    structuralNumeratorCoefficient22 s =
      termOneCoefficient22 s
        - termTwoCoefficient22 s
        - termThreeCoefficient22 s
      := by
  simp only [structuralNumeratorCoefficient22,
    termOneCoefficient22,
    termTwoCoefficient22,
    termThreeCoefficient22]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_23 (s : ℚ) :
    structuralNumeratorCoefficient23 s =
      termOneCoefficient23 s
        - termTwoCoefficient23 s
        - termThreeCoefficient23 s
      := by
  simp only [structuralNumeratorCoefficient23,
    termOneCoefficient23,
    termTwoCoefficient23,
    termThreeCoefficient23]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_24 (s : ℚ) :
    structuralNumeratorCoefficient24 s =
      termOneCoefficient24 s
        - termTwoCoefficient24 s
        - termThreeCoefficient24 s
      := by
  simp only [structuralNumeratorCoefficient24,
    termOneCoefficient24,
    termTwoCoefficient24,
    termThreeCoefficient24]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_25 (s : ℚ) :
    structuralNumeratorCoefficient25 s =
      termOneCoefficient25 s
        - termTwoCoefficient25 s
        - termThreeCoefficient25 s
      := by
  simp only [structuralNumeratorCoefficient25,
    termOneCoefficient25,
    termTwoCoefficient25,
    termThreeCoefficient25]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_26 (s : ℚ) :
    structuralNumeratorCoefficient26 s =
      termOneCoefficient26 s
        - termTwoCoefficient26 s
        - termThreeCoefficient26 s
      := by
  simp only [structuralNumeratorCoefficient26,
    termOneCoefficient26,
    termTwoCoefficient26,
    termThreeCoefficient26]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_27 (s : ℚ) :
    structuralNumeratorCoefficient27 s =
      termOneCoefficient27 s
        - termTwoCoefficient27 s
        - termThreeCoefficient27 s
      := by
  simp only [structuralNumeratorCoefficient27,
    termOneCoefficient27,
    termTwoCoefficient27,
    termThreeCoefficient27]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_28 (s : ℚ) :
    structuralNumeratorCoefficient28 s =
      termOneCoefficient28 s
        - termTwoCoefficient28 s
        - termThreeCoefficient28 s
      := by
  simp only [structuralNumeratorCoefficient28,
    termOneCoefficient28,
    termTwoCoefficient28,
    termThreeCoefficient28]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_29 (s : ℚ) :
    structuralNumeratorCoefficient29 s =
      termOneCoefficient29 s
        - termTwoCoefficient29 s
        - termThreeCoefficient29 s
      := by
  simp only [structuralNumeratorCoefficient29,
    termOneCoefficient29,
    termTwoCoefficient29,
    termThreeCoefficient29]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_30 (s : ℚ) :
    structuralNumeratorCoefficient30 s =
      termOneCoefficient30 s
        - termTwoCoefficient30 s
        - termThreeCoefficient30 s
      := by
  simp only [structuralNumeratorCoefficient30,
    termOneCoefficient30,
    termTwoCoefficient30,
    termThreeCoefficient30]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_31 (s : ℚ) :
    structuralNumeratorCoefficient31 s =
      termOneCoefficient31 s
        - termTwoCoefficient31 s
        - termThreeCoefficient31 s
      := by
  simp only [structuralNumeratorCoefficient31,
    termOneCoefficient31,
    termTwoCoefficient31,
    termThreeCoefficient31]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_32 (s : ℚ) :
    structuralNumeratorCoefficient32 s =
      termOneCoefficient32 s
        - termTwoCoefficient32 s
        - termThreeCoefficient32 s
      := by
  simp only [structuralNumeratorCoefficient32,
    termOneCoefficient32,
    termTwoCoefficient32,
    termThreeCoefficient32]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_33 (s : ℚ) :
    structuralNumeratorCoefficient33 s =
      termOneCoefficient33 s
        - termTwoCoefficient33 s
        - termThreeCoefficient33 s
      := by
  simp only [structuralNumeratorCoefficient33,
    termOneCoefficient33,
    termTwoCoefficient33,
    termThreeCoefficient33]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_linear_certificate_34 (s : ℚ) :
    structuralNumeratorCoefficient34 s =
      termOneCoefficient34 s
        - termTwoCoefficient34 s
        - 0
      := by
  simp only [structuralNumeratorCoefficient34,
    termOneCoefficient34,
    termTwoCoefficient34]
  ring

/-- Checked staged polynomial-combination identity. -/
theorem structuralNumerator_eq_linearCombination (r s : ℚ) :
    structuralNumerator r s = termOne r s - termTwo r s - termThree r s := by
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
  simp only [structuralNumerator, termOne, termTwo, termThree]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient0 (s : ℚ) : ℚ :=
  s ^ 19
    - s ^ 18
    + s ^ 17
    - s ^ 16

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 25
    + 4 * s ^ 24
    - 10 * s ^ 23
    + 21 * s ^ 22
    - 38 * s ^ 21
    + 63 * s ^ 20
    - 86 * s ^ 19
    + 62 * s ^ 18
    - 44 * s ^ 17
    + 17 * s ^ 16
    + 15 * s ^ 15
    - 3 * s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient2 (s : ℚ) : ℚ :=
  -3 * s ^ 26
    + 15 * s ^ 25
    - 22 * s ^ 24
    + 27 * s ^ 23
    - 45 * s ^ 22
    + 42 * s ^ 21
    + 79 * s ^ 20
    - 559 * s ^ 19
    + 1316 * s ^ 18
    - 1497 * s ^ 17
    + 1572 * s ^ 16
    - 1267 * s ^ 15
    + 496 * s ^ 14
    - 251 * s ^ 13
    + 146 * s ^ 12
    - 69 * s ^ 11
    + 26 * s ^ 10
    - 7 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 28
    + 5 * s ^ 27
    - 20 * s ^ 26
    + 132 * s ^ 25
    - 471 * s ^ 24
    + 949 * s ^ 23
    - 1993 * s ^ 22
    + 4721 * s ^ 21
    - 9938 * s ^ 20
    + 16703 * s ^ 19
    - 19749 * s ^ 18
    + 16057 * s ^ 17
    - 12198 * s ^ 16
    + 5194 * s ^ 15
    + 576 * s ^ 14
    + 810 * s ^ 13
    - 1274 * s ^ 12
    + 681 * s ^ 11
    - 202 * s ^ 10
    - 4 * s ^ 9
    + 33 * s ^ 8
    - 12 * s ^ 7
    + s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient4 (s : ℚ) : ℚ :=
  -2 * s ^ 29
    + 17 * s ^ 28
    - 72 * s ^ 27
    + 296 * s ^ 26
    - 997 * s ^ 25
    + 2305 * s ^ 24
    - 5941 * s ^ 23
    + 18406 * s ^ 22
    - 42038 * s ^ 21
    + 66266 * s ^ 20
    - 68867 * s ^ 19
    + 32982 * s ^ 18
    + 11423 * s ^ 17
    - 28928 * s ^ 16
    + 45071 * s ^ 15
    - 24204 * s ^ 14
    - 20001 * s ^ 13
    + 21004 * s ^ 12
    - 8045 * s ^ 11
    + 635 * s ^ 10
    + 1374 * s ^ 9
    - 899 * s ^ 8
    + 223 * s ^ 7
    - 6 * s ^ 6
    - 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 30
    + 8 * s ^ 29
    - 14 * s ^ 28
    + 29 * s ^ 27
    - 452 * s ^ 26
    + 2634 * s ^ 25
    - 11563 * s ^ 24
    + 40391 * s ^ 23
    - 87216 * s ^ 22
    + 91856 * s ^ 21
    + 19500 * s ^ 20
    - 246899 * s ^ 19
    + 448103 * s ^ 18
    - 409082 * s ^ 17
    + 181803 * s ^ 16
    + 53723 * s ^ 15
    - 378232 * s ^ 14
    + 489204 * s ^ 13
    - 242760 * s ^ 12
    + 38916 * s ^ 11
    + 29495 * s ^ 10
    - 29970 * s ^ 9
    + 12980 * s ^ 8
    - 2435 * s ^ 7
    - 49 * s ^ 6
    + 29 * s ^ 5
    + 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient6 (s : ℚ) : ℚ :=
  -2 * s ^ 30
    + 24 * s ^ 29
    - 22 * s ^ 28
    - 865 * s ^ 27
    + 5724 * s ^ 26
    - 19590 * s ^ 25
    + 42143 * s ^ 24
    - 24500 * s ^ 23
    - 196604 * s ^ 22
    + 750117 * s ^ 21
    - 1360046 * s ^ 20
    + 1362773 * s ^ 19
    - 155311 * s ^ 18
    - 2030311 * s ^ 17
    + 3947300 * s ^ 16
    - 4990572 * s ^ 15
    + 5075071 * s ^ 14
    - 3136819 * s ^ 13
    + 471558 * s ^ 12
    + 661963 * s ^ 11
    - 666098 * s ^ 10
    + 366283 * s ^ 9
    - 119835 * s ^ 8
    + 16414 * s ^ 7
    + 1470 * s ^ 6
    - 230 * s ^ 5
    - 34 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient7 (s : ℚ) : ℚ :=
  -8 * s ^ 30
    + 151 * s ^ 29
    - 1132 * s ^ 28
    + 3779 * s ^ 27
    - 848 * s ^ 26
    - 46730 * s ^ 25
    + 244137 * s ^ 24
    - 735631 * s ^ 23
    + 1325505 * s ^ 22
    - 744760 * s ^ 21
    - 3059802 * s ^ 20
    + 10942783 * s ^ 19
    - 21014130 * s ^ 18
    + 28766793 * s ^ 17
    - 30380756 * s ^ 16
    + 25860128 * s ^ 15
    - 15028840 * s ^ 14
    - 621339 * s ^ 13
    + 10551400 * s ^ 12
    - 10095095 * s ^ 11
    + 5965697 * s ^ 10
    - 2512377 * s ^ 9
    + 637888 * s ^ 8
    - 38418 * s ^ 7
    - 20289 * s ^ 6
    + 1618 * s ^ 5
    + 254 * s ^ 4
    + 22 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 31
    + 7 * s ^ 30
    + 155 * s ^ 29
    - 2738 * s ^ 28
    + 19508 * s ^ 27
    - 77259 * s ^ 26
    + 162346 * s ^ 25
    + 37353 * s ^ 24
    - 1781581 * s ^ 23
    + 8024177 * s ^ 22
    - 22315265 * s ^ 21
    + 44467629 * s ^ 20
    - 67497751 * s ^ 19
    + 80386248 * s ^ 18
    - 73852707 * s ^ 17
    + 46461329 * s ^ 16
    - 2319360 * s ^ 15
    - 52843909 * s ^ 14
    + 95000707 * s ^ 13
    - 92883935 * s ^ 12
    + 59148612 * s ^ 11
    - 27972991 * s ^ 10
    + 9487461 * s ^ 9
    - 1498804 * s ^ 8
    - 302755 * s ^ 7
    + 163109 * s ^ 6
    - 8105 * s ^ 5
    - 1260 * s ^ 4
    - 220 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient9 (s : ℚ) : ℚ :=
  -2 * s ^ 31
    + 38 * s ^ 30
    - 114 * s ^ 29
    - 3259 * s ^ 28
    + 47228 * s ^ 27
    - 337610 * s ^ 26
    + 1612144 * s ^ 25
    - 5717888 * s ^ 24
    + 15764141 * s ^ 23
    - 33983559 * s ^ 22
    + 56196614 * s ^ 21
    - 68464234 * s ^ 20
    + 53477968 * s ^ 19
    + 350642 * s ^ 18
    - 96241627 * s ^ 17
    + 228048605 * s ^ 16
    - 378204564 * s ^ 15
    + 495933249 * s ^ 14
    - 493297015 * s ^ 13
    + 351578013 * s ^ 12
    - 180609698 * s ^ 11
    + 69501618 * s ^ 10
    - 15564075 * s ^ 9
    - 2380353 * s ^ 8
    + 3044203 * s ^ 7
    - 767270 * s ^ 6
    + 9771 * s ^ 5
    + 5636 * s ^ 4
    + 1402 * s ^ 3
    - 4 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient10 (s : ℚ) : ℚ :=
  s ^ 32
    - 34 * s ^ 31
    + 575 * s ^ 30
    - 6147 * s ^ 29
    + 45210 * s ^ 28
    - 239392 * s ^ 27
    + 939109 * s ^ 26
    - 2759747 * s ^ 25
    + 5896965 * s ^ 24
    - 7630773 * s ^ 23
    - 1990984 * s ^ 22
    + 41523113 * s ^ 21
    - 130424136 * s ^ 20
    + 281208866 * s ^ 19
    - 505396327 * s ^ 18
    + 812331502 * s ^ 17
    - 1175594565 * s ^ 16
    + 1485460374 * s ^ 15
    - 1543098619 * s ^ 14
    + 1220602962 * s ^ 13
    - 688702028 * s ^ 12
    + 268591621 * s ^ 11
    - 59145413 * s ^ 10
    - 19783539 * s ^ 9
    + 28606429 * s ^ 8
    - 12551473 * s ^ 7
    + 1998690 * s ^ 6
    + 145132 * s ^ 5
    - 20420 * s ^ 4
    - 7037 * s ^ 3
    + 85 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient11 (s : ℚ) : ℚ :=
  -2 * s ^ 32
    + 50 * s ^ 31
    - 563 * s ^ 30
    + 3443 * s ^ 29
    - 8900 * s ^ 28
    - 36056 * s ^ 27
    + 506674 * s ^ 26
    - 2959201 * s ^ 25
    + 11983829 * s ^ 24
    - 37684186 * s ^ 23
    + 96477176 * s ^ 22
    - 208550758 * s ^ 21
    + 399943480 * s ^ 20
    - 717389447 * s ^ 19
    + 1221821054 * s ^ 18
    - 1907287422 * s ^ 17
    + 2588087074 * s ^ 16
    - 2890905697 * s ^ 15
    + 2484070511 * s ^ 14
    - 1488457320 * s ^ 13
    + 511432725 * s ^ 12
    + 4871997 * s ^ 11
    - 160099127 * s ^ 10
    + 164547588 * s ^ 9
    - 96441631 * s ^ 8
    + 28749719 * s ^ 7
    - 1756330 * s ^ 6
    - 974015 * s ^ 5
    + 25031 * s ^ 4
    + 31060 * s ^ 3
    - 753 * s ^ 2
    - 3 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient12 (s : ℚ) : ℚ :=
  -s ^ 32
    + 41 * s ^ 31
    - 734 * s ^ 30
    + 7949 * s ^ 29
    - 59345 * s ^ 28
    + 328515 * s ^ 27
    - 1419103 * s ^ 26
    + 4987817 * s ^ 25
    - 14809332 * s ^ 24
    + 38625703 * s ^ 23
    - 92901506 * s ^ 22
    + 216163945 * s ^ 21
    - 489406074 * s ^ 20
    + 1023921571 * s ^ 19
    - 1853904673 * s ^ 18
    + 2770926574 * s ^ 17
    - 3288232778 * s ^ 16
    + 2903550915 * s ^ 15
    - 1605602796 * s ^ 14
    + 126393446 * s ^ 13
    + 690780256 * s ^ 12
    - 783584732 * s ^ 11
    + 621874709 * s ^ 10
    - 412533593 * s ^ 9
    + 180688147 * s ^ 8
    - 32813923 * s ^ 7
    - 5955608 * s ^ 6
    + 2882940 * s ^ 5
    + 203729 * s ^ 4
    - 115720 * s ^ 3
    + 3609 * s ^ 2
    + 52 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient13 (s : ℚ) : ℚ :=
  s ^ 32
    - 27 * s ^ 31
    + 339 * s ^ 30
    - 2639 * s ^ 29
    + 14569 * s ^ 28
    - 64792 * s ^ 27
    + 273234 * s ^ 26
    - 1224730 * s ^ 25
    + 5590637 * s ^ 24
    - 23417311 * s ^ 23
    + 84270874 * s ^ 22
    - 252008492 * s ^ 21
    + 613176390 * s ^ 20
    - 1193333588 * s ^ 19
    + 1820065001 * s ^ 18
    - 2081058110 * s ^ 17
    + 1535178678 * s ^ 16
    - 141387693 * s ^ 15
    - 1443214925 * s ^ 14
    + 2267322942 * s ^ 13
    - 2077515076 * s ^ 12
    + 1507337468 * s ^ 11
    - 1042515115 * s ^ 10
    + 599037557 * s ^ 9
    - 187759005 * s ^ 8
    - 8085995 * s ^ 7
    + 24305310 * s ^ 6
    - 3950309 * s ^ 5
    - 1357513 * s ^ 4
    + 332716 * s ^ 3
    - 10014 * s ^ 2
    - 381 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient14 (s : ℚ) : ℚ :=
  -s ^ 31
    + 14 * s ^ 30
    + 54 * s ^ 29
    - 3200 * s ^ 28
    + 42127 * s ^ 27
    - 339489 * s ^ 26
    + 1981010 * s ^ 25
    - 8960910 * s ^ 24
    + 32384448 * s ^ 23
    - 94148593 * s ^ 22
    + 217654245 * s ^ 21
    - 387008746 * s ^ 20
    + 484512373 * s ^ 19
    - 280048406 * s ^ 18
    - 442296361 * s ^ 17
    + 1641329789 * s ^ 16
    - 2842375822 * s ^ 15
    + 3344764646 * s ^ 14
    - 2902302006 * s ^ 13
    + 2090851798 * s ^ 12
    - 1537553973 * s ^ 11
    + 1112341391 * s ^ 10
    - 526543851 * s ^ 9
    + 38724916 * s ^ 8
    + 94062029 * s ^ 7
    - 39027117 * s ^ 6
    - 1650267 * s ^ 5
    + 4287924 * s ^ 4
    - 694149 * s ^ 3
    + 14534 * s ^ 2
    + 1580 * s
    + 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient15 (s : ℚ) : ℚ :=
  -s ^ 31
    + 34 * s ^ 30
    - 549 * s ^ 29
    + 5626 * s ^ 28
    - 41061 * s ^ 27
    + 225902 * s ^ 26
    - 958865 * s ^ 25
    + 3107708 * s ^ 24
    - 7148984 * s ^ 23
    + 8141700 * s ^ 22
    + 16906325 * s ^ 21
    - 123494668 * s ^ 20
    + 391698219 * s ^ 19
    - 871163445 * s ^ 18
    + 1494417077 * s ^ 17
    - 2026006544 * s ^ 16
    + 2155897182 * s ^ 15
    - 1802581389 * s ^ 14
    + 1342044358 * s ^ 13
    - 1212286160 * s ^ 12
    + 1224589438 * s ^ 11
    - 844181016 * s ^ 10
    + 169895484 * s ^ 9
    + 203237829 * s ^ 8
    - 153482007 * s ^ 7
    + 20180261 * s ^ 6
    + 18545950 * s ^ 5
    - 8539352 * s ^ 4
    + 995950 * s ^ 3
    - 833 * s ^ 2
    - 4092 * s
    - 77

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient16 (s : ℚ) : ℚ :=
  s ^ 30
    - 33 * s ^ 29
    + 539 * s ^ 28
    - 5810 * s ^ 27
    + 46330 * s ^ 26
    - 289141 * s ^ 25
    + 1451087 * s ^ 24
    - 5916488 * s ^ 23
    + 19629969 * s ^ 22
    - 52936947 * s ^ 21
    + 115978471 * s ^ 20
    - 206526696 * s ^ 19
    + 297678423 * s ^ 18
    - 339387689 * s ^ 17
    + 290346334 * s ^ 16
    - 196044337 * s ^ 15
    + 244451037 * s ^ 14
    - 591274771 * s ^ 13
    + 999609084 * s ^ 12
    - 931354024 * s ^ 11
    + 297587134 * s ^ 10
    + 282060740 * s ^ 9
    - 334004500 * s ^ 8
    + 96524617 * s ^ 7
    + 42021213 * s ^ 6
    - 40026975 * s ^ 5
    + 11289890 * s ^ 4
    - 874101 * s ^ 3
    - 40304 * s ^ 2
    + 6673 * s
    + 274

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient17 (s : ℚ) : ℚ :=
  -12 * s ^ 27
    + 378 * s ^ 26
    - 5727 * s ^ 25
    + 54681 * s ^ 24
    - 363578 * s ^ 23
    + 1766637 * s ^ 22
    - 6441781 * s ^ 21
    + 17905221 * s ^ 20
    - 38229818 * s ^ 19
    + 61980852 * s ^ 18
    - 68649025 * s ^ 17
    + 13622893 * s ^ 16
    + 168513617 * s ^ 15
    - 493958388 * s ^ 14
    + 793930431 * s ^ 13
    - 741516938 * s ^ 12
    + 229965662 * s ^ 11
    + 339016440 * s ^ 10
    - 467917849 * s ^ 9
    + 192926402 * s ^ 8
    + 64139514 * s ^ 7
    - 106159597 * s ^ 6
    + 48637956 * s ^ 5
    - 9537638 * s ^ 4
    + 245746 * s ^ 3
    + 80558 * s ^ 2
    - 5988 * s
    - 649

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient18 (s : ℚ) : ℚ :=
  -s ^ 27
    + 37 * s ^ 26
    - 667 * s ^ 25
    + 7690 * s ^ 24
    - 62566 * s ^ 23
    + 376895 * s ^ 22
    - 1732786 * s ^ 21
    + 6238914 * s ^ 20
    - 18116445 * s ^ 19
    + 44058351 * s ^ 18
    - 93336107 * s ^ 17
    + 174653365 * s ^ 16
    - 276855443 * s ^ 15
    + 332093370 * s ^ 14
    - 223787218 * s ^ 13
    - 83073594 * s ^ 12
    + 401501937 * s ^ 11
    - 448687994 * s ^ 10
    + 189438345 * s ^ 9
    + 99331023 * s ^ 8
    - 185045733 * s ^ 7
    + 113548886 * s ^ 6
    - 35022463 * s ^ 5
    + 4141869 * s ^ 4
    + 398207 * s ^ 3
    - 69107 * s ^ 2
    + 166 * s
    + 1069

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient19 (s : ℚ) : ℚ :=
  -2 * s ^ 25
    + 71 * s ^ 24
    - 1107 * s ^ 23
    + 10052 * s ^ 22
    - 58864 * s ^ 21
    + 229993 * s ^ 20
    - 592291 * s ^ 19
    + 971373 * s ^ 18
    - 1404734 * s ^ 17
    + 5843911 * s ^ 16
    - 28881271 * s ^ 15
    + 92336162 * s ^ 14
    - 193563477 * s ^ 13
    + 267675816 * s ^ 12
    - 218746807 * s ^ 11
    + 34274085 * s ^ 10
    + 160175295 * s ^ 9
    - 224354393 * s ^ 8
    + 156736665 * s ^ 7
    - 62468600 * s ^ 6
    + 11934412 * s ^ 5
    + 372164 * s ^ 4
    - 496533 * s ^ 3
    + 2185 * s ^ 2
    + 7134 * s
    - 1239

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient20 (s : ℚ) : ℚ :=
  s ^ 24
    - 28 * s ^ 23
    + 330 * s ^ 22
    - 1916 * s ^ 21
    + 2400 * s ^ 20
    + 50894 * s ^ 19
    - 475189 * s ^ 18
    + 2361297 * s ^ 17
    - 7889115 * s ^ 16
    + 18513177 * s ^ 15
    - 29278614 * s ^ 14
    + 23828622 * s ^ 13
    + 17195808 * s ^ 12
    - 90907142 * s ^ 11
    + 157339525 * s ^ 10
    - 168501639 * s ^ 9
    + 119308388 * s ^ 8
    - 53062646 * s ^ 7
    + 11393476 * s ^ 6
    + 1190697 * s ^ 5
    - 1259341 * s ^ 4
    + 143246 * s ^ 3
    + 56497 * s ^ 2
    - 9724 * s
    + 996

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient21 (s : ℚ) : ℚ :=
  -2 * s ^ 22
    + 67 * s ^ 21
    - 1062 * s ^ 20
    + 10594 * s ^ 19
    - 74517 * s ^ 18
    + 391941 * s ^ 17
    - 1593849 * s ^ 16
    + 5107267 * s ^ 15
    - 13017023 * s ^ 14
    + 26427961 * s ^ 13
    - 42459587 * s ^ 12
    + 53062535 * s ^ 11
    - 49812058 * s ^ 10
    + 32560867 * s ^ 9
    - 11719743 * s ^ 8
    - 1168808 * s ^ 7
    + 3832373 * s ^ 6
    - 1876835 * s ^ 5
    + 257407 * s ^ 4
    + 124181 * s ^ 3
    - 57717 * s ^ 2
    + 6538 * s
    - 530

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient22 (s : ℚ) : ℚ :=
  2 * s ^ 19
    - 59 * s ^ 18
    + 811 * s ^ 17
    - 6910 * s ^ 16
    + 40911 * s ^ 15
    - 178543 * s ^ 14
    + 593389 * s ^ 13
    - 1526858 * s ^ 12
    + 3056290 * s ^ 11
    - 4733398 * s ^ 10
    + 5578800 * s ^ 9
    - 4840282 * s ^ 8
    + 2882829 * s ^ 7
    - 957206 * s ^ 6
    - 43243 * s ^ 5
    + 220834 * s ^ 4
    - 110980 * s ^ 3
    + 25672 * s ^ 2
    - 2227 * s
    + 168

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient23 (s : ℚ) : ℚ :=
  -s ^ 16
    + 27 * s ^ 15
    - 333 * s ^ 14
    + 2485 * s ^ 13
    - 12528 * s ^ 12
    + 45115 * s ^ 11
    - 119643 * s ^ 10
    + 237410 * s ^ 9
    - 354616 * s ^ 8
    + 397992 * s ^ 7
    - 332705 * s ^ 6
    + 203881 * s ^ 5
    - 89038 * s ^ 4
    + 26018 * s ^ 3
    - 4276 * s ^ 2
    + 236 * s
    - 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient24 (s : ℚ) : ℚ :=
  s ^ 7
    - 12 * s ^ 6
    + 58 * s ^ 5
    - 144 * s ^ 4
    + 193 * s ^ 3
    - 132 * s ^ 2
    + 36 * s

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
    multiplierCoefficient24 s * r ^ 24

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_0 (s : ℚ) :
    structuralNumeratorCoefficient0 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient0,
    sutherlandPolynomialCoefficient0,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_1 (s : ℚ) :
    structuralNumeratorCoefficient1 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient1,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_2 (s : ℚ) :
    structuralNumeratorCoefficient2 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient2,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_3 (s : ℚ) :
    structuralNumeratorCoefficient3 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient3,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_4 (s : ℚ) :
    structuralNumeratorCoefficient4 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient4,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_5 (s : ℚ) :
    structuralNumeratorCoefficient5 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient5,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_6 (s : ℚ) :
    structuralNumeratorCoefficient6 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient6,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_7 (s : ℚ) :
    structuralNumeratorCoefficient7 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient7,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_8 (s : ℚ) :
    structuralNumeratorCoefficient8 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient8,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_9 (s : ℚ) :
    structuralNumeratorCoefficient9 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient9,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_10 (s : ℚ) :
    structuralNumeratorCoefficient10 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient1 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient0 s
    := by
  simp only [structuralNumeratorCoefficient10,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1,
    multiplierCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_11 (s : ℚ) :
    structuralNumeratorCoefficient11 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient2 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient1 s
    := by
  simp only [structuralNumeratorCoefficient11,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2,
    multiplierCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_12 (s : ℚ) :
    structuralNumeratorCoefficient12 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient3 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient2 s
    := by
  simp only [structuralNumeratorCoefficient12,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3,
    multiplierCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_13 (s : ℚ) :
    structuralNumeratorCoefficient13 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient4 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient3 s
    := by
  simp only [structuralNumeratorCoefficient13,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4,
    multiplierCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_14 (s : ℚ) :
    structuralNumeratorCoefficient14 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient5 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient4 s
    := by
  simp only [structuralNumeratorCoefficient14,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5,
    multiplierCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_15 (s : ℚ) :
    structuralNumeratorCoefficient15 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient6 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient5 s
    := by
  simp only [structuralNumeratorCoefficient15,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6,
    multiplierCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_16 (s : ℚ) :
    structuralNumeratorCoefficient16 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient7 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient6 s
    := by
  simp only [structuralNumeratorCoefficient16,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7,
    multiplierCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_17 (s : ℚ) :
    structuralNumeratorCoefficient17 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient8 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient7 s
    := by
  simp only [structuralNumeratorCoefficient17,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8,
    multiplierCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_18 (s : ℚ) :
    structuralNumeratorCoefficient18 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient9 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient8 s
    := by
  simp only [structuralNumeratorCoefficient18,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9,
    multiplierCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_19 (s : ℚ) :
    structuralNumeratorCoefficient19 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient10 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient9 s
    := by
  simp only [structuralNumeratorCoefficient19,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10,
    multiplierCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_20 (s : ℚ) :
    structuralNumeratorCoefficient20 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient11 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient10 s
    := by
  simp only [structuralNumeratorCoefficient20,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11,
    multiplierCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_21 (s : ℚ) :
    structuralNumeratorCoefficient21 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient12 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient11 s
    := by
  simp only [structuralNumeratorCoefficient21,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12,
    multiplierCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_22 (s : ℚ) :
    structuralNumeratorCoefficient22 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient13 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient12 s
    := by
  simp only [structuralNumeratorCoefficient22,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13,
    multiplierCoefficient12]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_23 (s : ℚ) :
    structuralNumeratorCoefficient23 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient14 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient13 s
    := by
  simp only [structuralNumeratorCoefficient23,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14,
    multiplierCoefficient13]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_24 (s : ℚ) :
    structuralNumeratorCoefficient24 s =
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient15 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient14 s
    := by
  simp only [structuralNumeratorCoefficient24,
    sutherlandPolynomialCoefficient0,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15,
    multiplierCoefficient14]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_25 (s : ℚ) :
    structuralNumeratorCoefficient25 s =
    sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient16 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient15 s
    := by
  simp only [structuralNumeratorCoefficient25,
    sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16,
    multiplierCoefficient15]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_26 (s : ℚ) :
    structuralNumeratorCoefficient26 s =
    sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient17 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient16 s
    := by
  simp only [structuralNumeratorCoefficient26,
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17,
    multiplierCoefficient16]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_27 (s : ℚ) :
    structuralNumeratorCoefficient27 s =
    sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient18 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient17 s
    := by
  simp only [structuralNumeratorCoefficient27,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18,
    multiplierCoefficient17]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_28 (s : ℚ) :
    structuralNumeratorCoefficient28 s =
    sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient19 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient18 s
    := by
  simp only [structuralNumeratorCoefficient28,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19,
    multiplierCoefficient18]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_29 (s : ℚ) :
    structuralNumeratorCoefficient29 s =
    sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient20 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient19 s
    := by
  simp only [structuralNumeratorCoefficient29,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_30 (s : ℚ) :
    structuralNumeratorCoefficient30 s =
    sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient20 s
    := by
  simp only [structuralNumeratorCoefficient30,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_31 (s : ℚ) :
    structuralNumeratorCoefficient31 s =
    sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient21 s
    := by
  simp only [structuralNumeratorCoefficient31,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_32 (s : ℚ) :
    structuralNumeratorCoefficient32 s =
    sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient22 s
    := by
  simp only [structuralNumeratorCoefficient32,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_33 (s : ℚ) :
    structuralNumeratorCoefficient33 s =
    sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient23 s
    := by
  simp only [structuralNumeratorCoefficient33,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24,
    multiplierCoefficient23]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_34 (s : ℚ) :
    structuralNumeratorCoefficient34 s =
    sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient24 s
    := by
  simp only [structuralNumeratorCoefficient34,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient24]
  ring

/-- Checked staged polynomial-product identity. -/
theorem structuralNumerator_eq_sutherlandPolynomial_mul_multiplier (r s : ℚ) :
    structuralNumerator r s = sutherlandPolynomial r s * multiplier r s := by
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
  simp only [structuralNumerator, sutherlandPolynomial, multiplier]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34

/-- The normalized fourth cyclic unit relation vanishes on the raw curve. -/
theorem relation_eq_zero
    (r s : ℚ)
    (hCurve : sutherlandPolynomial r s = 0)
    (hEight : rawUnitEightDenominator r s ≠ 0)
    (hFour : rawUnitFourDenominator r s ≠ 0)
    (hTwo : rawUnitTwoDenominator r s ≠ 0)
    (hNine : rawUnitNineDenominator r s ≠ 0) :
    rawUnitEightNumerator r s /
          rawUnitEightDenominator r s -
        rawUnitFourNumerator r s /
          rawUnitFourDenominator r s -
      (rawUnitEightNumerator r s /
          rawUnitEightDenominator r s) *
        (rawUnitTwoNumerator r s /
          rawUnitTwoDenominator r s) *
        (rawUnitNineNumerator r s /
            rawUnitNineDenominator r s -
          rawUnitEightNumerator r s /
            rawUnitEightDenominator r s) =
      0 := by
  have hStructural :=
    structuralNumerator_eq_sutherlandPolynomial_mul_multiplier r s
  simp only [structuralNumerator_eq_linearCombination,
    t1Step1_eq_rawUnitEightNumerator_mul_rawUnitEightDenominator,
    t1Step2_eq_t1Step1_mul_rawUnitFourDenominator,
    t1Step3_eq_t1Step2_mul_rawUnitTwoDenominator,
    termOne_eq_t1Step3_mul_rawUnitNineDenominator,
    t2Step1_eq_rawUnitFourNumerator_mul_rawUnitEightDenominator,
    t2Step2_eq_t2Step1_mul_rawUnitEightDenominator,
    t2Step3_eq_t2Step2_mul_rawUnitTwoDenominator,
    termTwo_eq_t2Step3_mul_rawUnitNineDenominator,
    t3Step1_eq_rawUnitEightNumerator_mul_rawUnitTwoNumerator,
    t3Step2_eq_t3Step1_mul_difference,
    termThree_eq_t3Step2_mul_rawUnitFourDenominator,
    difference_eq_linearCombination,
    differenceLeft_eq_rawUnitNineNumerator_mul_rawUnitEightDenominator,
    differenceRight_eq_rawUnitEightNumerator_mul_rawUnitNineDenominator] at hStructural
  rw [hCurve, zero_mul] at hStructural
  field_simp [hEight, hFour, hTwo, hNine]
  linear_combination hStructural

end MazurTorsion.Kubert.OrderTwentyFiveRawOrbitRelationThreeData
