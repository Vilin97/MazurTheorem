/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveRawOrbitData

/-!
# Exact raw-orbit norm certificate for order twenty-five

This coefficientwise certificate proves the norm-one relation for the
five raw modular units. Exact polynomial division over `ℚ` discovered
the quotient; Lean checks every coefficient and staged polynomial product.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawOrbitNormData

open OrderTwentyFiveRawOrbitData

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 16
    + 3 * s ^ 15
    - 4 * s ^ 14
    + 4 * s ^ 13
    - 4 * s ^ 12
    + 4 * s ^ 11
    - 3 * s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 17
    + s ^ 16
    + 24 * s ^ 15
    - 75 * s ^ 14
    + 103 * s ^ 13
    - 95 * s ^ 12
    + 84 * s ^ 11
    - 93 * s ^ 10
    + 96 * s ^ 9
    - 63 * s ^ 8
    + 25 * s ^ 7
    - 7 * s ^ 6
    + s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient3 (s : ℚ) : ℚ :=
  s ^ 18
    - 14 * s ^ 17
    + 84 * s ^ 16
    - 205 * s ^ 15
    + 103 * s ^ 14
    + 308 * s ^ 13
    - 511 * s ^ 12
    + 172 * s ^ 11
    + 348 * s ^ 10
    - 423 * s ^ 9
    + 40 * s ^ 8
    + 230 * s ^ 7
    - 221 * s ^ 6
    + 123 * s ^ 5
    - 43 * s ^ 4
    + 9 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient4 (s : ℚ) : ℚ :=
  s ^ 19
    - 10 * s ^ 18
    + 28 * s ^ 17
    + 99 * s ^ 16
    - 937 * s ^ 15
    + 2587 * s ^ 14
    - 2764 * s ^ 13
    - 518 * s ^ 12
    + 4519 * s ^ 11
    - 4548 * s ^ 10
    - 245 * s ^ 9
    + 5258 * s ^ 8
    - 6266 * s ^ 7
    + 4336 * s ^ 6
    - 2113 * s ^ 5
    + 707 * s ^ 4
    - 151 * s ^ 3
    + 17 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient5 (s : ℚ) : ℚ :=
  3 * s ^ 19
    - 50 * s ^ 18
    + 347 * s ^ 17
    - 1236 * s ^ 16
    + 1801 * s ^ 15
    + 2619 * s ^ 14
    - 15728 * s ^ 13
    + 26645 * s ^ 12
    - 14996 * s ^ 11
    - 22817 * s ^ 10
    + 64106 * s ^ 9
    - 79768 * s ^ 8
    + 64828 * s ^ 7
    - 38578 * s ^ 6
    + 17386 * s ^ 5
    - 5628 * s ^ 4
    + 1201 * s ^ 3
    - 135 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient6 (s : ℚ) : ℚ :=
  s ^ 20
    - 12 * s ^ 19
    + 33 * s ^ 18
    + 287 * s ^ 17
    - 2949 * s ^ 16
    + 12312 * s ^ 15
    - 26820 * s ^ 14
    + 18728 * s ^ 13
    + 61919 * s ^ 12
    - 227087 * s ^ 11
    + 408144 * s ^ 10
    - 500840 * s ^ 9
    + 454276 * s ^ 8
    - 316599 * s ^ 7
    + 174762 * s ^ 6
    - 75576 * s ^ 5
    + 23863 * s ^ 4
    - 4955 * s ^ 3
    + 496 * s ^ 2
    + 18 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 20
    - 39 * s ^ 19
    + 321 * s ^ 18
    - 1326 * s ^ 17
    + 1507 * s ^ 16
    + 13864 * s ^ 15
    - 93046 * s ^ 14
    + 313660 * s ^ 13
    - 706451 * s ^ 12
    + 1164182 * s ^ 11
    - 1477384 * s ^ 10
    + 1484588 * s ^ 9
    - 1198497 * s ^ 8
    + 790274 * s ^ 7
    - 428734 * s ^ 6
    + 183634 * s ^ 5
    - 56575 * s ^ 4
    + 10811 * s ^ 3
    - 625 * s ^ 2
    - 176 * s
    + 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient8 (s : ℚ) : ℚ :=
  3 * s ^ 20
    - 77 * s ^ 19
    + 921 * s ^ 18
    - 6816 * s ^ 17
    + 34882 * s ^ 16
    - 130488 * s ^ 15
    + 368086 * s ^ 14
    - 799679 * s ^ 13
    + 1365700 * s ^ 12
    - 1877338 * s ^ 11
    + 2123208 * s ^ 10
    - 2002141 * s ^ 9
    + 1590588 * s ^ 8
    - 1074898 * s ^ 7
    + 604176 * s ^ 6
    - 260011 * s ^ 5
    + 74963 * s ^ 4
    - 10411 * s ^ 3
    - 1379 * s ^ 2
    + 755 * s
    - 44

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient9 (s : ℚ) : ℚ :=
  s ^ 21
    - 24 * s ^ 20
    + 277 * s ^ 19
    - 2028 * s ^ 18
    + 10483 * s ^ 17
    - 40370 * s ^ 16
    + 119464 * s ^ 15
    - 277821 * s ^ 14
    + 519994 * s ^ 13
    - 807968 * s ^ 12
    + 1077016 * s ^ 11
    - 1255499 * s ^ 10
    + 1282772 * s ^ 9
    - 1144465 * s ^ 8
    + 868691 * s ^ 7
    - 517651 * s ^ 6
    + 211203 * s ^ 5
    - 43888 * s ^ 4
    - 5447 * s ^ 3
    + 7022 * s ^ 2
    - 1874 * s
    + 112

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient10 (s : ℚ) : ℚ :=
  -3 * s ^ 18
    + 49 * s ^ 17
    - 338 * s ^ 16
    + 1090 * s ^ 15
    - 35 * s ^ 14
    - 15117 * s ^ 13
    + 71796 * s ^ 12
    - 194085 * s ^ 11
    + 365094 * s ^ 10
    - 519663 * s ^ 9
    + 575567 * s ^ 8
    - 475893 * s ^ 7
    + 259547 * s ^ 6
    - 62973 * s ^ 5
    - 24127 * s ^ 4
    + 29923 * s ^ 3
    - 13612 * s ^ 2
    + 2961 * s
    - 181

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient11 (s : ℚ) : ℚ :=
  -s ^ 18
    + 23 * s ^ 17
    - 247 * s ^ 16
    + 1636 * s ^ 15
    - 7427 * s ^ 14
    + 24405 * s ^ 13
    - 60312 * s ^ 12
    + 116317 * s ^ 11
    - 181182 * s ^ 10
    + 229032 * s ^ 9
    - 219811 * s ^ 8
    + 130553 * s ^ 7
    - 7119 * s ^ 6
    - 67874 * s ^ 5
    + 70982 * s ^ 4
    - 41404 * s ^ 3
    + 15287 * s ^ 2
    - 3048 * s
    + 190

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient12 (s : ℚ) : ℚ :=
  8 * s ^ 14
    - 134 * s ^ 13
    + 961 * s ^ 12
    - 3744 * s ^ 11
    + 7889 * s ^ 10
    - 5101 * s ^ 9
    - 18041 * s ^ 8
    + 59077 * s ^ 7
    - 89697 * s ^ 6
    + 86829 * s ^ 5
    - 59456 * s ^ 4
    + 29865 * s ^ 3
    - 10314 * s ^ 2
    + 1984 * s
    - 126

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient13 (s : ℚ) : ℚ :=
  s ^ 14
    - 22 * s ^ 13
    + 218 * s ^ 12
    - 1286 * s ^ 11
    + 5020 * s ^ 10
    - 13635 * s ^ 9
    + 26472 * s ^ 8
    - 37471 * s ^ 7
    + 39666 * s ^ 6
    - 32602 * s ^ 5
    + 21441 * s ^ 4
    - 10952 * s ^ 3
    + 3842 * s ^ 2
    - 740 * s
    + 48

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep1Coefficient14 (s : ℚ) : ℚ :=
  -s ^ 10
    + 17 * s ^ 9
    - 124 * s ^ 8
    + 509 * s ^ 7
    - 1296 * s ^ 6
    + 2126 * s ^ 5
    - 2257 * s ^ 4
    + 1512 * s ^ 3
    - 598 * s ^ 2
    + 120 * s
    - 8

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def numeratorStep1 (r s : ℚ) : ℚ :=
  numeratorStep1Coefficient0 s +
    numeratorStep1Coefficient1 s * r +
    numeratorStep1Coefficient2 s * r ^ 2 +
    numeratorStep1Coefficient3 s * r ^ 3 +
    numeratorStep1Coefficient4 s * r ^ 4 +
    numeratorStep1Coefficient5 s * r ^ 5 +
    numeratorStep1Coefficient6 s * r ^ 6 +
    numeratorStep1Coefficient7 s * r ^ 7 +
    numeratorStep1Coefficient8 s * r ^ 8 +
    numeratorStep1Coefficient9 s * r ^ 9 +
    numeratorStep1Coefficient10 s * r ^ 10 +
    numeratorStep1Coefficient11 s * r ^ 11 +
    numeratorStep1Coefficient12 s * r ^ 12 +
    numeratorStep1Coefficient13 s * r ^ 13 +
    numeratorStep1Coefficient14 s * r ^ 14

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_0 (s : ℚ) :
    numeratorStep1Coefficient0 s =
    rawUnitOneNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [numeratorStep1Coefficient0,
    rawUnitOneNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_1 (s : ℚ) :
    numeratorStep1Coefficient1 s =
    rawUnitOneNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitOneNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [numeratorStep1Coefficient1,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_2 (s : ℚ) :
    numeratorStep1Coefficient2 s =
    rawUnitOneNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitOneNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitOneNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [numeratorStep1Coefficient2,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_3 (s : ℚ) :
    numeratorStep1Coefficient3 s =
    rawUnitOneNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitOneNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitOneNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitOneNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [numeratorStep1Coefficient3,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_4 (s : ℚ) :
    numeratorStep1Coefficient4 s =
    rawUnitOneNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitOneNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitOneNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitOneNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitOneNumeratorCoefficient4 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [numeratorStep1Coefficient4,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_5 (s : ℚ) :
    numeratorStep1Coefficient5 s =
    rawUnitOneNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitOneNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitOneNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitOneNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitOneNumeratorCoefficient4 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitOneNumeratorCoefficient5 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [numeratorStep1Coefficient5,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_6 (s : ℚ) :
    numeratorStep1Coefficient6 s =
    rawUnitOneNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitOneNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitOneNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitOneNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitOneNumeratorCoefficient4 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitOneNumeratorCoefficient5 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitOneNumeratorCoefficient6 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [numeratorStep1Coefficient6,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_7 (s : ℚ) :
    numeratorStep1Coefficient7 s =
    rawUnitOneNumeratorCoefficient0 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitOneNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitOneNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitOneNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitOneNumeratorCoefficient4 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitOneNumeratorCoefficient5 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitOneNumeratorCoefficient6 s *
        rawUnitTwoNumeratorCoefficient1 s
      + rawUnitOneNumeratorCoefficient7 s *
        rawUnitTwoNumeratorCoefficient0 s
    := by
  simp only [numeratorStep1Coefficient7,
    rawUnitOneNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_8 (s : ℚ) :
    numeratorStep1Coefficient8 s =
    rawUnitOneNumeratorCoefficient1 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitOneNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitOneNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitOneNumeratorCoefficient4 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitOneNumeratorCoefficient5 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitOneNumeratorCoefficient6 s *
        rawUnitTwoNumeratorCoefficient2 s
      + rawUnitOneNumeratorCoefficient7 s *
        rawUnitTwoNumeratorCoefficient1 s
    := by
  simp only [numeratorStep1Coefficient8,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_9 (s : ℚ) :
    numeratorStep1Coefficient9 s =
    rawUnitOneNumeratorCoefficient2 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitOneNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitOneNumeratorCoefficient4 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitOneNumeratorCoefficient5 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitOneNumeratorCoefficient6 s *
        rawUnitTwoNumeratorCoefficient3 s
      + rawUnitOneNumeratorCoefficient7 s *
        rawUnitTwoNumeratorCoefficient2 s
    := by
  simp only [numeratorStep1Coefficient9,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_10 (s : ℚ) :
    numeratorStep1Coefficient10 s =
    rawUnitOneNumeratorCoefficient3 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitOneNumeratorCoefficient4 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitOneNumeratorCoefficient5 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitOneNumeratorCoefficient6 s *
        rawUnitTwoNumeratorCoefficient4 s
      + rawUnitOneNumeratorCoefficient7 s *
        rawUnitTwoNumeratorCoefficient3 s
    := by
  simp only [numeratorStep1Coefficient10,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_11 (s : ℚ) :
    numeratorStep1Coefficient11 s =
    rawUnitOneNumeratorCoefficient4 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitOneNumeratorCoefficient5 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitOneNumeratorCoefficient6 s *
        rawUnitTwoNumeratorCoefficient5 s
      + rawUnitOneNumeratorCoefficient7 s *
        rawUnitTwoNumeratorCoefficient4 s
    := by
  simp only [numeratorStep1Coefficient11,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_12 (s : ℚ) :
    numeratorStep1Coefficient12 s =
    rawUnitOneNumeratorCoefficient5 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitOneNumeratorCoefficient6 s *
        rawUnitTwoNumeratorCoefficient6 s
      + rawUnitOneNumeratorCoefficient7 s *
        rawUnitTwoNumeratorCoefficient5 s
    := by
  simp only [numeratorStep1Coefficient12,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_13 (s : ℚ) :
    numeratorStep1Coefficient13 s =
    rawUnitOneNumeratorCoefficient6 s *
        rawUnitTwoNumeratorCoefficient7 s
      + rawUnitOneNumeratorCoefficient7 s *
        rawUnitTwoNumeratorCoefficient6 s
    := by
  simp only [numeratorStep1Coefficient13,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep1Coefficient_product_certificate_14 (s : ℚ) :
    numeratorStep1Coefficient14 s =
    rawUnitOneNumeratorCoefficient7 s *
        rawUnitTwoNumeratorCoefficient7 s
    := by
  simp only [numeratorStep1Coefficient14,
    rawUnitOneNumeratorCoefficient7,
    rawUnitTwoNumeratorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem numeratorStep1_eq_rawUnitOneNumerator_mul_rawUnitTwoNumerator (r s : ℚ) :
    numeratorStep1 r s = rawUnitOneNumerator r s * rawUnitTwoNumerator r s := by
  have h0 := numeratorStep1Coefficient_product_certificate_0 s
  have h1 := numeratorStep1Coefficient_product_certificate_1 s
  have h2 := numeratorStep1Coefficient_product_certificate_2 s
  have h3 := numeratorStep1Coefficient_product_certificate_3 s
  have h4 := numeratorStep1Coefficient_product_certificate_4 s
  have h5 := numeratorStep1Coefficient_product_certificate_5 s
  have h6 := numeratorStep1Coefficient_product_certificate_6 s
  have h7 := numeratorStep1Coefficient_product_certificate_7 s
  have h8 := numeratorStep1Coefficient_product_certificate_8 s
  have h9 := numeratorStep1Coefficient_product_certificate_9 s
  have h10 := numeratorStep1Coefficient_product_certificate_10 s
  have h11 := numeratorStep1Coefficient_product_certificate_11 s
  have h12 := numeratorStep1Coefficient_product_certificate_12 s
  have h13 := numeratorStep1Coefficient_product_certificate_13 s
  have h14 := numeratorStep1Coefficient_product_certificate_14 s
  simp only [numeratorStep1, rawUnitOneNumerator, rawUnitTwoNumerator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient2 (s : ℚ) : ℚ :=
  s ^ 25
    - 6 * s ^ 24
    + 19 * s ^ 23
    - 42 * s ^ 22
    + 72 * s ^ 21
    - 102 * s ^ 20
    + 124 * s ^ 19
    - 132 * s ^ 18
    + 124 * s ^ 17
    - 102 * s ^ 16
    + 72 * s ^ 15
    - 42 * s ^ 14
    + 19 * s ^ 13
    - 6 * s ^ 12
    + s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient3 (s : ℚ) : ℚ :=
  s ^ 28
    - 9 * s ^ 27
    + 44 * s ^ 26
    - 146 * s ^ 25
    + 338 * s ^ 24
    - 569 * s ^ 23
    + 710 * s ^ 22
    - 632 * s ^ 21
    + 310 * s ^ 20
    + 179 * s ^ 19
    - 724 * s ^ 18
    + 1234 * s ^ 17
    - 1639 * s ^ 16
    + 1849 * s ^ 15
    - 1784 * s ^ 14
    + 1442 * s ^ 13
    - 946 * s ^ 12
    + 487 * s ^ 11
    - 188 * s ^ 10
    + 52 * s ^ 9
    - 10 * s ^ 8
    + s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient4 (s : ℚ) : ℚ :=
  s ^ 29
    - 7 * s ^ 28
    + s ^ 27
    + 166 * s ^ 26
    - 1037 * s ^ 25
    + 3757 * s ^ 24
    - 9498 * s ^ 23
    + 18279 * s ^ 22
    - 28400 * s ^ 21
    + 37413 * s ^ 20
    - 43974 * s ^ 19
    + 48246 * s ^ 18
    - 50685 * s ^ 17
    + 50618 * s ^ 16
    - 46265 * s ^ 15
    + 36744 * s ^ 14
    - 23751 * s ^ 13
    + 11223 * s ^ 12
    - 2728 * s ^ 11
    - 933 * s ^ 10
    + 1398 * s ^ 9
    - 805 * s ^ 8
    + 302 * s ^ 7
    - 76 * s ^ 6
    + 12 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 30
    + 20 * s ^ 29
    - 191 * s ^ 28
    + 1066 * s ^ 27
    - 3913 * s ^ 26
    + 10135 * s ^ 25
    - 18446 * s ^ 24
    + 21549 * s ^ 23
    - 10011 * s ^ 22
    - 15924 * s ^ 21
    + 37978 * s ^ 20
    - 28951 * s ^ 19
    - 21845 * s ^ 18
    + 92016 * s ^ 17
    - 135062 * s ^ 16
    + 112506 * s ^ 15
    - 26193 * s ^ 14
    - 79699 * s ^ 13
    + 149462 * s ^ 12
    - 156617 * s ^ 11
    + 117067 * s ^ 10
    - 65944 * s ^ 9
    + 28436 * s ^ 8
    - 9343 * s ^ 7
    + 2226 * s ^ 6
    - 350 * s ^ 5
    + 29 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 31
    + 16 * s ^ 30
    - 108 * s ^ 29
    + 313 * s ^ 28
    + 469 * s ^ 27
    - 8256 * s ^ 26
    + 39502 * s ^ 25
    - 119326 * s ^ 24
    + 254694 * s ^ 23
    - 388391 * s ^ 22
    + 396206 * s ^ 21
    - 173604 * s ^ 20
    - 228425 * s ^ 19
    + 545050 * s ^ 18
    - 418406 * s ^ 17
    - 365973 * s ^ 16
    + 1672844 * s ^ 15
    - 3011903 * s ^ 14
    + 3798037 * s ^ 13
    - 3713182 * s ^ 12
    + 2903635 * s ^ 11
    - 1830957 * s ^ 10
    + 927528 * s ^ 9
    - 373466 * s ^ 8
    + 116584 * s ^ 7
    - 26486 * s ^ 6
    + 3859 * s ^ 5
    - 236 * s ^ 4
    - 18 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient7 (s : ℚ) : ℚ :=
  -3 * s ^ 31
    + 69 * s ^ 30
    - 719 * s ^ 29
    + 4518 * s ^ 28
    - 18852 * s ^ 27
    + 53302 * s ^ 26
    - 94532 * s ^ 25
    + 48307 * s ^ 24
    + 303358 * s ^ 23
    - 1179465 * s ^ 22
    + 2423638 * s ^ 21
    - 3118321 * s ^ 20
    + 1616046 * s ^ 19
    + 3747587 * s ^ 18
    - 13508738 * s ^ 17
    + 26187601 * s ^ 16
    - 38277626 * s ^ 15
    + 45542078 * s ^ 14
    - 45209668 * s ^ 13
    + 37663921 * s ^ 12
    - 26262042 * s ^ 11
    + 15204219 * s ^ 10
    - 7212536 * s ^ 9
    + 2747416 * s ^ 8
    - 807671 * s ^ 7
    + 167170 * s ^ 6
    - 19053 * s ^ 5
    - 410 * s ^ 4
    + 430 * s ^ 3
    - 24 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient8 (s : ℚ) : ℚ :=
  -s ^ 32
    + 18 * s ^ 31
    - 122 * s ^ 30
    + 147 * s ^ 29
    + 3712 * s ^ 28
    - 34124 * s ^ 27
    + 168076 * s ^ 26
    - 561409 * s ^ 25
    + 1329365 * s ^ 24
    - 2055780 * s ^ 23
    + 873304 * s ^ 22
    + 6292512 * s ^ 21
    - 25276438 * s ^ 20
    + 61514524 * s ^ 19
    - 116573295 * s ^ 18
    + 184807746 * s ^ 17
    - 252141070 * s ^ 16
    + 298991905 * s ^ 15
    - 308296797 * s ^ 14
    + 275084926 * s ^ 13
    - 210662787 * s ^ 12
    + 137002678 * s ^ 11
    - 74621443 * s ^ 10
    + 33371733 * s ^ 9
    - 11858850 * s ^ 8
    + 3116943 * s ^ 7
    - 489269 * s ^ 6
    - 4543 * s ^ 5
    + 22973 * s ^ 4
    - 4908 * s ^ 3
    + 274 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient9 (s : ℚ) : ℚ :=
  -2 * s ^ 32
    + 52 * s ^ 31
    - 605 * s ^ 30
    + 4103 * s ^ 29
    - 16923 * s ^ 28
    + 32553 * s ^ 27
    + 87288 * s ^ 26
    - 1031862 * s ^ 25
    + 5019536 * s ^ 24
    - 17349826 * s ^ 23
    + 47792716 * s ^ 22
    - 110323932 * s ^ 21
    + 220030722 * s ^ 20
    - 386748911 * s ^ 19
    + 605665937 * s ^ 18
    - 847964967 * s ^ 17
    + 1058762005 * s ^ 16
    - 1171409750 * s ^ 15
    + 1138671063 * s ^ 14
    - 962795538 * s ^ 13
    + 700023389 * s ^ 12
    - 431540744 * s ^ 11
    + 221104894 * s ^ 10
    - 91043878 * s ^ 9
    + 28023872 * s ^ 8
    - 5045846 * s ^ 7
    - 376882 * s ^ 6
    + 600605 * s ^ 5
    - 199488 * s ^ 4
    + 32048 * s ^ 3
    - 1603 * s ^ 2
    - 27 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient10 (s : ℚ) : ℚ :=
  -3 * s ^ 32
    + 98 * s ^ 31
    - 1504 * s ^ 30
    + 14548 * s ^ 29
    - 100404 * s ^ 28
    + 530537 * s ^ 27
    - 2249528 * s ^ 26
    + 7922327 * s ^ 25
    - 23797847 * s ^ 24
    + 62251960 * s ^ 23
    - 144172562 * s ^ 22
    + 299529713 * s ^ 21
    - 562964740 * s ^ 20
    + 959047975 * s ^ 19
    - 1475219902 * s ^ 18
    + 2034250328 * s ^ 17
    - 2492805500 * s ^ 16
    + 2689708775 * s ^ 15
    - 2530897801 * s ^ 14
    + 2053888614 * s ^ 13
    - 1416874599 * s ^ 12
    + 812713143 * s ^ 11
    - 371721783 * s ^ 10
    + 122013516 * s ^ 9
    - 16997034 * s ^ 8
    - 10180365 * s ^ 7
    + 9045219 * s ^ 6
    - 3750039 * s ^ 5
    + 940839 * s ^ 4
    - 128659 * s ^ 3
    + 4269 * s ^ 2
    + 425 * s
    - 16

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient11 (s : ℚ) : ℚ :=
  -s ^ 33
    + 30 * s ^ 32
    - 437 * s ^ 31
    + 4116 * s ^ 30
    - 28298 * s ^ 29
    + 152578 * s ^ 28
    - 678539 * s ^ 27
    + 2584961 * s ^ 26
    - 8671290 * s ^ 25
    + 26069059 * s ^ 24
    - 70879275 * s ^ 23
    + 174718072 * s ^ 22
    - 389361606 * s ^ 21
    + 779141216 * s ^ 20
    - 1388511979 * s ^ 19
    + 2187347170 * s ^ 18
    - 3026400006 * s ^ 17
    + 3654241342 * s ^ 16
    - 3821774011 * s ^ 15
    + 3425616097 * s ^ 14
    - 2586376004 * s ^ 13
    + 1591835483 * s ^ 12
    - 738179614 * s ^ 11
    + 188324902 * s ^ 10
    + 60711213 * s ^ 9
    - 112480488 * s ^ 8
    + 80937355 * s ^ 7
    - 38726461 * s ^ 6
    + 12877618 * s ^ 5
    - 2810407 * s ^ 4
    + 316640 * s ^ 3
    + 3555 * s ^ 2
    - 3110 * s
    + 119

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient12 (s : ℚ) : ℚ :=
  s ^ 32
    - 20 * s ^ 31
    + 141 * s ^ 30
    + 174 * s ^ 29
    - 12250 * s ^ 28
    + 128777 * s ^ 27
    - 852102 * s ^ 26
    + 4222097 * s ^ 25
    - 16777344 * s ^ 24
    + 55410009 * s ^ 23
    - 155118826 * s ^ 22
    + 371886085 * s ^ 21
    - 767441931 * s ^ 20
    + 1366739874 * s ^ 19
    - 2101415311 * s ^ 18
    + 2781382938 * s ^ 17
    - 3143693387 * s ^ 16
    + 2982955984 * s ^ 15
    - 2287781682 * s ^ 14
    + 1277097682 * s ^ 13
    - 292093967 * s ^ 12
    - 387115938 * s ^ 11
    + 665279857 * s ^ 10
    - 626025564 * s ^ 9
    + 434653051 * s ^ 8
    - 234124245 * s ^ 7
    + 96378769 * s ^ 6
    - 28686747 * s ^ 5
    + 5448488 * s ^ 4
    - 384165 * s ^ 3
    - 73922 * s ^ 2
    + 14019 * s
    - 545

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient13 (s : ℚ) : ℚ :=
  s ^ 32
    - 32 * s ^ 31
    + 496 * s ^ 30
    - 4996 * s ^ 29
    + 36971 * s ^ 28
    - 215219 * s ^ 27
    + 1028191 * s ^ 26
    - 4138064 * s ^ 25
    + 14234388 * s ^ 24
    - 42105580 * s ^ 23
    + 107195353 * s ^ 22
    - 234498617 * s ^ 21
    + 439421520 * s ^ 20
    - 700687901 * s ^ 19
    + 935395345 * s ^ 18
    - 1003584130 * s ^ 17
    + 764994294 * s ^ 16
    - 171663709 * s ^ 15
    - 665791838 * s ^ 14
    + 1499334310 * s ^ 13
    - 2058709671 * s ^ 12
    + 2188965611 * s ^ 11
    - 1914115583 * s ^ 10
    + 1399201851 * s ^ 9
    - 850441122 * s ^ 8
    + 418928947 * s ^ 7
    - 158984797 * s ^ 6
    + 42386375 * s ^ 5
    - 6144124 * s ^ 4
    - 308329 * s ^ 3
    + 311789 * s ^ 2
    - 43445 * s
    + 1715

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient14 (s : ℚ) : ℚ :=
  -5 * s ^ 30
    + 144 * s ^ 29
    - 1987 * s ^ 28
    + 17405 * s ^ 27
    - 107896 * s ^ 26
    + 498554 * s ^ 25
    - 1754489 * s ^ 24
    + 4673970 * s ^ 23
    - 8875939 * s ^ 22
    + 8677559 * s ^ 21
    + 14054456 * s ^ 20
    - 97410807 * s ^ 19
    + 300080913 * s ^ 18
    - 684241918 * s ^ 17
    + 1276835784 * s ^ 16
    - 2026516728 * s ^ 15
    + 2787674056 * s ^ 14
    - 3355710035 * s ^ 13
    + 3549703114 * s ^ 12
    - 3296957382 * s ^ 11
    + 2669525051 * s ^ 10
    - 1856522544 * s ^ 9
    + 1080953698 * s ^ 8
    - 504455406 * s ^ 7
    + 174694312 * s ^ 6
    - 37465118 * s ^ 5
    + 872015 * s ^ 4
    + 2463496 * s ^ 3
    - 798096 * s ^ 2
    + 97738 * s
    - 3915

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient15 (s : ℚ) : ℚ :=
  -s ^ 30
    + 34 * s ^ 29
    - 553 * s ^ 28
    + 5764 * s ^ 27
    - 43379 * s ^ 26
    + 251398 * s ^ 25
    - 1168277 * s ^ 24
    + 4481926 * s ^ 23
    - 14542042 * s ^ 22
    + 40800994 * s ^ 21
    - 100955369 * s ^ 20
    + 223437952 * s ^ 19
    - 445445789 * s ^ 18
    + 801399812 * s ^ 17
    - 1301380046 * s ^ 16
    + 1906946745 * s ^ 15
    - 2517396952 * s ^ 14
    + 2983404925 * s ^ 13
    - 3155046192 * s ^ 12
    + 2947132628 * s ^ 11
    - 2392797524 * s ^ 10
    + 1648648480 * s ^ 9
    - 928129820 * s ^ 8
    + 398767271 * s ^ 7
    - 111286569 * s ^ 6
    + 6492289 * s ^ 5
    + 10961758 * s ^ 4
    - 5812214 * s ^ 3
    + 1430232 * s ^ 2
    - 164148 * s
    + 6667

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient16 (s : ℚ) : ℚ :=
  2 * s ^ 28
    - 60 * s ^ 27
    + 881 * s ^ 26
    - 8518 * s ^ 25
    + 61298 * s ^ 24
    - 349773 * s ^ 23
    + 1635977 * s ^ 22
    - 6377794 * s ^ 21
    + 20928767 * s ^ 20
    - 58369704 * s ^ 19
    + 140050305 * s ^ 18
    - 292963963 * s ^ 17
    + 540039602 * s ^ 16
    - 881953663 * s ^ 15
    + 1276459673 * s ^ 14
    - 1631514897 * s ^ 13
    + 1827362891 * s ^ 12
    - 1769344040 * s ^ 11
    + 1449973224 * s ^ 10
    - 971618492 * s ^ 9
    + 497782193 * s ^ 8
    - 162394402 * s ^ 7
    + 2509994 * s ^ 6
    + 34355689 * s ^ 5
    - 23195360 * s ^ 4
    + 8608850 * s ^ 3
    - 1878318 * s ^ 2
    + 208207 * s
    - 8569

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient17 (s : ℚ) : ℚ :=
  s ^ 27
    - 35 * s ^ 26
    + 571 * s ^ 25
    - 5829 * s ^ 24
    + 42120 * s ^ 23
    - 231343 * s ^ 22
    + 1015800 * s ^ 21
    - 3711159 * s ^ 20
    + 11627904 * s ^ 19
    - 31794648 * s ^ 18
    + 76200210 * s ^ 17
    - 159531052 * s ^ 16
    + 290423876 * s ^ 15
    - 458041490 * s ^ 14
    + 622367007 * s ^ 13
    - 720317786 * s ^ 12
    + 695590574 * s ^ 11
    - 539294751 * s ^ 10
    + 306797179 * s ^ 9
    - 89525747 * s ^ 8
    - 41527114 * s ^ 7
    + 76755189 * s ^ 6
    - 56950205 * s ^ 5
    + 27387117 * s ^ 4
    - 8915561 * s ^ 3
    + 1830078 * s ^ 2
    - 199210 * s
    + 8304

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient18 (s : ℚ) : ℚ :=
  -2 * s ^ 25
    + 66 * s ^ 24
    - 1039 * s ^ 23
    + 10369 * s ^ 22
    - 73372 * s ^ 21
    + 390217 * s ^ 20
    - 1617265 * s ^ 19
    + 5364181 * s ^ 18
    - 14559274 * s ^ 17
    + 32945636 * s ^ 16
    - 62916291 * s ^ 15
    + 101504781 * s ^ 14
    - 136423481 * s ^ 13
    + 147492455 * s ^ 12
    - 117788485 * s ^ 11
    + 48837973 * s ^ 10
    + 33948396 * s ^ 9
    - 94140481 * s ^ 8
    + 109215595 * s ^ 7
    - 85991714 * s ^ 6
    + 49838438 * s ^ 5
    - 21451588 * s ^ 4
    + 6591405 * s ^ 3
    - 1312310 * s ^ 2
    + 141775 * s
    - 5985

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient19 (s : ℚ) : ℚ :=
  s ^ 22
    - 4 * s ^ 21
    - 271 * s ^ 20
    + 4696 * s ^ 19
    - 38410 * s ^ 18
    + 192947 * s ^ 17
    - 636314 * s ^ 16
    + 1332803 * s ^ 15
    - 1243879 * s ^ 14
    - 2420290 * s ^ 13
    + 13414216 * s ^ 12
    - 33488723 * s ^ 11
    + 58975163 * s ^ 10
    - 80206037 * s ^ 9
    + 86444281 * s ^ 8
    - 74241076 * s ^ 7
    + 50744152 * s ^ 6
    - 27375674 * s ^ 5
    + 11359620 * s ^ 4
    - 3421266 * s ^ 3
    + 673767 * s ^ 2
    - 72816 * s
    + 3114

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient20 (s : ℚ) : ℚ :=
  2 * s ^ 21
    - 64 * s ^ 20
    + 944 * s ^ 19
    - 8549 * s ^ 18
    + 53444 * s ^ 17
    - 246167 * s ^ 16
    + 872889 * s ^ 15
    - 2466539 * s ^ 14
    + 5721660 * s ^ 13
    - 11159681 * s ^ 12
    + 18551366 * s ^ 11
    - 26288620 * s ^ 10
    + 31436178 * s ^ 9
    - 31315577 * s ^ 8
    + 25724300 * s ^ 7
    - 17272594 * s ^ 6
    + 9325466 * s ^ 5
    - 3902823 * s ^ 4
    + 1184291 * s ^ 3
    - 234328 * s ^ 2
    + 25508 * s
    - 1106

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient21 (s : ℚ) : ℚ :=
  -s ^ 19
    + 31 * s ^ 18
    - 447 * s ^ 17
    + 3980 * s ^ 16
    - 24481 * s ^ 15
    + 110234 * s ^ 14
    - 375795 * s ^ 13
    + 990601 * s ^ 12
    - 2048935 * s ^ 11
    + 3365920 * s ^ 10
    - 4444968 * s ^ 9
    + 4777368 * s ^ 8
    - 4216569 * s ^ 7
    + 3048107 * s ^ 6
    - 1763564 * s ^ 5
    + 779105 * s ^ 4
    - 244764 * s ^ 3
    + 49390 * s ^ 2
    - 5452 * s
    + 240

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep2Coefficient22 (s : ℚ) : ℚ :=
  s ^ 15
    - 26 * s ^ 14
    + 306 * s ^ 13
    - 2158 * s ^ 12
    + 10175 * s ^ 11
    - 33888 * s ^ 10
    + 82114 * s ^ 9
    - 146889 * s ^ 8
    + 194738 * s ^ 7
    - 190290 * s ^ 6
    + 134942 * s ^ 5
    - 67507 * s ^ 4
    + 22724 * s ^ 3
    - 4754 * s ^ 2
    + 536 * s
    - 24

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def numeratorStep2 (r s : ℚ) : ℚ :=
  numeratorStep2Coefficient0 s +
    numeratorStep2Coefficient1 s * r +
    numeratorStep2Coefficient2 s * r ^ 2 +
    numeratorStep2Coefficient3 s * r ^ 3 +
    numeratorStep2Coefficient4 s * r ^ 4 +
    numeratorStep2Coefficient5 s * r ^ 5 +
    numeratorStep2Coefficient6 s * r ^ 6 +
    numeratorStep2Coefficient7 s * r ^ 7 +
    numeratorStep2Coefficient8 s * r ^ 8 +
    numeratorStep2Coefficient9 s * r ^ 9 +
    numeratorStep2Coefficient10 s * r ^ 10 +
    numeratorStep2Coefficient11 s * r ^ 11 +
    numeratorStep2Coefficient12 s * r ^ 12 +
    numeratorStep2Coefficient13 s * r ^ 13 +
    numeratorStep2Coefficient14 s * r ^ 14 +
    numeratorStep2Coefficient15 s * r ^ 15 +
    numeratorStep2Coefficient16 s * r ^ 16 +
    numeratorStep2Coefficient17 s * r ^ 17 +
    numeratorStep2Coefficient18 s * r ^ 18 +
    numeratorStep2Coefficient19 s * r ^ 19 +
    numeratorStep2Coefficient20 s * r ^ 20 +
    numeratorStep2Coefficient21 s * r ^ 21 +
    numeratorStep2Coefficient22 s * r ^ 22

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_0 (s : ℚ) :
    numeratorStep2Coefficient0 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient0,
    numeratorStep1Coefficient0,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_1 (s : ℚ) :
    numeratorStep2Coefficient1 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient1,
    numeratorStep1Coefficient0,
    numeratorStep1Coefficient1,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_2 (s : ℚ) :
    numeratorStep2Coefficient2 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient2,
    numeratorStep1Coefficient0,
    numeratorStep1Coefficient1,
    numeratorStep1Coefficient2,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_3 (s : ℚ) :
    numeratorStep2Coefficient3 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient3,
    numeratorStep1Coefficient0,
    numeratorStep1Coefficient1,
    numeratorStep1Coefficient2,
    numeratorStep1Coefficient3,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_4 (s : ℚ) :
    numeratorStep2Coefficient4 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient4,
    numeratorStep1Coefficient0,
    numeratorStep1Coefficient1,
    numeratorStep1Coefficient2,
    numeratorStep1Coefficient3,
    numeratorStep1Coefficient4,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_5 (s : ℚ) :
    numeratorStep2Coefficient5 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient5,
    numeratorStep1Coefficient0,
    numeratorStep1Coefficient1,
    numeratorStep1Coefficient2,
    numeratorStep1Coefficient3,
    numeratorStep1Coefficient4,
    numeratorStep1Coefficient5,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_6 (s : ℚ) :
    numeratorStep2Coefficient6 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient6,
    numeratorStep1Coefficient0,
    numeratorStep1Coefficient1,
    numeratorStep1Coefficient2,
    numeratorStep1Coefficient3,
    numeratorStep1Coefficient4,
    numeratorStep1Coefficient5,
    numeratorStep1Coefficient6,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_7 (s : ℚ) :
    numeratorStep2Coefficient7 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient7,
    numeratorStep1Coefficient0,
    numeratorStep1Coefficient1,
    numeratorStep1Coefficient2,
    numeratorStep1Coefficient3,
    numeratorStep1Coefficient4,
    numeratorStep1Coefficient5,
    numeratorStep1Coefficient6,
    numeratorStep1Coefficient7,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_8 (s : ℚ) :
    numeratorStep2Coefficient8 s =
    numeratorStep1Coefficient0 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient8,
    numeratorStep1Coefficient0,
    numeratorStep1Coefficient1,
    numeratorStep1Coefficient2,
    numeratorStep1Coefficient3,
    numeratorStep1Coefficient4,
    numeratorStep1Coefficient5,
    numeratorStep1Coefficient6,
    numeratorStep1Coefficient7,
    numeratorStep1Coefficient8,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_9 (s : ℚ) :
    numeratorStep2Coefficient9 s =
    numeratorStep1Coefficient1 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient9,
    numeratorStep1Coefficient1,
    numeratorStep1Coefficient2,
    numeratorStep1Coefficient3,
    numeratorStep1Coefficient4,
    numeratorStep1Coefficient5,
    numeratorStep1Coefficient6,
    numeratorStep1Coefficient7,
    numeratorStep1Coefficient8,
    numeratorStep1Coefficient9,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_10 (s : ℚ) :
    numeratorStep2Coefficient10 s =
    numeratorStep1Coefficient2 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient10,
    numeratorStep1Coefficient2,
    numeratorStep1Coefficient3,
    numeratorStep1Coefficient4,
    numeratorStep1Coefficient5,
    numeratorStep1Coefficient6,
    numeratorStep1Coefficient7,
    numeratorStep1Coefficient8,
    numeratorStep1Coefficient9,
    numeratorStep1Coefficient10,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_11 (s : ℚ) :
    numeratorStep2Coefficient11 s =
    numeratorStep1Coefficient3 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient11,
    numeratorStep1Coefficient3,
    numeratorStep1Coefficient4,
    numeratorStep1Coefficient5,
    numeratorStep1Coefficient6,
    numeratorStep1Coefficient7,
    numeratorStep1Coefficient8,
    numeratorStep1Coefficient9,
    numeratorStep1Coefficient10,
    numeratorStep1Coefficient11,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_12 (s : ℚ) :
    numeratorStep2Coefficient12 s =
    numeratorStep1Coefficient4 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient12,
    numeratorStep1Coefficient4,
    numeratorStep1Coefficient5,
    numeratorStep1Coefficient6,
    numeratorStep1Coefficient7,
    numeratorStep1Coefficient8,
    numeratorStep1Coefficient9,
    numeratorStep1Coefficient10,
    numeratorStep1Coefficient11,
    numeratorStep1Coefficient12,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_13 (s : ℚ) :
    numeratorStep2Coefficient13 s =
    numeratorStep1Coefficient5 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient13,
    numeratorStep1Coefficient5,
    numeratorStep1Coefficient6,
    numeratorStep1Coefficient7,
    numeratorStep1Coefficient8,
    numeratorStep1Coefficient9,
    numeratorStep1Coefficient10,
    numeratorStep1Coefficient11,
    numeratorStep1Coefficient12,
    numeratorStep1Coefficient13,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_14 (s : ℚ) :
    numeratorStep2Coefficient14 s =
    numeratorStep1Coefficient6 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient1 s
      + numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient0 s
    := by
  simp only [numeratorStep2Coefficient14,
    numeratorStep1Coefficient6,
    numeratorStep1Coefficient7,
    numeratorStep1Coefficient8,
    numeratorStep1Coefficient9,
    numeratorStep1Coefficient10,
    numeratorStep1Coefficient11,
    numeratorStep1Coefficient12,
    numeratorStep1Coefficient13,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_15 (s : ℚ) :
    numeratorStep2Coefficient15 s =
    numeratorStep1Coefficient7 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient2 s
      + numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient1 s
    := by
  simp only [numeratorStep2Coefficient15,
    numeratorStep1Coefficient7,
    numeratorStep1Coefficient8,
    numeratorStep1Coefficient9,
    numeratorStep1Coefficient10,
    numeratorStep1Coefficient11,
    numeratorStep1Coefficient12,
    numeratorStep1Coefficient13,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_16 (s : ℚ) :
    numeratorStep2Coefficient16 s =
    numeratorStep1Coefficient8 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient3 s
      + numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient2 s
    := by
  simp only [numeratorStep2Coefficient16,
    numeratorStep1Coefficient8,
    numeratorStep1Coefficient9,
    numeratorStep1Coefficient10,
    numeratorStep1Coefficient11,
    numeratorStep1Coefficient12,
    numeratorStep1Coefficient13,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_17 (s : ℚ) :
    numeratorStep2Coefficient17 s =
    numeratorStep1Coefficient9 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient4 s
      + numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient3 s
    := by
  simp only [numeratorStep2Coefficient17,
    numeratorStep1Coefficient9,
    numeratorStep1Coefficient10,
    numeratorStep1Coefficient11,
    numeratorStep1Coefficient12,
    numeratorStep1Coefficient13,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_18 (s : ℚ) :
    numeratorStep2Coefficient18 s =
    numeratorStep1Coefficient10 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient5 s
      + numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient4 s
    := by
  simp only [numeratorStep2Coefficient18,
    numeratorStep1Coefficient10,
    numeratorStep1Coefficient11,
    numeratorStep1Coefficient12,
    numeratorStep1Coefficient13,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_19 (s : ℚ) :
    numeratorStep2Coefficient19 s =
    numeratorStep1Coefficient11 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient6 s
      + numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient5 s
    := by
  simp only [numeratorStep2Coefficient19,
    numeratorStep1Coefficient11,
    numeratorStep1Coefficient12,
    numeratorStep1Coefficient13,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_20 (s : ℚ) :
    numeratorStep2Coefficient20 s =
    numeratorStep1Coefficient12 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient7 s
      + numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient6 s
    := by
  simp only [numeratorStep2Coefficient20,
    numeratorStep1Coefficient12,
    numeratorStep1Coefficient13,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_21 (s : ℚ) :
    numeratorStep2Coefficient21 s =
    numeratorStep1Coefficient13 s *
        rawUnitFourNumeratorCoefficient8 s
      + numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient7 s
    := by
  simp only [numeratorStep2Coefficient21,
    numeratorStep1Coefficient13,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep2Coefficient_product_certificate_22 (s : ℚ) :
    numeratorStep2Coefficient22 s =
    numeratorStep1Coefficient14 s *
        rawUnitFourNumeratorCoefficient8 s
    := by
  simp only [numeratorStep2Coefficient22,
    numeratorStep1Coefficient14,
    rawUnitFourNumeratorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem numeratorStep2_eq_numeratorStep1_mul_rawUnitFourNumerator (r s : ℚ) :
    numeratorStep2 r s = numeratorStep1 r s * rawUnitFourNumerator r s := by
  have h0 := numeratorStep2Coefficient_product_certificate_0 s
  have h1 := numeratorStep2Coefficient_product_certificate_1 s
  have h2 := numeratorStep2Coefficient_product_certificate_2 s
  have h3 := numeratorStep2Coefficient_product_certificate_3 s
  have h4 := numeratorStep2Coefficient_product_certificate_4 s
  have h5 := numeratorStep2Coefficient_product_certificate_5 s
  have h6 := numeratorStep2Coefficient_product_certificate_6 s
  have h7 := numeratorStep2Coefficient_product_certificate_7 s
  have h8 := numeratorStep2Coefficient_product_certificate_8 s
  have h9 := numeratorStep2Coefficient_product_certificate_9 s
  have h10 := numeratorStep2Coefficient_product_certificate_10 s
  have h11 := numeratorStep2Coefficient_product_certificate_11 s
  have h12 := numeratorStep2Coefficient_product_certificate_12 s
  have h13 := numeratorStep2Coefficient_product_certificate_13 s
  have h14 := numeratorStep2Coefficient_product_certificate_14 s
  have h15 := numeratorStep2Coefficient_product_certificate_15 s
  have h16 := numeratorStep2Coefficient_product_certificate_16 s
  have h17 := numeratorStep2Coefficient_product_certificate_17 s
  have h18 := numeratorStep2Coefficient_product_certificate_18 s
  have h19 := numeratorStep2Coefficient_product_certificate_19 s
  have h20 := numeratorStep2Coefficient_product_certificate_20 s
  have h21 := numeratorStep2Coefficient_product_certificate_21 s
  have h22 := numeratorStep2Coefficient_product_certificate_22 s
  simp only [numeratorStep2, numeratorStep1, rawUnitFourNumerator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 29
    + 7 * s ^ 28
    - 26 * s ^ 27
    + 68 * s ^ 26
    - 139 * s ^ 25
    + 235 * s ^ 24
    - 340 * s ^ 23
    + 430 * s ^ 22
    - 482 * s ^ 21
    + 482 * s ^ 20
    - 430 * s ^ 19
    + 340 * s ^ 18
    - 235 * s ^ 17
    + 139 * s ^ 16
    - 68 * s ^ 15
    + 26 * s ^ 14
    - 7 * s ^ 13
    + s ^ 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient3 (s : ℚ) : ℚ :=
  -s ^ 32
    + 10 * s ^ 31
    - 54 * s ^ 30
    + 200 * s ^ 29
    - 535 * s ^ 28
    + 1086 * s ^ 27
    - 1733 * s ^ 26
    + 2195 * s ^ 25
    - 2151 * s ^ 24
    + 1406 * s ^ 23
    + 5 * s ^ 22
    - 1835 * s ^ 21
    + 3746 * s ^ 20
    - 5386 * s ^ 19
    + 6432 * s ^ 18
    - 6646 * s ^ 17
    + 5975 * s ^ 16
    - 4640 * s ^ 15
    + 3063 * s ^ 14
    - 1679 * s ^ 13
    + 741 * s ^ 12
    - 252 * s ^ 11
    + 63 * s ^ 10
    - 11 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 33
    + 8 * s ^ 32
    - 7 * s ^ 31
    - 174 * s ^ 30
    + 1272 * s ^ 29
    - 5189 * s ^ 28
    + 14898 * s ^ 27
    - 33073 * s ^ 26
    + 60115 * s ^ 25
    - 93061 * s ^ 24
    + 126756 * s ^ 23
    - 156231 * s ^ 22
    + 178423 * s ^ 21
    - 191845 * s ^ 20
    + 194557 * s ^ 19
    - 183687 * s ^ 18
    + 157571 * s ^ 17
    - 118947 * s ^ 16
    + 75788 * s ^ 15
    - 37917 * s ^ 14
    + 12227 * s ^ 13
    + 279 * s ^ 12
    - 3514 * s ^ 11
    + 2657 * s ^ 10
    - 1226 * s ^ 9
    + 399 * s ^ 8
    - 90 * s ^ 7
    + 13 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient5 (s : ℚ) : ℚ :=
  s ^ 34
    - 21 * s ^ 33
    + 214 * s ^ 32
    - 1290 * s ^ 31
    + 5169 * s ^ 30
    - 14869 * s ^ 29
    + 31285 * s ^ 28
    - 46815 * s ^ 27
    + 44547 * s ^ 26
    - 10090 * s ^ 25
    - 49225 * s ^ 24
    + 94384 * s ^ 23
    - 72379 * s ^ 22
    - 44793 * s ^ 21
    + 224280 * s ^ 20
    - 372416 * s ^ 19
    + 387089 * s ^ 18
    - 227208 * s ^ 17
    - 51378 * s ^ 16
    + 326261 * s ^ 15
    - 484805 * s ^ 14
    + 486476 * s ^ 13
    - 373305 * s ^ 12
    + 226172 * s ^ 11
    - 108474 * s ^ 10
    + 40858 * s ^ 9
    - 11828 * s ^ 8
    + 2468 * s ^ 7
    - 328 * s ^ 6
    + 19 * s ^ 5
    + s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient6 (s : ℚ) : ℚ :=
  s ^ 35
    - 17 * s ^ 34
    + 123 * s ^ 33
    - 398 * s ^ 32
    - 404 * s ^ 31
    + 10242 * s ^ 30
    - 54142 * s ^ 29
    + 179999 * s ^ 28
    - 432315 * s ^ 27
    + 780332 * s ^ 26
    - 1061559 * s ^ 25
    + 1024362 * s ^ 24
    - 496894 * s ^ 23
    - 391300 * s ^ 22
    + 1108890 * s ^ 21
    - 866937 * s ^ 20
    - 965128 * s ^ 19
    + 4363522 * s ^ 18
    - 8456004 * s ^ 17
    + 11832640 * s ^ 16
    - 13253850 * s ^ 15
    + 12307334 * s ^ 14
    - 9572930 * s ^ 13
    + 6226515 * s ^ 12
    - 3354301 * s ^ 11
    + 1472343 * s ^ 10
    - 514608 * s ^ 9
    + 137254 * s ^ 8
    - 25198 * s ^ 7
    + 2368 * s ^ 6
    + 110 * s ^ 5
    - 51 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient7 (s : ℚ) : ℚ :=
  3 * s ^ 35
    - 74 * s ^ 34
    + 821 * s ^ 33
    - 5482 * s ^ 32
    + 24352 * s ^ 31
    - 73891 * s ^ 30
    + 145237 * s ^ 29
    - 115444 * s ^ 28
    - 358462 * s ^ 27
    + 1763070 * s ^ 26
    - 4259252 * s ^ 25
    + 6971541 * s ^ 24
    - 7464140 * s ^ 23
    + 1905295 * s ^ 22
    + 13726577 * s ^ 21
    - 41539345 * s ^ 20
    + 79381276 * s ^ 19
    - 119828365 * s ^ 18
    + 151969418 * s ^ 17
    - 165703909 * s ^ 16
    + 156569148 * s ^ 15
    - 128108597 * s ^ 14
    + 90142156 * s ^ 13
    - 53899360 * s ^ 12
    + 26919143 * s ^ 11
    - 10956260 * s ^ 10
    + 3496155 * s ^ 9
    - 803770 * s ^ 8
    + 99912 * s ^ 7
    + 6767 * s ^ 6
    - 5328 * s ^ 5
    + 817 * s ^ 4
    - 8 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient8 (s : ℚ) : ℚ :=
  s ^ 36
    - 19 * s ^ 35
    + 134 * s ^ 34
    - 132 * s ^ 33
    - 4976 * s ^ 32
    + 46591 * s ^ 31
    - 238464 * s ^ 30
    + 834254 * s ^ 29
    - 2104610 * s ^ 28
    + 3676290 * s ^ 27
    - 3092290 * s ^ 26
    - 5880136 * s ^ 25
    + 34039076 * s ^ 24
    - 95835312 * s ^ 23
    + 205901716 * s ^ 22
    - 372316955 * s ^ 21
    + 587552189 * s ^ 20
    - 821265483 * s ^ 19
    + 1022427870 * s ^ 18
    - 1134500748 * s ^ 17
    + 1118840688 * s ^ 16
    - 974794873 * s ^ 15
    + 743231123 * s ^ 14
    - 489305060 * s ^ 13
    + 273148495 * s ^ 12
    - 125960164 * s ^ 11
    + 45964880 * s ^ 10
    - 12095515 * s ^ 9
    + 1583255 * s ^ 8
    + 337631 * s ^ 7
    - 243856 * s ^ 6
    + 61008 * s ^ 5
    - 6474 * s ^ 4
    - 161 * s ^ 3
    + 27 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient9 (s : ℚ) : ℚ :=
  2 * s ^ 36
    - 56 * s ^ 35
    + 691 * s ^ 34
    - 4901 * s ^ 33
    + 20733 * s ^ 32
    - 38039 * s ^ 31
    - 141164 * s ^ 30
    + 1515161 * s ^ 29
    - 7353486 * s ^ 28
    + 25727585 * s ^ 27
    - 72592094 * s ^ 26
    + 174297469 * s ^ 25
    - 368722286 * s ^ 24
    + 702725335 * s ^ 23
    - 1219458725 * s ^ 22
    + 1931204176 * s ^ 21
    - 2784775761 * s ^ 20
    + 3641571228 * s ^ 19
    - 4298431651 * s ^ 18
    + 4554221138 * s ^ 17
    - 4298703108 * s ^ 16
    + 3577949055 * s ^ 15
    - 2589219093 * s ^ 14
    + 1597112217 * s ^ 13
    - 814852801 * s ^ 12
    + 325378659 * s ^ 11
    - 88051882 * s ^ 10
    + 5498904 * s ^ 9
    + 9450632 * s ^ 8
    - 5926568 * s ^ 7
    + 1925323 * s ^ 6
    - 351121 * s ^ 5
    + 20695 * s ^ 4
    + 4109 * s ^ 3
    - 377 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient10 (s : ℚ) : ℚ :=
  3 * s ^ 36
    - 106 * s ^ 35
    + 1730 * s ^ 34
    - 17517 * s ^ 33
    + 124744 * s ^ 32
    - 671665 * s ^ 31
    + 2875095 * s ^ 30
    - 10183994 * s ^ 29
    + 30908579 * s ^ 28
    - 82855171 * s ^ 27
    + 201094889 * s ^ 26
    - 449552878 * s ^ 25
    + 931850226 * s ^ 24
    - 1784297690 * s ^ 23
    + 3129310784 * s ^ 22
    - 4988542555 * s ^ 21
    + 7189957799 * s ^ 20
    - 9331567000 * s ^ 19
    + 10857188708 * s ^ 18
    - 11248347267 * s ^ 17
    + 10270429492 * s ^ 16
    - 8138252934 * s ^ 15
    + 5464442374 * s ^ 14
    - 2982401349 * s ^ 13
    + 1203769828 * s ^ 12
    - 241732532 * s ^ 11
    - 106591612 * s ^ 10
    + 140792421 * s ^ 9
    - 82682221 * s ^ 8
    + 31883989 * s ^ 7
    - 7952961 * s ^ 6
    + 989802 * s ^ 5
    + 66863 * s ^ 4
    - 40875 * s ^ 3
    + 2993 * s ^ 2
    + 9 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient11 (s : ℚ) : ℚ :=
  s ^ 37
    - 31 * s ^ 36
    + 460 * s ^ 35
    - 4328 * s ^ 34
    + 29088 * s ^ 33
    - 150659 * s ^ 32
    + 641605 * s ^ 31
    - 2394600 * s ^ 30
    + 8273549 * s ^ 29
    - 27171619 * s ^ 28
    + 84199615 * s ^ 27
    - 240523482 * s ^ 26
    + 620131478 * s ^ 25
    - 1424582627 * s ^ 24
    + 2902187934 * s ^ 23
    - 5250139356 * s ^ 22
    + 8463379915 * s ^ 21
    - 12182841645 * s ^ 20
    + 15638155232 * s ^ 19
    - 17789795152 * s ^ 18
    + 17715888793 * s ^ 17
    - 15125921179 * s ^ 16
    + 10667428504 * s ^ 15
    - 5715590899 * s ^ 14
    + 1692295732 * s ^ 13
    + 637022338 * s ^ 12
    - 1380193898 * s ^ 11
    + 1179508213 * s ^ 10
    - 696054253 * s ^ 9
    + 304299122 * s ^ 8
    - 94529855 * s ^ 7
    + 17065599 * s ^ 6
    + 178771 * s ^ 5
    - 1015799 * s ^ 4
    + 237795 * s ^ 3
    - 14027 * s ^ 2
    - 354 * s
    + 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient12 (s : ℚ) : ℚ :=
  -3 * s ^ 36
    + 77 * s ^ 35
    - 889 * s ^ 34
    + 5667 * s ^ 33
    - 16397 * s ^ 32
    - 53030 * s ^ 31
    + 919026 * s ^ 30
    - 6072228 * s ^ 29
    + 27920186 * s ^ 28
    - 101070151 * s ^ 27
    + 303602494 * s ^ 26
    - 779041895 * s ^ 25
    + 1740541516 * s ^ 24
    - 3435308472 * s ^ 23
    + 6049784703 * s ^ 22
    - 9536710302 * s ^ 21
    + 13393411256 * s ^ 20
    - 16544804972 * s ^ 19
    + 17566667366 * s ^ 18
    - 15363296751 * s ^ 17
    + 10001173900 * s ^ 16
    - 3018400719 * s ^ 15
    - 3229529361 * s ^ 14
    + 6857027279 * s ^ 13
    - 7423429597 * s ^ 12
    + 5866801482 * s ^ 11
    - 3625395829 * s ^ 10
    + 1760840534 * s ^ 9
    - 641029415 * s ^ 8
    + 145895103 * s ^ 7
    - 1366062 * s ^ 6
    - 13481871 * s ^ 5
    + 5279980 * s ^ 4
    - 901486 * s ^ 3
    + 35360 * s ^ 2
    + 3671 * s
    - 170

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient13 (s : ℚ) : ℚ :=
  -2 * s ^ 36
    + 70 * s ^ 35
    - 1153 * s ^ 34
    + 12003 * s ^ 33
    - 89287 * s ^ 32
    + 509109 * s ^ 31
    - 2334833 * s ^ 30
    + 8936887 * s ^ 29
    - 29413086 * s ^ 28
    + 85211862 * s ^ 27
    - 221128041 * s ^ 26
    + 520498193 * s ^ 25
    - 1119660521 * s ^ 24
    + 2198686909 * s ^ 23
    - 3888443081 * s ^ 22
    + 6037463314 * s ^ 21
    - 7923267087 * s ^ 20
    + 8201503134 * s ^ 19
    - 5415454978 * s ^ 18
    - 969225972 * s ^ 17
    + 9691010138 * s ^ 16
    - 17889880878 * s ^ 15
    + 22546623366 * s ^ 14
    - 22240405626 * s ^ 13
    + 17861890429 * s ^ 12
    - 11772141311 * s ^ 11
    + 6269974710 * s ^ 10
    - 2552996890 * s ^ 9
    + 650275194 * s ^ 8
    + 23729086 * s ^ 7
    - 118424478 * s ^ 6
    + 61162135 * s ^ 5
    - 16868208 * s ^ 4
    + 2273659 * s ^ 3
    - 3952 * s ^ 2
    - 21764 * s
    + 950

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient14 (s : ℚ) : ℚ :=
  4 * s ^ 35
    - 117 * s ^ 34
    + 1611 * s ^ 33
    - 13799 * s ^ 32
    + 81479 * s ^ 31
    - 344033 * s ^ 30
    + 1012405 * s ^ 29
    - 1658343 * s ^ 28
    - 1852209 * s ^ 27
    + 25527535 * s ^ 26
    - 111138086 * s ^ 25
    + 332463746 * s ^ 24
    - 748918374 * s ^ 23
    + 1246716262 * s ^ 22
    - 1292190236 * s ^ 21
    - 194333215 * s ^ 20
    + 4533497869 * s ^ 19
    - 12425151647 * s ^ 18
    + 22932917982 * s ^ 17
    - 33215948279 * s ^ 16
    + 39612873258 * s ^ 15
    - 39612632070 * s ^ 14
    + 33356235752 * s ^ 13
    - 23471264602 * s ^ 12
    + 13424882012 * s ^ 11
    - 5760722166 * s ^ 10
    + 1310791687 * s ^ 9
    + 480055991 * s ^ 8
    - 728000547 * s ^ 7
    + 435698941 * s ^ 6
    - 161226165 * s ^ 5
    + 36388080 * s ^ 4
    - 3484660 * s ^ 3
    - 349777 * s ^ 2
    + 87418 * s
    - 3707

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient15 (s : ℚ) : ℚ :=
  s ^ 35
    - 37 * s ^ 34
    + 636 * s ^ 33
    - 6858 * s ^ 32
    + 52629 * s ^ 31
    - 308789 * s ^ 30
    + 1452319 * s ^ 29
    - 5654158 * s ^ 28
    + 18533389 * s ^ 27
    - 50961091 * s ^ 26
    + 113297050 * s ^ 25
    - 181120845 * s ^ 24
    + 104329824 * s ^ 23
    + 531028457 * s ^ 22
    - 2482679708 * s ^ 21
    + 6691744238 * s ^ 20
    - 13759510979 * s ^ 19
    + 23198766604 * s ^ 18
    - 32984836669 * s ^ 17
    + 40017544924 * s ^ 16
    - 41521372436 * s ^ 15
    + 36606218136 * s ^ 14
    - 26877431652 * s ^ 13
    + 15562554721 * s ^ 12
    - 5850227284 * s ^ 11
    - 404210156 * s ^ 10
    + 3039220457 * s ^ 9
    - 3098613400 * s ^ 8
    + 2014641411 * s ^ 7
    - 919164492 * s ^ 6
    + 286063537 * s ^ 5
    - 51966181 * s ^ 4
    + 1272181 * s ^ 3
    + 1589624 * s ^ 2
    - 256098 * s
    + 10695

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient16 (s : ℚ) : ℚ :=
  -s ^ 34
    + 29 * s ^ 33
    - 393 * s ^ 32
    + 3356 * s ^ 31
    - 21009 * s ^ 30
    + 111154 * s ^ 29
    - 572817 * s ^ 28
    + 3009853 * s ^ 27
    - 14969344 * s ^ 26
    + 64860548 * s ^ 25
    - 235881020 * s ^ 24
    + 716214057 * s ^ 23
    - 1831501373 * s ^ 22
    + 3995060770 * s ^ 21
    - 7516295705 * s ^ 20
    + 12274223958 * s ^ 19
    - 17416468968 * s ^ 18
    + 21390241957 * s ^ 17
    - 22486327241 * s ^ 16
    + 19694707827 * s ^ 15
    - 13373127280 * s ^ 14
    + 5221601431 * s ^ 13
    + 2470673624 * s ^ 12
    - 7767722122 * s ^ 11
    + 9763024193 * s ^ 10
    - 8797805387 * s ^ 9
    + 6138432901 * s ^ 8
    - 3297014938 * s ^ 7
    + 1303042792 * s ^ 6
    - 341324497 * s ^ 5
    + 38523576 * s ^ 4
    + 9021217 * s ^ 3
    - 4266330 * s ^ 2
    + 568739 * s
    - 23557

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient17 (s : ℚ) : ℚ :=
  -s ^ 33
    + 44 * s ^ 32
    - 885 * s ^ 31
    + 11056 * s ^ 30
    - 97344 * s ^ 29
    + 646274 * s ^ 28
    - 3369886 * s ^ 27
    + 14174735 * s ^ 26
    - 49040332 * s ^ 25
    + 141842644 * s ^ 24
    - 348288475 * s ^ 23
    + 736131743 * s ^ 22
    - 1350674737 * s ^ 21
    + 2146399927 * s ^ 20
    - 2899278499 * s ^ 19
    + 3171069750 * s ^ 18
    - 2409238652 * s ^ 17
    + 177395734 * s ^ 16
    + 3573257254 * s ^ 15
    - 8329172715 * s ^ 14
    + 13074999095 * s ^ 13
    - 16562564089 * s ^ 12
    + 17701975957 * s ^ 11
    - 16061648976 * s ^ 10
    + 12214916979 * s ^ 9
    - 7562465727 * s ^ 8
    + 3628471596 * s ^ 7
    - 1235085838 * s ^ 6
    + 229569056 * s ^ 5
    + 21356390 * s ^ 4
    - 28483166 * s ^ 3
    + 8128189 * s ^ 2
    - 977416 * s
    + 40315

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient18 (s : ℚ) : ℚ :=
  s ^ 32
    - 36 * s ^ 31
    + 624 * s ^ 30
    - 6962 * s ^ 29
    + 56154 * s ^ 28
    - 347528 * s ^ 27
    + 1707696 * s ^ 26
    - 6813275 * s ^ 25
    + 22497868 * s ^ 24
    - 62905274 * s ^ 23
    + 153601426 * s ^ 22
    - 339592137 * s ^ 21
    + 699839580 * s ^ 20
    - 1358811334 * s ^ 19
    + 2477136886 * s ^ 18
    - 4218297685 * s ^ 17
    + 6690714767 * s ^ 16
    - 9847697167 * s ^ 15
    + 13366190819 * s ^ 14
    - 16572580393 * s ^ 13
    + 18502625297 * s ^ 12
    - 18241142589 * s ^ 11
    + 15504528729 * s ^ 10
    - 11014771919 * s ^ 9
    + 6245435098 * s ^ 8
    - 2605619775 * s ^ 7
    + 641233383 * s ^ 6
    + 32555006 * s ^ 5
    - 109014657 * s ^ 4
    + 49833079 * s ^ 3
    - 11613451 * s ^ 2
    + 1311781 * s
    - 54012

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient19 (s : ℚ) : ℚ :=
  -s ^ 30
    + 28 * s ^ 29
    - 384 * s ^ 28
    + 3636 * s ^ 27
    - 28291 * s ^ 26
    + 194034 * s ^ 25
    - 1155912 * s ^ 24
    + 5758280 * s ^ 23
    - 23506969 * s ^ 22
    + 78787938 * s ^ 21
    - 220685232 * s ^ 20
    + 530851684 * s ^ 19
    - 1128877603 * s ^ 18
    + 2167881235 * s ^ 17
    - 3791701013 * s ^ 16
    + 6030839403 * s ^ 15
    - 8662420183 * s ^ 14
    + 11110286080 * s ^ 13
    - 12525824831 * s ^ 12
    + 12169155367 * s ^ 11
    - 9923240888 * s ^ 10
    + 6514005115 * s ^ 9
    - 3170590755 * s ^ 8
    + 889783289 * s ^ 7
    + 115768083 * s ^ 6
    - 288953980 * s ^ 5
    + 172865043 * s ^ 4
    - 60547563 * s ^ 3
    + 12672700 * s ^ 2
    - 1374914 * s
    + 56604

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient20 (s : ℚ) : ℚ :=
  -s ^ 29
    + 37 * s ^ 28
    - 638 * s ^ 27
    + 6847 * s ^ 26
    - 51525 * s ^ 25
    + 291311 * s ^ 24
    - 1304761 * s ^ 23
    + 4876460 * s ^ 22
    - 16033912 * s ^ 21
    + 48260415 * s ^ 20
    - 134196728 * s ^ 19
    + 338925481 * s ^ 18
    - 761177193 * s ^ 17
    + 1502410399 * s ^ 16
    - 2595774976 * s ^ 15
    + 3910992942 * s ^ 14
    - 5095342713 * s ^ 13
    + 5656775876 * s ^ 12
    - 5225701601 * s ^ 11
    + 3840126720 * s ^ 10
    - 2010405627 * s ^ 9
    + 446560614 * s ^ 8
    + 395974760 * s ^ 7
    - 556569671 * s ^ 6
    + 380344787 * s ^ 5
    - 173257427 * s ^ 4
    + 53759452 * s ^ 3
    - 10559015 * s ^ 2
    + 1115668 * s
    - 45981

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient21 (s : ℚ) : ℚ :=
  2 * s ^ 27
    - 74 * s ^ 26
    + 1310 * s ^ 25
    - 14728 * s ^ 24
    + 117590 * s ^ 23
    - 706974 * s ^ 22
    + 3320527 * s ^ 21
    - 12522956 * s ^ 20
    + 38848625 * s ^ 19
    - 101421055 * s ^ 18
    + 227304481 * s ^ 17
    - 442807828 * s ^ 16
    + 750449726 * s ^ 15
    - 1094227433 * s ^ 14
    + 1343023124 * s ^ 13
    - 1334793711 * s ^ 12
    + 980388134 * s ^ 11
    - 359260608 * s ^ 10
    - 283667309 * s ^ 9
    + 680708840 * s ^ 8
    - 729016917 * s ^ 7
    + 537668496 * s ^ 6
    - 294625850 * s ^ 5
    + 120299720 * s ^ 4
    - 35025324 * s ^ 3
    + 6619444 * s ^ 2
    - 687655 * s
    + 28403

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient22 (s : ℚ) : ℚ :=
  s ^ 24
    - 66 * s ^ 23
    + 1516 * s ^ 22
    - 19034 * s ^ 21
    + 154087 * s ^ 20
    - 872328 * s ^ 19
    + 3610761 * s ^ 18
    - 11185578 * s ^ 17
    + 26078893 * s ^ 16
    - 44772733 * s ^ 15
    + 50888689 * s ^ 14
    - 15684531 * s ^ 13
    - 87364783 * s ^ 12
    + 257411103 * s ^ 11
    - 446839138 * s ^ 10
    + 573838192 * s ^ 9
    - 575811068 * s ^ 8
    + 459945201 * s ^ 7
    - 293890157 * s ^ 6
    + 148868409 * s ^ 5
    - 57987774 * s ^ 4
    + 16357279 * s ^ 3
    - 3025311 * s ^ 2
    + 311270 * s
    - 12900

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient23 (s : ℚ) : ℚ :=
  -2 * s ^ 23
    + 71 * s ^ 22
    - 1170 * s ^ 21
    + 11914 * s ^ 20
    - 84229 * s ^ 19
    + 440857 * s ^ 18
    - 1782662 * s ^ 17
    + 5757674 * s ^ 16
    - 15304075 * s ^ 15
    + 34416511 * s ^ 14
    - 66934850 * s ^ 13
    + 113733575 * s ^ 12
    - 168177496 * s ^ 11
    + 213587779 * s ^ 10
    - 229695904 * s ^ 9
    + 207064968 * s ^ 8
    - 155407647 * s ^ 7
    + 96161284 * s ^ 6
    - 47997070 * s ^ 5
    + 18538487 * s ^ 4
    - 5185823 * s ^ 3
    + 951298 * s ^ 2
    - 97552 * s
    + 4062

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient24 (s : ℚ) : ℚ :=
  s ^ 21
    - 35 * s ^ 20
    + 574 * s ^ 19
    - 5860 * s ^ 18
    + 41711 * s ^ 17
    - 219661 * s ^ 16
    + 886463 * s ^ 15
    - 2803290 * s ^ 14
    + 7052721 * s ^ 13
    - 14278208 * s ^ 12
    + 23494631 * s ^ 11
    - 31745367 * s ^ 10
    + 35596418 * s ^ 9
    - 33406024 * s ^ 8
    + 26257406 * s ^ 7
    - 17053351 * s ^ 6
    + 8870821 * s ^ 5
    - 3521252 * s ^ 4
    + 998018 * s ^ 3
    - 183824 * s ^ 2
    + 18900 * s
    - 792

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorStep3Coefficient25 (s : ℚ) : ℚ :=
  -s ^ 17
    + 30 * s ^ 16
    - 413 * s ^ 15
    + 3460 * s ^ 14
    - 19725 * s ^ 13
    + 81062 * s ^ 12
    - 248191 * s ^ 11
    + 577009 * s ^ 10
    - 1028636 * s ^ 9
    + 1409909 * s ^ 8
    - 1480316 * s ^ 7
    + 1178145 * s ^ 6
    - 697578 * s ^ 5
    + 298171 * s ^ 4
    - 87724 * s ^ 3
    + 16430 * s ^ 2
    - 1704 * s
    + 72

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def numeratorStep3 (r s : ℚ) : ℚ :=
  numeratorStep3Coefficient0 s +
    numeratorStep3Coefficient1 s * r +
    numeratorStep3Coefficient2 s * r ^ 2 +
    numeratorStep3Coefficient3 s * r ^ 3 +
    numeratorStep3Coefficient4 s * r ^ 4 +
    numeratorStep3Coefficient5 s * r ^ 5 +
    numeratorStep3Coefficient6 s * r ^ 6 +
    numeratorStep3Coefficient7 s * r ^ 7 +
    numeratorStep3Coefficient8 s * r ^ 8 +
    numeratorStep3Coefficient9 s * r ^ 9 +
    numeratorStep3Coefficient10 s * r ^ 10 +
    numeratorStep3Coefficient11 s * r ^ 11 +
    numeratorStep3Coefficient12 s * r ^ 12 +
    numeratorStep3Coefficient13 s * r ^ 13 +
    numeratorStep3Coefficient14 s * r ^ 14 +
    numeratorStep3Coefficient15 s * r ^ 15 +
    numeratorStep3Coefficient16 s * r ^ 16 +
    numeratorStep3Coefficient17 s * r ^ 17 +
    numeratorStep3Coefficient18 s * r ^ 18 +
    numeratorStep3Coefficient19 s * r ^ 19 +
    numeratorStep3Coefficient20 s * r ^ 20 +
    numeratorStep3Coefficient21 s * r ^ 21 +
    numeratorStep3Coefficient22 s * r ^ 22 +
    numeratorStep3Coefficient23 s * r ^ 23 +
    numeratorStep3Coefficient24 s * r ^ 24 +
    numeratorStep3Coefficient25 s * r ^ 25

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_0 (s : ℚ) :
    numeratorStep3Coefficient0 s =
    numeratorStep2Coefficient0 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient0,
    numeratorStep2Coefficient0,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_1 (s : ℚ) :
    numeratorStep3Coefficient1 s =
    numeratorStep2Coefficient0 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient1 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient1,
    numeratorStep2Coefficient0,
    numeratorStep2Coefficient1,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_2 (s : ℚ) :
    numeratorStep3Coefficient2 s =
    numeratorStep2Coefficient0 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient1 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient2 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient2,
    numeratorStep2Coefficient0,
    numeratorStep2Coefficient1,
    numeratorStep2Coefficient2,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_3 (s : ℚ) :
    numeratorStep3Coefficient3 s =
    numeratorStep2Coefficient0 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient1 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient2 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient3 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient3,
    numeratorStep2Coefficient0,
    numeratorStep2Coefficient1,
    numeratorStep2Coefficient2,
    numeratorStep2Coefficient3,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_4 (s : ℚ) :
    numeratorStep3Coefficient4 s =
    numeratorStep2Coefficient1 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient2 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient3 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient4 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient4,
    numeratorStep2Coefficient1,
    numeratorStep2Coefficient2,
    numeratorStep2Coefficient3,
    numeratorStep2Coefficient4,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_5 (s : ℚ) :
    numeratorStep3Coefficient5 s =
    numeratorStep2Coefficient2 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient3 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient4 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient5 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient5,
    numeratorStep2Coefficient2,
    numeratorStep2Coefficient3,
    numeratorStep2Coefficient4,
    numeratorStep2Coefficient5,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_6 (s : ℚ) :
    numeratorStep3Coefficient6 s =
    numeratorStep2Coefficient3 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient4 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient5 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient6 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient6,
    numeratorStep2Coefficient3,
    numeratorStep2Coefficient4,
    numeratorStep2Coefficient5,
    numeratorStep2Coefficient6,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_7 (s : ℚ) :
    numeratorStep3Coefficient7 s =
    numeratorStep2Coefficient4 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient5 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient6 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient7 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient7,
    numeratorStep2Coefficient4,
    numeratorStep2Coefficient5,
    numeratorStep2Coefficient6,
    numeratorStep2Coefficient7,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_8 (s : ℚ) :
    numeratorStep3Coefficient8 s =
    numeratorStep2Coefficient5 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient6 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient7 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient8 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient8,
    numeratorStep2Coefficient5,
    numeratorStep2Coefficient6,
    numeratorStep2Coefficient7,
    numeratorStep2Coefficient8,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_9 (s : ℚ) :
    numeratorStep3Coefficient9 s =
    numeratorStep2Coefficient6 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient7 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient8 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient9 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient9,
    numeratorStep2Coefficient6,
    numeratorStep2Coefficient7,
    numeratorStep2Coefficient8,
    numeratorStep2Coefficient9,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_10 (s : ℚ) :
    numeratorStep3Coefficient10 s =
    numeratorStep2Coefficient7 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient8 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient9 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient10 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient10,
    numeratorStep2Coefficient7,
    numeratorStep2Coefficient8,
    numeratorStep2Coefficient9,
    numeratorStep2Coefficient10,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_11 (s : ℚ) :
    numeratorStep3Coefficient11 s =
    numeratorStep2Coefficient8 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient9 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient10 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient11 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient11,
    numeratorStep2Coefficient8,
    numeratorStep2Coefficient9,
    numeratorStep2Coefficient10,
    numeratorStep2Coefficient11,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_12 (s : ℚ) :
    numeratorStep3Coefficient12 s =
    numeratorStep2Coefficient9 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient10 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient11 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient12 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient12,
    numeratorStep2Coefficient9,
    numeratorStep2Coefficient10,
    numeratorStep2Coefficient11,
    numeratorStep2Coefficient12,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_13 (s : ℚ) :
    numeratorStep3Coefficient13 s =
    numeratorStep2Coefficient10 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient11 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient12 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient13 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient13,
    numeratorStep2Coefficient10,
    numeratorStep2Coefficient11,
    numeratorStep2Coefficient12,
    numeratorStep2Coefficient13,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_14 (s : ℚ) :
    numeratorStep3Coefficient14 s =
    numeratorStep2Coefficient11 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient12 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient13 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient14 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient14,
    numeratorStep2Coefficient11,
    numeratorStep2Coefficient12,
    numeratorStep2Coefficient13,
    numeratorStep2Coefficient14,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_15 (s : ℚ) :
    numeratorStep3Coefficient15 s =
    numeratorStep2Coefficient12 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient13 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient14 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient15 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient15,
    numeratorStep2Coefficient12,
    numeratorStep2Coefficient13,
    numeratorStep2Coefficient14,
    numeratorStep2Coefficient15,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_16 (s : ℚ) :
    numeratorStep3Coefficient16 s =
    numeratorStep2Coefficient13 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient14 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient15 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient16 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient16,
    numeratorStep2Coefficient13,
    numeratorStep2Coefficient14,
    numeratorStep2Coefficient15,
    numeratorStep2Coefficient16,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_17 (s : ℚ) :
    numeratorStep3Coefficient17 s =
    numeratorStep2Coefficient14 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient15 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient16 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient17 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient17,
    numeratorStep2Coefficient14,
    numeratorStep2Coefficient15,
    numeratorStep2Coefficient16,
    numeratorStep2Coefficient17,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_18 (s : ℚ) :
    numeratorStep3Coefficient18 s =
    numeratorStep2Coefficient15 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient16 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient17 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient18 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient18,
    numeratorStep2Coefficient15,
    numeratorStep2Coefficient16,
    numeratorStep2Coefficient17,
    numeratorStep2Coefficient18,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_19 (s : ℚ) :
    numeratorStep3Coefficient19 s =
    numeratorStep2Coefficient16 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient17 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient18 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient19 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient19,
    numeratorStep2Coefficient16,
    numeratorStep2Coefficient17,
    numeratorStep2Coefficient18,
    numeratorStep2Coefficient19,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_20 (s : ℚ) :
    numeratorStep3Coefficient20 s =
    numeratorStep2Coefficient17 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient18 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient19 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient20 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient20,
    numeratorStep2Coefficient17,
    numeratorStep2Coefficient18,
    numeratorStep2Coefficient19,
    numeratorStep2Coefficient20,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_21 (s : ℚ) :
    numeratorStep3Coefficient21 s =
    numeratorStep2Coefficient18 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient19 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient20 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient21 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient21,
    numeratorStep2Coefficient18,
    numeratorStep2Coefficient19,
    numeratorStep2Coefficient20,
    numeratorStep2Coefficient21,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_22 (s : ℚ) :
    numeratorStep3Coefficient22 s =
    numeratorStep2Coefficient19 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient20 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient21 s *
        rawUnitEightNumeratorCoefficient1 s
      + numeratorStep2Coefficient22 s *
        rawUnitEightNumeratorCoefficient0 s
    := by
  simp only [numeratorStep3Coefficient22,
    numeratorStep2Coefficient19,
    numeratorStep2Coefficient20,
    numeratorStep2Coefficient21,
    numeratorStep2Coefficient22,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_23 (s : ℚ) :
    numeratorStep3Coefficient23 s =
    numeratorStep2Coefficient20 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient21 s *
        rawUnitEightNumeratorCoefficient2 s
      + numeratorStep2Coefficient22 s *
        rawUnitEightNumeratorCoefficient1 s
    := by
  simp only [numeratorStep3Coefficient23,
    numeratorStep2Coefficient20,
    numeratorStep2Coefficient21,
    numeratorStep2Coefficient22,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_24 (s : ℚ) :
    numeratorStep3Coefficient24 s =
    numeratorStep2Coefficient21 s *
        rawUnitEightNumeratorCoefficient3 s
      + numeratorStep2Coefficient22 s *
        rawUnitEightNumeratorCoefficient2 s
    := by
  simp only [numeratorStep3Coefficient24,
    numeratorStep2Coefficient21,
    numeratorStep2Coefficient22,
    rawUnitEightNumeratorCoefficient3,
    rawUnitEightNumeratorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorStep3Coefficient_product_certificate_25 (s : ℚ) :
    numeratorStep3Coefficient25 s =
    numeratorStep2Coefficient22 s *
        rawUnitEightNumeratorCoefficient3 s
    := by
  simp only [numeratorStep3Coefficient25,
    numeratorStep2Coefficient22,
    rawUnitEightNumeratorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem numeratorStep3_eq_numeratorStep2_mul_rawUnitEightNumerator (r s : ℚ) :
    numeratorStep3 r s = numeratorStep2 r s * rawUnitEightNumerator r s := by
  have h0 := numeratorStep3Coefficient_product_certificate_0 s
  have h1 := numeratorStep3Coefficient_product_certificate_1 s
  have h2 := numeratorStep3Coefficient_product_certificate_2 s
  have h3 := numeratorStep3Coefficient_product_certificate_3 s
  have h4 := numeratorStep3Coefficient_product_certificate_4 s
  have h5 := numeratorStep3Coefficient_product_certificate_5 s
  have h6 := numeratorStep3Coefficient_product_certificate_6 s
  have h7 := numeratorStep3Coefficient_product_certificate_7 s
  have h8 := numeratorStep3Coefficient_product_certificate_8 s
  have h9 := numeratorStep3Coefficient_product_certificate_9 s
  have h10 := numeratorStep3Coefficient_product_certificate_10 s
  have h11 := numeratorStep3Coefficient_product_certificate_11 s
  have h12 := numeratorStep3Coefficient_product_certificate_12 s
  have h13 := numeratorStep3Coefficient_product_certificate_13 s
  have h14 := numeratorStep3Coefficient_product_certificate_14 s
  have h15 := numeratorStep3Coefficient_product_certificate_15 s
  have h16 := numeratorStep3Coefficient_product_certificate_16 s
  have h17 := numeratorStep3Coefficient_product_certificate_17 s
  have h18 := numeratorStep3Coefficient_product_certificate_18 s
  have h19 := numeratorStep3Coefficient_product_certificate_19 s
  have h20 := numeratorStep3Coefficient_product_certificate_20 s
  have h21 := numeratorStep3Coefficient_product_certificate_21 s
  have h22 := numeratorStep3Coefficient_product_certificate_22 s
  have h23 := numeratorStep3Coefficient_product_certificate_23 s
  have h24 := numeratorStep3Coefficient_product_certificate_24 s
  have h25 := numeratorStep3Coefficient_product_certificate_25 s
  simp only [numeratorStep3, numeratorStep2, rawUnitEightNumerator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient2 (s : ℚ) : ℚ :=
  s ^ 39
    - 7 * s ^ 38
    + 27 * s ^ 37
    - 75 * s ^ 36
    + 166 * s ^ 35
    - 310 * s ^ 34
    + 505 * s ^ 33
    - 733 * s ^ 32
    + 961 * s ^ 31
    - 1147 * s ^ 30
    + 1252 * s ^ 29
    - 1252 * s ^ 28
    + 1147 * s ^ 27
    - 961 * s ^ 26
    + 733 * s ^ 25
    - 505 * s ^ 24
    + 310 * s ^ 23
    - 166 * s ^ 22
    + 75 * s ^ 21
    - 27 * s ^ 20
    + 7 * s ^ 19
    - s ^ 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 43
    + 11 * s ^ 42
    - 65 * s ^ 41
    + 273 * s ^ 40
    - 895 * s ^ 39
    + 2366 * s ^ 38
    - 5208 * s ^ 37
    + 9822 * s ^ 36
    - 16250 * s ^ 35
    + 24045 * s ^ 34
    - 32248 * s ^ 33
    + 39529 * s ^ 32
    - 44438 * s ^ 31
    + 45758 * s ^ 30
    - 42930 * s ^ 29
    + 36299 * s ^ 28
    - 27104 * s ^ 27
    + 17091 * s ^ 26
    - 7984 * s ^ 25
    + 1062 * s ^ 24
    + 3110 * s ^ 23
    - 4681 * s ^ 22
    + 4364 * s ^ 21
    - 3113 * s ^ 20
    + 1759 * s ^ 19
    - 781 * s ^ 18
    + 263 * s ^ 17
    - 64 * s ^ 16
    + 11 * s ^ 15
    - s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 46
    + 14 * s ^ 45
    - 105 * s ^ 44
    + 546 * s ^ 43
    - 2150 * s ^ 42
    + 6752 * s ^ 41
    - 17460 * s ^ 40
    + 37793 * s ^ 39
    - 69119 * s ^ 38
    + 107985 * s ^ 37
    - 145437 * s ^ 36
    + 169299 * s ^ 35
    - 167645 * s ^ 34
    + 130620 * s ^ 33
    - 51619 * s ^ 32
    - 71389 * s ^ 31
    + 232451 * s ^ 30
    - 414239 * s ^ 29
    + 589540 * s ^ 28
    - 727410 * s ^ 27
    + 802783 * s ^ 26
    - 802866 * s ^ 25
    + 729444 * s ^ 24
    - 598866 * s ^ 23
    + 438456 * s ^ 22
    - 280350 * s ^ 21
    + 151560 * s ^ 20
    - 65535 * s ^ 19
    + 20113 * s ^ 18
    - 2539 * s ^ 17
    - 1354 * s ^ 16
    + 1037 * s ^ 15
    - 388 * s ^ 14
    + 91 * s ^ 13
    - 13 * s ^ 12
    + s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient5 (s : ℚ) : ℚ :=
  s ^ 48
    - 17 * s ^ 47
    + 144 * s ^ 46
    - 788 * s ^ 45
    + 3093 * s ^ 44
    - 9006 * s ^ 43
    + 18900 * s ^ 42
    - 23345 * s ^ 41
    - 13013 * s ^ 40
    + 169453 * s ^ 39
    - 568546 * s ^ 38
    + 1338258 * s ^ 37
    - 2558128 * s ^ 36
    + 4233821 * s ^ 35
    - 6327697 * s ^ 34
    + 8809193 * s ^ 33
    - 11650972 * s ^ 32
    + 14761611 * s ^ 31
    - 17894242 * s ^ 30
    + 20630933 * s ^ 29
    - 22481680 * s ^ 28
    + 23029681 * s ^ 27
    - 22055023 * s ^ 26
    + 19578765 * s ^ 25
    - 15883346 * s ^ 24
    + 11511404 * s ^ 23
    - 7177342 * s ^ 22
    + 3577647 * s ^ 21
    - 1142763 * s ^ 20
    - 100177 * s ^ 19
    + 464648 * s ^ 18
    - 388504 * s ^ 17
    + 209653 * s ^ 16
    - 82314 * s ^ 15
    + 24091 * s ^ 14
    - 5019 * s ^ 13
    + 671 * s ^ 12
    - 44 * s ^ 11
    - s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient6 (s : ℚ) : ℚ :=
  s ^ 49
    - 12 * s ^ 48
    + 27 * s ^ 47
    + 464 * s ^ 46
    - 5462 * s ^ 45
    + 33405 * s ^ 44
    - 144630 * s ^ 43
    + 487618 * s ^ 42
    - 1340070 * s ^ 41
    + 3084332 * s ^ 40
    - 6050298 * s ^ 39
    + 10270238 * s ^ 38
    - 15442148 * s ^ 37
    + 21439846 * s ^ 36
    - 29159212 * s ^ 35
    + 40915049 * s ^ 34
    - 59591945 * s ^ 33
    + 86733407 * s ^ 32
    - 120840654 * s ^ 31
    + 157009717 * s ^ 30
    - 188308520 * s ^ 29
    + 207845935 * s ^ 28
    - 210314284 * s ^ 27
    + 192922134 * s ^ 26
    - 156224339 * s ^ 25
    + 105305614 * s ^ 24
    - 49858320 * s ^ 23
    + 1699096 * s ^ 22
    + 29720058 * s ^ 21
    - 41397870 * s ^ 20
    + 37425942 * s ^ 19
    - 25877063 * s ^ 18
    + 14194767 * s ^ 17
    - 6185904 * s ^ 16
    + 2109753 * s ^ 15
    - 543383 * s ^ 14
    + 95126 * s ^ 13
    - 7978 * s ^ 12
    - 684 * s ^ 11
    + 266 * s ^ 10
    - 20 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 50
    + 29 * s ^ 49
    - 399 * s ^ 48
    + 3322 * s ^ 47
    - 18728 * s ^ 46
    + 75935 * s ^ 45
    - 225578 * s ^ 44
    + 468930 * s ^ 43
    - 497072 * s ^ 42
    - 817417 * s ^ 41
    + 5883286 * s ^ 40
    - 17880481 * s ^ 39
    + 37909455 * s ^ 38
    - 59611506 * s ^ 37
    + 64827459 * s ^ 36
    - 26540114 * s ^ 35
    - 78627560 * s ^ 34
    + 254314266 * s ^ 33
    - 476382502 * s ^ 32
    + 699344051 * s ^ 31
    - 871665134 * s ^ 30
    + 948812120 * s ^ 29
    - 895529139 * s ^ 28
    + 684251964 * s ^ 27
    - 304561373 * s ^ 26
    - 213264235 * s ^ 25
    + 778152185 * s ^ 24
    - 1252360476 * s ^ 23
    + 1505671758 * s ^ 22
    - 1480092383 * s ^ 21
    + 1220912586 * s ^ 20
    - 848904870 * s ^ 19
    + 494313173 * s ^ 18
    - 237521615 * s ^ 17
    + 91819942 * s ^ 16
    - 27316467 * s ^ 15
    + 5627127 * s ^ 14
    - 488312 * s ^ 13
    - 131548 * s ^ 12
    + 58854 * s ^ 11
    - 10261 * s ^ 10
    + 758 * s ^ 9
    - 28 * s ^ 8
    - s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 51
    + 22 * s ^ 50
    - 205 * s ^ 49
    + 821 * s ^ 48
    + 1930 * s ^ 47
    - 47240 * s ^ 46
    + 335916 * s ^ 45
    - 1549984 * s ^ 44
    + 5306178 * s ^ 43
    - 14055156 * s ^ 42
    + 28625982 * s ^ 41
    - 41063074 * s ^ 40
    + 22677809 * s ^ 39
    + 85477321 * s ^ 38
    - 362134860 * s ^ 37
    + 858959488 * s ^ 36
    - 1531319117 * s ^ 35
    + 2199780348 * s ^ 34
    - 2590811566 * s ^ 33
    + 2445023300 * s ^ 32
    - 1606854928 * s ^ 31
    + 10838147 * s ^ 30
    + 2426184885 * s ^ 29
    - 5888406152 * s ^ 28
    + 10554216982 * s ^ 27
    - 16276169073 * s ^ 26
    + 22263249063 * s ^ 25
    - 27097120421 * s ^ 24
    + 29250921187 * s ^ 23
    - 27862541351 * s ^ 22
    + 23262186975 * s ^ 21
    - 16867822761 * s ^ 20
    + 10485785659 * s ^ 19
    - 5484008882 * s ^ 18
    + 2343169780 * s ^ 17
    - 774853004 * s ^ 16
    + 172868498 * s ^ 15
    - 10289734 * s ^ 14
    - 10666312 * s ^ 13
    + 5216241 * s ^ 12
    - 1278983 * s ^ 11
    + 175911 * s ^ 10
    - 9522 * s ^ 9
    - 190 * s ^ 8
    + 74 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient9 (s : ℚ) : ℚ :=
  -4 * s ^ 51
    + 123 * s ^ 50
    - 1719 * s ^ 49
    + 14492 * s ^ 48
    - 80778 * s ^ 47
    + 297437 * s ^ 46
    - 593716 * s ^ 45
    - 630699 * s ^ 44
    + 10881738 * s ^ 43
    - 52770534 * s ^ 42
    + 175578254 * s ^ 41
    - 455238200 * s ^ 40
    + 953385998 * s ^ 39
    - 1603421301 * s ^ 38
    + 2033975079 * s ^ 37
    - 1445352706 * s ^ 36
    - 1271677312 * s ^ 35
    + 7127530523 * s ^ 34
    - 16624001989 * s ^ 33
    + 29823408587 * s ^ 32
    - 47119918213 * s ^ 31
    + 70234586926 * s ^ 30
    - 102376379487 * s ^ 29
    + 146630317756 * s ^ 28
    - 202676412978 * s ^ 27
    + 263677368575 * s ^ 26
    - 316057147015 * s ^ 25
    + 343742461883 * s ^ 24
    - 335463485320 * s ^ 23
    + 290924113660 * s ^ 22
    - 221803970652 * s ^ 21
    + 146589892689 * s ^ 20
    - 82263949204 * s ^ 19
    + 37886040809 * s ^ 18
    - 13360949546 * s ^ 17
    + 2908609729 * s ^ 16
    + 159003036 * s ^ 15
    - 487406572 * s ^ 14
    + 248849195 * s ^ 13
    - 76206350 * s ^ 12
    + 14792682 * s ^ 11
    - 1520792 * s ^ 10
    - 10173 * s ^ 9
    + 17995 * s ^ 8
    - 1925 * s ^ 7
    + 18 * s ^ 6
    + s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 52
    + 20 * s ^ 51
    - 79 * s ^ 50
    - 1899 * s ^ 49
    + 34768 * s ^ 48
    - 310735 * s ^ 47
    + 1856265 * s ^ 46
    - 8110351 * s ^ 45
    + 26722952 * s ^ 44
    - 65203603 * s ^ 43
    + 101569718 * s ^ 42
    + 4525149 * s ^ 41
    - 695034730 * s ^ 40
    + 2976645681 * s ^ 39
    - 8624489908 * s ^ 38
    + 20040080017 * s ^ 37
    - 39563623230 * s ^ 36
    + 68713373415 * s ^ 35
    - 108784705970 * s ^ 34
    + 164179380018 * s ^ 33
    - 247836495625 * s ^ 32
    + 385051311844 * s ^ 31
    - 610057585568 * s ^ 30
    + 951572782386 * s ^ 29
    - 1409533917938 * s ^ 28
    + 1933731793084 * s ^ 27
    - 2420701877039 * s ^ 26
    + 2740062934509 * s ^ 25
    - 2785077855297 * s ^ 24
    + 2523476179695 * s ^ 23
    - 2018490491136 * s ^ 22
    + 1404876973213 * s ^ 21
    - 831077885662 * s ^ 20
    + 400059805386 * s ^ 19
    - 141104219016 * s ^ 18
    + 22265725355 * s ^ 17
    + 13209996453 * s ^ 16
    - 13994574070 * s ^ 15
    + 7328253482 * s ^ 14
    - 2616029190 * s ^ 13
    + 643628865 * s ^ 12
    - 95804802 * s ^ 11
    + 3087166 * s ^ 10
    + 1879854 * s ^ 9
    - 349571 * s ^ 8
    + 25933 * s ^ 7
    + 237 * s ^ 6
    - 45 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient11 (s : ℚ) : ℚ :=
  -4 * s ^ 52
    + 128 * s ^ 51
    - 1809 * s ^ 50
    + 14208 * s ^ 49
    - 56789 * s ^ 48
    - 53942 * s ^ 47
    + 2468359 * s ^ 46
    - 19649019 * s ^ 45
    + 101944380 * s ^ 44
    - 405205803 * s ^ 43
    + 1314600791 * s ^ 42
    - 3601334526 * s ^ 41
    + 8504646501 * s ^ 40
    - 17559898253 * s ^ 39
    + 32155585658 * s ^ 38
    - 53631029202 * s ^ 37
    + 86488439121 * s ^ 36
    - 148753079579 * s ^ 35
    + 291262346972 * s ^ 34
    - 619602459284 * s ^ 33
    + 1302227818403 * s ^ 32
    - 2543577871451 * s ^ 31
    + 4508663134410 * s ^ 30
    - 7208805503281 * s ^ 29
    + 10391865123213 * s ^ 28
    - 13508446768559 * s ^ 27
    + 15817832502435 * s ^ 26
    - 16633471207029 * s ^ 25
    + 15615200404199 * s ^ 24
    - 12955332155863 * s ^ 23
    + 9337275566843 * s ^ 22
    - 5665785884381 * s ^ 21
    + 2703456017826 * s ^ 20
    - 809885692708 * s ^ 19
    - 88961746988 * s ^ 18
    + 327108940347 * s ^ 17
    - 265367349150 * s ^ 16
    + 143008367136 * s ^ 15
    - 56983694157 * s ^ 14
    + 16628825806 * s ^ 13
    - 3168581547 * s ^ 12
    + 204110029 * s ^ 11
    + 83280609 * s ^ 10
    - 28384874 * s ^ 9
    + 3656720 * s ^ 8
    - 173335 * s ^ 7
    - 13579 * s ^ 6
    + 1019 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient12 (s : ℚ) : ℚ :=
  -9 * s ^ 52
    + 364 * s ^ 51
    - 6819 * s ^ 50
    + 79023 * s ^ 49
    - 636481 * s ^ 48
    + 3784409 * s ^ 47
    - 17162619 * s ^ 46
    + 60127105 * s ^ 45
    - 160672064 * s ^ 44
    + 303574693 * s ^ 43
    - 261660570 * s ^ 42
    - 704091889 * s ^ 41
    + 3930837442 * s ^ 40
    - 9779033494 * s ^ 39
    + 10575848153 * s ^ 38
    + 29107610650 * s ^ 37
    - 213250555277 * s ^ 36
    + 776903525530 * s ^ 35
    - 2149959329318 * s ^ 34
    + 4975078827940 * s ^ 33
    - 10018239074309 * s ^ 32
    + 17924281878341 * s ^ 31
    - 28826061885224 * s ^ 30
    + 41918935617583 * s ^ 29
    - 55229251906143 * s ^ 28
    + 65845072160718 * s ^ 27
    - 70727490482740 * s ^ 26
    + 67889568002989 * s ^ 25
    - 57407932960644 * s ^ 24
    + 41667441535209 * s ^ 23
    - 24568013419674 * s ^ 22
    + 10000631561110 * s ^ 21
    - 369236007432 * s ^ 20
    - 4050993559269 * s ^ 19
    + 4661393131167 * s ^ 18
    - 3433834843038 * s ^ 17
    + 1913584445437 * s ^ 16
    - 830804193066 * s ^ 15
    + 274243959634 * s ^ 14
    - 61733180699 * s ^ 13
    + 5188880770 * s ^ 12
    + 2339010088 * s ^ 11
    - 1132870270 * s ^ 10
    + 234977011 * s ^ 9
    - 21991741 * s ^ 8
    - 84397 * s ^ 7
    + 245680 * s ^ 6
    - 13825 * s ^ 5
    - 37 * s ^ 4
    + 2 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient13 (s : ℚ) : ℚ :=
  -2 * s ^ 53
    + 65 * s ^ 52
    - 910 * s ^ 51
    + 6281 * s ^ 50
    - 5819 * s ^ 49
    - 332012 * s ^ 48
    + 3908753 * s ^ 47
    - 26632479 * s ^ 46
    + 130154737 * s ^ 45
    - 484783177 * s ^ 44
    + 1379801871 * s ^ 43
    - 2740913121 * s ^ 42
    + 1700545202 * s ^ 41
    + 15585907290 * s ^ 40
    - 96059425931 * s ^ 39
    + 369574174294 * s ^ 38
    - 1141664329121 * s ^ 37
    + 3030901841334 * s ^ 36
    - 7114729222746 * s ^ 35
    + 14993519186543 * s ^ 34
    - 28637227635442 * s ^ 33
    + 49871265632271 * s ^ 32
    - 79432930956302 * s ^ 31
    + 115752056088919 * s ^ 30
    - 153970729956524 * s ^ 29
    + 186010241537243 * s ^ 28
    - 202351164796208 * s ^ 27
    + 195399446070689 * s ^ 26
    - 163186228893729 * s ^ 25
    + 111433783985856 * s ^ 24
    - 52390760135928 * s ^ 23
    + 416183889609 * s ^ 22
    + 33719427894318 * s ^ 21
    - 46774922468978 * s ^ 20
    + 43055621237685 * s ^ 19
    - 30847550228149 * s ^ 18
    + 17839952700913 * s ^ 17
    - 8303899135643 * s ^ 16
    + 2996887889036 * s ^ 15
    - 743102213195 * s ^ 14
    + 59069654395 * s ^ 13
    + 48579844003 * s ^ 12
    - 27720709385 * s ^ 11
    + 7757001549 * s ^ 10
    - 1187809753 * s ^ 9
    + 50436228 * s ^ 8
    + 13685986 * s ^ 7
    - 2607924 * s ^ 6
    + 115441 * s ^ 5
    + 2040 * s ^ 4
    - 73 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient14 (s : ℚ) : ℚ :=
  -3 * s ^ 53
    + 129 * s ^ 52
    - 2520 * s ^ 51
    + 29528 * s ^ 50
    - 226318 * s ^ 49
    + 1108202 * s ^ 48
    - 2350320 * s ^ 47
    - 13802222 * s ^ 46
    + 184469970 * s ^ 45
    - 1215709586 * s ^ 44
    + 5994682251 * s ^ 43
    - 24594581882 * s ^ 42
    + 88127621320 * s ^ 41
    - 283016587735 * s ^ 40
    + 825633598843 * s ^ 39
    - 2201901414925 * s ^ 38
    + 5383788769271 * s ^ 37
    - 12089502910067 * s ^ 36
    + 24973495297925 * s ^ 35
    - 47529212200188 * s ^ 34
    + 83390117123179 * s ^ 33
    - 134716380742161 * s ^ 32
    + 199666118151628 * s ^ 31
    - 269722022988675 * s ^ 30
    + 328590313605761 * s ^ 29
    - 354684793259960 * s ^ 28
    + 328020526623560 * s ^ 27
    - 239744422326640 * s ^ 26
    + 99893373803664 * s ^ 25
    + 61792221004722 * s ^ 24
    - 204687304245797 * s ^ 23
    + 293100947267127 * s ^ 22
    - 311290419661672 * s ^ 21
    + 268949176893964 * s ^ 20
    - 193818533819515 * s ^ 19
    + 116513119071619 * s ^ 18
    - 57320688324954 * s ^ 17
    + 21907554130632 * s ^ 16
    - 5518604845174 * s ^ 15
    + 96385343051 * s ^ 14
    + 766098175255 * s ^ 13
    - 456781794830 * s ^ 12
    + 155549010375 * s ^ 11
    - 32599805802 * s ^ 10
    + 3052341167 * s ^ 9
    + 363151306 * s ^ 8
    - 147226416 * s ^ 7
    + 18106616 * s ^ 6
    - 515640 * s ^ 5
    - 39312 * s ^ 4
    + 1248 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient15 (s : ℚ) : ℚ :=
  -4 * s ^ 53
    + 208 * s ^ 52
    - 5049 * s ^ 51
    + 76844 * s ^ 50
    - 830298 * s ^ 49
    + 6839859 * s ^ 48
    - 45123435 * s ^ 47
    + 247853321 * s ^ 46
    - 1172209238 * s ^ 45
    + 4914386237 * s ^ 44
    - 18683739447 * s ^ 43
    + 65327090570 * s ^ 42
    - 211187009084 * s ^ 41
    + 630895991149 * s ^ 40
    - 1737322721043 * s ^ 39
    + 4402007535915 * s ^ 38
    - 10260037105188 * s ^ 37
    + 22013335801067 * s ^ 36
    - 43494081693137 * s ^ 35
    + 79018268220472 * s ^ 34
    - 131369887781174 * s ^ 33
    + 198000321864725 * s ^ 32
    - 266165187109066 * s ^ 31
    + 309589600050152 * s ^ 30
    - 290609891174483 * s ^ 29
    + 170838187092196 * s ^ 28
    + 70600565115150 * s ^ 27
    - 418019857734970 * s ^ 26
    + 810425991890719 * s ^ 25
    - 1153120988793050 * s ^ 24
    + 1350689556893446 * s ^ 23
    - 1348240578613706 * s ^ 22
    + 1157999702283353 * s ^ 21
    - 853261556282447 * s ^ 20
    + 531798738703919 * s ^ 19
    - 271558182887410 * s ^ 18
    + 105055527257943 * s ^ 17
    - 22698405085885 * s ^ 16
    - 5576197704057 * s ^ 15
    + 8897480076898 * s ^ 14
    - 5283857647244 * s ^ 13
    + 2055764255920 * s ^ 12
    - 534724692869 * s ^ 11
    + 74899383126 * s ^ 10
    + 4096550167 * s ^ 9
    - 4414197562 * s ^ 8
    + 906795391 * s ^ 7
    - 82059094 * s ^ 6
    - 234886 * s ^ 5
    + 437431 * s ^ 4
    - 12275 * s ^ 3
    - 78 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient16 (s : ℚ) : ℚ :=
  -s ^ 54
    + 45 * s ^ 53
    - 975 * s ^ 52
    + 13505 * s ^ 51
    - 134791 * s ^ 50
    + 1044299 * s ^ 49
    - 6674678 * s ^ 48
    + 37267279 * s ^ 47
    - 190765783 * s ^ 46
    + 917959418 * s ^ 45
    - 4138725812 * s ^ 44
    + 17167851627 * s ^ 43
    - 64455051611 * s ^ 42
    + 217363854074 * s ^ 41
    - 658512353772 * s ^ 40
    + 1800082587896 * s ^ 39
    - 4463401136166 * s ^ 38
    + 10071735411280 * s ^ 37
    - 20653089787904 * s ^ 36
    + 38140848608674 * s ^ 35
    - 62102544143547 * s ^ 34
    + 85106544253673 * s ^ 33
    - 86180242547497 * s ^ 32
    + 25360632723737 * s ^ 31
    + 155078886498405 * s ^ 30
    - 516869905627854 * s ^ 29
    + 1097681007385372 * s ^ 28
    - 1875565097136225 * s ^ 27
    + 2742970689942548 * s ^ 26
    - 3512683239592661 * s ^ 25
    + 3969788019845247 * s ^ 24
    - 3958292183952922 * s ^ 23
    + 3460582358510988 * s ^ 22
    - 2618369612361595 * s ^ 21
    + 1673076417908252 * s ^ 20
    - 857227250558229 * s ^ 19
    + 302843135128924 * s ^ 18
    - 16982970660606 * s ^ 17
    - 76826521350034 * s ^ 16
    + 73925904851184 * s ^ 15
    - 43697107810969 * s ^ 14
    + 18671691294733 * s ^ 13
    - 5675971290371 * s ^ 12
    + 1017737649337 * s ^ 11
    + 22061645485 * s ^ 10
    - 77645174298 * s ^ 9
    + 24279426230 * s ^ 8
    - 3658694388 * s ^ 7
    + 205761244 * s ^ 6
    + 21221081 * s ^ 5
    - 3182882 * s ^ 4
    + 69237 * s ^ 3
    + 1826 * s ^ 2
    - 29 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient17 (s : ℚ) : ℚ :=
  4 * s ^ 53
    - 149 * s ^ 52
    + 2509 * s ^ 51
    - 23776 * s ^ 50
    + 113352 * s ^ 49
    + 206953 * s ^ 48
    - 8689912 * s ^ 47
    + 85526633 * s ^ 46
    - 557401329 * s ^ 45
    + 2793081614 * s ^ 44
    - 11442424202 * s ^ 43
    + 39751304195 * s ^ 42
    - 120141555724 * s ^ 41
    + 321086306356 * s ^ 40
    - 760471701349 * s ^ 39
    + 1557361851137 * s ^ 38
    - 2517065562467 * s ^ 37
    + 2035395768778 * s ^ 36
    + 5678360883565 * s ^ 35
    - 35969122802260 * s ^ 34
    + 121468128251029 * s ^ 33
    - 319296707273722 * s ^ 32
    + 711497374291231 * s ^ 31
    - 1390501285493647 * s ^ 30
    + 2423559009930316 * s ^ 29
    - 3798786946950069 * s ^ 28
    + 5371313354729827 * s ^ 27
    - 6845015857698083 * s ^ 26
    + 7827923565358975 * s ^ 25
    - 7969772814380290 * s ^ 24
    + 7131431513207946 * s ^ 23
    - 5487794105597841 * s ^ 22
    + 3481158203965014 * s ^ 21
    - 1631810441949569 * s ^ 20
    + 314580617518140 * s ^ 19
    + 364890147192600 * s ^ 18
    - 537470583113015 * s ^ 17
    + 435382481687850 * s ^ 16
    - 259650294757722 * s ^ 15
    + 119138080029125 * s ^ 14
    - 40506231975265 * s ^ 13
    + 8456719831670 * s ^ 12
    + 169505668357 * s ^ 11
    - 930602585959 * s ^ 10
    + 387511767723 * s ^ 9
    - 85636436238 * s ^ 8
    + 9330184108 * s ^ 7
    + 91272033 * s ^ 6
    - 167220845 * s ^ 5
    + 15837479 * s ^ 4
    - 153370 * s ^ 3
    - 22069 * s ^ 2
    + 352 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient18 (s : ℚ) : ℚ :=
  3 * s ^ 53
    - 142 * s ^ 52
    + 3156 * s ^ 51
    - 43761 * s ^ 50
    + 422776 * s ^ 49
    - 2998095 * s ^ 48
    + 15899362 * s ^ 47
    - 61871849 * s ^ 46
    + 156822541 * s ^ 45
    - 72593296 * s ^ 44
    - 1764061422 * s ^ 43
    + 12139461133 * s ^ 42
    - 55709900981 * s ^ 41
    + 217997133703 * s ^ 40
    - 792554331616 * s ^ 39
    + 2744847089313 * s ^ 38
    - 8977429075503 * s ^ 37
    + 27223945130514 * s ^ 36
    - 75483262043956 * s ^ 35
    + 190130186900154 * s ^ 34
    - 434716657649976 * s ^ 33
    + 904146982451642 * s ^ 32
    - 1715323566940546 * s ^ 31
    + 2973650330314242 * s ^ 30
    - 4709454611560746 * s ^ 29
    + 6795400688335685 * s ^ 28
    - 8885066693856977 * s ^ 27
    + 10436393037601687 * s ^ 26
    - 10867802589331805 * s ^ 25
    + 9818846356482630 * s ^ 24
    - 7386015719467347 * s ^ 23
    + 4166295405733755 * s ^ 22
    - 1033231419352207 * s ^ 21
    - 1248477203144374 * s ^ 20
    + 2338218773962413 * s ^ 19
    - 2381100321067168 * s ^ 18
    + 1817803880447444 * s ^ 17
    - 1106902647149455 * s ^ 16
    + 537484757622191 * s ^ 15
    - 197029144883196 * s ^ 14
    + 43687603740174 * s ^ 13
    + 3332288544580 * s ^ 12
    - 8258328395170 * s ^ 11
    + 4103285385677 * s ^ 10
    - 1189693059850 * s ^ 9
    + 198931531625 * s ^ 8
    - 9528940880 * s ^ 7
    - 3354922245 * s ^ 6
    + 779711916 * s ^ 5
    - 53390569 * s ^ 4
    - 860192 * s ^ 3
    + 167386 * s ^ 2
    - 2354 * s
    - 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient19 (s : ℚ) : ℚ :=
  s ^ 53
    - 60 * s ^ 52
    + 1636 * s ^ 51
    - 27486 * s ^ 50
    + 322700 * s ^ 49
    - 2836568 * s ^ 48
    + 19518339 * s ^ 47
    - 108804724 * s ^ 46
    + 508338784 * s ^ 45
    - 2079046484 * s ^ 44
    + 7904924767 * s ^ 43
    - 29834195429 * s ^ 42
    + 115497330888 * s ^ 41
    - 448754989381 * s ^ 40
    + 1670399338025 * s ^ 39
    - 5747783966802 * s ^ 38
    + 17974629080518 * s ^ 37
    - 50860405506478 * s ^ 36
    + 130459039622127 * s ^ 35
    - 304663637372721 * s ^ 34
    + 650668116559596 * s ^ 33
    - 1274693519047440 * s ^ 32
    + 2291814060556029 * s ^ 31
    - 3771898504885887 * s ^ 30
    + 5649236805401721 * s ^ 29
    - 7626055954525818 * s ^ 28
    + 9142405118466296 * s ^ 27
    - 9496691890335229 * s ^ 26
    + 8137096089149171 * s ^ 25
    - 5010674346292326 * s ^ 24
    + 747725368993038 * s ^ 23
    + 3502549532824941 * s ^ 22
    - 6557263602959011 * s ^ 21
    + 7735770150950648 * s ^ 20
    - 7115874856096357 * s ^ 19
    + 5373688757238003 * s ^ 18
    - 3358749969626124 * s ^ 17
    + 1699752675289123 * s ^ 16
    - 643971590253515 * s ^ 15
    + 129635865490169 * s ^ 14
    + 40811811808897 * s ^ 13
    - 55754430059574 * s ^ 12
    + 30631947079100 * s ^ 11
    - 10791447595501 * s ^ 10
    + 2427636360110 * s ^ 9
    - 249118732951 * s ^ 8
    - 34284008344 * s ^ 7
    + 16556186289 * s ^ 6
    - 2485421060 * s ^ 5
    + 106605538 * s ^ 4
    + 10013587 * s ^ 3
    - 873823 * s ^ 2
    + 8777 * s
    + 275

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient20 (s : ℚ) : ℚ :=
  -6 * s ^ 52
    + 288 * s ^ 51
    - 6541 * s ^ 50
    + 93115 * s ^ 49
    - 923787 * s ^ 48
    + 6662529 * s ^ 47
    - 34618416 * s ^ 46
    + 114104221 * s ^ 45
    - 33578437 * s ^ 44
    - 2608965036 * s ^ 43
    + 22191966635 * s ^ 42
    - 123238953586 * s ^ 41
    + 543575826631 * s ^ 40
    - 2033703301113 * s ^ 39
    + 6670625611462 * s ^ 38
    - 19575145512678 * s ^ 37
    + 52105879836451 * s ^ 36
    - 126986567563584 * s ^ 35
    + 284814585737581 * s ^ 34
    - 588336868752566 * s ^ 33
    + 1115078647195650 * s ^ 32
    - 1923300592495933 * s ^ 31
    + 2980280438312954 * s ^ 30
    - 4067112715224728 * s ^ 29
    + 4718589948545655 * s ^ 28
    - 4288764617319675 * s ^ 27
    + 2200415226616518 * s ^ 26
    + 1683716260721452 * s ^ 25
    - 6776497576433727 * s ^ 24
    + 11815023562864799 * s ^ 23
    - 15324210921055219 * s ^ 22
    + 16285609960398183 * s ^ 21
    - 14612165755026808 * s ^ 20
    + 11130876271677729 * s ^ 19
    - 7108578041687994 * s ^ 18
    + 3649286269565149 * s ^ 17
    - 1316683084675210 * s ^ 16
    + 114446487690764 * s ^ 15
    + 287809556776539 * s ^ 14
    - 285210525619664 * s ^ 13
    + 165867212872091 * s ^ 12
    - 67540112547270 * s ^ 11
    + 18861247475271 * s ^ 10
    - 2900200029051 * s ^ 9
    - 156336804783 * s ^ 8
    + 204971420402 * s ^ 7
    - 49747544084 * s ^ 6
    + 5444340840 * s ^ 5
    - 8704408 * s ^ 4
    - 52238236 * s ^ 3
    + 3280622 * s ^ 2
    - 8991 * s
    - 2000

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient21 (s : ℚ) : ℚ :=
  -2 * s ^ 52
    + 116 * s ^ 51
    - 3180 * s ^ 50
    + 55271 * s ^ 49
    - 688046 * s ^ 48
    + 6565614 * s ^ 47
    - 50195246 * s ^ 46
    + 317503026 * s ^ 45
    - 1704922518 * s ^ 44
    + 7947073347 * s ^ 43
    - 32815992156 * s ^ 42
    + 122319047715 * s ^ 41
    - 418473173067 * s ^ 40
    + 1331628016840 * s ^ 39
    - 3974929052139 * s ^ 38
    + 11159131005195 * s ^ 37
    - 29357689902842 * s ^ 36
    + 71722713910293 * s ^ 35
    - 160561438519993 * s ^ 34
    + 323828893934435 * s ^ 33
    - 575447515634016 * s ^ 32
    + 869593405303818 * s ^ 31
    - 1033717451278611 * s ^ 30
    + 716896361857017 * s ^ 29
    + 577959732936605 * s ^ 28
    - 3316315263362463 * s ^ 27
    + 7625481637516242 * s ^ 26
    - 13004475897567601 * s ^ 25
    + 18275762726718912 * s ^ 24
    - 21926276675061015 * s ^ 23
    + 22743731271517607 * s ^ 22
    - 20408296213853095 * s ^ 21
    + 15668352355491997 * s ^ 20
    - 9979783420411171 * s ^ 19
    + 4837599796769373 * s ^ 18
    - 1199652318748462 * s ^ 17
    - 719540848588628 * s ^ 16
    + 1282781046696037 * s ^ 15
    - 1087153012010076 * s ^ 14
    + 658329590629005 * s ^ 13
    - 299744096662102 * s ^ 12
    + 98757895180322 * s ^ 11
    - 19701923538921 * s ^ 10
    - 100141182120 * s ^ 9
    + 1619695201417 * s ^ 8
    - 581610176790 * s ^ 7
    + 102703285435 * s ^ 6
    - 7049236650 * s ^ 5
    - 810544462 * s ^ 4
    + 183100668 * s ^ 3
    - 8921775 * s ^ 2
    - 99512 * s
    + 10352

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient22 (s : ℚ) : ℚ :=
  5 * s ^ 51
    - 247 * s ^ 50
    + 5843 * s ^ 49
    - 88002 * s ^ 48
    + 945099 * s ^ 47
    - 7665934 * s ^ 46
    + 48346207 * s ^ 45
    - 238484354 * s ^ 44
    + 893394781 * s ^ 43
    - 2203389664 * s ^ 42
    + 385111618 * s ^ 41
    + 32153441355 * s ^ 40
    - 219895541774 * s ^ 39
    + 991971950267 * s ^ 38
    - 3527379702181 * s ^ 37
    + 10354624698150 * s ^ 36
    - 25220713526046 * s ^ 35
    + 49520595483323 * s ^ 34
    - 70260827373524 * s ^ 33
    + 34497635125932 * s ^ 32
    + 187719264034194 * s ^ 31
    - 832847647523699 * s ^ 30
    + 2226478313136660 * s ^ 29
    - 4676554088365803 * s ^ 28
    + 8272685484401878 * s ^ 27
    - 12667054206216882 * s ^ 26
    + 16986663730903956 * s ^ 25
    - 20015750475128793 * s ^ 24
    + 20649237120900362 * s ^ 23
    - 18417899525991610 * s ^ 22
    + 13778728279217412 * s ^ 21
    - 7969038119872322 * s ^ 20
    + 2489074855581261 * s ^ 19
    + 1494896052524448 * s ^ 18
    - 3515991725185084 * s ^ 17
    + 3808970176808809 * s ^ 16
    - 3033809609513283 * s ^ 15
    + 1912348838298283 * s ^ 14
    - 953502566708099 * s ^ 13
    + 357505540548771 * s ^ 12
    - 85145497163909 * s ^ 11
    + 1462857304060 * s ^ 10
    + 9055960260843 * s ^ 9
    - 4356691698909 * s ^ 8
    + 1094849017886 * s ^ 7
    - 140528693039 * s ^ 6
    - 640759605 * s ^ 5
    + 3410679508 * s ^ 4
    - 470922446 * s ^ 3
    + 16711598 * s ^ 2
    + 723226 * s
    - 40526

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient23 (s : ℚ) : ℚ :=
  s ^ 51
    - 58 * s ^ 50
    + 1602 * s ^ 49
    - 28243 * s ^ 48
    + 358936 * s ^ 47
    - 3519223 * s ^ 46
    + 27815288 * s ^ 45
    - 182833108 * s ^ 44
    + 1022756889 * s ^ 43
    - 4950792245 * s ^ 42
    + 20951113605 * s ^ 41
    - 77709702442 * s ^ 40
    + 250667382902 * s ^ 39
    - 686126207506 * s ^ 38
    + 1495280184662 * s ^ 37
    - 2064899341662 * s ^ 36
    - 1321630594284 * s ^ 35
    + 21429642300227 * s ^ 34
    - 91366540588858 * s ^ 33
    + 280247202203810 * s ^ 32
    - 705459902926239 * s ^ 31
    + 1524694080439089 * s ^ 30
    - 2887009044233285 * s ^ 29
    + 4835035231188482 * s ^ 28
    - 7185630318769246 * s ^ 27
    + 9459478397213847 * s ^ 26
    - 10944077815837875 * s ^ 25
    + 10924347763455608 * s ^ 24
    - 9008538037562876 * s ^ 23
    + 5382023010335071 * s ^ 22
    - 824414758078148 * s ^ 21
    - 3551321878004173 * s ^ 20
    + 6716163612066179 * s ^ 19
    - 8092252543038306 * s ^ 18
    + 7707253996519812 * s ^ 17
    - 6096145067008851 * s ^ 16
    + 4024674251251469 * s ^ 15
    - 2169731350824555 * s ^ 14
    + 899370304470426 * s ^ 13
    - 238852766360305 * s ^ 12
    + 198403040741 * s ^ 11
    + 38711887742068 * s ^ 10
    - 22495138202144 * s ^ 9
    + 7345086142795 * s ^ 8
    - 1397525053148 * s ^ 7
    + 86299787278 * s ^ 6
    + 28879504747 * s ^ 5
    - 8696662326 * s ^ 4
    + 907793372 * s ^ 3
    - 16154447 * s ^ 2
    - 2869824 * s
    + 124471

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient24 (s : ℚ) : ℚ :=
  -s ^ 50
    + 48 * s ^ 49
    - 1102 * s ^ 48
    + 16164 * s ^ 47
    - 171473 * s ^ 46
    + 1425715 * s ^ 45
    - 9993614 * s ^ 44
    + 63725506 * s ^ 43
    - 393009398 * s ^ 42
    + 2376281218 * s ^ 41
    - 13645336962 * s ^ 40
    + 71472248928 * s ^ 39
    - 332855257472 * s ^ 38
    + 1364384567909 * s ^ 37
    - 4917934791987 * s ^ 36
    + 15640952440302 * s ^ 35
    - 44106168265262 * s ^ 34
    + 110812191940519 * s ^ 33
    - 248983263195223 * s ^ 32
    + 501308592216244 * s ^ 31
    - 903954667158896 * s ^ 30
    + 1453787759694260 * s ^ 29
    - 2065021618629833 * s ^ 28
    + 2537537009171327 * s ^ 27
    - 2570108030770869 * s ^ 26
    + 1842562217357744 * s ^ 25
    - 155577089046354 * s ^ 24
    - 2428820599043383 * s ^ 23
    + 5525176664151744 * s ^ 22
    - 8493685280732198 * s ^ 21
    + 10629763659097450 * s ^ 20
    - 11403592148262917 * s ^ 19
    + 10654363990787579 * s ^ 18
    - 8658014848079052 * s ^ 17
    + 6029009273128732 * s ^ 16
    - 3480956033532096 * s ^ 15
    + 1549046064955256 * s ^ 14
    - 419642031592448 * s ^ 13
    - 44805032872882 * s ^ 12
    + 130073562131958 * s ^ 11
    - 83848340245843 * s ^ 10
    + 33139805775051 * s ^ 9
    - 8340361266379 * s ^ 8
    + 997375141597 * s ^ 7
    + 129913009243 * s ^ 6
    - 81601438098 * s ^ 5
    + 15912826354 * s ^ 4
    - 1279265862 * s ^ 3
    - 17972536 * s ^ 2
    + 8148332 * s
    - 307040

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient25 (s : ℚ) : ℚ :=
  -s ^ 49
    + 65 * s ^ 48
    - 2000 * s ^ 47
    + 39157 * s ^ 46
    - 551252 * s ^ 45
    + 5965940 * s ^ 44
    - 51750485 * s ^ 43
    + 370070227 * s ^ 42
    - 2225805040 * s ^ 41
    + 11428140377 * s ^ 40
    - 50666429005 * s ^ 39
    + 195743462283 * s ^ 38
    - 663910575086 * s ^ 37
    + 1988678782772 * s ^ 36
    - 5282236267069 * s ^ 35
    + 12455178190514 * s ^ 34
    - 25964820322177 * s ^ 33
    + 47190115307161 * s ^ 32
    - 72110248488712 * s ^ 31
    + 83261212790015 * s ^ 30
    - 38890245008363 * s ^ 29
    - 135975779645843 * s ^ 28
    + 547958047334752 * s ^ 27
    - 1314292786014870 * s ^ 26
    + 2519560750009197 * s ^ 25
    - 4159448653407675 * s ^ 24
    + 6092911254629179 * s ^ 23
    - 8028590933473319 * s ^ 22
    + 9565367034994198 * s ^ 21
    - 10292684101836812 * s ^ 20
    + 9933558573807508 * s ^ 19
    - 8481450965811233 * s ^ 18
    + 6256261884320088 * s ^ 17
    - 3816888700084938 * s ^ 16
    + 1740977195716711 * s ^ 15
    - 384193227267883 * s ^ 14
    - 231643077538293 * s ^ 13
    + 338451213446200 * s ^ 12
    - 229715194650153 * s ^ 11
    + 104504834367754 * s ^ 10
    - 32280064708103 * s ^ 9
    + 5548008429020 * s ^ 8
    + 283262860317 * s ^ 7
    - 479173478197 * s ^ 6
    + 142600046712 * s ^ 5
    - 21584691307 * s ^ 4
    + 1155493909 * s ^ 3
    + 116867160 * s ^ 2
    - 17880992 * s
    + 617592

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient26 (s : ℚ) : ℚ :=
  s ^ 48
    - 56 * s ^ 47
    + 1531 * s ^ 46
    - 27260 * s ^ 45
    + 355455 * s ^ 44
    - 3615961 * s ^ 43
    + 29838722 * s ^ 42
    - 205025987 * s ^ 41
    + 1195316519 * s ^ 40
    - 6000427029 * s ^ 39
    + 26267376666 * s ^ 38
    - 101504515057 * s ^ 37
    + 350669113285 * s ^ 36
    - 1097671810077 * s ^ 35
    + 3154995554357 * s ^ 34
    - 8423241994898 * s ^ 33
    + 21052845177175 * s ^ 32
    - 49424426378893 * s ^ 31
    + 108961425173993 * s ^ 30
    - 225160958412331 * s ^ 29
    + 435300663868719 * s ^ 28
    - 786362022100519 * s ^ 27
    + 1326253547770708 * s ^ 26
    - 2086072677313515 * s ^ 25
    + 3053778234417055 * s ^ 24
    - 4145013639013698 * s ^ 23
    + 5184897376454151 * s ^ 22
    - 5922174180841860 * s ^ 21
    + 6094501421549756 * s ^ 20
    - 5539501123818477 * s ^ 19
    + 4304557520177920 * s ^ 18
    - 2679411388526626 * s ^ 17
    + 1099362991066146 * s ^ 16
    + 49117732298794 * s ^ 15
    - 602844758724935 * s ^ 14
    + 659155135713334 * s ^ 13
    - 461438143587581 * s ^ 12
    + 233493280056837 * s ^ 11
    - 84023582211063 * s ^ 10
    + 18110894061902 * s ^ 9
    + 270519956304 * s ^ 8
    - 1931291216362 * s ^ 7
    + 797092981558 * s ^ 6
    - 177597781056 * s ^ 5
    + 21004969228 * s ^ 4
    - 167413687 * s ^ 3
    - 288828272 * s ^ 2
    + 31357650 * s
    - 1022566

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient27 (s : ℚ) : ℚ :=
  -s ^ 46
    + 47 * s ^ 45
    - 1094 * s ^ 44
    + 17109 * s ^ 43
    - 206025 * s ^ 42
    + 2062478 * s ^ 41
    - 17848751 * s ^ 40
    + 135227563 * s ^ 39
    - 895995911 * s ^ 38
    + 5171327996 * s ^ 37
    - 25958187080 * s ^ 36
    + 113556543650 * s ^ 35
    - 435179087837 * s ^ 34
    + 1472079867928 * s ^ 33
    - 4436377180328 * s ^ 32
    + 12033551545744 * s ^ 31
    - 29678179517248 * s ^ 30
    + 67145337405045 * s ^ 29
    - 140262160584681 * s ^ 28
    + 271447472765054 * s ^ 27
    - 486813253872368 * s ^ 26
    + 806942964321442 * s ^ 25
    - 1229881009861167 * s ^ 24
    + 1709902731234746 * s ^ 23
    - 2143950370524563 * s ^ 22
    + 2383884667295545 * s ^ 21
    - 2286925822914482 * s ^ 20
    + 1793078060480557 * s ^ 19
    - 987476978964478 * s ^ 18
    + 94764045440454 * s ^ 17
    + 614237440934505 * s ^ 16
    - 957322935982839 * s ^ 15
    + 927175854801553 * s ^ 14
    - 668098872368418 * s ^ 13
    + 367171860270649 * s ^ 12
    - 147696826438618 * s ^ 11
    + 36138512422166 * s ^ 10
    + 1042914316001 * s ^ 9
    - 5808412236430 * s ^ 8
    + 2998320732046 * s ^ 7
    - 887043394444 * s ^ 6
    + 158963166339 * s ^ 5
    - 12230771916 * s ^ 4
    - 1563277820 * s ^ 3
    + 490311692 * s ^ 2
    - 44674561 * s
    + 1400751

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient28 (s : ℚ) : ℚ :=
  -s ^ 45
    + 56 * s ^ 44
    - 1507 * s ^ 43
    + 25992 * s ^ 42
    - 323178 * s ^ 41
    + 3089580 * s ^ 40
    - 23670863 * s ^ 39
    + 149822974 * s ^ 38
    - 803535473 * s ^ 37
    + 3739641068 * s ^ 36
    - 15464506133 * s ^ 35
    + 58115331265 * s ^ 34
    - 202017188888 * s ^ 33
    + 655412948698 * s ^ 32
    - 1983153573651 * s ^ 31
    + 5556846270611 * s ^ 30
    - 14293768379618 * s ^ 29
    + 33508680289844 * s ^ 28
    - 71214796741449 * s ^ 27
    + 136606177953854 * s ^ 26
    - 235250745076210 * s ^ 25
    + 360646437416067 * s ^ 24
    - 485006532896501 * s ^ 23
    + 556503845162113 * s ^ 22
    - 511805042162495 * s ^ 21
    + 306572032513472 * s ^ 20
    + 47750471293280 * s ^ 19
    - 466245496295890 * s ^ 18
    + 815071493209966 * s ^ 17
    - 975283279110969 * s ^ 16
    + 908323308709771 * s ^ 15
    - 675453319258290 * s ^ 14
    + 394912403142398 * s ^ 13
    - 169858922588587 * s ^ 12
    + 41353248944689 * s ^ 11
    + 7102601437710 * s ^ 10
    - 13656000378403 * s ^ 9
    + 7936080959376 * s ^ 8
    - 2892547607150 * s ^ 7
    + 692047363618 * s ^ 6
    - 92777747495 * s ^ 5
    - 1120415109 * s ^ 4
    + 3300099474 * s ^ 3
    - 634668845 * s ^ 2
    + 52090429 * s
    - 1589600

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient29 (s : ℚ) : ℚ :=
  2 * s ^ 43
    - 112 * s ^ 42
    + 3068 * s ^ 41
    - 54679 * s ^ 40
    + 711016 * s ^ 39
    - 7170375 * s ^ 38
    + 58217762 * s ^ 37
    - 390249374 * s ^ 36
    + 2199429116 * s ^ 35
    - 10570235858 * s ^ 34
    + 43824402938 * s ^ 33
    - 158333658993 * s ^ 32
    + 502926873777 * s ^ 31
    - 1415046306660 * s ^ 30
    + 3546011116492 * s ^ 29
    - 7931674124768 * s ^ 28
    + 15791484450718 * s ^ 27
    - 27690890509610 * s ^ 26
    + 41743596198437 * s ^ 25
    - 51111458514120 * s ^ 24
    + 42317114382971 * s ^ 23
    + 2874033877970 * s ^ 22
    - 99656551982396 * s ^ 21
    + 247624223718294 * s ^ 20
    - 420310065469171 * s ^ 19
    + 567105600086069 * s ^ 18
    - 633062429641446 * s ^ 17
    + 588699000895853 * s ^ 16
    - 449958374800088 * s ^ 15
    + 271372365878423 * s ^ 14
    - 114920474284532 * s ^ 13
    + 17168225705071 * s ^ 12
    + 21809189180610 * s ^ 11
    - 24599235010643 * s ^ 10
    + 15015395850627 * s ^ 9
    - 6347913916503 * s ^ 8
    + 1882881812774 * s ^ 7
    - 350277224222 * s ^ 6
    + 17093749998 * s ^ 5
    + 12026370391 * s ^ 4
    - 4159827477 * s ^ 3
    + 648351746 * s ^ 2
    - 49774236 * s
    + 1491140

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient30 (s : ℚ) : ℚ :=
  s ^ 41
    - 56 * s ^ 40
    + 1456 * s ^ 39
    - 23459 * s ^ 38
    + 262882 * s ^ 37
    - 2173421 * s ^ 36
    + 13687271 * s ^ 35
    - 66693441 * s ^ 34
    + 253034404 * s ^ 33
    - 757593852 * s ^ 32
    + 1958771710 * s ^ 31
    - 5998308033 * s ^ 30
    + 27515573039 * s ^ 29
    - 138756180196 * s ^ 28
    + 603073542968 * s ^ 27
    - 2164063095038 * s ^ 26
    + 6488963179251 * s ^ 25
    - 16550249721009 * s ^ 24
    + 36416914739971 * s ^ 23
    - 69781195448469 * s ^ 22
    + 116997089082877 * s ^ 21
    - 171699015015685 * s ^ 20
    + 219632675098343 * s ^ 19
    - 242494387106463 * s ^ 18
    + 226790497795915 * s ^ 17
    - 173027880924379 * s ^ 16
    + 98117191236844 * s ^ 15
    - 27436488851617 * s ^ 14
    - 18942518249529 * s ^ 13
    + 35861219481324 * s ^ 12
    - 31836843097250 * s ^ 11
    + 19926793189982 * s ^ 10
    - 9374169830815 * s ^ 9
    + 3262626483068 * s ^ 8
    - 757175841497 * s ^ 7
    + 64992086398 * s ^ 6
    + 30140977445 * s ^ 5
    - 15661035056 * s ^ 4
    + 3801697984 * s ^ 3
    - 528413196 * s ^ 2
    + 38828762 * s
    - 1149434

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient31 (s : ℚ) : ℚ :=
  -4 * s ^ 39
    + 220 * s ^ 38
    - 5838 * s ^ 37
    + 99601 * s ^ 36
    - 1227829 * s ^ 35
    + 11651262 * s ^ 34
    - 88538344 * s ^ 33
    + 553530503 * s ^ 32
    - 2903950974 * s ^ 31
    + 12982013255 * s ^ 30
    - 50078397760 * s ^ 29
    + 168477936621 * s ^ 28
    - 498885394574 * s ^ 27
    + 1310220584780 * s ^ 26
    - 3069484801955 * s ^ 25
    + 6435144807737 * s ^ 24
    - 12073519462116 * s ^ 23
    + 20195859422611 * s ^ 22
    - 29871324527584 * s ^ 21
    + 38504814523766 * s ^ 20
    - 42155170706902 * s ^ 19
    + 37151804634476 * s ^ 18
    - 22523341430045 * s ^ 17
    + 1641315663265 * s ^ 16
    + 18626713611116 * s ^ 15
    - 31382107916082 * s ^ 14
    + 33570850213065 * s ^ 13
    - 27280852152330 * s ^ 12
    + 17568856042336 * s ^ 11
    - 8970375355702 * s ^ 10
    + 3503531357685 * s ^ 9
    - 929764954742 * s ^ 8
    + 82639551382 * s ^ 7
    + 63106297590 * s ^ 6
    - 39353816777 * s ^ 5
    + 12692169074 * s ^ 4
    - 2640745035 * s ^ 3
    + 343061886 * s ^ 2
    - 24508279 * s
    + 720641

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient32 (s : ℚ) : ℚ :=
  s ^ 37
    - 52 * s ^ 36
    + 1345 * s ^ 35
    - 22990 * s ^ 34
    + 289936 * s ^ 33
    - 2850022 * s ^ 32
    + 22523765 * s ^ 31
    - 145894672 * s ^ 30
    + 784518459 * s ^ 29
    - 3532611587 * s ^ 28
    + 13391973310 * s ^ 27
    - 42825136456 * s ^ 26
    + 115229502618 * s ^ 25
    - 258288332668 * s ^ 24
    + 470015730352 * s ^ 23
    - 646653716552 * s ^ 22
    + 498836130031 * s ^ 21
    + 458965726090 * s ^ 20
    - 2739017789349 * s ^ 19
    + 6512825227683 * s ^ 18
    - 11225462414312 * s ^ 17
    + 15537181630379 * s ^ 16
    - 17842742832561 * s ^ 15
    + 17178003625279 * s ^ 14
    - 13858966486548 * s ^ 13
    + 9283499584542 * s ^ 12
    - 5043696614193 * s ^ 11
    + 2096216990350 * s ^ 10
    - 548750234261 * s ^ 9
    - 18291699985 * s ^ 8
    + 112097123522 * s ^ 7
    - 69386113989 * s ^ 6
    + 26758752533 * s ^ 5
    - 7308175425 * s ^ 4
    + 1405097529 * s ^ 3
    - 175468789 * s ^ 2
    + 12328335 * s
    - 361648

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient33 (s : ℚ) : ℚ :=
  2 * s ^ 35
    - 108 * s ^ 34
    + 2781 * s ^ 33
    - 45550 * s ^ 32
    + 534030 * s ^ 31
    - 4781212 * s ^ 30
    + 34054148 * s ^ 29
    - 198474942 * s ^ 28
    + 966283529 * s ^ 27
    - 3992403286 * s ^ 26
    + 14176517551 * s ^ 25
    - 43713262496 * s ^ 24
    + 118065711479 * s ^ 23
    - 281298415962 * s ^ 22
    + 594303809224 * s ^ 21
    - 1116577742969 * s ^ 20
    + 1865498508829 * s ^ 19
    - 2762738705147 * s ^ 18
    + 3604309065393 * s ^ 17
    - 4105626138079 * s ^ 16
    + 4036412671769 * s ^ 15
    - 3371937554955 * s ^ 14
    + 2333965569782 * s ^ 13
    - 1269196249469 * s ^ 12
    + 459163650629 * s ^ 11
    - 6478784491 * s ^ 10
    - 149348013437 * s ^ 9
    + 140553454028 * s ^ 8
    - 82957100772 * s ^ 7
    + 36089511393 * s ^ 6
    - 12027179158 * s ^ 5
    + 3056395234 * s ^ 4
    - 565414111 * s ^ 3
    + 69211216 * s ^ 2
    - 4826676 * s
    + 141803

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient34 (s : ℚ) : ℚ :=
  -s ^ 33
    + 51 * s ^ 32
    - 1246 * s ^ 31
    + 19440 * s ^ 30
    - 217823 * s ^ 29
    + 1868530 * s ^ 28
    - 12769317 * s ^ 27
    + 71391273 * s ^ 26
    - 332556894 * s ^ 25
    + 1306926935 * s ^ 24
    - 4368383572 * s ^ 23
    + 12475475582 * s ^ 22
    - 30487634908 * s ^ 21
    + 63673255818 * s ^ 20
    - 113158853243 * s ^ 19
    + 169720909593 * s ^ 18
    - 211632717494 * s ^ 17
    + 212878578200 * s ^ 16
    - 160020032158 * s ^ 15
    + 64898200478 * s ^ 14
    + 39486105406 * s ^ 13
    - 117688497751 * s ^ 12
    + 150042411623 * s ^ 11
    - 138742533141 * s ^ 10
    + 101725378989 * s ^ 9
    - 60510417460 * s ^ 8
    + 29326291612 * s ^ 7
    - 11555845464 * s ^ 6
    + 3666694745 * s ^ 5
    - 910803761 * s ^ 4
    + 166692629 * s ^ 3
    - 20312073 * s ^ 2
    + 1417252 * s
    - 41850

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient35 (s : ℚ) : ℚ :=
  s ^ 30
    - 49 * s ^ 29
    + 1145 * s ^ 28
    - 16981 * s ^ 27
    + 179433 * s ^ 26
    - 1437512 * s ^ 25
    + 9071162 * s ^ 24
    - 46241605 * s ^ 23
    + 193797264 * s ^ 22
    - 676241482 * s ^ 21
    + 1983430925 * s ^ 20
    - 4927099973 * s ^ 19
    + 10436752605 * s ^ 18
    - 18982991966 * s ^ 17
    + 29888017811 * s ^ 16
    - 41129720386 * s ^ 15
    + 49993699576 * s ^ 14
    - 54152565883 * s ^ 13
    + 52440173144 * s ^ 12
    - 45159633233 * s ^ 11
    + 34139316520 * s ^ 10
    - 22291853876 * s ^ 9
    + 12391648145 * s ^ 8
    - 5802401673 * s ^ 7
    + 2266729691 * s ^ 6
    - 725563950 * s ^ 5
    + 182996710 * s ^ 4
    - 33934637 * s ^ 3
    + 4173862 * s ^ 2
    - 293530 * s
    + 8742

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient36 (s : ℚ) : ℚ :=
  -s ^ 26
    + 45 * s ^ 25
    - 958 * s ^ 24
    + 12833 * s ^ 23
    - 121368 * s ^ 22
    + 861952 * s ^ 21
    - 4773625 * s ^ 20
    + 21133015 * s ^ 19
    - 76059062 * s ^ 18
    + 225137616 * s ^ 17
    - 552374256 * s ^ 16
    + 1128861612 * s ^ 15
    - 1926840275 * s ^ 14
    + 2749947049 * s ^ 13
    - 3282047711 * s ^ 12
    + 3276031036 * s ^ 11
    - 2737911784 * s ^ 10
    + 1921780670 * s ^ 9
    - 1138289987 * s ^ 8
    + 570451308 * s ^ 7
    - 240061136 * s ^ 6
    + 82570164 * s ^ 5
    - 22060387 * s ^ 4
    + 4251472 * s ^ 3
    - 535290 * s ^ 2
    + 38220 * s
    - 1152

/-- Coefficient of the indicated power of the raw chart variable. -/
def numeratorProductCoefficient37 (s : ℚ) : ℚ :=
  s ^ 20
    - 36 * s ^ 19
    + 602 * s ^ 18
    - 6209 * s ^ 17
    + 44232 * s ^ 16
    - 230965 * s ^ 15
    + 915548 * s ^ 14
    - 2815438 * s ^ 13
    + 6805471 * s ^ 12
    - 13022997 * s ^ 11
    + 19774503 * s ^ 10
    - 23777858 * s ^ 9
    + 22499201 * s ^ 8
    - 16567260 * s ^ 7
    + 9333097 * s ^ 6
    - 3923891 * s ^ 5
    + 1187971 * s ^ 4
    - 245890 * s ^ 3
    + 32198 * s ^ 2
    - 2352 * s
    + 72

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def numeratorProduct (r s : ℚ) : ℚ :=
  numeratorProductCoefficient0 s +
    numeratorProductCoefficient1 s * r +
    numeratorProductCoefficient2 s * r ^ 2 +
    numeratorProductCoefficient3 s * r ^ 3 +
    numeratorProductCoefficient4 s * r ^ 4 +
    numeratorProductCoefficient5 s * r ^ 5 +
    numeratorProductCoefficient6 s * r ^ 6 +
    numeratorProductCoefficient7 s * r ^ 7 +
    numeratorProductCoefficient8 s * r ^ 8 +
    numeratorProductCoefficient9 s * r ^ 9 +
    numeratorProductCoefficient10 s * r ^ 10 +
    numeratorProductCoefficient11 s * r ^ 11 +
    numeratorProductCoefficient12 s * r ^ 12 +
    numeratorProductCoefficient13 s * r ^ 13 +
    numeratorProductCoefficient14 s * r ^ 14 +
    numeratorProductCoefficient15 s * r ^ 15 +
    numeratorProductCoefficient16 s * r ^ 16 +
    numeratorProductCoefficient17 s * r ^ 17 +
    numeratorProductCoefficient18 s * r ^ 18 +
    numeratorProductCoefficient19 s * r ^ 19 +
    numeratorProductCoefficient20 s * r ^ 20 +
    numeratorProductCoefficient21 s * r ^ 21 +
    numeratorProductCoefficient22 s * r ^ 22 +
    numeratorProductCoefficient23 s * r ^ 23 +
    numeratorProductCoefficient24 s * r ^ 24 +
    numeratorProductCoefficient25 s * r ^ 25 +
    numeratorProductCoefficient26 s * r ^ 26 +
    numeratorProductCoefficient27 s * r ^ 27 +
    numeratorProductCoefficient28 s * r ^ 28 +
    numeratorProductCoefficient29 s * r ^ 29 +
    numeratorProductCoefficient30 s * r ^ 30 +
    numeratorProductCoefficient31 s * r ^ 31 +
    numeratorProductCoefficient32 s * r ^ 32 +
    numeratorProductCoefficient33 s * r ^ 33 +
    numeratorProductCoefficient34 s * r ^ 34 +
    numeratorProductCoefficient35 s * r ^ 35 +
    numeratorProductCoefficient36 s * r ^ 36 +
    numeratorProductCoefficient37 s * r ^ 37

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_0 (s : ℚ) :
    numeratorProductCoefficient0 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient0,
    numeratorStep3Coefficient0,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_1 (s : ℚ) :
    numeratorProductCoefficient1 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient1,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_2 (s : ℚ) :
    numeratorProductCoefficient2 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient2,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_3 (s : ℚ) :
    numeratorProductCoefficient3 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient3,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_4 (s : ℚ) :
    numeratorProductCoefficient4 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient4,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_5 (s : ℚ) :
    numeratorProductCoefficient5 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient5,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_6 (s : ℚ) :
    numeratorProductCoefficient6 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient6,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_7 (s : ℚ) :
    numeratorProductCoefficient7 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient7,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_8 (s : ℚ) :
    numeratorProductCoefficient8 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient8,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_9 (s : ℚ) :
    numeratorProductCoefficient9 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient9,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_10 (s : ℚ) :
    numeratorProductCoefficient10 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient10,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_11 (s : ℚ) :
    numeratorProductCoefficient11 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient11,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_12 (s : ℚ) :
    numeratorProductCoefficient12 s =
    numeratorStep3Coefficient0 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient12,
    numeratorStep3Coefficient0,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_13 (s : ℚ) :
    numeratorProductCoefficient13 s =
    numeratorStep3Coefficient1 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient13,
    numeratorStep3Coefficient1,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_14 (s : ℚ) :
    numeratorProductCoefficient14 s =
    numeratorStep3Coefficient2 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient14,
    numeratorStep3Coefficient2,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_15 (s : ℚ) :
    numeratorProductCoefficient15 s =
    numeratorStep3Coefficient3 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient15,
    numeratorStep3Coefficient3,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_16 (s : ℚ) :
    numeratorProductCoefficient16 s =
    numeratorStep3Coefficient4 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient16,
    numeratorStep3Coefficient4,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_17 (s : ℚ) :
    numeratorProductCoefficient17 s =
    numeratorStep3Coefficient5 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient17,
    numeratorStep3Coefficient5,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_18 (s : ℚ) :
    numeratorProductCoefficient18 s =
    numeratorStep3Coefficient6 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient18,
    numeratorStep3Coefficient6,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_19 (s : ℚ) :
    numeratorProductCoefficient19 s =
    numeratorStep3Coefficient7 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient19,
    numeratorStep3Coefficient7,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_20 (s : ℚ) :
    numeratorProductCoefficient20 s =
    numeratorStep3Coefficient8 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient20,
    numeratorStep3Coefficient8,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_21 (s : ℚ) :
    numeratorProductCoefficient21 s =
    numeratorStep3Coefficient9 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient21,
    numeratorStep3Coefficient9,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_22 (s : ℚ) :
    numeratorProductCoefficient22 s =
    numeratorStep3Coefficient10 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient22,
    numeratorStep3Coefficient10,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_23 (s : ℚ) :
    numeratorProductCoefficient23 s =
    numeratorStep3Coefficient11 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient23,
    numeratorStep3Coefficient11,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_24 (s : ℚ) :
    numeratorProductCoefficient24 s =
    numeratorStep3Coefficient12 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient24,
    numeratorStep3Coefficient12,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_25 (s : ℚ) :
    numeratorProductCoefficient25 s =
    numeratorStep3Coefficient13 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient1 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient0 s
    := by
  simp only [numeratorProductCoefficient25,
    numeratorStep3Coefficient13,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1,
    rawUnitNineNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_26 (s : ℚ) :
    numeratorProductCoefficient26 s =
    numeratorStep3Coefficient14 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient2 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient1 s
    := by
  simp only [numeratorProductCoefficient26,
    numeratorStep3Coefficient14,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2,
    rawUnitNineNumeratorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_27 (s : ℚ) :
    numeratorProductCoefficient27 s =
    numeratorStep3Coefficient15 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient3 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient2 s
    := by
  simp only [numeratorProductCoefficient27,
    numeratorStep3Coefficient15,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3,
    rawUnitNineNumeratorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_28 (s : ℚ) :
    numeratorProductCoefficient28 s =
    numeratorStep3Coefficient16 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient4 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient3 s
    := by
  simp only [numeratorProductCoefficient28,
    numeratorStep3Coefficient16,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4,
    rawUnitNineNumeratorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_29 (s : ℚ) :
    numeratorProductCoefficient29 s =
    numeratorStep3Coefficient17 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient5 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient4 s
    := by
  simp only [numeratorProductCoefficient29,
    numeratorStep3Coefficient17,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5,
    rawUnitNineNumeratorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_30 (s : ℚ) :
    numeratorProductCoefficient30 s =
    numeratorStep3Coefficient18 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient6 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient5 s
    := by
  simp only [numeratorProductCoefficient30,
    numeratorStep3Coefficient18,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6,
    rawUnitNineNumeratorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_31 (s : ℚ) :
    numeratorProductCoefficient31 s =
    numeratorStep3Coefficient19 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient7 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient6 s
    := by
  simp only [numeratorProductCoefficient31,
    numeratorStep3Coefficient19,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7,
    rawUnitNineNumeratorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_32 (s : ℚ) :
    numeratorProductCoefficient32 s =
    numeratorStep3Coefficient20 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient8 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient7 s
    := by
  simp only [numeratorProductCoefficient32,
    numeratorStep3Coefficient20,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8,
    rawUnitNineNumeratorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_33 (s : ℚ) :
    numeratorProductCoefficient33 s =
    numeratorStep3Coefficient21 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient9 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient8 s
    := by
  simp only [numeratorProductCoefficient33,
    numeratorStep3Coefficient21,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9,
    rawUnitNineNumeratorCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_34 (s : ℚ) :
    numeratorProductCoefficient34 s =
    numeratorStep3Coefficient22 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient10 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient9 s
    := by
  simp only [numeratorProductCoefficient34,
    numeratorStep3Coefficient22,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10,
    rawUnitNineNumeratorCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_35 (s : ℚ) :
    numeratorProductCoefficient35 s =
    numeratorStep3Coefficient23 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient11 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient10 s
    := by
  simp only [numeratorProductCoefficient35,
    numeratorStep3Coefficient23,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11,
    rawUnitNineNumeratorCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_36 (s : ℚ) :
    numeratorProductCoefficient36 s =
    numeratorStep3Coefficient24 s *
        rawUnitNineNumeratorCoefficient12 s
      + numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient11 s
    := by
  simp only [numeratorProductCoefficient36,
    numeratorStep3Coefficient24,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12,
    rawUnitNineNumeratorCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem numeratorProductCoefficient_product_certificate_37 (s : ℚ) :
    numeratorProductCoefficient37 s =
    numeratorStep3Coefficient25 s *
        rawUnitNineNumeratorCoefficient12 s
    := by
  simp only [numeratorProductCoefficient37,
    numeratorStep3Coefficient25,
    rawUnitNineNumeratorCoefficient12]
  ring

/-- Checked staged polynomial-product identity. -/
theorem numeratorProduct_eq_numeratorStep3_mul_rawUnitNineNumerator (r s : ℚ) :
    numeratorProduct r s = numeratorStep3 r s * rawUnitNineNumerator r s := by
  have h0 := numeratorProductCoefficient_product_certificate_0 s
  have h1 := numeratorProductCoefficient_product_certificate_1 s
  have h2 := numeratorProductCoefficient_product_certificate_2 s
  have h3 := numeratorProductCoefficient_product_certificate_3 s
  have h4 := numeratorProductCoefficient_product_certificate_4 s
  have h5 := numeratorProductCoefficient_product_certificate_5 s
  have h6 := numeratorProductCoefficient_product_certificate_6 s
  have h7 := numeratorProductCoefficient_product_certificate_7 s
  have h8 := numeratorProductCoefficient_product_certificate_8 s
  have h9 := numeratorProductCoefficient_product_certificate_9 s
  have h10 := numeratorProductCoefficient_product_certificate_10 s
  have h11 := numeratorProductCoefficient_product_certificate_11 s
  have h12 := numeratorProductCoefficient_product_certificate_12 s
  have h13 := numeratorProductCoefficient_product_certificate_13 s
  have h14 := numeratorProductCoefficient_product_certificate_14 s
  have h15 := numeratorProductCoefficient_product_certificate_15 s
  have h16 := numeratorProductCoefficient_product_certificate_16 s
  have h17 := numeratorProductCoefficient_product_certificate_17 s
  have h18 := numeratorProductCoefficient_product_certificate_18 s
  have h19 := numeratorProductCoefficient_product_certificate_19 s
  have h20 := numeratorProductCoefficient_product_certificate_20 s
  have h21 := numeratorProductCoefficient_product_certificate_21 s
  have h22 := numeratorProductCoefficient_product_certificate_22 s
  have h23 := numeratorProductCoefficient_product_certificate_23 s
  have h24 := numeratorProductCoefficient_product_certificate_24 s
  have h25 := numeratorProductCoefficient_product_certificate_25 s
  have h26 := numeratorProductCoefficient_product_certificate_26 s
  have h27 := numeratorProductCoefficient_product_certificate_27 s
  have h28 := numeratorProductCoefficient_product_certificate_28 s
  have h29 := numeratorProductCoefficient_product_certificate_29 s
  have h30 := numeratorProductCoefficient_product_certificate_30 s
  have h31 := numeratorProductCoefficient_product_certificate_31 s
  have h32 := numeratorProductCoefficient_product_certificate_32 s
  have h33 := numeratorProductCoefficient_product_certificate_33 s
  have h34 := numeratorProductCoefficient_product_certificate_34 s
  have h35 := numeratorProductCoefficient_product_certificate_35 s
  have h36 := numeratorProductCoefficient_product_certificate_36 s
  have h37 := numeratorProductCoefficient_product_certificate_37 s
  simp only [numeratorProduct, numeratorStep3, rawUnitNineNumerator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 + r ^ 36 * h36 + r ^ 37 * h37

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient1 (s : ℚ) : ℚ :=
  s ^ 18
    - 4 * s ^ 17
    + 10 * s ^ 16
    - 18 * s ^ 15
    + 25 * s ^ 14
    - 28 * s ^ 13
    + 25 * s ^ 12
    - 18 * s ^ 11
    + 10 * s ^ 10
    - 4 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient2 (s : ℚ) : ℚ :=
  3 * s ^ 18
    - 31 * s ^ 17
    + 108 * s ^ 16
    - 258 * s ^ 15
    + 470 * s ^ 14
    - 692 * s ^ 13
    + 855 * s ^ 12
    - 889 * s ^ 11
    + 789 * s ^ 10
    - 593 * s ^ 9
    + 374 * s ^ 8
    - 196 * s ^ 7
    + 82 * s ^ 6
    - 28 * s ^ 5
    + 7 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient3 (s : ℚ) : ℚ :=
  s ^ 21
    - 10 * s ^ 20
    + 55 * s ^ 19
    - 212 * s ^ 18
    + 595 * s ^ 17
    - 1247 * s ^ 16
    + 2203 * s ^ 15
    - 3342 * s ^ 14
    + 4456 * s ^ 13
    - 5245 * s ^ 12
    + 5378 * s ^ 11
    - 4824 * s ^ 10
    + 3699 * s ^ 9
    - 2398 * s ^ 8
    + 1291 * s ^ 7
    - 554 * s ^ 6
    + 193 * s ^ 5
    - 42 * s ^ 4
    + s ^ 3
    + 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient4 (s : ℚ) : ℚ :=
  -4 * s ^ 20
    + 29 * s ^ 19
    - 125 * s ^ 18
    + 387 * s ^ 17
    - 734 * s ^ 16
    + 542 * s ^ 15
    + 608 * s ^ 14
    - 2957 * s ^ 13
    + 5845 * s ^ 12
    - 8116 * s ^ 11
    + 9004 * s ^ 10
    - 7900 * s ^ 9
    + 5652 * s ^ 8
    - 3238 * s ^ 7
    + 1424 * s ^ 6
    - 473 * s ^ 5
    + 17 * s ^ 4
    + 63 * s ^ 3
    - 23 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient5 (s : ℚ) : ℚ :=
  -2 * s ^ 20
    + 30 * s ^ 19
    - 170 * s ^ 18
    + 709 * s ^ 17
    - 2303 * s ^ 16
    + 5280 * s ^ 15
    - 8709 * s ^ 14
    + 12297 * s ^ 13
    - 15067 * s ^ 12
    + 16668 * s ^ 11
    - 16525 * s ^ 10
    + 13474 * s ^ 9
    - 9402 * s ^ 8
    + 5178 * s ^ 7
    - 2004 * s ^ 6
    + 221 * s ^ 5
    + 686 * s ^ 4
    - 488 * s ^ 3
    + 112 * s ^ 2
    + 15 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient6 (s : ℚ) : ℚ :=
  5 * s ^ 19
    - 43 * s ^ 18
    + 154 * s ^ 17
    - 646 * s ^ 16
    + 2323 * s ^ 15
    - 4524 * s ^ 14
    + 4045 * s ^ 13
    - 695 * s ^ 12
    - 4966 * s ^ 11
    + 8941 * s ^ 10
    - 8747 * s ^ 9
    + 7280 * s ^ 8
    - 3533 * s ^ 7
    - 292 * s ^ 6
    + 3117 * s ^ 5
    - 3971 * s ^ 4
    + 1915 * s ^ 3
    - 258 * s ^ 2
    - 105 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient7 (s : ℚ) : ℚ :=
  s ^ 19
    - 14 * s ^ 18
    + 43 * s ^ 17
    - 58 * s ^ 16
    + 883 * s ^ 15
    - 4850 * s ^ 14
    + 11616 * s ^ 13
    - 16295 * s ^ 12
    + 17697 * s ^ 11
    - 13884 * s ^ 10
    + 9182 * s ^ 9
    - 6235 * s ^ 8
    - 1271 * s ^ 7
    + 9254 * s ^ 6
    - 14440 * s ^ 5
    + 12354 * s ^ 4
    - 4390 * s ^ 3
    - 48 * s ^ 2
    + 455 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient8 (s : ℚ) : ℚ :=
  -25 * s ^ 17
    + 329 * s ^ 16
    - 1493 * s ^ 15
    + 2589 * s ^ 14
    - 119 * s ^ 13
    - 5614 * s ^ 12
    + 8923 * s ^ 11
    - 8737 * s ^ 10
    + 3349 * s ^ 9
    - 3608 * s ^ 8
    + 18217 * s ^ 7
    - 32893 * s ^ 6
    + 37047 * s ^ 5
    - 23698 * s ^ 4
    + 4753 * s ^ 3
    + 2321 * s ^ 2
    - 1340 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient9 (s : ℚ) : ℚ :=
  -7 * s ^ 17
    + 140 * s ^ 16
    - 1056 * s ^ 15
    + 3852 * s ^ 14
    - 7093 * s ^ 13
    + 5642 * s ^ 12
    + 1502 * s ^ 11
    - 8629 * s ^ 10
    + 8481 * s ^ 9
    + 12688 * s ^ 8
    - 46226 * s ^ 7
    + 64767 * s ^ 6
    - 56547 * s ^ 5
    + 23989 * s ^ 4
    + 3784 * s ^ 3
    - 8066 * s ^ 2
    + 2770 * s
    + 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient10 (s : ℚ) : ℚ :=
  -s ^ 17
    + 31 * s ^ 16
    - 353 * s ^ 15
    + 2024 * s ^ 14
    - 6557 * s ^ 13
    + 12682 * s ^ 12
    - 14950 * s ^ 11
    + 8165 * s ^ 10
    + 12786 * s ^ 9
    - 48173 * s ^ 8
    + 75403 * s ^ 7
    - 73516 * s ^ 6
    + 42141 * s ^ 5
    + 1608 * s ^ 4
    - 22724 * s ^ 3
    + 15487 * s ^ 2
    - 4017 * s
    - 36

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient11 (s : ℚ) : ℚ :=
  2 * s ^ 16
    - 44 * s ^ 15
    + 400 * s ^ 14
    - 1988 * s ^ 13
    + 6134 * s ^ 12
    - 13305 * s ^ 11
    + 23924 * s ^ 10
    - 39011 * s ^ 9
    + 52157 * s ^ 8
    - 48910 * s ^ 7
    + 25372 * s ^ 6
    + 10690 * s ^ 5
    - 39273 * s ^ 4
    + 38435 * s ^ 3
    - 18638 * s ^ 2
    + 3973 * s
    + 82

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient12 (s : ℚ) : ℚ :=
  -s ^ 15
    + 17 * s ^ 14
    - 112 * s ^ 13
    + 331 * s ^ 12
    - 229 * s ^ 11
    - 1127 * s ^ 10
    + 2639 * s ^ 9
    + 540 * s ^ 8
    - 11891 * s ^ 7
    + 29231 * s ^ 6
    - 46170 * s ^ 5
    + 49923 * s ^ 4
    - 34439 * s ^ 3
    + 13903 * s ^ 2
    - 2501 * s
    - 114

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient13 (s : ℚ) : ℚ :=
  2 * s ^ 13
    - 38 * s ^ 12
    + 314 * s ^ 11
    - 1494 * s ^ 10
    + 4623 * s ^ 9
    - 10191 * s ^ 8
    + 17586 * s ^ 7
    - 25483 * s ^ 6
    + 30420 * s ^ 5
    - 27083 * s ^ 4
    + 16216 * s ^ 3
    - 5815 * s ^ 2
    + 847 * s
    + 96

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient14 (s : ℚ) : ℚ :=
  -s ^ 11
    + 19 * s ^ 10
    - 158 * s ^ 9
    + 755 * s ^ 8
    - 2290 * s ^ 7
    + 4596 * s ^ 6
    - 6170 * s ^ 5
    + 5482 * s ^ 4
    - 3117 * s ^ 3
    + 1001 * s ^ 2
    - 72 * s
    - 45

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep1Coefficient15 (s : ℚ) : ℚ :=
  s ^ 4
    - 8 * s ^ 3
    + 22 * s ^ 2
    - 24 * s
    + 9

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def denominatorStep1 (r s : ℚ) : ℚ :=
  denominatorStep1Coefficient0 s +
    denominatorStep1Coefficient1 s * r +
    denominatorStep1Coefficient2 s * r ^ 2 +
    denominatorStep1Coefficient3 s * r ^ 3 +
    denominatorStep1Coefficient4 s * r ^ 4 +
    denominatorStep1Coefficient5 s * r ^ 5 +
    denominatorStep1Coefficient6 s * r ^ 6 +
    denominatorStep1Coefficient7 s * r ^ 7 +
    denominatorStep1Coefficient8 s * r ^ 8 +
    denominatorStep1Coefficient9 s * r ^ 9 +
    denominatorStep1Coefficient10 s * r ^ 10 +
    denominatorStep1Coefficient11 s * r ^ 11 +
    denominatorStep1Coefficient12 s * r ^ 12 +
    denominatorStep1Coefficient13 s * r ^ 13 +
    denominatorStep1Coefficient14 s * r ^ 14 +
    denominatorStep1Coefficient15 s * r ^ 15

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_0 (s : ℚ) :
    denominatorStep1Coefficient0 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [denominatorStep1Coefficient0,
    rawUnitOneDenominatorCoefficient0,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_1 (s : ℚ) :
    denominatorStep1Coefficient1 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient1 s
      + rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [denominatorStep1Coefficient1,
    rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_2 (s : ℚ) :
    denominatorStep1Coefficient2 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient2 s
      + rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient1 s
      + rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [denominatorStep1Coefficient2,
    rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_3 (s : ℚ) :
    denominatorStep1Coefficient3 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient3 s
      + rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient2 s
      + rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient1 s
      + rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [denominatorStep1Coefficient3,
    rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_4 (s : ℚ) :
    denominatorStep1Coefficient4 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient4 s
      + rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient3 s
      + rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient2 s
      + rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient1 s
      + rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [denominatorStep1Coefficient4,
    rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_5 (s : ℚ) :
    denominatorStep1Coefficient5 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient5 s
      + rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient4 s
      + rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient3 s
      + rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient2 s
      + rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient1 s
      + rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [denominatorStep1Coefficient5,
    rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_6 (s : ℚ) :
    denominatorStep1Coefficient6 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient6 s
      + rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient5 s
      + rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient4 s
      + rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient3 s
      + rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient2 s
      + rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient1 s
      + rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [denominatorStep1Coefficient6,
    rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_7 (s : ℚ) :
    denominatorStep1Coefficient7 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient7 s
      + rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient6 s
      + rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient5 s
      + rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient4 s
      + rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient3 s
      + rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient2 s
      + rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient1 s
      + rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [denominatorStep1Coefficient7,
    rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
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
theorem denominatorStep1Coefficient_product_certificate_8 (s : ℚ) :
    denominatorStep1Coefficient8 s =
    rawUnitOneDenominatorCoefficient0 s *
        rawUnitTwoDenominatorCoefficient8 s
      + rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient7 s
      + rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient6 s
      + rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient5 s
      + rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient4 s
      + rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient3 s
      + rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient2 s
      + rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient1 s
    := by
  simp only [denominatorStep1Coefficient8,
    rawUnitOneDenominatorCoefficient0,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
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
theorem denominatorStep1Coefficient_product_certificate_9 (s : ℚ) :
    denominatorStep1Coefficient9 s =
    rawUnitOneDenominatorCoefficient1 s *
        rawUnitTwoDenominatorCoefficient8 s
      + rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient7 s
      + rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient6 s
      + rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient5 s
      + rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient4 s
      + rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient3 s
      + rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient2 s
    := by
  simp only [denominatorStep1Coefficient9,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_10 (s : ℚ) :
    denominatorStep1Coefficient10 s =
    rawUnitOneDenominatorCoefficient2 s *
        rawUnitTwoDenominatorCoefficient8 s
      + rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient7 s
      + rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient6 s
      + rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient5 s
      + rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient4 s
      + rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient3 s
    := by
  simp only [denominatorStep1Coefficient10,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_11 (s : ℚ) :
    denominatorStep1Coefficient11 s =
    rawUnitOneDenominatorCoefficient3 s *
        rawUnitTwoDenominatorCoefficient8 s
      + rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient7 s
      + rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient6 s
      + rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient5 s
      + rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient4 s
    := by
  simp only [denominatorStep1Coefficient11,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_12 (s : ℚ) :
    denominatorStep1Coefficient12 s =
    rawUnitOneDenominatorCoefficient4 s *
        rawUnitTwoDenominatorCoefficient8 s
      + rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient7 s
      + rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient6 s
      + rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient5 s
    := by
  simp only [denominatorStep1Coefficient12,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_13 (s : ℚ) :
    denominatorStep1Coefficient13 s =
    rawUnitOneDenominatorCoefficient5 s *
        rawUnitTwoDenominatorCoefficient8 s
      + rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient7 s
      + rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient6 s
    := by
  simp only [denominatorStep1Coefficient13,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_14 (s : ℚ) :
    denominatorStep1Coefficient14 s =
    rawUnitOneDenominatorCoefficient6 s *
        rawUnitTwoDenominatorCoefficient8 s
      + rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient7 s
    := by
  simp only [denominatorStep1Coefficient14,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep1Coefficient_product_certificate_15 (s : ℚ) :
    denominatorStep1Coefficient15 s =
    rawUnitOneDenominatorCoefficient7 s *
        rawUnitTwoDenominatorCoefficient8 s
    := by
  simp only [denominatorStep1Coefficient15,
    rawUnitOneDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem denominatorStep1_eq_rawUnitOneDenominator_mul_rawUnitTwoDenominator (r s : ℚ) :
    denominatorStep1 r s = rawUnitOneDenominator r s * rawUnitTwoDenominator r s := by
  have h0 := denominatorStep1Coefficient_product_certificate_0 s
  have h1 := denominatorStep1Coefficient_product_certificate_1 s
  have h2 := denominatorStep1Coefficient_product_certificate_2 s
  have h3 := denominatorStep1Coefficient_product_certificate_3 s
  have h4 := denominatorStep1Coefficient_product_certificate_4 s
  have h5 := denominatorStep1Coefficient_product_certificate_5 s
  have h6 := denominatorStep1Coefficient_product_certificate_6 s
  have h7 := denominatorStep1Coefficient_product_certificate_7 s
  have h8 := denominatorStep1Coefficient_product_certificate_8 s
  have h9 := denominatorStep1Coefficient_product_certificate_9 s
  have h10 := denominatorStep1Coefficient_product_certificate_10 s
  have h11 := denominatorStep1Coefficient_product_certificate_11 s
  have h12 := denominatorStep1Coefficient_product_certificate_12 s
  have h13 := denominatorStep1Coefficient_product_certificate_13 s
  have h14 := denominatorStep1Coefficient_product_certificate_14 s
  have h15 := denominatorStep1Coefficient_product_certificate_15 s
  simp only [denominatorStep1, rawUnitOneDenominator, rawUnitTwoDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient1 (s : ℚ) : ℚ :=
  s ^ 24
    - 4 * s ^ 23
    + 10 * s ^ 22
    - 18 * s ^ 21
    + 25 * s ^ 20
    - 28 * s ^ 19
    + 25 * s ^ 18
    - 18 * s ^ 17
    + 10 * s ^ 16
    - 4 * s ^ 15
    + s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient2 (s : ℚ) : ℚ :=
  -2 * s ^ 26
    + 14 * s ^ 25
    - 47 * s ^ 24
    + 79 * s ^ 23
    - 64 * s ^ 22
    - 71 * s ^ 21
    + 355 * s ^ 20
    - 730 * s ^ 19
    + 1071 * s ^ 18
    - 1224 * s ^ 17
    + 1142 * s ^ 16
    - 874 * s ^ 15
    + 547 * s ^ 14
    - 278 * s ^ 13
    + 110 * s ^ 12
    - 35 * s ^ 11
    + 8 * s ^ 10
    - s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient3 (s : ℚ) : ℚ :=
  s ^ 28
    - 9 * s ^ 27
    + 30 * s ^ 26
    + 23 * s ^ 25
    - 525 * s ^ 24
    + 2171 * s ^ 23
    - 5394 * s ^ 22
    + 10005 * s ^ 21
    - 14592 * s ^ 20
    + 17131 * s ^ 19
    - 16044 * s ^ 18
    + 11149 * s ^ 17
    - 4334 * s ^ 16
    - 1963 * s ^ 15
    + 5712 * s ^ 14
    - 6463 * s ^ 13
    + 5188 * s ^ 12
    - 3219 * s ^ 11
    + 1632 * s ^ 10
    - 673 * s ^ 9
    + 220 * s ^ 8
    - 55 * s ^ 7
    + 10 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient4 (s : ℚ) : ℚ :=
  -2 * s ^ 29
    + 33 * s ^ 28
    - 281 * s ^ 27
    + 1510 * s ^ 26
    - 5552 * s ^ 25
    + 14419 * s ^ 24
    - 27020 * s ^ 23
    + 35994 * s ^ 22
    - 29482 * s ^ 21
    - 5610 * s ^ 20
    + 73349 * s ^ 19
    - 163606 * s ^ 18
    + 252327 * s ^ 17
    - 309996 * s ^ 16
    + 319325 * s ^ 15
    - 279970 * s ^ 14
    + 210304 * s ^ 13
    - 135398 * s ^ 12
    + 74244 * s ^ 11
    - 34750 * s ^ 10
    + 13532 * s ^ 9
    - 4216 * s ^ 8
    + 993 * s ^ 7
    - 156 * s ^ 6
    + 7 * s ^ 5
    + 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient5 (s : ℚ) : ℚ :=
  s ^ 31
    - 17 * s ^ 30
    + 143 * s ^ 29
    - 757 * s ^ 28
    + 2653 * s ^ 27
    - 5508 * s ^ 26
    + 1147 * s ^ 25
    + 38899 * s ^ 24
    - 169400 * s ^ 23
    + 456386 * s ^ 22
    - 946107 * s ^ 21
    + 1635919 * s ^ 20
    - 2436188 * s ^ 19
    + 3182320 * s ^ 18
    - 3674053 * s ^ 17
    + 3758579 * s ^ 16
    - 3411234 * s ^ 15
    + 2732273 * s ^ 14
    - 1922763 * s ^ 13
    + 1180660 * s ^ 12
    - 626854 * s ^ 11
    + 285407 * s ^ 10
    - 107011 * s ^ 9
    + 31156 * s ^ 8
    - 6291 * s ^ 7
    + 529 * s ^ 6
    + 158 * s ^ 5
    - 46 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient6 (s : ℚ) : ℚ :=
  4 * s ^ 31
    - 87 * s ^ 30
    + 920 * s ^ 29
    - 6351 * s ^ 28
    + 32050 * s ^ 27
    - 125036 * s ^ 26
    + 389362 * s ^ 25
    - 992227 * s ^ 24
    + 2124899 * s ^ 23
    - 3941562 * s ^ 22
    + 6503788 * s ^ 21
    - 9690903 * s ^ 20
    + 13077848 * s ^ 19
    - 15988232 * s ^ 18
    + 17644569 * s ^ 17
    - 17513403 * s ^ 16
    + 15560964 * s ^ 15
    - 12271011 * s ^ 14
    + 8539423 * s ^ 13
    - 5197722 * s ^ 12
    + 2734262 * s ^ 11
    - 1215731 * s ^ 10
    + 424371 * s ^ 9
    - 101934 * s ^ 8
    + 8852 * s ^ 7
    + 5157 * s ^ 6
    - 2719 * s ^ 5
    + 418 * s ^ 4
    + 31 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient7 (s : ℚ) : ℚ :=
  -s ^ 33
    + 22 * s ^ 32
    - 246 * s ^ 31
    + 1824 * s ^ 30
    - 9960 * s ^ 29
    + 42364 * s ^ 28
    - 145195 * s ^ 27
    + 410844 * s ^ 26
    - 984154 * s ^ 25
    + 2066660 * s ^ 24
    - 3973581 * s ^ 23
    + 7222746 * s ^ 22
    - 12399408 * s ^ 21
    + 19643492 * s ^ 20
    - 28165425 * s ^ 19
    + 36285316 * s ^ 18
    - 41795112 * s ^ 17
    + 42937362 * s ^ 16
    - 39136335 * s ^ 15
    + 31421086 * s ^ 14
    - 22149390 * s ^ 13
    + 13542928 * s ^ 12
    - 7017865 * s ^ 11
    + 2894904 * s ^ 10
    - 770037 * s ^ 9
    + 16316 * s ^ 8
    + 106745 * s ^ 7
    - 62818 * s ^ 6
    + 19032 * s ^ 5
    - 1700 * s ^ 4
    - 412 * s ^ 3
    - 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient8 (s : ℚ) : ℚ :=
  4 * s ^ 32
    - 77 * s ^ 31
    + 754 * s ^ 30
    - 4870 * s ^ 29
    + 22818 * s ^ 28
    - 80248 * s ^ 27
    + 208180 * s ^ 26
    - 352261 * s ^ 25
    + 128398 * s ^ 24
    + 1463478 * s ^ 23
    - 5919516 * s ^ 22
    + 14410542 * s ^ 21
    - 26894298 * s ^ 20
    + 41936067 * s ^ 19
    - 56846694 * s ^ 18
    + 67863608 * s ^ 17
    - 71584640 * s ^ 16
    + 66385707 * s ^ 15
    - 53909666 * s ^ 14
    + 38165831 * s ^ 13
    - 22803374 * s ^ 12
    + 10641601 * s ^ 11
    - 2851618 * s ^ 10
    - 716833 * s ^ 9
    + 1297650 * s ^ 8
    - 815878 * s ^ 7
    + 327096 * s ^ 6
    - 74825 * s ^ 5
    - 166 * s ^ 4
    + 3182 * s ^ 3
    + 48 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient9 (s : ℚ) : ℚ :=
  2 * s ^ 32
    - 54 * s ^ 31
    + 673 * s ^ 30
    - 5420 * s ^ 29
    + 32096 * s ^ 28
    - 149181 * s ^ 27
    + 562524 * s ^ 26
    - 1743801 * s ^ 25
    + 4460058 * s ^ 24
    - 9452638 * s ^ 23
    + 16870239 * s ^ 22
    - 26303512 * s ^ 21
    + 37751690 * s ^ 20
    - 51674376 * s ^ 19
    + 66875598 * s ^ 18
    - 79201650 * s ^ 17
    + 83774655 * s ^ 16
    - 77843500 * s ^ 15
    + 63077650 * s ^ 14
    - 43016870 * s ^ 13
    + 21343637 * s ^ 12
    - 3345814 * s ^ 11
    - 7169797 * s ^ 10
    + 9375026 * s ^ 9
    - 6476429 * s ^ 8
    + 3115746 * s ^ 7
    - 1034508 * s ^ 6
    + 154100 * s ^ 5
    + 40547 * s ^ 4
    - 16167 * s ^ 3
    - 523 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient10 (s : ℚ) : ℚ :=
  -5 * s ^ 31
    + 103 * s ^ 30
    - 1035 * s ^ 29
    + 7056 * s ^ 28
    - 37493 * s ^ 27
    + 165622 * s ^ 26
    - 613039 * s ^ 25
    + 1847780 * s ^ 24
    - 4336566 * s ^ 23
    + 7427009 * s ^ 22
    - 7936608 * s ^ 21
    + 1081588 * s ^ 20
    + 14959805 * s ^ 19
    - 35638830 * s ^ 18
    + 53054273 * s ^ 17
    - 61485471 * s ^ 16
    + 58787550 * s ^ 15
    - 45099284 * s ^ 14
    + 20236042 * s ^ 13
    + 10437321 * s ^ 12
    - 34013641 * s ^ 11
    + 41331225 * s ^ 10
    - 32724333 * s ^ 9
    + 18315665 * s ^ 8
    - 7586139 * s ^ 7
    + 1967314 * s ^ 6
    + 44833 * s ^ 5
    - 251243 * s ^ 4
    + 56993 * s ^ 3
    + 3489 * s ^ 2
    + 19 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient11 (s : ℚ) : ℚ :=
  -s ^ 31
    + 26 * s ^ 30
    - 284 * s ^ 29
    + 1907 * s ^ 28
    - 10079 * s ^ 27
    + 51330 * s ^ 26
    - 260804 * s ^ 25
    + 1173863 * s ^ 24
    - 4248983 * s ^ 23
    + 11928592 * s ^ 22
    - 25785863 * s ^ 21
    + 43088202 * s ^ 20
    - 56462887 * s ^ 19
    + 60119500 * s ^ 18
    - 55520495 * s ^ 17
    + 46920938 * s ^ 16
    - 32248257 * s ^ 15
    + 2747480 * s ^ 14
    + 45451023 * s ^ 13
    - 94983995 * s ^ 12
    + 118660826 * s ^ 11
    - 106135226 * s ^ 10
    + 69564352 * s ^ 9
    - 33507579 * s ^ 8
    + 11382825 * s ^ 7
    - 1169350 * s ^ 6
    - 1506100 * s ^ 5
    + 904700 * s ^ 4
    - 139452 * s ^ 3
    - 16036 * s ^ 2
    - 173 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient12 (s : ℚ) : ℚ :=
  25 * s ^ 29
    - 619 * s ^ 28
    + 6975 * s ^ 27
    - 47600 * s ^ 26
    + 216529 * s ^ 25
    - 664385 * s ^ 24
    + 1247687 * s ^ 23
    - 594122 * s ^ 22
    - 4442076 * s ^ 21
    + 16360860 * s ^ 20
    - 31592320 * s ^ 19
    + 39593150 * s ^ 18
    - 33823474 * s ^ 17
    + 25429442 * s ^ 16
    - 40264529 * s ^ 15
    + 95788112 * s ^ 14
    - 175834353 * s ^ 13
    + 232052339 * s ^ 12
    - 227990769 * s ^ 11
    + 169677054 * s ^ 10
    - 93339094 * s ^ 9
    + 35837193 * s ^ 8
    - 5738248 * s ^ 7
    - 5691186 * s ^ 6
    + 5767204 * s ^ 5
    - 2225474 * s ^ 4
    + 217024 * s ^ 3
    + 53652 * s ^ 2
    + 1003 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient13 (s : ℚ) : ℚ :=
  7 * s ^ 29
    - 223 * s ^ 28
    + 3203 * s ^ 27
    - 27969 * s ^ 26
    + 167200 * s ^ 25
    - 722007 * s ^ 24
    + 2290844 * s ^ 23
    - 5254649 * s ^ 22
    + 8031195 * s ^ 21
    - 5370972 * s ^ 20
    - 8830724 * s ^ 19
    + 31737735 * s ^ 18
    - 43184169 * s ^ 17
    + 13120872 * s ^ 16
    + 74239565 * s ^ 15
    - 197355437 * s ^ 14
    + 298303194 * s ^ 13
    - 321076100 * s ^ 12
    + 259719421 * s ^ 11
    - 155728726 * s ^ 10
    + 61120576 * s ^ 9
    - 4821196 * s ^ 8
    - 18915563 * s ^ 7
    + 22214380 * s ^ 6
    - 13245612 * s ^ 5
    + 3839175 * s ^ 4
    - 116134 * s ^ 3
    - 133778 * s ^ 2
    - 4107 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient14 (s : ℚ) : ℚ :=
  s ^ 29
    - 43 * s ^ 28
    + 796 * s ^ 27
    - 8773 * s ^ 26
    + 65945 * s ^ 25
    - 362469 * s ^ 24
    + 1510114 * s ^ 23
    - 4842481 * s ^ 22
    + 11937973 * s ^ 21
    - 22077410 * s ^ 20
    + 28055070 * s ^ 19
    - 14909799 * s ^ 18
    - 32923005 * s ^ 17
    + 117863250 * s ^ 16
    - 218787280 * s ^ 15
    + 293834451 * s ^ 14
    - 302315067 * s ^ 13
    + 237123748 * s ^ 12
    - 132750603 * s ^ 11
    + 34290694 * s ^ 10
    + 29561334 * s ^ 9
    - 56442818 * s ^ 8
    + 59513550 * s ^ 7
    - 44604848 * s ^ 6
    + 20804923 * s ^ 5
    - 4406347 * s ^ 4
    - 392427 * s ^ 3
    + 249072 * s ^ 2
    + 12436 * s
    + 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient15 (s : ℚ) : ℚ :=
  -2 * s ^ 28
    + 68 * s ^ 27
    - 1082 * s ^ 26
    + 10846 * s ^ 25
    - 77278 * s ^ 24
    + 415883 * s ^ 23
    - 1747358 * s ^ 22
    + 5847004 * s ^ 21
    - 15804304 * s ^ 20
    + 34935567 * s ^ 19
    - 63943700 * s ^ 18
    + 98013609 * s ^ 17
    - 126272314 * s ^ 16
    + 134273739 * s ^ 15
    - 110308774 * s ^ 14
    + 55849284 * s ^ 13
    + 10233082 * s ^ 12
    - 65611016 * s ^ 11
    + 100372354 * s ^ 10
    - 114667655 * s ^ 9
    + 112852570 * s ^ 8
    - 95033622 * s ^ 7
    + 59569196 * s ^ 6
    - 22341842 * s ^ 5
    + 2513300 * s ^ 4
    + 1289705 * s ^ 3
    - 338764 * s ^ 2
    - 28418 * s
    - 78

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient16 (s : ℚ) : ℚ :=
  s ^ 27
    - 30 * s ^ 26
    + 440 * s ^ 25
    - 4228 * s ^ 24
    + 29629 * s ^ 23
    - 158334 * s ^ 22
    + 659131 * s ^ 21
    - 2169722 * s ^ 20
    + 5738511 * s ^ 19
    - 12466982 * s ^ 18
    + 22993463 * s ^ 17
    - 37536148 * s ^ 16
    + 56047672 * s ^ 15
    - 76812664 * s ^ 14
    + 95289055 * s ^ 13
    - 108116472 * s ^ 12
    + 118041498 * s ^ 11
    - 128812160 * s ^ 10
    + 136563248 * s ^ 9
    - 130891552 * s ^ 8
    + 101510245 * s ^ 7
    - 54102678 * s ^ 6
    + 14497312 * s ^ 5
    + 1408582 * s ^ 4
    - 2071324 * s ^ 3
    + 313944 * s ^ 2
    + 49279 * s
    + 284

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient17 (s : ℚ) : ℚ :=
  -11 * s ^ 24
    + 268 * s ^ 23
    - 2914 * s ^ 22
    + 18556 * s ^ 21
    - 75353 * s ^ 20
    + 191522 * s ^ 19
    - 223729 * s ^ 18
    - 391984 * s ^ 17
    + 2635095 * s ^ 16
    - 7283388 * s ^ 15
    + 14546688 * s ^ 14
    - 25421656 * s ^ 13
    + 42985531 * s ^ 12
    - 68972337 * s ^ 11
    + 97487441 * s ^ 10
    - 114925493 * s ^ 9
    + 107704633 * s ^ 8
    - 73412930 * s ^ 7
    + 29835121 * s ^ 6
    - 1922668 * s ^ 5
    - 4640757 * s ^ 4
    + 2085621 * s ^ 3
    - 152131 * s ^ 2
    - 64431 * s
    - 694

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient18 (s : ℚ) : ℚ :=
  -s ^ 24
    + 30 * s ^ 23
    - 404 * s ^ 22
    + 3256 * s ^ 21
    - 17645 * s ^ 20
    + 68501 * s ^ 19
    - 199579 * s ^ 18
    + 465739 * s ^ 17
    - 999255 * s ^ 16
    + 2369399 * s ^ 15
    - 6219994 * s ^ 14
    + 15249561 * s ^ 13
    - 31198287 * s ^ 12
    + 51584525 * s ^ 11
    - 68646525 * s ^ 10
    + 72560255 * s ^ 9
    - 57703121 * s ^ 8
    + 29536758 * s ^ 7
    - 4178667 * s ^ 6
    - 6213348 * s ^ 5
    + 4794689 * s ^ 4
    - 1274541 * s ^ 3
    - 44767 * s ^ 2
    + 62233 * s
    + 1188

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient19 (s : ℚ) : ℚ :=
  2 * s ^ 22
    - 60 * s ^ 21
    + 839 * s ^ 20
    - 7320 * s ^ 19
    + 44978 * s ^ 18
    - 207938 * s ^ 17
    + 752795 * s ^ 16
    - 2189051 * s ^ 15
    + 5201162 * s ^ 14
    - 10223326 * s ^ 13
    + 16761717 * s ^ 12
    - 22922753 * s ^ 11
    + 25626302 * s ^ 10
    - 21920574 * s ^ 9
    + 11701239 * s ^ 8
    + 120778 * s ^ 7
    - 6651280 * s ^ 6
    + 6031181 * s ^ 5
    - 2537623 * s ^ 4
    + 322314 * s ^ 3
    + 140606 * s ^ 2
    - 42547 * s
    - 1441

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient20 (s : ℚ) : ℚ :=
  -s ^ 20
    + 27 * s ^ 19
    - 338 * s ^ 18
    + 2628 * s ^ 17
    - 14345 * s ^ 16
    + 58712 * s ^ 15
    - 186334 * s ^ 14
    + 461434 * s ^ 13
    - 867861 * s ^ 12
    + 1125045 * s ^ 11
    - 622854 * s ^ 10
    - 1117665 * s ^ 9
    + 3545731 * s ^ 8
    - 4987136 * s ^ 7
    + 4264254 * s ^ 6
    - 2178933 * s ^ 5
    + 477177 * s ^ 4
    + 131018 * s ^ 3
    - 110586 * s ^ 2
    + 18806 * s
    + 1221

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient21 (s : ℚ) : ℚ :=
  2 * s ^ 17
    - 54 * s ^ 16
    + 672 * s ^ 15
    - 5127 * s ^ 14
    + 26885 * s ^ 13
    - 102730 * s ^ 12
    + 294847 * s ^ 11
    - 642876 * s ^ 10
    + 1059648 * s ^ 9
    - 1290334 * s ^ 8
    + 1100294 * s ^ 7
    - 568514 * s ^ 6
    + 62820 * s ^ 5
    + 150138 * s ^ 4
    - 122775 * s ^ 3
    + 41971 * s ^ 2
    - 4177 * s
    - 690

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient22 (s : ℚ) : ℚ :=
  -s ^ 14
    + 25 * s ^ 13
    - 282 * s ^ 12
    + 1897 * s ^ 11
    - 8478 * s ^ 10
    + 26552 * s ^ 9
    - 59918 * s ^ 8
    + 98697 * s ^ 7
    - 119010 * s ^ 6
    + 104397 * s ^ 5
    - 65132 * s ^ 4
    + 26940 * s ^ 3
    - 5813 * s ^ 2
    - 108 * s
    + 234

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep2Coefficient23 (s : ℚ) : ℚ :=
  s ^ 7
    - 14 * s ^ 6
    + 80 * s ^ 5
    - 240 * s ^ 4
    + 405 * s ^ 3
    - 382 * s ^ 2
    + 186 * s
    - 36

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def denominatorStep2 (r s : ℚ) : ℚ :=
  denominatorStep2Coefficient0 s +
    denominatorStep2Coefficient1 s * r +
    denominatorStep2Coefficient2 s * r ^ 2 +
    denominatorStep2Coefficient3 s * r ^ 3 +
    denominatorStep2Coefficient4 s * r ^ 4 +
    denominatorStep2Coefficient5 s * r ^ 5 +
    denominatorStep2Coefficient6 s * r ^ 6 +
    denominatorStep2Coefficient7 s * r ^ 7 +
    denominatorStep2Coefficient8 s * r ^ 8 +
    denominatorStep2Coefficient9 s * r ^ 9 +
    denominatorStep2Coefficient10 s * r ^ 10 +
    denominatorStep2Coefficient11 s * r ^ 11 +
    denominatorStep2Coefficient12 s * r ^ 12 +
    denominatorStep2Coefficient13 s * r ^ 13 +
    denominatorStep2Coefficient14 s * r ^ 14 +
    denominatorStep2Coefficient15 s * r ^ 15 +
    denominatorStep2Coefficient16 s * r ^ 16 +
    denominatorStep2Coefficient17 s * r ^ 17 +
    denominatorStep2Coefficient18 s * r ^ 18 +
    denominatorStep2Coefficient19 s * r ^ 19 +
    denominatorStep2Coefficient20 s * r ^ 20 +
    denominatorStep2Coefficient21 s * r ^ 21 +
    denominatorStep2Coefficient22 s * r ^ 22 +
    denominatorStep2Coefficient23 s * r ^ 23

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_0 (s : ℚ) :
    denominatorStep2Coefficient0 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient0,
    denominatorStep1Coefficient0,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_1 (s : ℚ) :
    denominatorStep2Coefficient1 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient1,
    denominatorStep1Coefficient0,
    denominatorStep1Coefficient1,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_2 (s : ℚ) :
    denominatorStep2Coefficient2 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient2,
    denominatorStep1Coefficient0,
    denominatorStep1Coefficient1,
    denominatorStep1Coefficient2,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_3 (s : ℚ) :
    denominatorStep2Coefficient3 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient3,
    denominatorStep1Coefficient0,
    denominatorStep1Coefficient1,
    denominatorStep1Coefficient2,
    denominatorStep1Coefficient3,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_4 (s : ℚ) :
    denominatorStep2Coefficient4 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient4,
    denominatorStep1Coefficient0,
    denominatorStep1Coefficient1,
    denominatorStep1Coefficient2,
    denominatorStep1Coefficient3,
    denominatorStep1Coefficient4,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_5 (s : ℚ) :
    denominatorStep2Coefficient5 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient5,
    denominatorStep1Coefficient0,
    denominatorStep1Coefficient1,
    denominatorStep1Coefficient2,
    denominatorStep1Coefficient3,
    denominatorStep1Coefficient4,
    denominatorStep1Coefficient5,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_6 (s : ℚ) :
    denominatorStep2Coefficient6 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient6,
    denominatorStep1Coefficient0,
    denominatorStep1Coefficient1,
    denominatorStep1Coefficient2,
    denominatorStep1Coefficient3,
    denominatorStep1Coefficient4,
    denominatorStep1Coefficient5,
    denominatorStep1Coefficient6,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_7 (s : ℚ) :
    denominatorStep2Coefficient7 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient7,
    denominatorStep1Coefficient0,
    denominatorStep1Coefficient1,
    denominatorStep1Coefficient2,
    denominatorStep1Coefficient3,
    denominatorStep1Coefficient4,
    denominatorStep1Coefficient5,
    denominatorStep1Coefficient6,
    denominatorStep1Coefficient7,
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
theorem denominatorStep2Coefficient_product_certificate_8 (s : ℚ) :
    denominatorStep2Coefficient8 s =
    denominatorStep1Coefficient0 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient8,
    denominatorStep1Coefficient0,
    denominatorStep1Coefficient1,
    denominatorStep1Coefficient2,
    denominatorStep1Coefficient3,
    denominatorStep1Coefficient4,
    denominatorStep1Coefficient5,
    denominatorStep1Coefficient6,
    denominatorStep1Coefficient7,
    denominatorStep1Coefficient8,
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
theorem denominatorStep2Coefficient_product_certificate_9 (s : ℚ) :
    denominatorStep2Coefficient9 s =
    denominatorStep1Coefficient1 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient9,
    denominatorStep1Coefficient1,
    denominatorStep1Coefficient2,
    denominatorStep1Coefficient3,
    denominatorStep1Coefficient4,
    denominatorStep1Coefficient5,
    denominatorStep1Coefficient6,
    denominatorStep1Coefficient7,
    denominatorStep1Coefficient8,
    denominatorStep1Coefficient9,
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
theorem denominatorStep2Coefficient_product_certificate_10 (s : ℚ) :
    denominatorStep2Coefficient10 s =
    denominatorStep1Coefficient2 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient10,
    denominatorStep1Coefficient2,
    denominatorStep1Coefficient3,
    denominatorStep1Coefficient4,
    denominatorStep1Coefficient5,
    denominatorStep1Coefficient6,
    denominatorStep1Coefficient7,
    denominatorStep1Coefficient8,
    denominatorStep1Coefficient9,
    denominatorStep1Coefficient10,
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
theorem denominatorStep2Coefficient_product_certificate_11 (s : ℚ) :
    denominatorStep2Coefficient11 s =
    denominatorStep1Coefficient3 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient11,
    denominatorStep1Coefficient3,
    denominatorStep1Coefficient4,
    denominatorStep1Coefficient5,
    denominatorStep1Coefficient6,
    denominatorStep1Coefficient7,
    denominatorStep1Coefficient8,
    denominatorStep1Coefficient9,
    denominatorStep1Coefficient10,
    denominatorStep1Coefficient11,
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
theorem denominatorStep2Coefficient_product_certificate_12 (s : ℚ) :
    denominatorStep2Coefficient12 s =
    denominatorStep1Coefficient4 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient12,
    denominatorStep1Coefficient4,
    denominatorStep1Coefficient5,
    denominatorStep1Coefficient6,
    denominatorStep1Coefficient7,
    denominatorStep1Coefficient8,
    denominatorStep1Coefficient9,
    denominatorStep1Coefficient10,
    denominatorStep1Coefficient11,
    denominatorStep1Coefficient12,
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
theorem denominatorStep2Coefficient_product_certificate_13 (s : ℚ) :
    denominatorStep2Coefficient13 s =
    denominatorStep1Coefficient5 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient13,
    denominatorStep1Coefficient5,
    denominatorStep1Coefficient6,
    denominatorStep1Coefficient7,
    denominatorStep1Coefficient8,
    denominatorStep1Coefficient9,
    denominatorStep1Coefficient10,
    denominatorStep1Coefficient11,
    denominatorStep1Coefficient12,
    denominatorStep1Coefficient13,
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
theorem denominatorStep2Coefficient_product_certificate_14 (s : ℚ) :
    denominatorStep2Coefficient14 s =
    denominatorStep1Coefficient6 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient14,
    denominatorStep1Coefficient6,
    denominatorStep1Coefficient7,
    denominatorStep1Coefficient8,
    denominatorStep1Coefficient9,
    denominatorStep1Coefficient10,
    denominatorStep1Coefficient11,
    denominatorStep1Coefficient12,
    denominatorStep1Coefficient13,
    denominatorStep1Coefficient14,
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
theorem denominatorStep2Coefficient_product_certificate_15 (s : ℚ) :
    denominatorStep2Coefficient15 s =
    denominatorStep1Coefficient7 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient1 s
      + denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [denominatorStep2Coefficient15,
    denominatorStep1Coefficient7,
    denominatorStep1Coefficient8,
    denominatorStep1Coefficient9,
    denominatorStep1Coefficient10,
    denominatorStep1Coefficient11,
    denominatorStep1Coefficient12,
    denominatorStep1Coefficient13,
    denominatorStep1Coefficient14,
    denominatorStep1Coefficient15,
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
theorem denominatorStep2Coefficient_product_certificate_16 (s : ℚ) :
    denominatorStep2Coefficient16 s =
    denominatorStep1Coefficient8 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient2 s
      + denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient1 s
    := by
  simp only [denominatorStep2Coefficient16,
    denominatorStep1Coefficient8,
    denominatorStep1Coefficient9,
    denominatorStep1Coefficient10,
    denominatorStep1Coefficient11,
    denominatorStep1Coefficient12,
    denominatorStep1Coefficient13,
    denominatorStep1Coefficient14,
    denominatorStep1Coefficient15,
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
theorem denominatorStep2Coefficient_product_certificate_17 (s : ℚ) :
    denominatorStep2Coefficient17 s =
    denominatorStep1Coefficient9 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient3 s
      + denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient2 s
    := by
  simp only [denominatorStep2Coefficient17,
    denominatorStep1Coefficient9,
    denominatorStep1Coefficient10,
    denominatorStep1Coefficient11,
    denominatorStep1Coefficient12,
    denominatorStep1Coefficient13,
    denominatorStep1Coefficient14,
    denominatorStep1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_18 (s : ℚ) :
    denominatorStep2Coefficient18 s =
    denominatorStep1Coefficient10 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient4 s
      + denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient3 s
    := by
  simp only [denominatorStep2Coefficient18,
    denominatorStep1Coefficient10,
    denominatorStep1Coefficient11,
    denominatorStep1Coefficient12,
    denominatorStep1Coefficient13,
    denominatorStep1Coefficient14,
    denominatorStep1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_19 (s : ℚ) :
    denominatorStep2Coefficient19 s =
    denominatorStep1Coefficient11 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient5 s
      + denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient4 s
    := by
  simp only [denominatorStep2Coefficient19,
    denominatorStep1Coefficient11,
    denominatorStep1Coefficient12,
    denominatorStep1Coefficient13,
    denominatorStep1Coefficient14,
    denominatorStep1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_20 (s : ℚ) :
    denominatorStep2Coefficient20 s =
    denominatorStep1Coefficient12 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient6 s
      + denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient5 s
    := by
  simp only [denominatorStep2Coefficient20,
    denominatorStep1Coefficient12,
    denominatorStep1Coefficient13,
    denominatorStep1Coefficient14,
    denominatorStep1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_21 (s : ℚ) :
    denominatorStep2Coefficient21 s =
    denominatorStep1Coefficient13 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient7 s
      + denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient6 s
    := by
  simp only [denominatorStep2Coefficient21,
    denominatorStep1Coefficient13,
    denominatorStep1Coefficient14,
    denominatorStep1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_22 (s : ℚ) :
    denominatorStep2Coefficient22 s =
    denominatorStep1Coefficient14 s *
        rawUnitFourDenominatorCoefficient8 s
      + denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient7 s
    := by
  simp only [denominatorStep2Coefficient22,
    denominatorStep1Coefficient14,
    denominatorStep1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep2Coefficient_product_certificate_23 (s : ℚ) :
    denominatorStep2Coefficient23 s =
    denominatorStep1Coefficient15 s *
        rawUnitFourDenominatorCoefficient8 s
    := by
  simp only [denominatorStep2Coefficient23,
    denominatorStep1Coefficient15,
    rawUnitFourDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem denominatorStep2_eq_denominatorStep1_mul_rawUnitFourDenominator (r s : ℚ) :
    denominatorStep2 r s = denominatorStep1 r s * rawUnitFourDenominator r s := by
  have h0 := denominatorStep2Coefficient_product_certificate_0 s
  have h1 := denominatorStep2Coefficient_product_certificate_1 s
  have h2 := denominatorStep2Coefficient_product_certificate_2 s
  have h3 := denominatorStep2Coefficient_product_certificate_3 s
  have h4 := denominatorStep2Coefficient_product_certificate_4 s
  have h5 := denominatorStep2Coefficient_product_certificate_5 s
  have h6 := denominatorStep2Coefficient_product_certificate_6 s
  have h7 := denominatorStep2Coefficient_product_certificate_7 s
  have h8 := denominatorStep2Coefficient_product_certificate_8 s
  have h9 := denominatorStep2Coefficient_product_certificate_9 s
  have h10 := denominatorStep2Coefficient_product_certificate_10 s
  have h11 := denominatorStep2Coefficient_product_certificate_11 s
  have h12 := denominatorStep2Coefficient_product_certificate_12 s
  have h13 := denominatorStep2Coefficient_product_certificate_13 s
  have h14 := denominatorStep2Coefficient_product_certificate_14 s
  have h15 := denominatorStep2Coefficient_product_certificate_15 s
  have h16 := denominatorStep2Coefficient_product_certificate_16 s
  have h17 := denominatorStep2Coefficient_product_certificate_17 s
  have h18 := denominatorStep2Coefficient_product_certificate_18 s
  have h19 := denominatorStep2Coefficient_product_certificate_19 s
  have h20 := denominatorStep2Coefficient_product_certificate_20 s
  have h21 := denominatorStep2Coefficient_product_certificate_21 s
  have h22 := denominatorStep2Coefficient_product_certificate_22 s
  have h23 := denominatorStep2Coefficient_product_certificate_23 s
  simp only [denominatorStep2, denominatorStep1, rawUnitFourDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 27
    + 4 * s ^ 26
    - 10 * s ^ 25
    + 18 * s ^ 24
    - 25 * s ^ 23
    + 28 * s ^ 22
    - 25 * s ^ 21
    + 18 * s ^ 20
    - 10 * s ^ 19
    + 4 * s ^ 18
    - s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient2 (s : ℚ) : ℚ :=
  2 * s ^ 29
    - 14 * s ^ 28
    + 46 * s ^ 27
    - 69 * s ^ 26
    + 27 * s ^ 25
    + 162 * s ^ 24
    - 522 * s ^ 23
    + 972 * s ^ 22
    - 1357 * s ^ 21
    + 1501 * s ^ 20
    - 1363 * s ^ 19
    + 1017 * s ^ 18
    - 620 * s ^ 17
    + 306 * s ^ 16
    - 117 * s ^ 15
    + 36 * s ^ 14
    - 8 * s ^ 13
    + s ^ 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient3 (s : ℚ) : ℚ :=
  -s ^ 31
    + 9 * s ^ 30
    - 28 * s ^ 29
    - 50 * s ^ 28
    + 671 * s ^ 27
    - 2615 * s ^ 26
    + 6195 * s ^ 25
    - 10825 * s ^ 24
    + 14445 * s ^ 23
    - 14604 * s ^ 22
    + 9988 * s ^ 21
    - 1441 * s ^ 20
    - 7723 * s ^ 19
    + 14199 * s ^ 18
    - 16036 * s ^ 17
    + 13742 * s ^ 16
    - 9469 * s ^ 15
    + 5293 * s ^ 14
    - 2458 * s ^ 13
    + 937 * s ^ 12
    - 285 * s ^ 11
    + 66 * s ^ 10
    - 11 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient4 (s : ℚ) : ℚ :=
  2 * s ^ 32
    - 34 * s ^ 31
    + 298 * s ^ 30
    - 1621 * s ^ 29
    + 5872 * s ^ 28
    - 14303 * s ^ 27
    + 22602 * s ^ 26
    - 17152 * s ^ 25
    - 19648 * s ^ 24
    + 101311 * s ^ 23
    - 221503 * s ^ 22
    + 350910 * s ^ 21
    - 446231 * s ^ 20
    + 469803 * s ^ 19
    - 415065 * s ^ 18
    + 304508 * s ^ 17
    - 180207 * s ^ 16
    + 79352 * s ^ 15
    - 18174 * s ^ 14
    - 6871 * s ^ 13
    + 11341 * s ^ 12
    - 8046 * s ^ 11
    + 4013 * s ^ 10
    - 1515 * s ^ 9
    + 439 * s ^ 8
    - 93 * s ^ 7
    + 13 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 34
    + 17 * s ^ 33
    - 142 * s ^ 32
    + 726 * s ^ 31
    - 2252 * s ^ 30
    + 2423 * s ^ 29
    + 14673 * s ^ 28
    - 96306 * s ^ 27
    + 322104 * s ^ 26
    - 761955 * s ^ 25
    + 1409882 * s ^ 24
    - 2148178 * s ^ 23
    + 2737390 * s ^ 22
    - 2915269 * s ^ 21
    + 2516971 * s ^ 20
    - 1589670 * s ^ 19
    + 412580 * s ^ 18
    + 657794 * s ^ 17
    - 1322285 * s ^ 16
    + 1489023 * s ^ 15
    - 1271808 * s ^ 14
    + 882509 * s ^ 13
    - 514566 * s ^ 12
    + 252889 * s ^ 11
    - 103557 * s ^ 10
    + 34536 * s ^ 9
    - 9051 * s ^ 8
    + 1706 * s ^ 7
    - 188 * s ^ 6
    + 3 * s ^ 5
    + 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient6 (s : ℚ) : ℚ :=
  -5 * s ^ 34
    + 112 * s ^ 33
    - 1211 * s ^ 32
    + 8482 * s ^ 31
    - 42911 * s ^ 30
    + 164643 * s ^ 29
    - 489231 * s ^ 28
    + 1135063 * s ^ 27
    - 2057117 * s ^ 26
    + 2874661 * s ^ 25
    - 2875455 * s ^ 24
    + 1203910 * s ^ 23
    + 2854092 * s ^ 22
    - 9349049 * s ^ 21
    + 17401996 * s ^ 20
    - 25196881 * s ^ 19
    + 30593258 * s ^ 18
    - 32096024 * s ^ 17
    + 29368865 * s ^ 16
    - 23532032 * s ^ 15
    + 16508534 * s ^ 14
    - 10119684 * s ^ 13
    + 5413890 * s ^ 12
    - 2488931 * s ^ 11
    + 959140 * s ^ 10
    - 298236 * s ^ 9
    + 69825 * s ^ 8
    - 10020 * s ^ 7
    + 81 * s ^ 6
    + 283 * s ^ 5
    - 47 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient7 (s : ℚ) : ℚ :=
  s ^ 36
    - 23 * s ^ 35
    + 264 * s ^ 34
    - 1950 * s ^ 33
    + 10135 * s ^ 32
    - 38023 * s ^ 31
    + 98384 * s ^ 30
    - 129415 * s ^ 29
    - 229358 * s ^ 28
    + 1994850 * s ^ 27
    - 7034165 * s ^ 26
    + 17734640 * s ^ 25
    - 36335583 * s ^ 24
    + 64287794 * s ^ 23
    - 101258504 * s ^ 22
    + 143664254 * s ^ 21
    - 184495220 * s ^ 20
    + 214431610 * s ^ 19
    - 225267098 * s ^ 18
    + 213320470 * s ^ 17
    - 181069416 * s ^ 16
    + 137171235 * s ^ 15
    - 92273194 * s ^ 14
    + 54813190 * s ^ 13
    - 28488236 * s ^ 12
    + 12608049 * s ^ 11
    - 4562041 * s ^ 10
    + 1252230 * s ^ 9
    - 209478 * s ^ 8
    - 7611 * s ^ 7
    + 16030 * s ^ 6
    - 4269 * s ^ 5
    + 415 * s ^ 4
    + 33 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient8 (s : ℚ) : ℚ :=
  s ^ 36
    - 36 * s ^ 35
    + 565 * s ^ 34
    - 5512 * s ^ 33
    + 38284 * s ^ 32
    - 203100 * s ^ 31
    + 857613 * s ^ 30
    - 2957339 * s ^ 29
    + 8483934 * s ^ 28
    - 20629592 * s ^ 27
    + 43571481 * s ^ 26
    - 82411024 * s ^ 25
    + 143519595 * s ^ 24
    - 233039362 * s ^ 23
    + 351461541 * s ^ 22
    - 487764712 * s ^ 21
    + 618742620 * s ^ 20
    - 713618679 * s ^ 19
    + 745478970 * s ^ 18
    - 701896585 * s ^ 17
    + 592219619 * s ^ 16
    - 446230372 * s ^ 15
    + 298601614 * s ^ 14
    - 175832531 * s ^ 13
    + 89131337 * s ^ 12
    - 36932928 * s ^ 11
    + 11382906 * s ^ 10
    - 1857446 * s ^ 9
    - 415028 * s ^ 8
    + 434420 * s ^ 7
    - 157152 * s ^ 6
    + 28603 * s ^ 5
    - 1234 * s ^ 4
    - 469 * s ^ 3
    - 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient9 (s : ℚ) : ℚ :=
  s ^ 37
    - 27 * s ^ 36
    + 359 * s ^ 35
    - 3101 * s ^ 34
    + 19483 * s ^ 33
    - 94559 * s ^ 32
    + 367974 * s ^ 31
    - 1179969 * s ^ 30
    + 3209909 * s ^ 29
    - 7748181 * s ^ 28
    + 17723273 * s ^ 27
    - 40549420 * s ^ 26
    + 91992367 * s ^ 25
    - 195551279 * s ^ 24
    + 371768488 * s ^ 23
    - 622667176 * s ^ 22
    + 923268023 * s ^ 21
    - 1222564974 * s ^ 20
    + 1451996897 * s ^ 19
    - 1547765896 * s ^ 18
    + 1476229862 * s ^ 17
    - 1256361837 * s ^ 16
    + 952164421 * s ^ 15
    - 636104514 * s ^ 14
    + 365862231 * s ^ 13
    - 170771753 * s ^ 12
    + 55329012 * s ^ 11
    - 4851075 * s ^ 10
    - 8061757 * s ^ 9
    + 6583221 * s ^ 8
    - 2921783 * s ^ 7
    + 783723 * s ^ 6
    - 98645 * s ^ 5
    - 7235 * s ^ 4
    + 3885 * s ^ 3
    + 52 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient10 (s : ℚ) : ℚ :=
  -4 * s ^ 36
    + 95 * s ^ 35
    - 1104 * s ^ 34
    + 8242 * s ^ 33
    - 43591 * s ^ 32
    + 167347 * s ^ 31
    - 437763 * s ^ 30
    + 481505 * s ^ 29
    + 2124036 * s ^ 28
    - 15410515 * s ^ 27
    + 57010243 * s ^ 26
    - 153082515 * s ^ 25
    + 328165954 * s ^ 24
    - 593398741 * s ^ 23
    + 944285143 * s ^ 22
    - 1359160971 * s ^ 21
    + 1783875065 * s ^ 20
    - 2124305968 * s ^ 19
    + 2277717525 * s ^ 18
    - 2184611393 * s ^ 17
    + 1869020876 * s ^ 16
    - 1412655991 * s ^ 15
    + 910743268 * s ^ 14
    - 460294307 * s ^ 13
    + 134210431 * s ^ 12
    + 36622583 * s ^ 11
    - 80037584 * s ^ 10
    + 61473419 * s ^ 9
    - 31389967 * s ^ 8
    + 11070864 * s ^ 7
    - 2293306 * s ^ 6
    + 72111 * s ^ 5
    + 96820 * s ^ 4
    - 21188 * s ^ 3
    - 618 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient11 (s : ℚ) : ℚ :=
  -2 * s ^ 36
    + 64 * s ^ 35
    - 955 * s ^ 34
    + 9120 * s ^ 33
    - 63517 * s ^ 32
    + 345677 * s ^ 31
    - 1526449 * s ^ 30
    + 5569291 * s ^ 29
    - 16892767 * s ^ 28
    + 42681111 * s ^ 27
    - 90489055 * s ^ 26
    + 165172646 * s ^ 25
    - 274561668 * s ^ 24
    + 446607113 * s ^ 23
    - 730657287 * s ^ 22
    + 1150770138 * s ^ 21
    - 1645923054 * s ^ 20
    + 2077085302 * s ^ 19
    - 2303925303 * s ^ 18
    + 2252949938 * s ^ 17
    - 1928765677 * s ^ 16
    + 1371647464 * s ^ 15
    - 681615121 * s ^ 14
    + 44108668 * s ^ 13
    + 362631403 * s ^ 12
    - 470380484 * s ^ 11
    + 369490707 * s ^ 10
    - 212727081 * s ^ 9
    + 91093250 * s ^ 8
    - 26225940 * s ^ 7
    + 2975093 * s ^ 6
    + 1075119 * s ^ 5
    - 542360 * s ^ 4
    + 80073 * s ^ 3
    + 4522 * s ^ 2
    + 21 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient12 (s : ℚ) : ℚ :=
  5 * s ^ 35
    - 127 * s ^ 34
    + 1563 * s ^ 33
    - 12758 * s ^ 32
    + 79385 * s ^ 31
    - 404840 * s ^ 30
    + 1733251 * s ^ 29
    - 6151162 * s ^ 28
    + 17442739 * s ^ 27
    - 37082519 * s ^ 26
    + 50363383 * s ^ 25
    - 8469172 * s ^ 24
    - 163392862 * s ^ 23
    + 506843952 * s ^ 22
    - 965531053 * s ^ 21
    + 1405471872 * s ^ 20
    - 1710147405 * s ^ 19
    + 1823496022 * s ^ 18
    - 1694380935 * s ^ 17
    + 1229066161 * s ^ 16
    - 376592771 * s ^ 15
    - 665294549 * s ^ 14
    + 1482589693 * s ^ 13
    - 1753507011 * s ^ 12
    + 1475812831 * s ^ 11
    - 946986906 * s ^ 10
    + 471397915 * s ^ 9
    - 169615991 * s ^ 8
    + 31615624 * s ^ 7
    + 6452437 * s ^ 6
    - 6530577 * s ^ 5
    + 1965709 * s ^ 4
    - 208750 * s ^ 3
    - 22942 * s ^ 2
    - 212 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient13 (s : ℚ) : ℚ :=
  s ^ 35
    - 31 * s ^ 34
    + 423 * s ^ 33
    - 3597 * s ^ 32
    + 23263 * s ^ 31
    - 133940 * s ^ 30
    + 734627 * s ^ 29
    - 3667800 * s ^ 28
    + 15488860 * s ^ 27
    - 52940556 * s ^ 26
    + 143818268 * s ^ 25
    - 308432020 * s ^ 24
    + 521240141 * s ^ 23
    - 698481070 * s ^ 22
    + 765862443 * s ^ 21
    - 750840914 * s ^ 20
    + 743038053 * s ^ 19
    - 704571829 * s ^ 18
    + 360168056 * s ^ 17
    + 611674275 * s ^ 16
    - 2161977246 * s ^ 15
    + 3669381712 * s ^ 14
    - 4372674212 * s ^ 13
    + 3977900476 * s ^ 12
    - 2828948577 * s ^ 11
    + 1580882076 * s ^ 10
    - 664472783 * s ^ 9
    + 159334302 * s ^ 8
    + 27513496 * s ^ 7
    - 46988442 * s ^ 6
    + 21676790 * s ^ 5
    - 5026522 * s ^ 4
    + 335397 * s ^ 3
    + 85512 * s ^ 2
    + 1368 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient14 (s : ℚ) : ℚ :=
  -25 * s ^ 33
    + 736 * s ^ 32
    - 9988 * s ^ 31
    + 82814 * s ^ 30
    - 463478 * s ^ 29
    + 1795684 * s ^ 28
    - 4558016 * s ^ 27
    + 5162099 * s ^ 26
    + 13066296 * s ^ 25
    - 84822362 * s ^ 24
    + 237944802 * s ^ 23
    - 430252370 * s ^ 22
    + 518993664 * s ^ 21
    - 379233176 * s ^ 20
    + 142784293 * s ^ 19
    - 295773242 * s ^ 18
    + 1397411486 * s ^ 17
    - 3528031746 * s ^ 16
    + 5942272282 * s ^ 15
    - 7435958543 * s ^ 14
    + 7260256422 * s ^ 13
    - 5625966527 * s ^ 12
    + 3433219708 * s ^ 11
    - 1572996118 * s ^ 10
    + 401493664 * s ^ 9
    + 131799673 * s ^ 8
    - 227619856 * s ^ 7
    + 139837399 * s ^ 6
    - 49203598 * s ^ 5
    + 9122471 * s ^ 4
    - 107373 * s ^ 3
    - 240791 * s ^ 2
    - 6283 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient15 (s : ℚ) : ℚ :=
  -7 * s ^ 33
    + 257 * s ^ 32
    - 4330 * s ^ 31
    + 44894 * s ^ 30
    - 321992 * s ^ 29
    + 1690507 * s ^ 28
    - 6654454 * s ^ 27
    + 19576651 * s ^ 26
    - 41124060 * s ^ 25
    + 51029119 * s ^ 24
    + 10889621 * s ^ 23
    - 221624148 * s ^ 22
    + 564715128 * s ^ 21
    - 783693442 * s ^ 20
    + 376697885 * s ^ 19
    + 1129398675 * s ^ 18
    - 3730970224 * s ^ 17
    + 6668634540 * s ^ 16
    - 8689531939 * s ^ 15
    + 8849606252 * s ^ 14
    - 7178837113 * s ^ 13
    + 4551290875 * s ^ 12
    - 2040284549 * s ^ 11
    + 294685235 * s ^ 10
    + 600699289 * s ^ 9
    - 801254959 * s ^ 8
    + 579523594 * s ^ 7
    - 272456838 * s ^ 6
    + 79754645 * s ^ 5
    - 10903544 * s ^ 4
    - 1113824 * s ^ 3
    + 516631 * s ^ 2
    + 21610 * s
    + 15

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient16 (s : ℚ) : ℚ :=
  -s ^ 33
    + 48 * s ^ 32
    - 1018 * s ^ 31
    + 13063 * s ^ 30
    - 115615 * s ^ 29
    + 756214 * s ^ 28
    - 3799549 * s ^ 27
    + 14965829 * s ^ 26
    - 46512300 * s ^ 25
    + 113077781 * s ^ 24
    - 207269178 * s ^ 23
    + 251275772 * s ^ 22
    - 58992011 * s ^ 21
    - 622566233 * s ^ 20
    + 1958487298 * s ^ 19
    - 3824614610 * s ^ 18
    + 5704282106 * s ^ 17
    - 6833048404 * s ^ 16
    + 6624536030 * s ^ 15
    - 5095330664 * s ^ 14
    + 2847999631 * s ^ 13
    - 643288105 * s ^ 12
    - 982091269 * s ^ 11
    + 1859107298 * s ^ 10
    - 2032118092 * s ^ 9
    + 1619206376 * s ^ 8
    - 936959814 * s ^ 7
    + 374545825 * s ^ 6
    - 89834771 * s ^ 5
    + 5493420 * s ^ 4
    + 3688432 * s ^ 3
    - 836273 * s ^ 2
    - 57111 * s
    - 105

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient17 (s : ℚ) : ℚ :=
  2 * s ^ 32
    - 78 * s ^ 31
    + 1439 * s ^ 30
    - 16839 * s ^ 29
    + 140856 * s ^ 28
    - 896585 * s ^ 27
    + 4502435 * s ^ 26
    - 18239454 * s ^ 25
    + 60500359 * s ^ 24
    - 166186715 * s ^ 23
    + 381816430 * s ^ 22
    - 740835389 * s ^ 21
    + 1224318499 * s ^ 20
    - 1729347366 * s ^ 19
    + 2067731789 * s ^ 18
    - 2015742369 * s ^ 17
    + 1432872591 * s ^ 16
    - 391086049 * s ^ 15
    - 843123859 * s ^ 14
    + 1993159440 * s ^ 13
    - 2892080192 * s ^ 12
    + 3438310597 * s ^ 11
    - 3527483601 * s ^ 10
    + 3048364275 * s ^ 9
    - 2085240719 * s ^ 8
    + 1054245277 * s ^ 7
    - 358100438 * s ^ 6
    + 59950869 * s ^ 5
    + 8154107 * s ^ 4
    - 6788593 * s ^ 3
    + 981441 * s ^ 2
    + 117387 * s
    + 453

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient18 (s : ℚ) : ℚ :=
  -s ^ 31
    + 35 * s ^ 30
    - 599 * s ^ 29
    + 6700 * s ^ 28
    - 54771 * s ^ 27
    + 344905 * s ^ 26
    - 1719449 * s ^ 25
    + 6899966 * s ^ 24
    - 22582667 * s ^ 23
    + 61122146 * s ^ 22
    - 139308063 * s ^ 21
    + 274129437 * s ^ 20
    - 480203997 * s ^ 19
    + 769517254 * s ^ 18
    - 1142223623 * s ^ 17
    + 1570803875 * s ^ 16
    - 2016538246 * s ^ 15
    + 2482653326 * s ^ 14
    - 3007245431 * s ^ 13
    + 3548841676 * s ^ 12
    - 3902969019 * s ^ 11
    + 3776295427 * s ^ 10
    - 3014136692 * s ^ 9
    + 1853768899 * s ^ 8
    - 810434631 * s ^ 7
    + 209363501 * s ^ 6
    - 829554 * s ^ 5
    - 22976753 * s ^ 4
    + 8400972 * s ^ 3
    - 735094 * s ^ 2
    - 188189 * s
    - 1340

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient19 (s : ℚ) : ℚ :=
  11 * s ^ 28
    - 321 * s ^ 27
    + 4287 * s ^ 26
    - 34557 * s ^ 25
    + 185514 * s ^ 24
    - 680270 * s ^ 23
    + 1604011 * s ^ 22
    - 1507954 * s ^ 21
    - 5512805 * s ^ 20
    + 32155402 * s ^ 19
    - 96039617 * s ^ 18
    + 216722129 * s ^ 17
    - 423407544 * s ^ 16
    + 768459413 * s ^ 15
    - 1304631740 * s ^ 14
    + 2002560017 * s ^ 13
    - 2678166642 * s ^ 12
    + 3031088980 * s ^ 11
    - 2811934034 * s ^ 10
    + 2042767522 * s ^ 9
    - 1084644440 * s ^ 8
    + 362226800 * s ^ 7
    - 24934805 * s ^ 6
    - 48027693 * s ^ 5
    + 28410322 * s ^ 4
    - 7041270 * s ^ 3
    + 142390 * s ^ 2
    + 234034 * s
    + 2860

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient20 (s : ℚ) : ℚ :=
  s ^ 28
    - 35 * s ^ 27
    + 563 * s ^ 26
    - 5552 * s ^ 25
    + 37744 * s ^ 24
    - 188642 * s ^ 23
    + 724316 * s ^ 22
    - 2229816 * s ^ 21
    + 5856079 * s ^ 20
    - 14429453 * s ^ 19
    + 36414570 * s ^ 18
    - 93610061 * s ^ 17
    + 225826051 * s ^ 16
    - 476750520 * s ^ 15
    + 853577803 * s ^ 14
    - 1283815974 * s ^ 13
    + 1612369353 * s ^ 12
    - 1664394218 * s ^ 11
    + 1362673873 * s ^ 10
    - 825281893 * s ^ 9
    + 310583458 * s ^ 8
    - 9710846 * s ^ 7
    - 76564969 * s ^ 6
    + 56415499 * s ^ 5
    - 21252607 * s ^ 4
    + 3546912 * s ^ 3
    + 435244 * s ^ 2
    - 222369 * s
    - 4511

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient21 (s : ℚ) : ℚ :=
  -2 * s ^ 26
    + 70 * s ^ 25
    - 1158 * s ^ 24
    + 12094 * s ^ 23
    - 89810 * s ^ 22
    + 505943 * s ^ 21
    - 2250630 * s ^ 20
    + 8118729 * s ^ 19
    - 24196535 * s ^ 18
    + 60412786 * s ^ 17
    - 127746658 * s ^ 16
    + 230650330 * s ^ 15
    - 356808836 * s ^ 14
    + 470180959 * s ^ 13
    - 516275663 * s ^ 12
    + 449638042 * s ^ 11
    - 277746037 * s ^ 10
    + 77458362 * s ^ 9
    + 58141337 * s ^ 8
    - 96081787 * s ^ 7
    + 71214060 * s ^ 6
    - 33337192 * s ^ 5
    + 9088421 * s ^ 4
    - 405946 * s ^ 3
    - 642876 * s ^ 2
    + 156706 * s
    + 5291

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient22 (s : ℚ) : ℚ :=
  s ^ 24
    - 32 * s ^ 23
    + 484 * s ^ 22
    - 4625 * s ^ 21
    + 31474 * s ^ 20
    - 162749 * s ^ 19
    + 664163 * s ^ 18
    - 2182762 * s ^ 17
    + 5808628 * s ^ 16
    - 12388692 * s ^ 15
    + 20479488 * s ^ 14
    - 23984137 * s ^ 13
    + 13538522 * s ^ 12
    + 15042132 * s ^ 11
    - 51472978 * s ^ 10
    + 75102045 * s ^ 9
    - 73258412 * s ^ 8
    + 52115080 * s ^ 7
    - 27184748 * s ^ 6
    + 9386455 * s ^ 5
    - 1105248 * s ^ 4
    - 818509 * s ^ 3
    + 476375 * s ^ 2
    - 77382 * s
    - 4573

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient23 (s : ℚ) : ℚ :=
  -2 * s ^ 21
    + 63 * s ^ 20
    - 933 * s ^ 19
    + 8643 * s ^ 18
    - 56159 * s ^ 17
    + 271718 * s ^ 16
    - 1013167 * s ^ 15
    + 2969476 * s ^ 14
    - 6910176 * s ^ 13
    + 12808052 * s ^ 12
    - 18878388 * s ^ 11
    + 22038140 * s ^ 10
    - 20288821 * s ^ 9
    + 14633617 * s ^ 8
    - 8006214 * s ^ 7
    + 2795136 * s ^ 6
    + 82614 * s ^ 5
    - 893041 * s ^ 4
    + 622128 * s ^ 3
    - 209111 * s ^ 2
    + 23590 * s
    + 2835

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient24 (s : ℚ) : ℚ :=
  s ^ 18
    - 28 * s ^ 17
    + 362 * s ^ 16
    - 2864 * s ^ 15
    + 15476 * s ^ 14
    - 60308 * s ^ 13
    + 174402 * s ^ 12
    - 380114 * s ^ 11
    + 632044 * s ^ 10
    - 820828 * s ^ 9
    + 882330 * s ^ 8
    - 864550 * s ^ 7
    + 811696 * s ^ 6
    - 674307 * s ^ 5
    + 435772 * s ^ 4
    - 195062 * s ^ 3
    + 49903 * s ^ 2
    - 2731 * s
    - 1194

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient25 (s : ℚ) : ℚ :=
  -s ^ 14
    + 25 * s ^ 13
    - 282 * s ^ 12
    + 1896 * s ^ 11
    - 8459 * s ^ 10
    + 26393 * s ^ 9
    - 59148 * s ^ 8
    + 96314 * s ^ 7
    - 114095 * s ^ 6
    + 97536 * s ^ 5
    - 58628 * s ^ 4
    + 22748 * s ^ 3
    - 3981 * s ^ 2
    - 624 * s
    + 306

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorStep3Coefficient26 (s : ℚ) : ℚ :=
  s ^ 7
    - 14 * s ^ 6
    + 80 * s ^ 5
    - 240 * s ^ 4
    + 405 * s ^ 3
    - 382 * s ^ 2
    + 186 * s
    - 36

/-- Exact polynomial, presented coefficientwise in the raw chart variable. -/
def denominatorStep3 (r s : ℚ) : ℚ :=
  denominatorStep3Coefficient0 s +
    denominatorStep3Coefficient1 s * r +
    denominatorStep3Coefficient2 s * r ^ 2 +
    denominatorStep3Coefficient3 s * r ^ 3 +
    denominatorStep3Coefficient4 s * r ^ 4 +
    denominatorStep3Coefficient5 s * r ^ 5 +
    denominatorStep3Coefficient6 s * r ^ 6 +
    denominatorStep3Coefficient7 s * r ^ 7 +
    denominatorStep3Coefficient8 s * r ^ 8 +
    denominatorStep3Coefficient9 s * r ^ 9 +
    denominatorStep3Coefficient10 s * r ^ 10 +
    denominatorStep3Coefficient11 s * r ^ 11 +
    denominatorStep3Coefficient12 s * r ^ 12 +
    denominatorStep3Coefficient13 s * r ^ 13 +
    denominatorStep3Coefficient14 s * r ^ 14 +
    denominatorStep3Coefficient15 s * r ^ 15 +
    denominatorStep3Coefficient16 s * r ^ 16 +
    denominatorStep3Coefficient17 s * r ^ 17 +
    denominatorStep3Coefficient18 s * r ^ 18 +
    denominatorStep3Coefficient19 s * r ^ 19 +
    denominatorStep3Coefficient20 s * r ^ 20 +
    denominatorStep3Coefficient21 s * r ^ 21 +
    denominatorStep3Coefficient22 s * r ^ 22 +
    denominatorStep3Coefficient23 s * r ^ 23 +
    denominatorStep3Coefficient24 s * r ^ 24 +
    denominatorStep3Coefficient25 s * r ^ 25 +
    denominatorStep3Coefficient26 s * r ^ 26

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_0 (s : ℚ) :
    denominatorStep3Coefficient0 s =
    denominatorStep2Coefficient0 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient0,
    denominatorStep2Coefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_1 (s : ℚ) :
    denominatorStep3Coefficient1 s =
    denominatorStep2Coefficient0 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient1 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient1,
    denominatorStep2Coefficient0,
    denominatorStep2Coefficient1,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_2 (s : ℚ) :
    denominatorStep3Coefficient2 s =
    denominatorStep2Coefficient0 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient1 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient2 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient2,
    denominatorStep2Coefficient0,
    denominatorStep2Coefficient1,
    denominatorStep2Coefficient2,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_3 (s : ℚ) :
    denominatorStep3Coefficient3 s =
    denominatorStep2Coefficient0 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient1 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient2 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient3 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient3,
    denominatorStep2Coefficient0,
    denominatorStep2Coefficient1,
    denominatorStep2Coefficient2,
    denominatorStep2Coefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_4 (s : ℚ) :
    denominatorStep3Coefficient4 s =
    denominatorStep2Coefficient1 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient2 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient3 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient4 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient4,
    denominatorStep2Coefficient1,
    denominatorStep2Coefficient2,
    denominatorStep2Coefficient3,
    denominatorStep2Coefficient4,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_5 (s : ℚ) :
    denominatorStep3Coefficient5 s =
    denominatorStep2Coefficient2 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient3 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient4 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient5 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient5,
    denominatorStep2Coefficient2,
    denominatorStep2Coefficient3,
    denominatorStep2Coefficient4,
    denominatorStep2Coefficient5,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_6 (s : ℚ) :
    denominatorStep3Coefficient6 s =
    denominatorStep2Coefficient3 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient4 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient5 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient6 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient6,
    denominatorStep2Coefficient3,
    denominatorStep2Coefficient4,
    denominatorStep2Coefficient5,
    denominatorStep2Coefficient6,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_7 (s : ℚ) :
    denominatorStep3Coefficient7 s =
    denominatorStep2Coefficient4 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient5 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient6 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient7 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient7,
    denominatorStep2Coefficient4,
    denominatorStep2Coefficient5,
    denominatorStep2Coefficient6,
    denominatorStep2Coefficient7,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_8 (s : ℚ) :
    denominatorStep3Coefficient8 s =
    denominatorStep2Coefficient5 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient6 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient7 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient8 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient8,
    denominatorStep2Coefficient5,
    denominatorStep2Coefficient6,
    denominatorStep2Coefficient7,
    denominatorStep2Coefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_9 (s : ℚ) :
    denominatorStep3Coefficient9 s =
    denominatorStep2Coefficient6 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient7 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient8 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient9 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient9,
    denominatorStep2Coefficient6,
    denominatorStep2Coefficient7,
    denominatorStep2Coefficient8,
    denominatorStep2Coefficient9,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_10 (s : ℚ) :
    denominatorStep3Coefficient10 s =
    denominatorStep2Coefficient7 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient8 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient9 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient10 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient10,
    denominatorStep2Coefficient7,
    denominatorStep2Coefficient8,
    denominatorStep2Coefficient9,
    denominatorStep2Coefficient10,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_11 (s : ℚ) :
    denominatorStep3Coefficient11 s =
    denominatorStep2Coefficient8 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient9 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient10 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient11 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient11,
    denominatorStep2Coefficient8,
    denominatorStep2Coefficient9,
    denominatorStep2Coefficient10,
    denominatorStep2Coefficient11,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_12 (s : ℚ) :
    denominatorStep3Coefficient12 s =
    denominatorStep2Coefficient9 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient10 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient11 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient12 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient12,
    denominatorStep2Coefficient9,
    denominatorStep2Coefficient10,
    denominatorStep2Coefficient11,
    denominatorStep2Coefficient12,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_13 (s : ℚ) :
    denominatorStep3Coefficient13 s =
    denominatorStep2Coefficient10 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient11 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient12 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient13 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient13,
    denominatorStep2Coefficient10,
    denominatorStep2Coefficient11,
    denominatorStep2Coefficient12,
    denominatorStep2Coefficient13,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_14 (s : ℚ) :
    denominatorStep3Coefficient14 s =
    denominatorStep2Coefficient11 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient12 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient13 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient14 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient14,
    denominatorStep2Coefficient11,
    denominatorStep2Coefficient12,
    denominatorStep2Coefficient13,
    denominatorStep2Coefficient14,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_15 (s : ℚ) :
    denominatorStep3Coefficient15 s =
    denominatorStep2Coefficient12 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient13 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient14 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient15 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient15,
    denominatorStep2Coefficient12,
    denominatorStep2Coefficient13,
    denominatorStep2Coefficient14,
    denominatorStep2Coefficient15,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_16 (s : ℚ) :
    denominatorStep3Coefficient16 s =
    denominatorStep2Coefficient13 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient14 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient15 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient16 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient16,
    denominatorStep2Coefficient13,
    denominatorStep2Coefficient14,
    denominatorStep2Coefficient15,
    denominatorStep2Coefficient16,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_17 (s : ℚ) :
    denominatorStep3Coefficient17 s =
    denominatorStep2Coefficient14 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient15 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient16 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient17 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient17,
    denominatorStep2Coefficient14,
    denominatorStep2Coefficient15,
    denominatorStep2Coefficient16,
    denominatorStep2Coefficient17,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_18 (s : ℚ) :
    denominatorStep3Coefficient18 s =
    denominatorStep2Coefficient15 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient16 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient17 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient18 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient18,
    denominatorStep2Coefficient15,
    denominatorStep2Coefficient16,
    denominatorStep2Coefficient17,
    denominatorStep2Coefficient18,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_19 (s : ℚ) :
    denominatorStep3Coefficient19 s =
    denominatorStep2Coefficient16 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient17 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient18 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient19 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient19,
    denominatorStep2Coefficient16,
    denominatorStep2Coefficient17,
    denominatorStep2Coefficient18,
    denominatorStep2Coefficient19,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_20 (s : ℚ) :
    denominatorStep3Coefficient20 s =
    denominatorStep2Coefficient17 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient18 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient19 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient20 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient20,
    denominatorStep2Coefficient17,
    denominatorStep2Coefficient18,
    denominatorStep2Coefficient19,
    denominatorStep2Coefficient20,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_21 (s : ℚ) :
    denominatorStep3Coefficient21 s =
    denominatorStep2Coefficient18 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient19 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient20 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient21 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient21,
    denominatorStep2Coefficient18,
    denominatorStep2Coefficient19,
    denominatorStep2Coefficient20,
    denominatorStep2Coefficient21,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_22 (s : ℚ) :
    denominatorStep3Coefficient22 s =
    denominatorStep2Coefficient19 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient20 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient21 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient22 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient22,
    denominatorStep2Coefficient19,
    denominatorStep2Coefficient20,
    denominatorStep2Coefficient21,
    denominatorStep2Coefficient22,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_23 (s : ℚ) :
    denominatorStep3Coefficient23 s =
    denominatorStep2Coefficient20 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient21 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient22 s *
        rawUnitEightDenominatorCoefficient1 s
      + denominatorStep2Coefficient23 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [denominatorStep3Coefficient23,
    denominatorStep2Coefficient20,
    denominatorStep2Coefficient21,
    denominatorStep2Coefficient22,
    denominatorStep2Coefficient23,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_24 (s : ℚ) :
    denominatorStep3Coefficient24 s =
    denominatorStep2Coefficient21 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient22 s *
        rawUnitEightDenominatorCoefficient2 s
      + denominatorStep2Coefficient23 s *
        rawUnitEightDenominatorCoefficient1 s
    := by
  simp only [denominatorStep3Coefficient24,
    denominatorStep2Coefficient21,
    denominatorStep2Coefficient22,
    denominatorStep2Coefficient23,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_25 (s : ℚ) :
    denominatorStep3Coefficient25 s =
    denominatorStep2Coefficient22 s *
        rawUnitEightDenominatorCoefficient3 s
      + denominatorStep2Coefficient23 s *
        rawUnitEightDenominatorCoefficient2 s
    := by
  simp only [denominatorStep3Coefficient25,
    denominatorStep2Coefficient22,
    denominatorStep2Coefficient23,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorStep3Coefficient_product_certificate_26 (s : ℚ) :
    denominatorStep3Coefficient26 s =
    denominatorStep2Coefficient23 s *
        rawUnitEightDenominatorCoefficient3 s
    := by
  simp only [denominatorStep3Coefficient26,
    denominatorStep2Coefficient23,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem denominatorStep3_eq_denominatorStep2_mul_rawUnitEightDenominator (r s : ℚ) :
    denominatorStep3 r s = denominatorStep2 r s * rawUnitEightDenominator r s := by
  have h0 := denominatorStep3Coefficient_product_certificate_0 s
  have h1 := denominatorStep3Coefficient_product_certificate_1 s
  have h2 := denominatorStep3Coefficient_product_certificate_2 s
  have h3 := denominatorStep3Coefficient_product_certificate_3 s
  have h4 := denominatorStep3Coefficient_product_certificate_4 s
  have h5 := denominatorStep3Coefficient_product_certificate_5 s
  have h6 := denominatorStep3Coefficient_product_certificate_6 s
  have h7 := denominatorStep3Coefficient_product_certificate_7 s
  have h8 := denominatorStep3Coefficient_product_certificate_8 s
  have h9 := denominatorStep3Coefficient_product_certificate_9 s
  have h10 := denominatorStep3Coefficient_product_certificate_10 s
  have h11 := denominatorStep3Coefficient_product_certificate_11 s
  have h12 := denominatorStep3Coefficient_product_certificate_12 s
  have h13 := denominatorStep3Coefficient_product_certificate_13 s
  have h14 := denominatorStep3Coefficient_product_certificate_14 s
  have h15 := denominatorStep3Coefficient_product_certificate_15 s
  have h16 := denominatorStep3Coefficient_product_certificate_16 s
  have h17 := denominatorStep3Coefficient_product_certificate_17 s
  have h18 := denominatorStep3Coefficient_product_certificate_18 s
  have h19 := denominatorStep3Coefficient_product_certificate_19 s
  have h20 := denominatorStep3Coefficient_product_certificate_20 s
  have h21 := denominatorStep3Coefficient_product_certificate_21 s
  have h22 := denominatorStep3Coefficient_product_certificate_22 s
  have h23 := denominatorStep3Coefficient_product_certificate_23 s
  have h24 := denominatorStep3Coefficient_product_certificate_24 s
  have h25 := denominatorStep3Coefficient_product_certificate_25 s
  have h26 := denominatorStep3Coefficient_product_certificate_26 s
  simp only [denominatorStep3, denominatorStep2, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 35
    + 4 * s ^ 34
    - 10 * s ^ 33
    + 18 * s ^ 32
    - 25 * s ^ 31
    + 28 * s ^ 30
    - 25 * s ^ 29
    + 18 * s ^ 28
    - 10 * s ^ 27
    + 4 * s ^ 26
    - s ^ 25

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient2 (s : ℚ) : ℚ :=
  s ^ 41
    - 7 * s ^ 40
    + 28 * s ^ 39
    - 82 * s ^ 38
    + 196 * s ^ 37
    - 408 * s ^ 36
    + 752 * s ^ 35
    - 1179 * s ^ 34
    + 1556 * s ^ 33
    - 1665 * s ^ 32
    + 1357 * s ^ 31
    - 675 * s ^ 30
    - 150 * s ^ 29
    + 776 * s ^ 28
    - 1024 * s ^ 27
    + 904 * s ^ 26
    - 599 * s ^ 25
    + 307 * s ^ 24
    - 117 * s ^ 23
    + 36 * s ^ 22
    - 8 * s ^ 21
    + s ^ 20

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient3 (s : ℚ) : ℚ :=
  -2 * s ^ 43
    + 22 * s ^ 42
    - 117 * s ^ 41
    + 381 * s ^ 40
    - 891 * s ^ 39
    + 1585 * s ^ 38
    - 2116 * s ^ 37
    + 1548 * s ^ 36
    + 2316 * s ^ 35
    - 13001 * s ^ 34
    + 32990 * s ^ 33
    - 61403 * s ^ 32
    + 91288 * s ^ 31
    - 111943 * s ^ 30
    + 114305 * s ^ 29
    - 96247 * s ^ 28
    + 65375 * s ^ 27
    - 33125 * s ^ 26
    + 9348 * s ^ 25
    + 2677 * s ^ 24
    - 5674 * s ^ 23
    + 4256 * s ^ 22
    - 2261 * s ^ 21
    + 919 * s ^ 20
    - 286 * s ^ 19
    + 66 * s ^ 18
    - 11 * s ^ 17
    + s ^ 16

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient4 (s : ℚ) : ℚ :=
  s ^ 45
    - 16 * s ^ 44
    + 108 * s ^ 43
    - 353 * s ^ 42
    + 285 * s ^ 41
    + 2601 * s ^ 40
    - 14518 * s ^ 39
    + 46803 * s ^ 38
    - 116967 * s ^ 37
    + 249689 * s ^ 36
    - 469615 * s ^ 35
    + 771377 * s ^ 34
    - 1081938 * s ^ 33
    + 1262265 * s ^ 32
    - 1151323 * s ^ 31
    + 675122 * s ^ 30
    + 80102 * s ^ 29
    - 877485 * s ^ 28
    + 1437627 * s ^ 27
    - 1604666 * s ^ 26
    + 1399342 * s ^ 25
    - 990657 * s ^ 24
    + 573495 * s ^ 23
    - 267649 * s ^ 22
    + 98594 * s ^ 21
    - 25398 * s ^ 20
    + 2199 * s ^ 19
    + 1823 * s ^ 18
    - 1178 * s ^ 17
    + 411 * s ^ 16
    - 93 * s ^ 15
    + 13 * s ^ 14
    - s ^ 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient5 (s : ℚ) : ℚ :=
  11 * s ^ 45
    - 237 * s ^ 44
    + 2320 * s ^ 43
    - 13730 * s ^ 42
    + 55444 * s ^ 41
    - 165369 * s ^ 40
    + 388632 * s ^ 39
    - 761450 * s ^ 38
    + 1282548 * s ^ 37
    - 1828119 * s ^ 36
    + 1937162 * s ^ 35
    - 593354 * s ^ 34
    - 3575719 * s ^ 33
    + 11512652 * s ^ 32
    - 22755932 * s ^ 31
    + 34777325 * s ^ 30
    - 43697750 * s ^ 29
    + 46024221 * s ^ 28
    - 40625452 * s ^ 27
    + 29550652 * s ^ 26
    - 16744569 * s ^ 25
    + 6111463 * s ^ 24
    + 338564 * s ^ 23
    - 2809234 * s ^ 22
    + 2787235 * s ^ 21
    - 1876472 * s ^ 20
    + 986388 * s ^ 19
    - 419029 * s ^ 18
    + 144530 * s ^ 17
    - 40181 * s ^ 16
    + 8707 * s ^ 15
    - 1412 * s ^ 14
    + 168 * s ^ 13
    - 14 * s ^ 12
    + s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient6 (s : ℚ) : ℚ :=
  s ^ 48
    - 23 * s ^ 47
    + 271 * s ^ 46
    - 2124 * s ^ 45
    + 11890 * s ^ 44
    - 48042 * s ^ 43
    + 136863 * s ^ 42
    - 249812 * s ^ 41
    + 146098 * s ^ 40
    + 830494 * s ^ 39
    - 3986243 * s ^ 38
    + 11816924 * s ^ 37
    - 28998508 * s ^ 36
    + 62884744 * s ^ 35
    - 120897736 * s ^ 34
    + 203663747 * s ^ 33
    - 297832863 * s ^ 32
    + 374583013 * s ^ 31
    - 397923575 * s ^ 30
    + 343222923 * s ^ 29
    - 213706566 * s ^ 28
    + 44771020 * s ^ 27
    + 111008689 * s ^ 26
    - 210079256 * s ^ 25
    + 235953736 * s ^ 24
    - 203068136 * s ^ 23
    + 142411569 * s ^ 22
    - 82913762 * s ^ 21
    + 40166711 * s ^ 20
    - 15725839 * s ^ 19
    + 4561892 * s ^ 18
    - 669854 * s ^ 17
    - 203951 * s ^ 16
    + 204518 * s ^ 15
    - 91915 * s ^ 14
    + 28967 * s ^ 13
    - 7017 * s ^ 12
    + 1327 * s ^ 11
    - 193 * s ^ 10
    + 19 * s ^ 9
    - s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 49
    - 40 * s ^ 48
    + 369 * s ^ 47
    - 1906 * s ^ 46
    + 3944 * s ^ 45
    + 22504 * s ^ 44
    - 262698 * s ^ 43
    + 1424651 * s ^ 42
    - 5379462 * s ^ 41
    + 15838907 * s ^ 40
    - 39119030 * s ^ 39
    + 86131868 * s ^ 38
    - 175669681 * s ^ 37
    + 332662957 * s ^ 36
    - 569541227 * s ^ 35
    + 847203795 * s ^ 34
    - 1040906338 * s ^ 33
    + 952049930 * s ^ 32
    - 383601551 * s ^ 31
    - 738345496 * s ^ 30
    + 2258821512 * s ^ 29
    - 3799124127 * s ^ 28
    + 4892346506 * s ^ 27
    - 5202160203 * s ^ 26
    + 4683771063 * s ^ 25
    - 3584215346 * s ^ 24
    + 2308306726 * s ^ 23
    - 1213104577 * s ^ 22
    + 477351159 * s ^ 21
    - 93617471 * s ^ 20
    - 49538007 * s ^ 19
    + 69692988 * s ^ 18
    - 48168910 * s ^ 17
    + 24520444 * s ^ 16
    - 9964179 * s ^ 15
    + 3293843 * s ^ 14
    - 886650 * s ^ 13
    + 192593 * s ^ 12
    - 32520 * s ^ 11
    + 3885 * s ^ 10
    - 215 * s ^ 9
    - 15 * s ^ 8
    + 3 * s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient8 (s : ℚ) : ℚ :=
  14 * s ^ 49
    - 384 * s ^ 48
    + 5040 * s ^ 47
    - 42521 * s ^ 46
    + 258795 * s ^ 45
    - 1200892 * s ^ 44
    + 4373955 * s ^ 43
    - 12763972 * s ^ 42
    + 30648494 * s ^ 41
    - 63420413 * s ^ 40
    + 120510748 * s ^ 39
    - 217399855 * s ^ 38
    + 348247853 * s ^ 37
    - 387255438 * s ^ 36
    - 70362590 * s ^ 35
    + 1800692358 * s ^ 34
    - 5784332315 * s ^ 33
    + 12723546604 * s ^ 32
    - 22413838959 * s ^ 31
    + 33295254633 * s ^ 30
    - 42604555799 * s ^ 29
    + 47327638629 * s ^ 28
    - 45549117273 * s ^ 27
    + 37499233171 * s ^ 26
    - 25541467279 * s ^ 25
    + 13109586440 * s ^ 24
    - 3232121741 * s ^ 23
    - 2641903893 * s ^ 22
    + 4785902179 * s ^ 21
    - 4512276015 * s ^ 20
    + 3242214861 * s ^ 19
    - 1919480972 * s ^ 18
    + 959200604 * s ^ 17
    - 407076551 * s ^ 16
    + 146171449 * s ^ 15
    - 43765599 * s ^ 14
    + 10678498 * s ^ 13
    - 2032908 * s ^ 12
    + 266165 * s ^ 11
    - 11867 * s ^ 10
    - 4164 * s ^ 9
    + 984 * s ^ 8
    - 71 * s ^ 7
    - 3 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient9 (s : ℚ) : ℚ :=
  -2 * s ^ 51
    + 60 * s ^ 50
    - 876 * s ^ 49
    + 8082 * s ^ 48
    - 51868 * s ^ 47
    + 240080 * s ^ 46
    - 787909 * s ^ 45
    + 1585471 * s ^ 44
    - 89879 * s ^ 43
    - 13682880 * s ^ 42
    + 63725807 * s ^ 41
    - 196568645 * s ^ 40
    + 523245204 * s ^ 39
    - 1391058363 * s ^ 38
    + 3778755865 * s ^ 37
    - 9780243955 * s ^ 36
    + 22654972940 * s ^ 35
    - 45808374965 * s ^ 34
    + 80619359522 * s ^ 33
    - 123992883949 * s ^ 32
    + 167017708421 * s ^ 31
    - 196137479867 * s ^ 30
    + 197661022893 * s ^ 29
    - 164246522007 * s ^ 28
    + 99820393270 * s ^ 27
    - 19706627448 * s ^ 26
    - 55121901339 * s ^ 25
    + 106546201982 * s ^ 24
    - 126280616950 * s ^ 23
    + 117897000660 * s ^ 22
    - 92672546751 * s ^ 21
    + 63032677343 * s ^ 20
    - 37526302472 * s ^ 19
    + 19550417523 * s ^ 18
    - 8858724751 * s ^ 17
    + 3453539875 * s ^ 16
    - 1137204790 * s ^ 15
    + 305765905 * s ^ 14
    - 62955367 * s ^ 13
    + 8155504 * s ^ 12
    + 158045 * s ^ 11
    - 407954 * s ^ 10
    + 112433 * s ^ 9
    - 14341 * s ^ 8
    + 329 * s ^ 7
    + 113 * s ^ 6
    + s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 52
    + 25 * s ^ 51
    - 261 * s ^ 50
    + 1117 * s ^ 49
    + 4711 * s ^ 48
    - 109964 * s ^ 47
    + 921682 * s ^ 46
    - 5163390 * s ^ 45
    + 21904840 * s ^ 44
    - 74756684 * s ^ 43
    + 217513053 * s ^ 42
    - 586100087 * s ^ 41
    + 1601011903 * s ^ 40
    - 4538429144 * s ^ 39
    + 12547021918 * s ^ 38
    - 31495383221 * s ^ 37
    + 69128348038 * s ^ 36
    - 131082513590 * s ^ 35
    + 214159735084 * s ^ 34
    - 299844487892 * s ^ 33
    + 352242957328 * s ^ 32
    - 323969190930 * s ^ 31
    + 172174465798 * s ^ 30
    + 118220814078 * s ^ 29
    - 515876089047 * s ^ 28
    + 942596562957 * s ^ 27
    - 1296199966386 * s ^ 26
    + 1488901833046 * s ^ 25
    - 1481665578868 * s ^ 24
    + 1298182937631 * s ^ 23
    - 1010051229852 * s ^ 22
    + 701027336901 * s ^ 21
    - 434594985119 * s ^ 20
    + 239758694527 * s ^ 19
    - 116471995454 * s ^ 18
    + 49065670152 * s ^ 17
    - 17508522435 * s ^ 16
    + 5065234391 * s ^ 15
    - 1068302600 * s ^ 14
    + 102407614 * s ^ 13
    + 33261721 * s ^ 12
    - 21023965 * s ^ 11
    + 6216350 * s ^ 10
    - 1116414 * s ^ 9
    + 84153 * s ^ 8
    + 8202 * s ^ 7
    - 1868 * s ^ 6
    - 48 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient11 (s : ℚ) : ℚ :=
  -4 * s ^ 52
    + 139 * s ^ 51
    - 2272 * s ^ 50
    + 23327 * s ^ 49
    - 168825 * s ^ 48
    + 915219 * s ^ 47
    - 3872254 * s ^ 46
    + 13393674 * s ^ 45
    - 41423693 * s ^ 44
    + 133863068 * s ^ 43
    - 497939865 * s ^ 42
    + 1931594792 * s ^ 41
    - 6780005443 * s ^ 40
    + 20102608918 * s ^ 39
    - 49308934271 * s ^ 38
    + 99227820676 * s ^ 37
    - 160778949641 * s ^ 36
    + 195958644108 * s ^ 35
    - 126630908522 * s ^ 34
    - 164249088779 * s ^ 33
    + 812000878066 * s ^ 32
    - 1924646629770 * s ^ 31
    + 3515047983649 * s ^ 30
    - 5438707123838 * s ^ 29
    + 7383732408400 * s ^ 28
    - 8939772742607 * s ^ 27
    + 9730922557977 * s ^ 26
    - 9558602354754 * s ^ 25
    + 8483880853281 * s ^ 24
    - 6805538302136 * s ^ 23
    + 4932910719055 * s ^ 22
    - 3225146260132 * s ^ 21
    + 1892146596297 * s ^ 20
    - 984397188495 * s ^ 19
    + 444774528826 * s ^ 18
    - 168987817402 * s ^ 17
    + 50571670691 * s ^ 16
    - 9687650938 * s ^ 15
    - 388442383 * s ^ 14
    + 1279964944 * s ^ 13
    - 634416933 * s ^ 12
    + 201880237 * s ^ 11
    - 44229020 * s ^ 10
    + 5573412 * s ^ 9
    + 117466 * s ^ 8
    - 162687 * s ^ 7
    + 17400 * s ^ 6
    + 1040 * s ^ 5
    + 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient12 (s : ℚ) : ℚ :=
  -s ^ 53
    + 30 * s ^ 52
    - 396 * s ^ 51
    + 2857 * s ^ 50
    - 10081 * s ^ 49
    - 9433 * s ^ 48
    + 273380 * s ^ 47
    - 895150 * s ^ 46
    - 4994206 * s ^ 45
    + 74057436 * s ^ 44
    - 473895477 * s ^ 43
    + 2066402937 * s ^ 42
    - 6708351794 * s ^ 41
    + 16293824976 * s ^ 40
    - 27074596218 * s ^ 39
    + 15091400220 * s ^ 38
    + 87880941220 * s ^ 37
    - 420904037228 * s ^ 36
    + 1210578620461 * s ^ 35
    - 2765786384159 * s ^ 34
    + 5436986181140 * s ^ 33
    - 9518365198366 * s ^ 32
    + 15079058462146 * s ^ 31
    - 21769371931784 * s ^ 30
    + 28726335467210 * s ^ 29
    - 34691661353526 * s ^ 28
    + 38347251682791 * s ^ 27
    - 38763240561047 * s ^ 26
    + 35772883917076 * s ^ 25
    - 30078346151641 * s ^ 24
    + 22996048282349 * s ^ 23
    - 15939337080517 * s ^ 22
    + 9950357069696 * s ^ 21
    - 5516737509754 * s ^ 20
    + 2643063784980 * s ^ 19
    - 1039191386122 * s ^ 18
    + 296094327951 * s ^ 17
    - 28703909948 * s ^ 16
    - 31019987960 * s ^ 15
    + 25738626681 * s ^ 14
    - 12140461471 * s ^ 13
    + 4156976329 * s ^ 12
    - 1056204873 * s ^ 11
    + 175279800 * s ^ 10
    - 6057278 * s ^ 9
    - 6012556 * s ^ 8
    + 1504113 * s ^ 7
    - 90980 * s ^ 6
    - 13734 * s ^ 5
    - 79 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient13 (s : ℚ) : ℚ :=
  -s ^ 53
    + 39 * s ^ 52
    - 634 * s ^ 51
    + 5334 * s ^ 50
    - 16908 * s ^ 49
    - 143996 * s ^ 48
    + 2424096 * s ^ 47
    - 18649138 * s ^ 46
    + 96257185 * s ^ 45
    - 350442213 * s ^ 44
    + 801831473 * s ^ 43
    - 123229324 * s ^ 42
    - 9147420381 * s ^ 41
    + 53214453884 * s ^ 40
    - 201501237222 * s ^ 39
    + 602396446426 * s ^ 38
    - 1523441812718 * s ^ 37
    + 3388193384112 * s ^ 36
    - 6801947568724 * s ^ 35
    + 12537064828732 * s ^ 34
    - 21402270140677 * s ^ 33
    + 33913033210028 * s ^ 32
    - 49801315706213 * s ^ 31
    + 67610439192059 * s ^ 30
    - 84689044110791 * s ^ 29
    + 97713747767861 * s ^ 28
    - 103638160871692 * s ^ 27
    + 100785713418148 * s ^ 26
    - 89607477914207 * s ^ 25
    + 72621392290423 * s ^ 24
    - 53436800367158 * s ^ 23
    + 35401499060533 * s ^ 22
    - 20718748415456 * s ^ 21
    + 10285511650436 * s ^ 20
    - 3930967480314 * s ^ 19
    + 783502895806 * s ^ 18
    + 335090687747 * s ^ 17
    - 481118128167 * s ^ 16
    + 321374400221 * s ^ 15
    - 154510112927 * s ^ 14
    + 57242515636 * s ^ 13
    - 16316405045 * s ^ 12
    + 3249546236 * s ^ 11
    - 228012248 * s ^ 10
    - 123586090 * s ^ 9
    + 53989532 * s ^ 8
    - 8726326 * s ^ 7
    + 116007 * s ^ 6
    + 125141 * s ^ 5
    + 1474 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient14 (s : ℚ) : ℚ :=
  -2 * s ^ 53
    + 88 * s ^ 52
    - 1778 * s ^ 51
    + 21513 * s ^ 50
    - 168068 * s ^ 49
    + 794862 * s ^ 48
    - 843474 * s ^ 47
    - 22442710 * s ^ 46
    + 242749112 * s ^ 45
    - 1571325804 * s ^ 44
    + 7707162148 * s ^ 43
    - 30801934017 * s ^ 42
    + 103964334116 * s ^ 41
    - 303652782412 * s ^ 40
    + 784087898436 * s ^ 39
    - 1828970804992 * s ^ 38
    + 3934848939182 * s ^ 37
    - 7934375209453 * s ^ 36
    + 15105496077277 * s ^ 35
    - 27100743870950 * s ^ 34
    + 45492172301897 * s ^ 33
    - 70915916701877 * s ^ 32
    + 102157566854855 * s ^ 31
    - 135701427726167 * s ^ 30
    + 166060274170678 * s ^ 29
    - 186922945089677 * s ^ 28
    + 193030392115431 * s ^ 27
    - 182257293333931 * s ^ 26
    + 156736755053638 * s ^ 25
    - 122080884031017 * s ^ 24
    + 85070661407084 * s ^ 23
    - 51444050608453 * s ^ 22
    + 24977468396311 * s ^ 21
    - 7354823545834 * s ^ 20
    - 1831743643846 * s ^ 19
    + 4727308864047 * s ^ 18
    - 4226632253356 * s ^ 17
    + 2692795644590 * s ^ 16
    - 1352894180663 * s ^ 15
    + 543905448984 * s ^ 14
    - 170743189584 * s ^ 13
    + 38206279214 * s ^ 12
    - 3341337416 * s ^ 11
    - 1858409560 * s ^ 10
    + 1097929235 * s ^ 9
    - 292882674 * s ^ 8
    + 32350812 * s ^ 7
    + 2381516 * s ^ 6
    - 839879 * s ^ 5
    - 17398 * s ^ 4
    - 34 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient15 (s : ℚ) : ℚ :=
  -4 * s ^ 53
    + 200 * s ^ 52
    - 4814 * s ^ 51
    + 74118 * s ^ 50
    - 820210 * s ^ 49
    + 6960409 * s ^ 48
    - 47213942 * s ^ 47
    + 263448250 * s ^ 46
    - 1234783169 * s ^ 45
    + 4941346631 * s ^ 44
    - 17132754531 * s ^ 43
    + 52317657286 * s ^ 42
    - 143790743375 * s ^ 41
    + 366014939334 * s ^ 40
    - 889548949642 * s ^ 39
    + 2103781745593 * s ^ 38
    - 4826808371607 * s ^ 37
    + 10529987468159 * s ^ 36
    - 21361934509101 * s ^ 35
    + 39718169804246 * s ^ 34
    - 67323133442732 * s ^ 33
    + 104153574819261 * s ^ 32
    - 147648765702075 * s ^ 31
    + 192407855273503 * s ^ 30
    - 230523603727124 * s ^ 29
    + 253131215217438 * s ^ 28
    - 253481075853070 * s ^ 27
    + 230090060224767 * s ^ 26
    - 187505221041753 * s ^ 25
    + 134041383832725 * s ^ 24
    - 78685289546873 * s ^ 23
    + 29580990300642 * s ^ 22
    + 6530488145828 * s ^ 21
    - 26005413209585 * s ^ 20
    + 30133610573982 * s ^ 19
    - 24519889870457 * s ^ 18
    + 15807999643424 * s ^ 17
    - 8373334980692 * s ^ 16
    + 3630771409018 * s ^ 15
    - 1238200993542 * s ^ 14
    + 294799678865 * s ^ 13
    - 21672752013 * s ^ 12
    - 23026747381 * s ^ 11
    + 15265280684 * s ^ 10
    - 5383867542 * s ^ 9
    + 1087912731 * s ^ 8
    - 55606556 * s ^ 7
    - 24715042 * s ^ 6
    + 4302751 * s ^ 5
    + 146426 * s ^ 4
    + 561 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient16 (s : ℚ) : ℚ :=
  -s ^ 54
    + 45 * s ^ 53
    - 980 * s ^ 52
    + 13679 * s ^ 51
    - 136825 * s ^ 50
    + 1040201 * s ^ 49
    - 6226137 * s ^ 48
    + 30015230 * s ^ 47
    - 118611997 * s ^ 46
    + 393927445 * s ^ 45
    - 1170687902 * s ^ 44
    + 3588987798 * s ^ 43
    - 13139909554 * s ^ 42
    + 54461455558 * s ^ 41
    - 217158408796 * s ^ 40
    + 760275252279 * s ^ 39
    - 2280677831917 * s ^ 38
    + 5875692921501 * s ^ 37
    - 13147341455213 * s ^ 36
    + 25929388795215 * s ^ 35
    - 45817481049542 * s ^ 34
    + 73719233527424 * s ^ 33
    - 109396424682405 * s ^ 32
    + 150579290778257 * s ^ 31
    - 191651676147767 * s ^ 30
    + 223384180488563 * s ^ 29
    - 235611473047101 * s ^ 28
    + 221956862733702 * s ^ 27
    - 182585451858144 * s ^ 26
    + 122819674158074 * s ^ 25
    - 50562175941830 * s ^ 24
    - 23612922325532 * s ^ 23
    + 85363574198349 * s ^ 22
    - 120345610346412 * s ^ 21
    + 122747296934865 * s ^ 20
    - 99795488859030 * s ^ 19
    + 66784654290267 * s ^ 18
    - 37269601037940 * s ^ 17
    + 17197794728709 * s ^ 16
    - 6221347518143 * s ^ 15
    + 1473547064251 * s ^ 14
    + 11415736756 * s ^ 13
    - 238744887728 * s ^ 12
    + 156347057181 * s ^ 11
    - 65226968948 * s ^ 10
    + 18258631709 * s ^ 9
    - 2671318021 * s ^ 8
    - 180031705 * s ^ 7
    + 144567292 * s ^ 6
    - 17071580 * s ^ 5
    - 937213 * s ^ 4
    - 5987 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient17 (s : ℚ) : ℚ :=
  5 * s ^ 53
    - 206 * s ^ 52
    + 4098 * s ^ 51
    - 51956 * s ^ 50
    + 465976 * s ^ 49
    - 3083945 * s ^ 48
    + 14967019 * s ^ 47
    - 47659603 * s ^ 46
    + 30770724 * s ^ 45
    + 798160891 * s ^ 44
    - 6641530426 * s ^ 43
    + 34271922519 * s ^ 42
    - 135892356869 * s ^ 41
    + 440735564114 * s ^ 40
    - 1203163733006 * s ^ 39
    + 2818311001458 * s ^ 38
    - 5776257081687 * s ^ 37
    + 10625453877265 * s ^ 36
    - 18125605517828 * s ^ 35
    + 29606493763105 * s ^ 34
    - 46964907611531 * s ^ 33
    + 71321964988801 * s ^ 32
    - 100303856862826 * s ^ 31
    + 126193961935477 * s ^ 30
    - 137996685147795 * s ^ 29
    + 126794503682789 * s ^ 28
    - 89003682497577 * s ^ 27
    + 24371143250872 * s ^ 26
    + 65990575673392 * s ^ 25
    - 174552438970260 * s ^ 24
    + 279259278575908 * s ^ 23
    - 346506200482366 * s ^ 22
    + 350773377728151 * s ^ 21
    - 294317852646066 * s ^ 20
    + 205883936267102 * s ^ 19
    - 120069334130318 * s ^ 18
    + 57511103115864 * s ^ 17
    - 21052285945230 * s ^ 16
    + 4148585074676 * s ^ 15
    + 1366475585556 * s ^ 14
    - 1940034237334 * s ^ 13
    + 1220944898760 * s ^ 12
    - 561223107401 * s ^ 11
    + 193855723425 * s ^ 10
    - 43782951938 * s ^ 9
    + 2719547248 * s ^ 8
    + 1913508517 * s ^ 7
    - 611185842 * s ^ 6
    + 51948722 * s ^ 5
    + 4743159 * s ^ 4
    + 46416 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient18 (s : ℚ) : ℚ :=
  2 * s ^ 53
    - 104 * s ^ 52
    + 2558 * s ^ 51
    - 40095 * s ^ 50
    + 453027 * s ^ 49
    - 3947656 * s ^ 48
    + 27663843 * s ^ 47
    - 160118857 * s ^ 46
    + 777663441 * s ^ 45
    - 3190726122 * s ^ 44
    + 11042223786 * s ^ 43
    - 31904874244 * s ^ 42
    + 75339517567 * s ^ 41
    - 139705038053 * s ^ 40
    + 188118652776 * s ^ 39
    - 158131723870 * s ^ 38
    + 121879150693 * s ^ 37
    - 694258992258 * s ^ 36
    + 3480391191041 * s ^ 35
    - 10819906031364 * s ^ 34
    + 24014042039265 * s ^ 33
    - 40501656090090 * s ^ 32
    + 52569333037343 * s ^ 31
    - 50218017452792 * s ^ 30
    + 26358512163034 * s ^ 29
    + 22314371265429 * s ^ 28
    - 101295304625491 * s ^ 27
    + 221159967238381 * s ^ 26
    - 384800980838932 * s ^ 25
    + 565373524440745 * s ^ 24
    - 702204058209556 * s ^ 23
    + 732776821500862 * s ^ 22
    - 639230884894128 * s ^ 21
    + 463654314658556 * s ^ 20
    - 276509691049268 * s ^ 19
    + 131003460916885 * s ^ 18
    - 42695044726277 * s ^ 17
    + 775842916864 * s ^ 16
    + 12353935295359 * s ^ 15
    - 11709598957383 * s ^ 14
    + 7279962302849 * s ^ 13
    - 3566942646255 * s ^ 12
    + 1418469849255 * s ^ 11
    - 418730309146 * s ^ 10
    + 64219522020 * s ^ 9
    + 10926022452 * s ^ 8
    - 8973891163 * s ^ 7
    + 1999373460 * s ^ 6
    - 114148089 * s ^ 5
    - 19452180 * s ^ 4
    - 278091 * s ^ 3
    - 29 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient19 (s : ℚ) : ℚ :=
  -7 * s ^ 52
    + 314 * s ^ 51
    - 6860 * s ^ 50
    + 97714 * s ^ 49
    - 1024926 * s ^ 48
    + 8472536 * s ^ 47
    - 57554660 * s ^ 46
    + 329304645 * s ^ 45
    - 1604575690 * s ^ 44
    + 6655525725 * s ^ 43
    - 23242113187 * s ^ 42
    + 66668711515 * s ^ 41
    - 148776075305 * s ^ 40
    + 218935190618 * s ^ 39
    - 16756242555 * s ^ 38
    - 1121525580931 * s ^ 37
    + 4238169929296 * s ^ 36
    - 10049119566955 * s ^ 35
    + 17410206063300 * s ^ 34
    - 21936605960848 * s ^ 33
    + 16811915706337 * s ^ 32
    + 3445851594251 * s ^ 31
    - 39970986526376 * s ^ 30
    + 93951370658142 * s ^ 29
    - 178196029415191 * s ^ 28
    + 320620941303599 * s ^ 27
    - 541862176364523 * s ^ 26
    + 815407074353564 * s ^ 25
    - 1051324568052079 * s ^ 24
    + 1138026063502303 * s ^ 23
    - 1020897373939902 * s ^ 22
    + 747231885384646 * s ^ 21
    - 431499416983049 * s ^ 20
    + 176117814614060 * s ^ 19
    - 21072599692569 * s ^ 18
    - 47953144787960 * s ^ 17
    + 63118203683871 * s ^ 16
    - 51624185486732 * s ^ 15
    + 32627844424472 * s ^ 14
    - 16990761746505 * s ^ 13
    + 7469564078753 * s ^ 12
    - 2646912368200 * s ^ 11
    + 607055931020 * s ^ 10
    + 7684819215 * s ^ 9
    - 73095019238 * s ^ 8
    + 29662130084 * s ^ 7
    - 5169159435 * s ^ 6
    + 135797223 * s ^ 5
    + 65629748 * s ^ 4
    + 1336329 * s ^ 3
    + 403 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient20 (s : ℚ) : ℚ :=
  -s ^ 52
    + 54 * s ^ 51
    - 1348 * s ^ 50
    + 21286 * s ^ 49
    - 244501 * s ^ 48
    + 2227189 * s ^ 47
    - 17081042 * s ^ 46
    + 114447014 * s ^ 45
    - 679174611 * s ^ 44
    + 3554983368 * s ^ 43
    - 16210747167 * s ^ 42
    + 63541991992 * s ^ 41
    - 211434532155 * s ^ 40
    + 589019236205 * s ^ 39
    - 1344942782111 * s ^ 38
    + 2408946474216 * s ^ 37
    - 2981640047492 * s ^ 36
    + 1026380510585 * s ^ 35
    + 6413403379588 * s ^ 34
    - 21311389340358 * s ^ 33
    + 42241086668670 * s ^ 32
    - 65657703371953 * s ^ 31
    + 95293314062131 * s ^ 30
    - 155733776552515 * s ^ 29
    + 292571525638842 * s ^ 28
    - 541160956740716 * s ^ 27
    + 874699726753179 * s ^ 26
    - 1179869041693538 * s ^ 25
    + 1304782812165291 * s ^ 24
    - 1161469028613474 * s ^ 23
    + 798333331939226 * s ^ 22
    - 369720510835550 * s ^ 21
    + 27563992037706 * s ^ 20
    + 163728422313981 * s ^ 19
    - 226277132160067 * s ^ 18
    + 212992284046092 * s ^ 17
    - 165068269928224 * s ^ 16
    + 108281547682366 * s ^ 15
    - 60355892723452 * s ^ 14
    + 28889894237868 * s ^ 13
    - 11649806955156 * s ^ 12
    + 3426906110135 * s ^ 11
    - 278893457488 * s ^ 10
    - 387515757822 * s ^ 9
    + 250433846671 * s ^ 8
    - 75866929905 * s ^ 7
    + 10480170776 * s ^ 6
    + 177599827 * s ^ 5
    - 183595676 * s ^ 4
    - 5274363 * s ^ 3
    - 3573 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient21 (s : ℚ) : ℚ :=
  s ^ 51
    - 24 * s ^ 50
    - 32 * s ^ 49
    + 9134 * s ^ 48
    - 181974 * s ^ 47
    + 2021603 * s ^ 46
    - 14691072 * s ^ 45
    + 68550083 * s ^ 44
    - 134304680 * s ^ 43
    - 860066604 * s ^ 42
    + 10517688450 * s ^ 41
    - 63453938037 * s ^ 40
    + 274989120963 * s ^ 39
    - 932795536521 * s ^ 38
    + 2552655285660 * s ^ 37
    - 5674843065053 * s ^ 36
    + 10134127381177 * s ^ 35
    - 14025731293325 * s ^ 34
    + 13894448867727 * s ^ 33
    - 8916688339799 * s ^ 32
    + 10287179261640 * s ^ 31
    - 50084595242939 * s ^ 30
    + 175111455094944 * s ^ 29
    - 413721592195322 * s ^ 28
    + 728196456451289 * s ^ 27
    - 996304180917432 * s ^ 26
    + 1062436405664017 * s ^ 25
    - 842164658969434 * s ^ 24
    + 398758697770478 * s ^ 23
    + 86727894215306 * s ^ 22
    - 437435610756493 * s ^ 21
    + 586343839212881 * s ^ 20
    - 577814976351647 * s ^ 19
    + 491269009990206 * s ^ 18
    - 378581819242277 * s ^ 17
    + 261795225784866 * s ^ 16
    - 157888125439228 * s ^ 15
    + 82124707217610 * s ^ 14
    - 36555808091264 * s ^ 13
    + 12646658639326 * s ^ 12
    - 1825464376190 * s ^ 11
    - 1503997125796 * s ^ 10
    + 1415911093515 * s ^ 9
    - 622270694728 * s ^ 8
    + 154280165277 * s ^ 7
    - 15817289777 * s ^ 6
    - 1534990419 * s ^ 5
    + 426224963 * s ^ 4
    + 17366250 * s ^ 3
    + 22701 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient22 (s : ℚ) : ℚ :=
  7 * s ^ 50
    - 405 * s ^ 49
    + 10999 * s ^ 48
    - 187701 * s ^ 47
    + 2264911 * s ^ 46
    - 20557261 * s ^ 45
    + 145384197 * s ^ 44
    - 816356561 * s ^ 43
    + 3657254237 * s ^ 42
    - 12894464921 * s ^ 41
    + 33875652033 * s ^ 40
    - 52977982707 * s ^ 39
    - 39225034296 * s ^ 38
    + 624613483802 * s ^ 37
    - 2576368330216 * s ^ 36
    + 7141330092056 * s ^ 35
    - 14630597709683 * s ^ 34
    + 21025047568197 * s ^ 33
    - 13181012340006 * s ^ 32
    - 32858740621903 * s ^ 31
    + 142442014449452 * s ^ 30
    - 317513682750095 * s ^ 29
    + 508095139339635 * s ^ 28
    - 609701925698125 * s ^ 27
    + 511147440735703 * s ^ 26
    - 176159869095873 * s ^ 25
    - 304482669473641 * s ^ 24
    + 750389889549726 * s ^ 23
    - 1005919075313296 * s ^ 22
    + 1036893673347074 * s ^ 21
    - 922663081582928 * s ^ 20
    + 763678690945174 * s ^ 19
    - 606973171439781 * s ^ 18
    + 451865388827376 * s ^ 17
    - 299083328826396 * s ^ 16
    + 169916904193120 * s ^ 15
    - 81847630954200 * s ^ 14
    + 31206446669602 * s ^ 13
    - 5318723071279 * s ^ 12
    - 4905659186563 * s ^ 11
    + 5859477126684 * s ^ 10
    - 3380930565687 * s ^ 9
    + 1208554287387 * s ^ 8
    - 248378155841 * s ^ 7
    + 14331048997 * s ^ 6
    + 5020557880 * s ^ 5
    - 814801493 * s ^ 4
    - 48177403 * s ^ 3
    - 109987 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient23 (s : ℚ) : ℚ :=
  s ^ 50
    - 73 * s ^ 49
    + 2410 * s ^ 48
    - 49063 * s ^ 47
    + 700569 * s ^ 46
    - 7522637 * s ^ 45
    + 63385498 * s ^ 44
    - 430803467 * s ^ 43
    + 2404706447 * s ^ 42
    - 11144867719 * s ^ 41
    + 43070990241 * s ^ 40
    - 138240381679 * s ^ 39
    + 361554390776 * s ^ 38
    - 727491174377 * s ^ 37
    + 899673549945 * s ^ 36
    + 525714418143 * s ^ 35
    - 7126156272737 * s ^ 34
    + 25346249392689 * s ^ 33
    - 62698111265886 * s ^ 32
    + 120856834808722 * s ^ 31
    - 183872452065897 * s ^ 30
    + 209190504938732 * s ^ 29
    - 135951847336271 * s ^ 28
    - 80735192080796 * s ^ 27
    + 424257473001232 * s ^ 26
    - 798296942789477 * s ^ 25
    + 1068045888525922 * s ^ 24
    - 1145469305221685 * s ^ 23
    + 1050720471474314 * s ^ 22
    - 887141187548935 * s ^ 21
    + 748051203569855 * s ^ 20
    - 648119926404821 * s ^ 19
    + 543555456514940 * s ^ 18
    - 404459663588407 * s ^ 17
    + 252206881952254 * s ^ 16
    - 128430048843994 * s ^ 15
    + 49588164477819 * s ^ 14
    - 5716181248665 * s ^ 13
    - 14949474185569 * s ^ 12
    + 18808548528831 * s ^ 11
    - 13190057260332 * s ^ 10
    + 6141045567290 * s ^ 9
    - 1865764471525 * s ^ 8
    + 303595935929 * s ^ 7
    + 4894974895 * s ^ 6
    - 11438125618 * s ^ 5
    + 1254019414 * s ^ 4
    + 113260928 * s ^ 3
    + 421813 * s ^ 2
    + 21 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient24 (s : ℚ) : ℚ :=
  -3 * s ^ 49
    + 180 * s ^ 48
    - 5176 * s ^ 47
    + 95276 * s ^ 46
    - 1263384 * s ^ 45
    + 12865946 * s ^ 44
    - 104708724 * s ^ 43
    + 699580971 * s ^ 42
    - 3911612861 * s ^ 41
    + 18566626199 * s ^ 40
    - 75620664022 * s ^ 39
    + 266371473756 * s ^ 38
    - 815355980208 * s ^ 37
    + 2169966658556 * s ^ 36
    - 4988893204035 * s ^ 35
    + 9714058107340 * s ^ 34
    - 15212933275302 * s ^ 33
    + 16185839722457 * s ^ 32
    - 314298473217 * s ^ 31
    - 51495906078288 * s ^ 30
    + 157162535184215 * s ^ 29
    - 317097002953260 * s ^ 28
    + 498855343749914 * s ^ 27
    - 640161186383031 * s ^ 26
    + 680709452393112 * s ^ 25
    - 608260090997337 * s ^ 24
    + 480084145652113 * s ^ 23
    - 387868111652494 * s ^ 22
    + 383794448083855 * s ^ 21
    - 435155496369472 * s ^ 20
    + 457396992948784 * s ^ 19
    - 394752452560834 * s ^ 18
    + 266111134576218 * s ^ 17
    - 134040009846478 * s ^ 16
    + 40974697076287 * s ^ 15
    + 12860406475227 * s ^ 14
    - 41032946506725 * s ^ 13
    + 48413378140861 * s ^ 12
    - 38632461417565 * s ^ 11
    + 22001175295168 * s ^ 10
    - 8792718111390 * s ^ 9
    + 2253663746827 * s ^ 8
    - 241967989035 * s ^ 7
    - 49755750727 * s ^ 6
    + 20030680313 * s ^ 5
    - 1465870135 * s ^ 4
    - 226148956 * s ^ 3
    - 1310708 * s ^ 2
    - 208 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient25 (s : ℚ) : ℚ :=
  3 * s ^ 48
    - 167 * s ^ 47
    + 4517 * s ^ 46
    - 79026 * s ^ 45
    + 1004168 * s ^ 44
    - 9868036 * s ^ 43
    + 78023191 * s ^ 42
    - 510265290 * s ^ 41
    + 2819102985 * s ^ 40
    - 13388560298 * s ^ 39
    + 55500167925 * s ^ 38
    - 203552467470 * s ^ 37
    + 667964971114 * s ^ 36
    - 1975989593703 * s ^ 35
    + 5281980591831 * s ^ 34
    - 12716129407289 * s ^ 33
    + 27341896127233 * s ^ 32
    - 51859161452078 * s ^ 31
    + 85345175458769 * s ^ 30
    - 119040342083648 * s ^ 29
    + 135167146615339 * s ^ 28
    - 113990375787120 * s ^ 27
    + 49812089798168 * s ^ 26
    + 33390694961088 * s ^ 25
    - 83641635012216 * s ^ 24
    + 50518784870911 * s ^ 23
    + 71376656421532 * s ^ 22
    - 223500341237794 * s ^ 21
    + 317585363777815 * s ^ 20
    - 301633936446296 * s ^ 19
    + 197535460405781 * s ^ 18
    - 73980996420956 * s ^ 17
    - 15694590205112 * s ^ 16
    + 65271583677350 * s ^ 15
    - 91607940837852 * s ^ 14
    + 100219282453121 * s ^ 13
    - 87057111195955 * s ^ 12
    + 57968760732164 * s ^ 11
    - 28603503241801 * s ^ 10
    + 9867110220417 * s ^ 9
    - 1996612611689 * s ^ 8
    + 20240884752 * s ^ 7
    + 113646350021 * s ^ 6
    - 27560689427 * s ^ 5
    + 1064354219 * s ^ 4
    + 383139809 * s ^ 3
    + 3347710 * s ^ 2
    + 1290 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient26 (s : ℚ) : ℚ :=
  -s ^ 47
    + 52 * s ^ 46
    - 1307 * s ^ 45
    + 20980 * s ^ 44
    - 239618 * s ^ 43
    + 2054444 * s ^ 42
    - 13590213 * s ^ 41
    + 70082044 * s ^ 40
    - 280642902 * s ^ 39
    + 860070278 * s ^ 38
    - 2035002117 * s ^ 37
    + 4775545116 * s ^ 36
    - 20742618742 * s ^ 35
    + 125034336731 * s ^ 34
    - 631609091764 * s ^ 33
    + 2485674142512 * s ^ 32
    - 7800064849219 * s ^ 31
    + 19988716659938 * s ^ 30
    - 42431799548018 * s ^ 29
    + 74893519188327 * s ^ 28
    - 108781464401671 * s ^ 27
    + 125168438243141 * s ^ 26
    - 100750441316197 * s ^ 25
    + 23332152287662 * s ^ 24
    + 90887034925968 * s ^ 23
    - 194807759205634 * s ^ 22
    + 234323575446277 * s ^ 21
    - 186535222821490 * s ^ 20
    + 79103791975174 * s ^ 19
    + 31209679524110 * s ^ 18
    - 103524126584542 * s ^ 17
    + 137687957985148 * s ^ 16
    - 155215236314285 * s ^ 15
    + 163790171255978 * s ^ 14
    - 152016386480257 * s ^ 13
    + 114845535402151 * s ^ 12
    - 67123176313315 * s ^ 11
    + 28910944980958 * s ^ 10
    - 8287864598087 * s ^ 9
    + 1007611590314 * s ^ 8
    + 304239504021 * s ^ 7
    - 170530289514 * s ^ 6
    + 29358508360 * s ^ 5
    + 165645548 * s ^ 4
    - 548375026 * s ^ 3
    - 7085706 * s ^ 2
    - 5607 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient27 (s : ℚ) : ℚ :=
  2 * s ^ 45
    - 131 * s ^ 44
    + 4084 * s ^ 43
    - 80669 * s ^ 42
    + 1135947 * s ^ 41
    - 12163907 * s ^ 40
    + 103077291 * s ^ 39
    - 709457841 * s ^ 38
    + 4035406560 * s ^ 37
    - 19186725612 * s ^ 36
    + 76791858738 * s ^ 35
    - 259562010421 * s ^ 34
    + 740316457690 * s ^ 33
    - 1769730993610 * s ^ 32
    + 3481578746217 * s ^ 31
    - 5372837701711 * s ^ 30
    + 5522560852618 * s ^ 29
    - 82404455134 * s ^ 28
    - 15962723972529 * s ^ 27
    + 45859476890171 * s ^ 26
    - 86317077844114 * s ^ 25
    + 123764873195475 * s ^ 24
    - 136714790575731 * s ^ 23
    + 107245888598867 * s ^ 22
    - 36060422642240 * s ^ 21
    - 52646362602349 * s ^ 20
    + 125577666773040 * s ^ 19
    - 164844134997774 * s ^ 18
    + 179659713207947 * s ^ 17
    - 191208434687518 * s ^ 16
    + 205166332131500 * s ^ 15
    - 204469073619433 * s ^ 14
    + 172471299871536 * s ^ 13
    - 116068408506973 * s ^ 12
    + 59592803715983 * s ^ 11
    - 21728510348682 * s ^ 10
    + 4464585163633 * s ^ 9
    + 308838374740 * s ^ 8
    - 576424514827 * s ^ 7
    + 187880591402 * s ^ 6
    - 22657725064 * s ^ 5
    - 1950483573 * s ^ 4
    + 657567562 * s ^ 3
    + 12470731 * s ^ 2
    + 18109 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient28 (s : ℚ) : ℚ :=
  -2 * s ^ 44
    + 123 * s ^ 43
    - 3612 * s ^ 42
    + 67822 * s ^ 41
    - 917800 * s ^ 40
    + 9545417 * s ^ 39
    - 79322027 * s ^ 38
    + 540080568 * s ^ 37
    - 3064797960 * s ^ 36
    + 14672470556 * s ^ 35
    - 59802432981 * s ^ 34
    + 209012582497 * s ^ 33
    - 630144080621 * s ^ 32
    + 1646851931356 * s ^ 31
    - 3744337844965 * s ^ 30
    + 7413848188091 * s ^ 29
    - 12725711553877 * s ^ 28
    + 18619262080166 * s ^ 27
    - 22153986837301 * s ^ 26
    + 18415947184212 * s ^ 25
    - 2133233155096 * s ^ 24
    - 28623943341959 * s ^ 23
    + 68685277130956 * s ^ 22
    - 106275486668606 * s ^ 21
    + 130212231170215 * s ^ 20
    - 139528768577623 * s ^ 19
    + 145926020029103 * s ^ 18
    - 163235684605408 * s ^ 17
    + 190943896675888 * s ^ 16
    - 209376121777118 * s ^ 15
    + 196178033523766 * s ^ 14
    - 148908885432640 * s ^ 13
    + 88112999248268 * s ^ 12
    - 38407582658758 * s ^ 11
    + 10512548868915 * s ^ 10
    - 319159153638 * s ^ 9
    - 1273521251851 * s ^ 8
    + 648160007918 * s ^ 7
    - 152324464008 * s ^ 6
    + 9673287569 * s ^ 5
    + 3524671732 * s ^ 4
    - 651581822 * s ^ 3
    - 18240518 * s ^ 2
    - 44947 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient29 (s : ℚ) : ℚ :=
  s ^ 43
    - 56 * s ^ 42
    + 1542 * s ^ 41
    - 27817 * s ^ 40
    + 368223 * s ^ 39
    - 3789456 * s ^ 38
    + 31345780 * s ^ 37
    - 212884700 * s ^ 36
    + 1205035244 * s ^ 35
    - 5752889978 * s ^ 34
    + 23405328372 * s ^ 33
    - 81976184655 * s ^ 32
    + 249869228699 * s ^ 31
    - 670936736919 * s ^ 30
    + 1608438084783 * s ^ 29
    - 3487360171176 * s ^ 28
    + 6901558726949 * s ^ 27
    - 12490651520752 * s ^ 26
    + 20540419272483 * s ^ 25
    - 30327991953188 * s ^ 24
    + 39767166354154 * s ^ 23
    - 46346824882035 * s ^ 22
    + 49669306947207 * s ^ 21
    - 53892036747176 * s ^ 20
    + 66871993408077 * s ^ 19
    - 94289729965904 * s ^ 18
    + 131810966792937 * s ^ 17
    - 162952339388062 * s ^ 16
    + 168352201640873 * s ^ 15
    - 141097147482143 * s ^ 14
    + 93302494394651 * s ^ 13
    - 46347708884059 * s ^ 12
    + 15054698454677 * s ^ 11
    - 1071778039288 * s ^ 10
    - 2134765841079 * s ^ 9
    + 1461407014202 * s ^ 8
    - 501367332467 * s ^ 7
    + 83819494145 * s ^ 6
    + 3166408215 * s ^ 5
    - 4107375945 * s ^ 4
    + 521629826 * s ^ 3
    + 22078386 * s ^ 2
    + 87429 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient30 (s : ℚ) : ℚ :=
  s ^ 41
    - 68 * s ^ 40
    + 2051 * s ^ 39
    - 37402 * s ^ 38
    + 468593 * s ^ 37
    - 4318786 * s ^ 36
    + 30492836 * s ^ 35
    - 168979973 * s ^ 34
    + 744203670 * s ^ 33
    - 2608504800 * s ^ 32
    + 7183505077 * s ^ 31
    - 14937885988 * s ^ 30
    + 20867650332 * s ^ 29
    - 10225442740 * s ^ 28
    - 31331321782 * s ^ 27
    + 78414310343 * s ^ 26
    - 30451677149 * s ^ 25
    - 186076287942 * s ^ 24
    + 210616457864 * s ^ 23
    + 1395094011084 * s ^ 22
    - 7463891856447 * s ^ 21
    + 21340507984139 * s ^ 20
    - 44411046606547 * s ^ 19
    + 73099376861108 * s ^ 18
    - 98009827351105 * s ^ 17
    + 107761824641729 * s ^ 16
    - 96435958607371 * s ^ 15
    + 68682085291321 * s ^ 14
    - 36937690954006 * s ^ 13
    + 12758747335643 * s ^ 12
    - 329479526773 * s ^ 11
    - 3063548967523 * s ^ 10
    + 2360386234987 * s ^ 9
    - 1020521217335 * s ^ 8
    + 259180251833 * s ^ 7
    - 20443915977 * s ^ 6
    - 10003049146 * s ^ 5
    + 3503014016 * s ^ 4
    - 324140484 * s ^ 3
    - 21932641 * s ^ 2
    - 134642 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient31 (s : ℚ) : ℚ :=
  -s ^ 40
    + 52 * s ^ 39
    - 1270 * s ^ 38
    + 19346 * s ^ 37
    - 205467 * s ^ 36
    + 1606000 * s ^ 35
    - 9448896 * s ^ 34
    + 41506808 * s ^ 33
    - 126884955 * s ^ 32
    + 182808836 * s ^ 31
    + 616275870 * s ^ 30
    - 5646801184 * s ^ 29
    + 23544625706 * s ^ 28
    - 66494497744 * s ^ 27
    + 127852161670 * s ^ 26
    - 113523983273 * s ^ 25
    - 283519542851 * s ^ 24
    + 1714557573934 * s ^ 23
    - 5169622164443 * s ^ 22
    + 11647872506774 * s ^ 21
    - 21421509668235 * s ^ 20
    + 33131212146806 * s ^ 19
    - 43409176387822 * s ^ 18
    + 47896495268746 * s ^ 17
    - 43724315966463 * s ^ 16
    + 31866827692843 * s ^ 15
    - 17047895211357 * s ^ 14
    + 4780002475168 * s ^ 13
    + 1971906465954 * s ^ 12
    - 3709458019762 * s ^ 11
    + 2794552869033 * s ^ 10
    - 1374166304241 * s ^ 9
    + 443420848422 * s ^ 8
    - 68958445603 * s ^ 7
    - 12421715708 * s ^ 6
    + 9825129940 * s ^ 5
    - 2227976526 * s ^ 4
    + 143432310 * s ^ 3
    + 17646955 * s ^ 2
    + 164628 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient32 (s : ℚ) : ℚ :=
  2 * s ^ 38
    - 107 * s ^ 37
    + 2749 * s ^ 36
    - 45235 * s ^ 35
    + 536457 * s ^ 34
    - 4891362 * s ^ 33
    + 35716242 * s ^ 32
    - 214776013 * s ^ 31
    + 1085429498 * s ^ 30
    - 4681648757 * s ^ 29
    + 17444948620 * s ^ 28
    - 56727829101 * s ^ 27
    + 162390709498 * s ^ 26
    - 412371738183 * s ^ 25
    + 934915969479 * s ^ 24
    - 1900886155782 * s ^ 23
    + 3470627694921 * s ^ 22
    - 5671951370909 * s ^ 21
    + 8223888801494 * s ^ 20
    - 10415622862850 * s ^ 19
    + 11243584112232 * s ^ 18
    - 9925335270838 * s ^ 17
    + 6545825979515 * s ^ 16
    - 2253568066459 * s ^ 15
    - 1344911508129 * s ^ 14
    + 3177153702385 * s ^ 13
    - 3236111602537 * s ^ 12
    + 2289828306324 * s ^ 11
    - 1197404381412 * s ^ 10
    + 442002535994 * s ^ 9
    - 88189424452 * s ^ 8
    - 12457120892 * s ^ 7
    + 16692815282 * s ^ 6
    - 6022466154 * s ^ 5
    + 1028880498 * s ^ 4
    - 33551832 * s ^ 3
    - 11270997 * s ^ 2
    - 159189 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient33 (s : ℚ) : ℚ :=
  -s ^ 36
    + 51 * s ^ 35
    - 1252 * s ^ 34
    + 19741 * s ^ 33
    - 225073 * s ^ 32
    + 1980142 * s ^ 31
    - 14002287 * s ^ 30
    + 81789195 * s ^ 29
    - 402049033 * s ^ 28
    + 1683827881 * s ^ 27
    - 6052117860 * s ^ 26
    + 18721883130 * s ^ 25
    - 49774606376 * s ^ 24
    + 113017063149 * s ^ 23
    - 216256953574 * s ^ 22
    + 339585437649 * s ^ 21
    - 411883043550 * s ^ 20
    + 315709560422 * s ^ 19
    + 50304589464 * s ^ 18
    - 671101142945 * s ^ 17
    + 1362969548345 * s ^ 16
    - 1850000859542 * s ^ 15
    + 1935482634685 * s ^ 14
    - 1625617047493 * s ^ 13
    + 1102239656151 * s ^ 12
    - 587838609847 * s ^ 11
    + 224666809964 * s ^ 10
    - 39331801950 * s ^ 9
    - 19482727642 * s ^ 8
    + 20437123540 * s ^ 7
    - 9276991580 * s ^ 6
    + 2447957096 * s ^ 5
    - 316867041 * s ^ 4
    - 6493360 * s ^ 3
    + 5539436 * s ^ 2
    + 120365 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient34 (s : ℚ) : ℚ :=
  2 * s ^ 33
    - 101 * s ^ 32
    + 2447 * s ^ 31
    - 37885 * s ^ 30
    + 421148 * s ^ 29
    - 3580155 * s ^ 28
    + 24198359 * s ^ 27
    - 133456268 * s ^ 26
    + 611423262 * s ^ 25
    - 2356421686 * s ^ 24
    + 7706716168 * s ^ 23
    - 21515041750 * s ^ 22
    + 51458839802 * s ^ 21
    - 105647930399 * s ^ 20
    + 186296823506 * s ^ 19
    - 282041555015 * s ^ 18
    + 366126297317 * s ^ 17
    - 406545978016 * s ^ 16
    + 384214362307 * s ^ 15
    - 305356976104 * s ^ 14
    + 197768194598 * s ^ 13
    - 95027047429 * s ^ 12
    + 21184761291 * s ^ 11
    + 16229088973 * s ^ 10
    - 24471699663 * s ^ 9
    + 17853864914 * s ^ 8
    - 8766970800 * s ^ 7
    + 2953389440 * s ^ 6
    - 617642148 * s ^ 5
    + 48559724 * s ^ 4
    + 9454118 * s ^ 3
    - 1990251 * s ^ 2
    - 69706 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient35 (s : ℚ) : ℚ :=
  -s ^ 30
    + 47 * s ^ 29
    - 1052 * s ^ 28
    + 14920 * s ^ 27
    - 150468 * s ^ 26
    + 1147746 * s ^ 25
    - 6875586 * s ^ 24
    + 33152370 * s ^ 23
    - 130835314 * s ^ 22
    + 427587045 * s ^ 21
    - 1167149939 * s ^ 20
    + 2679497084 * s ^ 19
    - 5210482259 * s ^ 18
    + 8663229385 * s ^ 17
    - 12493736900 * s ^ 16
    + 15961341349 * s ^ 15
    - 18521619032 * s ^ 14
    + 19879302702 * s ^ 13
    - 19690300125 * s ^ 12
    + 17553924195 * s ^ 11
    - 13576420291 * s ^ 10
    + 8767200237 * s ^ 9
    - 4544380486 * s ^ 8
    + 1796839570 * s ^ 7
    - 494483959 * s ^ 6
    + 72318706 * s ^ 5
    + 4345980 * s ^ 4
    - 3969850 * s ^ 3
    + 474064 * s ^ 2
    + 29862 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient36 (s : ℚ) : ℚ :=
  s ^ 26
    - 44 * s ^ 25
    + 915 * s ^ 24
    - 11959 * s ^ 23
    + 110202 * s ^ 22
    - 761367 * s ^ 21
    + 4094290 * s ^ 20
    - 17562297 * s ^ 19
    + 61094650 * s ^ 18
    - 174321100 * s ^ 17
    + 411033315 * s ^ 16
    - 804577982 * s ^ 15
    + 1310231472 * s ^ 14
    - 1774841725 * s ^ 13
    + 1994721582 * s ^ 12
    - 1849255542 * s ^ 11
    + 1398879130 * s ^ 10
    - 846271751 * s ^ 9
    + 393673430 * s ^ 8
    - 128722992 * s ^ 7
    + 21418925 * s ^ 6
    + 3590135 * s ^ 5
    - 3286018 * s ^ 4
    + 831196 * s ^ 3
    - 57550 * s ^ 2
    - 8916 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient37 (s : ℚ) : ℚ :=
  -s ^ 19
    + 33 * s ^ 18
    - 505 * s ^ 17
    + 4756 * s ^ 16
    - 30849 * s ^ 15
    + 146129 * s ^ 14
    - 522997 * s ^ 13
    + 1443239 * s ^ 12
    - 3105932 * s ^ 11
    + 5237558 * s ^ 10
    - 6915149 * s ^ 9
    + 7104941 * s ^ 8
    - 5613414 * s ^ 7
    + 3343064 * s ^ 6
    - 1448651 * s ^ 5
    + 423040 * s ^ 4
    - 65790 * s ^ 3
    - 1128 * s ^ 2
    + 1656 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def denominatorProductCoefficient38 (s : ℚ) : ℚ :=
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
def denominatorProduct (r s : ℚ) : ℚ :=
  denominatorProductCoefficient0 s +
    denominatorProductCoefficient1 s * r +
    denominatorProductCoefficient2 s * r ^ 2 +
    denominatorProductCoefficient3 s * r ^ 3 +
    denominatorProductCoefficient4 s * r ^ 4 +
    denominatorProductCoefficient5 s * r ^ 5 +
    denominatorProductCoefficient6 s * r ^ 6 +
    denominatorProductCoefficient7 s * r ^ 7 +
    denominatorProductCoefficient8 s * r ^ 8 +
    denominatorProductCoefficient9 s * r ^ 9 +
    denominatorProductCoefficient10 s * r ^ 10 +
    denominatorProductCoefficient11 s * r ^ 11 +
    denominatorProductCoefficient12 s * r ^ 12 +
    denominatorProductCoefficient13 s * r ^ 13 +
    denominatorProductCoefficient14 s * r ^ 14 +
    denominatorProductCoefficient15 s * r ^ 15 +
    denominatorProductCoefficient16 s * r ^ 16 +
    denominatorProductCoefficient17 s * r ^ 17 +
    denominatorProductCoefficient18 s * r ^ 18 +
    denominatorProductCoefficient19 s * r ^ 19 +
    denominatorProductCoefficient20 s * r ^ 20 +
    denominatorProductCoefficient21 s * r ^ 21 +
    denominatorProductCoefficient22 s * r ^ 22 +
    denominatorProductCoefficient23 s * r ^ 23 +
    denominatorProductCoefficient24 s * r ^ 24 +
    denominatorProductCoefficient25 s * r ^ 25 +
    denominatorProductCoefficient26 s * r ^ 26 +
    denominatorProductCoefficient27 s * r ^ 27 +
    denominatorProductCoefficient28 s * r ^ 28 +
    denominatorProductCoefficient29 s * r ^ 29 +
    denominatorProductCoefficient30 s * r ^ 30 +
    denominatorProductCoefficient31 s * r ^ 31 +
    denominatorProductCoefficient32 s * r ^ 32 +
    denominatorProductCoefficient33 s * r ^ 33 +
    denominatorProductCoefficient34 s * r ^ 34 +
    denominatorProductCoefficient35 s * r ^ 35 +
    denominatorProductCoefficient36 s * r ^ 36 +
    denominatorProductCoefficient37 s * r ^ 37 +
    denominatorProductCoefficient38 s * r ^ 38

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_0 (s : ℚ) :
    denominatorProductCoefficient0 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient0,
    denominatorStep3Coefficient0,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_1 (s : ℚ) :
    denominatorProductCoefficient1 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient1,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_2 (s : ℚ) :
    denominatorProductCoefficient2 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient2,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_3 (s : ℚ) :
    denominatorProductCoefficient3 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient3,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_4 (s : ℚ) :
    denominatorProductCoefficient4 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient4,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_5 (s : ℚ) :
    denominatorProductCoefficient5 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient5,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_6 (s : ℚ) :
    denominatorProductCoefficient6 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient6,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    rawUnitNineDenominatorCoefficient6,
    rawUnitNineDenominatorCoefficient5,
    rawUnitNineDenominatorCoefficient4,
    rawUnitNineDenominatorCoefficient3,
    rawUnitNineDenominatorCoefficient2,
    rawUnitNineDenominatorCoefficient1,
    rawUnitNineDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_7 (s : ℚ) :
    denominatorProductCoefficient7 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient7,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
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
theorem denominatorProductCoefficient_product_certificate_8 (s : ℚ) :
    denominatorProductCoefficient8 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient8,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
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
theorem denominatorProductCoefficient_product_certificate_9 (s : ℚ) :
    denominatorProductCoefficient9 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient9,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
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
theorem denominatorProductCoefficient_product_certificate_10 (s : ℚ) :
    denominatorProductCoefficient10 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient10,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
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
theorem denominatorProductCoefficient_product_certificate_11 (s : ℚ) :
    denominatorProductCoefficient11 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient11,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
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
theorem denominatorProductCoefficient_product_certificate_12 (s : ℚ) :
    denominatorProductCoefficient12 s =
    denominatorStep3Coefficient0 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient12,
    denominatorStep3Coefficient0,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
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
theorem denominatorProductCoefficient_product_certificate_13 (s : ℚ) :
    denominatorProductCoefficient13 s =
    denominatorStep3Coefficient1 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient13,
    denominatorStep3Coefficient1,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
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
theorem denominatorProductCoefficient_product_certificate_14 (s : ℚ) :
    denominatorProductCoefficient14 s =
    denominatorStep3Coefficient2 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient14,
    denominatorStep3Coefficient2,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
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
theorem denominatorProductCoefficient_product_certificate_15 (s : ℚ) :
    denominatorProductCoefficient15 s =
    denominatorStep3Coefficient3 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient15,
    denominatorStep3Coefficient3,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
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
theorem denominatorProductCoefficient_product_certificate_16 (s : ℚ) :
    denominatorProductCoefficient16 s =
    denominatorStep3Coefficient4 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient16,
    denominatorStep3Coefficient4,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
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
theorem denominatorProductCoefficient_product_certificate_17 (s : ℚ) :
    denominatorProductCoefficient17 s =
    denominatorStep3Coefficient5 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient17,
    denominatorStep3Coefficient5,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
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
theorem denominatorProductCoefficient_product_certificate_18 (s : ℚ) :
    denominatorProductCoefficient18 s =
    denominatorStep3Coefficient6 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient18,
    denominatorStep3Coefficient6,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
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
theorem denominatorProductCoefficient_product_certificate_19 (s : ℚ) :
    denominatorProductCoefficient19 s =
    denominatorStep3Coefficient7 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient19,
    denominatorStep3Coefficient7,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
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
theorem denominatorProductCoefficient_product_certificate_20 (s : ℚ) :
    denominatorProductCoefficient20 s =
    denominatorStep3Coefficient8 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient20,
    denominatorStep3Coefficient8,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
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
theorem denominatorProductCoefficient_product_certificate_21 (s : ℚ) :
    denominatorProductCoefficient21 s =
    denominatorStep3Coefficient9 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient21,
    denominatorStep3Coefficient9,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
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
theorem denominatorProductCoefficient_product_certificate_22 (s : ℚ) :
    denominatorProductCoefficient22 s =
    denominatorStep3Coefficient10 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient22,
    denominatorStep3Coefficient10,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
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
theorem denominatorProductCoefficient_product_certificate_23 (s : ℚ) :
    denominatorProductCoefficient23 s =
    denominatorStep3Coefficient11 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient23,
    denominatorStep3Coefficient11,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
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
theorem denominatorProductCoefficient_product_certificate_24 (s : ℚ) :
    denominatorProductCoefficient24 s =
    denominatorStep3Coefficient12 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient24,
    denominatorStep3Coefficient12,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
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
theorem denominatorProductCoefficient_product_certificate_25 (s : ℚ) :
    denominatorProductCoefficient25 s =
    denominatorStep3Coefficient13 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient25,
    denominatorStep3Coefficient13,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
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
theorem denominatorProductCoefficient_product_certificate_26 (s : ℚ) :
    denominatorProductCoefficient26 s =
    denominatorStep3Coefficient14 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient1 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient0 s
    := by
  simp only [denominatorProductCoefficient26,
    denominatorStep3Coefficient14,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
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
theorem denominatorProductCoefficient_product_certificate_27 (s : ℚ) :
    denominatorProductCoefficient27 s =
    denominatorStep3Coefficient15 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient2 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient1 s
    := by
  simp only [denominatorProductCoefficient27,
    denominatorStep3Coefficient15,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
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
theorem denominatorProductCoefficient_product_certificate_28 (s : ℚ) :
    denominatorProductCoefficient28 s =
    denominatorStep3Coefficient16 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient3 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient2 s
    := by
  simp only [denominatorProductCoefficient28,
    denominatorStep3Coefficient16,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
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
theorem denominatorProductCoefficient_product_certificate_29 (s : ℚ) :
    denominatorProductCoefficient29 s =
    denominatorStep3Coefficient17 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient4 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient3 s
    := by
  simp only [denominatorProductCoefficient29,
    denominatorStep3Coefficient17,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
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
theorem denominatorProductCoefficient_product_certificate_30 (s : ℚ) :
    denominatorProductCoefficient30 s =
    denominatorStep3Coefficient18 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient5 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient4 s
    := by
  simp only [denominatorProductCoefficient30,
    denominatorStep3Coefficient18,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
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
theorem denominatorProductCoefficient_product_certificate_31 (s : ℚ) :
    denominatorProductCoefficient31 s =
    denominatorStep3Coefficient19 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient6 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient5 s
    := by
  simp only [denominatorProductCoefficient31,
    denominatorStep3Coefficient19,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
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
theorem denominatorProductCoefficient_product_certificate_32 (s : ℚ) :
    denominatorProductCoefficient32 s =
    denominatorStep3Coefficient20 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient7 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient6 s
    := by
  simp only [denominatorProductCoefficient32,
    denominatorStep3Coefficient20,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7,
    rawUnitNineDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_33 (s : ℚ) :
    denominatorProductCoefficient33 s =
    denominatorStep3Coefficient21 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient8 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient7 s
    := by
  simp only [denominatorProductCoefficient33,
    denominatorStep3Coefficient21,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8,
    rawUnitNineDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_34 (s : ℚ) :
    denominatorProductCoefficient34 s =
    denominatorStep3Coefficient22 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient9 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient8 s
    := by
  simp only [denominatorProductCoefficient34,
    denominatorStep3Coefficient22,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9,
    rawUnitNineDenominatorCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_35 (s : ℚ) :
    denominatorProductCoefficient35 s =
    denominatorStep3Coefficient23 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient10 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient9 s
    := by
  simp only [denominatorProductCoefficient35,
    denominatorStep3Coefficient23,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10,
    rawUnitNineDenominatorCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_36 (s : ℚ) :
    denominatorProductCoefficient36 s =
    denominatorStep3Coefficient24 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient11 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient10 s
    := by
  simp only [denominatorProductCoefficient36,
    denominatorStep3Coefficient24,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11,
    rawUnitNineDenominatorCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_37 (s : ℚ) :
    denominatorProductCoefficient37 s =
    denominatorStep3Coefficient25 s *
        rawUnitNineDenominatorCoefficient12 s
      + denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient11 s
    := by
  simp only [denominatorProductCoefficient37,
    denominatorStep3Coefficient25,
    denominatorStep3Coefficient26,
    rawUnitNineDenominatorCoefficient12,
    rawUnitNineDenominatorCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem denominatorProductCoefficient_product_certificate_38 (s : ℚ) :
    denominatorProductCoefficient38 s =
    denominatorStep3Coefficient26 s *
        rawUnitNineDenominatorCoefficient12 s
    := by
  simp only [denominatorProductCoefficient38,
    denominatorStep3Coefficient26,
    rawUnitNineDenominatorCoefficient12]
  ring

/-- Checked staged polynomial-product identity. -/
theorem denominatorProduct_eq_denominatorStep3_mul_rawUnitNineDenominator (r s : ℚ) :
    denominatorProduct r s = denominatorStep3 r s * rawUnitNineDenominator r s := by
  have h0 := denominatorProductCoefficient_product_certificate_0 s
  have h1 := denominatorProductCoefficient_product_certificate_1 s
  have h2 := denominatorProductCoefficient_product_certificate_2 s
  have h3 := denominatorProductCoefficient_product_certificate_3 s
  have h4 := denominatorProductCoefficient_product_certificate_4 s
  have h5 := denominatorProductCoefficient_product_certificate_5 s
  have h6 := denominatorProductCoefficient_product_certificate_6 s
  have h7 := denominatorProductCoefficient_product_certificate_7 s
  have h8 := denominatorProductCoefficient_product_certificate_8 s
  have h9 := denominatorProductCoefficient_product_certificate_9 s
  have h10 := denominatorProductCoefficient_product_certificate_10 s
  have h11 := denominatorProductCoefficient_product_certificate_11 s
  have h12 := denominatorProductCoefficient_product_certificate_12 s
  have h13 := denominatorProductCoefficient_product_certificate_13 s
  have h14 := denominatorProductCoefficient_product_certificate_14 s
  have h15 := denominatorProductCoefficient_product_certificate_15 s
  have h16 := denominatorProductCoefficient_product_certificate_16 s
  have h17 := denominatorProductCoefficient_product_certificate_17 s
  have h18 := denominatorProductCoefficient_product_certificate_18 s
  have h19 := denominatorProductCoefficient_product_certificate_19 s
  have h20 := denominatorProductCoefficient_product_certificate_20 s
  have h21 := denominatorProductCoefficient_product_certificate_21 s
  have h22 := denominatorProductCoefficient_product_certificate_22 s
  have h23 := denominatorProductCoefficient_product_certificate_23 s
  have h24 := denominatorProductCoefficient_product_certificate_24 s
  have h25 := denominatorProductCoefficient_product_certificate_25 s
  have h26 := denominatorProductCoefficient_product_certificate_26 s
  have h27 := denominatorProductCoefficient_product_certificate_27 s
  have h28 := denominatorProductCoefficient_product_certificate_28 s
  have h29 := denominatorProductCoefficient_product_certificate_29 s
  have h30 := denominatorProductCoefficient_product_certificate_30 s
  have h31 := denominatorProductCoefficient_product_certificate_31 s
  have h32 := denominatorProductCoefficient_product_certificate_32 s
  have h33 := denominatorProductCoefficient_product_certificate_33 s
  have h34 := denominatorProductCoefficient_product_certificate_34 s
  have h35 := denominatorProductCoefficient_product_certificate_35 s
  have h36 := denominatorProductCoefficient_product_certificate_36 s
  have h37 := denominatorProductCoefficient_product_certificate_37 s
  have h38 := denominatorProductCoefficient_product_certificate_38 s
  simp only [denominatorProduct, denominatorStep3, rawUnitNineDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 + r ^ 36 * h36 + r ^ 37 * h37 +
    r ^ 38 * h38

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient1 (s : ℚ) : ℚ :=
  s ^ 35
    - 4 * s ^ 34
    + 10 * s ^ 33
    - 18 * s ^ 32
    + 25 * s ^ 31
    - 28 * s ^ 30
    + 25 * s ^ 29
    - 18 * s ^ 28
    + 10 * s ^ 27
    - 4 * s ^ 26
    + s ^ 25

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 41
    + 7 * s ^ 40
    - 27 * s ^ 39
    + 75 * s ^ 38
    - 169 * s ^ 37
    + 333 * s ^ 36
    - 586 * s ^ 35
    + 869 * s ^ 34
    - 1051 * s ^ 33
    + 932 * s ^ 32
    - 396 * s ^ 31
    - 472 * s ^ 30
    + 1402 * s ^ 29
    - 2028 * s ^ 28
    + 2171 * s ^ 27
    - 1865 * s ^ 26
    + 1332 * s ^ 25
    - 812 * s ^ 24
    + 427 * s ^ 23
    - 202 * s ^ 22
    + 83 * s ^ 21
    - 28 * s ^ 20
    + 7 * s ^ 19
    - s ^ 18

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient3 (s : ℚ) : ℚ :=
  s ^ 43
    - 11 * s ^ 42
    + 52 * s ^ 41
    - 108 * s ^ 40
    - 4 * s ^ 39
    + 781 * s ^ 38
    - 3092 * s ^ 37
    + 8274 * s ^ 36
    - 18566 * s ^ 35
    + 37046 * s ^ 34
    - 65238 * s ^ 33
    + 100932 * s ^ 32
    - 135726 * s ^ 31
    + 157701 * s ^ 30
    - 157235 * s ^ 29
    + 132546 * s ^ 28
    - 92479 * s ^ 27
    + 50216 * s ^ 26
    - 17332 * s ^ 25
    - 1615 * s ^ 24
    + 8784 * s ^ 23
    - 8937 * s ^ 22
    + 6625 * s ^ 21
    - 4032 * s ^ 20
    + 2045 * s ^ 19
    - 847 * s ^ 18
    + 274 * s ^ 17
    - 65 * s ^ 16
    + 11 * s ^ 15
    - s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 46
    + 13 * s ^ 45
    - 89 * s ^ 44
    + 438 * s ^ 43
    - 1797 * s ^ 42
    + 6467 * s ^ 41
    - 20061 * s ^ 40
    + 52311 * s ^ 39
    - 115922 * s ^ 38
    + 224952 * s ^ 37
    - 395126 * s ^ 36
    + 638914 * s ^ 35
    - 939022 * s ^ 34
    + 1212558 * s ^ 33
    - 1313884 * s ^ 32
    + 1079934 * s ^ 31
    - 442671 * s ^ 30
    - 494341 * s ^ 29
    + 1467025 * s ^ 28
    - 2165037 * s ^ 27
    + 2407449 * s ^ 26
    - 2202208 * s ^ 25
    + 1720101 * s ^ 24
    - 1172361 * s ^ 23
    + 706105 * s ^ 22
    - 378944 * s ^ 21
    + 176958 * s ^ 20
    - 67734 * s ^ 19
    + 18290 * s ^ 18
    - 1361 * s ^ 17
    - 1765 * s ^ 16
    + 1130 * s ^ 15
    - 401 * s ^ 14
    + 92 * s ^ 13
    - 13 * s ^ 12
    + s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient5 (s : ℚ) : ℚ :=
  s ^ 48
    - 17 * s ^ 47
    + 144 * s ^ 46
    - 799 * s ^ 45
    + 3330 * s ^ 44
    - 11326 * s ^ 43
    + 32630 * s ^ 42
    - 78789 * s ^ 41
    + 152356 * s ^ 40
    - 219179 * s ^ 39
    + 192904 * s ^ 38
    + 55710 * s ^ 37
    - 730009 * s ^ 36
    + 2296659 * s ^ 35
    - 5734343 * s ^ 34
    + 12384912 * s ^ 33
    - 23163624 * s ^ 32
    + 37517543 * s ^ 31
    - 52671567 * s ^ 30
    + 64328683 * s ^ 29
    - 68505901 * s ^ 28
    + 63655133 * s ^ 27
    - 51605675 * s ^ 26
    + 36323334 * s ^ 25
    - 21994809 * s ^ 24
    + 11172840 * s ^ 23
    - 4368108 * s ^ 22
    + 790412 * s ^ 21
    + 733709 * s ^ 20
    - 1086565 * s ^ 19
    + 883677 * s ^ 18
    - 533034 * s ^ 17
    + 249834 * s ^ 16
    - 91021 * s ^ 15
    + 25503 * s ^ 14
    - 5187 * s ^ 13
    + 685 * s ^ 12
    - 45 * s ^ 11
    - s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient6 (s : ℚ) : ℚ :=
  s ^ 49
    - 13 * s ^ 48
    + 50 * s ^ 47
    + 193 * s ^ 46
    - 3338 * s ^ 45
    + 21515 * s ^ 44
    - 96588 * s ^ 43
    + 350755 * s ^ 42
    - 1090258 * s ^ 41
    + 2938234 * s ^ 40
    - 6880792 * s ^ 39
    + 14256481 * s ^ 38
    - 27259072 * s ^ 37
    + 50438354 * s ^ 36
    - 92043956 * s ^ 35
    + 161812785 * s ^ 34
    - 263255692 * s ^ 33
    + 384566270 * s ^ 32
    - 495423667 * s ^ 31
    + 554933292 * s ^ 30
    - 531531443 * s ^ 29
    + 421552501 * s ^ 28
    - 255085304 * s ^ 27
    + 81913445 * s ^ 26
    + 53854917 * s ^ 25
    - 130648122 * s ^ 24
    + 153209816 * s ^ 23
    - 140712473 * s ^ 22
    + 112633820 * s ^ 21
    - 81564581 * s ^ 20
    + 53151781 * s ^ 19
    - 30438955 * s ^ 18
    + 14864621 * s ^ 17
    - 5981953 * s ^ 16
    + 1905235 * s ^ 15
    - 451468 * s ^ 14
    + 66159 * s ^ 13
    - 961 * s ^ 12
    - 2011 * s ^ 11
    + 459 * s ^ 10
    - 39 * s ^ 9
    + 2 * s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 50
    + 27 * s ^ 49
    - 359 * s ^ 48
    + 2953 * s ^ 47
    - 16822 * s ^ 46
    + 71991 * s ^ 45
    - 248082 * s ^ 44
    + 731628 * s ^ 43
    - 1921723 * s ^ 42
    + 4562045 * s ^ 41
    - 9955621 * s ^ 40
    + 21238549 * s ^ 39
    - 48222413 * s ^ 38
    + 116058175 * s ^ 37
    - 267835498 * s ^ 36
    + 543001113 * s ^ 35
    - 925831355 * s ^ 34
    + 1295220604 * s ^ 33
    - 1428432432 * s ^ 32
    + 1082945602 * s ^ 31
    - 133319638 * s ^ 30
    - 1310009392 * s ^ 29
    + 2903594988 * s ^ 28
    - 4208094542 * s ^ 27
    + 4897598830 * s ^ 26
    - 4897035298 * s ^ 25
    + 4362367531 * s ^ 24
    - 3560667202 * s ^ 23
    + 2718776335 * s ^ 22
    - 1957443542 * s ^ 21
    + 1314530057 * s ^ 20
    - 799366863 * s ^ 19
    + 424620185 * s ^ 18
    - 189352705 * s ^ 17
    + 67299498 * s ^ 16
    - 17352288 * s ^ 15
    + 2333284 * s ^ 14
    + 398338 * s ^ 13
    - 324141 * s ^ 12
    + 91374 * s ^ 11
    - 14146 * s ^ 10
    + 973 * s ^ 9
    - 13 * s ^ 8
    - 4 * s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 51
    + 22 * s ^ 50
    - 219 * s ^ 49
    + 1205 * s ^ 48
    - 3110 * s ^ 47
    - 4719 * s ^ 46
    + 77121 * s ^ 45
    - 349092 * s ^ 44
    + 932223 * s ^ 43
    - 1291184 * s ^ 42
    - 2022512 * s ^ 41
    + 22357339 * s ^ 40
    - 97832939 * s ^ 39
    + 302877176 * s ^ 38
    - 710382713 * s ^ 37
    + 1246214926 * s ^ 36
    - 1460956527 * s ^ 35
    + 399087990 * s ^ 34
    + 3193520749 * s ^ 33
    - 10278523304 * s ^ 32
    + 20806984031 * s ^ 31
    - 33284416486 * s ^ 30
    + 45030740684 * s ^ 29
    - 53216044781 * s ^ 28
    + 56103334255 * s ^ 27
    - 53775402244 * s ^ 26
    + 47804716342 * s ^ 25
    - 40206706861 * s ^ 24
    + 32483042928 * s ^ 23
    - 25220637458 * s ^ 22
    + 18476284796 * s ^ 21
    - 12355546746 * s ^ 20
    + 7243570798 * s ^ 19
    - 3564527910 * s ^ 18
    + 1383969176 * s ^ 17
    - 367776453 * s ^ 16
    + 26697049 * s ^ 15
    + 33475865 * s ^ 14
    - 21344810 * s ^ 13
    + 7249149 * s ^ 12
    - 1545148 * s ^ 11
    + 187778 * s ^ 10
    - 5358 * s ^ 9
    - 1174 * s ^ 8
    + 145 * s ^ 7
    + 2 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient9 (s : ℚ) : ℚ :=
  -2 * s ^ 51
    + 63 * s ^ 50
    - 843 * s ^ 49
    + 6410 * s ^ 48
    - 28910 * s ^ 47
    + 57357 * s ^ 46
    + 194193 * s ^ 45
    - 2216170 * s ^ 44
    + 10971617 * s ^ 43
    - 39087654 * s ^ 42
    + 111852447 * s ^ 41
    - 258669555 * s ^ 40
    + 430140794 * s ^ 39
    - 212362938 * s ^ 38
    - 1744780786 * s ^ 37
    + 8334891249 * s ^ 36
    - 23926650252 * s ^ 35
    + 52935905488 * s ^ 34
    - 97243361511 * s ^ 33
    + 153816292536 * s ^ 32
    - 214137626634 * s ^ 31
    + 266372066793 * s ^ 30
    - 300037402380 * s ^ 29
    + 310876839763 * s ^ 28
    - 302496806248 * s ^ 27
    + 283383996023 * s ^ 26
    - 260935245676 * s ^ 25
    + 237196259901 * s ^ 24
    - 209182868370 * s ^ 23
    + 173027113000 * s ^ 22
    - 129131423901 * s ^ 21
    + 83557215346 * s ^ 20
    - 44737646732 * s ^ 19
    + 18335623286 * s ^ 18
    - 4502224795 * s ^ 17
    - 544930146 * s ^ 16
    + 1296207826 * s ^ 15
    - 793172477 * s ^ 14
    + 311804562 * s ^ 13
    - 84361854 * s ^ 12
    + 14634637 * s ^ 11
    - 1112838 * s ^ 10
    - 122606 * s ^ 9
    + 32336 * s ^ 8
    - 2254 * s ^ 7
    - 95 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient10 (s : ℚ) : ℚ :=
  -5 * s ^ 51
    + 182 * s ^ 50
    - 3016 * s ^ 49
    + 30057 * s ^ 48
    - 200771 * s ^ 47
    + 934583 * s ^ 46
    - 2946961 * s ^ 45
    + 4818112 * s ^ 44
    + 9553081 * s ^ 43
    - 115943335 * s ^ 42
    + 590625236 * s ^ 41
    - 2296046633 * s ^ 40
    + 7515074825 * s ^ 39
    - 21171511826 * s ^ 38
    + 51535463238 * s ^ 37
    - 108691971268 * s ^ 36
    + 199795887005 * s ^ 35
    - 322944441054 * s ^ 34
    + 464023867910 * s ^ 33
    - 600079452953 * s ^ 32
    + 709020502774 * s ^ 31
    - 782232051366 * s ^ 30
    + 833351968308 * s ^ 29
    - 893657828891 * s ^ 28
    + 991135230127 * s ^ 27
    - 1124501910653 * s ^ 26
    + 1251161101463 * s ^ 25
    - 1303412276429 * s ^ 24
    + 1225293242064 * s ^ 23
    - 1008439261284 * s ^ 22
    + 703849636312 * s ^ 21
    - 396482900543 * s ^ 20
    + 160301110859 * s ^ 19
    - 24632223562 * s ^ 18
    - 26799944797 * s ^ 17
    + 30718518888 * s ^ 16
    - 19059808461 * s ^ 15
    + 8396556082 * s ^ 14
    - 2718436804 * s ^ 13
    + 610367144 * s ^ 12
    - 74780837 * s ^ 11
    - 3129184 * s ^ 10
    + 2996268 * s ^ 9
    - 433724 * s ^ 8
    + 17731 * s ^ 7
    + 2105 * s ^ 6
    + 3 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient11 (s : ℚ) : ℚ :=
  -11 * s ^ 51
    + 463 * s ^ 50
    - 9119 * s ^ 49
    + 112036 * s ^ 48
    - 969161 * s ^ 47
    + 6340613 * s ^ 46
    - 33042693 * s ^ 45
    + 143368073 * s ^ 44
    - 539068871 * s ^ 43
    + 1812540656 * s ^ 42
    - 5532929318 * s ^ 41
    + 15284651944 * s ^ 40
    - 37662507171 * s ^ 39
    + 81464519929 * s ^ 38
    - 152858849878 * s ^ 37
    + 247267388762 * s ^ 36
    - 344711723687 * s ^ 35
    + 417893255494 * s ^ 34
    - 455353370505 * s ^ 33
    + 490226940337 * s ^ 32
    - 618931241681 * s ^ 31
    + 993615150761 * s ^ 30
    - 1770098379443 * s ^ 29
    + 3008132714813 * s ^ 28
    - 4568674025952 * s ^ 27
    + 6086909944458 * s ^ 26
    - 7074868852275 * s ^ 25
    + 7131319550918 * s ^ 24
    - 6149793853727 * s ^ 23
    + 4404364847788 * s ^ 22
    - 2440639624249 * s ^ 21
    + 811309421529 * s ^ 20
    + 174511495787 * s ^ 19
    - 533736275814 * s ^ 18
    + 496096757749 * s ^ 17
    - 315939019841 * s ^ 16
    + 152696018074 * s ^ 15
    - 56595251774 * s ^ 14
    + 15348860862 * s ^ 13
    - 2534164614 * s ^ 12
    + 2229792 * s ^ 11
    + 127509629 * s ^ 10
    - 33958286 * s ^ 9
    + 3539254 * s ^ 8
    - 10648 * s ^ 7
    - 30979 * s ^ 6
    - 21 * s ^ 5
    - 3 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient12 (s : ℚ) : ℚ :=
  s ^ 53
    - 39 * s ^ 52
    + 760 * s ^ 51
    - 9676 * s ^ 50
    + 89104 * s ^ 49
    - 627048 * s ^ 48
    + 3511029 * s ^ 47
    - 16267469 * s ^ 46
    + 65121311 * s ^ 45
    - 234729500 * s ^ 44
    + 777470170 * s ^ 43
    - 2328063507 * s ^ 42
    + 6004259905 * s ^ 41
    - 12362987534 * s ^ 40
    + 17295562724 * s ^ 39
    - 4515552067 * s ^ 38
    - 58773330570 * s ^ 37
    + 207653481951 * s ^ 36
    - 433675094931 * s ^ 35
    + 615827054841 * s ^ 34
    - 461907353200 * s ^ 33
    - 499873875943 * s ^ 32
    + 2845223416195 * s ^ 31
    - 7056689953440 * s ^ 30
    + 13192600150373 * s ^ 29
    - 20537590552617 * s ^ 28
    + 27497820477927 * s ^ 27
    - 31964249921693 * s ^ 26
    + 32116684085913 * s ^ 25
    - 27329586809003 * s ^ 24
    + 18671393252860 * s ^ 23
    - 8628676339157 * s ^ 22
    + 50274491414 * s ^ 21
    + 5147501502322 * s ^ 20
    - 6694057344249 * s ^ 19
    + 5700584517289 * s ^ 18
    - 3729929170989 * s ^ 17
    + 1942288355385 * s ^ 16
    - 799784205106 * s ^ 15
    + 248505332953 * s ^ 14
    - 49592719228 * s ^ 13
    + 1031904441 * s ^ 12
    + 3395214961 * s ^ 11
    - 1308150070 * s ^ 10
    + 241034289 * s ^ 9
    - 15979185 * s ^ 8
    - 1588510 * s ^ 7
    + 336660 * s ^ 6
    - 91 * s ^ 5
    + 42 * s ^ 4
    + 2 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient13 (s : ℚ) : ℚ :=
  -s ^ 53
    + 26 * s ^ 52
    - 276 * s ^ 51
    + 947 * s ^ 50
    + 11089 * s ^ 49
    - 188016 * s ^ 48
    + 1484657 * s ^ 47
    - 7983341 * s ^ 46
    + 33897552 * s ^ 45
    - 134340964 * s ^ 44
    + 577970398 * s ^ 43
    - 2617683797 * s ^ 42
    + 10847965583 * s ^ 41
    - 37628546594 * s ^ 40
    + 105441811291 * s ^ 39
    - 232822272132 * s ^ 38
    + 381777483597 * s ^ 37
    - 357291542778 * s ^ 36
    - 312781654022 * s ^ 35
    + 2456454357811 * s ^ 34
    - 7234957494765 * s ^ 33
    + 15958232422243 * s ^ 32
    - 29631615250089 * s ^ 31
    + 48141616896860 * s ^ 30
    - 69281685845733 * s ^ 29
    + 88296493769382 * s ^ 28
    - 98713003924516 * s ^ 27
    + 94613732652541 * s ^ 26
    - 73578750979522 * s ^ 25
    + 38812391695433 * s ^ 24
    + 1046040231230 * s ^ 23
    - 34985315170924 * s ^ 22
    + 54438176309774 * s ^ 21
    - 57060434119414 * s ^ 20
    + 46986588717999 * s ^ 19
    - 31631053123955 * s ^ 18
    + 17504862013166 * s ^ 17
    - 7822781007476 * s ^ 16
    + 2675513488815 * s ^ 15
    - 588592100268 * s ^ 14
    + 1827138759 * s ^ 13
    + 64896249048 * s ^ 12
    - 30970255621 * s ^ 11
    + 7985013797 * s ^ 10
    - 1064223663 * s ^ 9
    - 3553304 * s ^ 8
    + 22412312 * s ^ 7
    - 2723931 * s ^ 6
    - 9700 * s ^ 5
    + 566 * s ^ 4
    - 74 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient14 (s : ℚ) : ℚ :=
  -s ^ 53
    + 41 * s ^ 52
    - 742 * s ^ 51
    + 8015 * s ^ 50
    - 58250 * s ^ 49
    + 313340 * s ^ 48
    - 1506846 * s ^ 47
    + 8640488 * s ^ 46
    - 58279142 * s ^ 45
    + 355616218 * s ^ 44
    - 1712479897 * s ^ 43
    + 6207352135 * s ^ 42
    - 15836712796 * s ^ 41
    + 20636194677 * s ^ 40
    + 41545700407 * s ^ 39
    - 372930609933 * s ^ 38
    + 1448939830089 * s ^ 37
    - 4155127700614 * s ^ 36
    + 9867999220648 * s ^ 35
    - 20428468329238 * s ^ 34
    + 37897944821282 * s ^ 33
    - 63800464040284 * s ^ 32
    + 97508551296773 * s ^ 31
    - 134020595262508 * s ^ 30
    + 162530039435083 * s ^ 29
    - 167761848170283 * s ^ 28
    + 134990134508129 * s ^ 27
    - 57487128992709 * s ^ 26
    - 56843381249974 * s ^ 25
    + 183873105035739 * s ^ 24
    - 289757965652881 * s ^ 23
    + 344544997875580 * s ^ 22
    - 336267888057983 * s ^ 21
    + 276304000439798 * s ^ 20
    - 191986790175669 * s ^ 19
    + 111785810207572 * s ^ 18
    - 53094056071598 * s ^ 17
    + 19214758486042 * s ^ 16
    - 4165710664511 * s ^ 15
    - 447520105933 * s ^ 14
    + 936841364839 * s ^ 13
    - 494988074044 * s ^ 12
    + 158890347791 * s ^ 11
    - 30741396242 * s ^ 10
    + 1954411932 * s ^ 9
    + 656033980 * s ^ 8
    - 179577228 * s ^ 7
    + 15725100 * s ^ 6
    + 324239 * s ^ 5
    - 21914 * s ^ 4
    + 1282 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient15 (s : ℚ) : ℚ :=
  8 * s ^ 52
    - 235 * s ^ 51
    + 2726 * s ^ 50
    - 10088 * s ^ 49
    - 120550 * s ^ 48
    + 2090507 * s ^ 47
    - 15594929 * s ^ 46
    + 62573931 * s ^ 45
    - 26960394 * s ^ 44
    - 1550984916 * s ^ 43
    + 13009433284 * s ^ 42
    - 67396265709 * s ^ 41
    + 264881051815 * s ^ 40
    - 847773771401 * s ^ 39
    + 2298225790322 * s ^ 38
    - 5433228733581 * s ^ 37
    + 11483348332908 * s ^ 36
    - 22132147184036 * s ^ 35
    + 39300098416226 * s ^ 34
    - 64046754338442 * s ^ 33
    + 93846747045464 * s ^ 32
    - 118516421406991 * s ^ 31
    + 117181744776649 * s ^ 30
    - 60086287447359 * s ^ 29
    - 82293028125242 * s ^ 28
    + 324081640968220 * s ^ 27
    - 648109917959737 * s ^ 26
    + 997931212932472 * s ^ 25
    - 1287162372625775 * s ^ 24
    + 1429374846440319 * s ^ 23
    - 1377821568914348 * s ^ 22
    + 1151469214137525 * s ^ 21
    - 827256143072862 * s ^ 20
    + 501665128129937 * s ^ 19
    - 247038293016953 * s ^ 18
    + 89247527614519 * s ^ 17
    - 14325070105193 * s ^ 16
    - 9206969113075 * s ^ 15
    + 10135681070440 * s ^ 14
    - 5578657326109 * s ^ 13
    + 2077437007933 * s ^ 12
    - 511697945488 * s ^ 11
    + 59634102442 * s ^ 10
    + 9480417709 * s ^ 9
    - 5502110293 * s ^ 8
    + 962401947 * s ^ 7
    - 57344052 * s ^ 6
    - 4537637 * s ^ 5
    + 291005 * s ^ 4
    - 12836 * s ^ 3
    - 78 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient16 (s : ℚ) : ℚ :=
  5 * s ^ 52
    - 174 * s ^ 51
    + 2034 * s ^ 50
    + 4098 * s ^ 49
    - 448541 * s ^ 48
    + 7252049 * s ^ 47
    - 72153786 * s ^ 46
    + 524031973 * s ^ 45
    - 2968037910 * s ^ 44
    + 13578863829 * s ^ 43
    - 51315142057 * s ^ 42
    + 162902398516 * s ^ 41
    - 441353944976 * s ^ 40
    + 1039807335617 * s ^ 39
    - 2182723304249 * s ^ 38
    + 4196042489779 * s ^ 37
    - 7505748332691 * s ^ 36
    + 12211459813459 * s ^ 35
    - 16285063094005 * s ^ 34
    + 11387310726249 * s ^ 33
    + 23216182134908 * s ^ 32
    - 125218658054520 * s ^ 31
    + 346730562646172 * s ^ 30
    - 740254086116417 * s ^ 29
    + 1333292480432473 * s ^ 28
    - 2097521959869927 * s ^ 27
    + 2925556141800692 * s ^ 26
    - 3635502913750735 * s ^ 25
    + 4020350195787077 * s ^ 24
    - 3934679261627390 * s ^ 23
    + 3375218784312639 * s ^ 22
    - 2498024002015183 * s ^ 21
    + 1550329120973387 * s ^ 20
    - 757431761699199 * s ^ 19
    + 236058480838657 * s ^ 18
    + 20286630377334 * s ^ 17
    - 94024316078743 * s ^ 16
    + 80147252369327 * s ^ 15
    - 45170654875220 * s ^ 14
    + 18660275557977 * s ^ 13
    - 5437226402643 * s ^ 12
    + 861390592156 * s ^ 11
    + 87288614433 * s ^ 10
    - 95903806007 * s ^ 9
    + 26950744251 * s ^ 8
    - 3478662683 * s ^ 7
    + 61193952 * s ^ 6
    + 38292661 * s ^ 5
    - 2245669 * s ^ 4
    + 75224 * s ^ 3
    + 1826 * s ^ 2
    - 29 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient17 (s : ℚ) : ℚ :=
  -s ^ 53
    + 57 * s ^ 52
    - 1589 * s ^ 51
    + 28180 * s ^ 50
    - 352624 * s ^ 49
    + 3290898 * s ^ 48
    - 23656931 * s ^ 47
    + 133186236 * s ^ 46
    - 588172053 * s ^ 45
    + 1994920723 * s ^ 44
    - 4800893776 * s ^ 43
    + 5479381676 * s ^ 42
    + 15750801145 * s ^ 41
    - 119649257758 * s ^ 40
    + 442692031657 * s ^ 39
    - 1260949150321 * s ^ 38
    + 3259191519220 * s ^ 37
    - 8590058108487 * s ^ 36
    + 23803966401393 * s ^ 35
    - 65575616565365 * s ^ 34
    + 168433035862560 * s ^ 33
    - 390618672262523 * s ^ 32
    + 811801231154057 * s ^ 31
    - 1516695247429124 * s ^ 30
    + 2561555695078111 * s ^ 29
    - 3925581450632858 * s ^ 28
    + 5460317037227404 * s ^ 27
    - 6869387000948955 * s ^ 26
    + 7761932989685583 * s ^ 25
    - 7795220375410030 * s ^ 24
    + 6852172234632038 * s ^ 23
    - 5141287905115475 * s ^ 22
    + 3130384826236863 * s ^ 21
    - 1337492589303503 * s ^ 20
    + 108696681251038 * s ^ 19
    + 484959481322918 * s ^ 18
    - 594981686228879 * s ^ 17
    + 456434767633080 * s ^ 16
    - 263798879832398 * s ^ 15
    + 117771604443569 * s ^ 14
    - 38566197737931 * s ^ 13
    + 7235774932910 * s ^ 12
    + 730728775758 * s ^ 11
    - 1124458309384 * s ^ 10
    + 431294719661 * s ^ 9
    - 88355983486 * s ^ 8
    + 7416675591 * s ^ 7
    + 702457875 * s ^ 6
    - 219169567 * s ^ 5
    + 11094320 * s ^ 4
    - 199786 * s ^ 3
    - 22070 * s ^ 2
    + 352 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient18 (s : ℚ) : ℚ :=
  s ^ 53
    - 38 * s ^ 52
    + 598 * s ^ 51
    - 3666 * s ^ 50
    - 30251 * s ^ 49
    + 949561 * s ^ 48
    - 11764481 * s ^ 47
    + 98247008 * s ^ 46
    - 620840900 * s ^ 45
    + 3118132826 * s ^ 44
    - 12806285208 * s ^ 43
    + 44044335377 * s ^ 42
    - 131049418548 * s ^ 41
    + 357702171756 * s ^ 40
    - 980672984392 * s ^ 39
    + 2902978813183 * s ^ 38
    - 9099308226196 * s ^ 37
    + 27918204122772 * s ^ 36
    - 78963653234997 * s ^ 35
    + 200950092931518 * s ^ 34
    - 458730699689241 * s ^ 33
    + 944648638541732 * s ^ 32
    - 1767892899977889 * s ^ 31
    + 3023868347767034 * s ^ 30
    - 4735813123723780 * s ^ 29
    + 6773086317070256 * s ^ 28
    - 8783771389231486 * s ^ 27
    + 10215233070363306 * s ^ 26
    - 10483001608492873 * s ^ 25
    + 9253472832041885 * s ^ 24
    - 6683811661257791 * s ^ 23
    + 3433518584232893 * s ^ 22
    - 394000534458079 * s ^ 21
    - 1712131517802930 * s ^ 20
    + 2614728465011681 * s ^ 19
    - 2512103781984053 * s ^ 18
    + 1860498925173721 * s ^ 17
    - 1107678490066319 * s ^ 16
    + 525130822326832 * s ^ 15
    - 185319545925813 * s ^ 14
    + 36407641437325 * s ^ 13
    + 6899231190835 * s ^ 12
    - 9676798244425 * s ^ 11
    + 4522015694823 * s ^ 10
    - 1253912581870 * s ^ 9
    + 188005509173 * s ^ 8
    - 555049717 * s ^ 7
    - 5354295705 * s ^ 6
    + 893860005 * s ^ 5
    - 33938389 * s ^ 4
    - 582101 * s ^ 3
    + 167415 * s ^ 2
    - 2354 * s
    - 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient19 (s : ℚ) : ℚ :=
  s ^ 53
    - 53 * s ^ 52
    + 1322 * s ^ 51
    - 20626 * s ^ 50
    + 224986 * s ^ 49
    - 1811642 * s ^ 48
    + 11045803 * s ^ 47
    - 51250064 * s ^ 46
    + 179034139 * s ^ 45
    - 474470794 * s ^ 44
    + 1249399042 * s ^ 43
    - 6592082242 * s ^ 42
    + 48828619373 * s ^ 41
    - 299978914076 * s ^ 40
    + 1451464147407 * s ^ 39
    - 5731027724247 * s ^ 38
    + 19096154661449 * s ^ 37
    - 55098575435774 * s ^ 36
    + 140508159189082 * s ^ 35
    - 322073843436021 * s ^ 34
    + 672604722520444 * s ^ 33
    - 1291505434753777 * s ^ 32
    + 2288368208961778 * s ^ 31
    - 3731927518359511 * s ^ 30
    + 5555285434743579 * s ^ 29
    - 7447859925110627 * s ^ 28
    + 8821784177162697 * s ^ 27
    - 8954829713970706 * s ^ 26
    + 7321689014795607 * s ^ 25
    - 3959349778240247 * s ^ 24
    - 390300694509265 * s ^ 23
    + 4523446906764843 * s ^ 22
    - 7304495488343657 * s ^ 21
    + 8167269567933697 * s ^ 20
    - 7291992670710417 * s ^ 19
    + 5394761356930572 * s ^ 18
    - 3310796824838164 * s ^ 17
    + 1636634471605252 * s ^ 16
    - 592347404766783 * s ^ 15
    + 97008021065697 * s ^ 14
    + 57802573555402 * s ^ 13
    - 63223994138327 * s ^ 12
    + 33278859447300 * s ^ 11
    - 11398503526521 * s ^ 10
    + 2419951540895 * s ^ 9
    - 176023713713 * s ^ 8
    - 63946138428 * s ^ 7
    + 21725345724 * s ^ 6
    - 2621218283 * s ^ 5
    + 40975790 * s ^ 4
    + 8677258 * s ^ 3
    - 874226 * s ^ 2
    + 8777 * s
    + 275

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient20 (s : ℚ) : ℚ :=
  -5 * s ^ 52
    + 234 * s ^ 51
    - 5193 * s ^ 50
    + 71829 * s ^ 49
    - 679286 * s ^ 48
    + 4435340 * s ^ 47
    - 17537374 * s ^ 46
    - 342793 * s ^ 45
    + 645596174 * s ^ 44
    - 6163948404 * s ^ 43
    + 38402713802 * s ^ 42
    - 186780945578 * s ^ 41
    + 755010358786 * s ^ 40
    - 2622722537318 * s ^ 39
    + 8015568393573 * s ^ 38
    - 21984091986894 * s ^ 37
    + 55087519883943 * s ^ 36
    - 128012948074169 * s ^ 35
    + 278401182357993 * s ^ 34
    - 567025479412208 * s ^ 33
    + 1072837560526980 * s ^ 32
    - 1857642889123980 * s ^ 31
    + 2884987124250823 * s ^ 30
    - 3911378938672213 * s ^ 29
    + 4426018422906813 * s ^ 28
    - 3747603660578959 * s ^ 27
    + 1325715499863339 * s ^ 26
    + 2863585302414990 * s ^ 25
    - 8081280388599018 * s ^ 24
    + 12976492591478273 * s ^ 23
    - 16122544252994445 * s ^ 22
    + 16655330471233733 * s ^ 21
    - 14639729747064514 * s ^ 20
    + 10967147849363748 * s ^ 19
    - 6882300909527927 * s ^ 18
    + 3436293985519057 * s ^ 17
    - 1151614814746986 * s ^ 16
    + 6164940008398 * s ^ 15
    + 348165449499991 * s ^ 14
    - 314100419857532 * s ^ 13
    + 177517019827247 * s ^ 12
    - 70967018657405 * s ^ 11
    + 19140140932759 * s ^ 10
    - 2512684271229 * s ^ 9
    - 406770651454 * s ^ 8
    + 280838350307 * s ^ 7
    - 60227714860 * s ^ 6
    + 5266741013 * s ^ 5
    + 174891268 * s ^ 4
    - 46963873 * s ^ 3
    + 3284195 * s ^ 2
    - 8991 * s
    - 2000

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient21 (s : ℚ) : ℚ :=
  -2 * s ^ 52
    + 115 * s ^ 51
    - 3156 * s ^ 50
    + 55303 * s ^ 49
    - 697180 * s ^ 48
    + 6747588 * s ^ 47
    - 52216849 * s ^ 46
    + 332194098 * s ^ 45
    - 1773472601 * s ^ 44
    + 8081378027 * s ^ 43
    - 31955925552 * s ^ 42
    + 111801359265 * s ^ 41
    - 355019235030 * s ^ 40
    + 1056638895877 * s ^ 39
    - 3042133515618 * s ^ 38
    + 8606475719535 * s ^ 37
    - 23682846837789 * s ^ 36
    + 61588586529116 * s ^ 35
    - 146535707226668 * s ^ 34
    + 309934445066708 * s ^ 33
    - 566530827294217 * s ^ 32
    + 859306226042178 * s ^ 31
    - 983632856035672 * s ^ 30
    + 541784906762073 * s ^ 29
    + 991681325131927 * s ^ 28
    - 4044511719813752 * s ^ 27
    + 8621785818433674 * s ^ 26
    - 14066912303231618 * s ^ 25
    + 19117927385688346 * s ^ 24
    - 22325035372831493 * s ^ 23
    + 22657003377302301 * s ^ 22
    - 19970860603096602 * s ^ 21
    + 15082008516279116 * s ^ 20
    - 9401968444059524 * s ^ 19
    + 4346330786779167 * s ^ 18
    - 821070499506185 * s ^ 17
    - 981336074373494 * s ^ 16
    + 1440669172135265 * s ^ 15
    - 1169277719227686 * s ^ 14
    + 694885398720269 * s ^ 13
    - 312390755301428 * s ^ 12
    + 100583359556512 * s ^ 11
    - 18197926413125 * s ^ 10
    - 1516052275635 * s ^ 9
    + 2241965896145 * s ^ 8
    - 735890342067 * s ^ 7
    + 118520575212 * s ^ 6
    - 5514246231 * s ^ 5
    - 1236769425 * s ^ 4
    + 165734418 * s ^ 3
    - 8944476 * s ^ 2
    - 99512 * s
    + 10352

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient22 (s : ℚ) : ℚ :=
  5 * s ^ 51
    - 254 * s ^ 50
    + 6248 * s ^ 49
    - 99001 * s ^ 48
    + 1132800 * s ^ 47
    - 9930845 * s ^ 46
    + 68903468 * s ^ 45
    - 383868551 * s ^ 44
    + 1709751342 * s ^ 43
    - 5860643901 * s ^ 42
    + 13279576539 * s ^ 41
    - 1722210678 * s ^ 40
    - 166917559067 * s ^ 39
    + 1031196984563 * s ^ 38
    - 4151993185983 * s ^ 37
    + 12930993028366 * s ^ 36
    - 32362043618102 * s ^ 35
    + 64151193193006 * s ^ 34
    - 91285874941721 * s ^ 33
    + 47678647465938 * s ^ 32
    + 220578004656097 * s ^ 31
    - 975289661973151 * s ^ 30
    + 2543991995886755 * s ^ 29
    - 5184649227705438 * s ^ 28
    + 8882387410100003 * s ^ 27
    - 13178201646952585 * s ^ 26
    + 17162823599999829 * s ^ 25
    - 19711267805655152 * s ^ 24
    + 19898847231350636 * s ^ 23
    - 17411980450678314 * s ^ 22
    + 12741834605870338 * s ^ 21
    - 7046375038289394 * s ^ 20
    + 1725396164636087 * s ^ 19
    + 2101869223964229 * s ^ 18
    - 3967857114012460 * s ^ 17
    + 4108053505635205 * s ^ 16
    - 3203726513706403 * s ^ 15
    + 1994196469252483 * s ^ 14
    - 984709013377701 * s ^ 13
    + 362824263620050 * s ^ 12
    - 80239837977346 * s ^ 11
    - 4396619822624 * s ^ 10
    + 12436890826530 * s ^ 9
    - 5565245986296 * s ^ 8
    + 1343227173727 * s ^ 7
    - 154859742036 * s ^ 6
    - 5661317485 * s ^ 5
    + 4225481001 * s ^ 4
    - 422745043 * s ^ 3
    + 16821585 * s ^ 2
    + 723227 * s
    - 40526

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient23 (s : ℚ) : ℚ :=
  s ^ 51
    - 59 * s ^ 50
    + 1675 * s ^ 49
    - 30653 * s ^ 48
    + 407999 * s ^ 47
    - 4219792 * s ^ 46
    + 35337925 * s ^ 45
    - 246218606 * s ^ 44
    + 1453560356 * s ^ 43
    - 7355498692 * s ^ 42
    + 32095981324 * s ^ 41
    - 120780692683 * s ^ 40
    + 388907764581 * s ^ 39
    - 1047680598282 * s ^ 38
    + 2222771359039 * s ^ 37
    - 2964572891607 * s ^ 36
    - 1847345012427 * s ^ 35
    + 28555798572964 * s ^ 34
    - 116712789981547 * s ^ 33
    + 342945313469696 * s ^ 32
    - 826316737734961 * s ^ 31
    + 1708566532504986 * s ^ 30
    - 3096199549172017 * s ^ 29
    + 4970987078524753 * s ^ 28
    - 7104895126688450 * s ^ 27
    + 9035220924212615 * s ^ 26
    - 10145780873048398 * s ^ 25
    + 9856301874929686 * s ^ 24
    - 7863068732341191 * s ^ 23
    + 4331302538860757 * s ^ 22
    + 62726429470787 * s ^ 21
    - 4299373081574028 * s ^ 20
    + 7364283538471000 * s ^ 19
    - 8635807999553246 * s ^ 18
    + 8111713660108219 * s ^ 17
    - 6348351948961105 * s ^ 16
    + 4153104300095463 * s ^ 15
    - 2219319515302374 * s ^ 14
    + 905086485719091 * s ^ 13
    - 223903292174736 * s ^ 12
    - 18610145488090 * s ^ 11
    + 51901945002400 * s ^ 10
    - 28636183769434 * s ^ 9
    + 9210850614320 * s ^ 8
    - 1701120989077 * s ^ 7
    + 81404812383 * s ^ 6
    + 40317630365 * s ^ 5
    - 9950681740 * s ^ 4
    + 794532444 * s ^ 3
    - 16576260 * s ^ 2
    - 2869845 * s
    + 124471

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient24 (s : ℚ) : ℚ :=
  -s ^ 50
    + 51 * s ^ 49
    - 1282 * s ^ 48
    + 21340 * s ^ 47
    - 266749 * s ^ 46
    + 2689099 * s ^ 45
    - 22859560 * s ^ 44
    + 168434230 * s ^ 43
    - 1092590369 * s ^ 42
    + 6287894079 * s ^ 41
    - 32211963161 * s ^ 40
    + 147092912950 * s ^ 39
    - 599226731228 * s ^ 38
    + 2179740548117 * s ^ 37
    - 7087901450543 * s ^ 36
    + 20629845644337 * s ^ 35
    - 53820226372602 * s ^ 34
    + 126025125215821 * s ^ 33
    - 265169102917680 * s ^ 32
    + 501622890689461 * s ^ 31
    - 852458761080608 * s ^ 30
    + 1296625224510045 * s ^ 29
    - 1747924615676573 * s ^ 28
    + 2038681665421413 * s ^ 27
    - 1929946844387838 * s ^ 26
    + 1161852764964632 * s ^ 25
    + 452683001950983 * s ^ 24
    - 2908904744695496 * s ^ 23
    + 5913044775804238 * s ^ 22
    - 8877479728816053 * s ^ 21
    + 11064919155466922 * s ^ 20
    - 11860989141211701 * s ^ 19
    + 11049116443348413 * s ^ 18
    - 8924125982655270 * s ^ 17
    + 6163049282975210 * s ^ 16
    - 3521930730608383 * s ^ 15
    + 1536185658480029 * s ^ 14
    - 378609085085723 * s ^ 13
    - 93218411013743 * s ^ 12
    + 168706023549523 * s ^ 11
    - 105849515541011 * s ^ 10
    + 41932523886441 * s ^ 9
    - 10594025013206 * s ^ 8
    + 1239343130632 * s ^ 7
    + 179668759970 * s ^ 6
    - 101632118411 * s ^ 5
    + 17378696489 * s ^ 4
    - 1053116906 * s ^ 3
    - 16661828 * s ^ 2
    + 8148540 * s
    - 307040

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient25 (s : ℚ) : ℚ :=
  -s ^ 49
    + 62 * s ^ 48
    - 1833 * s ^ 47
    + 34640 * s ^ 46
    - 472226 * s ^ 45
    + 4961772 * s ^ 44
    - 41882449 * s ^ 43
    + 292047036 * s ^ 42
    - 1715539750 * s ^ 41
    + 8609037392 * s ^ 40
    - 37277868707 * s ^ 39
    + 140243294358 * s ^ 38
    - 460358107616 * s ^ 37
    + 1320713811658 * s ^ 36
    - 3306246673366 * s ^ 35
    + 7173197598683 * s ^ 34
    - 13248690914888 * s ^ 33
    + 19848219179928 * s ^ 32
    - 20251087036634 * s ^ 31
    - 2083962668754 * s ^ 30
    + 80150097075285 * s ^ 29
    - 271142926261182 * s ^ 28
    + 661948423121872 * s ^ 27
    - 1364104875813038 * s ^ 26
    + 2486170055048109 * s ^ 25
    - 4075807018395459 * s ^ 24
    + 6042392469758268 * s ^ 23
    - 8099967589894851 * s ^ 22
    + 9788867376231992 * s ^ 21
    - 10610269465614627 * s ^ 20
    + 10235192510253804 * s ^ 19
    - 8678986426217014 * s ^ 18
    + 6330242880741044 * s ^ 17
    - 3801194109879826 * s ^ 16
    + 1675705612039361 * s ^ 15
    - 292585286430031 * s ^ 14
    - 331862359991414 * s ^ 13
    + 425508324642155 * s ^ 12
    - 287683955382317 * s ^ 11
    + 133108337609555 * s ^ 10
    - 42147174928520 * s ^ 9
    + 7544621040709 * s ^ 8
    + 263021975565 * s ^ 7
    - 592819828218 * s ^ 6
    + 170160736139 * s ^ 5
    - 22649045526 * s ^ 4
    + 772354100 * s ^ 3
    + 113519450 * s ^ 2
    - 17882282 * s
    + 617592

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient26 (s : ℚ) : ℚ :=
  s ^ 48
    - 55 * s ^ 47
    + 1479 * s ^ 46
    - 25953 * s ^ 45
    + 334475 * s ^ 44
    - 3376343 * s ^ 43
    + 27784278 * s ^ 42
    - 191435774 * s ^ 41
    + 1125234475 * s ^ 40
    - 5719784127 * s ^ 39
    + 25407306388 * s ^ 38
    - 99469512940 * s ^ 37
    + 345893568169 * s ^ 36
    - 1076929191335 * s ^ 35
    + 3029961217626 * s ^ 34
    - 7791632903134 * s ^ 33
    + 18567171034663 * s ^ 32
    - 41624361529674 * s ^ 31
    + 88972708514055 * s ^ 30
    - 182729158864313 * s ^ 29
    + 360407144680392 * s ^ 28
    - 677580557698848 * s ^ 27
    + 1201085109527567 * s ^ 26
    - 1985322235997318 * s ^ 25
    + 3030446082129393 * s ^ 24
    - 4235900673939666 * s ^ 23
    + 5379705135659785 * s ^ 22
    - 6156497756288137 * s ^ 21
    + 6281036644371246 * s ^ 20
    - 5618604915793651 * s ^ 19
    + 4273347840653810 * s ^ 18
    - 2575887261942084 * s ^ 17
    + 961675033080998 * s ^ 16
    + 204332968613079 * s ^ 15
    - 766634929980913 * s ^ 14
    + 811171522193591 * s ^ 13
    - 576283678989732 * s ^ 12
    + 300616456370152 * s ^ 11
    - 112934527192021 * s ^ 10
    + 26398758659989 * s ^ 9
    - 737091634010 * s ^ 8
    - 2235530720383 * s ^ 7
    + 967623271072 * s ^ 6
    - 206956289416 * s ^ 5
    + 20839323680 * s ^ 4
    + 380961339 * s ^ 3
    - 281742566 * s ^ 2
    + 31363257 * s
    - 1022566

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient27 (s : ℚ) : ℚ :=
  -s ^ 46
    + 45 * s ^ 45
    - 963 * s ^ 44
    + 13025 * s ^ 43
    - 125356 * s ^ 42
    + 926531 * s ^ 41
    - 5684844 * s ^ 40
    + 32150272 * s ^ 39
    - 186538070 * s ^ 38
    + 1135921436 * s ^ 37
    - 6771461468 * s ^ 36
    + 36764684912 * s ^ 35
    - 175617077416 * s ^ 34
    + 731763410238 * s ^ 33
    - 2666646186718 * s ^ 32
    + 8551972799527 * s ^ 31
    - 24305341815537 * s ^ 30
    + 61622776552427 * s ^ 29
    - 140179756129547 * s ^ 28
    + 287410196737583 * s ^ 27
    - 532672730762539 * s ^ 26
    + 893260042165556 * s ^ 25
    - 1353645883056642 * s ^ 24
    + 1846617521810477 * s ^ 23
    - 2251196259123430 * s ^ 22
    + 2419945089937785 * s ^ 21
    - 2234279460312133 * s ^ 20
    + 1667500393707517 * s ^ 19
    - 822632843966704 * s ^ 18
    - 84895667767493 * s ^ 17
    + 805445875622023 * s ^ 16
    - 1162489268114339 * s ^ 15
    + 1131644928420986 * s ^ 14
    - 840570172239954 * s ^ 13
    + 483240268777622 * s ^ 12
    - 207289630154601 * s ^ 11
    + 57867022770848 * s ^ 10
    - 3421670847632 * s ^ 9
    - 6117250611170 * s ^ 8
    + 3574745246873 * s ^ 7
    - 1074923985846 * s ^ 6
    + 181620891403 * s ^ 5
    - 10280288343 * s ^ 4
    - 2220845382 * s ^ 3
    + 477840961 * s ^ 2
    - 44692670 * s
    + 1400751

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient28 (s : ℚ) : ℚ :=
  -s ^ 45
    + 58 * s ^ 44
    - 1630 * s ^ 43
    + 29604 * s ^ 42
    - 391000 * s ^ 41
    + 4007380 * s ^ 40
    - 33216280 * s ^ 39
    + 229145001 * s ^ 38
    - 1343616041 * s ^ 37
    + 6804439028 * s ^ 36
    - 30136976689 * s ^ 35
    + 117917764246 * s ^ 34
    - 411029771385 * s ^ 33
    + 1285557029319 * s ^ 32
    - 3630005505007 * s ^ 31
    + 9301184115576 * s ^ 30
    - 21707616567709 * s ^ 29
    + 46234391843721 * s ^ 28
    - 89834058821615 * s ^ 27
    + 158760164791155 * s ^ 26
    - 253666692260422 * s ^ 25
    + 362779670571163 * s ^ 24
    - 456382589554542 * s ^ 23
    + 487818568031157 * s ^ 22
    - 405529555493889 * s ^ 21
    + 176359801343257 * s ^ 20
    + 187279239870903 * s ^ 19
    - 612171516324993 * s ^ 18
    + 978307177815374 * s ^ 17
    - 1166227175786857 * s ^ 16
    + 1117699430486889 * s ^ 15
    - 871631352782056 * s ^ 14
    + 543821288575038 * s ^ 13
    - 257971921836855 * s ^ 12
    + 79760831603447 * s ^ 11
    - 3409947431205 * s ^ 10
    - 13336841224765 * s ^ 9
    + 9209602211227 * s ^ 8
    - 3540707615068 * s ^ 7
    + 844371827626 * s ^ 6
    - 102451035064 * s ^ 5
    - 4645086841 * s ^ 4
    + 3951681296 * s ^ 3
    - 616428327 * s ^ 2
    + 52135376 * s
    - 1589600

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient29 (s : ℚ) : ℚ :=
  s ^ 43
    - 56 * s ^ 42
    + 1526 * s ^ 41
    - 26862 * s ^ 40
    + 342793 * s ^ 39
    - 3380919 * s ^ 38
    + 26871982 * s ^ 37
    - 177364674 * s ^ 36
    + 994393872 * s ^ 35
    - 4817345880 * s ^ 34
    + 20419074566 * s ^ 33
    - 76357474338 * s ^ 32
    + 253057645078 * s ^ 31
    - 744109569741 * s ^ 30
    + 1937573031709 * s ^ 29
    - 4444313953592 * s ^ 28
    + 8889925723769 * s ^ 27
    - 15200238988858 * s ^ 26
    + 21203176925954 * s ^ 25
    - 20783466560932 * s ^ 24
    + 2549948028817 * s ^ 23
    + 49220858760005 * s ^ 22
    - 149325858929603 * s ^ 21
    + 301516260465470 * s ^ 20
    - 487182058877248 * s ^ 19
    + 661395330051973 * s ^ 18
    - 764873396434383 * s ^ 17
    + 751651340283915 * s ^ 16
    - 618310576440961 * s ^ 15
    + 412469513360566 * s ^ 14
    - 208222968679183 * s ^ 13
    + 63515934589130 * s ^ 12
    + 6754490725933 * s ^ 11
    - 23527456971355 * s ^ 10
    + 17150161691706 * s ^ 9
    - 7809320930705 * s ^ 8
    + 2384249145241 * s ^ 7
    - 434096718367 * s ^ 6
    + 13927341783 * s ^ 5
    + 16133746336 * s ^ 4
    - 4681457303 * s ^ 3
    + 626273360 * s ^ 2
    - 49861665 * s
    + 1491140

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient30 (s : ℚ) : ℚ :=
  12 * s ^ 40
    - 595 * s ^ 39
    + 13943 * s ^ 38
    - 205711 * s ^ 37
    + 2145365 * s ^ 36
    - 16805565 * s ^ 35
    + 102286532 * s ^ 34
    - 491169266 * s ^ 33
    + 1850910948 * s ^ 32
    - 5224733367 * s ^ 31
    + 8939577955 * s ^ 30
    + 6647922707 * s ^ 29
    - 128530737456 * s ^ 28
    + 634404864750 * s ^ 27
    - 2242477405381 * s ^ 26
    + 6519414856400 * s ^ 25
    - 16364173433067 * s ^ 24
    + 36206298282107 * s ^ 23
    - 71176289459553 * s ^ 22
    + 124460980939324 * s ^ 21
    - 193039522999824 * s ^ 20
    + 264043721704890 * s ^ 19
    - 315593763967571 * s ^ 18
    + 324800325147020 * s ^ 17
    - 280789705566108 * s ^ 16
    + 194553149844215 * s ^ 15
    - 96118574142938 * s ^ 14
    + 17995172704477 * s ^ 13
    + 23102472145681 * s ^ 12
    - 31507363570477 * s ^ 11
    + 22990342157505 * s ^ 10
    - 11734556065802 * s ^ 9
    + 4283147700403 * s ^ 8
    - 1016356093330 * s ^ 7
    + 85436002375 * s ^ 6
    + 40144026591 * s ^ 5
    - 19164049072 * s ^ 4
    + 4125838468 * s ^ 3
    - 506480555 * s ^ 2
    + 38963404 * s
    - 1149434

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient31 (s : ℚ) : ℚ :=
  s ^ 40
    - 56 * s ^ 39
    + 1490 * s ^ 38
    - 25184 * s ^ 37
    + 305068 * s ^ 36
    - 2833829 * s ^ 35
    + 21100158 * s ^ 34
    - 130045152 * s ^ 33
    + 680415458 * s ^ 32
    - 3086759810 * s ^ 31
    + 12365737385 * s ^ 30
    - 44431596576 * s ^ 29
    + 144933310915 * s ^ 28
    - 432390896830 * s ^ 27
    + 1182368423110 * s ^ 26
    - 2955960818682 * s ^ 25
    + 6718664350588 * s ^ 24
    - 13788077036050 * s ^ 23
    + 25365481587054 * s ^ 22
    - 41519197034358 * s ^ 21
    + 59926324192001 * s ^ 20
    - 75286382853708 * s ^ 19
    + 80560981022298 * s ^ 18
    - 70419836698791 * s ^ 17
    + 45365631629728 * s ^ 16
    - 13240114081727 * s ^ 15
    - 14334212704725 * s ^ 14
    + 28790847737897 * s ^ 13
    - 29252758618284 * s ^ 12
    + 21278314062098 * s ^ 11
    - 11764928224735 * s ^ 10
    + 4877697661926 * s ^ 9
    - 1373185803164 * s ^ 8
    + 151597996985 * s ^ 7
    + 75528013298 * s ^ 6
    - 49178946717 * s ^ 5
    + 14920145600 * s ^ 4
    - 2784177345 * s ^ 3
    + 325414931 * s ^ 2
    - 24672907 * s
    + 720641

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient32 (s : ℚ) : ℚ :=
  -2 * s ^ 38
    + 108 * s ^ 37
    - 2801 * s ^ 36
    + 46580 * s ^ 35
    - 559447 * s ^ 34
    + 5181298 * s ^ 33
    - 38566264 * s ^ 32
    + 237299778 * s ^ 31
    - 1231324170 * s ^ 30
    + 5466167216 * s ^ 29
    - 20977560207 * s ^ 28
    + 70119802411 * s ^ 27
    - 205215845954 * s ^ 26
    + 527601240801 * s ^ 25
    - 1193204302147 * s ^ 24
    + 2370901886134 * s ^ 23
    - 4117281411473 * s ^ 22
    + 6170787500940 * s ^ 21
    - 7764923075404 * s ^ 20
    + 7676605073501 * s ^ 19
    - 4730758884549 * s ^ 18
    - 1300127143474 * s ^ 17
    + 8991355650864 * s ^ 16
    - 15589174766102 * s ^ 15
    + 18522915133408 * s ^ 14
    - 17036120188933 * s ^ 13
    + 12519611187079 * s ^ 12
    - 7333524920517 * s ^ 11
    + 3293621371762 * s ^ 10
    - 990752770255 * s ^ 9
    + 69897724467 * s ^ 8
    + 124554244414 * s ^ 7
    - 86078929271 * s ^ 6
    + 32781218687 * s ^ 5
    - 8337055923 * s ^ 4
    + 1438649361 * s ^ 3
    - 164197792 * s ^ 2
    + 12487524 * s
    - 361648

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient33 (s : ℚ) : ℚ :=
  s ^ 36
    - 49 * s ^ 35
    + 1144 * s ^ 34
    - 16960 * s ^ 33
    + 179523 * s ^ 32
    - 1446112 * s ^ 31
    + 9221075 * s ^ 30
    - 47735047 * s ^ 29
    + 203574091 * s ^ 28
    - 717544352 * s ^ 27
    + 2059714574 * s ^ 26
    - 4545365579 * s ^ 25
    + 6061343880 * s ^ 24
    + 5048648330 * s ^ 23
    - 65041462388 * s ^ 22
    + 254718371575 * s ^ 21
    - 704694699419 * s ^ 20
    + 1549788948407 * s ^ 19
    - 2813043294611 * s ^ 18
    + 4275410208338 * s ^ 17
    - 5468595686424 * s ^ 16
    + 5886413531311 * s ^ 15
    - 5307420189640 * s ^ 14
    + 3959582617275 * s ^ 13
    - 2371435905620 * s ^ 12
    + 1047002260476 * s ^ 11
    - 231145594455 * s ^ 10
    - 110016211487 * s ^ 9
    + 160036181670 * s ^ 8
    - 103394224312 * s ^ 7
    + 45366502973 * s ^ 6
    - 14475136254 * s ^ 5
    + 3373262275 * s ^ 4
    - 558920751 * s ^ 3
    + 63671780 * s ^ 2
    - 4947041 * s
    + 141803

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient34 (s : ℚ) : ℚ :=
  -3 * s ^ 33
    + 152 * s ^ 32
    - 3693 * s ^ 31
    + 57325 * s ^ 30
    - 638971 * s ^ 29
    + 5448685 * s ^ 28
    - 36967676 * s ^ 27
    + 204847541 * s ^ 26
    - 943980156 * s ^ 25
    + 3663348621 * s ^ 24
    - 12075099740 * s ^ 23
    + 33990517332 * s ^ 22
    - 81946474710 * s ^ 21
    + 169321186217 * s ^ 20
    - 299455676749 * s ^ 19
    + 451762464608 * s ^ 18
    - 577759014811 * s ^ 17
    + 619424556216 * s ^ 16
    - 544234394465 * s ^ 15
    + 370255176582 * s ^ 14
    - 158282089192 * s ^ 13
    - 22661450322 * s ^ 12
    + 128857650332 * s ^ 11
    - 154971622114 * s ^ 10
    + 126197078652 * s ^ 9
    - 78364282374 * s ^ 8
    + 38093262412 * s ^ 7
    - 14509234904 * s ^ 6
    + 4284336893 * s ^ 5
    - 959363485 * s ^ 4
    + 157238511 * s ^ 3
    - 18321822 * s ^ 2
    + 1486958 * s
    - 41850

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient35 (s : ℚ) : ℚ :=
  2 * s ^ 30
    - 96 * s ^ 29
    + 2197 * s ^ 28
    - 31901 * s ^ 27
    + 329901 * s ^ 26
    - 2585258 * s ^ 25
    + 15946748 * s ^ 24
    - 79393975 * s ^ 23
    + 324632578 * s ^ 22
    - 1103828527 * s ^ 21
    + 3150580864 * s ^ 20
    - 7606597057 * s ^ 19
    + 15647234864 * s ^ 18
    - 27646221351 * s ^ 17
    + 42381754711 * s ^ 16
    - 57091061735 * s ^ 15
    + 68515318608 * s ^ 14
    - 74031868585 * s ^ 13
    + 72130473269 * s ^ 12
    - 62713557428 * s ^ 11
    + 47715736811 * s ^ 10
    - 31059054113 * s ^ 9
    + 16936028631 * s ^ 8
    - 7599241243 * s ^ 7
    + 2761213650 * s ^ 6
    - 797882656 * s ^ 5
    + 178650730 * s ^ 4
    - 29964787 * s ^ 3
    + 3699798 * s ^ 2
    - 323392 * s
    + 8742

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient36 (s : ℚ) : ℚ :=
  -2 * s ^ 26
    + 89 * s ^ 25
    - 1873 * s ^ 24
    + 24792 * s ^ 23
    - 231570 * s ^ 22
    + 1623319 * s ^ 21
    - 8867915 * s ^ 20
    + 38695312 * s ^ 19
    - 137153712 * s ^ 18
    + 399458716 * s ^ 17
    - 963407571 * s ^ 16
    + 1933439594 * s ^ 15
    - 3237071747 * s ^ 14
    + 4524788774 * s ^ 13
    - 5276769293 * s ^ 12
    + 5125286578 * s ^ 11
    - 4136790914 * s ^ 10
    + 2768052421 * s ^ 9
    - 1531963417 * s ^ 8
    + 699174300 * s ^ 7
    - 261480061 * s ^ 6
    + 78980029 * s ^ 5
    - 18774369 * s ^ 4
    + 3420276 * s ^ 3
    - 477740 * s ^ 2
    + 47136 * s
    - 1152

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient37 (s : ℚ) : ℚ :=
  s ^ 20
    - 35 * s ^ 19
    + 569 * s ^ 18
    - 5704 * s ^ 17
    + 39476 * s ^ 16
    - 200116 * s ^ 15
    + 769419 * s ^ 14
    - 2292441 * s ^ 13
    + 5362232 * s ^ 12
    - 9917065 * s ^ 11
    + 14536945 * s ^ 10
    - 16862709 * s ^ 9
    + 15394260 * s ^ 8
    - 10953846 * s ^ 7
    + 5990033 * s ^ 6
    - 2475240 * s ^ 5
    + 764931 * s ^ 4
    - 180100 * s ^ 3
    + 33326 * s ^ 2
    - 4008 * s
    + 72

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient38 (s : ℚ) : ℚ :=
  -s ^ 10
    + 18 * s ^ 9
    - 140 * s ^ 8
    + 616 * s ^ 7
    - 1685 * s ^ 6
    + 2962 * s ^ 5
    - 3334 * s ^ 4
    + 2308 * s ^ 3
    - 888 * s ^ 2
    + 144 * s

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
    structuralNumeratorCoefficient37 s * r ^ 37 +
    structuralNumeratorCoefficient38 s * r ^ 38

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_0 (s : ℚ) :
    structuralNumeratorCoefficient0 s =
      numeratorProductCoefficient0 s
        - denominatorProductCoefficient0 s
      := by
  simp only [structuralNumeratorCoefficient0,
    numeratorProductCoefficient0,
    denominatorProductCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_1 (s : ℚ) :
    structuralNumeratorCoefficient1 s =
      numeratorProductCoefficient1 s
        - denominatorProductCoefficient1 s
      := by
  simp only [structuralNumeratorCoefficient1,
    numeratorProductCoefficient1,
    denominatorProductCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_2 (s : ℚ) :
    structuralNumeratorCoefficient2 s =
      numeratorProductCoefficient2 s
        - denominatorProductCoefficient2 s
      := by
  simp only [structuralNumeratorCoefficient2,
    numeratorProductCoefficient2,
    denominatorProductCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_3 (s : ℚ) :
    structuralNumeratorCoefficient3 s =
      numeratorProductCoefficient3 s
        - denominatorProductCoefficient3 s
      := by
  simp only [structuralNumeratorCoefficient3,
    numeratorProductCoefficient3,
    denominatorProductCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_4 (s : ℚ) :
    structuralNumeratorCoefficient4 s =
      numeratorProductCoefficient4 s
        - denominatorProductCoefficient4 s
      := by
  simp only [structuralNumeratorCoefficient4,
    numeratorProductCoefficient4,
    denominatorProductCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_5 (s : ℚ) :
    structuralNumeratorCoefficient5 s =
      numeratorProductCoefficient5 s
        - denominatorProductCoefficient5 s
      := by
  simp only [structuralNumeratorCoefficient5,
    numeratorProductCoefficient5,
    denominatorProductCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_6 (s : ℚ) :
    structuralNumeratorCoefficient6 s =
      numeratorProductCoefficient6 s
        - denominatorProductCoefficient6 s
      := by
  simp only [structuralNumeratorCoefficient6,
    numeratorProductCoefficient6,
    denominatorProductCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_7 (s : ℚ) :
    structuralNumeratorCoefficient7 s =
      numeratorProductCoefficient7 s
        - denominatorProductCoefficient7 s
      := by
  simp only [structuralNumeratorCoefficient7,
    numeratorProductCoefficient7,
    denominatorProductCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_8 (s : ℚ) :
    structuralNumeratorCoefficient8 s =
      numeratorProductCoefficient8 s
        - denominatorProductCoefficient8 s
      := by
  simp only [structuralNumeratorCoefficient8,
    numeratorProductCoefficient8,
    denominatorProductCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_9 (s : ℚ) :
    structuralNumeratorCoefficient9 s =
      numeratorProductCoefficient9 s
        - denominatorProductCoefficient9 s
      := by
  simp only [structuralNumeratorCoefficient9,
    numeratorProductCoefficient9,
    denominatorProductCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_10 (s : ℚ) :
    structuralNumeratorCoefficient10 s =
      numeratorProductCoefficient10 s
        - denominatorProductCoefficient10 s
      := by
  simp only [structuralNumeratorCoefficient10,
    numeratorProductCoefficient10,
    denominatorProductCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_11 (s : ℚ) :
    structuralNumeratorCoefficient11 s =
      numeratorProductCoefficient11 s
        - denominatorProductCoefficient11 s
      := by
  simp only [structuralNumeratorCoefficient11,
    numeratorProductCoefficient11,
    denominatorProductCoefficient11]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_12 (s : ℚ) :
    structuralNumeratorCoefficient12 s =
      numeratorProductCoefficient12 s
        - denominatorProductCoefficient12 s
      := by
  simp only [structuralNumeratorCoefficient12,
    numeratorProductCoefficient12,
    denominatorProductCoefficient12]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_13 (s : ℚ) :
    structuralNumeratorCoefficient13 s =
      numeratorProductCoefficient13 s
        - denominatorProductCoefficient13 s
      := by
  simp only [structuralNumeratorCoefficient13,
    numeratorProductCoefficient13,
    denominatorProductCoefficient13]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_14 (s : ℚ) :
    structuralNumeratorCoefficient14 s =
      numeratorProductCoefficient14 s
        - denominatorProductCoefficient14 s
      := by
  simp only [structuralNumeratorCoefficient14,
    numeratorProductCoefficient14,
    denominatorProductCoefficient14]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_15 (s : ℚ) :
    structuralNumeratorCoefficient15 s =
      numeratorProductCoefficient15 s
        - denominatorProductCoefficient15 s
      := by
  simp only [structuralNumeratorCoefficient15,
    numeratorProductCoefficient15,
    denominatorProductCoefficient15]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_16 (s : ℚ) :
    structuralNumeratorCoefficient16 s =
      numeratorProductCoefficient16 s
        - denominatorProductCoefficient16 s
      := by
  simp only [structuralNumeratorCoefficient16,
    numeratorProductCoefficient16,
    denominatorProductCoefficient16]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_17 (s : ℚ) :
    structuralNumeratorCoefficient17 s =
      numeratorProductCoefficient17 s
        - denominatorProductCoefficient17 s
      := by
  simp only [structuralNumeratorCoefficient17,
    numeratorProductCoefficient17,
    denominatorProductCoefficient17]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_18 (s : ℚ) :
    structuralNumeratorCoefficient18 s =
      numeratorProductCoefficient18 s
        - denominatorProductCoefficient18 s
      := by
  simp only [structuralNumeratorCoefficient18,
    numeratorProductCoefficient18,
    denominatorProductCoefficient18]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_19 (s : ℚ) :
    structuralNumeratorCoefficient19 s =
      numeratorProductCoefficient19 s
        - denominatorProductCoefficient19 s
      := by
  simp only [structuralNumeratorCoefficient19,
    numeratorProductCoefficient19,
    denominatorProductCoefficient19]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_20 (s : ℚ) :
    structuralNumeratorCoefficient20 s =
      numeratorProductCoefficient20 s
        - denominatorProductCoefficient20 s
      := by
  simp only [structuralNumeratorCoefficient20,
    numeratorProductCoefficient20,
    denominatorProductCoefficient20]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_21 (s : ℚ) :
    structuralNumeratorCoefficient21 s =
      numeratorProductCoefficient21 s
        - denominatorProductCoefficient21 s
      := by
  simp only [structuralNumeratorCoefficient21,
    numeratorProductCoefficient21,
    denominatorProductCoefficient21]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_22 (s : ℚ) :
    structuralNumeratorCoefficient22 s =
      numeratorProductCoefficient22 s
        - denominatorProductCoefficient22 s
      := by
  simp only [structuralNumeratorCoefficient22,
    numeratorProductCoefficient22,
    denominatorProductCoefficient22]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_23 (s : ℚ) :
    structuralNumeratorCoefficient23 s =
      numeratorProductCoefficient23 s
        - denominatorProductCoefficient23 s
      := by
  simp only [structuralNumeratorCoefficient23,
    numeratorProductCoefficient23,
    denominatorProductCoefficient23]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_24 (s : ℚ) :
    structuralNumeratorCoefficient24 s =
      numeratorProductCoefficient24 s
        - denominatorProductCoefficient24 s
      := by
  simp only [structuralNumeratorCoefficient24,
    numeratorProductCoefficient24,
    denominatorProductCoefficient24]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_25 (s : ℚ) :
    structuralNumeratorCoefficient25 s =
      numeratorProductCoefficient25 s
        - denominatorProductCoefficient25 s
      := by
  simp only [structuralNumeratorCoefficient25,
    numeratorProductCoefficient25,
    denominatorProductCoefficient25]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_26 (s : ℚ) :
    structuralNumeratorCoefficient26 s =
      numeratorProductCoefficient26 s
        - denominatorProductCoefficient26 s
      := by
  simp only [structuralNumeratorCoefficient26,
    numeratorProductCoefficient26,
    denominatorProductCoefficient26]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_27 (s : ℚ) :
    structuralNumeratorCoefficient27 s =
      numeratorProductCoefficient27 s
        - denominatorProductCoefficient27 s
      := by
  simp only [structuralNumeratorCoefficient27,
    numeratorProductCoefficient27,
    denominatorProductCoefficient27]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_28 (s : ℚ) :
    structuralNumeratorCoefficient28 s =
      numeratorProductCoefficient28 s
        - denominatorProductCoefficient28 s
      := by
  simp only [structuralNumeratorCoefficient28,
    numeratorProductCoefficient28,
    denominatorProductCoefficient28]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_29 (s : ℚ) :
    structuralNumeratorCoefficient29 s =
      numeratorProductCoefficient29 s
        - denominatorProductCoefficient29 s
      := by
  simp only [structuralNumeratorCoefficient29,
    numeratorProductCoefficient29,
    denominatorProductCoefficient29]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_30 (s : ℚ) :
    structuralNumeratorCoefficient30 s =
      numeratorProductCoefficient30 s
        - denominatorProductCoefficient30 s
      := by
  simp only [structuralNumeratorCoefficient30,
    numeratorProductCoefficient30,
    denominatorProductCoefficient30]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_31 (s : ℚ) :
    structuralNumeratorCoefficient31 s =
      numeratorProductCoefficient31 s
        - denominatorProductCoefficient31 s
      := by
  simp only [structuralNumeratorCoefficient31,
    numeratorProductCoefficient31,
    denominatorProductCoefficient31]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_32 (s : ℚ) :
    structuralNumeratorCoefficient32 s =
      numeratorProductCoefficient32 s
        - denominatorProductCoefficient32 s
      := by
  simp only [structuralNumeratorCoefficient32,
    numeratorProductCoefficient32,
    denominatorProductCoefficient32]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_33 (s : ℚ) :
    structuralNumeratorCoefficient33 s =
      numeratorProductCoefficient33 s
        - denominatorProductCoefficient33 s
      := by
  simp only [structuralNumeratorCoefficient33,
    numeratorProductCoefficient33,
    denominatorProductCoefficient33]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_34 (s : ℚ) :
    structuralNumeratorCoefficient34 s =
      numeratorProductCoefficient34 s
        - denominatorProductCoefficient34 s
      := by
  simp only [structuralNumeratorCoefficient34,
    numeratorProductCoefficient34,
    denominatorProductCoefficient34]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_35 (s : ℚ) :
    structuralNumeratorCoefficient35 s =
      numeratorProductCoefficient35 s
        - denominatorProductCoefficient35 s
      := by
  simp only [structuralNumeratorCoefficient35,
    numeratorProductCoefficient35,
    denominatorProductCoefficient35]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_36 (s : ℚ) :
    structuralNumeratorCoefficient36 s =
      numeratorProductCoefficient36 s
        - denominatorProductCoefficient36 s
      := by
  simp only [structuralNumeratorCoefficient36,
    numeratorProductCoefficient36,
    denominatorProductCoefficient36]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_37 (s : ℚ) :
    structuralNumeratorCoefficient37 s =
      numeratorProductCoefficient37 s
        - denominatorProductCoefficient37 s
      := by
  simp only [structuralNumeratorCoefficient37,
    numeratorProductCoefficient37,
    denominatorProductCoefficient37]
  ring

/-- Checked coefficient identity for the polynomial combination. -/
theorem structuralNumeratorCoefficient_subtraction_certificate_38 (s : ℚ) :
    structuralNumeratorCoefficient38 s =
      0
        - denominatorProductCoefficient38 s
      := by
  simp only [structuralNumeratorCoefficient38,
    denominatorProductCoefficient38]
  ring

/-- Checked staged polynomial-combination identity. -/
theorem structuralNumerator_eq_linearCombination (r s : ℚ) :
    structuralNumerator r s = numeratorProduct r s - denominatorProduct r s := by
  have h0 := structuralNumeratorCoefficient_subtraction_certificate_0 s
  have h1 := structuralNumeratorCoefficient_subtraction_certificate_1 s
  have h2 := structuralNumeratorCoefficient_subtraction_certificate_2 s
  have h3 := structuralNumeratorCoefficient_subtraction_certificate_3 s
  have h4 := structuralNumeratorCoefficient_subtraction_certificate_4 s
  have h5 := structuralNumeratorCoefficient_subtraction_certificate_5 s
  have h6 := structuralNumeratorCoefficient_subtraction_certificate_6 s
  have h7 := structuralNumeratorCoefficient_subtraction_certificate_7 s
  have h8 := structuralNumeratorCoefficient_subtraction_certificate_8 s
  have h9 := structuralNumeratorCoefficient_subtraction_certificate_9 s
  have h10 := structuralNumeratorCoefficient_subtraction_certificate_10 s
  have h11 := structuralNumeratorCoefficient_subtraction_certificate_11 s
  have h12 := structuralNumeratorCoefficient_subtraction_certificate_12 s
  have h13 := structuralNumeratorCoefficient_subtraction_certificate_13 s
  have h14 := structuralNumeratorCoefficient_subtraction_certificate_14 s
  have h15 := structuralNumeratorCoefficient_subtraction_certificate_15 s
  have h16 := structuralNumeratorCoefficient_subtraction_certificate_16 s
  have h17 := structuralNumeratorCoefficient_subtraction_certificate_17 s
  have h18 := structuralNumeratorCoefficient_subtraction_certificate_18 s
  have h19 := structuralNumeratorCoefficient_subtraction_certificate_19 s
  have h20 := structuralNumeratorCoefficient_subtraction_certificate_20 s
  have h21 := structuralNumeratorCoefficient_subtraction_certificate_21 s
  have h22 := structuralNumeratorCoefficient_subtraction_certificate_22 s
  have h23 := structuralNumeratorCoefficient_subtraction_certificate_23 s
  have h24 := structuralNumeratorCoefficient_subtraction_certificate_24 s
  have h25 := structuralNumeratorCoefficient_subtraction_certificate_25 s
  have h26 := structuralNumeratorCoefficient_subtraction_certificate_26 s
  have h27 := structuralNumeratorCoefficient_subtraction_certificate_27 s
  have h28 := structuralNumeratorCoefficient_subtraction_certificate_28 s
  have h29 := structuralNumeratorCoefficient_subtraction_certificate_29 s
  have h30 := structuralNumeratorCoefficient_subtraction_certificate_30 s
  have h31 := structuralNumeratorCoefficient_subtraction_certificate_31 s
  have h32 := structuralNumeratorCoefficient_subtraction_certificate_32 s
  have h33 := structuralNumeratorCoefficient_subtraction_certificate_33 s
  have h34 := structuralNumeratorCoefficient_subtraction_certificate_34 s
  have h35 := structuralNumeratorCoefficient_subtraction_certificate_35 s
  have h36 := structuralNumeratorCoefficient_subtraction_certificate_36 s
  have h37 := structuralNumeratorCoefficient_subtraction_certificate_37 s
  have h38 := structuralNumeratorCoefficient_subtraction_certificate_38 s
  simp only [structuralNumerator, numeratorProduct, denominatorProduct]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 + r ^ 36 * h36 + r ^ 37 * h37 +
    r ^ 38 * h38

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient1 (s : ℚ) : ℚ :=
  s ^ 25
    - 4 * s ^ 24
    + 10 * s ^ 23
    - 18 * s ^ 22
    + 25 * s ^ 21
    - 28 * s ^ 20
    + 25 * s ^ 19
    - 18 * s ^ 18
    + 10 * s ^ 17
    - 4 * s ^ 16
    + s ^ 15

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 31
    + 7 * s ^ 30
    - 27 * s ^ 29
    + 75 * s ^ 28
    - 169 * s ^ 27
    + 333 * s ^ 26
    - 592 * s ^ 25
    + 921 * s ^ 24
    - 1244 * s ^ 23
    + 1419 * s ^ 22
    - 1330 * s ^ 21
    + 970 * s ^ 20
    - 454 * s ^ 19
    - 4 * s ^ 18
    + 270 * s ^ 17
    - 314 * s ^ 16
    + 223 * s ^ 15
    - 111 * s ^ 14
    + 35 * s ^ 13
    - 8 * s ^ 12
    + s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient3 (s : ℚ) : ℚ :=
  s ^ 33
    - 11 * s ^ 32
    + 58 * s ^ 31
    - 179 * s ^ 30
    + 385 * s ^ 29
    - 642 * s ^ 28
    + 922 * s ^ 27
    - 1205 * s ^ 26
    + 1150 * s ^ 25
    + 306 * s ^ 24
    - 4407 * s ^ 23
    + 11990 * s ^ 22
    - 21907 * s ^ 21
    + 31074 * s ^ 20
    - 35787 * s ^ 19
    + 33705 * s ^ 18
    - 26029 * s ^ 17
    + 15992 * s ^ 16
    - 7370 * s ^ 15
    + 2137 * s ^ 14
    - 4 * s ^ 13
    - 310 * s ^ 12
    + 178 * s ^ 11
    - 56 * s ^ 10
    + 10 * s ^ 9
    - s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient4 (s : ℚ) : ℚ :=
  s ^ 34
    - 8 * s ^ 33
    + s ^ 32
    + 243 * s ^ 31
    - 1494 * s ^ 30
    + 5004 * s ^ 29
    - 11987 * s ^ 28
    + 23780 * s ^ 27
    - 44506 * s ^ 26
    + 84277 * s ^ 25
    - 155476 * s ^ 24
    + 260758 * s ^ 23
    - 383709 * s ^ 22
    + 483094 * s ^ 21
    - 512682 * s ^ 20
    + 446897 * s ^ 19
    - 301642 * s ^ 18
    + 132254 * s ^ 17
    + 4235 * s ^ 16
    - 73304 * s ^ 15
    + 80381 * s ^ 14
    - 55224 * s ^ 13
    + 26578 * s ^ 12
    - 9551 * s ^ 11
    + 2443 * s ^ 10
    - 397 * s ^ 9
    + 33 * s ^ 8
    + s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 35
    + 20 * s ^ 34
    - 202 * s ^ 33
    + 1190 * s ^ 32
    - 4423 * s ^ 31
    + 10999 * s ^ 30
    - 20033 * s ^ 29
    + 35792 * s ^ 28
    - 88361 * s ^ 27
    + 251001 * s ^ 26
    - 610849 * s ^ 25
    + 1178435 * s ^ 24
    - 1805295 * s ^ 23
    + 2186067 * s ^ 22
    - 1964253 * s ^ 21
    + 979841 * s ^ 20
    + 578191 * s ^ 19
    - 2183526 * s ^ 18
    + 3236293 * s ^ 17
    - 3423552 * s ^ 16
    + 2824080 * s ^ 15
    - 1853169 * s ^ 14
    + 954867 * s ^ 13
    - 370491 * s ^ 12
    + 103294 * s ^ 11
    - 15573 * s ^ 10
    - 1389 * s ^ 9
    + 1349 * s ^ 8
    - 333 * s ^ 7
    + 33 * s ^ 6
    - 2 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 36
    + 17 * s ^ 35
    - 126 * s ^ 34
    + 462 * s ^ 33
    - 276 * s ^ 32
    - 4679 * s ^ 31
    + 18156 * s ^ 30
    - 7598 * s ^ 29
    - 166654 * s ^ 28
    + 757932 * s ^ 27
    - 1930330 * s ^ 26
    + 3335274 * s ^ 25
    - 3794465 * s ^ 24
    + 1505819 * s ^ 23
    + 5187453 * s ^ 22
    - 16641348 * s ^ 21
    + 30849744 * s ^ 20
    - 43756391 * s ^ 19
    + 50798214 * s ^ 18
    - 49359880 * s ^ 17
    + 40274198 * s ^ 16
    - 27168178 * s ^ 15
    + 14691691 * s ^ 14
    - 5934845 * s ^ 13
    + 1459676 * s ^ 12
    + 27132 * s ^ 11
    - 234463 * s ^ 10
    + 123720 * s ^ 9
    - 36026 * s ^ 8
    + 6200 * s ^ 7
    - 427 * s ^ 6
    - 5 * s ^ 5
    + 4 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 36
    + 32 * s ^ 35
    - 359 * s ^ 34
    + 1984 * s ^ 33
    - 4130 * s ^ 32
    - 18597 * s ^ 31
    + 184041 * s ^ 30
    - 751552 * s ^ 29
    + 1861360 * s ^ 28
    - 2631034 * s ^ 27
    - 125625 * s ^ 26
    + 12478420 * s ^ 25
    - 41977771 * s ^ 24
    + 94232803 * s ^ 23
    - 168544460 * s ^ 22
    + 253934567 * s ^ 21
    - 329029258 * s ^ 20
    + 369220564 * s ^ 19
    - 357681902 * s ^ 18
    + 295653796 * s ^ 17
    - 203023079 * s ^ 16
    + 108904368 * s ^ 15
    - 38426602 * s ^ 14
    + 742927 * s ^ 13
    + 10507370 * s ^ 12
    - 8665591 * s ^ 11
    + 4358958 * s ^ 10
    - 1496399 * s ^ 9
    + 334980 * s ^ 8
    - 39027 * s ^ 7
    - 1559 * s ^ 6
    + 869 * s ^ 5
    - 91 * s ^ 4
    - 2 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient8 (s : ℚ) : ℚ :=
  -3 * s ^ 36
    + 95 * s ^ 35
    - 1369 * s ^ 34
    + 11408 * s ^ 33
    - 59742 * s ^ 32
    + 187988 * s ^ 31
    - 189249 * s ^ 30
    - 1442936 * s ^ 29
    + 9758153 * s ^ 28
    - 35891821 * s ^ 27
    + 97461642 * s ^ 26
    - 214708693 * s ^ 25
    + 402239285 * s ^ 24
    - 658098291 * s ^ 23
    + 951734417 * s ^ 22
    - 1217398489 * s ^ 21
    + 1367721510 * s ^ 20
    - 1330320074 * s ^ 19
    + 1088074102 * s ^ 18
    - 701138925 * s ^ 17
    + 285559179 * s ^ 16
    + 38001835 * s ^ 15
    - 200805645 * s ^ 14
    + 216558566 * s ^ 13
    - 152618694 * s ^ 12
    + 79002191 * s ^ 11
    - 30778928 * s ^ 10
    + 8398216 * s ^ 9
    - 1264093 * s ^ 8
    - 52280 * s ^ 7
    + 72362 * s ^ 6
    - 12535 * s ^ 5
    + 753 * s ^ 4
    + 65 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient9 (s : ℚ) : ℚ :=
  -6 * s ^ 36
    + 230 * s ^ 35
    - 4090 * s ^ 34
    + 44826 * s ^ 33
    - 339652 * s ^ 32
    + 1899504 * s ^ 31
    - 8180377 * s ^ 30
    + 28010324 * s ^ 29
    - 78473509 * s ^ 28
    + 185020482 * s ^ 27
    - 377255618 * s ^ 26
    + 680548612 * s ^ 25
    - 1100893036 * s ^ 24
    + 1598252063 * s ^ 23
    - 2055113438 * s ^ 22
    + 2277814681 * s ^ 21
    - 2067326448 * s ^ 20
    + 1333680701 * s ^ 19
    - 186892710 * s ^ 18
    - 1058078828 * s ^ 17
    + 2004646951 * s ^ 16
    - 2360986339 * s ^ 15
    + 2102164263 * s ^ 14
    - 1476830236 * s ^ 13
    + 818618440 * s ^ 12
    - 350943895 * s ^ 11
    + 109711421 * s ^ 10
    - 18834382 * s ^ 9
    - 2011243 * s ^ 8
    + 2365252 * s ^ 7
    - 694202 * s ^ 6
    + 81791 * s ^ 5
    - 545 * s ^ 4
    - 986 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient10 (s : ℚ) : ℚ :=
  s ^ 38
    - 33 * s ^ 37
    + 552 * s ^ 36
    - 6112 * s ^ 35
    + 49341 * s ^ 34
    - 304037 * s ^ 33
    + 1468188 * s ^ 32
    - 5661005 * s ^ 31
    + 17725754 * s ^ 30
    - 45992202 * s ^ 29
    + 101653901 * s ^ 28
    - 198051814 * s ^ 27
    + 350192500 * s ^ 26
    - 563364949 * s ^ 25
    + 790187191 * s ^ 24
    - 859972443 * s ^ 23
    + 445633038 * s ^ 22
    + 835978178 * s ^ 21
    - 3192419026 * s ^ 20
    + 6422751116 * s ^ 19
    - 9819730694 * s ^ 18
    + 12327596954 * s ^ 17
    - 12993681638 * s ^ 16
    + 11498899429 * s ^ 15
    - 8447082093 * s ^ 14
    + 5044292246 * s ^ 13
    - 2350955873 * s ^ 12
    + 781499044 * s ^ 11
    - 122772129 * s ^ 10
    - 49007571 * s ^ 9
    + 44710605 * s ^ 8
    - 16807703 * s ^ 7
    + 3412420 * s ^ 6
    - 208297 * s ^ 5
    - 41752 * s ^ 4
    + 8856 * s ^ 3
    + 58 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient11 (s : ℚ) : ℚ :=
  -2 * s ^ 38
    + 56 * s ^ 37
    - 762 * s ^ 36
    + 6535 * s ^ 35
    - 38372 * s ^ 34
    + 155702 * s ^ 33
    - 400142 * s ^ 32
    + 322504 * s ^ 31
    + 2388975 * s ^ 30
    - 13749498 * s ^ 29
    + 43889047 * s ^ 28
    - 108416500 * s ^ 27
    + 249252031 * s ^ 26
    - 603836611 * s ^ 25
    + 1513900303 * s ^ 24
    - 3577085100 * s ^ 23
    + 7498393122 * s ^ 22
    - 13705594932 * s ^ 21
    + 21898264699 * s ^ 20
    - 30746176976 * s ^ 19
    + 37936147334 * s ^ 18
    - 40854125690 * s ^ 17
    + 37884216860 * s ^ 16
    - 29610562781 * s ^ 15
    + 18894452455 * s ^ 14
    - 9275305425 * s ^ 13
    + 2954281920 * s ^ 12
    - 52540154 * s ^ 11
    - 671884055 * s ^ 10
    + 519478656 * s ^ 9
    - 229795221 * s ^ 8
    + 63128665 * s ^ 7
    - 8403036 * s ^ 6
    - 720232 * s ^ 5
    + 408132 * s ^ 4
    - 50435 * s ^ 3
    - 1096 * s ^ 2
    + 24 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient12 (s : ℚ) : ℚ :=
  12 * s ^ 37
    - 341 * s ^ 36
    + 4754 * s ^ 35
    - 42627 * s ^ 34
    + 272601 * s ^ 33
    - 1311777 * s ^ 32
    + 4928671 * s ^ 31
    - 15071332 * s ^ 30
    + 40282966 * s ^ 29
    - 105441690 * s ^ 28
    + 295146675 * s ^ 27
    - 854544758 * s ^ 26
    + 2329452761 * s ^ 25
    - 5638057972 * s ^ 24
    + 11919515882 * s ^ 23
    - 22092553236 * s ^ 22
    + 36223694441 * s ^ 21
    - 52868334779 * s ^ 20
    + 68592557645 * s ^ 19
    - 78320649576 * s ^ 18
    + 77291567554 * s ^ 17
    - 64091701932 * s ^ 16
    + 42542624457 * s ^ 15
    - 20204757860 * s ^ 14
    + 3868638940 * s ^ 13
    + 4038499128 * s ^ 12
    - 5420584117 * s ^ 11
    + 3849215501 * s ^ 10
    - 1913265289 * s ^ 9
    + 651578248 * s ^ 8
    - 126762470 * s ^ 7
    - 1731177 * s ^ 6
    + 8745839 * s ^ 5
    - 2107938 * s ^ 4
    + 182275 * s ^ 3
    + 10759 * s ^ 2
    - 237 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient13 (s : ℚ) : ℚ :=
  s ^ 38
    - 30 * s ^ 37
    + 412 * s ^ 36
    - 3435 * s ^ 35
    + 19244 * s ^ 34
    - 77104 * s ^ 33
    + 256119 * s ^ 32
    - 1051406 * s ^ 31
    + 6186683 * s ^ 30
    - 35603444 * s ^ 29
    + 165425357 * s ^ 28
    - 612568586 * s ^ 27
    + 1854256991 * s ^ 26
    - 4720566880 * s ^ 25
    + 10369179508 * s ^ 24
    - 20074093911 * s ^ 23
    + 34759754206 * s ^ 22
    - 54131358730 * s ^ 21
    + 75371958807 * s ^ 20
    - 92244560968 * s ^ 19
    + 96507443701 * s ^ 18
    - 82476048646 * s ^ 17
    + 52101050038 * s ^ 16
    - 15821301908 * s ^ 15
    - 13117634485 * s ^ 14
    + 26889089670 * s ^ 13
    - 26505702715 * s ^ 12
    + 18666565694 * s ^ 11
    - 10073076731 * s ^ 10
    + 4038650198 * s ^ 9
    - 1002768528 * s ^ 8
    + 24227643 * s ^ 7
    + 95763087 * s ^ 6
    - 39963460 * s ^ 5
    + 6980767 * s ^ 4
    - 362371 * s ^ 3
    - 66081 * s ^ 2
    + 1274 * s
    + 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient14 (s : ℚ) : ℚ :=
  -3 * s ^ 37
    + 71 * s ^ 36
    - 665 * s ^ 35
    + 1629 * s ^ 34
    + 30944 * s ^ 33
    - 454572 * s ^ 32
    + 3513472 * s ^ 31
    - 19258791 * s ^ 30
    + 81978867 * s ^ 29
    - 284160538 * s ^ 28
    + 829977181 * s ^ 27
    - 2105010107 * s ^ 26
    + 4763267804 * s ^ 25
    - 9813501737 * s ^ 24
    + 18546174068 * s ^ 23
    - 31879611246 * s ^ 22
    + 48724746532 * s ^ 21
    - 63969586387 * s ^ 20
    + 68428130109 * s ^ 19
    - 53143922233 * s ^ 18
    + 16667212914 * s ^ 17
    + 30588153050 * s ^ 16
    - 70428600802 * s ^ 15
    + 88077829649 * s ^ 14
    - 81211733503 * s ^ 13
    + 59054232822 * s ^ 12
    - 34284760365 * s ^ 11
    + 15361848811 * s ^ 10
    - 4476247928 * s ^ 9
    + 87877107 * s ^ 8
    + 701072730 * s ^ 7
    - 398452690 * s ^ 6
    + 114133715 * s ^ 5
    - 15098254 * s ^ 4
    - 56040 * s ^ 3
    + 278354 * s ^ 2
    - 3798 * s
    - 170

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient15 (s : ℚ) : ℚ :=
  -2 * s ^ 37
    + 74 * s ^ 36
    - 1283 * s ^ 35
    + 14034 * s ^ 34
    - 109245 * s ^ 33
    + 645540 * s ^ 32
    - 3020616 * s ^ 31
    + 11597831 * s ^ 30
    - 38028387 * s ^ 29
    + 112032505 * s ^ 28
    - 312779319 * s ^ 27
    + 850008740 * s ^ 26
    - 2205049921 * s ^ 25
    + 5207861858 * s ^ 24
    - 10670537714 * s ^ 23
    + 18119506820 * s ^ 22
    - 23865112913 * s ^ 21
    + 20206201372 * s ^ 20
    + 1635973803 * s ^ 19
    - 44686410063 * s ^ 18
    + 100133349162 * s ^ 17
    - 148545622140 * s ^ 16
    + 170248319780 * s ^ 15
    - 157867584159 * s ^ 14
    + 120130163763 * s ^ 13
    - 74345224371 * s ^ 12
    + 35610733599 * s ^ 11
    - 10690625576 * s ^ 10
    - 1032604661 * s ^ 9
    + 3722042752 * s ^ 8
    - 2498445508 * s ^ 7
    + 972548212 * s ^ 6
    - 220243383 * s ^ 5
    + 18212092 * s ^ 4
    + 3026162 * s ^ 3
    - 843207 * s ^ 2
    + 3419 * s
    + 950

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient16 (s : ℚ) : ℚ :=
  4 * s ^ 36
    - 126 * s ^ 35
    + 1885 * s ^ 34
    - 17685 * s ^ 33
    + 114327 * s ^ 32
    - 516287 * s ^ 31
    + 1471390 * s ^ 30
    - 864541 * s ^ 29
    - 17081298 * s ^ 28
    + 113558888 * s ^ 27
    - 445913592 * s ^ 26
    + 1269030621 * s ^ 25
    - 2691979451 * s ^ 24
    + 3941431065 * s ^ 23
    - 2219189491 * s ^ 22
    - 7873683534 * s ^ 21
    + 32650924080 * s ^ 20
    - 74707988849 * s ^ 19
    + 127783278457 * s ^ 18
    - 175997413592 * s ^ 17
    + 200526918262 * s ^ 16
    - 190677963927 * s ^ 15
    + 150741346130 * s ^ 14
    - 96543457157 * s ^ 13
    + 45608456274 * s ^ 12
    - 9234959914 * s ^ 11
    - 9695247900 * s ^ 10
    + 14235465199 * s ^ 9
    - 10486529893 * s ^ 8
    + 5052851653 * s ^ 7
    - 1601137755 * s ^ 6
    + 274845844 * s ^ 5
    + 3683682 * s ^ 4
    - 11323679 * s ^ 3
    + 1871636 * s ^ 2
    + 22981 * s
    - 3707

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient17 (s : ℚ) : ℚ :=
  s ^ 36
    - 40 * s ^ 35
    + 756 * s ^ 34
    - 9113 * s ^ 33
    + 79160 * s ^ 32
    - 527556 * s ^ 31
    + 2790543 * s ^ 30
    - 11903860 * s ^ 29
    + 40946402 * s ^ 28
    - 110895988 * s ^ 27
    + 216927550 * s ^ 26
    - 193166566 * s ^ 25
    - 606325301 * s ^ 24
    + 3772642493 * s ^ 23
    - 12073224221 * s ^ 22
    + 28709793438 * s ^ 21
    - 55124294464 * s ^ 20
    + 88183054835 * s ^ 19
    - 119058432861 * s ^ 18
    + 135960002952 * s ^ 17
    - 130267293285 * s ^ 16
    + 102053066239 * s ^ 15
    - 60208894227 * s ^ 14
    + 17215009204 * s ^ 13
    + 16452142204 * s ^ 12
    - 35106356348 * s ^ 11
    + 38244168950 * s ^ 10
    - 29801560397 * s ^ 9
    + 17018110435 * s ^ 8
    - 6868772469 * s ^ 7
    + 1759480939 * s ^ 6
    - 150242117 * s ^ 5
    - 68547611 * s ^ 4
    + 25359630 * s ^ 3
    - 3011033 * s ^ 2
    - 128969 * s
    + 10695

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient18 (s : ℚ) : ℚ :=
  -s ^ 35
    + 34 * s ^ 34
    - 578 * s ^ 33
    + 6670 * s ^ 32
    - 59204 * s ^ 31
    + 429176 * s ^ 30
    - 2613141 * s ^ 29
    + 13529610 * s ^ 28
    - 59892253 * s ^ 27
    + 227337944 * s ^ 26
    - 741344180 * s ^ 25
    + 2079549090 * s ^ 24
    - 5020979691 * s ^ 23
    + 10433364075 * s ^ 22
    - 18635220982 * s ^ 21
    + 28504127077 * s ^ 20
    - 36981135194 * s ^ 19
    + 39735583333 * s ^ 18
    - 33134573839 * s ^ 17
    + 16486108127 * s ^ 16
    + 7254637198 * s ^ 15
    - 32929425858 * s ^ 14
    + 54976359657 * s ^ 13
    - 68251733705 * s ^ 12
    + 69093579865 * s ^ 11
    - 57311721743 * s ^ 10
    + 37702844994 * s ^ 9
    - 18584577927 * s ^ 8
    + 6249773575 * s ^ 7
    - 1040433942 * s ^ 6
    - 190935280 * s ^ 5
    + 163118475 * s ^ 4
    - 39324579 * s ^ 3
    + 3271897 * s ^ 2
    + 374857 * s
    - 23557

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient19 (s : ℚ) : ℚ :=
  -s ^ 34
    + 43 * s ^ 33
    - 856 * s ^ 32
    + 10671 * s ^ 31
    - 94411 * s ^ 30
    + 633772 * s ^ 29
    - 3357280 * s ^ 28
    + 14370320 * s ^ 27
    - 50370378 * s ^ 26
    + 145300710 * s ^ 25
    - 343404399 * s ^ 24
    + 651486763 * s ^ 23
    - 931427217 * s ^ 22
    + 765344353 * s ^ 21
    + 606711998 * s ^ 20
    - 4165507164 * s ^ 19
    + 10780070389 * s ^ 18
    - 20799994379 * s ^ 17
    + 33861508668 * s ^ 16
    - 48977544641 * s ^ 15
    + 64338559259 * s ^ 14
    - 76561496105 * s ^ 13
    + 80839815186 * s ^ 12
    - 73417881344 * s ^ 11
    + 55049533735 * s ^ 10
    - 32194709386 * s ^ 9
    + 13415780926 * s ^ 8
    - 3122726512 * s ^ 7
    - 292098727 * s ^ 6
    + 584490384 * s ^ 5
    - 233480846 * s ^ 4
    + 42864569 * s ^ 3
    - 1676537 * s ^ 2
    - 751878 * s
    + 40315

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient20 (s : ℚ) : ℚ :=
  s ^ 33
    - 37 * s ^ 32
    + 664 * s ^ 31
    - 7748 * s ^ 30
    + 66197 * s ^ 29
    - 440501 * s ^ 28
    + 2366902 * s ^ 27
    - 10509871 * s ^ 26
    + 39212799 * s ^ 25
    - 124645599 * s ^ 24
    + 342172044 * s ^ 23
    - 823667184 * s ^ 22
    + 1769665576 * s ^ 21
    - 3459325908 * s ^ 20
    + 6264693557 * s ^ 19
    - 10663908266 * s ^ 18
    + 17224233545 * s ^ 17
    - 26442910451 * s ^ 16
    + 38187071465 * s ^ 15
    - 50690323497 * s ^ 14
    + 60019537417 * s ^ 13
    - 61418554234 * s ^ 12
    + 52434053207 * s ^ 11
    - 35555345566 * s ^ 10
    + 17565276635 * s ^ 9
    - 4970261680 * s ^ 8
    - 493187107 * s ^ 7
    + 1375068061 * s ^ 6
    - 765323560 * s ^ 5
    + 225865112 * s ^ 4
    - 30407580 * s ^ 3
    - 1530395 * s ^ 2
    + 1120014 * s
    - 54012

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient21 (s : ℚ) : ℚ :=
  -s ^ 31
    + 27 * s ^ 30
    - 335 * s ^ 29
    + 2608 * s ^ 28
    - 15372 * s ^ 27
    + 83386 * s ^ 26
    - 472935 * s ^ 25
    + 2666177 * s ^ 24
    - 13396119 * s ^ 23
    + 56864304 * s ^ 22
    - 202443926 * s ^ 21
    + 611653287 * s ^ 20
    - 1595696131 * s ^ 19
    + 3651510645 * s ^ 18
    - 7396788486 * s ^ 17
    + 13262143642 * s ^ 16
    - 20870348076 * s ^ 15
    + 28435660905 * s ^ 14
    - 32962591663 * s ^ 13
    + 31712952225 * s ^ 12
    - 24257429243 * s ^ 11
    + 13454082346 * s ^ 10
    - 3925821847 * s ^ 9
    - 1244589209 * s ^ 8
    + 2342734085 * s ^ 7
    - 1554613842 * s ^ 6
    + 625183307 * s ^ 5
    - 143424674 * s ^ 4
    + 8732953 * s ^ 3
    + 4575969 * s ^ 2
    - 1270611 * s
    + 56604

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient22 (s : ℚ) : ℚ :=
  -s ^ 30
    + 39 * s ^ 29
    - 713 * s ^ 28
    + 8209 * s ^ 27
    - 67430 * s ^ 26
    + 424322 * s ^ 25
    - 2144952 * s ^ 24
    + 9021356 * s ^ 23
    - 32463722 * s ^ 22
    + 102221074 * s ^ 21
    - 286173989 * s ^ 20
    + 717641650 * s ^ 19
    - 1609281247 * s ^ 18
    + 3198522898 * s ^ 17
    - 5563426807 * s ^ 16
    + 8346836203 * s ^ 15
    - 10613955622 * s ^ 14
    + 11134420904 * s ^ 13
    - 9128920835 * s ^ 12
    + 5051480307 * s ^ 11
    - 637319871 * s ^ 10
    - 2207864472 * s ^ 9
    + 2832966983 * s ^ 8
    - 2041975565 * s ^ 7
    + 998159022 * s ^ 6
    - 318352773 * s ^ 5
    + 46517262 * s ^ 4
    + 8278012 * s ^ 3
    - 5606625 * s ^ 2
    + 1102364 * s
    - 45981

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient23 (s : ℚ) : ℚ :=
  2 * s ^ 28
    - 74 * s ^ 27
    + 1303 * s ^ 26
    - 14607 * s ^ 25
    + 117566 * s ^ 24
    - 725315 * s ^ 23
    + 3569292 * s ^ 22
    - 14366862 * s ^ 21
    + 48051447 * s ^ 20
    - 134795567 * s ^ 19
    + 318598969 * s ^ 18
    - 634472531 * s ^ 17
    + 1057883084 * s ^ 16
    - 1449596925 * s ^ 15
    + 1554472441 * s ^ 14
    - 1115145605 * s ^ 13
    + 91715914 * s ^ 12
    + 1169091753 * s ^ 11
    - 2065043600 * s ^ 10
    + 2187653610 * s ^ 9
    - 1653050493 * s ^ 8
    + 920225135 * s ^ 7
    - 360675793 * s ^ 6
    + 76486882 * s ^ 5
    + 9213265 * s ^ 4
    - 12916803 * s ^ 3
    + 4419064 * s ^ 2
    - 723955 * s
    + 28403

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient24 (s : ℚ) : ℚ :=
  -s ^ 26
    + 32 * s ^ 25
    - 477 * s ^ 24
    + 4403 * s ^ 23
    - 28160 * s ^ 22
    + 131640 * s ^ 21
    - 456846 * s ^ 20
    + 1130632 * s ^ 19
    - 1539259 * s ^ 18
    - 1990451 * s ^ 17
    + 20839871 * s ^ 16
    - 78865669 * s ^ 15
    + 208271668 * s ^ 14
    - 424157332 * s ^ 13
    + 683666807 * s ^ 12
    - 875506460 * s ^ 11
    + 886731925 * s ^ 10
    - 703652691 * s ^ 9
    + 428476987 * s ^ 8
    - 186648282 * s ^ 7
    + 40694829 * s ^ 6
    + 14873098 * s ^ 5
    - 18729222 * s ^ 4
    + 8800956 * s ^ 3
    - 2386134 * s ^ 2
    + 351036 * s
    - 12900

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient25 (s : ℚ) : ℚ :=
  3 * s ^ 23
    - 101 * s ^ 22
    + 1607 * s ^ 21
    - 16089 * s ^ 20
    + 113768 * s ^ 19
    - 603951 * s ^ 18
    + 2494636 * s ^ 17
    - 8189059 * s ^ 16
    + 21607401 * s ^ 15
    - 46003122 * s ^ 14
    + 78844766 * s ^ 13
    - 107912701 * s ^ 12
    + 116224435 * s ^ 11
    - 95797535 * s ^ 10
    + 56138226 * s ^ 9
    - 16106743 * s ^ 8
    - 10590170 * s ^ 7
    + 20433529 * s ^ 6
    - 17440119 * s ^ 5
    + 9603058 * s ^ 4
    - 3554465 * s ^ 3
    + 868676 * s ^ 2
    - 120112 * s
    + 4062

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient26 (s : ℚ) : ℚ :=
  -2 * s ^ 20
    + 62 * s ^ 19
    - 897 * s ^ 18
    + 8038 * s ^ 17
    - 49898 * s ^ 16
    + 227296 * s ^ 15
    - 785221 * s ^ 14
    + 2099412 * s ^ 13
    - 4407806 * s ^ 12
    + 7376598 * s ^ 11
    - 10063279 * s ^ 10
    + 11593930 * s ^ 9
    - 11745450 * s ^ 8
    + 10614178 * s ^ 7
    - 8248857 * s ^ 6
    + 5153268 * s ^ 5
    - 2435352 * s ^ 4
    + 836298 * s ^ 3
    - 198262 * s ^ 2
    + 26736 * s
    - 792

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient27 (s : ℚ) : ℚ :=
  2 * s ^ 16
    - 55 * s ^ 15
    + 692 * s ^ 14
    - 5275 * s ^ 13
    + 27199 * s ^ 12
    - 100316 * s ^ 11
    + 272916 * s ^ 10
    - 556603 * s ^ 9
    + 856242 * s ^ 8
    - 992307 * s ^ 7
    + 861198 * s ^ 6
    - 556196 * s ^ 5
    + 267017 * s ^ 4
    - 95144 * s ^ 3
    + 23846 * s ^ 2
    - 3288 * s
    + 72

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient28 (s : ℚ) : ℚ :=
  -s ^ 10
    + 18 * s ^ 9
    - 140 * s ^ 8
    + 616 * s ^ 7
    - 1685 * s ^ 6
    + 2962 * s ^ 5
    - 3334 * s ^ 4
    + 2308 * s ^ 3
    - 888 * s ^ 2
    + 144 * s

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
    multiplierCoefficient27 s * r ^ 27 +
    multiplierCoefficient28 s * r ^ 28

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
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient1 s *
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
    multiplierCoefficient25,
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
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient2 s *
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
    multiplierCoefficient26,
    multiplierCoefficient25,
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
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient3 s *
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
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25,
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
    sutherlandPolynomialCoefficient0 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient4 s *
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
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25,
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
    sutherlandPolynomialCoefficient1 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient5 s *
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
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25,
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
    sutherlandPolynomialCoefficient2 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient6 s *
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
    sutherlandPolynomialCoefficient2,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_31 (s : ℚ) :
    structuralNumeratorCoefficient31 s =
    sutherlandPolynomialCoefficient3 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient21 s
    := by
  simp only [structuralNumeratorCoefficient31,
    sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_32 (s : ℚ) :
    structuralNumeratorCoefficient32 s =
    sutherlandPolynomialCoefficient4 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient22 s
    := by
  simp only [structuralNumeratorCoefficient32,
    sutherlandPolynomialCoefficient4,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25,
    multiplierCoefficient24,
    multiplierCoefficient23,
    multiplierCoefficient22]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_33 (s : ℚ) :
    structuralNumeratorCoefficient33 s =
    sutherlandPolynomialCoefficient5 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient24 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient23 s
    := by
  simp only [structuralNumeratorCoefficient33,
    sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25,
    multiplierCoefficient24,
    multiplierCoefficient23]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_34 (s : ℚ) :
    structuralNumeratorCoefficient34 s =
    sutherlandPolynomialCoefficient6 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient25 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient24 s
    := by
  simp only [structuralNumeratorCoefficient34,
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25,
    multiplierCoefficient24]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_35 (s : ℚ) :
    structuralNumeratorCoefficient35 s =
    sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient26 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient25 s
    := by
  simp only [structuralNumeratorCoefficient35,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26,
    multiplierCoefficient25]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_36 (s : ℚ) :
    structuralNumeratorCoefficient36 s =
    sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient27 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient26 s
    := by
  simp only [structuralNumeratorCoefficient36,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28,
    multiplierCoefficient27,
    multiplierCoefficient26]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_37 (s : ℚ) :
    structuralNumeratorCoefficient37 s =
    sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient28 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient27 s
    := by
  simp only [structuralNumeratorCoefficient37,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28,
    multiplierCoefficient27]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_38 (s : ℚ) :
    structuralNumeratorCoefficient38 s =
    sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient28 s
    := by
  simp only [structuralNumeratorCoefficient38,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient28]
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
  have h35 := structuralNumeratorCoefficient_product_certificate_35 s
  have h36 := structuralNumeratorCoefficient_product_certificate_36 s
  have h37 := structuralNumeratorCoefficient_product_certificate_37 s
  have h38 := structuralNumeratorCoefficient_product_certificate_38 s
  simp only [structuralNumerator, sutherlandPolynomial, multiplier]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34 + r ^ 35 * h35 + r ^ 36 * h36 + r ^ 37 * h37 +
    r ^ 38 * h38

/-- The product of the five normalized raw units is one on the curve. -/
theorem relation_eq_zero
    (r s : ℚ)
    (hCurve : sutherlandPolynomial r s = 0)
    (hOne : rawUnitOneDenominator r s ≠ 0)
    (hTwo : rawUnitTwoDenominator r s ≠ 0)
    (hFour : rawUnitFourDenominator r s ≠ 0)
    (hEight : rawUnitEightDenominator r s ≠ 0)
    (hNine : rawUnitNineDenominator r s ≠ 0) :
    (rawUnitOneNumerator r s / rawUnitOneDenominator r s) *
          (rawUnitTwoNumerator r s / rawUnitTwoDenominator r s) *
          (rawUnitFourNumerator r s / rawUnitFourDenominator r s) *
          (rawUnitEightNumerator r s / rawUnitEightDenominator r s) *
          (rawUnitNineNumerator r s / rawUnitNineDenominator r s) -
        1 =
      0 := by
  have hStructural :=
    structuralNumerator_eq_sutherlandPolynomial_mul_multiplier r s
  simp only [structuralNumerator_eq_linearCombination,
    numeratorStep1_eq_rawUnitOneNumerator_mul_rawUnitTwoNumerator,
    numeratorStep2_eq_numeratorStep1_mul_rawUnitFourNumerator,
    numeratorStep3_eq_numeratorStep2_mul_rawUnitEightNumerator,
    numeratorProduct_eq_numeratorStep3_mul_rawUnitNineNumerator,
    denominatorStep1_eq_rawUnitOneDenominator_mul_rawUnitTwoDenominator,
    denominatorStep2_eq_denominatorStep1_mul_rawUnitFourDenominator,
    denominatorStep3_eq_denominatorStep2_mul_rawUnitEightDenominator,
    denominatorProduct_eq_denominatorStep3_mul_rawUnitNineDenominator] at hStructural
  rw [hCurve, zero_mul] at hStructural
  field_simp [hOne, hTwo, hFour, hEight, hNine]
  linear_combination hStructural

end MazurTorsion.Kubert.OrderTwentyFiveRawOrbitNormData
