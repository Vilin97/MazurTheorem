/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveRawOrbitData

/-!
# Second exact raw-orbit certificate for order twenty-five

This coefficientwise certificate proves the second independent cyclic
unit relation used by the order-twenty-five Tate bridge. Exact polynomial
division over `ℚ` discovered the quotient; Lean checks every coefficient
and every staged polynomial product.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawOrbitRelationTwoData

open OrderTwentyFiveRawOrbitData

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 15
    + 3 * s ^ 14
    - 6 * s ^ 13
    + 8 * s ^ 12
    - 8 * s ^ 11
    + 6 * s ^ 10
    - 3 * s ^ 9
    + s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 18
    + 8 * s ^ 17
    - 33 * s ^ 16
    + 87 * s ^ 15
    - 148 * s ^ 14
    + 186 * s ^ 13
    - 160 * s ^ 12
    + 82 * s ^ 11
    + 12 * s ^ 10
    - 75 * s ^ 9
    + 80 * s ^ 8
    - 54 * s ^ 7
    + 21 * s ^ 6
    - 6 * s ^ 5
    + s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient3 (s : ℚ) : ℚ :=
  2 * s ^ 20
    - 19 * s ^ 19
    + 93 * s ^ 18
    - 289 * s ^ 17
    + 609 * s ^ 16
    - 839 * s ^ 15
    + 569 * s ^ 14
    + 405 * s ^ 13
    - 1967 * s ^ 12
    + 3434 * s ^ 11
    - 4178 * s ^ 10
    + 3848 * s ^ 9
    - 2698 * s ^ 8
    + 1444 * s ^ 7
    - 540 * s ^ 6
    + 150 * s ^ 5
    - 24 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 22
    + 12 * s ^ 21
    - 69 * s ^ 20
    + 229 * s ^ 19
    - 416 * s ^ 18
    - 17 * s ^ 17
    + 2730 * s ^ 16
    - 9987 * s ^ 15
    + 22786 * s ^ 14
    - 39057 * s ^ 13
    + 54126 * s ^ 12
    - 61836 * s ^ 11
    + 58919 * s ^ 10
    - 46074 * s ^ 9
    + 28904 * s ^ 8
    - 14170 * s ^ 7
    + 5060 * s ^ 6
    - 1326 * s ^ 5
    + 174 * s ^ 4
    + 14 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient5 (s : ℚ) : ℚ :=
  -4 * s ^ 22
    + 66 * s ^ 21
    - 524 * s ^ 20
    + 2694 * s ^ 19
    - 10066 * s ^ 18
    + 29144 * s ^ 17
    - 67870 * s ^ 16
    + 130520 * s ^ 15
    - 211674 * s ^ 14
    + 294705 * s ^ 13
    - 355231 * s ^ 12
    + 368432 * s ^ 11
    - 325304 * s ^ 10
    + 238076 * s ^ 9
    - 140528 * s ^ 8
    + 64409 * s ^ 7
    - 21209 * s ^ 6
    + 4712 * s ^ 5
    - 110 * s ^ 4
    - 256 * s ^ 3
    + 18 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient6 (s : ℚ) : ℚ :=
  s ^ 24
    - 18 * s ^ 23
    + 164 * s ^ 22
    - 984 * s ^ 21
    + 4335 * s ^ 20
    - 14932 * s ^ 19
    + 41918 * s ^ 18
    - 98826 * s ^ 17
    + 200067 * s ^ 16
    - 354090 * s ^ 15
    + 554219 * s ^ 14
    - 767831 * s ^ 13
    + 929782 * s ^ 12
    - 964346 * s ^ 11
    + 838497 * s ^ 10
    - 591722 * s ^ 9
    + 327992 * s ^ 8
    - 133603 * s ^ 7
    + 33246 * s ^ 6
    - 1126 * s ^ 5
    - 4509 * s ^ 4
    + 1884 * s ^ 3
    - 116 * s ^ 2
    - 2 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient7 (s : ℚ) : ℚ :=
  -s ^ 23
    + 11 * s ^ 22
    - 46 * s ^ 21
    - 34 * s ^ 20
    + 1498 * s ^ 19
    - 9766 * s ^ 18
    + 40101 * s ^ 17
    - 122817 * s ^ 16
    + 298182 * s ^ 15
    - 587066 * s ^ 14
    + 942755 * s ^ 13
    - 1231635 * s ^ 12
    + 1300264 * s ^ 11
    - 1090272 * s ^ 10
    + 694747 * s ^ 9
    - 307205 * s ^ 8
    + 56652 * s ^ 7
    + 39456 * s ^ 6
    - 43847 * s ^ 5
    + 26045 * s ^ 4
    - 7343 * s ^ 3
    + 293 * s ^ 2
    + 28 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient8 (s : ℚ) : ℚ :=
  -s ^ 23
    + 20 * s ^ 22
    - 194 * s ^ 21
    + 1242 * s ^ 20
    - 5894 * s ^ 19
    + 22087 * s ^ 18
    - 67685 * s ^ 17
    + 172151 * s ^ 16
    - 363514 * s ^ 15
    + 631774 * s ^ 14
    - 892401 * s ^ 13
    + 1004607 * s ^ 12
    - 864360 * s ^ 11
    + 496897 * s ^ 10
    - 67305 * s ^ 9
    - 228781 * s ^ 8
    + 326632 * s ^ 7
    - 269435 * s ^ 6
    + 161181 * s ^ 5
    - 73733 * s ^ 4
    + 16751 * s ^ 3
    + 120 * s ^ 2
    - 158 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient9 (s : ℚ) : ℚ :=
  5 * s ^ 21
    - 85 * s ^ 20
    + 696 * s ^ 19
    - 3632 * s ^ 18
    + 13186 * s ^ 17
    - 34212 * s ^ 16
    + 61997 * s ^ 15
    - 67619 * s ^ 14
    - 815 * s ^ 13
    + 186321 * s ^ 12
    - 477099 * s ^ 11
    + 786005 * s ^ 10
    - 980039 * s ^ 9
    + 977813 * s ^ 8
    - 810774 * s ^ 7
    + 552610 * s ^ 6
    - 307216 * s ^ 5
    + 126932 * s ^ 4
    - 21791 * s ^ 3
    - 2777 * s ^ 2
    + 484 * s
    + 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient10 (s : ℚ) : ℚ :=
  s ^ 21
    - 22 * s ^ 20
    + 226 * s ^ 19
    - 1490 * s ^ 18
    + 7108 * s ^ 17
    - 25896 * s ^ 16
    + 74507 * s ^ 15
    - 173974 * s ^ 14
    + 338799 * s ^ 13
    - 564434 * s ^ 12
    + 817257 * s ^ 11
    - 1032812 * s ^ 10
    + 1138493 * s ^ 9
    - 1101680 * s ^ 8
    + 930126 * s ^ 7
    - 656479 * s ^ 6
    + 369484 * s ^ 5
    - 136707 * s ^ 4
    + 10061 * s ^ 3
    + 8343 * s ^ 2
    - 866 * s
    - 45

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient11 (s : ℚ) : ℚ :=
  -2 * s ^ 19
    + 34 * s ^ 18
    - 274 * s ^ 17
    + 1488 * s ^ 16
    - 6319 * s ^ 15
    + 22057 * s ^ 14
    - 63555 * s ^ 13
    + 149957 * s ^ 12
    - 290104 * s ^ 11
    + 467024 * s ^ 10
    - 636890 * s ^ 9
    + 738468 * s ^ 8
    - 706962 * s ^ 7
    + 532174 * s ^ 6
    - 291366 * s ^ 5
    + 80366 * s ^ 4
    + 16463 * s ^ 3
    - 13497 * s ^ 2
    + 819 * s
    + 119

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient12 (s : ℚ) : ℚ :=
  -s ^ 18
    + 24 * s ^ 17
    - 249 * s ^ 16
    + 1539 * s ^ 15
    - 6566 * s ^ 14
    + 21105 * s ^ 13
    - 54220 * s ^ 12
    + 116078 * s ^ 11
    - 210916 * s ^ 10
    + 322374 * s ^ 9
    - 402439 * s ^ 8
    + 393374 * s ^ 7
    - 283969 * s ^ 6
    + 125832 * s ^ 5
    + 1065 * s ^ 4
    - 35745 * s ^ 3
    + 12981 * s ^ 2
    - 65 * s
    - 202

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient13 (s : ℚ) : ℚ :=
  2 * s ^ 16
    - 42 * s ^ 15
    + 396 * s ^ 14
    - 2267 * s ^ 13
    + 8941 * s ^ 12
    - 25847 * s ^ 11
    + 56363 * s ^ 10
    - 93667 * s ^ 9
    + 117699 * s ^ 8
    - 107101 * s ^ 7
    + 58921 * s ^ 6
    + 3764 * s ^ 5
    - 40320 * s ^ 4
    + 30363 * s ^ 3
    - 6597 * s ^ 2
    - 833 * s
    + 225

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient14 (s : ℚ) : ℚ :=
  -s ^ 14
    + 17 * s ^ 13
    - 125 * s ^ 12
    + 531 * s ^ 11
    - 1447 * s ^ 10
    + 2481 * s ^ 9
    - 1698 * s ^ 8
    - 4123 * s ^ 7
    + 15936 * s ^ 6
    - 27016 * s ^ 5
    + 25435 * s ^ 4
    - 11339 * s ^ 3
    + 480 * s ^ 2
    + 1029 * s
    - 160

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient15 (s : ℚ) : ℚ :=
  2 * s ^ 11
    - 34 * s ^ 10
    + 252 * s ^ 9
    - 1082 * s ^ 8
    + 2995 * s ^ 7
    - 5509 * s ^ 6
    + 6452 * s ^ 5
    - 4026 * s ^ 4
    + 287 * s ^ 3
    + 1151 * s ^ 2
    - 554 * s
    + 66

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step1Coefficient16 (s : ℚ) : ℚ :=
  -s ^ 8
    + 15 * s ^ 7
    - 93 * s ^ 6
    + 308 * s ^ 5
    - 588 * s ^ 4
    + 651 * s ^ 3
    - 398 * s ^ 2
    + 118 * s
    - 12

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
    t1Step1Coefficient14 s * r ^ 14 +
    t1Step1Coefficient15 s * r ^ 15 +
    t1Step1Coefficient16 s * r ^ 16

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_0 (s : ℚ) :
    t1Step1Coefficient0 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient0,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_1 (s : ℚ) :
    t1Step1Coefficient1 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient1,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_2 (s : ℚ) :
    t1Step1Coefficient2 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient2,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_3 (s : ℚ) :
    t1Step1Coefficient3 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient3,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_4 (s : ℚ) :
    t1Step1Coefficient4 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient4,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_5 (s : ℚ) :
    t1Step1Coefficient5 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient5,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_6 (s : ℚ) :
    t1Step1Coefficient6 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient6,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_7 (s : ℚ) :
    t1Step1Coefficient7 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient7,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
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
theorem t1Step1Coefficient_product_certificate_8 (s : ℚ) :
    t1Step1Coefficient8 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t1Step1Coefficient8,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
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
theorem t1Step1Coefficient_product_certificate_9 (s : ℚ) :
    t1Step1Coefficient9 s =
    rawUnitFourNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient1 s
    := by
  simp only [t1Step1Coefficient9,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
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
theorem t1Step1Coefficient_product_certificate_10 (s : ℚ) :
    t1Step1Coefficient10 s =
    rawUnitFourNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient2 s
    := by
  simp only [t1Step1Coefficient10,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_11 (s : ℚ) :
    t1Step1Coefficient11 s =
    rawUnitFourNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient3 s
    := by
  simp only [t1Step1Coefficient11,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_12 (s : ℚ) :
    t1Step1Coefficient12 s =
    rawUnitFourNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient4 s
    := by
  simp only [t1Step1Coefficient12,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_13 (s : ℚ) :
    t1Step1Coefficient13 s =
    rawUnitFourNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient5 s
    := by
  simp only [t1Step1Coefficient13,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_14 (s : ℚ) :
    t1Step1Coefficient14 s =
    rawUnitFourNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient6 s
    := by
  simp only [t1Step1Coefficient14,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_15 (s : ℚ) :
    t1Step1Coefficient15 s =
    rawUnitFourNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient7 s
    := by
  simp only [t1Step1Coefficient15,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step1Coefficient_product_certificate_16 (s : ℚ) :
    t1Step1Coefficient16 s =
    rawUnitFourNumeratorCoefficient8 s *
        rawUnitFourDenominatorCoefficient8 s
    := by
  simp only [t1Step1Coefficient16,
    rawUnitFourNumeratorCoefficient8,
    rawUnitFourDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step1_eq_rawUnitFourNumerator_mul_rawUnitFourDenominator (r s : ℚ) :
    t1Step1 r s = rawUnitFourNumerator r s * rawUnitFourDenominator r s := by
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
  have h15 := t1Step1Coefficient_product_certificate_15 s
  have h16 := t1Step1Coefficient_product_certificate_16 s
  simp only [t1Step1, rawUnitFourNumerator, rawUnitFourDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 23
    + 3 * s ^ 22
    - 6 * s ^ 21
    + 8 * s ^ 20
    - 8 * s ^ 19
    + 6 * s ^ 18
    - 3 * s ^ 17
    + s ^ 16

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 26
    + 8 * s ^ 25
    - 33 * s ^ 24
    + 84 * s ^ 23
    - 122 * s ^ 22
    + 107 * s ^ 21
    + 2 * s ^ 20
    - 159 * s ^ 19
    + 292 * s ^ 18
    - 335 * s ^ 17
    + 272 * s ^ 16
    - 169 * s ^ 15
    + 75 * s ^ 14
    - 27 * s ^ 13
    + 7 * s ^ 12
    - s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient3 (s : ℚ) : ℚ :=
  2 * s ^ 28
    - 19 * s ^ 27
    + 89 * s ^ 26
    - 239 * s ^ 25
    + 319 * s ^ 24
    + 226 * s ^ 23
    - 2127 * s ^ 22
    + 5274 * s ^ 21
    - 8690 * s ^ 20
    + 10488 * s ^ 19
    - 9681 * s ^ 18
    + 6513 * s ^ 17
    - 2539 * s ^ 16
    - 360 * s ^ 15
    + 1602 * s ^ 14
    - 1469 * s ^ 13
    + 933 * s ^ 12
    - 450 * s ^ 11
    + 165 * s ^ 10
    - 45 * s ^ 9
    + 9 * s ^ 8
    - s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 30
    + 11 * s ^ 29
    - 49 * s ^ 28
    + 36 * s ^ 27
    + 709 * s ^ 26
    - 4488 * s ^ 25
    + 15536 * s ^ 24
    - 37005 * s ^ 23
    + 64184 * s ^ 22
    - 81909 * s ^ 21
    + 73949 * s ^ 20
    - 32481 * s ^ 19
    - 30012 * s ^ 18
    + 90033 * s ^ 17
    - 123204 * s ^ 16
    + 120284 * s ^ 15
    - 92516 * s ^ 14
    + 57368 * s ^ 13
    - 29739 * s ^ 12
    + 12647 * s ^ 11
    - 4263 * s ^ 10
    + 1087 * s ^ 9
    - 192 * s ^ 8
    + 13 * s ^ 7
    + 2 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient5 (s : ℚ) : ℚ :=
  2 * s ^ 31
    - 38 * s ^ 30
    + 368 * s ^ 29
    - 2289 * s ^ 28
    + 10021 * s ^ 27
    - 32147 * s ^ 26
    + 76434 * s ^ 25
    - 130175 * s ^ 24
    + 133471 * s ^ 23
    + 18934 * s ^ 22
    - 413706 * s ^ 21
    + 1035409 * s ^ 20
    - 1742996 * s ^ 19
    + 2300738 * s ^ 18
    - 2512612 * s ^ 17
    + 2305215 * s ^ 16
    - 1788749 * s ^ 15
    + 1180745 * s ^ 14
    - 661408 * s ^ 13
    + 316183 * s ^ 12
    - 123944 * s ^ 11
    + 37609 * s ^ 10
    - 7947 * s ^ 9
    + 748 * s ^ 8
    + 204 * s ^ 7
    - 70 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 33
    + 19 * s ^ 32
    - 180 * s ^ 31
    + 1093 * s ^ 30
    - 4561 * s ^ 29
    + 12624 * s ^ 28
    - 16358 * s ^ 27
    - 41927 * s ^ 26
    + 338363 * s ^ 25
    - 1221474 * s ^ 24
    + 3134856 * s ^ 23
    - 6336856 * s ^ 22
    + 10566979 * s ^ 21
    - 14973511 * s ^ 20
    + 18363562 * s ^ 19
    - 19629124 * s ^ 18
    + 18327539 * s ^ 17
    - 14868155 * s ^ 16
    + 10453756 * s ^ 15
    - 6359286 * s ^ 14
    + 3317670 * s ^ 13
    - 1461281 * s ^ 12
    + 495879 * s ^ 11
    - 107178 * s ^ 10
    + 1038 * s ^ 9
    + 10400 * s ^ 8
    - 4698 * s ^ 7
    + 774 * s ^ 6
    + 40 * s ^ 5
    - 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient7 (s : ℚ) : ℚ :=
  -4 * s ^ 33
    + 95 * s ^ 32
    - 1109 * s ^ 31
    + 8528 * s ^ 30
    - 48416 * s ^ 29
    + 214962 * s ^ 28
    - 771364 * s ^ 27
    + 2284970 * s ^ 26
    - 5673367 * s ^ 25
    + 11953295 * s ^ 24
    - 21614931 * s ^ 23
    + 33961897 * s ^ 22
    - 46987945 * s ^ 21
    + 57876921 * s ^ 20
    - 63662188 * s ^ 19
    + 62218152 * s ^ 18
    - 53595782 * s ^ 17
    + 40259781 * s ^ 16
    - 26292493 * s ^ 15
    + 14794589 * s ^ 14
    - 6914632 * s ^ 13
    + 2386066 * s ^ 12
    - 244693 * s ^ 11
    - 335423 * s ^ 10
    + 275698 * s ^ 9
    - 122709 * s ^ 8
    + 33673 * s ^ 7
    - 2697 * s ^ 6
    - 910 * s ^ 5
    + 35 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient8 (s : ℚ) : ℚ :=
  s ^ 35
    - 24 * s ^ 34
    + 293 * s ^ 33
    - 2388 * s ^ 32
    + 14472 * s ^ 31
    - 69042 * s ^ 30
    + 268104 * s ^ 29
    - 865102 * s ^ 28
    + 2351837 * s ^ 27
    - 5446493 * s ^ 26
    + 10866949 * s ^ 25
    - 18952050 * s ^ 24
    + 29469891 * s ^ 23
    - 41825013 * s ^ 22
    + 55038200 * s ^ 21
    - 66749589 * s ^ 20
    + 72635490 * s ^ 19
    - 68893702 * s ^ 18
    + 55835773 * s ^ 17
    - 38117497 * s ^ 16
    + 21713453 * s ^ 15
    - 9070600 * s ^ 14
    + 539740 * s ^ 13
    + 3965205 * s ^ 12
    - 4954140 * s ^ 11
    + 3443929 * s ^ 10
    - 1646281 * s ^ 9
    + 553986 * s ^ 8
    - 101325 * s ^ 7
    - 12598 * s ^ 6
    + 8680 * s ^ 5
    - 130 * s ^ 4
    - 29 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient9 (s : ℚ) : ℚ :=
  -3 * s ^ 34
    + 62 * s ^ 33
    - 662 * s ^ 32
    + 4792 * s ^ 31
    - 26197 * s ^ 30
    + 114148 * s ^ 29
    - 406555 * s ^ 28
    + 1192067 * s ^ 27
    - 2859953 * s ^ 26
    + 5497661 * s ^ 25
    - 8039912 * s ^ 24
    + 7630092 * s ^ 23
    - 823002 * s ^ 22
    - 12567096 * s ^ 21
    + 26374975 * s ^ 20
    - 31611560 * s ^ 19
    + 25100441 * s ^ 18
    - 12123505 * s ^ 17
    - 73113 * s ^ 16
    + 9374090 * s ^ 15
    - 18899743 * s ^ 14
    + 26843991 * s ^ 13
    - 28478972 * s ^ 12
    + 22319375 * s ^ 11
    - 12264831 * s ^ 10
    + 4813064 * s ^ 9
    - 1176003 * s ^ 8
    - 35576 * s ^ 7
    + 168160 * s ^ 6
    - 45087 * s ^ 5
    - 1492 * s ^ 4
    + 342 * s ^ 3
    + 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient10 (s : ℚ) : ℚ :=
  -s ^ 34
    + 27 * s ^ 33
    - 336 * s ^ 32
    + 2736 * s ^ 31
    - 16812 * s ^ 30
    + 84140 * s ^ 29
    - 356405 * s ^ 28
    + 1293285 * s ^ 27
    - 4010934 * s ^ 26
    + 10549615 * s ^ 25
    - 23293092 * s ^ 24
    + 42551039 * s ^ 23
    - 62872507 * s ^ 22
    + 72442065 * s ^ 21
    - 60944115 * s ^ 20
    + 31615903 * s ^ 19
    - 1267680 * s ^ 18
    - 17255568 * s ^ 17
    + 28772414 * s ^ 16
    - 47920024 * s ^ 15
    + 76863097 * s ^ 14
    - 95110225 * s ^ 13
    + 86897473 * s ^ 12
    - 57139297 * s ^ 11
    + 25373981 * s ^ 10
    - 6918624 * s ^ 9
    - 200808 * s ^ 8
    + 1532207 * s ^ 7
    - 820484 * s ^ 6
    + 131060 * s ^ 5
    + 20117 * s ^ 4
    - 2203 * s ^ 3
    - 44 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient11 (s : ℚ) : ℚ :=
  s ^ 33
    - 10 * s ^ 32
    - 40 * s ^ 31
    + 1264 * s ^ 30
    - 10443 * s ^ 29
    + 48344 * s ^ 28
    - 126509 * s ^ 27
    + 48739 * s ^ 26
    + 1228834 * s ^ 25
    - 6723882 * s ^ 24
    + 21941972 * s ^ 23
    - 51944952 * s ^ 22
    + 93229467 * s ^ 21
    - 127064437 * s ^ 20
    + 129379238 * s ^ 19
    - 98441151 * s ^ 18
    + 69424764 * s ^ 17
    - 86775832 * s ^ 16
    + 156302119 * s ^ 15
    - 227086063 * s ^ 14
    + 235808193 * s ^ 13
    - 174755512 * s ^ 12
    + 86779260 * s ^ 11
    - 21599786 * s ^ 10
    - 5015094 * s ^ 9
    + 10037906 * s ^ 8
    - 6780329 * s ^ 7
    + 2330625 * s ^ 6
    - 127431 * s ^ 5
    - 118189 * s ^ 4
    + 8505 * s ^ 3
    + 428 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient12 (s : ℚ) : ℚ :=
  5 * s ^ 32
    - 156 * s ^ 31
    + 2176 * s ^ 30
    - 18678 * s ^ 29
    + 112546 * s ^ 28
    - 508626 * s ^ 27
    + 1785498 * s ^ 26
    - 4931291 * s ^ 25
    + 10560477 * s ^ 24
    - 16320090 * s ^ 23
    + 13152066 * s ^ 22
    + 13887636 * s ^ 21
    - 71374123 * s ^ 20
    + 133544765 * s ^ 19
    - 138402933 * s ^ 18
    + 31056287 * s ^ 17
    + 172766436 * s ^ 16
    - 371197547 * s ^ 15
    + 442084258 * s ^ 14
    - 349099816 * s ^ 13
    + 173033875 * s ^ 12
    - 22396301 * s ^ 11
    - 46205126 * s ^ 10
    + 51034589 * s ^ 9
    - 35282802 * s ^ 8
    + 16613833 * s ^ 7
    - 3667854 * s ^ 6
    - 644378 * s ^ 5
    + 436052 * s ^ 4
    - 18266 * s ^ 3
    - 2495 * s ^ 2
    - 17 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient13 (s : ℚ) : ℚ :=
  s ^ 32
    - 40 * s ^ 31
    + 690 * s ^ 30
    - 7150 * s ^ 29
    + 51561 * s ^ 28
    - 280832 * s ^ 27
    + 1214329 * s ^ 26
    - 4300500 * s ^ 25
    + 12670136 * s ^ 24
    - 31022869 * s ^ 23
    + 61808603 * s ^ 22
    - 94972066 * s ^ 21
    + 96541811 * s ^ 20
    - 15272690 * s ^ 19
    - 177189643 * s ^ 18
    + 435940623 * s ^ 17
    - 638825348 * s ^ 16
    + 656930268 * s ^ 15
    - 458388192 * s ^ 14
    + 152905897 * s ^ 13
    + 96010170 * s ^ 12
    - 202513296 * s ^ 11
    + 185879467 * s ^ 10
    - 123647159 * s ^ 9
    + 66849543 * s ^ 8
    - 23250255 * s ^ 7
    + 429757 * s ^ 6
    + 3513115 * s ^ 5
    - 1090156 * s ^ 4
    + 4308 * s ^ 3
    + 9779 * s ^ 2
    + 138 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient14 (s : ℚ) : ℚ :=
  -2 * s ^ 31
    + 59 * s ^ 30
    - 801 * s ^ 29
    + 6848 * s ^ 28
    - 42702 * s ^ 27
    + 213581 * s ^ 26
    - 917568 * s ^ 25
    + 3521067 * s ^ 24
    - 12097138 * s ^ 23
    + 36337588 * s ^ 22
    - 92718560 * s ^ 21
    + 196528071 * s ^ 20
    - 340524029 * s ^ 19
    + 474018782 * s ^ 18
    - 511407614 * s ^ 17
    + 382124982 * s ^ 16
    - 94405828 * s ^ 15
    - 240781626 * s ^ 14
    + 471432984 * s ^ 13
    - 520495480 * s ^ 12
    + 427034786 * s ^ 11
    - 282325444 * s ^ 10
    + 159293299 * s ^ 9
    - 69960041 * s ^ 8
    + 9055260 * s ^ 7
    + 13325009 * s ^ 6
    - 9122159 * s ^ 5
    + 1820337 * s ^ 4
    + 113895 * s ^ 3
    - 26845 * s ^ 2
    - 711 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient15 (s : ℚ) : ℚ :=
  16 * s ^ 29
    - 455 * s ^ 28
    + 6074 * s ^ 27
    - 50945 * s ^ 26
    + 300936 * s ^ 25
    - 1318853 * s ^ 24
    + 4370377 * s ^ 23
    - 10861369 * s ^ 22
    + 19149212 * s ^ 21
    - 18552206 * s ^ 20
    - 14061315 * s ^ 19
    + 106142699 * s ^ 18
    - 268403934 * s ^ 17
    + 473307421 * s ^ 16
    - 651815997 * s ^ 15
    + 724623409 * s ^ 14
    - 661146188 * s ^ 13
    + 507848639 * s ^ 12
    - 339779325 * s ^ 11
    + 201955516 * s ^ 10
    - 98643086 * s ^ 9
    + 14889751 * s ^ 8
    + 35595620 * s ^ 7
    - 36354346 * s ^ 6
    + 14912970 * s ^ 5
    - 1737486 * s ^ 4
    - 430954 * s ^ 3
    + 51260 * s ^ 2
    + 2558 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient16 (s : ℚ) : ℚ :=
  2 * s ^ 29
    - 71 * s ^ 28
    + 1165 * s ^ 27
    - 11976 * s ^ 26
    + 87509 * s ^ 25
    - 484895 * s ^ 24
    + 2110295 * s ^ 23
    - 7362846 * s ^ 22
    + 20887878 * s ^ 21
    - 48773347 * s ^ 20
    + 94908588 * s ^ 19
    - 155832581 * s ^ 18
    + 217809973 * s ^ 17
    - 259033388 * s ^ 16
    + 259265335 * s ^ 15
    - 217050804 * s ^ 14
    + 158155754 * s ^ 13
    - 112096190 * s ^ 12
    + 79508022 * s ^ 11
    - 39537920 * s ^ 10
    - 19319445 * s ^ 9
    + 77113280 * s ^ 8
    - 89774640 * s ^ 7
    + 53925724 * s ^ 6
    - 15310538 * s ^ 5
    - 13004 * s ^ 4
    + 897863 * s ^ 3
    - 63067 * s ^ 2
    - 6665 * s
    - 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient17 (s : ℚ) : ℚ :=
  -s ^ 28
    + 30 * s ^ 27
    - 439 * s ^ 26
    + 4239 * s ^ 25
    - 30247 * s ^ 24
    + 166712 * s ^ 23
    - 721985 * s ^ 22
    + 2481125 * s ^ 21
    - 6837702 * s ^ 20
    + 15332989 * s ^ 19
    - 28560449 * s ^ 18
    + 45286130 * s ^ 17
    - 62023717 * s ^ 16
    + 71954412 * s ^ 15
    - 65844570 * s ^ 14
    + 41915979 * s ^ 13
    - 17948570 * s ^ 12
    + 22191972 * s ^ 11
    - 64693701 * s ^ 10
    + 121858600 * s ^ 9
    - 147021970 * s ^ 8
    + 112146199 * s ^ 7
    - 48807074 * s ^ 6
    + 7477018 * s ^ 5
    + 2840981 * s ^ 4
    - 1212087 * s ^ 3
    + 33351 * s ^ 2
    + 12720 * s
    + 55

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient18 (s : ℚ) : ℚ :=
  14 * s ^ 25
    - 366 * s ^ 24
    + 4346 * s ^ 23
    - 31167 * s ^ 22
    + 151309 * s ^ 21
    - 528129 * s ^ 20
    + 1378711 * s ^ 19
    - 2809415 * s ^ 18
    + 4825412 * s ^ 17
    - 7841204 * s ^ 16
    + 12518051 * s ^ 15
    - 16561620 * s ^ 14
    + 10571730 * s ^ 13
    + 18202179 * s ^ 12
    - 71902795 * s ^ 11
    + 131917262 * s ^ 10
    - 164829557 * s ^ 9
    + 144428893 * s ^ 8
    - 81575406 * s ^ 7
    + 22168852 * s ^ 6
    + 3440617 * s ^ 5
    - 4593729 * s ^ 4
    + 1045148 * s ^ 3
    + 38716 * s ^ 2
    - 17688 * s
    - 164

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient19 (s : ℚ) : ℚ :=
  s ^ 25
    - 31 * s ^ 24
    + 430 * s ^ 23
    - 3551 * s ^ 22
    + 19531 * s ^ 21
    - 75510 * s ^ 20
    + 210440 * s ^ 19
    - 431832 * s ^ 18
    + 726180 * s ^ 17
    - 1482154 * s ^ 16
    + 4592169 * s ^ 15
    - 14261195 * s ^ 14
    + 35178001 * s ^ 13
    - 67434585 * s ^ 12
    + 102156618 * s ^ 11
    - 122800267 * s ^ 10
    + 113604813 * s ^ 9
    - 73775571 * s ^ 8
    + 25507774 * s ^ 7
    + 3693373 * s ^ 6
    - 8676483 * s ^ 5
    + 3805300 * s ^ 4
    - 466363 * s ^ 3
    - 104896 * s ^ 2
    + 17487 * s
    + 321

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient20 (s : ℚ) : ℚ :=
  -2 * s ^ 23
    + 62 * s ^ 22
    - 896 * s ^ 21
    + 8081 * s ^ 20
    - 51357 * s ^ 19
    + 245858 * s ^ 18
    - 923551 * s ^ 17
    + 2794940 * s ^ 16
    - 6938271 * s ^ 15
    + 14318389 * s ^ 14
    - 24800949 * s ^ 13
    + 36154395 * s ^ 12
    - 43779914 * s ^ 11
    + 42046978 * s ^ 10
    - 28320837 * s ^ 9
    + 7946047 * s ^ 8
    + 7389845 * s ^ 7
    - 10668358 * s ^ 6
    + 6104299 * s ^ 5
    - 1567915 * s ^ 4
    - 57439 * s ^ 3
    + 112594 * s ^ 2
    - 11572 * s
    - 427

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient21 (s : ℚ) : ℚ :=
  s ^ 21
    - 28 * s ^ 20
    + 364 * s ^ 19
    - 2943 * s ^ 18
    + 16731 * s ^ 17
    - 71487 * s ^ 16
    + 237855 * s ^ 15
    - 622503 * s ^ 14
    + 1258035 * s ^ 13
    - 1831413 * s ^ 12
    + 1470673 * s ^ 11
    + 790214 * s ^ 10
    - 4649780 * s ^ 9
    + 7789766 * s ^ 8
    - 7745743 * s ^ 7
    + 4801906 * s ^ 6
    - 1618838 * s ^ 5
    + 36016 * s ^ 4
    + 204152 * s ^ 3
    - 67715 * s ^ 2
    + 4352 * s
    + 385

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient22 (s : ℚ) : ℚ :=
  -2 * s ^ 18
    + 56 * s ^ 17
    - 724 * s ^ 16
    + 5750 * s ^ 15
    - 31460 * s ^ 14
    + 125806 * s ^ 13
    - 379507 * s ^ 12
    + 875261 * s ^ 11
    - 1540872 * s ^ 10
    + 2035360 * s ^ 9
    - 1937680 * s ^ 8
    + 1207136 * s ^ 7
    - 331487 * s ^ 6
    - 167406 * s ^ 5
    + 224613 * s ^ 4
    - 105510 * s ^ 3
    + 21205 * s ^ 2
    - 313 * s
    - 226

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient23 (s : ℚ) : ℚ :=
  s ^ 15
    - 26 * s ^ 14
    + 306 * s ^ 13
    - 2156 * s ^ 12
    + 10138 * s ^ 11
    - 33586 * s ^ 10
    + 80685 * s ^ 9
    - 142580 * s ^ 8
    + 186195 * s ^ 7
    - 179121 * s ^ 6
    + 125123 * s ^ 5
    - 60760 * s ^ 4
    + 17986 * s ^ 3
    - 1875 * s ^ 2
    - 408 * s
    + 78

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step2Coefficient24 (s : ℚ) : ℚ :=
  -s ^ 8
    + 15 * s ^ 7
    - 93 * s ^ 6
    + 308 * s ^ 5
    - 588 * s ^ 4
    + 651 * s ^ 3
    - 398 * s ^ 2
    + 118 * s
    - 12

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
    t1Step2Coefficient24 s * r ^ 24

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_0 (s : ℚ) :
    t1Step2Coefficient0 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient0,
    t1Step1Coefficient0,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_1 (s : ℚ) :
    t1Step2Coefficient1 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient1,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_2 (s : ℚ) :
    t1Step2Coefficient2 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient2,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_3 (s : ℚ) :
    t1Step2Coefficient3 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient3,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_4 (s : ℚ) :
    t1Step2Coefficient4 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient4,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_5 (s : ℚ) :
    t1Step2Coefficient5 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient5,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_6 (s : ℚ) :
    t1Step2Coefficient6 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient6,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_7 (s : ℚ) :
    t1Step2Coefficient7 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient7,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    t1Step1Coefficient7,
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
theorem t1Step2Coefficient_product_certificate_8 (s : ℚ) :
    t1Step2Coefficient8 s =
    t1Step1Coefficient0 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient8,
    t1Step1Coefficient0,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    t1Step1Coefficient7,
    t1Step1Coefficient8,
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
theorem t1Step2Coefficient_product_certificate_9 (s : ℚ) :
    t1Step2Coefficient9 s =
    t1Step1Coefficient1 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient9,
    t1Step1Coefficient1,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    t1Step1Coefficient7,
    t1Step1Coefficient8,
    t1Step1Coefficient9,
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
theorem t1Step2Coefficient_product_certificate_10 (s : ℚ) :
    t1Step2Coefficient10 s =
    t1Step1Coefficient2 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient10,
    t1Step1Coefficient2,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    t1Step1Coefficient7,
    t1Step1Coefficient8,
    t1Step1Coefficient9,
    t1Step1Coefficient10,
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
theorem t1Step2Coefficient_product_certificate_11 (s : ℚ) :
    t1Step2Coefficient11 s =
    t1Step1Coefficient3 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient11,
    t1Step1Coefficient3,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    t1Step1Coefficient7,
    t1Step1Coefficient8,
    t1Step1Coefficient9,
    t1Step1Coefficient10,
    t1Step1Coefficient11,
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
theorem t1Step2Coefficient_product_certificate_12 (s : ℚ) :
    t1Step2Coefficient12 s =
    t1Step1Coefficient4 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient12,
    t1Step1Coefficient4,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    t1Step1Coefficient7,
    t1Step1Coefficient8,
    t1Step1Coefficient9,
    t1Step1Coefficient10,
    t1Step1Coefficient11,
    t1Step1Coefficient12,
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
theorem t1Step2Coefficient_product_certificate_13 (s : ℚ) :
    t1Step2Coefficient13 s =
    t1Step1Coefficient5 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient13,
    t1Step1Coefficient5,
    t1Step1Coefficient6,
    t1Step1Coefficient7,
    t1Step1Coefficient8,
    t1Step1Coefficient9,
    t1Step1Coefficient10,
    t1Step1Coefficient11,
    t1Step1Coefficient12,
    t1Step1Coefficient13,
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
theorem t1Step2Coefficient_product_certificate_14 (s : ℚ) :
    t1Step2Coefficient14 s =
    t1Step1Coefficient6 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient14,
    t1Step1Coefficient6,
    t1Step1Coefficient7,
    t1Step1Coefficient8,
    t1Step1Coefficient9,
    t1Step1Coefficient10,
    t1Step1Coefficient11,
    t1Step1Coefficient12,
    t1Step1Coefficient13,
    t1Step1Coefficient14,
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
theorem t1Step2Coefficient_product_certificate_15 (s : ℚ) :
    t1Step2Coefficient15 s =
    t1Step1Coefficient7 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient15,
    t1Step1Coefficient7,
    t1Step1Coefficient8,
    t1Step1Coefficient9,
    t1Step1Coefficient10,
    t1Step1Coefficient11,
    t1Step1Coefficient12,
    t1Step1Coefficient13,
    t1Step1Coefficient14,
    t1Step1Coefficient15,
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
theorem t1Step2Coefficient_product_certificate_16 (s : ℚ) :
    t1Step2Coefficient16 s =
    t1Step1Coefficient8 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [t1Step2Coefficient16,
    t1Step1Coefficient8,
    t1Step1Coefficient9,
    t1Step1Coefficient10,
    t1Step1Coefficient11,
    t1Step1Coefficient12,
    t1Step1Coefficient13,
    t1Step1Coefficient14,
    t1Step1Coefficient15,
    t1Step1Coefficient16,
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
theorem t1Step2Coefficient_product_certificate_17 (s : ℚ) :
    t1Step2Coefficient17 s =
    t1Step1Coefficient9 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient1 s
    := by
  simp only [t1Step2Coefficient17,
    t1Step1Coefficient9,
    t1Step1Coefficient10,
    t1Step1Coefficient11,
    t1Step1Coefficient12,
    t1Step1Coefficient13,
    t1Step1Coefficient14,
    t1Step1Coefficient15,
    t1Step1Coefficient16,
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
theorem t1Step2Coefficient_product_certificate_18 (s : ℚ) :
    t1Step2Coefficient18 s =
    t1Step1Coefficient10 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient2 s
    := by
  simp only [t1Step2Coefficient18,
    t1Step1Coefficient10,
    t1Step1Coefficient11,
    t1Step1Coefficient12,
    t1Step1Coefficient13,
    t1Step1Coefficient14,
    t1Step1Coefficient15,
    t1Step1Coefficient16,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_19 (s : ℚ) :
    t1Step2Coefficient19 s =
    t1Step1Coefficient11 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient3 s
    := by
  simp only [t1Step2Coefficient19,
    t1Step1Coefficient11,
    t1Step1Coefficient12,
    t1Step1Coefficient13,
    t1Step1Coefficient14,
    t1Step1Coefficient15,
    t1Step1Coefficient16,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_20 (s : ℚ) :
    t1Step2Coefficient20 s =
    t1Step1Coefficient12 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient4 s
    := by
  simp only [t1Step2Coefficient20,
    t1Step1Coefficient12,
    t1Step1Coefficient13,
    t1Step1Coefficient14,
    t1Step1Coefficient15,
    t1Step1Coefficient16,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_21 (s : ℚ) :
    t1Step2Coefficient21 s =
    t1Step1Coefficient13 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient5 s
    := by
  simp only [t1Step2Coefficient21,
    t1Step1Coefficient13,
    t1Step1Coefficient14,
    t1Step1Coefficient15,
    t1Step1Coefficient16,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_22 (s : ℚ) :
    t1Step2Coefficient22 s =
    t1Step1Coefficient14 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient6 s
    := by
  simp only [t1Step2Coefficient22,
    t1Step1Coefficient14,
    t1Step1Coefficient15,
    t1Step1Coefficient16,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_23 (s : ℚ) :
    t1Step2Coefficient23 s =
    t1Step1Coefficient15 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient7 s
    := by
  simp only [t1Step2Coefficient23,
    t1Step1Coefficient15,
    t1Step1Coefficient16,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step2Coefficient_product_certificate_24 (s : ℚ) :
    t1Step2Coefficient24 s =
    t1Step1Coefficient16 s *
        rawUnitTwoDenominatorCoefficient8 s
    := by
  simp only [t1Step2Coefficient24,
    t1Step1Coefficient16,
    rawUnitTwoDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step2_eq_t1Step1_mul_rawUnitTwoDenominator (r s : ℚ) :
    t1Step2 r s = t1Step1 r s * rawUnitTwoDenominator r s := by
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
  simp only [t1Step2, t1Step1, rawUnitTwoDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 33
    + 7 * s ^ 32
    - 28 * s ^ 31
    + 80 * s ^ 30
    - 179 * s ^ 29
    + 329 * s ^ 28
    - 510 * s ^ 27
    + 678 * s ^ 26
    - 780 * s ^ 25
    + 780 * s ^ 24
    - 678 * s ^ 23
    + 510 * s ^ 22
    - 329 * s ^ 21
    + 179 * s ^ 20
    - 80 * s ^ 19
    + 28 * s ^ 18
    - 7 * s ^ 17
    + s ^ 16

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient3 (s : ℚ) : ℚ :=
  -s ^ 36
    + 12 * s ^ 35
    - 75 * s ^ 34
    + 314 * s ^ 33
    - 955 * s ^ 32
    + 2251 * s ^ 31
    - 4232 * s ^ 30
    + 6399 * s ^ 29
    - 7599 * s ^ 28
    + 6350 * s ^ 27
    - 1639 * s ^ 26
    - 6271 * s ^ 25
    + 15554 * s ^ 24
    - 23471 * s ^ 23
    + 27615 * s ^ 22
    - 27038 * s ^ 21
    + 22579 * s ^ 20
    - 16219 * s ^ 19
    + 10028 * s ^ 18
    - 5307 * s ^ 17
    + 2379 * s ^ 16
    - 890 * s ^ 15
    + 271 * s ^ 14
    - 65 * s ^ 13
    + 11 * s ^ 12
    - s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient4 (s : ℚ) : ℚ :=
  2 * s ^ 38
    - 27 * s ^ 37
    + 185 * s ^ 36
    - 819 * s ^ 35
    + 2541 * s ^ 34
    - 5519 * s ^ 33
    + 7236 * s ^ 32
    + 775 * s ^ 31
    - 35081 * s ^ 30
    + 117169 * s ^ 29
    - 263259 * s ^ 28
    + 469809 * s ^ 27
    - 703464 * s ^ 26
    + 905404 * s ^ 25
    - 1011813 * s ^ 24
    + 982940 * s ^ 23
    - 823296 * s ^ 22
    + 581070 * s ^ 21
    - 326065 * s ^ 20
    + 118968 * s ^ 19
    + 9947 * s ^ 18
    - 64195 * s ^ 17
    + 68133 * s ^ 16
    - 49725 * s ^ 15
    + 28690 * s ^ 14
    - 13603 * s ^ 13
    + 5362 * s ^ 12
    - 1739 * s ^ 11
    + 453 * s ^ 10
    - 91 * s ^ 9
    + 13 * s ^ 8
    - s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 40
    + 15 * s ^ 39
    - 103 * s ^ 38
    + 356 * s ^ 37
    - 110 * s ^ 36
    - 5931 * s ^ 35
    + 38515 * s ^ 34
    - 152712 * s ^ 33
    + 454397 * s ^ 32
    - 1089835 * s ^ 31
    + 2185084 * s ^ 30
    - 3733538 * s ^ 29
    + 5483844 * s ^ 28
    - 6908638 * s ^ 27
    + 7330144 * s ^ 26
    - 6195480 * s ^ 25
    + 3381871 * s ^ 24
    + 635541 * s ^ 23
    - 4893946 * s ^ 22
    + 8299503 * s ^ 21
    - 10065743 * s ^ 20
    + 10000578 * s ^ 19
    - 8498880 * s ^ 18
    + 6286172 * s ^ 17
    - 4072475 * s ^ 16
    + 2312433 * s ^ 15
    - 1147067 * s ^ 14
    + 493284 * s ^ 13
    - 181627 * s ^ 12
    + 55940 * s ^ 11
    - 13901 * s ^ 10
    + 2619 * s ^ 9
    - 324 * s ^ 8
    + 13 * s ^ 7
    + 2 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient6 (s : ℚ) : ℚ :=
  2 * s ^ 41
    - 46 * s ^ 40
    + 542 * s ^ 39
    - 4199 * s ^ 38
    + 23673 * s ^ 37
    - 102585 * s ^ 36
    + 353719 * s ^ 35
    - 991499 * s ^ 34
    + 2284149 * s ^ 33
    - 4317481 * s ^ 32
    + 6527571 * s ^ 31
    - 7139814 * s ^ 30
    + 2861413 * s ^ 29
    + 10696044 * s ^ 28
    - 37623523 * s ^ 27
    + 79554758 * s ^ 26
    - 133642048 * s ^ 25
    + 191875740 * s ^ 24
    - 242583254 * s ^ 23
    + 274019142 * s ^ 22
    - 278580044 * s ^ 21
    + 255740195 * s ^ 20
    - 212141471 * s ^ 19
    + 158805762 * s ^ 18
    - 106973032 * s ^ 17
    + 64547539 * s ^ 16
    - 34671495 * s ^ 15
    + 16434881 * s ^ 14
    - 6786916 * s ^ 13
    + 2394424 * s ^ 12
    - 697677 * s ^ 11
    + 158379 * s ^ 10
    - 24529 * s ^ 9
    + 1358 * s ^ 8
    + 408 * s ^ 7
    - 86 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient7 (s : ℚ) : ℚ :=
  -s ^ 43
    + 23 * s ^ 42
    - 266 * s ^ 41
    + 2017 * s ^ 40
    - 11022 * s ^ 39
    + 44792 * s ^ 38
    - 132850 * s ^ 37
    + 249384 * s ^ 36
    - 12408 * s ^ 35
    - 2128894 * s ^ 34
    + 10446357 * s ^ 33
    - 34051391 * s ^ 32
    + 88705931 * s ^ 31
    - 196836130 * s ^ 30
    + 384083124 * s ^ 29
    - 671387531 * s ^ 28
    + 1063616970 * s ^ 27
    - 1538160640 * s ^ 26
    + 2039523175 * s ^ 25
    - 2485364190 * s ^ 24
    + 2785759502 * s ^ 23
    - 2871045407 * s ^ 22
    + 2716970832 * s ^ 21
    - 2355624415 * s ^ 20
    + 1865285431 * s ^ 19
    - 1343467710 * s ^ 18
    + 875600982 * s ^ 17
    - 512944699 * s ^ 16
    + 267728183 * s ^ 15
    - 122946992 * s ^ 14
    + 48719628 * s ^ 13
    - 16123935 * s ^ 12
    + 4176118 * s ^ 11
    - 717560 * s ^ 10
    + 19970 * s ^ 9
    + 33078 * s ^ 8
    - 10712 * s ^ 7
    + 1210 * s ^ 6
    + 48 * s ^ 5
    - 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient8 (s : ℚ) : ℚ :=
  -4 * s ^ 43
    + 113 * s ^ 42
    - 1567 * s ^ 41
    + 14330 * s ^ 40
    - 97242 * s ^ 39
    + 521145 * s ^ 38
    - 2291591 * s ^ 37
    + 8489438 * s ^ 36
    - 27042014 * s ^ 35
    + 75338975 * s ^ 34
    - 186339319 * s ^ 33
    + 414625820 * s ^ 32
    - 839530607 * s ^ 31
    + 1560908980 * s ^ 30
    - 2681735970 * s ^ 29
    + 4273376579 * s ^ 28
    - 6326862595 * s ^ 27
    + 8705169467 * s ^ 26
    - 11123465994 * s ^ 25
    + 13182015674 * s ^ 24
    - 14460338824 * s ^ 23
    + 14648930946 * s ^ 22
    - 13665135474 * s ^ 21
    + 11697866722 * s ^ 20
    - 9150612438 * s ^ 19
    + 6506802159 * s ^ 18
    - 4177855814 * s ^ 17
    + 2400337156 * s ^ 16
    - 1218083441 * s ^ 15
    + 534658584 * s ^ 14
    - 195446063 * s ^ 13
    + 54745354 * s ^ 12
    - 8771914 * s ^ 11
    - 1172052 * s ^ 10
    + 1404800 * s ^ 9
    - 519304 * s ^ 8
    + 103102 * s ^ 7
    - 5749 * s ^ 6
    - 1416 * s ^ 5
    + 47 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient9 (s : ℚ) : ℚ :=
  s ^ 45
    - 28 * s ^ 44
    + 399 * s ^ 43
    - 3808 * s ^ 42
    + 27168 * s ^ 41
    - 153861 * s ^ 40
    + 718592 * s ^ 39
    - 2843834 * s ^ 38
    + 9745499 * s ^ 37
    - 29484072 * s ^ 36
    + 80210723 * s ^ 35
    - 199593567 * s ^ 34
    + 460730668 * s ^ 33
    - 995609197 * s ^ 32
    + 2020484918 * s ^ 31
    - 3844563742 * s ^ 30
    + 6832402474 * s ^ 29
    - 11296432245 * s ^ 28
    + 17324987314 * s ^ 27
    - 24597357818 * s ^ 26
    + 32280618763 * s ^ 25
    - 39102992445 * s ^ 24
    + 43649035098 * s ^ 23
    - 44804500956 * s ^ 22
    + 42174027501 * s ^ 21
    - 36271270262 * s ^ 20
    + 28362165699 * s ^ 19
    - 20029207282 * s ^ 18
    + 12652034756 * s ^ 17
    - 7042608343 * s ^ 16
    + 3366603586 * s ^ 15
    - 1310650676 * s ^ 14
    + 358789299 * s ^ 13
    - 21607559 * s ^ 12
    - 46394126 * s ^ 11
    + 33071525 * s ^ 10
    - 13402317 * s ^ 9
    + 3504534 * s ^ 8
    - 468134 * s ^ 7
    - 32298 * s ^ 6
    + 18412 * s ^ 5
    - 322 * s ^ 4
    - 37 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient10 (s : ℚ) : ℚ :=
  -5 * s ^ 44
    + 122 * s ^ 43
    - 1506 * s ^ 42
    + 12312 * s ^ 41
    - 73793 * s ^ 40
    + 339111 * s ^ 39
    - 1204188 * s ^ 38
    + 3161743 * s ^ 37
    - 4862808 * s ^ 36
    - 4766361 * s ^ 35
    + 67931411 * s ^ 34
    - 301040401 * s ^ 33
    + 959147978 * s ^ 32
    - 2501331880 * s ^ 31
    + 5613249932 * s ^ 30
    - 11132585576 * s ^ 29
    + 19834571222 * s ^ 28
    - 32073822559 * s ^ 27
    + 47362070764 * s ^ 26
    - 64067267018 * s ^ 25
    + 79471268832 * s ^ 24
    - 90350109650 * s ^ 23
    + 93967681520 * s ^ 22
    - 89111942498 * s ^ 21
    + 76670726345 * s ^ 20
    - 59397031750 * s ^ 19
    + 40947053176 * s ^ 18
    - 24616820155 * s ^ 17
    + 12400169342 * s ^ 16
    - 4727877123 * s ^ 15
    + 833810044 * s ^ 14
    + 572302758 * s ^ 13
    - 721852384 * s ^ 12
    + 461358456 * s ^ 11
    - 205268043 * s ^ 10
    + 64865612 * s ^ 9
    - 12620603 * s ^ 8
    + 247456 * s ^ 7
    + 649272 * s ^ 6
    - 138089 * s ^ 5
    - 1614 * s ^ 4
    + 594 * s ^ 3
    + 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient11 (s : ℚ) : ℚ :=
  -3 * s ^ 44
    + 100 * s ^ 43
    - 1560 * s ^ 42
    + 15758 * s ^ 41
    - 117386 * s ^ 40
    + 691241 * s ^ 39
    - 3356024 * s ^ 38
    + 13803567 * s ^ 37
    - 49007646 * s ^ 36
    + 152387780 * s ^ 35
    - 420420671 * s ^ 34
    + 1042366907 * s ^ 33
    - 2352772161 * s ^ 32
    + 4894985541 * s ^ 31
    - 9483101234 * s ^ 30
    + 17206963167 * s ^ 29
    - 29258600902 * s ^ 28
    + 46457961639 * s ^ 27
    - 68518231139 * s ^ 26
    + 93354465709 * s ^ 25
    - 116924400053 * s ^ 24
    + 133991248472 * s ^ 23
    - 139734486950 * s ^ 22
    + 131662478350 * s ^ 21
    - 110879343524 * s ^ 20
    + 81942938524 * s ^ 19
    - 51275739579 * s ^ 18
    + 24826573660 * s ^ 17
    - 6225452805 * s ^ 16
    - 3855445140 * s ^ 15
    + 7109347578 * s ^ 14
    - 6303826894 * s ^ 13
    + 4044576796 * s ^ 12
    - 1988371796 * s ^ 11
    + 731834505 * s ^ 10
    - 180088572 * s ^ 9
    + 13715603 * s ^ 8
    + 10449444 * s ^ 7
    - 4717698 * s ^ 6
    + 636020 * s ^ 5
    + 47009 * s ^ 4
    - 5573 * s ^ 3
    - 60 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient12 (s : ℚ) : ℚ :=
  11 * s ^ 43
    - 289 * s ^ 42
    + 3682 * s ^ 41
    - 30819 * s ^ 40
    + 191499 * s ^ 39
    - 941527 * s ^ 38
    + 3784193 * s ^ 37
    - 12532649 * s ^ 36
    + 33534921 * s ^ 35
    - 67235001 * s ^ 34
    + 71194010 * s ^ 33
    + 137173860 * s ^ 32
    - 1057152102 * s ^ 31
    + 3709227626 * s ^ 30
    - 9698368797 * s ^ 29
    + 20910230659 * s ^ 28
    - 38744729995 * s ^ 27
    + 63068189193 * s ^ 26
    - 91310908707 * s ^ 25
    + 118259929024 * s ^ 24
    - 136979834698 * s ^ 23
    + 140905619228 * s ^ 22
    - 126571862055 * s ^ 21
    + 95604715489 * s ^ 20
    - 54751070876 * s ^ 19
    + 13637551206 * s ^ 18
    + 18773882123 * s ^ 17
    - 37150391703 * s ^ 16
    + 41130121052 * s ^ 15
    - 34587801042 * s ^ 14
    + 23367225053 * s ^ 13
    - 12689148549 * s ^ 12
    + 5335224513 * s ^ 11
    - 1550325874 * s ^ 10
    + 169265020 * s ^ 9
    + 111707579 * s ^ 8
    - 75446998 * s ^ 7
    + 20968920 * s ^ 6
    - 1556243 * s ^ 5
    - 435987 * s ^ 4
    + 34217 * s ^ 3
    + 832 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient13 (s : ℚ) : ℚ :=
  3 * s ^ 43
    - 106 * s ^ 42
    + 1663 * s ^ 41
    - 16396 * s ^ 40
    + 118810 * s ^ 39
    - 692992 * s ^ 38
    + 3442298 * s ^ 37
    - 15000113 * s ^ 36
    + 57903590 * s ^ 35
    - 197985501 * s ^ 34
    + 598571963 * s ^ 33
    - 1600367192 * s ^ 32
    + 3793723356 * s ^ 31
    - 8013466689 * s ^ 30
    + 15196244135 * s ^ 29
    - 26112873056 * s ^ 28
    + 41012681859 * s ^ 27
    - 59116859169 * s ^ 26
    + 77914587368 * s ^ 25
    - 92615527164 * s ^ 24
    + 96560869479 * s ^ 23
    - 83301381271 * s ^ 22
    + 49923125080 * s ^ 21
    + 296435552 * s ^ 20
    - 57576242654 * s ^ 19
    + 108351065529 * s ^ 18
    - 139984035549 * s ^ 17
    + 145430783072 * s ^ 16
    - 126249384844 * s ^ 15
    + 91838952947 * s ^ 14
    - 54963433050 * s ^ 13
    + 25877213755 * s ^ 12
    - 8481224243 * s ^ 11
    + 953729474 * s ^ 10
    + 938490841 * s ^ 9
    - 764206716 * s ^ 8
    + 303969514 * s ^ 7
    - 60506131 * s ^ 6
    - 1088120 * s ^ 5
    + 2530066 * s ^ 4
    - 142210 * s ^ 3
    - 7163 * s ^ 2
    - 25 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient14 (s : ℚ) : ℚ :=
  -6 * s ^ 42
    + 129 * s ^ 41
    - 1013 * s ^ 40
    + 1528 * s ^ 39
    + 38500 * s ^ 38
    - 417324 * s ^ 37
    + 2450582 * s ^ 36
    - 10078679 * s ^ 35
    + 31450933 * s ^ 34
    - 77354450 * s ^ 33
    + 154572890 * s ^ 32
    - 267958684 * s ^ 31
    + 478883647 * s ^ 30
    - 1070290125 * s ^ 29
    + 2721686623 * s ^ 28
    - 6305598902 * s ^ 27
    + 11876599659 * s ^ 26
    - 17068898326 * s ^ 25
    + 16075108312 * s ^ 24
    - 620927724 * s ^ 23
    - 36646506719 * s ^ 22
    + 97783830141 * s ^ 21
    - 176424267579 * s ^ 20
    + 257248236087 * s ^ 19
    - 319225798477 * s ^ 18
    + 342496346614 * s ^ 17
    - 317280795336 * s ^ 16
    + 250570683219 * s ^ 15
    - 164257069103 * s ^ 14
    + 84621514494 * s ^ 13
    - 29452681667 * s ^ 12
    + 1742593883 * s ^ 11
    + 6385708560 * s ^ 10
    - 5463053021 * s ^ 9
    + 2679910849 * s ^ 8
    - 811419027 * s ^ 7
    + 95123629 * s ^ 6
    + 28413546 * s ^ 5
    - 10457641 * s ^ 4
    + 376575 * s ^ 3
    + 43101 * s ^ 2
    + 302 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient15 (s : ℚ) : ℚ :=
  -s ^ 42
    + 25 * s ^ 41
    - 127 * s ^ 40
    - 2363 * s ^ 39
    + 47065 * s ^ 38
    - 433050 * s ^ 37
    + 2647481 * s ^ 36
    - 11923314 * s ^ 35
    + 41279211 * s ^ 34
    - 110873367 * s ^ 33
    + 223100245 * s ^ 32
    - 282833102 * s ^ 31
    - 36532159 * s ^ 30
    + 1349646356 * s ^ 29
    - 4223325737 * s ^ 28
    + 8187420485 * s ^ 27
    - 10384828083 * s ^ 26
    + 4813198052 * s ^ 25
    + 16934659230 * s ^ 24
    - 63340312736 * s ^ 23
    + 139720898166 * s ^ 22
    - 244764016524 * s ^ 21
    + 366862883082 * s ^ 20
    - 481677933631 * s ^ 19
    + 555552144680 * s ^ 18
    - 557745014860 * s ^ 17
    + 478252716321 * s ^ 16
    - 338731757922 * s ^ 15
    + 184330093157 * s ^ 14
    - 60326424680 * s ^ 13
    - 10526278146 * s ^ 12
    + 33355172604 * s ^ 11
    - 28595338575 * s ^ 10
    + 16029044935 * s ^ 9
    - 6218744434 * s ^ 8
    + 1370872745 * s ^ 7
    + 61039718 * s ^ 6
    - 141911422 * s ^ 5
    + 32185665 * s ^ 4
    - 370286 * s ^ 3
    - 192359 * s ^ 2
    - 2345 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient16 (s : ℚ) : ℚ :=
  -s ^ 41
    + 91 * s ^ 40
    - 2425 * s ^ 39
    + 34486 * s ^ 38
    - 321144 * s ^ 37
    + 2171653 * s ^ 36
    - 11337727 * s ^ 35
    + 47556010 * s ^ 34
    - 164615219 * s ^ 33
    + 477866996 * s ^ 32
    - 1168491826 * s ^ 31
    + 2380927643 * s ^ 30
    - 3897757995 * s ^ 29
    + 4587270702 * s ^ 28
    - 1902793470 * s ^ 27
    - 8167773634 * s ^ 26
    + 30739506183 * s ^ 25
    - 71810965301 * s ^ 24
    + 138228471770 * s ^ 23
    - 236229735027 * s ^ 22
    + 365951193423 * s ^ 21
    - 511962573286 * s ^ 20
    + 637182116984 * s ^ 19
    - 691153426768 * s ^ 18
    + 635174088961 * s ^ 17
    - 471185469437 * s ^ 16
    + 249696337122 * s ^ 15
    - 45013500383 * s ^ 14
    - 85401488715 * s ^ 13
    + 128308167812 * s ^ 12
    - 109616599608 * s ^ 11
    + 67838928530 * s ^ 10
    - 31077198116 * s ^ 9
    + 9426254706 * s ^ 8
    - 758936193 * s ^ 7
    - 892410819 * s ^ 6
    + 449833123 * s ^ 5
    - 74124049 * s ^ 4
    - 1874467 * s ^ 3
    + 656330 * s ^ 2
    + 13084 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient17 (s : ℚ) : ℚ :=
  11 * s ^ 40
    - 438 * s ^ 39
    + 7918 * s ^ 38
    - 88203 * s ^ 37
    + 691247 * s ^ 36
    - 4114269 * s ^ 35
    + 19573554 * s ^ 34
    - 77307511 * s ^ 33
    + 260929442 * s ^ 32
    - 767740858 * s ^ 31
    + 1989390604 * s ^ 30
    - 4553982128 * s ^ 29
    + 9239265958 * s ^ 28
    - 16841402646 * s ^ 27
    + 28528819457 * s ^ 26
    - 47354227112 * s ^ 25
    + 80505879321 * s ^ 24
    - 139684443598 * s ^ 23
    + 235689708562 * s ^ 22
    - 365888327928 * s ^ 21
    + 501059317108 * s ^ 20
    - 585606955504 * s ^ 19
    + 560722721805 * s ^ 18
    - 402421807364 * s ^ 17
    + 148151546665 * s ^ 16
    + 114973330042 * s ^ 15
    - 297128638384 * s ^ 14
    + 354454447664 * s ^ 13
    - 305160409922 * s ^ 12
    + 204504182824 * s ^ 11
    - 106203450075 * s ^ 10
    + 39203472584 * s ^ 9
    - 6303656316 * s ^ 8
    - 3483925244 * s ^ 7
    + 3078398976 * s ^ 6
    - 1033724625 * s ^ 5
    + 122603465 * s ^ 4
    + 11700955 * s ^ 3
    - 1730545 * s ^ 2
    - 55473 * s
    - 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient18 (s : ℚ) : ℚ :=
  s ^ 40
    - 54 * s ^ 39
    + 1206 * s ^ 38
    - 15667 * s ^ 37
    + 137268 * s ^ 36
    - 883703 * s ^ 35
    + 4433638 * s ^ 34
    - 18184534 * s ^ 33
    + 63726239 * s ^ 32
    - 198106363 * s ^ 31
    + 555829242 * s ^ 30
    - 1386688118 * s ^ 29
    + 2932817800 * s ^ 28
    - 4789541093 * s ^ 27
    + 4457961615 * s ^ 26
    + 4413455412 * s ^ 25
    - 32204995963 * s ^ 24
    + 89172752111 * s ^ 23
    - 175685025700 * s ^ 22
    + 270615476908 * s ^ 21
    - 328079639518 * s ^ 20
    + 292796813505 * s ^ 19
    - 132580000657 * s ^ 18
    - 130496250787 * s ^ 17
    + 416883773478 * s ^ 16
    - 625887941483 * s ^ 15
    + 689507109962 * s ^ 14
    - 606602650293 * s ^ 13
    + 434667184611 * s ^ 12
    - 249016931959 * s ^ 11
    + 104671372441 * s ^ 10
    - 21205979336 * s ^ 9
    - 10932993050 * s ^ 8
    + 13564750623 * s ^ 7
    - 6837154768 * s ^ 6
    + 1770119962 * s ^ 5
    - 121038829 * s ^ 4
    - 37372848 * s ^ 3
    + 3494189 * s ^ 2
    + 184341 * s
    + 171

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient19 (s : ℚ) : ℚ :=
  -2 * s ^ 39
    + 73 * s ^ 38
    - 1161 * s ^ 37
    + 10553 * s ^ 36
    - 58554 * s ^ 35
    + 175270 * s ^ 34
    + 53840 * s ^ 33
    - 3273759 * s ^ 32
    + 15977826 * s ^ 31
    - 31527069 * s ^ 30
    - 68899023 * s ^ 29
    + 807009672 * s ^ 28
    - 3628873779 * s ^ 27
    + 11373812149 * s ^ 26
    - 27904353006 * s ^ 25
    + 55816832632 * s ^ 24
    - 91681884156 * s ^ 23
    + 120305710594 * s ^ 22
    - 112774728898 * s ^ 21
    + 34412408648 * s ^ 20
    + 135958559692 * s ^ 19
    - 383944043976 * s ^ 18
    + 651082435468 * s ^ 17
    - 853330491455 * s ^ 16
    + 920935471169 * s ^ 15
    - 834297197384 * s ^ 14
    + 632507350015 * s ^ 13
    - 389326492422 * s ^ 12
    + 175357093422 * s ^ 11
    - 32338857368 * s ^ 10
    - 33778082091 * s ^ 9
    + 43872264066 * s ^ 8
    - 28193810631 * s ^ 7
    + 10997423064 * s ^ 6
    - 2198116769 * s ^ 5
    - 19704729 * s ^ 4
    + 83465861 * s ^ 3
    - 5168185 * s ^ 2
    - 488631 * s
    - 966

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient20 (s : ℚ) : ℚ :=
  26 * s ^ 37
    - 993 * s ^ 36
    + 17875 * s ^ 35
    - 203400 * s ^ 34
    + 1652007 * s ^ 33
    - 10222218 * s ^ 32
    + 50092071 * s ^ 31
    - 199194224 * s ^ 30
    + 653276954 * s ^ 29
    - 1785936233 * s ^ 28
    + 4088826649 * s ^ 27
    - 7785909574 * s ^ 26
    + 11887301540 * s ^ 25
    - 12583085371 * s ^ 24
    + 1413364153 * s ^ 23
    + 35248127728 * s ^ 22
    - 112994463558 * s ^ 21
    + 241216885236 * s ^ 20
    - 412401085385 * s ^ 19
    + 595456099122 * s ^ 18
    - 740778844156 * s ^ 17
    + 799020047228 * s ^ 16
    - 744251433743 * s ^ 15
    + 587507903671 * s ^ 14
    - 372958042170 * s ^ 13
    + 158671405442 * s ^ 12
    + 5612764873 * s ^ 11
    - 93719546843 * s ^ 10
    + 109557748773 * s ^ 9
    - 80596033055 * s ^ 8
    + 40729827782 * s ^ 7
    - 12985919730 * s ^ 6
    + 1724050027 * s ^ 5
    + 344042633 * s ^ 4
    - 139310019 * s ^ 3
    + 4750482 * s ^ 2
    + 1042573 * s
    + 3827

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient21 (s : ℚ) : ℚ :=
  2 * s ^ 37
    - 93 * s ^ 36
    + 1979 * s ^ 35
    - 26148 * s ^ 34
    + 244361 * s ^ 33
    - 1736228 * s ^ 32
    + 9804037 * s ^ 31
    - 45305708 * s ^ 30
    + 175192660 * s ^ 29
    - 578659114 * s ^ 28
    + 1668423066 * s ^ 27
    - 4295441293 * s ^ 26
    + 10074452375 * s ^ 25
    - 21792473465 * s ^ 24
    + 43584125920 * s ^ 23
    - 80216857318 * s ^ 22
    + 134925058782 * s ^ 21
    - 206044170973 * s ^ 20
    + 283885763667 * s ^ 19
    - 350284954875 * s ^ 18
    + 382889767632 * s ^ 17
    - 363346167105 * s ^ 16
    + 285527198799 * s ^ 15
    - 160398673399 * s ^ 14
    + 15219400882 * s ^ 13
    + 113840623925 * s ^ 12
    - 193482113608 * s ^ 11
    + 207406257126 * s ^ 10
    - 165909070754 * s ^ 9
    + 100022174535 * s ^ 8
    - 42691959031 * s ^ 7
    + 10639110715 * s ^ 6
    - 199692915 * s ^ 5
    - 753598701 * s ^ 4
    + 175144831 * s ^ 3
    - 37828 * s ^ 2
    - 1795485 * s
    - 11253

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient22 (s : ℚ) : ℚ :=
  -s ^ 36
    + 36 * s ^ 35
    - 600 * s ^ 34
    + 6216 * s ^ 33
    - 44909 * s ^ 32
    + 234610 * s ^ 31
    - 839878 * s ^ 30
    + 1366794 * s ^ 29
    + 6045309 * s ^ 28
    - 62477524 * s ^ 27
    + 308491697 * s ^ 26
    - 1094921119 * s ^ 25
    + 3081149270 * s ^ 24
    - 7197537813 * s ^ 23
    + 14358253356 * s ^ 22
    - 24888132215 * s ^ 21
    + 37702648240 * s ^ 20
    - 49459966994 * s ^ 19
    + 54229386393 * s ^ 18
    - 44235022113 * s ^ 17
    + 11921138085 * s ^ 16
    + 46355972368 * s ^ 15
    - 125444913947 * s ^ 14
    + 208389179893 * s ^ 13
    - 269294385261 * s ^ 12
    + 283922568366 * s ^ 11
    - 244810988194 * s ^ 10
    + 168999970012 * s ^ 9
    - 88687899714 * s ^ 8
    + 31310815695 * s ^ 7
    - 4586857747 * s ^ 6
    - 1675293378 * s ^ 5
    + 1018476075 * s ^ 4
    - 160013164 * s ^ 3
    - 8920964 * s ^ 2
    + 2487770 * s
    + 25350

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient23 (s : ℚ) : ℚ :=
  2 * s ^ 34
    - 60 * s ^ 33
    + 823 * s ^ 32
    - 7181 * s ^ 31
    + 49069 * s ^ 30
    - 308168 * s ^ 29
    + 1836621 * s ^ 28
    - 9659045 * s ^ 27
    + 42089351 * s ^ 26
    - 148896626 * s ^ 25
    + 430204216 * s ^ 24
    - 1036515588 * s ^ 23
    + 2155682745 * s ^ 22
    - 4069700298 * s ^ 21
    + 7403671460 * s ^ 20
    - 13583852052 * s ^ 19
    + 25320862618 * s ^ 18
    - 46670284821 * s ^ 17
    + 81823307780 * s ^ 16
    - 131899184949 * s ^ 15
    + 190757276419 * s ^ 14
    - 243137802288 * s ^ 13
    + 268655168717 * s ^ 12
    - 252365225314 * s ^ 11
    + 196246611204 * s ^ 10
    - 120958751287 * s ^ 9
    + 54037902229 * s ^ 8
    - 13273671140 * s ^ 7
    - 1649235346 * s ^ 6
    + 2775175552 * s ^ 5
    - 954708175 * s ^ 4
    + 92441133 * s ^ 3
    + 18312046 * s ^ 2
    - 2745132 * s
    - 44515

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient24 (s : ℚ) : ℚ :=
  s ^ 33
    - 42 * s ^ 32
    + 783 * s ^ 31
    - 8669 * s ^ 30
    + 64128 * s ^ 29
    - 337820 * s ^ 28
    + 1325634 * s ^ 27
    - 4095841 * s ^ 26
    + 11183610 * s ^ 25
    - 32856401 * s ^ 24
    + 113725922 * s ^ 23
    - 405232061 * s ^ 22
    + 1304387526 * s ^ 21
    - 3653913517 * s ^ 20
    + 8963700025 * s ^ 19
    - 19522760305 * s ^ 18
    + 38046290244 * s ^ 17
    - 66353222037 * s ^ 16
    + 103059328817 * s ^ 15
    - 141465128703 * s ^ 14
    + 169769755287 * s ^ 13
    - 175370194335 * s ^ 12
    + 152396675609 * s ^ 11
    - 107347191563 * s ^ 10
    + 56918329541 * s ^ 9
    - 18322095763 * s ^ 8
    - 778693742 * s ^ 7
    + 4640615019 * s ^ 6
    - 2547396271 * s ^ 5
    + 607806060 * s ^ 4
    - 9756912 * s ^ 3
    - 22729053 * s ^ 2
    + 2363446 * s
    + 61383

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient25 (s : ℚ) : ℚ :=
  -4 * s ^ 31
    + 162 * s ^ 30
    - 3052 * s ^ 29
    + 35771 * s ^ 28
    - 294601 * s ^ 27
    + 1828234 * s ^ 26
    - 8969399 * s ^ 25
    + 36127258 * s ^ 24
    - 123476828 * s ^ 23
    + 369054112 * s ^ 22
    - 989654863 * s ^ 21
    + 2422349260 * s ^ 20
    - 5443720198 * s ^ 19
    + 11187751134 * s ^ 18
    - 20841273740 * s ^ 17
    + 34855123122 * s ^ 16
    - 51845504180 * s ^ 15
    + 67858902000 * s ^ 14
    - 77013702270 * s ^ 13
    + 74139194977 * s ^ 12
    - 58378272920 * s ^ 11
    + 34902700317 * s ^ 10
    - 12562858907 * s ^ 9
    - 1396102230 * s ^ 8
    + 5582642152 * s ^ 7
    - 3989465052 * s ^ 6
    + 1478859931 * s ^ 5
    - 217272256 * s ^ 4
    - 42233197 * s ^ 3
    + 19827565 * s ^ 2
    - 1525892 * s
    - 66406

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient26 (s : ℚ) : ℚ :=
  6 * s ^ 29
    - 237 * s ^ 28
    + 4409 * s ^ 27
    - 51622 * s ^ 26
    + 429056 * s ^ 25
    - 2707601 * s ^ 24
    + 13548152 * s ^ 23
    - 55409122 * s ^ 22
    + 189417474 * s ^ 21
    - 550644482 * s ^ 20
    + 1379716804 * s ^ 19
    - 3010242600 * s ^ 18
    + 5755584829 * s ^ 17
    - 9658185061 * s ^ 16
    + 14155305065 * s ^ 15
    - 17891879320 * s ^ 14
    + 19048315490 * s ^ 13
    - 16330537184 * s ^ 12
    + 10100216282 * s ^ 11
    - 2638459591 * s ^ 10
    - 3017369342 * s ^ 9
    + 5040489717 * s ^ 8
    - 3977469787 * s ^ 7
    + 1907040306 * s ^ 6
    - 481999288 * s ^ 5
    - 12031957 * s ^ 4
    + 48590003 * s ^ 3
    - 12402435 * s ^ 2
    + 676191 * s
    + 55845

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient27 (s : ℚ) : ℚ :=
  -4 * s ^ 27
    + 150 * s ^ 26
    - 2652 * s ^ 25
    + 29525 * s ^ 24
    - 233305 * s ^ 23
    + 1397906 * s ^ 22
    - 6618705 * s ^ 21
    + 25434514 * s ^ 20
    - 80663207 * s ^ 19
    + 212982638 * s ^ 18
    - 468988085 * s ^ 17
    + 855877085 * s ^ 16
    - 1270583949 * s ^ 15
    + 1464161206 * s ^ 14
    - 1128915831 * s ^ 13
    + 122006467 * s ^ 12
    + 1313846133 * s ^ 11
    - 2560482762 * s ^ 10
    + 2981623305 * s ^ 9
    - 2420922693 * s ^ 8
    + 1352274320 * s ^ 7
    - 446532532 * s ^ 6
    + 16361986 * s ^ 5
    + 62154305 * s ^ 4
    - 29394732 * s ^ 3
    + 5375826 * s ^ 2
    - 151098 * s
    - 35811

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient28 (s : ℚ) : ℚ :=
  s ^ 25
    - 32 * s ^ 24
    + 463 * s ^ 23
    - 3955 * s ^ 22
    + 21467 * s ^ 21
    - 69395 * s ^ 20
    + 51668 * s ^ 19
    + 834904 * s ^ 18
    - 5833244 * s ^ 17
    + 23828964 * s ^ 16
    - 72406128 * s ^ 15
    + 175743768 * s ^ 14
    - 350608050 * s ^ 13
    + 579538142 * s ^ 12
    - 788261261 * s ^ 11
    + 863989398 * s ^ 10
    - 733968962 * s ^ 9
    + 447236122 * s ^ 8
    - 154687484 * s ^ 7
    - 16845962 * s ^ 6
    + 56742352 * s ^ 5
    - 34527042 * s ^ 4
    + 10685134 * s ^ 3
    - 1449393 * s ^ 2
    - 28404 * s
    + 16929

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient29 (s : ℚ) : ℚ :=
  -2 * s ^ 22
    + 70 * s ^ 21
    - 1146 * s ^ 20
    + 11682 * s ^ 19
    - 83266 * s ^ 18
    + 441592 * s ^ 17
    - 1808374 * s ^ 16
    + 5846198 * s ^ 15
    - 15084072 * s ^ 14
    + 31079187 * s ^ 13
    - 50550791 * s ^ 12
    + 62941833 * s ^ 11
    - 55519143 * s ^ 10
    + 25847472 * s ^ 9
    + 11266476 * s ^ 8
    - 34544613 * s ^ 7
    + 35234798 * s ^ 6
    - 22119784 * s ^ 5
    + 8952309 * s ^ 4
    - 2101088 * s ^ 3
    + 161781 * s ^ 2
    + 34443 * s
    - 5562

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient30 (s : ℚ) : ℚ :=
  s ^ 19
    - 34 * s ^ 18
    + 536 * s ^ 17
    - 5200 * s ^ 16
    + 34751 * s ^ 15
    - 169698 * s ^ 14
    + 626859 * s ^ 13
    - 1789152 * s ^ 12
    + 3995917 * s ^ 11
    - 7030169 * s ^ 10
    + 9760436 * s ^ 9
    - 10661196 * s ^ 8
    + 9074985 * s ^ 7
    - 5894940 * s ^ 6
    + 2792853 * s ^ 5
    - 865702 * s ^ 4
    + 117126 * s ^ 3
    + 22509 * s ^ 2
    - 11016 * s
    + 1134

/-- Coefficient of the indicated power of the raw chart variable. -/
def t1Step3Coefficient31 (s : ℚ) : ℚ :=
  -s ^ 12
    + 23 * s ^ 11
    - 235 * s ^ 10
    + 1406 * s ^ 9
    - 5467 * s ^ 8
    + 14498 * s ^ 7
    - 26771 * s ^ 6
    + 34508 * s ^ 5
    - 30628 * s ^ 4
    + 18103 * s ^ 3
    - 6678 * s ^ 2
    + 1350 * s
    - 108

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
    t1Step3Coefficient29 s * r ^ 29 +
    t1Step3Coefficient30 s * r ^ 30 +
    t1Step3Coefficient31 s * r ^ 31

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_0 (s : ℚ) :
    t1Step3Coefficient0 s =
    t1Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient0,
    t1Step2Coefficient0,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_1 (s : ℚ) :
    t1Step3Coefficient1 s =
    t1Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient1,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_2 (s : ℚ) :
    t1Step3Coefficient2 s =
    t1Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient2,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_3 (s : ℚ) :
    t1Step3Coefficient3 s =
    t1Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient3,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_4 (s : ℚ) :
    t1Step3Coefficient4 s =
    t1Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient4,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_5 (s : ℚ) :
    t1Step3Coefficient5 s =
    t1Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient5,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_6 (s : ℚ) :
    t1Step3Coefficient6 s =
    t1Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient6,
    t1Step2Coefficient0,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_7 (s : ℚ) :
    t1Step3Coefficient7 s =
    t1Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient0 s
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
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_8 (s : ℚ) :
    t1Step3Coefficient8 s =
    t1Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient8,
    t1Step2Coefficient1,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_9 (s : ℚ) :
    t1Step3Coefficient9 s =
    t1Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient9,
    t1Step2Coefficient2,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_10 (s : ℚ) :
    t1Step3Coefficient10 s =
    t1Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient10,
    t1Step2Coefficient3,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_11 (s : ℚ) :
    t1Step3Coefficient11 s =
    t1Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient11,
    t1Step2Coefficient4,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_12 (s : ℚ) :
    t1Step3Coefficient12 s =
    t1Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient12,
    t1Step2Coefficient5,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_13 (s : ℚ) :
    t1Step3Coefficient13 s =
    t1Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient13,
    t1Step2Coefficient6,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_14 (s : ℚ) :
    t1Step3Coefficient14 s =
    t1Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient14,
    t1Step2Coefficient7,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_15 (s : ℚ) :
    t1Step3Coefficient15 s =
    t1Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient15,
    t1Step2Coefficient8,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    t1Step2Coefficient15,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_16 (s : ℚ) :
    t1Step3Coefficient16 s =
    t1Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient16,
    t1Step2Coefficient9,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    t1Step2Coefficient15,
    t1Step2Coefficient16,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_17 (s : ℚ) :
    t1Step3Coefficient17 s =
    t1Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient17,
    t1Step2Coefficient10,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    t1Step2Coefficient15,
    t1Step2Coefficient16,
    t1Step2Coefficient17,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_18 (s : ℚ) :
    t1Step3Coefficient18 s =
    t1Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient18,
    t1Step2Coefficient11,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    t1Step2Coefficient15,
    t1Step2Coefficient16,
    t1Step2Coefficient17,
    t1Step2Coefficient18,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_19 (s : ℚ) :
    t1Step3Coefficient19 s =
    t1Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient19,
    t1Step2Coefficient12,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    t1Step2Coefficient15,
    t1Step2Coefficient16,
    t1Step2Coefficient17,
    t1Step2Coefficient18,
    t1Step2Coefficient19,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_20 (s : ℚ) :
    t1Step3Coefficient20 s =
    t1Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient20,
    t1Step2Coefficient13,
    t1Step2Coefficient14,
    t1Step2Coefficient15,
    t1Step2Coefficient16,
    t1Step2Coefficient17,
    t1Step2Coefficient18,
    t1Step2Coefficient19,
    t1Step2Coefficient20,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_21 (s : ℚ) :
    t1Step3Coefficient21 s =
    t1Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient21,
    t1Step2Coefficient14,
    t1Step2Coefficient15,
    t1Step2Coefficient16,
    t1Step2Coefficient17,
    t1Step2Coefficient18,
    t1Step2Coefficient19,
    t1Step2Coefficient20,
    t1Step2Coefficient21,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_22 (s : ℚ) :
    t1Step3Coefficient22 s =
    t1Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient22,
    t1Step2Coefficient15,
    t1Step2Coefficient16,
    t1Step2Coefficient17,
    t1Step2Coefficient18,
    t1Step2Coefficient19,
    t1Step2Coefficient20,
    t1Step2Coefficient21,
    t1Step2Coefficient22,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_23 (s : ℚ) :
    t1Step3Coefficient23 s =
    t1Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient23,
    t1Step2Coefficient16,
    t1Step2Coefficient17,
    t1Step2Coefficient18,
    t1Step2Coefficient19,
    t1Step2Coefficient20,
    t1Step2Coefficient21,
    t1Step2Coefficient22,
    t1Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_24 (s : ℚ) :
    t1Step3Coefficient24 s =
    t1Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient1 s
      + t1Step2Coefficient24 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t1Step3Coefficient24,
    t1Step2Coefficient17,
    t1Step2Coefficient18,
    t1Step2Coefficient19,
    t1Step2Coefficient20,
    t1Step2Coefficient21,
    t1Step2Coefficient22,
    t1Step2Coefficient23,
    t1Step2Coefficient24,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_25 (s : ℚ) :
    t1Step3Coefficient25 s =
    t1Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient2 s
      + t1Step2Coefficient24 s *
        rawUnitOneDenominatorCoefficient1 s
    := by
  simp only [t1Step3Coefficient25,
    t1Step2Coefficient18,
    t1Step2Coefficient19,
    t1Step2Coefficient20,
    t1Step2Coefficient21,
    t1Step2Coefficient22,
    t1Step2Coefficient23,
    t1Step2Coefficient24,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_26 (s : ℚ) :
    t1Step3Coefficient26 s =
    t1Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient3 s
      + t1Step2Coefficient24 s *
        rawUnitOneDenominatorCoefficient2 s
    := by
  simp only [t1Step3Coefficient26,
    t1Step2Coefficient19,
    t1Step2Coefficient20,
    t1Step2Coefficient21,
    t1Step2Coefficient22,
    t1Step2Coefficient23,
    t1Step2Coefficient24,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_27 (s : ℚ) :
    t1Step3Coefficient27 s =
    t1Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient4 s
      + t1Step2Coefficient24 s *
        rawUnitOneDenominatorCoefficient3 s
    := by
  simp only [t1Step3Coefficient27,
    t1Step2Coefficient20,
    t1Step2Coefficient21,
    t1Step2Coefficient22,
    t1Step2Coefficient23,
    t1Step2Coefficient24,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_28 (s : ℚ) :
    t1Step3Coefficient28 s =
    t1Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient5 s
      + t1Step2Coefficient24 s *
        rawUnitOneDenominatorCoefficient4 s
    := by
  simp only [t1Step3Coefficient28,
    t1Step2Coefficient21,
    t1Step2Coefficient22,
    t1Step2Coefficient23,
    t1Step2Coefficient24,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_29 (s : ℚ) :
    t1Step3Coefficient29 s =
    t1Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient6 s
      + t1Step2Coefficient24 s *
        rawUnitOneDenominatorCoefficient5 s
    := by
  simp only [t1Step3Coefficient29,
    t1Step2Coefficient22,
    t1Step2Coefficient23,
    t1Step2Coefficient24,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_30 (s : ℚ) :
    t1Step3Coefficient30 s =
    t1Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient7 s
      + t1Step2Coefficient24 s *
        rawUnitOneDenominatorCoefficient6 s
    := by
  simp only [t1Step3Coefficient30,
    t1Step2Coefficient23,
    t1Step2Coefficient24,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t1Step3Coefficient_product_certificate_31 (s : ℚ) :
    t1Step3Coefficient31 s =
    t1Step2Coefficient24 s *
        rawUnitOneDenominatorCoefficient7 s
    := by
  simp only [t1Step3Coefficient31,
    t1Step2Coefficient24,
    rawUnitOneDenominatorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t1Step3_eq_t1Step2_mul_rawUnitOneDenominator (r s : ℚ) :
    t1Step3 r s = t1Step2 r s * rawUnitOneDenominator r s := by
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
  have h30 := t1Step3Coefficient_product_certificate_30 s
  have h31 := t1Step3Coefficient_product_certificate_31 s
  simp only [t1Step3, t1Step2, rawUnitOneDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient2 (s : ℚ) : ℚ :=
  s ^ 36
    - 7 * s ^ 35
    + 28 * s ^ 34
    - 80 * s ^ 33
    + 179 * s ^ 32
    - 329 * s ^ 31
    + 510 * s ^ 30
    - 678 * s ^ 29
    + 780 * s ^ 28
    - 780 * s ^ 27
    + 678 * s ^ 26
    - 510 * s ^ 25
    + 329 * s ^ 24
    - 179 * s ^ 23
    + 80 * s ^ 22
    - 28 * s ^ 21
    + 7 * s ^ 20
    - s ^ 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient3 (s : ℚ) : ℚ :=
  s ^ 39
    - 12 * s ^ 38
    + 75 * s ^ 37
    - 313 * s ^ 36
    + 942 * s ^ 35
    - 2178 * s ^ 34
    + 3962 * s ^ 33
    - 5649 * s ^ 32
    + 5928 * s ^ 31
    - 3249 * s ^ 30
    - 3265 * s ^ 29
    + 12978 * s ^ 28
    - 23558 * s ^ 27
    + 31847 * s ^ 26
    - 35313 * s ^ 25
    + 33241 * s ^ 24
    - 26940 * s ^ 23
    + 18870 * s ^ 22
    - 11402 * s ^ 21
    + 5901 * s ^ 20
    - 2586 * s ^ 19
    + 945 * s ^ 18
    - 281 * s ^ 17
    + 66 * s ^ 16
    - 11 * s ^ 15
    + s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient4 (s : ℚ) : ℚ :=
  -2 * s ^ 41
    + 27 * s ^ 40
    - 184 * s ^ 39
    + 801 * s ^ 38
    - 2390 * s ^ 37
    + 4706 * s ^ 36
    - 4088 * s ^ 35
    - 10060 * s ^ 34
    + 56859 * s ^ 33
    - 158738 * s ^ 32
    + 328341 * s ^ 31
    - 552247 * s ^ 30
    + 782833 * s ^ 29
    - 949096 * s ^ 28
    + 985230 * s ^ 27
    - 864367 * s ^ 26
    + 615583 * s ^ 25
    - 313061 * s ^ 24
    + 42274 * s ^ 23
    + 137079 * s ^ 22
    - 209823 * s ^ 21
    + 199940 * s ^ 20
    - 148317 * s ^ 19
    + 90745 * s ^ 18
    - 46727 * s ^ 17
    + 20341 * s ^ 16
    - 7466 * s ^ 15
    + 2272 * s ^ 14
    - 557 * s ^ 13
    + 105 * s ^ 12
    - 14 * s ^ 11
    + s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient5 (s : ℚ) : ℚ :=
  s ^ 43
    - 15 * s ^ 42
    + 101 * s ^ 41
    - 316 * s ^ 40
    - 260 * s ^ 39
    + 8087 * s ^ 38
    - 47353 * s ^ 37
    + 179369 * s ^ 36
    - 513365 * s ^ 35
    + 1177062 * s ^ 34
    - 2224847 * s ^ 33
    + 3499397 * s ^ 32
    - 4534947 * s ^ 31
    + 4608607 * s ^ 30
    - 3003327 * s ^ 29
    - 594625 * s ^ 28
    + 5780481 * s ^ 27
    - 11415119 * s ^ 26
    + 16006055 * s ^ 25
    - 18311498 * s ^ 24
    + 17860236 * s ^ 23
    - 15099648 * s ^ 22
    + 11107487 * s ^ 21
    - 7074285 * s ^ 20
    + 3841317 * s ^ 19
    - 1718766 * s ^ 18
    + 580986 * s ^ 17
    - 101325 * s ^ 16
    - 37643 * s ^ 15
    + 46564 * s ^ 14
    - 26492 * s ^ 13
    + 10743 * s ^ 12
    - 3331 * s ^ 11
    + 792 * s ^ 10
    - 138 * s ^ 9
    + 16 * s ^ 8
    - s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient6 (s : ℚ) : ℚ :=
  -2 * s ^ 44
    + 47 * s ^ 43
    - 565 * s ^ 42
    + 4432 * s ^ 41
    - 25031 * s ^ 40
    + 107150 * s ^ 39
    - 358032 * s ^ 38
    + 944473 * s ^ 37
    - 1944011 * s ^ 36
    + 2922226 * s ^ 35
    - 2268104 * s ^ 34
    - 3359436 * s ^ 33
    + 18859037 * s ^ 32
    - 49206451 * s ^ 31
    + 96777369 * s ^ 30
    - 158453780 * s ^ 29
    + 224296314 * s ^ 28
    - 279267326 * s ^ 27
    + 308026741 * s ^ 26
    - 301061384 * s ^ 25
    + 259004132 * s ^ 24
    - 192821513 * s ^ 23
    + 119471945 * s ^ 22
    - 55256902 * s ^ 21
    + 10298053 * s ^ 20
    + 13492964 * s ^ 19
    - 20590342 * s ^ 18
    + 18090574 * s ^ 17
    - 12262918 * s ^ 16
    + 6864837 * s ^ 15
    - 3243871 * s ^ 14
    + 1295923 * s ^ 13
    - 433157 * s ^ 12
    + 118497 * s ^ 11
    - 25515 * s ^ 10
    + 3996 * s ^ 9
    - 381 * s ^ 8
    + 9 * s ^ 7
    + 2 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient7 (s : ℚ) : ℚ :=
  s ^ 46
    - 23 * s ^ 45
    + 265 * s ^ 44
    - 1979 * s ^ 43
    + 10385 * s ^ 42
    - 38211 * s ^ 41
    + 85190 * s ^ 40
    + 10113 * s ^ 39
    - 1097587 * s ^ 38
    + 5971622 * s ^ 37
    - 21431153 * s ^ 36
    + 60303313 * s ^ 35
    - 141391503 * s ^ 34
    + 284962928 * s ^ 33
    - 502761803 * s ^ 32
    + 784657459 * s ^ 31
    - 1088108567 * s ^ 30
    + 1338181588 * s ^ 29
    - 1444182032 * s ^ 28
    + 1330989160 * s ^ 27
    - 973951766 * s ^ 26
    + 420592219 * s ^ 25
    + 215724947 * s ^ 24
    - 791125470 * s ^ 23
    + 1182312549 * s ^ 22
    - 1329054189 * s ^ 21
    + 1248172218 * s ^ 20
    - 1015127853 * s ^ 19
    + 725467306 * s ^ 18
    - 458099463 * s ^ 17
    + 255673063 * s ^ 16
    - 125634613 * s ^ 15
    + 53907936 * s ^ 14
    - 19899332 * s ^ 13
    + 6173192 * s ^ 12
    - 1548851 * s ^ 11
    + 292128 * s ^ 10
    - 34011 * s ^ 9
    + 265 * s ^ 8
    + 649 * s ^ 7
    - 90 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient8 (s : ℚ) : ℚ :=
  5 * s ^ 46
    - 144 * s ^ 45
    + 2030 * s ^ 44
    - 18803 * s ^ 43
    + 128518 * s ^ 42
    - 688120 * s ^ 41
    + 2989276 * s ^ 40
    - 10778886 * s ^ 39
    + 32780414 * s ^ 38
    - 85047976 * s ^ 37
    + 189687859 * s ^ 36
    - 364873695 * s ^ 35
    + 602841472 * s ^ 34
    - 838536290 * s ^ 33
    + 919535872 * s ^ 32
    - 595629190 * s ^ 31
    - 450191468 * s ^ 30
    + 2516294067 * s ^ 29
    - 5749740600 * s ^ 28
    + 10009884282 * s ^ 27
    - 14794500619 * s ^ 26
    + 19292803834 * s ^ 25
    - 22586265814 * s ^ 24
    + 23938419867 * s ^ 23
    - 23058804664 * s ^ 22
    + 20210917666 * s ^ 21
    - 16108808710 * s ^ 20
    + 11651575042 * s ^ 19
    - 7622306331 * s ^ 18
    + 4488519753 * s ^ 17
    - 2363181231 * s ^ 16
    + 1101412496 * s ^ 15
    - 447614763 * s ^ 14
    + 154778082 * s ^ 13
    - 43693016 * s ^ 12
    + 9246797 * s ^ 11
    - 1110263 * s ^ 10
    - 85990 * s ^ 9
    + 73208 * s ^ 8
    - 15246 * s ^ 7
    + 1227 * s ^ 6
    + 54 * s ^ 5
    - 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 48
    + 29 * s ^ 47
    - 423 * s ^ 46
    + 4061 * s ^ 45
    - 28469 * s ^ 44
    + 153381 * s ^ 43
    - 649721 * s ^ 42
    + 2159290 * s ^ 41
    - 5385912 * s ^ 40
    + 8241143 * s ^ 39
    + 4361052 * s ^ 38
    - 85449643 * s ^ 37
    + 372050218 * s ^ 36
    - 1151228616 * s ^ 35
    + 2933037562 * s ^ 34
    - 6505176941 * s ^ 33
    + 12929942363 * s ^ 32
    - 23425149253 * s ^ 31
    + 39069849856 * s ^ 30
    - 60324586990 * s ^ 29
    + 86462193208 * s ^ 28
    - 115147979239 * s ^ 27
    + 142461054584 * s ^ 26
    - 163574154493 * s ^ 25
    + 174033255161 * s ^ 24
    - 171218969846 * s ^ 23
    + 155374492323 * s ^ 22
    - 129655532924 * s ^ 21
    + 99126627796 * s ^ 20
    - 69125326301 * s ^ 19
    + 43720107700 * s ^ 18
    - 24894337863 * s ^ 17
    + 12626790419 * s ^ 16
    - 5613061640 * s ^ 15
    + 2128555879 * s ^ 14
    - 654127826 * s ^ 13
    + 143897879 * s ^ 12
    - 11735969 * s ^ 11
    - 6816337 * s ^ 10
    + 3789624 * s ^ 9
    - 998394 * s ^ 8
    + 138358 * s ^ 7
    - 3479 * s ^ 6
    - 1655 * s ^ 5
    + 48 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 48
    + 43 * s ^ 47
    - 825 * s ^ 46
    + 9961 * s ^ 45
    - 86751 * s ^ 44
    + 585939 * s ^ 43
    - 3208977 * s ^ 42
    + 14681007 * s ^ 41
    - 57333192 * s ^ 40
    + 194451533 * s ^ 39
    - 581546974 * s ^ 38
    + 1555944613 * s ^ 37
    - 3776638648 * s ^ 36
    + 8424977749 * s ^ 35
    - 17462952306 * s ^ 34
    + 33885466185 * s ^ 33
    - 61775926009 * s ^ 32
    + 105851224296 * s ^ 31
    - 170216999012 * s ^ 30
    + 256339048211 * s ^ 29
    - 360740354756 * s ^ 28
    + 473452128127 * s ^ 27
    - 578387223907 * s ^ 26
    + 656387983601 * s ^ 25
    - 690493861918 * s ^ 24
    + 671635573137 * s ^ 23
    - 602289453022 * s ^ 22
    + 496149073806 * s ^ 21
    - 373772868920 * s ^ 20
    + 256018625572 * s ^ 19
    - 158176293548 * s ^ 18
    + 87120473119 * s ^ 17
    - 41967270914 * s ^ 16
    + 17078794003 * s ^ 15
    - 5441072373 * s ^ 14
    + 1047719074 * s ^ 13
    + 121930147 * s ^ 12
    - 215217618 * s ^ 11
    + 106967097 * s ^ 10
    - 33163790 * s ^ 9
    + 6363533 * s ^ 8
    - 485766 * s ^ 7
    - 83397 * s ^ 6
    + 22213 * s ^ 5
    - 303 * s ^ 4
    - 39 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 49
    + 33 * s ^ 48
    - 540 * s ^ 47
    + 5807 * s ^ 46
    - 46100 * s ^ 45
    + 288148 * s ^ 44
    - 1478752 * s ^ 43
    + 6426392 * s ^ 42
    - 24274775 * s ^ 41
    + 81720929 * s ^ 40
    - 251457749 * s ^ 39
    + 723706955 * s ^ 38
    - 1978672626 * s ^ 37
    + 5159603349 * s ^ 36
    - 12752123460 * s ^ 35
    + 29557206707 * s ^ 34
    - 63646447202 * s ^ 33
    + 126615567798 * s ^ 32
    - 232270091668 * s ^ 31
    + 393104125865 * s ^ 30
    - 614647637798 * s ^ 29
    + 888989761739 * s ^ 28
    - 1190166340423 * s ^ 27
    + 1474749314594 * s ^ 26
    - 1689949447447 * s ^ 25
    + 1788143208377 * s ^ 24
    - 1742977369381 * s ^ 23
    + 1560017471307 * s ^ 22
    - 1276333459611 * s ^ 21
    + 948589104849 * s ^ 20
    - 634553559814 * s ^ 19
    + 376482351396 * s ^ 18
    - 192991582192 * s ^ 17
    + 80881563435 * s ^ 16
    - 23602855796 * s ^ 15
    + 833343814 * s ^ 14
    + 4576296363 * s ^ 13
    - 3678088926 * s ^ 12
    + 1820175352 * s ^ 11
    - 641058945 * s ^ 10
    + 154541457 * s ^ 9
    - 18983114 * s ^ 8
    - 1831392 * s ^ 7
    + 1194042 * s ^ 6
    - 168820 * s ^ 5
    - 2841 * s ^ 4
    + 663 * s ^ 3
    + 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient12 (s : ℚ) : ℚ :=
  5 * s ^ 48
    - 144 * s ^ 47
    + 2032 * s ^ 46
    - 18501 * s ^ 45
    + 120274 * s ^ 44
    - 577220 * s ^ 43
    + 1976442 * s ^ 42
    - 3714397 * s ^ 41
    - 7055629 * s ^ 40
    + 102341262 * s ^ 39
    - 560521732 * s ^ 38
    + 2230374343 * s ^ 37
    - 7256812511 * s ^ 36
    + 20251354004 * s ^ 35
    - 49793846924 * s ^ 34
    + 109854695782 * s ^ 33
    - 220380911721 * s ^ 32
    + 405850535747 * s ^ 31
    - 690212558258 * s ^ 30
    + 1087158460036 * s ^ 29
    - 1587112535378 * s ^ 28
    + 2146036692799 * s ^ 27
    - 2683689659034 * s ^ 26
    + 3097305589497 * s ^ 25
    - 3289781224688 * s ^ 24
    + 3203422333892 * s ^ 23
    - 2844346233811 * s ^ 22
    + 2284602518101 * s ^ 21
    - 1639171651006 * s ^ 20
    + 1027329990860 * s ^ 19
    - 536848167292 * s ^ 18
    + 205482708702 * s ^ 17
    - 23741809817 * s ^ 16
    - 47425624675 * s ^ 15
    + 55261108366 * s ^ 14
    - 38465954373 * s ^ 13
    + 19863414849 * s ^ 12
    - 7827154114 * s ^ 11
    + 2236634887 * s ^ 10
    - 367248547 * s ^ 9
    - 21815409 * s ^ 8
    + 31675815 * s ^ 7
    - 8238052 * s ^ 6
    + 743581 * s ^ 5
    + 68631 * s ^ 4
    - 6610 * s ^ 3
    - 64 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient13 (s : ℚ) : ℚ :=
  3 * s ^ 48
    - 115 * s ^ 47
    + 2073 * s ^ 46
    - 24009 * s ^ 45
    + 203505 * s ^ 44
    - 1356126 * s ^ 43
    + 7426791 * s ^ 42
    - 34413952 * s ^ 41
    + 137674671 * s ^ 40
    - 482871580 * s ^ 39
    + 1505222002 * s ^ 38
    - 4228624089 * s ^ 37
    + 10864782948 * s ^ 36
    - 25905775798 * s ^ 35
    + 58016873644 * s ^ 34
    - 122853203184 * s ^ 33
    + 245952082891 * s ^ 32
    - 463009747915 * s ^ 31
    + 813540518627 * s ^ 30
    - 1325496962441 * s ^ 29
    + 1993494305572 * s ^ 28
    - 2759325262187 * s ^ 27
    + 3506806180342 * s ^ 26
    - 4080303889920 * s ^ 25
    + 4327369066111 * s ^ 24
    - 4153601531441 * s ^ 23
    + 3565567904592 * s ^ 22
    - 2678527042078 * s ^ 21
    + 1680934533584 * s ^ 20
    - 770397672064 * s ^ 19
    + 91980147352 * s ^ 18
    + 297132423988 * s ^ 17
    - 426589898190 * s ^ 16
    + 382274910581 * s ^ 15
    - 263353445102 * s ^ 14
    + 145135485169 * s ^ 13
    - 63369695361 * s ^ 12
    + 20698657179 * s ^ 11
    - 4072164826 * s ^ 10
    - 217366832 * s ^ 9
    + 513844796 * s ^ 8
    - 194791081 * s ^ 7
    + 35307582 * s ^ 6
    - 1208885 * s ^ 5
    - 651006 * s ^ 4
    + 43227 * s ^ 3
    + 951 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient14 (s : ℚ) : ℚ :=
  -11 * s ^ 47
    + 341 * s ^ 46
    - 5096 * s ^ 45
    + 49434 * s ^ 44
    - 352102 * s ^ 43
    + 1966330 * s ^ 42
    - 8911998 * s ^ 41
    + 33081853 * s ^ 40
    - 98312663 * s ^ 39
    + 212521774 * s ^ 38
    - 190679974 * s ^ 37
    - 963732867 * s ^ 36
    + 6607739419 * s ^ 35
    - 25352396719 * s ^ 34
    + 74904146889 * s ^ 33
    - 184829142971 * s ^ 32
    + 394830177378 * s ^ 31
    - 745665467160 * s ^ 30
    + 1262450261991 * s ^ 29
    - 1933183920185 * s ^ 28
    + 2688689039008 * s ^ 27
    - 3394536124299 * s ^ 26
    + 3868008743420 * s ^ 25
    - 3927791574157 * s ^ 24
    + 3465626397395 * s ^ 23
    - 2506632655245 * s ^ 22
    + 1223849671655 * s ^ 21
    + 107808029081 * s ^ 20
    - 1200535373845 * s ^ 19
    + 1847703190363 * s ^ 18
    - 1989154654802 * s ^ 17
    + 1718965871843 * s ^ 16
    - 1231524258220 * s ^ 15
    + 730913800241 * s ^ 14
    - 350554644010 * s ^ 13
    + 127019147841 * s ^ 12
    - 27376696357 * s ^ 11
    - 2833559620 * s ^ 10
    + 5733946104 * s ^ 9
    - 2774030525 * s ^ 8
    + 743897917 * s ^ 7
    - 91082114 * s ^ 6
    - 7866752 * s ^ 5
    + 3961809 * s ^ 4
    - 191559 * s ^ 3
    - 8808 * s ^ 2
    - 27 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient15 (s : ℚ) : ℚ :=
  -3 * s ^ 47
    + 121 * s ^ 46
    - 2213 * s ^ 45
    + 25487 * s ^ 44
    - 214244 * s ^ 43
    + 1435545 * s ^ 42
    - 8115005 * s ^ 41
    + 40001521 * s ^ 40
    - 174418905 * s ^ 39
    + 674714074 * s ^ 38
    - 2313703921 * s ^ 37
    + 7033798487 * s ^ 36
    - 19003152559 * s ^ 35
    + 45850155459 * s ^ 34
    - 99525683180 * s ^ 33
    + 196280490193 * s ^ 32
    - 355666421185 * s ^ 31
    + 597855315689 * s ^ 30
    - 935716084217 * s ^ 29
    + 1356580682289 * s ^ 28
    - 1795465877377 * s ^ 27
    + 2116100915114 * s ^ 26
    - 2125174229898 * s ^ 25
    + 1633805120108 * s ^ 24
    - 547973846270 * s ^ 23
    - 1055813221749 * s ^ 22
    + 2908912880270 * s ^ 21
    - 4604078775265 * s ^ 20
    + 5715997086910 * s ^ 19
    - 5957202182495 * s ^ 18
    + 5308557554772 * s ^ 17
    - 4039084802176 * s ^ 16
    + 2584572830301 * s ^ 15
    - 1344309682694 * s ^ 14
    + 522608873697 * s ^ 13
    - 108427581246 * s ^ 12
    - 33112846106 * s ^ 11
    + 47049271686 * s ^ 10
    - 26329174764 * s ^ 9
    + 9190991160 * s ^ 8
    - 1850861592 * s ^ 7
    + 61285077 * s ^ 6
    + 74179538 * s ^ 5
    - 17327334 * s ^ 4
    + 539294 * s ^ 3
    + 57253 * s ^ 2
    + 353 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient16 (s : ℚ) : ℚ :=
  6 * s ^ 46
    - 158 * s ^ 45
    + 1682 * s ^ 44
    - 7586 * s ^ 43
    - 17371 * s ^ 42
    + 498102 * s ^ 41
    - 3848414 * s ^ 40
    + 18796267 * s ^ 39
    - 65846712 * s ^ 38
    + 170645902 * s ^ 37
    - 323038255 * s ^ 36
    + 438909474 * s ^ 35
    - 616312534 * s ^ 34
    + 2426340741 * s ^ 33
    - 11963919543 * s ^ 32
    + 43352515000 * s ^ 31
    - 116862220923 * s ^ 30
    + 243122605810 * s ^ 29
    - 391734898708 * s ^ 28
    + 458844231634 * s ^ 27
    - 260384384393 * s ^ 26
    - 428599016145 * s ^ 25
    + 1792006333606 * s ^ 24
    - 3874194763374 * s ^ 23
    + 6494098402731 * s ^ 22
    - 9205020054768 * s ^ 21
    + 11352713107711 * s ^ 20
    - 12270289391876 * s ^ 19
    + 11576764600147 * s ^ 18
    - 9419353223230 * s ^ 17
    + 6459305445108 * s ^ 16
    - 3566481135497 * s ^ 15
    + 1404653670312 * s ^ 14
    - 188169082405 * s ^ 13
    - 262829274600 * s ^ 12
    + 289062820359 * s ^ 11
    - 176548192671 * s ^ 10
    + 74076101929 * s ^ 9
    - 20346337874 * s ^ 8
    + 2377138833 * s ^ 7
    + 640992065 * s ^ 6
    - 344073852 * s ^ 5
    + 56696879 * s ^ 4
    - 532954 * s ^ 3
    - 277481 * s ^ 2
    - 2974 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient17 (s : ℚ) : ℚ :=
  s ^ 46
    - 30 * s ^ 45
    + 262 * s ^ 44
    + 1391 * s ^ 43
    - 54229 * s ^ 42
    + 631985 * s ^ 41
    - 4622898 * s ^ 40
    + 24357036 * s ^ 39
    - 97031108 * s ^ 38
    + 293625919 * s ^ 37
    - 636073991 * s ^ 36
    + 694585914 * s ^ 35
    + 1464699814 * s ^ 34
    - 10929501379 * s ^ 33
    + 36598035395 * s ^ 32
    - 86823646875 * s ^ 31
    + 155624417486 * s ^ 30
    - 200524385361 * s ^ 29
    + 122416534051 * s ^ 28
    + 238817724724 * s ^ 27
    - 1086731459044 * s ^ 26
    + 2630557923639 * s ^ 25
    - 5023264166556 * s ^ 24
    + 8257339881736 * s ^ 23
    - 12018286046212 * s ^ 22
    + 15580732856604 * s ^ 21
    - 17906990627451 * s ^ 20
    + 18037234009162 * s ^ 19
    - 15632031654370 * s ^ 18
    + 11290610612152 * s ^ 17
    - 6338198385383 * s ^ 16
    + 2171485978568 * s ^ 15
    + 402037140190 * s ^ 14
    - 1385694108230 * s ^ 13
    + 1324807844673 * s ^ 12
    - 858794277239 * s ^ 11
    + 412325501914 * s ^ 10
    - 140382432869 * s ^ 9
    + 26242280333 * s ^ 8
    + 2698311350 * s ^ 7
    - 3582412521 * s ^ 6
    + 1105384857 * s ^ 5
    - 139110888 * s ^ 4
    - 3396119 * s ^ 3
    + 1035523 * s ^ 2
    + 18073 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient18 (s : ℚ) : ℚ :=
  s ^ 45
    - 96 * s ^ 44
    + 2877 * s ^ 43
    - 46877 * s ^ 42
    + 504005 * s ^ 41
    - 3945053 * s ^ 40
    + 23844794 * s ^ 39
    - 115678024 * s ^ 38
    + 462475912 * s ^ 37
    - 1550026491 * s ^ 36
    + 4389004279 * s ^ 35
    - 10453563462 * s ^ 34
    + 20436886868 * s ^ 33
    - 30469844629 * s ^ 32
    + 25264940861 * s ^ 31
    + 29696827016 * s ^ 30
    - 193265964919 * s ^ 29
    + 551886580239 * s ^ 28
    - 1229471048080 * s ^ 27
    + 2406717993709 * s ^ 26
    - 4322048999531 * s ^ 25
    + 7190226945063 * s ^ 24
    - 10990335135047 * s ^ 23
    + 15193233050167 * s ^ 22
    - 18660947705595 * s ^ 21
    + 19962087825345 * s ^ 20
    - 18090187644873 * s ^ 19
    + 13180531800314 * s ^ 18
    - 6649183056513 * s ^ 17
    + 541822824607 * s ^ 16
    + 3505171559894 * s ^ 15
    - 4984885989588 * s ^ 14
    + 4479023313244 * s ^ 13
    - 3054862766350 * s ^ 12
    + 1627101096626 * s ^ 11
    - 648037181701 * s ^ 10
    + 158776644370 * s ^ 9
    + 4130106352 * s ^ 8
    - 24021176588 * s ^ 7
    + 11243147158 * s ^ 6
    - 2651028029 * s ^ 5
    + 244082806 * s ^ 4
    + 22445817 * s ^ 3
    - 3016932 * s ^ 2
    - 83925 * s
    - 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient19 (s : ℚ) : ℚ :=
  -11 * s ^ 44
    + 492 * s ^ 43
    - 10145 * s ^ 42
    + 130172 * s ^ 41
    - 1180980 * s ^ 40
    + 8148959 * s ^ 39
    - 44886212 * s ^ 38
    + 204485355 * s ^ 37
    - 791776001 * s ^ 36
    + 2659596393 * s ^ 35
    - 7853807803 * s ^ 34
    + 20522016839 * s ^ 33
    - 47580039433 * s ^ 32
    + 98422573625 * s ^ 31
    - 184971793118 * s ^ 30
    + 328984056464 * s ^ 29
    - 587753153429 * s ^ 28
    + 1099002643726 * s ^ 27
    - 2112810409791 * s ^ 26
    + 3940412611884 * s ^ 25
    - 6754942986647 * s ^ 24
    + 10277842607139 * s ^ 23
    - 13554218483889 * s ^ 22
    + 15106622454761 * s ^ 21
    - 13585810377904 * s ^ 20
    + 8642873613502 * s ^ 19
    - 1418490868339 * s ^ 18
    - 5833918852310 * s ^ 17
    + 10849680709076 * s ^ 16
    - 12468527003224 * s ^ 15
    + 11033207627578 * s ^ 14
    - 7902748703059 * s ^ 13
    + 4579528065424 * s ^ 12
    - 2047510571462 * s ^ 11
    + 590615012821 * s ^ 10
    + 1903513409 * s ^ 9
    - 117121127732 * s ^ 8
    + 73265026451 * s ^ 7
    - 25147143777 * s ^ 6
    + 4804463743 * s ^ 5
    - 244880461 * s ^ 4
    - 78447969 * s ^ 3
    + 6837891 * s ^ 2
    + 307782 * s
    + 210

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient20 (s : ℚ) : ℚ :=
  -s ^ 44
    + 59 * s ^ 43
    - 1483 * s ^ 42
    + 22102 * s ^ 41
    - 225085 * s ^ 40
    + 1698793 * s ^ 39
    - 10037174 * s ^ 38
    + 48442240 * s ^ 37
    - 198137764 * s ^ 36
    + 709020706 * s ^ 35
    - 2267627767 * s ^ 34
    + 6499221474 * s ^ 33
    - 16352417638 * s ^ 32
    + 34461703447 * s ^ 31
    - 54912772470 * s ^ 30
    + 43081814520 * s ^ 29
    + 94319639843 * s ^ 28
    - 527759480157 * s ^ 27
    + 1468916854759 * s ^ 26
    - 3037596490355 * s ^ 25
    + 5042395076169 * s ^ 24
    - 6794381037097 * s ^ 23
    + 7160349366307 * s ^ 22
    - 4998785565695 * s ^ 21
    - 135170296932 * s ^ 20
    + 7431848229469 * s ^ 19
    - 14900861395244 * s ^ 18
    + 20196711492132 * s ^ 17
    - 21743881589068 * s ^ 16
    + 19456080610898 * s ^ 15
    - 14613062213471 * s ^ 14
    + 9070731507890 * s ^ 13
    - 4392912346157 * s ^ 12
    + 1350276576626 * s ^ 11
    + 92380689182 * s ^ 10
    - 452724431762 * s ^ 9
    + 335239664912 * s ^ 8
    - 149160064858 * s ^ 7
    + 42261568547 * s ^ 6
    - 6342267342 * s ^ 5
    - 117001800 * s ^ 4
    + 194800962 * s ^ 3
    - 11691186 * s ^ 2
    - 909204 * s
    - 1327

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient21 (s : ℚ) : ℚ :=
  2 * s ^ 43
    - 83 * s ^ 42
    + 1544 * s ^ 41
    - 17050 * s ^ 40
    + 123252 * s ^ 39
    - 592491 * s ^ 38
    + 1718166 * s ^ 37
    - 1323911 * s ^ 36
    - 10398133 * s ^ 35
    + 18789651 * s ^ 34
    + 313447013 * s ^ 33
    - 2917709494 * s ^ 32
    + 14859774869 * s ^ 31
    - 55069873003 * s ^ 30
    + 162037822792 * s ^ 29
    - 393629231202 * s ^ 28
    + 803014602878 * s ^ 27
    - 1374917516262 * s ^ 26
    + 1926015203385 * s ^ 25
    - 2018868653021 * s ^ 24
    + 987364891787 * s ^ 23
    + 1836677953660 * s ^ 22
    - 6716837899103 * s ^ 21
    + 13120214659180 * s ^ 20
    - 19641342657249 * s ^ 19
    + 24429223955393 * s ^ 18
    - 25968852483569 * s ^ 17
    + 23782385071788 * s ^ 16
    - 18636538806167 * s ^ 15
    + 12147473472634 * s ^ 14
    - 6064035745099 * s ^ 13
    + 1628902736680 * s ^ 12
    + 747163078065 * s ^ 11
    - 1416586954243 * s ^ 10
    + 1130840392523 * s ^ 9
    - 603625842291 * s ^ 8
    + 223984568758 * s ^ 7
    - 53154276746 * s ^ 6
    + 5162338901 * s ^ 5
    + 1087534043 * s ^ 4
    - 367883062 * s ^ 3
    + 13530454 * s ^ 2
    + 2188831 * s
    + 5930

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient22 (s : ℚ) : ℚ :=
  -26 * s ^ 41
    + 1121 * s ^ 40
    - 22970 * s ^ 39
    + 299310 * s ^ 38
    - 2796164 * s ^ 37
    + 19983397 * s ^ 36
    - 113651402 * s ^ 35
    + 527629393 * s ^ 34
    - 2033792906 * s ^ 33
    + 6583065939 * s ^ 32
    - 18009492686 * s ^ 31
    + 41634654197 * s ^ 30
    - 80226829120 * s ^ 29
    + 122490860645 * s ^ 28
    - 120551884851 * s ^ 27
    - 42098928482 * s ^ 26
    + 577318759503 * s ^ 25
    - 1780668814292 * s ^ 24
    + 3944046155336 * s ^ 23
    - 7186264748440 * s ^ 22
    + 11260178569578 * s ^ 21
    - 15457710800213 * s ^ 20
    + 18732450657341 * s ^ 19
    - 20048831547850 * s ^ 18
    + 18809415825991 * s ^ 17
    - 15145337454885 * s ^ 16
    + 9917329980830 * s ^ 15
    - 4420858038429 * s ^ 14
    - 65351732195 * s ^ 13
    + 2723276062940 * s ^ 12
    - 3462965940041 * s ^ 11
    + 2851978247479 * s ^ 10
    - 1736679412085 * s ^ 9
    + 786940828587 * s ^ 8
    - 251326398214 * s ^ 7
    + 46769243945 * s ^ 6
    + 127384683 * s ^ 5
    - 2582527818 * s ^ 4
    + 536195113 * s ^ 3
    - 5252191 * s ^ 2
    - 4320195 * s
    - 19873

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient23 (s : ℚ) : ℚ :=
  -2 * s ^ 41
    + 103 * s ^ 40
    - 2461 * s ^ 39
    + 36846 * s ^ 38
    - 392445 * s ^ 37
    + 3190609 * s ^ 36
    - 20691883 * s ^ 35
    + 110262154 * s ^ 34
    - 493399748 * s ^ 33
    + 1887993539 * s ^ 32
    - 6286118333 * s ^ 31
    + 18541144644 * s ^ 30
    - 49321426581 * s ^ 29
    + 120157027044 * s ^ 28
    - 270715182090 * s ^ 27
    + 565686734690 * s ^ 26
    - 1093735507630 * s ^ 25
    + 1947740661342 * s ^ 24
    - 3179761875400 * s ^ 23
    + 4737775747946 * s ^ 22
    - 6410613807934 * s ^ 21
    + 7821572055504 * s ^ 20
    - 8500881079947 * s ^ 19
    + 8029739744562 * s ^ 18
    - 6214075569540 * s ^ 17
    + 3228597977404 * s ^ 16
    + 342475110469 * s ^ 15
    - 3628135694738 * s ^ 14
    + 5764617153484 * s ^ 13
    - 6277131377527 * s ^ 12
    + 5325191839590 * s ^ 11
    - 3598442261865 * s ^ 10
    + 1908252122607 * s ^ 9
    - 758646456013 * s ^ 8
    + 201480147371 * s ^ 7
    - 20787311660 * s ^ 6
    - 8165847750 * s ^ 5
    + 3988440784 * s ^ 4
    - 591952380 * s ^ 3
    - 18486699 * s ^ 2
    + 7000251 * s
    + 51683

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient24 (s : ℚ) : ℚ :=
  s ^ 40
    - 41 * s ^ 39
    + 789 * s ^ 38
    - 9544 * s ^ 37
    + 81513 * s ^ 36
    - 516739 * s ^ 35
    + 2428543 * s ^ 34
    - 7711396 * s ^ 33
    + 8200413 * s ^ 32
    + 82876031 * s ^ 31
    - 693119164 * s ^ 30
    + 3294551817 * s ^ 29
    - 11751777088 * s ^ 28
    + 34058264467 * s ^ 27
    - 83375600823 * s ^ 26
    + 176637077519 * s ^ 25
    - 328873352554 * s ^ 24
    + 541707089545 * s ^ 23
    - 785931983987 * s ^ 22
    + 982451643893 * s ^ 21
    - 991745663715 * s ^ 20
    + 626049925726 * s ^ 19
    + 299362136802 * s ^ 18
    - 1866600602313 * s ^ 17
    + 3933912524588 * s ^ 16
    - 6071144317749 * s ^ 15
    + 7644191416730 * s ^ 14
    - 8079288606188 * s ^ 13
    + 7192377245060 * s ^ 12
    - 5338894620603 * s ^ 11
    + 3229762790531 * s ^ 10
    - 1527422810733 * s ^ 9
    + 518263737793 * s ^ 8
    - 94658997143 * s ^ 7
    - 12631472107 * s ^ 6
    + 14816187909 * s ^ 5
    - 4459678943 * s ^ 4
    + 458241458 * s ^ 3
    + 53807382 * s ^ 2
    - 9281212 * s
    - 106468

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient25 (s : ℚ) : ℚ :=
  -2 * s ^ 38
    + 70 * s ^ 37
    - 1143 * s ^ 36
    + 11928 * s ^ 35
    - 94259 * s ^ 34
    + 641102 * s ^ 33
    - 4009842 * s ^ 32
    + 22774517 * s ^ 31
    - 112343859 * s ^ 30
    + 466903399 * s ^ 29
    - 1620859597 * s ^ 28
    + 4730248232 * s ^ 27
    - 11806406309 * s ^ 26
    + 25928729606 * s ^ 25
    - 52198798365 * s ^ 24
    + 101115047895 * s ^ 23
    - 195866934912 * s ^ 22
    + 382778557998 * s ^ 21
    - 739389190261 * s ^ 20
    + 1367347296139 * s ^ 19
    - 2352751237207 * s ^ 18
    + 3689483783533 * s ^ 17
    - 5197559918922 * s ^ 16
    + 6504368983439 * s ^ 15
    - 7152493895427 * s ^ 14
    + 6825469177662 * s ^ 13
    - 5562115624625 * s ^ 12
    + 3781397833215 * s ^ 11
    - 2065038159339 * s ^ 10
    + 842072073891 * s ^ 9
    - 207258472766 * s ^ 8
    - 8956795614 * s ^ 7
    + 34830212648 * s ^ 6
    - 16208596452 * s ^ 5
    + 3619032322 * s ^ 4
    - 174547687 * s ^ 3
    - 85576042 * s ^ 2
    + 9979271 * s
    + 175763

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient26 (s : ℚ) : ℚ :=
  -s ^ 37
    + 47 * s ^ 36
    - 1002 * s ^ 35
    + 12972 * s ^ 34
    - 114936 * s ^ 33
    + 744550 * s ^ 32
    - 3689645 * s ^ 31
    + 14601446 * s ^ 30
    - 49035808 * s ^ 29
    + 153881138 * s ^ 28
    - 500369448 * s ^ 27
    + 1720013408 * s ^ 26
    - 5828627710 * s ^ 25
    + 18194880205 * s ^ 24
    - 50897924140 * s ^ 23
    + 127346296709 * s ^ 22
    - 286724053777 * s ^ 21
    + 583821520165 * s ^ 20
    - 1076095898621 * s ^ 19
    + 1791024825526 * s ^ 18
    - 2679251802478 * s ^ 17
    + 3579682630661 * s ^ 16
    - 4236366883855 * s ^ 15
    + 4392442108906 * s ^ 14
    - 3931347623486 * s ^ 13
    + 2972291171246 * s ^ 12
    - 1831752008526 * s ^ 11
    + 857588581925 * s ^ 10
    - 248121352936 * s ^ 9
    - 10620683440 * s ^ 8
    + 59475031178 * s ^ 7
    - 36352395702 * s ^ 6
    + 12142848218 * s ^ 5
    - 1963788193 * s ^ 4
    - 110786037 * s ^ 3
    + 96678294 * s ^ 2
    - 8553166 * s
    - 233687

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient27 (s : ℚ) : ℚ :=
  4 * s ^ 35
    - 182 * s ^ 34
    + 3899 * s ^ 33
    - 52553 * s ^ 32
    + 502636 * s ^ 31
    - 3650224 * s ^ 30
    + 21053937 * s ^ 29
    - 99765725 * s ^ 28
    + 399477168 * s ^ 27
    - 1386112722 * s ^ 26
    + 4263700302 * s ^ 25
    - 11849734370 * s ^ 24
    + 30140746621 * s ^ 23
    - 70536037234 * s ^ 22
    + 151663517190 * s ^ 21
    - 298062592095 * s ^ 20
    + 532040989961 * s ^ 19
    - 857156717100 * s ^ 18
    + 1238156768618 * s ^ 17
    - 1590778085163 * s ^ 16
    + 1798712880094 * s ^ 15
    - 1763718672802 * s ^ 14
    + 1466674923594 * s ^ 13
    - 995130368666 * s ^ 12
    + 506558411557 * s ^ 11
    - 143654649739 * s ^ 10
    - 38674491113 * s ^ 9
    + 79198212900 * s ^ 8
    - 54896414497 * s ^ 7
    + 23521092758 * s ^ 6
    - 6040779457 * s ^ 5
    + 454664976 * s ^ 4
    + 257255160 * s ^ 3
    - 81986035 * s ^ 2
    + 5658262 * s
    + 250040

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient28 (s : ℚ) : ℚ :=
  -6 * s ^ 33
    + 267 * s ^ 32
    - 5652 * s ^ 31
    + 75990 * s ^ 30
    - 731033 * s ^ 29
    + 5374923 * s ^ 28
    - 31503427 * s ^ 27
    + 151584091 * s ^ 26
    - 611939375 * s ^ 25
    + 2107863132 * s ^ 24
    - 6279410472 * s ^ 23
    + 16356641854 * s ^ 22
    - 37576035835 * s ^ 21
    + 76590939338 * s ^ 20
    - 138903863717 * s ^ 19
    + 223920845324 * s ^ 18
    - 319190669325 * s ^ 17
    + 398323862067 * s ^ 16
    - 428049480364 * s ^ 15
    + 385007660886 * s ^ 14
    - 273424722207 * s ^ 13
    + 129389851518 * s ^ 12
    - 3937580578 * s ^ 11
    - 66277130234 * s ^ 10
    + 78269683344 * s ^ 9
    - 56178333232 * s ^ 8
    + 28157403323 * s ^ 7
    - 9471885815 * s ^ 6
    + 1544336532 * s ^ 5
    + 298871654 * s ^ 4
    - 241239353 * s ^ 3
    + 52448848 * s ^ 2
    - 2698559 * s
    - 213907

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient29 (s : ℚ) : ℚ :=
  4 * s ^ 31
    - 170 * s ^ 30
    + 3444 * s ^ 29
    - 44389 * s ^ 28
    + 409853 * s ^ 27
    - 2893344 * s ^ 26
    + 16267272 * s ^ 25
    - 74855752 * s ^ 24
    + 287222179 * s ^ 23
    - 930437129 * s ^ 22
    + 2564051100 * s ^ 21
    - 6031650913 * s ^ 20
    + 12104362811 * s ^ 19
    - 20604266582 * s ^ 18
    + 29329630141 * s ^ 17
    - 33781272684 * s ^ 16
    + 28777273385 * s ^ 15
    - 11874093634 * s ^ 14
    - 13441739589 * s ^ 13
    + 37890598293 * s ^ 12
    - 51303450387 * s ^ 11
    + 49343752635 * s ^ 10
    - 36105991318 * s ^ 9
    + 20105481030 * s ^ 8
    - 8013360925 * s ^ 7
    + 1750995767 * s ^ 6
    + 251198670 * s ^ 5
    - 378306449 * s ^ 4
    + 144915120 * s ^ 3
    - 24698787 * s ^ 2
    + 755952 * s
    + 144396

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient30 (s : ℚ) : ℚ :=
  -s ^ 29
    + 37 * s ^ 28
    - 636 * s ^ 27
    + 6712 * s ^ 26
    - 48189 * s ^ 25
    + 243684 * s ^ 24
    - 840325 * s ^ 23
    + 1520904 * s ^ 22
    + 2760433 * s ^ 21
    - 35707260 * s ^ 20
    + 171347823 * s ^ 19
    - 582394465 * s ^ 18
    + 1575173973 * s ^ 17
    - 3537235105 * s ^ 16
    + 6708541279 * s ^ 15
    - 10789461640 * s ^ 14
    + 14661652008 * s ^ 13
    - 16691199431 * s ^ 12
    + 15726893813 * s ^ 11
    - 12046047037 * s ^ 10
    + 7245161419 * s ^ 9
    - 3118656379 * s ^ 8
    + 619209610 * s ^ 7
    + 337039207 * s ^ 6
    - 400383182 * s ^ 5
    + 203037345 * s ^ 4
    - 58597636 * s ^ 3
    + 8033715 * s ^ 2
    + 24555 * s
    - 75231

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient31 (s : ℚ) : ℚ :=
  2 * s ^ 26
    - 79 * s ^ 25
    + 1482 * s ^ 24
    - 17587 * s ^ 23
    + 148318 * s ^ 22
    - 946277 * s ^ 21
    + 4744610 * s ^ 20
    - 19158637 * s ^ 19
    + 63290639 * s ^ 18
    - 172670913 * s ^ 17
    + 390779378 * s ^ 16
    - 733749131 * s ^ 15
    + 1138632960 * s ^ 14
    - 1447889051 * s ^ 13
    + 1484330468 * s ^ 12
    - 1183656051 * s ^ 11
    + 659693289 * s ^ 10
    - 129287066 * s ^ 9
    - 226222845 * s ^ 8
    + 345694876 * s ^ 7
    - 286635636 * s ^ 6
    + 162552294 * s ^ 5
    - 63186624 * s ^ 4
    + 15179114 * s ^ 3
    - 1522764 * s ^ 2
    - 133956 * s
    + 29187

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient32 (s : ℚ) : ℚ :=
  -s ^ 23
    + 37 * s ^ 22
    - 645 * s ^ 21
    + 7044 * s ^ 20
    - 54031 * s ^ 19
    + 309199 * s ^ 18
    - 1368388 * s ^ 17
    + 4791759 * s ^ 16
    - 13485503 * s ^ 15
    + 30874853 * s ^ 14
    - 58205297 * s ^ 13
    + 91743192 * s ^ 12
    - 123380935 * s ^ 11
    + 144751815 * s ^ 10
    - 150129036 * s ^ 9
    + 136529140 * s ^ 8
    - 105523169 * s ^ 7
    + 66218363 * s ^ 6
    - 31857183 * s ^ 5
    + 10767067 * s ^ 4
    - 2094145 * s ^ 3
    + 51117 * s ^ 2
    + 62685 * s
    - 7938

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient33 (s : ℚ) : ℚ :=
  s ^ 19
    - 34 * s ^ 18
    + 536 * s ^ 17
    - 5199 * s ^ 16
    + 34723 * s ^ 15
    - 169339 * s ^ 14
    + 624067 * s ^ 13
    - 1774446 * s ^ 12
    + 3940444 * s ^ 11
    - 6875611 * s ^ 10
    + 9436911 * s ^ 9
    - 10148163 * s ^ 8
    + 8457090 * s ^ 7
    - 5330521 * s ^ 6
    + 2403658 * s ^ 5
    - 665074 * s ^ 4
    + 41518 * s ^ 3
    + 42237 * s ^ 2
    - 14148 * s
    + 1350

/-- Coefficient of the indicated power of the raw chart variable. -/
def termOneCoefficient34 (s : ℚ) : ℚ :=
  -s ^ 12
    + 23 * s ^ 11
    - 235 * s ^ 10
    + 1406 * s ^ 9
    - 5467 * s ^ 8
    + 14498 * s ^ 7
    - 26771 * s ^ 6
    + 34508 * s ^ 5
    - 30628 * s ^ 4
    + 18103 * s ^ 3
    - 6678 * s ^ 2
    + 1350 * s
    - 108

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
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient0,
    t1Step3Coefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_1 (s : ℚ) :
    termOneCoefficient1 s =
    t1Step3Coefficient0 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient1 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient1,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_2 (s : ℚ) :
    termOneCoefficient2 s =
    t1Step3Coefficient0 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient1 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient2 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient2,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_3 (s : ℚ) :
    termOneCoefficient3 s =
    t1Step3Coefficient0 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient1 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient2 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient3 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient3,
    t1Step3Coefficient0,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_4 (s : ℚ) :
    termOneCoefficient4 s =
    t1Step3Coefficient1 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient2 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient3 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient4 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient4,
    t1Step3Coefficient1,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_5 (s : ℚ) :
    termOneCoefficient5 s =
    t1Step3Coefficient2 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient3 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient4 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient5 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient5,
    t1Step3Coefficient2,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_6 (s : ℚ) :
    termOneCoefficient6 s =
    t1Step3Coefficient3 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient4 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient5 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient6 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient6,
    t1Step3Coefficient3,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_7 (s : ℚ) :
    termOneCoefficient7 s =
    t1Step3Coefficient4 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient5 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient6 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient7 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient7,
    t1Step3Coefficient4,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_8 (s : ℚ) :
    termOneCoefficient8 s =
    t1Step3Coefficient5 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient6 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient7 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient8 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient8,
    t1Step3Coefficient5,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_9 (s : ℚ) :
    termOneCoefficient9 s =
    t1Step3Coefficient6 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient7 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient8 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient9 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient9,
    t1Step3Coefficient6,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_10 (s : ℚ) :
    termOneCoefficient10 s =
    t1Step3Coefficient7 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient8 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient9 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient10 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient10,
    t1Step3Coefficient7,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_11 (s : ℚ) :
    termOneCoefficient11 s =
    t1Step3Coefficient8 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient9 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient10 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient11 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient11,
    t1Step3Coefficient8,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_12 (s : ℚ) :
    termOneCoefficient12 s =
    t1Step3Coefficient9 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient10 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient11 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient12 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient12,
    t1Step3Coefficient9,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_13 (s : ℚ) :
    termOneCoefficient13 s =
    t1Step3Coefficient10 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient11 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient12 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient13 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient13,
    t1Step3Coefficient10,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_14 (s : ℚ) :
    termOneCoefficient14 s =
    t1Step3Coefficient11 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient12 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient13 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient14 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient14,
    t1Step3Coefficient11,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_15 (s : ℚ) :
    termOneCoefficient15 s =
    t1Step3Coefficient12 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient13 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient14 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient15 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient15,
    t1Step3Coefficient12,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_16 (s : ℚ) :
    termOneCoefficient16 s =
    t1Step3Coefficient13 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient14 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient15 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient16 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient16,
    t1Step3Coefficient13,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_17 (s : ℚ) :
    termOneCoefficient17 s =
    t1Step3Coefficient14 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient15 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient16 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient17 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient17,
    t1Step3Coefficient14,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_18 (s : ℚ) :
    termOneCoefficient18 s =
    t1Step3Coefficient15 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient16 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient17 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient18 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient18,
    t1Step3Coefficient15,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_19 (s : ℚ) :
    termOneCoefficient19 s =
    t1Step3Coefficient16 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient17 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient18 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient19 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient19,
    t1Step3Coefficient16,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_20 (s : ℚ) :
    termOneCoefficient20 s =
    t1Step3Coefficient17 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient18 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient19 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient20 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient20,
    t1Step3Coefficient17,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_21 (s : ℚ) :
    termOneCoefficient21 s =
    t1Step3Coefficient18 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient19 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient20 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient21 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient21,
    t1Step3Coefficient18,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_22 (s : ℚ) :
    termOneCoefficient22 s =
    t1Step3Coefficient19 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient20 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient21 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient22 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient22,
    t1Step3Coefficient19,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_23 (s : ℚ) :
    termOneCoefficient23 s =
    t1Step3Coefficient20 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient21 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient22 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient23 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient23,
    t1Step3Coefficient20,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    t1Step3Coefficient23,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_24 (s : ℚ) :
    termOneCoefficient24 s =
    t1Step3Coefficient21 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient22 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient23 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient24 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient24,
    t1Step3Coefficient21,
    t1Step3Coefficient22,
    t1Step3Coefficient23,
    t1Step3Coefficient24,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_25 (s : ℚ) :
    termOneCoefficient25 s =
    t1Step3Coefficient22 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient23 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient24 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient25 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient25,
    t1Step3Coefficient22,
    t1Step3Coefficient23,
    t1Step3Coefficient24,
    t1Step3Coefficient25,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_26 (s : ℚ) :
    termOneCoefficient26 s =
    t1Step3Coefficient23 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient24 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient25 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient26 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient26,
    t1Step3Coefficient23,
    t1Step3Coefficient24,
    t1Step3Coefficient25,
    t1Step3Coefficient26,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_27 (s : ℚ) :
    termOneCoefficient27 s =
    t1Step3Coefficient24 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient25 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient26 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient27 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient27,
    t1Step3Coefficient24,
    t1Step3Coefficient25,
    t1Step3Coefficient26,
    t1Step3Coefficient27,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_28 (s : ℚ) :
    termOneCoefficient28 s =
    t1Step3Coefficient25 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient26 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient27 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient28 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient28,
    t1Step3Coefficient25,
    t1Step3Coefficient26,
    t1Step3Coefficient27,
    t1Step3Coefficient28,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_29 (s : ℚ) :
    termOneCoefficient29 s =
    t1Step3Coefficient26 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient27 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient28 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient29 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient29,
    t1Step3Coefficient26,
    t1Step3Coefficient27,
    t1Step3Coefficient28,
    t1Step3Coefficient29,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_30 (s : ℚ) :
    termOneCoefficient30 s =
    t1Step3Coefficient27 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient28 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient29 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient30 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient30,
    t1Step3Coefficient27,
    t1Step3Coefficient28,
    t1Step3Coefficient29,
    t1Step3Coefficient30,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_31 (s : ℚ) :
    termOneCoefficient31 s =
    t1Step3Coefficient28 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient29 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient30 s *
        rawUnitEightDenominatorCoefficient1 s
      + t1Step3Coefficient31 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termOneCoefficient31,
    t1Step3Coefficient28,
    t1Step3Coefficient29,
    t1Step3Coefficient30,
    t1Step3Coefficient31,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_32 (s : ℚ) :
    termOneCoefficient32 s =
    t1Step3Coefficient29 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient30 s *
        rawUnitEightDenominatorCoefficient2 s
      + t1Step3Coefficient31 s *
        rawUnitEightDenominatorCoefficient1 s
    := by
  simp only [termOneCoefficient32,
    t1Step3Coefficient29,
    t1Step3Coefficient30,
    t1Step3Coefficient31,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_33 (s : ℚ) :
    termOneCoefficient33 s =
    t1Step3Coefficient30 s *
        rawUnitEightDenominatorCoefficient3 s
      + t1Step3Coefficient31 s *
        rawUnitEightDenominatorCoefficient2 s
    := by
  simp only [termOneCoefficient33,
    t1Step3Coefficient30,
    t1Step3Coefficient31,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termOneCoefficient_product_certificate_34 (s : ℚ) :
    termOneCoefficient34 s =
    t1Step3Coefficient31 s *
        rawUnitEightDenominatorCoefficient3 s
    := by
  simp only [termOneCoefficient34,
    t1Step3Coefficient31,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termOne_eq_t1Step3_mul_rawUnitEightDenominator (r s : ℚ) :
    termOne r s = t1Step3 r s * rawUnitEightDenominator r s := by
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
  simp only [termOne, t1Step3, rawUnitEightDenominator]
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
  s ^ 15
    - 3 * s ^ 14
    + 4 * s ^ 13
    - 4 * s ^ 12
    + 4 * s ^ 11
    - 4 * s ^ 10
    + 3 * s ^ 9
    - s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient2 (s : ℚ) : ℚ :=
  -2 * s ^ 17
    + 13 * s ^ 16
    - 36 * s ^ 15
    + 41 * s ^ 14
    - 14 * s ^ 13
    - s ^ 12
    - 10 * s ^ 11
    + 12 * s ^ 10
    + 20 * s ^ 9
    - 53 * s ^ 8
    + 44 * s ^ 7
    - 19 * s ^ 6
    + 6 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient3 (s : ℚ) : ℚ :=
  s ^ 19
    - 11 * s ^ 18
    + 48 * s ^ 17
    - 81 * s ^ 16
    - 58 * s ^ 15
    + 489 * s ^ 14
    - 826 * s ^ 13
    + 699 * s ^ 12
    - 561 * s ^ 11
    + 939 * s ^ 10
    - 1573 * s ^ 9
    + 1680 * s ^ 8
    - 1091 * s ^ 7
    + 466 * s ^ 6
    - 144 * s ^ 5
    + 23 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient4 (s : ℚ) : ℚ :=
  s ^ 20
    - 6 * s ^ 19
    - 17 * s ^ 18
    + 308 * s ^ 17
    - 1455 * s ^ 16
    + 3642 * s ^ 15
    - 5277 * s ^ 14
    + 4504 * s ^ 13
    - 4098 * s ^ 12
    + 9236 * s ^ 11
    - 18630 * s ^ 10
    + 24446 * s ^ 9
    - 21192 * s ^ 8
    + 12386 * s ^ 7
    - 5152 * s ^ 6
    + 1534 * s ^ 5
    - 228 * s ^ 4
    - 2 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 21
    + 20 * s ^ 20
    - 183 * s ^ 19
    + 958 * s ^ 18
    - 3082 * s ^ 17
    + 5973 * s ^ 16
    - 5919 * s ^ 15
    + 1650 * s ^ 14
    - 7835 * s ^ 13
    + 50661 * s ^ 12
    - 129128 * s ^ 11
    + 196910 * s ^ 10
    - 204969 * s ^ 9
    + 151587 * s ^ 8
    - 81142 * s ^ 7
    + 32380 * s ^ 6
    - 9094 * s ^ 5
    + 1162 * s ^ 4
    + 53 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 22
    + 16 * s ^ 21
    - 114 * s ^ 20
    + 428 * s ^ 19
    - 621 * s ^ 18
    - 1562 * s ^ 17
    + 8664 * s ^ 16
    - 7908 * s ^ 15
    - 54942 * s ^ 14
    + 261374 * s ^ 13
    - 620984 * s ^ 12
    + 983392 * s ^ 11
    - 1129177 * s ^ 10
    + 971622 * s ^ 9
    - 632043 * s ^ 8
    + 313540 * s ^ 7
    - 118980 * s ^ 6
    + 30280 * s ^ 5
    - 2433 * s ^ 4
    - 566 * s ^ 3
    + 15 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient7 (s : ℚ) : ℚ :=
  -s ^ 22
    + 23 * s ^ 21
    - 223 * s ^ 20
    + 1168 * s ^ 19
    - 2923 * s ^ 18
    - 3570 * s ^ 17
    + 63568 * s ^ 16
    - 293392 * s ^ 15
    + 853024 * s ^ 14
    - 1782177 * s ^ 13
    + 2807913 * s ^ 12
    - 3418707 * s ^ 11
    + 3262060 * s ^ 10
    - 2451599 * s ^ 9
    + 1451472 * s ^ 8
    - 679387 * s ^ 7
    + 241825 * s ^ 6
    - 48334 * s ^ 5
    - 3713 * s ^ 4
    + 3037 * s ^ 3
    - 62 * s ^ 2
    - 2 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient8 (s : ℚ) : ℚ :=
  -2 * s ^ 22
    + 56 * s ^ 21
    - 733 * s ^ 20
    + 5978 * s ^ 19
    - 34095 * s ^ 18
    + 144224 * s ^ 17
    - 467735 * s ^ 16
    + 1186154 * s ^ 15
    - 2380901 * s ^ 14
    + 3813912 * s ^ 13
    - 4908181 * s ^ 12
    + 5106310 * s ^ 11
    - 4316687 * s ^ 10
    + 2972460 * s ^ 9
    - 1671671 * s ^ 8
    + 756494 * s ^ 7
    - 230603 * s ^ 6
    + 1292 * s ^ 5
    + 32408 * s ^ 4
    - 8632 * s ^ 3
    - 72 * s ^ 2
    + 24 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient9 (s : ℚ) : ℚ :=
  -s ^ 23
    + 25 * s ^ 22
    - 304 * s ^ 21
    + 2373 * s ^ 20
    - 13249 * s ^ 19
    + 55878 * s ^ 18
    - 183503 * s ^ 17
    + 477584 * s ^ 16
    - 995823 * s ^ 15
    + 1677186 * s ^ 14
    - 2302487 * s ^ 13
    + 2610876 * s ^ 12
    - 2491197 * s ^ 11
    + 2040806 * s ^ 10
    - 1453319 * s ^ 9
    + 880238 * s ^ 8
    - 377927 * s ^ 7
    + 6912 * s ^ 6
    + 129001 * s ^ 5
    - 76613 * s ^ 4
    + 12436 * s ^ 3
    + 1212 * s ^ 2
    - 103 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient10 (s : ℚ) : ℚ :=
  5 * s ^ 20
    - 98 * s ^ 19
    + 907 * s ^ 18
    - 5168 * s ^ 17
    + 19888 * s ^ 16
    - 53268 * s ^ 15
    + 97078 * s ^ 14
    - 103648 * s ^ 13
    + 2088 * s ^ 12
    + 222052 * s ^ 11
    - 462135 * s ^ 10
    + 545064 * s ^ 9
    - 369042 * s ^ 8
    + 16160 * s ^ 7
    + 250814 * s ^ 6
    - 244144 * s ^ 5
    + 91911 * s ^ 4
    - 4868 * s ^ 3
    - 3802 * s ^ 2
    + 198 * s
    + 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient11 (s : ℚ) : ℚ :=
  s ^ 20
    - 24 * s ^ 19
    + 273 * s ^ 18
    - 1955 * s ^ 17
    + 9827 * s ^ 16
    - 36618 * s ^ 15
    + 104304 * s ^ 14
    - 231101 * s ^ 13
    + 401505 * s ^ 12
    - 544818 * s ^ 11
    + 557643 * s ^ 10
    - 369305 * s ^ 9
    + 17409 * s ^ 8
    + 313381 * s ^ 7
    - 399863 * s ^ 6
    + 234673 * s ^ 5
    - 48400 * s ^ 4
    - 12728 * s ^ 3
    + 5940 * s ^ 2
    - 117 * s
    - 27

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient12 (s : ℚ) : ℚ :=
  -2 * s ^ 17
    + 35 * s ^ 16
    - 288 * s ^ 15
    + 1523 * s ^ 14
    - 5986 * s ^ 13
    + 19222 * s ^ 12
    - 53206 * s ^ 11
    + 126654 * s ^ 10
    - 247376 * s ^ 9
    + 371804 * s ^ 8
    - 398724 * s ^ 7
    + 271200 * s ^ 6
    - 83384 * s ^ 5
    - 19587 * s ^ 4
    + 23090 * s ^ 3
    - 4805 * s ^ 2
    - 220 * s
    + 50

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient13 (s : ℚ) : ℚ :=
  -s ^ 16
    + 23 * s ^ 15
    - 242 * s ^ 14
    + 1562 * s ^ 13
    - 6940 * s ^ 12
    + 22345 * s ^ 11
    - 52995 * s ^ 10
    + 91509 * s ^ 9
    - 109337 * s ^ 8
    + 77108 * s ^ 7
    - 8224 * s ^ 6
    - 40862 * s ^ 5
    + 38973 * s ^ 4
    - 14457 * s ^ 3
    + 1088 * s ^ 2
    + 504 * s
    - 54

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient14 (s : ℚ) : ℚ :=
  2 * s ^ 13
    - 40 * s ^ 12
    + 358 * s ^ 11
    - 1905 * s ^ 10
    + 6720 * s ^ 9
    - 16463 * s ^ 8
    + 28300 * s ^ 7
    - 33475 * s ^ 6
    + 25720 * s ^ 5
    - 11035 * s ^ 4
    + 1104 * s ^ 3
    + 1086 * s ^ 2
    - 404 * s
    + 32

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step1Coefficient15 (s : ℚ) : ℚ :=
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
    t2Step1Coefficient15 s * r ^ 15

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_0 (s : ℚ) :
    t2Step1Coefficient0 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient0,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_1 (s : ℚ) :
    t2Step1Coefficient1 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient1,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_2 (s : ℚ) :
    t2Step1Coefficient2 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient2,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_3 (s : ℚ) :
    t2Step1Coefficient3 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient3,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_4 (s : ℚ) :
    t2Step1Coefficient4 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient4,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_5 (s : ℚ) :
    t2Step1Coefficient5 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient5,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_6 (s : ℚ) :
    t2Step1Coefficient6 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient6,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_7 (s : ℚ) :
    t2Step1Coefficient7 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step1Coefficient7,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
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
theorem t2Step1Coefficient_product_certificate_8 (s : ℚ) :
    t2Step1Coefficient8 s =
    rawUnitTwoNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient1 s
    := by
  simp only [t2Step1Coefficient8,
    rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
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
theorem t2Step1Coefficient_product_certificate_9 (s : ℚ) :
    t2Step1Coefficient9 s =
    rawUnitTwoNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient2 s
    := by
  simp only [t2Step1Coefficient9,
    rawUnitTwoNumeratorCoefficient1,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_10 (s : ℚ) :
    t2Step1Coefficient10 s =
    rawUnitTwoNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient3 s
    := by
  simp only [t2Step1Coefficient10,
    rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_11 (s : ℚ) :
    t2Step1Coefficient11 s =
    rawUnitTwoNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient4 s
    := by
  simp only [t2Step1Coefficient11,
    rawUnitTwoNumeratorCoefficient3,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_12 (s : ℚ) :
    t2Step1Coefficient12 s =
    rawUnitTwoNumeratorCoefficient4 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient5 s
    := by
  simp only [t2Step1Coefficient12,
    rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_13 (s : ℚ) :
    t2Step1Coefficient13 s =
    rawUnitTwoNumeratorCoefficient5 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient6 s
    := by
  simp only [t2Step1Coefficient13,
    rawUnitTwoNumeratorCoefficient5,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_14 (s : ℚ) :
    t2Step1Coefficient14 s =
    rawUnitTwoNumeratorCoefficient6 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient7 s
    := by
  simp only [t2Step1Coefficient14,
    rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step1Coefficient_product_certificate_15 (s : ℚ) :
    t2Step1Coefficient15 s =
    rawUnitTwoNumeratorCoefficient7 s *
        rawUnitFourDenominatorCoefficient8 s
    := by
  simp only [t2Step1Coefficient15,
    rawUnitTwoNumeratorCoefficient7,
    rawUnitFourDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step1_eq_rawUnitTwoNumerator_mul_rawUnitFourDenominator (r s : ℚ) :
    t2Step1 r s = rawUnitTwoNumerator r s * rawUnitFourDenominator r s := by
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
  simp only [t2Step1, rawUnitTwoNumerator, rawUnitFourDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient1 (s : ℚ) : ℚ :=
  s ^ 21
    - 3 * s ^ 20
    + 4 * s ^ 19
    - 4 * s ^ 18
    + 4 * s ^ 17
    - 4 * s ^ 16
    + 3 * s ^ 15
    - s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient2 (s : ℚ) : ℚ :=
  -4 * s ^ 23
    + 25 * s ^ 22
    - 68 * s ^ 21
    + 81 * s ^ 20
    - 34 * s ^ 19
    - 6 * s ^ 18
    + 10 * s ^ 17
    - 23 * s ^ 16
    + 76 * s ^ 15
    - 117 * s ^ 14
    + 88 * s ^ 13
    - 38 * s ^ 12
    + 12 * s ^ 11
    - 2 * s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient3 (s : ℚ) : ℚ :=
  6 * s ^ 25
    - 58 * s ^ 24
    + 244 * s ^ 23
    - 487 * s ^ 22
    + 234 * s ^ 21
    + 1005 * s ^ 20
    - 2266 * s ^ 19
    + 2356 * s ^ 18
    - 2125 * s ^ 17
    + 2772 * s ^ 16
    - 3698 * s ^ 15
    + 3265 * s ^ 14
    - 1471 * s ^ 13
    + 57 * s ^ 12
    + 372 * s ^ 11
    - 318 * s ^ 10
    + 147 * s ^ 9
    - 43 * s ^ 8
    + 9 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient4 (s : ℚ) : ℚ :=
  -4 * s ^ 27
    + 54 * s ^ 26
    - 308 * s ^ 25
    + 822 * s ^ 24
    - 248 * s ^ 23
    - 5426 * s ^ 22
    + 18480 * s ^ 21
    - 30563 * s ^ 20
    + 28416 * s ^ 19
    - 18638 * s ^ 18
    + 22388 * s ^ 17
    - 37667 * s ^ 16
    + 38708 * s ^ 15
    - 13052 * s ^ 14
    - 18242 * s ^ 13
    + 30046 * s ^ 12
    - 24212 * s ^ 11
    + 13643 * s ^ 10
    - 5486 * s ^ 9
    + 1578 * s ^ 8
    - 324 * s ^ 7
    + 35 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient5 (s : ℚ) : ℚ :=
  s ^ 29
    - 19 * s ^ 28
    + 134 * s ^ 27
    - 328 * s ^ 26
    - 1250 * s ^ 25
    + 12964 * s ^ 24
    - 49896 * s ^ 23
    + 109850 * s ^ 22
    - 136079 * s ^ 21
    + 56152 * s ^ 20
    + 78185 * s ^ 19
    - 83545 * s ^ 18
    - 68715 * s ^ 17
    + 116784 * s ^ 16
    + 153236 * s ^ 15
    - 590288 * s ^ 14
    + 835931 * s ^ 13
    - 748471 * s ^ 12
    + 489847 * s ^ 11
    - 246294 * s ^ 10
    + 93383 * s ^ 9
    - 26291 * s ^ 8
    + 5247 * s ^ 7
    - 534 * s ^ 6
    - 4 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient6 (s : ℚ) : ℚ :=
  s ^ 30
    - 4 * s ^ 29
    - 137 * s ^ 28
    + 2006 * s ^ 27
    - 13526 * s ^ 26
    + 54970 * s ^ 25
    - 138667 * s ^ 24
    + 180564 * s ^ 23
    + 80293 * s ^ 22
    - 862548 * s ^ 21
    + 1784472 * s ^ 20
    - 1889124 * s ^ 19
    + 1054716 * s ^ 18
    - 1096868 * s ^ 17
    + 3971468 * s ^ 16
    - 8882980 * s ^ 15
    + 12555018 * s ^ 14
    - 12531908 * s ^ 13
    + 9429366 * s ^ 12
    - 5580700 * s ^ 11
    + 2618355 * s ^ 10
    - 949534 * s ^ 9
    + 259751 * s ^ 8
    - 49568 * s ^ 7
    + 4443 * s ^ 6
    + 142 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient7 (s : ℚ) : ℚ :=
  -2 * s ^ 31
    + 55 * s ^ 30
    - 668 * s ^ 29
    + 4661 * s ^ 28
    - 19710 * s ^ 27
    + 42928 * s ^ 26
    + 31535 * s ^ 25
    - 608304 * s ^ 24
    + 2399746 * s ^ 23
    - 5594945 * s ^ 22
    + 8456415 * s ^ 21
    - 8159759 * s ^ 20
    + 6209043 * s ^ 19
    - 12749263 * s ^ 18
    + 39101614 * s ^ 17
    - 81853790 * s ^ 16
    + 119517519 * s ^ 15
    - 130063401 * s ^ 14
    + 110015209 * s ^ 13
    - 74447367 * s ^ 12
    + 40964747 * s ^ 11
    - 18171064 * s ^ 10
    + 6311177 * s ^ 9
    - 1658020 * s ^ 8
    + 292900 * s ^ 7
    - 19037 * s ^ 6
    - 2241 * s ^ 5
    + 22 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient8 (s : ℚ) : ℚ :=
  -2 * s ^ 32
    + 36 * s ^ 31
    - 226 * s ^ 30
    - 300 * s ^ 29
    + 15733 * s ^ 28
    - 135924 * s ^ 27
    + 699340 * s ^ 26
    - 2478164 * s ^ 25
    + 6252289 * s ^ 24
    - 11018000 * s ^ 23
    + 12611920 * s ^ 22
    - 9326834 * s ^ 21
    + 18113610 * s ^ 20
    - 84671976 * s ^ 19
    + 255907339 * s ^ 18
    - 518842420 * s ^ 17
    + 773492192 * s ^ 16
    - 893883656 * s ^ 15
    + 826315950 * s ^ 14
    - 623676058 * s ^ 13
    + 389676650 * s ^ 12
    - 201875480 * s ^ 11
    + 85046283 * s ^ 10
    - 28145556 * s ^ 9
    + 6946351 * s ^ 8
    - 1049540 * s ^ 7
    + 6338 * s ^ 6
    + 20228 * s ^ 5
    - 119 * s ^ 4
    - 4 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient9 (s : ℚ) : ℚ :=
  s ^ 33
    - 37 * s ^ 32
    + 627 * s ^ 31
    - 6479 * s ^ 30
    + 45672 * s ^ 29
    - 231017 * s ^ 28
    + 850434 * s ^ 27
    - 2224770 * s ^ 26
    + 3733331 * s ^ 25
    - 2469522 * s ^ 24
    - 2988879 * s ^ 23
    - 7636763 * s ^ 22
    + 113548071 * s ^ 21
    - 466381867 * s ^ 20
    + 1209651745 * s ^ 19
    - 2306265568 * s ^ 18
    + 3432448397 * s ^ 17
    - 4117013539 * s ^ 16
    + 4061319994 * s ^ 15
    - 3342851328 * s ^ 14
    + 2319459424 * s ^ 13
    - 1361963390 * s ^ 12
    + 669845225 * s ^ 11
    - 267778060 * s ^ 10
    + 83142311 * s ^ 9
    - 18261028 * s ^ 8
    + 1730544 * s ^ 7
    + 409766 * s ^ 6
    - 112309 * s ^ 5
    - 1078 * s ^ 4
    + 92 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient10 (s : ℚ) : ℚ :=
  s ^ 34
    - 28 * s ^ 33
    + 371 * s ^ 32
    - 2990 * s ^ 31
    + 15499 * s ^ 30
    - 46978 * s ^ 29
    + 21598 * s ^ 28
    + 549662 * s ^ 27
    - 2805157 * s ^ 26
    + 5355262 * s ^ 25
    + 12613185 * s ^ 24
    - 135919396 * s ^ 23
    + 576388755 * s ^ 22
    - 1680424112 * s ^ 21
    + 3763104138 * s ^ 20
    - 6762607724 * s ^ 19
    + 9979678276 * s ^ 18
    - 12275679474 * s ^ 17
    + 12733762868 * s ^ 16
    - 11251443358 * s ^ 15
    + 8538037097 * s ^ 14
    - 5586335470 * s ^ 13
    + 3132112074 * s ^ 12
    - 1468627210 * s ^ 11
    + 550305852 * s ^ 10
    - 152842512 * s ^ 9
    + 24326208 * s ^ 8
    + 2565608 * s ^ 7
    - 2500869 * s ^ 6
    + 380412 * s ^ 5
    + 19246 * s ^ 4
    - 828 * s ^ 3
    - 6 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient11 (s : ℚ) : ℚ :=
  s ^ 34
    - 36 * s ^ 33
    + 593 * s ^ 32
    - 5904 * s ^ 31
    + 38455 * s ^ 30
    - 155783 * s ^ 29
    + 201873 * s ^ 28
    + 2304119 * s ^ 27
    - 21745440 * s ^ 26
    + 113652009 * s ^ 25
    - 435629474 * s ^ 24
    + 1321815816 * s ^ 23
    - 3281139409 * s ^ 22
    + 6780418305 * s ^ 21
    - 11790553655 * s ^ 20
    + 17389331522 * s ^ 19
    - 21909309842 * s ^ 18
    + 23766303716 * s ^ 17
    - 22390715368 * s ^ 16
    + 18474789283 * s ^ 15
    - 13410340618 * s ^ 14
    + 8516530037 * s ^ 13
    - 4623622799 * s ^ 12
    + 2046963432 * s ^ 11
    - 681495772 * s ^ 10
    + 136912999 * s ^ 9
    + 10625889 * s ^ 8
    - 22216525 * s ^ 7
    + 7838832 * s ^ 6
    - 673225 * s ^ 5
    - 126529 * s ^ 4
    + 3379 * s ^ 3
    + 119 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient12 (s : ℚ) : ℚ :=
  2 * s ^ 34
    - 84 * s ^ 33
    + 1687 * s ^ 32
    - 21672 * s ^ 31
    + 200508 * s ^ 30
    - 1423644 * s ^ 29
    + 8062370 * s ^ 28
    - 37342088 * s ^ 27
    + 143858662 * s ^ 26
    - 466326592 * s ^ 25
    + 1282088553 * s ^ 24
    - 3006363028 * s ^ 23
    + 6037834822 * s ^ 22
    - 10425459082 * s ^ 21
    + 15548224810 * s ^ 20
    - 20162227404 * s ^ 19
    + 22957397787 * s ^ 18
    - 23243336578 * s ^ 17
    + 21177938392 * s ^ 16
    - 17443050204 * s ^ 15
    + 12844372549 * s ^ 14
    - 8191084576 * s ^ 13
    + 4276245796 * s ^ 12
    - 1657785784 * s ^ 11
    + 359867852 * s ^ 10
    + 66694882 * s ^ 9
    - 115158124 * s ^ 8
    + 60856424 * s ^ 7
    - 14442171 * s ^ 6
    - 95314 * s ^ 5
    + 474836 * s ^ 4
    - 2612 * s ^ 3
    - 971 * s ^ 2
    - 4 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient13 (s : ℚ) : ℚ :=
  s ^ 35
    - 37 * s ^ 34
    + 675 * s ^ 33
    - 8056 * s ^ 32
    + 70432 * s ^ 31
    - 478864 * s ^ 30
    + 2624208 * s ^ 29
    - 11859410 * s ^ 28
    + 44869251 * s ^ 27
    - 143553539 * s ^ 26
    + 391028247 * s ^ 25
    - 911386946 * s ^ 24
    + 1826360086 * s ^ 23
    - 3168357540 * s ^ 22
    + 4816200571 * s ^ 21
    - 6550427563 * s ^ 20
    + 8211480521 * s ^ 19
    - 9756824316 * s ^ 18
    + 11056350177 * s ^ 17
    - 11645253495 * s ^ 16
    + 10883926025 * s ^ 15
    - 8557487806 * s ^ 14
    + 5304512160 * s ^ 13
    - 2301689948 * s ^ 12
    + 417418198 * s ^ 11
    + 314503730 * s ^ 10
    - 392813503 * s ^ 9
    + 251735209 * s ^ 8
    - 96901553 * s ^ 7
    + 13313156 * s ^ 6
    + 3784879 * s ^ 5
    - 1103329 * s ^ 4
    - 35903 * s ^ 3
    + 4218 * s ^ 2
    + 64 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient14 (s : ℚ) : ℚ :=
  -10 * s ^ 32
    + 320 * s ^ 31
    - 4986 * s ^ 30
    + 50036 * s ^ 29
    - 360810 * s ^ 28
    + 1975116 * s ^ 27
    - 8445726 * s ^ 26
    + 28518364 * s ^ 25
    - 75471008 * s ^ 24
    + 150297716 * s ^ 23
    - 193567564 * s ^ 22
    + 19800560 * s ^ 21
    + 684471284 * s ^ 20
    - 2185201044 * s ^ 19
    + 4363503533 * s ^ 18
    - 6497906550 * s ^ 17
    + 7527314421 * s ^ 16
    - 6767636276 * s ^ 15
    + 4503569921 * s ^ 14
    - 1849853690 * s ^ 13
    - 67101129 * s ^ 12
    + 864289688 * s ^ 11
    - 892555778 * s ^ 10
    + 631354680 * s ^ 9
    - 324189464 * s ^ 8
    + 90707968 * s ^ 7
    + 5203841 * s ^ 6
    - 10454642 * s ^ 5
    + 1516965 * s ^ 4
    + 184940 * s ^ 3
    - 10241 * s ^ 2
    - 434 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient15 (s : ℚ) : ℚ :=
  -2 * s ^ 32
    + 73 * s ^ 31
    - 1299 * s ^ 30
    + 15013 * s ^ 29
    - 126411 * s ^ 28
    + 823763 * s ^ 27
    - 4306129 * s ^ 26
    + 18467592 * s ^ 25
    - 65916812 * s ^ 24
    + 197552775 * s ^ 23
    - 499510495 * s ^ 22
    + 1067042709 * s ^ 21
    - 1921922233 * s ^ 20
    + 2900787765 * s ^ 19
    - 3621063304 * s ^ 18
    + 3636640821 * s ^ 17
    - 2745381174 * s ^ 16
    + 1212198038 * s ^ 15
    + 332876599 * s ^ 14
    - 1302163707 * s ^ 13
    + 1539441136 * s ^ 12
    - 1321854806 * s ^ 11
    + 978879124 * s ^ 10
    - 615775286 * s ^ 9
    + 259438242 * s ^ 8
    - 24091528 * s ^ 7
    - 36459847 * s ^ 6
    + 15605511 * s ^ 5
    - 736144 * s ^ 4
    - 472730 * s ^ 3
    + 11065 * s ^ 2
    + 1669 * s
    + 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient16 (s : ℚ) : ℚ :=
  14 * s ^ 29
    - 444 * s ^ 28
    + 6808 * s ^ 27
    - 67093 * s ^ 26
    + 476112 * s ^ 25
    - 2583012 * s ^ 24
    + 11104888 * s ^ 23
    - 38714680 * s ^ 22
    + 111145602 * s ^ 21
    - 265553328 * s ^ 20
    + 531974816 * s ^ 19
    - 898350251 * s ^ 18
    + 1283622372 * s ^ 17
    - 1555099231 * s ^ 16
    + 1599402844 * s ^ 15
    - 1407856650 * s ^ 14
    + 1107137592 * s ^ 13
    - 874637099 * s ^ 12
    + 766366836 * s ^ 11
    - 648331898 * s ^ 10
    + 390700316 * s ^ 9
    - 88579002 * s ^ 8
    - 65492556 * s ^ 7
    + 56965684 * s ^ 6
    - 12849860 * s ^ 5
    - 1536171 * s ^ 4
    + 740668 * s ^ 3
    + 10824 * s ^ 2
    - 4036 * s
    - 65

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient17 (s : ℚ) : ℚ :=
  s ^ 29
    - 35 * s ^ 28
    + 589 * s ^ 27
    - 6372 * s ^ 26
    + 49809 * s ^ 25
    - 299107 * s ^ 24
    + 1430674 * s ^ 23
    - 5575518 * s ^ 22
    + 17962860 * s ^ 21
    - 48292016 * s ^ 20
    + 108972387 * s ^ 19
    - 207001520 * s ^ 18
    + 330679533 * s ^ 17
    - 439822488 * s ^ 16
    + 470383464 * s ^ 15
    - 359574990 * s ^ 14
    + 93482325 * s ^ 13
    + 238224168 * s ^ 12
    - 448518662 * s ^ 11
    + 392340244 * s ^ 10
    - 139239927 * s ^ 9
    - 73911661 * s ^ 8
    + 109780013 * s ^ 7
    - 46177623 * s ^ 6
    + 2066539 * s ^ 5
    + 3795710 * s ^ 4
    - 693310 * s ^ 3
    - 61558 * s ^ 2
    + 6261 * s
    + 210

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient18 (s : ℚ) : ℚ :=
  -4 * s ^ 26
    + 118 * s ^ 25
    - 1658 * s ^ 24
    + 14838 * s ^ 23
    - 95269 * s ^ 22
    + 468634 * s ^ 21
    - 1845266 * s ^ 20
    + 6022158 * s ^ 19
    - 16806416 * s ^ 18
    + 41202652 * s ^ 17
    - 90156934 * s ^ 16
    + 175470880 * s ^ 15
    - 296279657 * s ^ 14
    + 415797468 * s ^ 13
    - 455539178 * s ^ 12
    + 347369396 * s ^ 11
    - 122261757 * s ^ 10
    - 79594696 * s ^ 9
    + 138997823 * s ^ 8
    - 80317750 * s ^ 7
    + 13245816 * s ^ 6
    + 7864858 * s ^ 5
    - 3914079 * s ^ 4
    + 253608 * s ^ 3
    + 110579 * s ^ 2
    - 5716 * s
    - 448

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient19 (s : ℚ) : ℚ :=
  -s ^ 25
    + 35 * s ^ 24
    - 576 * s ^ 23
    + 5987 * s ^ 22
    - 44391 * s ^ 21
    + 250457 * s ^ 20
    - 1115730 * s ^ 19
    + 4004666 * s ^ 18
    - 11675731 * s ^ 17
    + 27569505 * s ^ 16
    - 51846005 * s ^ 15
    + 74449556 * s ^ 14
    - 72713369 * s ^ 13
    + 25586727 * s ^ 12
    + 57898459 * s ^ 11
    - 128244144 * s ^ 10
    + 134079792 * s ^ 9
    - 78205859 * s ^ 8
    + 15495908 * s ^ 7
    + 11393276 * s ^ 6
    - 8854393 * s ^ 5
    + 1847672 * s ^ 4
    + 227313 * s ^ 3
    - 111346 * s ^ 2
    + 1536 * s
    + 656

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient20 (s : ℚ) : ℚ :=
  4 * s ^ 22
    - 128 * s ^ 21
    + 1924 * s ^ 20
    - 18144 * s ^ 19
    + 120716 * s ^ 18
    - 602558 * s ^ 17
    + 2336542 * s ^ 16
    - 7173960 * s ^ 15
    + 17574949 * s ^ 14
    - 34269466 * s ^ 13
    + 52424980 * s ^ 12
    - 60828336 * s ^ 11
    + 49428149 * s ^ 10
    - 21354204 * s ^ 9
    - 5796643 * s ^ 8
    + 16220048 * s ^ 7
    - 11216538 * s ^ 6
    + 3272532 * s ^ 5
    + 170329 * s ^ 4
    - 353512 * s ^ 3
    + 60856 * s ^ 2
    + 3120 * s
    - 660

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient21 (s : ℚ) : ℚ :=
  -6 * s ^ 19
    + 174 * s ^ 18
    - 2345 * s ^ 17
    + 19565 * s ^ 16
    - 113389 * s ^ 15
    + 484448 * s ^ 14
    - 1576638 * s ^ 13
    + 3973646 * s ^ 12
    - 7789668 * s ^ 11
    + 11794441 * s ^ 10
    - 13505465 * s ^ 9
    + 11181626 * s ^ 8
    - 6025380 * s ^ 7
    + 1393730 * s ^ 6
    + 589523 * s ^ 5
    - 582474 * s ^ 4
    + 170664 * s ^ 3
    - 8512 * s ^ 2
    - 4380 * s
    + 440

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient22 (s : ℚ) : ℚ :=
  4 * s ^ 16
    - 104 * s ^ 15
    + 1236 * s ^ 14
    - 8918 * s ^ 13
    + 43710 * s ^ 12
    - 154018 * s ^ 11
    + 401831 * s ^ 10
    - 785812 * s ^ 9
    + 1150402 * s ^ 8
    - 1242600 * s ^ 7
    + 959285 * s ^ 6
    - 496436 * s ^ 5
    + 146760 * s ^ 4
    - 8976 * s ^ 3
    - 8668 * s ^ 2
    + 2480 * s
    - 176

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step2Coefficient23 (s : ℚ) : ℚ :=
  -s ^ 13
    + 23 * s ^ 12
    - 236 * s ^ 11
    + 1427 * s ^ 10
    - 5658 * s ^ 9
    + 15488 * s ^ 8
    - 30009 * s ^ 7
    + 41498 * s ^ 6
    - 40744 * s ^ 5
    + 27856 * s ^ 4
    - 12756 * s ^ 3
    + 3640 * s ^ 2
    - 560 * s
    + 32

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
    t2Step2Coefficient23 s * r ^ 23

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_0 (s : ℚ) :
    t2Step2Coefficient0 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient0,
    t2Step1Coefficient0,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_1 (s : ℚ) :
    t2Step2Coefficient1 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient1,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_2 (s : ℚ) :
    t2Step2Coefficient2 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient2,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_3 (s : ℚ) :
    t2Step2Coefficient3 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient3,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_4 (s : ℚ) :
    t2Step2Coefficient4 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient4,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_5 (s : ℚ) :
    t2Step2Coefficient5 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient5,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_6 (s : ℚ) :
    t2Step2Coefficient6 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient6,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_7 (s : ℚ) :
    t2Step2Coefficient7 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient7,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
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
theorem t2Step2Coefficient_product_certificate_8 (s : ℚ) :
    t2Step2Coefficient8 s =
    t2Step1Coefficient0 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient8,
    t2Step1Coefficient0,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
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
theorem t2Step2Coefficient_product_certificate_9 (s : ℚ) :
    t2Step2Coefficient9 s =
    t2Step1Coefficient1 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient9,
    t2Step1Coefficient1,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
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
theorem t2Step2Coefficient_product_certificate_10 (s : ℚ) :
    t2Step2Coefficient10 s =
    t2Step1Coefficient2 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient10,
    t2Step1Coefficient2,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
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
theorem t2Step2Coefficient_product_certificate_11 (s : ℚ) :
    t2Step2Coefficient11 s =
    t2Step1Coefficient3 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient11,
    t2Step1Coefficient3,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
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
theorem t2Step2Coefficient_product_certificate_12 (s : ℚ) :
    t2Step2Coefficient12 s =
    t2Step1Coefficient4 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient12,
    t2Step1Coefficient4,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    t2Step1Coefficient12,
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
theorem t2Step2Coefficient_product_certificate_13 (s : ℚ) :
    t2Step2Coefficient13 s =
    t2Step1Coefficient5 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient13,
    t2Step1Coefficient5,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    t2Step1Coefficient12,
    t2Step1Coefficient13,
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
theorem t2Step2Coefficient_product_certificate_14 (s : ℚ) :
    t2Step2Coefficient14 s =
    t2Step1Coefficient6 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient14,
    t2Step1Coefficient6,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    t2Step1Coefficient12,
    t2Step1Coefficient13,
    t2Step1Coefficient14,
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
theorem t2Step2Coefficient_product_certificate_15 (s : ℚ) :
    t2Step2Coefficient15 s =
    t2Step1Coefficient7 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient1 s
      + t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [t2Step2Coefficient15,
    t2Step1Coefficient7,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    t2Step1Coefficient12,
    t2Step1Coefficient13,
    t2Step1Coefficient14,
    t2Step1Coefficient15,
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
theorem t2Step2Coefficient_product_certificate_16 (s : ℚ) :
    t2Step2Coefficient16 s =
    t2Step1Coefficient8 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient2 s
      + t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient1 s
    := by
  simp only [t2Step2Coefficient16,
    t2Step1Coefficient8,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    t2Step1Coefficient12,
    t2Step1Coefficient13,
    t2Step1Coefficient14,
    t2Step1Coefficient15,
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
theorem t2Step2Coefficient_product_certificate_17 (s : ℚ) :
    t2Step2Coefficient17 s =
    t2Step1Coefficient9 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient3 s
      + t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient2 s
    := by
  simp only [t2Step2Coefficient17,
    t2Step1Coefficient9,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    t2Step1Coefficient12,
    t2Step1Coefficient13,
    t2Step1Coefficient14,
    t2Step1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_18 (s : ℚ) :
    t2Step2Coefficient18 s =
    t2Step1Coefficient10 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient4 s
      + t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient3 s
    := by
  simp only [t2Step2Coefficient18,
    t2Step1Coefficient10,
    t2Step1Coefficient11,
    t2Step1Coefficient12,
    t2Step1Coefficient13,
    t2Step1Coefficient14,
    t2Step1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_19 (s : ℚ) :
    t2Step2Coefficient19 s =
    t2Step1Coefficient11 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient5 s
      + t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient4 s
    := by
  simp only [t2Step2Coefficient19,
    t2Step1Coefficient11,
    t2Step1Coefficient12,
    t2Step1Coefficient13,
    t2Step1Coefficient14,
    t2Step1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_20 (s : ℚ) :
    t2Step2Coefficient20 s =
    t2Step1Coefficient12 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient6 s
      + t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient5 s
    := by
  simp only [t2Step2Coefficient20,
    t2Step1Coefficient12,
    t2Step1Coefficient13,
    t2Step1Coefficient14,
    t2Step1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_21 (s : ℚ) :
    t2Step2Coefficient21 s =
    t2Step1Coefficient13 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient7 s
      + t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient6 s
    := by
  simp only [t2Step2Coefficient21,
    t2Step1Coefficient13,
    t2Step1Coefficient14,
    t2Step1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_22 (s : ℚ) :
    t2Step2Coefficient22 s =
    t2Step1Coefficient14 s *
        rawUnitFourDenominatorCoefficient8 s
      + t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient7 s
    := by
  simp only [t2Step2Coefficient22,
    t2Step1Coefficient14,
    t2Step1Coefficient15,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step2Coefficient_product_certificate_23 (s : ℚ) :
    t2Step2Coefficient23 s =
    t2Step1Coefficient15 s *
        rawUnitFourDenominatorCoefficient8 s
    := by
  simp only [t2Step2Coefficient23,
    t2Step1Coefficient15,
    rawUnitFourDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step2_eq_t2Step1_mul_rawUnitFourDenominator (r s : ℚ) :
    t2Step2 r s = t2Step1 r s * rawUnitFourDenominator r s := by
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
  simp only [t2Step2, t2Step1, rawUnitFourDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient2 (s : ℚ) : ℚ :=
  s ^ 31
    - 7 * s ^ 30
    + 26 * s ^ 29
    - 68 * s ^ 28
    + 139 * s ^ 27
    - 235 * s ^ 26
    + 340 * s ^ 25
    - 430 * s ^ 24
    + 482 * s ^ 23
    - 482 * s ^ 22
    + 430 * s ^ 21
    - 340 * s ^ 20
    + 235 * s ^ 19
    - 139 * s ^ 18
    + 68 * s ^ 17
    - 26 * s ^ 16
    + 7 * s ^ 15
    - s ^ 14

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient3 (s : ℚ) : ℚ :=
  -4 * s ^ 33
    + 41 * s ^ 32
    - 208 * s ^ 31
    + 673 * s ^ 30
    - 1582 * s ^ 29
    + 2905 * s ^ 28
    - 4330 * s ^ 27
    + 5339 * s ^ 26
    - 5422 * s ^ 25
    + 4308 * s ^ 24
    - 2084 * s ^ 23
    - 856 * s ^ 22
    + 3902 * s ^ 21
    - 6361 * s ^ 20
    + 7646 * s ^ 19
    - 7503 * s ^ 18
    + 6166 * s ^ 17
    - 4243 * s ^ 16
    + 2412 * s ^ 15
    - 1107 * s ^ 14
    + 396 * s ^ 13
    - 106 * s ^ 12
    + 20 * s ^ 11
    - 2 * s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient4 (s : ℚ) : ℚ :=
  6 * s ^ 35
    - 82 * s ^ 34
    + 536 * s ^ 33
    - 2143 * s ^ 32
    + 5766 * s ^ 31
    - 10725 * s ^ 30
    + 13005 * s ^ 29
    - 5374 * s ^ 28
    - 19687 * s ^ 27
    + 65648 * s ^ 26
    - 129593 * s ^ 25
    + 203003 * s ^ 24
    - 274549 * s ^ 23
    + 332371 * s ^ 22
    - 364521 * s ^ 21
    + 360888 * s ^ 20
    - 317833 * s ^ 19
    + 243046 * s ^ 18
    - 155341 * s ^ 17
    + 76844 * s ^ 16
    - 22949 * s ^ 15
    - 3530 * s ^ 14
    + 10235 * s ^ 13
    - 7853 * s ^ 12
    + 3989 * s ^ 11
    - 1507 * s ^ 10
    + 427 * s ^ 9
    - 89 * s ^ 8
    + 13 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient5 (s : ℚ) : ℚ :=
  -4 * s ^ 37
    + 70 * s ^ 36
    - 564 * s ^ 35
    + 2654 * s ^ 34
    - 7572 * s ^ 33
    + 10384 * s ^ 32
    + 13536 * s ^ 31
    - 117944 * s ^ 30
    + 371110 * s ^ 29
    - 817945 * s ^ 28
    + 1445918 * s ^ 27
    - 2184353 * s ^ 26
    + 2938710 * s ^ 25
    - 3620127 * s ^ 24
    + 4139690 * s ^ 23
    - 4374798 * s ^ 22
    + 4165556 * s ^ 21
    - 3398422 * s ^ 20
    + 2130072 * s ^ 19
    - 641959 * s ^ 18
    - 657006 * s ^ 17
    + 1435445 * s ^ 16
    - 1601756 * s ^ 15
    + 1317045 * s ^ 14
    - 859172 * s ^ 13
    + 454205 * s ^ 12
    - 195492 * s ^ 11
    + 68016 * s ^ 10
    - 18654 * s ^ 9
    + 3878 * s ^ 8
    - 564 * s ^ 7
    + 43 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient6 (s : ℚ) : ℚ :=
  s ^ 39
    - 23 * s ^ 38
    + 220 * s ^ 37
    - 1064 * s ^ 36
    + 1661 * s ^ 35
    + 12325 * s ^ 34
    - 105079 * s ^ 33
    + 442023 * s ^ 32
    - 1282433 * s ^ 31
    + 2825879 * s ^ 30
    - 4977777 * s ^ 29
    + 7282510 * s ^ 28
    - 9164721 * s ^ 27
    + 10295106 * s ^ 26
    - 10664214 * s ^ 25
    + 10109343 * s ^ 24
    - 7640369 * s ^ 23
    + 1323831 * s ^ 22
    + 10639334 * s ^ 21
    - 28019426 * s ^ 20
    + 47389844 * s ^ 19
    - 62993147 * s ^ 18
    + 69528529 * s ^ 17
    - 65060862 * s ^ 16
    + 51987107 * s ^ 15
    - 35486042 * s ^ 14
    + 20613982 * s ^ 13
    - 10120439 * s ^ 12
    + 4157945 * s ^ 11
    - 1406003 * s ^ 10
    + 379981 * s ^ 9
    - 78449 * s ^ 8
    + 11257 * s ^ 7
    - 826 * s ^ 6
    - 4 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient7 (s : ℚ) : ℚ :=
  s ^ 40
    - 8 * s ^ 39
    - 113 * s ^ 38
    + 2534 * s ^ 37
    - 23071 * s ^ 36
    + 131694 * s ^ 35
    - 526733 * s ^ 34
    + 1537394 * s ^ 33
    - 3278956 * s ^ 32
    + 4817258 * s ^ 31
    - 3454737 * s ^ 30
    - 4652732 * s ^ 29
    + 22371368 * s ^ 28
    - 50001174 * s ^ 27
    + 86903211 * s ^ 26
    - 136810642 * s ^ 25
    + 213141752 * s ^ 24
    - 337729952 * s ^ 23
    + 528745648 * s ^ 22
    - 781250628 * s ^ 21
    + 1053563952 * s ^ 20
    - 1273928046 * s ^ 19
    + 1369421026 * s ^ 18
    - 1302424042 * s ^ 17
    + 1091367113 * s ^ 16
    - 801684440 * s ^ 15
    + 513018769 * s ^ 14
    - 283800072 * s ^ 13
    + 134422410 * s ^ 12
    - 53827542 * s ^ 11
    + 17869694 * s ^ 10
    - 4765526 * s ^ 9
    + 970824 * s ^ 8
    - 135470 * s ^ 7
    + 9059 * s ^ 6
    + 178 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient8 (s : ℚ) : ℚ :=
  -2 * s ^ 41
    + 63 * s ^ 40
    - 910 * s ^ 39
    + 7925 * s ^ 38
    - 45735 * s ^ 37
    + 177146 * s ^ 36
    - 410417 * s ^ 35
    + 96530 * s ^ 34
    + 3743571 * s ^ 33
    - 18832029 * s ^ 32
    + 58292036 * s ^ 31
    - 136673337 * s ^ 30
    + 264176643 * s ^ 29
    - 450297345 * s ^ 28
    + 726900892 * s ^ 27
    - 1184411059 * s ^ 26
    + 1993880862 * s ^ 25
    - 3376973136 * s ^ 24
    + 5501224466 * s ^ 23
    - 8325392314 * s ^ 22
    + 11478636600 * s ^ 21
    - 14282537556 * s ^ 20
    + 15963239718 * s ^ 19
    - 15976147928 * s ^ 18
    + 14270297656 * s ^ 17
    - 11328370747 * s ^ 16
    + 7948792414 * s ^ 15
    - 4896779767 * s ^ 14
    + 2626764561 * s ^ 13
    - 1214295345 * s ^ 12
    + 476943331 * s ^ 11
    - 155756249 * s ^ 10
    + 40870417 * s ^ 9
    - 8136625 * s ^ 8
    + 1077150 * s ^ 7
    - 57905 * s ^ 6
    - 3605 * s ^ 5
    + 30 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient9 (s : ℚ) : ℚ :=
  -2 * s ^ 42
    + 44 * s ^ 41
    - 386 * s ^ 40
    + 888 * s ^ 39
    + 15310 * s ^ 38
    - 205238 * s ^ 37
    + 1422343 * s ^ 36
    - 6856758 * s ^ 35
    + 25076695 * s ^ 34
    - 72617706 * s ^ 33
    + 171924885 * s ^ 32
    - 346161704 * s ^ 31
    + 632966066 * s ^ 30
    - 1158553226 * s ^ 29
    + 2293078275 * s ^ 28
    - 4834770514 * s ^ 27
    + 10087106111 * s ^ 26
    - 19658121018 * s ^ 25
    + 34866270495 * s ^ 24
    - 55828229344 * s ^ 23
    + 80601108114 * s ^ 22
    - 104972497732 * s ^ 21
    + 123366577168 * s ^ 20
    - 130754619592 * s ^ 19
    + 124759408952 * s ^ 18
    - 106828901692 * s ^ 17
    + 81727295064 * s ^ 16
    - 55542357822 * s ^ 15
    + 33298754326 * s ^ 14
    - 17459768078 * s ^ 13
    + 7917896043 * s ^ 12
    - 3057149384 * s ^ 11
    + 981047510 * s ^ 10
    - 251786204 * s ^ 9
    + 48226020 * s ^ 8
    - 5775446 * s ^ 7
    + 154358 * s ^ 6
    + 43490 * s ^ 5
    - 307 * s ^ 4
    - 4 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient10 (s : ℚ) : ℚ :=
  s ^ 43
    - 41 * s ^ 42
    + 789 * s ^ 41
    - 9443 * s ^ 40
    + 78837 * s ^ 39
    - 487391 * s ^ 38
    + 2307409 * s ^ 37
    - 8522202 * s ^ 36
    + 24814417 * s ^ 35
    - 57747824 * s ^ 34
    + 113423006 * s ^ 33
    - 226949503 * s ^ 32
    + 604961120 * s ^ 31
    - 1992997266 * s ^ 30
    + 6301859680 * s ^ 29
    - 17318086143 * s ^ 28
    + 41079446542 * s ^ 27
    - 85334518169 * s ^ 26
    + 157523684527 * s ^ 25
    - 261139688258 * s ^ 24
    + 391366210564 * s ^ 23
    - 532185515330 * s ^ 22
    + 657617182820 * s ^ 21
    - 738371153984 * s ^ 20
    + 752190487735 * s ^ 19
    - 693327918469 * s ^ 18
    + 575971223959 * s ^ 17
    - 429073347443 * s ^ 16
    + 284898479796 * s ^ 15
    - 167380174496 * s ^ 14
    + 86219147704 * s ^ 13
    - 38466120305 * s ^ 12
    + 14602162259 * s ^ 11
    - 4587839921 * s ^ 10
    + 1139555587 * s ^ 9
    - 204117271 * s ^ 8
    + 19719269 * s ^ 7
    + 792051 * s ^ 6
    - 344801 * s ^ 5
    + 64 * s ^ 4
    + 124 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient11 (s : ℚ) : ℚ :=
  s ^ 44
    - 32 * s ^ 43
    + 491 * s ^ 42
    - 4694 * s ^ 41
    + 30354 * s ^ 40
    - 132744 * s ^ 39
    + 341941 * s ^ 38
    - 39910 * s ^ 37
    - 3814066 * s ^ 36
    + 15403330 * s ^ 35
    - 7670189 * s ^ 34
    - 231448324 * s ^ 33
    + 1557226200 * s ^ 32
    - 6459077406 * s ^ 31
    + 20689607482 * s ^ 30
    - 55304581938 * s ^ 29
    + 128408123051 * s ^ 28
    - 265280072218 * s ^ 27
    + 494872934509 * s ^ 26
    - 840676487152 * s ^ 25
    + 1306077504366 * s ^ 24
    - 1858853866008 * s ^ 23
    + 2423809631848 * s ^ 22
    - 2892651380552 * s ^ 21
    + 3153570621279 * s ^ 20
    - 3131750952184 * s ^ 19
    + 2822495276897 * s ^ 18
    - 2298042657426 * s ^ 17
    + 1681209405451 * s ^ 16
    - 1098202422640 * s ^ 15
    + 635650122460 * s ^ 14
    - 322798189680 * s ^ 13
    + 141849157445 * s ^ 12
    - 52831155040 * s ^ 11
    + 16128535606 * s ^ 10
    - 3800858200 * s ^ 9
    + 598828857 * s ^ 8
    - 28922974 * s ^ 7
    - 10914127 * s ^ 6
    + 1868116 * s ^ 5
    + 29478 * s ^ 4
    - 1652 * s ^ 3
    - 6 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient12 (s : ℚ) : ℚ :=
  s ^ 44
    - 42 * s ^ 43
    + 801 * s ^ 42
    - 9295 * s ^ 41
    + 72431 * s ^ 40
    - 381808 * s ^ 39
    + 1159105 * s ^ 38
    + 797296 * s ^ 37
    - 34829216 * s ^ 36
    + 253465361 * s ^ 35
    - 1242896864 * s ^ 34
    + 4808832743 * s ^ 33
    - 15606105777 * s ^ 32
    + 43995094085 * s ^ 31
    - 110370749509 * s ^ 30
    + 250713248915 * s ^ 29
    - 521652021446 * s ^ 28
    + 1000492091789 * s ^ 27
    - 1772919676412 * s ^ 26
    + 2902498730186 * s ^ 25
    - 4384827962220 * s ^ 24
    + 6103046851094 * s ^ 23
    - 7811926994034 * s ^ 22
    + 9175302321628 * s ^ 21
    - 9861012670301 * s ^ 20
    + 9664218201672 * s ^ 19
    - 8601635900043 * s ^ 18
    + 6920160756957 * s ^ 17
    - 5005133530388 * s ^ 16
    + 3233592107000 * s ^ 15
    - 1850933116332 * s ^ 14
    + 928333824951 * s ^ 13
    - 401370441126 * s ^ 12
    + 145806410164 * s ^ 11
    - 42584642646 * s ^ 10
    + 9125613558 * s ^ 9
    - 1052428413 * s ^ 8
    - 100191998 * s ^ 7
    + 62182259 * s ^ 6
    - 6879447 * s ^ 5
    - 346997 * s ^ 4
    + 12151 * s ^ 3
    + 167 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient13 (s : ℚ) : ℚ :=
  2 * s ^ 44
    - 96 * s ^ 43
    + 2186 * s ^ 42
    - 31666 * s ^ 41
    + 329515 * s ^ 40
    - 2633308 * s ^ 39
    + 16863441 * s ^ 38
    - 89189602 * s ^ 37
    + 398908365 * s ^ 36
    - 1539869362 * s ^ 35
    + 5228897079 * s ^ 34
    - 15906753218 * s ^ 33
    + 44082341581 * s ^ 32
    - 112785007850 * s ^ 31
    + 268561657014 * s ^ 30
    - 596587019394 * s ^ 29
    + 1234143103352 * s ^ 28
    - 2369206862624 * s ^ 27
    + 4206948358784 * s ^ 26
    - 6893878845384 * s ^ 25
    + 10409780865087 * s ^ 24
    - 14465935847492 * s ^ 23
    + 18471121122798 * s ^ 22
    - 21624078964460 * s ^ 21
    + 23144411931608 * s ^ 20
    - 22569629820944 * s ^ 19
    + 19973306870594 * s ^ 18
    - 15968213419886 * s ^ 17
    + 11471697184477 * s ^ 16
    - 7356211703560 * s ^ 15
    + 4172322915347 * s ^ 14
    - 2065517063316 * s ^ 13
    + 874303644572 * s ^ 12
    - 305675200924 * s ^ 11
    + 82538469692 * s ^ 10
    - 14315583956 * s ^ 9
    + 99904330 * s ^ 8
    + 819795800 * s ^ 7
    - 227172172 * s ^ 6
    + 15621902 * s ^ 5
    + 2254087 * s ^ 4
    - 50320 * s ^ 3
    - 2075 * s ^ 2
    - 4 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient14 (s : ℚ) : ℚ :=
  s ^ 45
    - 41 * s ^ 44
    + 827 * s ^ 43
    - 10887 * s ^ 42
    + 104926 * s ^ 41
    - 789141 * s ^ 40
    + 4834256 * s ^ 39
    - 24950533 * s ^ 38
    + 111852037 * s ^ 37
    - 448434798 * s ^ 36
    + 1650318223 * s ^ 35
    - 5676827266 * s ^ 34
    + 18364323048 * s ^ 33
    - 55612054011 * s ^ 32
    + 156146161236 * s ^ 31
    - 402964767852 * s ^ 30
    + 950952698250 * s ^ 29
    - 2049303087270 * s ^ 28
    + 4037357161693 * s ^ 27
    - 7287277241727 * s ^ 26
    + 12074099402669 * s ^ 25
    - 18381838475498 * s ^ 24
    + 25707077114383 * s ^ 23
    - 32978850593907 * s ^ 22
    + 38721601316039 * s ^ 21
    - 41492878590247 * s ^ 20
    + 40447575589458 * s ^ 19
    - 35738059219730 * s ^ 18
    + 28498927869829 * s ^ 17
    - 20399269683110 * s ^ 16
    + 13007980958292 * s ^ 15
    - 7307556121667 * s ^ 14
    + 3554552446182 * s ^ 13
    - 1454753870780 * s ^ 12
    + 474635496421 * s ^ 11
    - 108002142285 * s ^ 10
    + 7891803797 * s ^ 9
    + 5985208869 * s ^ 8
    - 2948556948 * s ^ 7
    + 569984392 * s ^ 6
    - 9505110 * s ^ 5
    - 9812489 * s ^ 4
    + 75099 * s ^ 3
    + 15274 * s ^ 2
    + 96 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient15 (s : ℚ) : ℚ :=
  -2 * s ^ 44
    + 70 * s ^ 43
    - 1147 * s ^ 42
    + 11170 * s ^ 41
    - 63839 * s ^ 40
    + 91718 * s ^ 39
    + 2253287 * s ^ 38
    - 28480856 * s ^ 37
    + 210596014 * s ^ 36
    - 1172673970 * s ^ 35
    + 5314130143 * s ^ 34
    - 20361487870 * s ^ 33
    + 67569929263 * s ^ 32
    - 197661201260 * s ^ 31
    + 516912808059 * s ^ 30
    - 1222314934338 * s ^ 29
    + 2636381125823 * s ^ 28
    - 5217109093224 * s ^ 27
    + 9500137150110 * s ^ 26
    - 15926401299000 * s ^ 25
    + 24550319271974 * s ^ 24
    - 34722522464840 * s ^ 23
    + 44946892569485 * s ^ 22
    - 53116722846134 * s ^ 21
    + 57163998012781 * s ^ 20
    - 55875539673768 * s ^ 19
    + 49447603910724 * s ^ 18
    - 39447657201484 * s ^ 17
    + 28190776964412 * s ^ 16
    - 17873285886856 * s ^ 15
    + 9901307656565 * s ^ 14
    - 4673227298262 * s ^ 13
    + 1793532669911 * s ^ 12
    - 501106266102 * s ^ 11
    + 61074181959 * s ^ 10
    + 28809112638 * s ^ 9
    - 21709304389 * s ^ 8
    + 6965974158 * s ^ 7
    - 938155856 * s ^ 6
    - 80774458 * s ^ 5
    + 30340645 * s ^ 4
    + 421882 * s ^ 3
    - 74081 * s ^ 2
    - 1054 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient16 (s : ℚ) : ℚ :=
  -2 * s ^ 44
    + 89 * s ^ 43
    - 1938 * s ^ 42
    + 27524 * s ^ 41
    - 286557 * s ^ 40
    + 2330702 * s ^ 39
    - 15418943 * s ^ 38
    + 85365575 * s ^ 37
    - 404368671 * s ^ 36
    + 1669901874 * s ^ 35
    - 6115429041 * s ^ 34
    + 20176902508 * s ^ 33
    - 60818868231 * s ^ 32
    + 169281997742 * s ^ 31
    - 437680623859 * s ^ 30
    + 1052158437771 * s ^ 29
    - 2344867376514 * s ^ 28
    + 4821893897816 * s ^ 27
    - 9106081005174 * s ^ 26
    + 15734670437279 * s ^ 25
    - 24816529320965 * s ^ 24
    + 35675426959862 * s ^ 23
    - 46707645490717 * s ^ 22
    + 55655216541863 * s ^ 21
    - 60297260837588 * s ^ 20
    + 59290743939972 * s ^ 19
    - 52744764458804 * s ^ 18
    + 42219038242241 * s ^ 17
    - 30138411306693 * s ^ 16
    + 18915449828630 * s ^ 15
    - 10193347074005 * s ^ 14
    + 4515275991233 * s ^ 13
    - 1483986524100 * s ^ 12
    + 230668422377 * s ^ 11
    + 105086892836 * s ^ 10
    - 105047445865 * s ^ 9
    + 46530906062 * s ^ 8
    - 11398640392 * s ^ 7
    + 687194784 * s ^ 6
    + 380346990 * s ^ 5
    - 66919017 * s ^ 4
    - 3421568 * s ^ 3
    + 245821 * s ^ 2
    + 7073 * s
    + 20

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient17 (s : ℚ) : ℚ :=
  2 * s ^ 43
    - 76 * s ^ 42
    + 1390 * s ^ 41
    - 16013 * s ^ 40
    + 126276 * s ^ 39
    - 670120 * s ^ 38
    + 1795598 * s ^ 37
    + 6608243 * s ^ 36
    - 119963358 * s ^ 35
    + 900755807 * s ^ 34
    - 4870316586 * s ^ 33
    + 21168164317 * s ^ 32
    - 77322932648 * s ^ 31
    + 243139419160 * s ^ 30
    - 668338999838 * s ^ 29
    + 1623770923155 * s ^ 28
    - 3516835142712 * s ^ 27
    + 6837136930697 * s ^ 26
    - 11998431847720 * s ^ 25
    + 19090790911236 * s ^ 24
    - 27630194503572 * s ^ 23
    + 36448447208794 * s ^ 22
    - 43851678185290 * s ^ 21
    + 48070004169037 * s ^ 20
    - 47865982515016 * s ^ 19
    + 43050981191029 * s ^ 18
    - 34651444062092 * s ^ 17
    + 24597430628866 * s ^ 16
    - 15034110521196 * s ^ 15
    + 7568563587444 * s ^ 14
    - 2819263093842 * s ^ 13
    + 465198043481 * s ^ 12
    + 317954267210 * s ^ 11
    - 358292909931 * s ^ 10
    + 197926422950 * s ^ 9
    - 68780573277 * s ^ 8
    + 11913380076 * s ^ 7
    + 1185398382 * s ^ 6
    - 964786340 * s ^ 5
    + 98488216 * s ^ 4
    + 13194186 * s ^ 3
    - 543186 * s ^ 2
    - 32550 * s
    - 189

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient18 (s : ℚ) : ℚ :=
  s ^ 43
    - 47 * s ^ 42
    + 1086 * s ^ 41
    - 16459 * s ^ 40
    + 183896 * s ^ 39
    - 1612868 * s ^ 38
    + 11541652 * s ^ 37
    - 69155497 * s ^ 36
    + 353430650 * s ^ 35
    - 1562296535 * s ^ 34
    + 6040122386 * s ^ 33
    - 20617780809 * s ^ 32
    + 62660374305 * s ^ 31
    - 170867887913 * s ^ 30
    + 421094985553 * s ^ 29
    - 944078668796 * s ^ 28
    + 1936365114168 * s ^ 27
    - 3649083310037 * s ^ 26
    + 6335259283449 * s ^ 25
    - 10142660487145 * s ^ 24
    + 14964089743484 * s ^ 23
    - 20299430364768 * s ^ 22
    + 25222648206005 * s ^ 21
    - 28545471417330 * s ^ 20
    + 29196037940652 * s ^ 19
    - 26692767020369 * s ^ 18
    + 21467459849727 * s ^ 17
    - 14799330106461 * s ^ 16
    + 8321399992499 * s ^ 15
    - 3345403744603 * s ^ 14
    + 397818788029 * s ^ 13
    + 784567344508 * s ^ 12
    - 884978858590 * s ^ 11
    + 571572220267 * s ^ 10
    - 252902836669 * s ^ 9
    + 69128687998 * s ^ 8
    - 3777067986 * s ^ 7
    - 5053495258 * s ^ 6
    + 1646764017 * s ^ 5
    - 65039449 * s ^ 4
    - 34157415 * s ^ 3
    + 640755 * s ^ 2
    + 108797 * s
    + 1120

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient19 (s : ℚ) : ℚ :=
  -2 * s ^ 41
    + 78 * s ^ 40
    - 1502 * s ^ 39
    + 19168 * s ^ 38
    - 183724 * s ^ 37
    + 1421245 * s ^ 36
    - 9293824 * s ^ 35
    + 52911733 * s ^ 34
    - 266657164 * s ^ 33
    + 1198190532 * s ^ 32
    - 4808152552 * s ^ 31
    + 17220884537 * s ^ 30
    - 55013778080 * s ^ 29
    + 156789069234 * s ^ 28
    - 399124905060 * s ^ 27
    + 909230587405 * s ^ 26
    - 1857486786694 * s ^ 25
    + 3408949585317 * s ^ 24
    - 5624714968760 * s ^ 23
    + 8337737427196 * s ^ 22
    - 11072722249280 * s ^ 21
    + 13102055610358 * s ^ 20
    - 13685455905592 * s ^ 19
    + 12421769491191 * s ^ 18
    - 9518216330794 * s ^ 17
    + 5774611327200 * s ^ 16
    - 2240959617616 * s ^ 15
    - 260921246063 * s ^ 14
    + 1452522533666 * s ^ 13
    - 1580525880125 * s ^ 12
    + 1147035610770 * s ^ 11
    - 610090124756 * s ^ 10
    + 223075050558 * s ^ 9
    - 36805435029 * s ^ 8
    - 12638399058 * s ^ 7
    + 9442650216 * s ^ 6
    - 1895512402 * s ^ 5
    - 100866746 * s ^ 4
    + 63779594 * s ^ 3
    + 421133 * s ^ 2
    - 271652 * s
    - 4656

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient20 (s : ℚ) : ℚ :=
  -2 * s ^ 40
    + 94 * s ^ 39
    - 2130 * s ^ 38
    + 31158 * s ^ 37
    - 331723 * s ^ 36
    + 2743942 * s ^ 35
    - 18370033 * s ^ 34
    + 102344038 * s ^ 33
    - 484163650 * s ^ 32
    + 1975086851 * s ^ 31
    - 7033533426 * s ^ 30
    + 22086372442 * s ^ 29
    - 61664541960 * s ^ 28
    + 154084618891 * s ^ 27
    - 346202649702 * s ^ 26
    + 701221274296 * s ^ 25
    - 1280632324083 * s ^ 24
    + 2104133865091 * s ^ 23
    - 3095499744235 * s ^ 22
    + 4045802537577 * s ^ 21
    - 4639638341799 * s ^ 20
    + 4568729632800 * s ^ 19
    - 3696443564205 * s ^ 18
    + 2176239608289 * s ^ 17
    - 427424370063 * s ^ 16
    - 1043990964682 * s ^ 15
    + 1877469130215 * s ^ 14
    - 1998805675540 * s ^ 13
    + 1598442766621 * s ^ 12
    - 990081312237 * s ^ 11
    + 449288875623 * s ^ 10
    - 115398326210 * s ^ 9
    - 15429076219 * s ^ 8
    + 28997081593 * s ^ 7
    - 11319243667 * s ^ 6
    + 1192707912 * s ^ 5
    + 387231600 * s ^ 4
    - 86019675 * s ^ 3
    - 3878092 * s ^ 2
    + 509914 * s
    + 14386

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient21 (s : ℚ) : ℚ :=
  4 * s ^ 38
    - 166 * s ^ 37
    + 3364 * s ^ 36
    - 44532 * s ^ 35
    + 433983 * s ^ 34
    - 3322300 * s ^ 33
    + 20790103 * s ^ 32
    - 109128016 * s ^ 31
    + 488746564 * s ^ 30
    - 1888745236 * s ^ 29
    + 6343817407 * s ^ 28
    - 18602044508 * s ^ 27
    + 47739330298 * s ^ 26
    - 107311419260 * s ^ 25
    + 211074662073 * s ^ 24
    - 361968795956 * s ^ 23
    + 536650095954 * s ^ 22
    - 675134976168 * s ^ 21
    + 689037420796 * s ^ 20
    - 495565242744 * s ^ 19
    + 67352606496 * s ^ 18
    + 529832431386 * s ^ 17
    - 1142057244017 * s ^ 16
    + 1583109136412 * s ^ 15
    - 1715599513845 * s ^ 14
    + 1514360807550 * s ^ 13
    - 1078816090835 * s ^ 12
    + 584672137146 * s ^ 11
    - 196607099535 * s ^ 10
    - 7992795780 * s ^ 9
    + 56912160846 * s ^ 8
    - 34333828722 * s ^ 7
    + 8615861597 * s ^ 6
    + 339720938 * s ^ 5
    - 646878276 * s ^ 4
    + 77942128 * s ^ 3
    + 9803988 * s ^ 2
    - 705004 * s
    - 34133

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient22 (s : ℚ) : ℚ :=
  s ^ 37
    - 47 * s ^ 36
    + 1037 * s ^ 35
    - 14434 * s ^ 34
    + 143211 * s ^ 33
    - 1082672 * s ^ 32
    + 6501143 * s ^ 31
    - 31889729 * s ^ 30
    + 130375947 * s ^ 29
    - 450900758 * s ^ 28
    + 1333710177 * s ^ 27
    - 3398276243 * s ^ 26
    + 7473508298 * s ^ 25
    - 14079036697 * s ^ 24
    + 22074963278 * s ^ 23
    - 26275708240 * s ^ 22
    + 14674437621 * s ^ 21
    + 32369836809 * s ^ 20
    - 137211239445 * s ^ 19
    + 312086834227 * s ^ 18
    - 542261429292 * s ^ 17
    + 776066257173 * s ^ 16
    - 934215487711 * s ^ 15
    + 942875847114 * s ^ 14
    - 778354614846 * s ^ 13
    + 493612224293 * s ^ 12
    - 197926678193 * s ^ 11
    - 5640125458 * s ^ 10
    + 80215860547 * s ^ 9
    - 64369959019 * s ^ 8
    + 25152070283 * s ^ 7
    - 2709823908 * s ^ 6
    - 1786014874 * s ^ 5
    + 686789618 * s ^ 4
    - 32038493 * s ^ 3
    - 15765725 * s ^ 2
    + 661679 * s
    + 63328

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient23 (s : ℚ) : ℚ :=
  -2 * s ^ 35
    + 84 * s ^ 34
    - 1698 * s ^ 33
    + 22082 * s ^ 32
    - 207904 * s ^ 31
    + 1509126 * s ^ 30
    - 8768938 * s ^ 29
    + 41757509 * s ^ 28
    - 165323146 * s ^ 27
    + 548181422 * s ^ 26
    - 1522803406 * s ^ 25
    + 3510980911 * s ^ 24
    - 6529532778 * s ^ 23
    + 8996801581 * s ^ 22
    - 6047879762 * s ^ 21
    - 11403927217 * s ^ 20
    + 54738742498 * s ^ 19
    - 131264653763 * s ^ 18
    + 234696962494 * s ^ 17
    - 338231440504 * s ^ 16
    + 398943907570 * s ^ 15
    - 378353409842 * s ^ 14
    + 270517467222 * s ^ 13
    - 115322180607 * s ^ 12
    - 20730607194 * s ^ 11
    + 87102559375 * s ^ 10
    - 81261559330 * s ^ 9
    + 41642834318 * s ^ 8
    - 9213786876 * s ^ 7
    - 2408294775 * s ^ 6
    + 2191900854 * s ^ 5
    - 458655083 * s ^ 4
    - 28079960 * s ^ 3
    + 17859272 * s ^ 2
    - 280908 * s
    - 92625

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient24 (s : ℚ) : ℚ :=
  10 * s ^ 32
    - 380 * s ^ 31
    + 6936 * s ^ 30
    - 81380 * s ^ 29
    + 692429 * s ^ 28
    - 4566151 * s ^ 27
    + 24340789 * s ^ 26
    - 107981920 * s ^ 25
    + 407188963 * s ^ 24
    - 1325894950 * s ^ 23
    + 3770615781 * s ^ 22
    - 9431612661 * s ^ 21
    + 20805022538 * s ^ 20
    - 40383691641 * s ^ 19
    + 68464339472 * s ^ 18
    - 99989649714 * s ^ 17
    + 122870570992 * s ^ 16
    - 121508987442 * s ^ 15
    + 86586064140 * s ^ 14
    - 25416441180 * s ^ 13
    - 37343625015 * s ^ 12
    + 73487036978 * s ^ 11
    - 70995023209 * s ^ 10
    + 42449652789 * s ^ 9
    - 12764141073 * s ^ 8
    - 2180716144 * s ^ 7
    + 3904124705 * s ^ 6
    - 1496649731 * s ^ 5
    + 129682354 * s ^ 4
    + 64107402 * s ^ 3
    - 14214142 * s ^ 2
    - 276323 * s
    + 106778

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient25 (s : ℚ) : ℚ :=
  2 * s ^ 31
    - 88 * s ^ 30
    + 1824 * s ^ 29
    - 23884 * s ^ 28
    + 223200 * s ^ 27
    - 1591753 * s ^ 26
    + 9029276 * s ^ 25
    - 41854196 * s ^ 24
    + 161350130 * s ^ 23
    - 522894252 * s ^ 22
    + 1431798086 * s ^ 21
    - 3310798241 * s ^ 20
    + 6415118838 * s ^ 19
    - 10209590992 * s ^ 18
    + 12709856646 * s ^ 17
    - 10618606831 * s ^ 16
    + 1061861464 * s ^ 15
    + 15495861832 * s ^ 14
    - 33420630024 * s ^ 13
    + 43862012734 * s ^ 12
    - 40601280506 * s ^ 11
    + 25549424812 * s ^ 10
    - 8057926966 * s ^ 9
    - 2671787463 * s ^ 8
    + 4696365200 * s ^ 7
    - 2467728718 * s ^ 6
    + 502020194 * s ^ 5
    + 81259993 * s ^ 4
    - 59275192 * s ^ 3
    + 7227447 * s ^ 2
    + 673620 * s
    - 96192

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient26 (s : ℚ) : ℚ :=
  -s ^ 29
    + 35 * s ^ 28
    - 556 * s ^ 27
    + 5231 * s ^ 26
    - 31099 * s ^ 25
    + 104123 * s ^ 24
    + 26746 * s ^ 23
    - 2771606 * s ^ 22
    + 20205513 * s ^ 21
    - 94916266 * s ^ 20
    + 340242593 * s ^ 19
    - 985753989 * s ^ 18
    + 2368834117 * s ^ 17
    - 4774993714 * s ^ 16
    + 8081458664 * s ^ 15
    - 11372163622 * s ^ 14
    + 12972232161 * s ^ 13
    - 11325949235 * s ^ 12
    + 6427860944 * s ^ 11
    - 478054532 * s ^ 10
    - 3467997374 * s ^ 9
    + 4005560649 * s ^ 8
    - 2350802964 * s ^ 7
    + 660250120 * s ^ 6
    + 57821019 * s ^ 5
    - 110498544 * s ^ 4
    + 31333573 * s ^ 3
    - 1365306 * s ^ 2
    - 703144 * s
    + 66464

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient27 (s : ℚ) : ℚ :=
  4 * s ^ 26
    - 148 * s ^ 25
    + 2584 * s ^ 24
    - 28410 * s ^ 23
    + 221324 * s ^ 22
    - 1301746 * s ^ 21
    + 6003408 * s ^ 20
    - 22202406 * s ^ 19
    + 66571440 * s ^ 18
    - 161786434 * s ^ 17
    + 313762567 * s ^ 16
    - 463486774 * s ^ 15
    + 448486166 * s ^ 14
    - 58439838 * s ^ 13
    - 766623417 * s ^ 12
    + 1732219802 * s ^ 11
    - 2274430788 * s ^ 10
    + 2016526170 * s ^ 9
    - 1164675107 * s ^ 8
    + 323803172 * s ^ 7
    + 90401334 * s ^ 6
    - 129676180 * s ^ 5
    + 53149281 * s ^ 4
    - 7888760 * s ^ 3
    - 1034920 * s ^ 2
    + 461744 * s
    - 34068

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient28 (s : ℚ) : ℚ :=
  -6 * s ^ 23
    + 214 * s ^ 22
    - 3590 * s ^ 21
    + 37746 * s ^ 20
    - 279492 * s ^ 19
    + 1551134 * s ^ 18
    - 6696256 * s ^ 17
    + 22998355 * s ^ 16
    - 63627599 * s ^ 15
    + 142395479 * s ^ 14
    - 256728280 * s ^ 13
    + 367425373 * s ^ 12
    - 403744367 * s ^ 11
    + 314439103 * s ^ 10
    - 129405805 * s ^ 9
    - 46213548 * s ^ 8
    + 122091236 * s ^ 7
    - 99311814 * s ^ 6
    + 44464659 * s ^ 5
    - 9352722 * s ^ 4
    - 805960 * s ^ 3
    + 950368 * s ^ 2
    - 196444 * s
    + 12216

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient29 (s : ℚ) : ℚ :=
  4 * s ^ 20
    - 134 * s ^ 19
    + 2092 * s ^ 18
    - 20244 * s ^ 17
    + 136192 * s ^ 16
    - 676814 * s ^ 15
    + 2574767 * s ^ 14
    - 7659350 * s ^ 13
    + 18021430 * s ^ 12
    - 33657084 * s ^ 11
    + 49705000 * s ^ 10
    - 57337922 * s ^ 9
    + 50405678 * s ^ 8
    - 32135000 * s ^ 7
    + 13125049 * s ^ 6
    - 1787724 * s ^ 5
    - 1497176 * s ^ 4
    + 1087600 * s ^ 3
    - 333596 * s ^ 2
    + 49968 * s
    - 2736

/-- Coefficient of the indicated power of the raw chart variable. -/
def t2Step3Coefficient30 (s : ℚ) : ℚ :=
  -s ^ 17
    + 31 * s ^ 16
    - 442 * s ^ 15
    + 3845 * s ^ 14
    - 22827 * s ^ 13
    + 98017 * s ^ 12
    - 314761 * s ^ 11
    + 770941 * s ^ 10
    - 1455560 * s ^ 9
    + 2126372 * s ^ 8
    - 2398005 * s ^ 7
    + 2069858 * s ^ 6
    - 1345552 * s ^ 5
    + 641440 * s ^ 4
    - 214740 * s ^ 3
    + 46904 * s ^ 2
    - 5808 * s
    + 288

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
    t2Step3Coefficient29 s * r ^ 29 +
    t2Step3Coefficient30 s * r ^ 30

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_0 (s : ℚ) :
    t2Step3Coefficient0 s =
    t2Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient0,
    t2Step2Coefficient0,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_1 (s : ℚ) :
    t2Step3Coefficient1 s =
    t2Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient1,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_2 (s : ℚ) :
    t2Step3Coefficient2 s =
    t2Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient2,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_3 (s : ℚ) :
    t2Step3Coefficient3 s =
    t2Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient3,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_4 (s : ℚ) :
    t2Step3Coefficient4 s =
    t2Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient4,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_5 (s : ℚ) :
    t2Step3Coefficient5 s =
    t2Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient5,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_6 (s : ℚ) :
    t2Step3Coefficient6 s =
    t2Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient6,
    t2Step2Coefficient0,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_7 (s : ℚ) :
    t2Step3Coefficient7 s =
    t2Step2Coefficient0 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient0 s
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
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_8 (s : ℚ) :
    t2Step3Coefficient8 s =
    t2Step2Coefficient1 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient8,
    t2Step2Coefficient1,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_9 (s : ℚ) :
    t2Step3Coefficient9 s =
    t2Step2Coefficient2 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient9,
    t2Step2Coefficient2,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_10 (s : ℚ) :
    t2Step3Coefficient10 s =
    t2Step2Coefficient3 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient10,
    t2Step2Coefficient3,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_11 (s : ℚ) :
    t2Step3Coefficient11 s =
    t2Step2Coefficient4 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient11,
    t2Step2Coefficient4,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_12 (s : ℚ) :
    t2Step3Coefficient12 s =
    t2Step2Coefficient5 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient12,
    t2Step2Coefficient5,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_13 (s : ℚ) :
    t2Step3Coefficient13 s =
    t2Step2Coefficient6 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient13,
    t2Step2Coefficient6,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_14 (s : ℚ) :
    t2Step3Coefficient14 s =
    t2Step2Coefficient7 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient14,
    t2Step2Coefficient7,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_15 (s : ℚ) :
    t2Step3Coefficient15 s =
    t2Step2Coefficient8 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient15,
    t2Step2Coefficient8,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    t2Step2Coefficient15,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_16 (s : ℚ) :
    t2Step3Coefficient16 s =
    t2Step2Coefficient9 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient16,
    t2Step2Coefficient9,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    t2Step2Coefficient15,
    t2Step2Coefficient16,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_17 (s : ℚ) :
    t2Step3Coefficient17 s =
    t2Step2Coefficient10 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient17,
    t2Step2Coefficient10,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    t2Step2Coefficient15,
    t2Step2Coefficient16,
    t2Step2Coefficient17,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_18 (s : ℚ) :
    t2Step3Coefficient18 s =
    t2Step2Coefficient11 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient18,
    t2Step2Coefficient11,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    t2Step2Coefficient15,
    t2Step2Coefficient16,
    t2Step2Coefficient17,
    t2Step2Coefficient18,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_19 (s : ℚ) :
    t2Step3Coefficient19 s =
    t2Step2Coefficient12 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient19,
    t2Step2Coefficient12,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    t2Step2Coefficient15,
    t2Step2Coefficient16,
    t2Step2Coefficient17,
    t2Step2Coefficient18,
    t2Step2Coefficient19,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_20 (s : ℚ) :
    t2Step3Coefficient20 s =
    t2Step2Coefficient13 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient20,
    t2Step2Coefficient13,
    t2Step2Coefficient14,
    t2Step2Coefficient15,
    t2Step2Coefficient16,
    t2Step2Coefficient17,
    t2Step2Coefficient18,
    t2Step2Coefficient19,
    t2Step2Coefficient20,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_21 (s : ℚ) :
    t2Step3Coefficient21 s =
    t2Step2Coefficient14 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient21,
    t2Step2Coefficient14,
    t2Step2Coefficient15,
    t2Step2Coefficient16,
    t2Step2Coefficient17,
    t2Step2Coefficient18,
    t2Step2Coefficient19,
    t2Step2Coefficient20,
    t2Step2Coefficient21,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_22 (s : ℚ) :
    t2Step3Coefficient22 s =
    t2Step2Coefficient15 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient22,
    t2Step2Coefficient15,
    t2Step2Coefficient16,
    t2Step2Coefficient17,
    t2Step2Coefficient18,
    t2Step2Coefficient19,
    t2Step2Coefficient20,
    t2Step2Coefficient21,
    t2Step2Coefficient22,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_23 (s : ℚ) :
    t2Step3Coefficient23 s =
    t2Step2Coefficient16 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient1 s
      + t2Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient0 s
    := by
  simp only [t2Step3Coefficient23,
    t2Step2Coefficient16,
    t2Step2Coefficient17,
    t2Step2Coefficient18,
    t2Step2Coefficient19,
    t2Step2Coefficient20,
    t2Step2Coefficient21,
    t2Step2Coefficient22,
    t2Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1,
    rawUnitOneDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_24 (s : ℚ) :
    t2Step3Coefficient24 s =
    t2Step2Coefficient17 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient2 s
      + t2Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient1 s
    := by
  simp only [t2Step3Coefficient24,
    t2Step2Coefficient17,
    t2Step2Coefficient18,
    t2Step2Coefficient19,
    t2Step2Coefficient20,
    t2Step2Coefficient21,
    t2Step2Coefficient22,
    t2Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2,
    rawUnitOneDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_25 (s : ℚ) :
    t2Step3Coefficient25 s =
    t2Step2Coefficient18 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient3 s
      + t2Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient2 s
    := by
  simp only [t2Step3Coefficient25,
    t2Step2Coefficient18,
    t2Step2Coefficient19,
    t2Step2Coefficient20,
    t2Step2Coefficient21,
    t2Step2Coefficient22,
    t2Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3,
    rawUnitOneDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_26 (s : ℚ) :
    t2Step3Coefficient26 s =
    t2Step2Coefficient19 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient4 s
      + t2Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient3 s
    := by
  simp only [t2Step3Coefficient26,
    t2Step2Coefficient19,
    t2Step2Coefficient20,
    t2Step2Coefficient21,
    t2Step2Coefficient22,
    t2Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4,
    rawUnitOneDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_27 (s : ℚ) :
    t2Step3Coefficient27 s =
    t2Step2Coefficient20 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient5 s
      + t2Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient4 s
    := by
  simp only [t2Step3Coefficient27,
    t2Step2Coefficient20,
    t2Step2Coefficient21,
    t2Step2Coefficient22,
    t2Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5,
    rawUnitOneDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_28 (s : ℚ) :
    t2Step3Coefficient28 s =
    t2Step2Coefficient21 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient6 s
      + t2Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient5 s
    := by
  simp only [t2Step3Coefficient28,
    t2Step2Coefficient21,
    t2Step2Coefficient22,
    t2Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6,
    rawUnitOneDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_29 (s : ℚ) :
    t2Step3Coefficient29 s =
    t2Step2Coefficient22 s *
        rawUnitOneDenominatorCoefficient7 s
      + t2Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient6 s
    := by
  simp only [t2Step3Coefficient29,
    t2Step2Coefficient22,
    t2Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7,
    rawUnitOneDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t2Step3Coefficient_product_certificate_30 (s : ℚ) :
    t2Step3Coefficient30 s =
    t2Step2Coefficient23 s *
        rawUnitOneDenominatorCoefficient7 s
    := by
  simp only [t2Step3Coefficient30,
    t2Step2Coefficient23,
    rawUnitOneDenominatorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t2Step3_eq_t2Step2_mul_rawUnitOneDenominator (r s : ℚ) :
    t2Step3 r s = t2Step2 r s * rawUnitOneDenominator r s := by
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
  have h30 := t2Step3Coefficient_product_certificate_30 s
  simp only [t2Step3, t2Step2, rawUnitOneDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient1 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 34
    + 7 * s ^ 33
    - 26 * s ^ 32
    + 68 * s ^ 31
    - 139 * s ^ 30
    + 235 * s ^ 29
    - 340 * s ^ 28
    + 430 * s ^ 27
    - 482 * s ^ 26
    + 482 * s ^ 25
    - 430 * s ^ 24
    + 340 * s ^ 23
    - 235 * s ^ 22
    + 139 * s ^ 21
    - 68 * s ^ 20
    + 26 * s ^ 19
    - 7 * s ^ 18
    + s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient3 (s : ℚ) : ℚ :=
  4 * s ^ 36
    - 41 * s ^ 35
    + 207 * s ^ 34
    - 660 * s ^ 33
    + 1511 * s ^ 32
    - 2659 * s ^ 31
    + 3698 * s ^ 30
    - 4040 * s ^ 29
    + 3187 * s ^ 28
    - 994 * s ^ 27
    - 2233 * s ^ 26
    + 5860 * s ^ 25
    - 9100 * s ^ 24
    + 11209 * s ^ 23
    - 11693 * s ^ 22
    + 10502 * s ^ 21
    - 8113 * s ^ 20
    + 5329 * s ^ 19
    - 2918 * s ^ 18
    + 1296 * s ^ 17
    - 449 * s ^ 16
    + 116 * s ^ 15
    - 21 * s ^ 14
    + 2 * s ^ 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient4 (s : ℚ) : ℚ :=
  -6 * s ^ 38
    + 82 * s ^ 37
    - 532 * s ^ 36
    + 2077 * s ^ 35
    - 5288 * s ^ 34
    + 8607 * s ^ 33
    - 6455 * s ^ 32
    - 9993 * s ^ 31
    + 48526 * s ^ 30
    - 110354 * s ^ 29
    + 187881 * s ^ 28
    - 267100 * s ^ 27
    + 332678 * s ^ 26
    - 371943 * s ^ 25
    + 375659 * s ^ 24
    - 339328 * s ^ 23
    + 266517 * s ^ 22
    - 171780 * s ^ 21
    + 78095 * s ^ 20
    - 7225 * s ^ 19
    - 30102 * s ^ 18
    + 37696 * s ^ 17
    - 28663 * s ^ 16
    + 16050 * s ^ 15
    - 6938 * s ^ 14
    + 2343 * s ^ 13
    - 605 * s ^ 12
    + 115 * s ^ 11
    - 15 * s ^ 10
    + s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient5 (s : ℚ) : ℚ :=
  4 * s ^ 40
    - 70 * s ^ 39
    + 558 * s ^ 38
    - 2532 * s ^ 37
    + 6465 * s ^ 36
    - 4324 * s ^ 35
    - 35948 * s ^ 34
    + 177221 * s ^ 33
    - 485692 * s ^ 32
    + 975492 * s ^ 31
    - 1569030 * s ^ 30
    + 2115607 * s ^ 29
    - 2464209 * s ^ 28
    + 2525512 * s ^ 27
    - 2273633 * s ^ 26
    + 1695521 * s ^ 25
    - 763966 * s ^ 24
    - 494597 * s ^ 23
    + 1898843 * s ^ 22
    - 3100583 * s ^ 21
    + 3730576 * s ^ 20
    - 3615496 * s ^ 19
    + 2885723 * s ^ 18
    - 1893957 * s ^ 17
    + 1003605 * s ^ 16
    - 410660 * s ^ 15
    + 115003 * s ^ 14
    - 10187 * s ^ 13
    - 10325 * s ^ 12
    + 7235 * s ^ 11
    - 2767 * s ^ 10
    + 730 * s ^ 9
    - 134 * s ^ 8
    + 16 * s ^ 7
    - s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 42
    + 23 * s ^ 41
    - 216 * s ^ 40
    + 964 * s ^ 39
    - 553 * s ^ 38
    - 19577 * s ^ 37
    + 135922 * s ^ 36
    - 528010 * s ^ 35
    + 1417721 * s ^ 34
    - 2793615 * s ^ 33
    + 4063094 * s ^ 32
    - 4049405 * s ^ 31
    + 1538285 * s ^ 30
    + 3975628 * s ^ 29
    - 12043208 * s ^ 28
    + 21895558 * s ^ 27
    - 33397038 * s ^ 26
    + 47251291 * s ^ 25
    - 63767601 * s ^ 24
    + 80954728 * s ^ 23
    - 93985799 * s ^ 22
    + 97183924 * s ^ 21
    - 87552347 * s ^ 20
    + 67160064 * s ^ 19
    - 42361392 * s ^ 18
    + 20398000 * s ^ 17
    - 5770756 * s ^ 16
    - 1142868 * s ^ 15
    + 2796360 * s ^ 14
    - 2152101 * s ^ 13
    + 1134793 * s ^ 12
    - 455180 * s ^ 11
    + 142140 * s ^ 10
    - 34221 * s ^ 9
    + 6071 * s ^ 8
    - 723 * s ^ 7
    + 45 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 43
    + 7 * s ^ 42
    + 146 * s ^ 41
    - 2985 * s ^ 40
    + 26475 * s ^ 39
    - 146542 * s ^ 38
    + 553992 * s ^ 37
    - 1438938 * s ^ 36
    + 2289427 * s ^ 35
    - 498635 * s ^ 34
    - 9522326 * s ^ 33
    + 34641329 * s ^ 32
    - 78649325 * s ^ 31
    + 139105216 * s ^ 30
    - 209886682 * s ^ 29
    + 289409207 * s ^ 28
    - 387624068 * s ^ 27
    + 522157712 * s ^ 26
    - 700688213 * s ^ 25
    + 899186131 * s ^ 24
    - 1055985691 * s ^ 23
    + 1095449783 * s ^ 22
    - 971403961 * s ^ 21
    + 701482849 * s ^ 20
    - 365219570 * s ^ 19
    + 64407537 * s ^ 18
    + 127861682 * s ^ 17
    - 196556885 * s ^ 16
    + 176474962 * s ^ 15
    - 119588654 * s ^ 14
    + 65122839 * s ^ 13
    - 29052270 * s ^ 12
    + 10618342 * s ^ 11
    - 3142347 * s ^ 10
    + 733175 * s ^ 9
    - 127838 * s ^ 8
    + 15025 * s ^ 7
    - 901 * s ^ 6
    - 4 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient8 (s : ℚ) : ℚ :=
  2 * s ^ 44
    - 65 * s ^ 43
    + 952 * s ^ 42
    - 8207 * s ^ 41
    + 44923 * s ^ 40
    - 147595 * s ^ 39
    + 139064 * s ^ 38
    + 1439169 * s ^ 37
    - 9929017 * s ^ 36
    + 37530915 * s ^ 35
    - 101580508 * s ^ 34
    + 213025631 * s ^ 33
    - 361590763 * s ^ 32
    + 519450236 * s ^ 31
    - 679510162 * s ^ 30
    + 909812905 * s ^ 29
    - 1371404280 * s ^ 28
    + 2247377519 * s ^ 27
    - 3583250049 * s ^ 26
    + 5123478708 * s ^ 25
    - 6283679148 * s ^ 24
    + 6358977712 * s ^ 23
    - 4907778351 * s ^ 22
    + 2081022466 * s ^ 21
    + 1345842268 * s ^ 20
    - 4307402124 * s ^ 19
    + 5962215642 * s ^ 18
    - 6068756690 * s ^ 17
    + 5003638882 * s ^ 16
    - 3451474360 * s ^ 15
    + 2015862392 * s ^ 14
    - 999546392 * s ^ 13
    + 418977553 * s ^ 12
    - 146822704 * s ^ 11
    + 42212634 * s ^ 10
    - 9639823 * s ^ 9
    + 1648233 * s ^ 8
    - 187954 * s ^ 7
    + 10198 * s ^ 6
    + 189 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient9 (s : ℚ) : ℚ :=
  2 * s ^ 45
    - 43 * s ^ 44
    + 324 * s ^ 43
    + 470 * s ^ 42
    - 31909 * s ^ 41
    + 338040 * s ^ 40
    - 2168874 * s ^ 39
    + 9878362 * s ^ 38
    - 33666337 * s ^ 37
    + 87140089 * s ^ 36
    - 168748680 * s ^ 35
    + 228010309 * s ^ 34
    - 158572821 * s ^ 33
    - 107645004 * s ^ 32
    + 389587680 * s ^ 31
    - 70244682 * s ^ 30
    - 1811070600 * s ^ 29
    + 6009984998 * s ^ 28
    - 12172693157 * s ^ 27
    + 18052687357 * s ^ 26
    - 19563496220 * s ^ 25
    + 12175238821 * s ^ 24
    + 6620986981 * s ^ 23
    - 35067454377 * s ^ 22
    + 66724704536 * s ^ 21
    - 92629676313 * s ^ 20
    + 105167811544 * s ^ 19
    - 101518976323 * s ^ 18
    + 84650088764 * s ^ 17
    - 61347547613 * s ^ 16
    + 38683689686 * s ^ 15
    - 21176172429 * s ^ 14
    + 10010484961 * s ^ 13
    - 4048648172 * s ^ 12
    + 1380516314 * s ^ 11
    - 388120274 * s ^ 10
    + 86705415 * s ^ 9
    - 14398007 * s ^ 8
    + 1546338 * s ^ 7
    - 65129 * s ^ 6
    - 4059 * s ^ 5
    + 32 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 46
    + 45 * s ^ 45
    - 918 * s ^ 44
    + 11342 * s ^ 43
    - 95225 * s ^ 42
    + 572417 * s ^ 41
    - 2494272 * s ^ 40
    + 7564663 * s ^ 39
    - 12734409 * s ^ 38
    - 11706266 * s ^ 37
    + 166309570 * s ^ 36
    - 647574133 * s ^ 35
    + 1627555976 * s ^ 34
    - 2858780901 * s ^ 33
    + 3133693778 * s ^ 32
    - 185808956 * s ^ 31
    - 8179390501 * s ^ 30
    + 21408761340 * s ^ 29
    - 32708890423 * s ^ 28
    + 26656137710 * s ^ 27
    + 19376632560 * s ^ 26
    - 127890984625 * s ^ 25
    + 308889159393 * s ^ 24
    - 547787368300 * s ^ 23
    + 801711457373 * s ^ 22
    - 1009720306081 * s ^ 21
    + 1114981355704 * s ^ 20
    - 1088788528468 * s ^ 19
    + 943252748504 * s ^ 18
    - 724989811110 * s ^ 17
    + 493349929176 * s ^ 16
    - 296124694447 * s ^ 15
    + 155923189499 * s ^ 14
    - 71456212315 * s ^ 13
    + 28172941247 * s ^ 12
    - 9395451115 * s ^ 11
    + 2583355559 * s ^ 10
    - 561096479 * s ^ 9
    + 88835581 * s ^ 8
    - 8466132 * s ^ 7
    + 132105 * s ^ 6
    + 51895 * s ^ 5
    - 356 * s ^ 4
    - 4 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 47
    + 33 * s ^ 46
    - 498 * s ^ 45
    + 4280 * s ^ 44
    - 19275 * s ^ 43
    - 12375 * s ^ 42
    + 919752 * s ^ 41
    - 8019735 * s ^ 40
    + 43595901 * s ^ 39
    - 171765796 * s ^ 38
    + 507944646 * s ^ 37
    - 1102225321 * s ^ 36
    + 1521274590 * s ^ 35
    - 157223809 * s ^ 34
    - 5997054566 * s ^ 33
    + 19473038185 * s ^ 32
    - 36685305279 * s ^ 31
    + 38458050983 * s ^ 30
    + 20554563415 * s ^ 29
    - 217727098693 * s ^ 28
    + 655114829448 * s ^ 27
    - 1430785842496 * s ^ 26
    + 2588723203443 * s ^ 25
    - 4063378684554 * s ^ 24
    + 5650328486809 * s ^ 23
    - 7033952824139 * s ^ 22
    + 7879013676270 * s ^ 21
    - 7955579348888 * s ^ 20
    + 7238014591968 * s ^ 19
    - 5921744503772 * s ^ 18
    + 4342984238502 * s ^ 17
    - 2843328709361 * s ^ 16
    + 1652983920031 * s ^ 15
    - 847466566205 * s ^ 14
    + 379579039587 * s ^ 13
    - 146553613592 * s ^ 12
    + 47836717479 * s ^ 11
    - 12810068456 * s ^ 10
    + 2670399309 * s ^ 9
    - 388908001 * s ^ 8
    + 28097301 * s ^ 7
    + 1638448 * s ^ 6
    - 436020 * s ^ 5
    + 320 * s ^ 4
    + 132 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient12 (s : ℚ) : ℚ :=
  -3 * s ^ 47
    + 126 * s ^ 46
    - 2490 * s ^ 45
    + 30793 * s ^ 44
    - 265773 * s ^ 43
    + 1681048 * s ^ 42
    - 7886469 * s ^ 41
    + 26502460 * s ^ 40
    - 53053203 * s ^ 39
    - 22551961 * s ^ 38
    + 689988578 * s ^ 37
    - 3241910245 * s ^ 36
    + 9650610953 * s ^ 35
    - 19851371936 * s ^ 34
    + 23104792847 * s ^ 33
    + 19473464641 * s ^ 32
    - 201026180470 * s ^ 31
    + 698260997515 * s ^ 30
    - 1791108553904 * s ^ 29
    + 3849679514868 * s ^ 28
    - 7258316889674 * s ^ 27
    + 12259299080104 * s ^ 26
    - 18744019731762 * s ^ 25
    + 26081583147723 * s ^ 24
    - 33108652610669 * s ^ 23
    + 38365781864744 * s ^ 22
    - 40550745019574 * s ^ 21
    + 39019428609217 * s ^ 20
    - 34086022104074 * s ^ 19
    + 26937322839710 * s ^ 18
    - 19177873493477 * s ^ 17
    + 12239633111283 * s ^ 16
    - 6960185752937 * s ^ 15
    + 3498893809141 * s ^ 14
    - 1538137245444 * s ^ 13
    + 582240321027 * s ^ 12
    - 185477450995 * s ^ 11
    + 47903007753 * s ^ 10
    - 9342685574 * s ^ 9
    + 1151609458 * s ^ 8
    - 23596753 * s ^ 7
    - 19161010 * s ^ 6
    + 2501841 * s ^ 5
    + 34459 * s ^ 4
    - 1886 * s ^ 3
    - 6 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient13 (s : ℚ) : ℚ :=
  -s ^ 48
    + 34 * s ^ 47
    - 516 * s ^ 46
    + 4199 * s ^ 45
    - 12479 * s ^ 44
    - 131372 * s ^ 43
    + 2179742 * s ^ 42
    - 17464078 * s ^ 41
    + 96500711 * s ^ 40
    - 395556877 * s ^ 39
    + 1193878442 * s ^ 38
    - 2318324731 * s ^ 37
    + 260597123 * s ^ 36
    + 20650486930 * s ^ 35
    - 108484347044 * s ^ 34
    + 381096347535 * s ^ 33
    - 1084257326213 * s ^ 32
    + 2668239224971 * s ^ 31
    - 5865244797135 * s ^ 30
    + 11717698507034 * s ^ 29
    - 21467837211911 * s ^ 28
    + 36215751700494 * s ^ 27
    - 56337057480869 * s ^ 26
    + 80820640604805 * s ^ 25
    - 106856578208567 * s ^ 24
    + 130045021455176 * s ^ 23
    - 145412294292014 * s ^ 22
    + 149025458612619 * s ^ 21
    - 139561826402578 * s ^ 20
    + 119015833655874 * s ^ 19
    - 92058335743368 * s ^ 18
    + 64297488957461 * s ^ 17
    - 40335318367905 * s ^ 16
    + 22574625666557 * s ^ 15
    - 11171088353128 * s ^ 14
    + 4826465870701 * s ^ 13
    - 1787356552762 * s ^ 12
    + 551275949355 * s ^ 11
    - 134567161989 * s ^ 10
    + 23187192152 * s ^ 9
    - 1797429956 * s ^ 8
    - 312677840 * s ^ 7
    + 110596000 * s ^ 6
    - 9711925 * s ^ 5
    - 447890 * s ^ 4
    + 15054 * s ^ 3
    + 179 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient14 (s : ℚ) : ℚ :=
  -2 * s ^ 48
    + 86 * s ^ 47
    - 1739 * s ^ 46
    + 21801 * s ^ 45
    - 186138 * s ^ 44
    + 1093850 * s ^ 43
    - 3884989 * s ^ 42
    + 5154 * s ^ 41
    + 113489661 * s ^ 40
    - 968354623 * s ^ 39
    + 5392333104 * s ^ 38
    - 23522657360 * s ^ 37
    + 85850376173 * s ^ 36
    - 271905599982 * s ^ 35
    + 766596679271 * s ^ 34
    - 1961257094366 * s ^ 33
    + 4616746454055 * s ^ 32
    - 10083935814204 * s ^ 31
    + 20509563466770 * s ^ 30
    - 38848793726150 * s ^ 29
    + 68430512520600 * s ^ 28
    - 111888885596181 * s ^ 27
    + 169547448936128 * s ^ 26
    - 237758451802536 * s ^ 25
    + 308069580850701 * s ^ 24
    - 368134964336168 * s ^ 23
    + 404752597684852 * s ^ 22
    - 408303952113044 * s ^ 21
    + 376715557352190 * s ^ 20
    - 316778695980662 * s ^ 19
    + 241827866512017 * s ^ 18
    - 166829568650860 * s ^ 17
    + 103412516911469 * s ^ 16
    - 57162614745610 * s ^ 15
    + 27880537995758 * s ^ 14
    - 11816269652333 * s ^ 13
    + 4250741806025 * s ^ 12
    - 1247344244976 * s ^ 11
    + 274922397286 * s ^ 10
    - 35081614610 * s ^ 9
    - 2019405772 * s ^ 8
    + 2082960075 * s ^ 7
    - 420151007 * s ^ 6
    + 22675020 * s ^ 5
    + 3163078 * s ^ 4
    - 69405 * s ^ 3
    - 2403 * s ^ 2
    - 4 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient15 (s : ℚ) : ℚ :=
  -3 * s ^ 48
    + 155 * s ^ 47
    - 3830 * s ^ 46
    + 60588 * s ^ 45
    - 691846 * s ^ 44
    + 6090795 * s ^ 43
    - 43112336 * s ^ 42
    + 252753807 * s ^ 41
    - 1256113463 * s ^ 40
    + 5398093038 * s ^ 39
    - 20436505044 * s ^ 38
    + 69406635723 * s ^ 37
    - 215131493017 * s ^ 36
    + 617515150175 * s ^ 35
    - 1657482554839 * s ^ 34
    + 4175541492907 * s ^ 33
    - 9859520842530 * s ^ 32
    + 21736695907510 * s ^ 31
    - 44566002197876 * s ^ 30
    + 84742087125866 * s ^ 29
    - 149241212126089 * s ^ 28
    + 243301753539968 * s ^ 27
    - 367036320873822 * s ^ 26
    + 511996522627063 * s ^ 25
    - 659554081793446 * s ^ 24
    + 783129920566198 * s ^ 23
    - 855044610456452 * s ^ 22
    + 856138670070866 * s ^ 21
    - 783816113281892 * s ^ 20
    + 653989136917175 * s ^ 19
    - 495384915413528 * s ^ 18
    + 339027284440741 * s ^ 17
    - 208276044348765 * s ^ 16
    + 113821339370390 * s ^ 15
    - 54610560390962 * s ^ 14
    + 22548222267977 * s ^ 13
    - 7750576715492 * s ^ 12
    + 2077547513812 * s ^ 11
    - 361280623324 * s ^ 10
    + 2239760794 * s ^ 9
    + 22488416731 * s ^ 8
    - 7513817589 * s ^ 7
    + 1097605710 * s ^ 6
    - 8222636 * s ^ 5
    - 14982980 * s ^ 4
    + 134381 * s ^ 3
    + 19287 * s ^ 2
    + 104 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient16 (s : ℚ) : ℚ :=
  -s ^ 49
    + 46 * s ^ 48
    - 1037 * s ^ 47
    + 15224 * s ^ 46
    - 163459 * s ^ 45
    + 1369358 * s ^ 44
    - 9348666 * s ^ 43
    + 53827635 * s ^ 42
    - 269592437 * s ^ 41
    + 1209790611 * s ^ 40
    - 4995045120 * s ^ 39
    + 19332548253 * s ^ 38
    - 70602970073 * s ^ 37
    + 242220149642 * s ^ 36
    - 773068206246 * s ^ 35
    + 2274441276783 * s ^ 34
    - 6134446271411 * s ^ 33
    + 15142827461699 * s ^ 32
    - 34253186264797 * s ^ 31
    + 71193452382759 * s ^ 30
    - 136370573847602 * s ^ 29
    + 241300270756926 * s ^ 28
    - 394885912557375 * s ^ 27
    + 597657035082150 * s ^ 26
    - 835700720850465 * s ^ 25
    + 1077773055176895 * s ^ 24
    - 1279332147262222 * s ^ 23
    + 1394592916972380 * s ^ 22
    - 1392820994610132 * s ^ 21
    + 1271161772937431 * s ^ 20
    - 1056868358353646 * s ^ 19
    + 797279098210361 * s ^ 18
    - 542694973569545 * s ^ 17
    + 330674113451957 * s ^ 16
    - 178267893764705 * s ^ 15
    + 83532232819361 * s ^ 14
    - 33039883401213 * s ^ 13
    + 10427381355695 * s ^ 12
    - 2261402133610 * s ^ 11
    + 109754004442 * s ^ 10
    + 159221915353 * s ^ 9
    - 77368048320 * s ^ 8
    + 18365629060 * s ^ 7
    - 1827277700 * s ^ 6
    - 174654292 * s ^ 5
    + 50666969 * s ^ 4
    + 497496 * s ^ 3
    - 103164 * s ^ 2
    - 1247 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient17 (s : ℚ) : ℚ :=
  2 * s ^ 48
    - 78 * s ^ 47
    + 1412 * s ^ 46
    - 14988 * s ^ 45
    + 89444 * s ^ 44
    - 41727 * s ^ 43
    - 5444889 * s ^ 42
    + 69709529 * s ^ 41
    - 560527962 * s ^ 40
    + 3454187121 * s ^ 39
    - 17463910860 * s ^ 38
    + 75029958186 * s ^ 37
    - 280178097067 * s ^ 36
    + 924744733099 * s ^ 35
    - 2734617627803 * s ^ 34
    + 7328063500165 * s ^ 33
    - 17960135830165 * s ^ 32
    + 40535339876677 * s ^ 31
    - 84607581821319 * s ^ 30
    + 163609243987470 * s ^ 29
    - 293057335520341 * s ^ 28
    + 485557752411032 * s ^ 27
    - 742760035778489 * s ^ 26
    + 1046978085406953 * s ^ 25
    - 1357534433749048 * s ^ 24
    + 1616642647026624 * s ^ 23
    - 1765522433078796 * s ^ 22
    + 1765161818840681 * s ^ 21
    - 1611986205069706 * s ^ 20
    + 1340225403549819 * s ^ 19
    - 1009522311950786 * s ^ 18
    + 683948443313897 * s ^ 17
    - 412286261363668 * s ^ 16
    + 217493534136941 * s ^ 15
    - 97703197051404 * s ^ 14
    + 35466108029315 * s ^ 13
    - 9068506456362 * s ^ 12
    + 653722982510 * s ^ 11
    + 815137637615 * s ^ 10
    - 518772010848 * s ^ 9
    + 170711339340 * s ^ 8
    - 30964589226 * s ^ 7
    + 987183052 * s ^ 6
    + 830112095 * s ^ 5
    - 123298701 * s ^ 4
    - 5171932 * s ^ 3
    + 383951 * s ^ 2
    + 9213 * s
    + 22

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient18 (s : ℚ) : ℚ :=
  2 * s ^ 48
    - 99 * s ^ 47
    + 2398 * s ^ 46
    - 37888 * s ^ 45
    + 439039 * s ^ 44
    - 3978021 * s ^ 43
    + 29353795 * s ^ 42
    - 181536641 * s ^ 41
    + 962046305 * s ^ 40
    - 4450823384 * s ^ 39
    + 18278935175 * s ^ 38
    - 67676119820 * s ^ 37
    + 229042410351 * s ^ 36
    - 716537169154 * s ^ 35
    + 2086896274715 * s ^ 34
    - 5672674239226 * s ^ 33
    + 14370338328299 * s ^ 32
    - 33799071856020 * s ^ 31
    + 73491516675889 * s ^ 30
    - 147196938105664 * s ^ 29
    + 270918572523785 * s ^ 28
    - 457622295854964 * s ^ 27
    + 709127807789647 * s ^ 26
    - 1008135134538510 * s ^ 25
    + 1315128326370709 * s ^ 24
    - 1574188093345512 * s ^ 23
    + 1727950332768577 * s ^ 22
    - 1736791555229378 * s ^ 21
    + 1594015801167603 * s ^ 20
    - 1329740626914252 * s ^ 19
    + 1001132191453886 * s ^ 18
    - 673031997650373 * s ^ 17
    + 397462477061559 * s ^ 16
    - 200670804038679 * s ^ 15
    + 82137805426692 * s ^ 14
    - 23605670199837 * s ^ 13
    + 1583183432692 * s ^ 12
    + 3227428063957 * s ^ 11
    - 2418639869008 * s ^ 10
    + 1010287539187 * s ^ 9
    - 262672078060 * s ^ 8
    + 31292755774 * s ^ 7
    + 4485409955 * s ^ 6
    - 2258311803 * s ^ 5
    + 203885658 * s ^ 4
    + 22812258 * s ^ 3
    - 984281 * s ^ 2
    - 47103 * s
    - 230

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient19 (s : ℚ) : ℚ :=
  -2 * s ^ 47
    + 85 * s ^ 46
    - 1735 * s ^ 45
    + 22284 * s ^ 44
    - 196031 * s ^ 43
    + 1164938 * s ^ 42
    - 3574451 * s ^ 41
    - 12951883 * s ^ 40
    + 278248525 * s ^ 39
    - 2362250727 * s ^ 38
    + 14410950039 * s ^ 37
    - 70800679978 * s ^ 36
    + 293210100173 * s ^ 35
    - 1048907338552 * s ^ 34
    + 3292035396437 * s ^ 33
    - 9166055060917 * s ^ 32
    + 22836349847631 * s ^ 31
    - 51268431480639 * s ^ 30
    + 104330927315261 * s ^ 29
    - 193402378688058 * s ^ 28
    + 327903029242061 * s ^ 27
    - 510040819043204 * s ^ 26
    + 729369834682431 * s ^ 25
    - 959864746995288 * s ^ 24
    + 1162252397710783 * s ^ 23
    - 1292772969458730 * s ^ 22
    + 1316645069872057 * s ^ 21
    - 1221454111774746 * s ^ 20
    + 1024214710837856 * s ^ 19
    - 767540062525647 * s ^ 18
    + 505280899718485 * s ^ 17
    - 283834594322167 * s ^ 16
    + 128179811505670 * s ^ 15
    - 38939757563431 * s ^ 14
    - 63623517200 * s ^ 13
    + 10039248363175 * s ^ 12
    - 8125001597152 * s ^ 11
    + 4052253391295 * s ^ 10
    - 1363691690844 * s ^ 9
    + 266542236359 * s ^ 8
    + 108425023 * s ^ 7
    - 16776273350 * s ^ 6
    + 4218317466 * s ^ 5
    - 164952411 * s ^ 4
    - 67114041 * s ^ 3
    + 1524778 * s ^ 2
    + 176854 * s
    + 1518

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient20 (s : ℚ) : ℚ :=
  -s ^ 47
    + 52 * s ^ 46
    - 1330 * s ^ 45
    + 22318 * s ^ 44
    - 276241 * s ^ 43
    + 2686723 * s ^ 42
    - 21353960 * s ^ 41
    + 142404216 * s ^ 40
    - 812026863 * s ^ 39
    + 4016219174 * s ^ 38
    - 17425142708 * s ^ 37
    + 66948789632 * s ^ 36
    - 229668389511 * s ^ 35
    + 708790717258 * s ^ 34
    - 1981696973640 * s ^ 33
    + 5052285171981 * s ^ 32
    - 11814406562952 * s ^ 31
    + 25464908957589 * s ^ 30
    - 50777963861119 * s ^ 29
    + 93883908233384 * s ^ 28
    - 161080678990119 * s ^ 27
    + 256336133714118 * s ^ 26
    - 377711063122565 * s ^ 25
    + 513922495356205 * s ^ 24
    - 643220002345546 * s ^ 23
    + 736805064351925 * s ^ 22
    - 767391447124952 * s ^ 21
    + 720347648301507 * s ^ 20
    - 601961564971209 * s ^ 19
    + 439361766324993 * s ^ 18
    - 270705477533167 * s ^ 17
    + 130273096954392 * s ^ 16
    - 36592056559664 * s ^ 15
    - 10465524811367 * s ^ 14
    + 23836057461240 * s ^ 13
    - 19911495118960 * s ^ 12
    + 11367737703089 * s ^ 11
    - 4665545302934 * s ^ 10
    + 1246863774595 * s ^ 9
    - 109897436430 * s ^ 8
    - 68484169939 * s ^ 7
    + 32839599204 * s ^ 6
    - 5414738098 * s ^ 5
    - 203203468 * s ^ 4
    + 143975016 * s ^ 3
    - 191435 * s ^ 2
    - 503348 * s
    - 7085

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient21 (s : ℚ) : ℚ :=
  2 * s ^ 45
    - 88 * s ^ 44
    + 1913 * s ^ 43
    - 27541 * s ^ 42
    + 297180 * s ^ 41
    - 2579056 * s ^ 40
    + 18838928 * s ^ 39
    - 119343510 * s ^ 38
    + 667880354 * s ^ 37
    - 3334660717 * s ^ 36
    + 14917976734 * s ^ 35
    - 59876453624 * s ^ 34
    + 215707915531 * s ^ 33
    - 697900944513 * s ^ 32
    + 2030269117841 * s ^ 31
    - 5320083982013 * s ^ 30
    + 12584093718980 * s ^ 29
    - 26928659384817 * s ^ 28
    + 52227959125282 * s ^ 27
    - 91915175656695 * s ^ 26
    + 146796646387577 * s ^ 25
    - 212501423180516 * s ^ 24
    + 278030752834951 * s ^ 23
    - 327177245526469 * s ^ 22
    + 343578668400557 * s ^ 21
    - 317883585327407 * s ^ 20
    + 253316970536591 * s ^ 19
    - 165853376893924 * s ^ 18
    + 78046542928694 * s ^ 17
    - 9667153295040 * s ^ 16
    - 29551592655263 * s ^ 15
    + 41426481913570 * s ^ 14
    - 35413479595984 * s ^ 13
    + 22564564437521 * s ^ 12
    - 10870295791256 * s ^ 11
    + 3650913085834 * s ^ 10
    - 575845548822 * s ^ 9
    - 174042797234 * s ^ 8
    + 146132536030 * s ^ 7
    - 42860468003 * s ^ 6
    + 3971651974 * s ^ 5
    + 1008885781 * s ^ 4
    - 228916651 * s ^ 3
    - 6567733 * s ^ 2
    + 1100233 * s
    + 24818

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient22 (s : ℚ) : ℚ :=
  2 * s ^ 44
    - 104 * s ^ 43
    + 2618 * s ^ 42
    - 42668 * s ^ 41
    + 507330 * s ^ 40
    - 4697514 * s ^ 39
    + 35287491 * s ^ 38
    - 221159612 * s ^ 37
    + 1180194543 * s ^ 36
    - 5446250995 * s ^ 35
    + 22003236856 * s ^ 34
    - 78615138611 * s ^ 33
    + 250504093064 * s ^ 32
    - 716877896400 * s ^ 31
    + 1852726283999 * s ^ 30
    - 4341714302189 * s ^ 29
    + 9247443015280 * s ^ 28
    - 17913075872158 * s ^ 27
    + 31524396363624 * s ^ 26
    - 50265687245118 * s ^ 25
    + 72292240585858 * s ^ 24
    - 93138262054301 * s ^ 23
    + 106337839901793 * s ^ 22
    - 105594982951887 * s ^ 21
    + 87825143100419 * s ^ 20
    - 55440614275318 * s ^ 19
    + 16245628629234 * s ^ 18
    + 19429059629769 * s ^ 17
    - 42957185036685 * s ^ 16
    + 50729721447599 * s ^ 15
    - 44915086485508 * s ^ 14
    + 31577568593612 * s ^ 13
    - 17427597262003 * s ^ 12
    + 6990790670182 * s ^ 11
    - 1497068831919 * s ^ 10
    - 317245550821 * s ^ 9
    + 430545655274 * s ^ 8
    - 182804729672 * s ^ 7
    + 36610190007 * s ^ 6
    + 776245146 * s ^ 5
    - 2003808041 * s ^ 4
    + 260060225 * s ^ 3
    + 21801701 * s ^ 2
    - 1836541 * s
    - 67561

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient23 (s : ℚ) : ℚ :=
  -4 * s ^ 42
    + 186 * s ^ 41
    - 4233 * s ^ 40
    + 63009 * s ^ 39
    - 691041 * s ^ 38
    + 5958663 * s ^ 37
    - 42055304 * s ^ 36
    + 249512364 * s ^ 35
    - 1267258108 * s ^ 34
    + 5579557938 * s ^ 33
    - 21482050067 * s ^ 32
    + 72761737067 * s ^ 31
    - 217706726148 * s ^ 30
    + 577001037968 * s ^ 29
    - 1356838479500 * s ^ 28
    + 2832328553240 * s ^ 27
    - 5242931473548 * s ^ 26
    + 8575686685366 * s ^ 25
    - 12291804731105 * s ^ 24
    + 15159621777187 * s ^ 23
    - 15409462951497 * s ^ 22
    + 11332715268947 * s ^ 21
    - 2190839184580 * s ^ 20
    - 10997491829246 * s ^ 19
    + 25328381585687 * s ^ 18
    - 36832270399383 * s ^ 17
    + 42023947367423 * s ^ 16
    - 39491867913972 * s ^ 15
    + 30653694313682 * s ^ 14
    - 19108097380989 * s ^ 13
    + 8821948457851 * s ^ 12
    - 2232008203533 * s ^ 11
    - 530408305868 * s ^ 10
    + 909336232264 * s ^ 9
    - 498276983502 * s ^ 8
    + 148095681703 * s ^ 7
    - 14161195098 * s ^ 6
    - 6766709509 * s ^ 5
    + 2588959861 * s ^ 4
    - 177255555 * s ^ 3
    - 43369681 * s ^ 2
    + 2255085 * s
    + 145980

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient24 (s : ℚ) : ℚ :=
  -s ^ 41
    + 52 * s ^ 40
    - 1281 * s ^ 39
    + 20052 * s ^ 38
    - 225166 * s ^ 37
    + 1938447 * s ^ 36
    - 13340278 * s ^ 35
    + 75521141 * s ^ 34
    - 359105719 * s ^ 33
    + 1457298941 * s ^ 32
    - 5111085556 * s ^ 31
    + 15647214051 * s ^ 30
    - 42119883820 * s ^ 29
    + 100069124810 * s ^ 28
    - 209459149001 * s ^ 27
    + 381829675713 * s ^ 26
    - 587302591136 * s ^ 25
    + 697576195189 * s ^ 24
    - 423439381985 * s ^ 23
    - 697210473107 * s ^ 22
    + 3181988922426 * s ^ 21
    - 7318617512347 * s ^ 20
    + 12794179558521 * s ^ 19
    - 18466595483749 * s ^ 18
    + 22554115633605 * s ^ 17
    - 23352604280064 * s ^ 16
    + 20203997579612 * s ^ 15
    - 14075868276535 * s ^ 14
    + 7194435380027 * s ^ 13
    - 1833239957551 * s ^ 12
    - 909465953145 * s ^ 11
    + 1435475146356 * s ^ 10
    - 927004703633 * s ^ 9
    + 355171086373 * s ^ 8
    - 64445669169 * s ^ 7
    - 11206038662 * s ^ 6
    + 10263506504 * s ^ 5
    - 2270177232 * s ^ 4
    - 10039634 * s ^ 3
    + 61558448 * s ^ 2
    - 1778083 * s
    - 253414

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient25 (s : ℚ) : ℚ :=
  2 * s ^ 39
    - 94 * s ^ 38
    + 2137 * s ^ 37
    - 31383 * s ^ 36
    + 334963 * s ^ 35
    - 2768340 * s ^ 34
    + 18411481 * s ^ 33
    - 101020463 * s ^ 32
    + 464806575 * s ^ 31
    - 1811849865 * s ^ 30
    + 6014258080 * s ^ 29
    - 16994950839 * s ^ 28
    + 40555935339 * s ^ 27
    - 79873181234 * s ^ 26
    + 121828081385 * s ^ 25
    - 112017432379 * s ^ 24
    - 72927868123 * s ^ 23
    + 629997042551 * s ^ 22
    - 1774918004115 * s ^ 21
    + 3607252725437 * s ^ 20
    - 5932087684531 * s ^ 19
    + 8156663744501 * s ^ 18
    - 9417098014172 * s ^ 17
    + 8987145963118 * s ^ 16
    - 6776338657719 * s ^ 15
    + 3534684446922 * s ^ 14
    - 504346196637 * s ^ 13
    - 1308706109638 * s ^ 12
    + 1697332718006 * s ^ 11
    - 1200782107065 * s ^ 10
    + 544222406791 * s ^ 9
    - 133220577705 * s ^ 8
    - 11129769198 * s ^ 7
    + 24011341545 * s ^ 6
    - 9156205692 * s ^ 5
    + 1181412580 * s ^ 4
    + 202704866 * s ^ 3
    - 64518781 * s ^ 2
    + 256338 * s
    + 355356

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient26 (s : ℚ) : ℚ :=
  -10 * s ^ 36
    + 428 * s ^ 35
    - 8844 * s ^ 34
    + 117922 * s ^ 33
    - 1143568 * s ^ 32
    + 8616375 * s ^ 31
    - 52605179 * s ^ 30
    + 267943960 * s ^ 29
    - 1163299796 * s ^ 28
    + 4375773545 * s ^ 27
    - 14438400667 * s ^ 26
    + 42168020904 * s ^ 25
    - 109620878384 * s ^ 24
    + 254224574435 * s ^ 23
    - 525337320531 * s ^ 22
    + 962850258373 * s ^ 21
    - 1552439005137 * s ^ 20
    + 2173828805731 * s ^ 19
    - 2589312193885 * s ^ 18
    + 2524899342461 * s ^ 17
    - 1839402312769 * s ^ 16
    + 678363379906 * s ^ 15
    + 534434778262 * s ^ 14
    - 1320517973656 * s ^ 13
    + 1447769158698 * s ^ 12
    - 1062302528232 * s ^ 11
    + 530307699877 * s ^ 10
    - 146630605427 * s ^ 9
    - 16428898050 * s ^ 8
    + 39959207248 * s ^ 7
    - 20493820866 * s ^ 6
    + 4952895649 * s ^ 5
    - 32671523 * s ^ 4
    - 287016620 * s ^ 3
    + 48850697 * s ^ 2
    + 1661046 * s
    - 402373

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient27 (s : ℚ) : ℚ :=
  -2 * s ^ 35
    + 98 * s ^ 34
    - 2282 * s ^ 33
    + 33815 * s ^ 32
    - 359813 * s ^ 31
    + 2937886 * s ^ 30
    - 19186082 * s ^ 29
    + 103023686 * s ^ 28
    - 463573707 * s ^ 27
    + 1770698995 * s ^ 26
    - 5789510482 * s ^ 25
    + 16276625296 * s ^ 24
    - 39376977535 * s ^ 23
    + 81675040052 * s ^ 22
    - 143766690527 * s ^ 21
    + 209904087699 * s ^ 20
    - 240624158309 * s ^ 19
    + 180743664493 * s ^ 18
    + 9565640377 * s ^ 17
    - 312238832593 * s ^ 16
    + 631171666498 * s ^ 15
    - 827806757829 * s ^ 14
    + 806359176234 * s ^ 13
    - 587061831237 * s ^ 12
    + 295566492171 * s ^ 11
    - 68343637536 * s ^ 10
    - 37569742274 * s ^ 9
    + 51094619514 * s ^ 8
    - 29424245952 * s ^ 7
    + 9613070559 * s ^ 6
    - 1026991489 * s ^ 5
    - 543970830 * s ^ 4
    + 236202265 * s ^ 3
    - 23965918 * s ^ 2
    - 2910867 * s
    + 365626

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient28 (s : ℚ) : ℚ :=
  s ^ 33
    - 40 * s ^ 32
    + 742 * s ^ 31
    - 8418 * s ^ 30
    + 64220 * s ^ 29
    - 332703 * s ^ 28
    + 1015512 * s ^ 27
    + 285986 * s ^ 26
    - 25196189 * s ^ 25
    + 181653921 * s ^ 24
    - 861007338 * s ^ 23
    + 3167313268 * s ^ 22
    - 9568714383 * s ^ 21
    + 24371476819 * s ^ 20
    - 53013712843 * s ^ 19
    + 98953274339 * s ^ 18
    - 158168841115 * s ^ 17
    + 214504105894 * s ^ 16
    - 242157793176 * s ^ 15
    + 219375609830 * s ^ 14
    - 146847174158 * s ^ 13
    + 53685310333 * s ^ 12
    + 20086919894 * s ^ 11
    - 51588720749 * s ^ 10
    + 46763247638 * s ^ 9
    - 27137233156 * s ^ 8
    + 10165501675 * s ^ 7
    - 1597404535 * s ^ 6
    - 680113594 * s ^ 5
    + 506637684 * s ^ 4
    - 122734630 * s ^ 3
    + 3922747 * s ^ 2
    + 2909712 * s
    - 263188

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient29 (s : ℚ) : ℚ :=
  -4 * s ^ 30
    + 167 * s ^ 29
    - 3325 * s ^ 28
    + 42122 * s ^ 27
    - 381993 * s ^ 26
    + 2643339 * s ^ 25
    - 14513847 * s ^ 24
    + 64844084 * s ^ 23
    - 239518294 * s ^ 22
    + 737940919 * s ^ 21
    - 1900670877 * s ^ 20
    + 4071065703 * s ^ 19
    - 7131891299 * s ^ 18
    + 9817281726 * s ^ 17
    - 9485775555 * s ^ 16
    + 3346368012 * s ^ 15
    + 8886779253 * s ^ 14
    - 23101654863 * s ^ 13
    + 32505396675 * s ^ 12
    - 32557904685 * s ^ 11
    + 24483021207 * s ^ 10
    - 13664326820 * s ^ 9
    + 5063946289 * s ^ 8
    - 498418657 * s ^ 7
    - 845113440 * s ^ 6
    + 662203292 * s ^ 5
    - 237781236 * s ^ 4
    + 33800169 * s ^ 3
    + 4471118 * s ^ 2
    - 1995996 * s
    + 146816

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient30 (s : ℚ) : ℚ :=
  6 * s ^ 27
    - 240 * s ^ 26
    + 4566 * s ^ 25
    - 55062 * s ^ 24
    + 472986 * s ^ 23
    - 3081614 * s ^ 22
    + 15820864 * s ^ 21
    - 65596690 * s ^ 20
    + 223182695 * s ^ 19
    - 629277289 * s ^ 18
    + 1477885248 * s ^ 17
    - 2894073210 * s ^ 16
    + 4712299430 * s ^ 15
    - 6335553965 * s ^ 14
    + 6945876752 * s ^ 13
    - 6071202871 * s ^ 12
    + 4029626551 * s ^ 11
    - 1736556449 * s ^ 10
    + 34078872 * s ^ 9
    + 770293524 * s ^ 8
    - 845146892 * s ^ 7
    + 554710233 * s ^ 6
    - 234298366 * s ^ 5
    + 52277425 * s ^ 4
    + 1744352 * s ^ 3
    - 4331292 * s ^ 2
    + 961672 * s
    - 61236

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient31 (s : ℚ) : ℚ :=
  -4 * s ^ 24
    + 148 * s ^ 23
    - 2584 * s ^ 22
    + 28336 * s ^ 21
    - 219037 * s ^ 20
    + 1269077 * s ^ 19
    - 5717960 * s ^ 18
    + 20506920 * s ^ 17
    - 59425114 * s ^ 16
    + 140476525 * s ^ 15
    - 272599556 * s ^ 14
    + 436476433 * s ^ 13
    - 580562605 * s ^ 12
    + 649107173 * s ^ 11
    - 621479878 * s ^ 10
    + 519228156 * s ^ 9
    - 378046702 * s ^ 8
    + 229055137 * s ^ 7
    - 103296734 * s ^ 6
    + 25939839 * s ^ 5
    + 2819862 * s ^ 4
    - 5169524 * s ^ 3
    + 1908112 * s ^ 2
    - 313996 * s
    + 17976

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient32 (s : ℚ) : ℚ :=
  s ^ 21
    - 32 * s ^ 20
    + 472 * s ^ 19
    - 4246 * s ^ 18
    + 25912 * s ^ 17
    - 112395 * s ^ 16
    + 349739 * s ^ 15
    - 751130 * s ^ 14
    + 921486 * s ^ 13
    + 223711 * s ^ 12
    - 3813893 * s ^ 11
    + 9143647 * s ^ 10
    - 12644427 * s ^ 9
    + 10562992 * s ^ 8
    - 3527650 * s ^ 7
    - 3290439 * s ^ 6
    + 5642128 * s ^ 5
    - 4090480 * s ^ 4
    + 1758408 * s ^ 3
    - 453228 * s ^ 2
    + 62736 * s
    - 3312

/-- Coefficient of the indicated power of the raw chart variable. -/
def termTwoCoefficient33 (s : ℚ) : ℚ :=
  -s ^ 17
    + 31 * s ^ 16
    - 442 * s ^ 15
    + 3845 * s ^ 14
    - 22827 * s ^ 13
    + 98017 * s ^ 12
    - 314761 * s ^ 11
    + 770941 * s ^ 10
    - 1455560 * s ^ 9
    + 2126372 * s ^ 8
    - 2398005 * s ^ 7
    + 2069858 * s ^ 6
    - 1345552 * s ^ 5
    + 641440 * s ^ 4
    - 214740 * s ^ 3
    + 46904 * s ^ 2
    - 5808 * s
    + 288

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
    termTwoCoefficient33 s * r ^ 33

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_0 (s : ℚ) :
    termTwoCoefficient0 s =
    t2Step3Coefficient0 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient0,
    t2Step3Coefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_1 (s : ℚ) :
    termTwoCoefficient1 s =
    t2Step3Coefficient0 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient1 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient1,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_2 (s : ℚ) :
    termTwoCoefficient2 s =
    t2Step3Coefficient0 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient1 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient2 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient2,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_3 (s : ℚ) :
    termTwoCoefficient3 s =
    t2Step3Coefficient0 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient1 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient2 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient3 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient3,
    t2Step3Coefficient0,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_4 (s : ℚ) :
    termTwoCoefficient4 s =
    t2Step3Coefficient1 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient2 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient3 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient4 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient4,
    t2Step3Coefficient1,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_5 (s : ℚ) :
    termTwoCoefficient5 s =
    t2Step3Coefficient2 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient3 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient4 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient5 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient5,
    t2Step3Coefficient2,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_6 (s : ℚ) :
    termTwoCoefficient6 s =
    t2Step3Coefficient3 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient4 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient5 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient6 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient6,
    t2Step3Coefficient3,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_7 (s : ℚ) :
    termTwoCoefficient7 s =
    t2Step3Coefficient4 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient5 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient6 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient7 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient7,
    t2Step3Coefficient4,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_8 (s : ℚ) :
    termTwoCoefficient8 s =
    t2Step3Coefficient5 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient6 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient7 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient8 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient8,
    t2Step3Coefficient5,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_9 (s : ℚ) :
    termTwoCoefficient9 s =
    t2Step3Coefficient6 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient7 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient8 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient9 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient9,
    t2Step3Coefficient6,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_10 (s : ℚ) :
    termTwoCoefficient10 s =
    t2Step3Coefficient7 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient8 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient9 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient10 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient10,
    t2Step3Coefficient7,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_11 (s : ℚ) :
    termTwoCoefficient11 s =
    t2Step3Coefficient8 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient9 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient10 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient11 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient11,
    t2Step3Coefficient8,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_12 (s : ℚ) :
    termTwoCoefficient12 s =
    t2Step3Coefficient9 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient10 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient11 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient12 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient12,
    t2Step3Coefficient9,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_13 (s : ℚ) :
    termTwoCoefficient13 s =
    t2Step3Coefficient10 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient11 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient12 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient13 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient13,
    t2Step3Coefficient10,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_14 (s : ℚ) :
    termTwoCoefficient14 s =
    t2Step3Coefficient11 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient12 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient13 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient14 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient14,
    t2Step3Coefficient11,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_15 (s : ℚ) :
    termTwoCoefficient15 s =
    t2Step3Coefficient12 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient13 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient14 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient15 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient15,
    t2Step3Coefficient12,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_16 (s : ℚ) :
    termTwoCoefficient16 s =
    t2Step3Coefficient13 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient14 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient15 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient16 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient16,
    t2Step3Coefficient13,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_17 (s : ℚ) :
    termTwoCoefficient17 s =
    t2Step3Coefficient14 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient15 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient16 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient17 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient17,
    t2Step3Coefficient14,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_18 (s : ℚ) :
    termTwoCoefficient18 s =
    t2Step3Coefficient15 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient16 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient17 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient18 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient18,
    t2Step3Coefficient15,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_19 (s : ℚ) :
    termTwoCoefficient19 s =
    t2Step3Coefficient16 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient17 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient18 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient19 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient19,
    t2Step3Coefficient16,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_20 (s : ℚ) :
    termTwoCoefficient20 s =
    t2Step3Coefficient17 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient18 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient19 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient20 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient20,
    t2Step3Coefficient17,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_21 (s : ℚ) :
    termTwoCoefficient21 s =
    t2Step3Coefficient18 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient19 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient20 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient21 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient21,
    t2Step3Coefficient18,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_22 (s : ℚ) :
    termTwoCoefficient22 s =
    t2Step3Coefficient19 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient20 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient21 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient22 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient22,
    t2Step3Coefficient19,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_23 (s : ℚ) :
    termTwoCoefficient23 s =
    t2Step3Coefficient20 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient21 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient22 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient23 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient23,
    t2Step3Coefficient20,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    t2Step3Coefficient23,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_24 (s : ℚ) :
    termTwoCoefficient24 s =
    t2Step3Coefficient21 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient22 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient23 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient24 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient24,
    t2Step3Coefficient21,
    t2Step3Coefficient22,
    t2Step3Coefficient23,
    t2Step3Coefficient24,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_25 (s : ℚ) :
    termTwoCoefficient25 s =
    t2Step3Coefficient22 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient23 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient24 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient25 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient25,
    t2Step3Coefficient22,
    t2Step3Coefficient23,
    t2Step3Coefficient24,
    t2Step3Coefficient25,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_26 (s : ℚ) :
    termTwoCoefficient26 s =
    t2Step3Coefficient23 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient24 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient25 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient26 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient26,
    t2Step3Coefficient23,
    t2Step3Coefficient24,
    t2Step3Coefficient25,
    t2Step3Coefficient26,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_27 (s : ℚ) :
    termTwoCoefficient27 s =
    t2Step3Coefficient24 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient25 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient26 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient27 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient27,
    t2Step3Coefficient24,
    t2Step3Coefficient25,
    t2Step3Coefficient26,
    t2Step3Coefficient27,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_28 (s : ℚ) :
    termTwoCoefficient28 s =
    t2Step3Coefficient25 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient26 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient27 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient28 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient28,
    t2Step3Coefficient25,
    t2Step3Coefficient26,
    t2Step3Coefficient27,
    t2Step3Coefficient28,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_29 (s : ℚ) :
    termTwoCoefficient29 s =
    t2Step3Coefficient26 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient27 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient28 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient29 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient29,
    t2Step3Coefficient26,
    t2Step3Coefficient27,
    t2Step3Coefficient28,
    t2Step3Coefficient29,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_30 (s : ℚ) :
    termTwoCoefficient30 s =
    t2Step3Coefficient27 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient28 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient29 s *
        rawUnitEightDenominatorCoefficient1 s
      + t2Step3Coefficient30 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [termTwoCoefficient30,
    t2Step3Coefficient27,
    t2Step3Coefficient28,
    t2Step3Coefficient29,
    t2Step3Coefficient30,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_31 (s : ℚ) :
    termTwoCoefficient31 s =
    t2Step3Coefficient28 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient29 s *
        rawUnitEightDenominatorCoefficient2 s
      + t2Step3Coefficient30 s *
        rawUnitEightDenominatorCoefficient1 s
    := by
  simp only [termTwoCoefficient31,
    t2Step3Coefficient28,
    t2Step3Coefficient29,
    t2Step3Coefficient30,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_32 (s : ℚ) :
    termTwoCoefficient32 s =
    t2Step3Coefficient29 s *
        rawUnitEightDenominatorCoefficient3 s
      + t2Step3Coefficient30 s *
        rawUnitEightDenominatorCoefficient2 s
    := by
  simp only [termTwoCoefficient32,
    t2Step3Coefficient29,
    t2Step3Coefficient30,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termTwoCoefficient_product_certificate_33 (s : ℚ) :
    termTwoCoefficient33 s =
    t2Step3Coefficient30 s *
        rawUnitEightDenominatorCoefficient3 s
    := by
  simp only [termTwoCoefficient33,
    t2Step3Coefficient30,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termTwo_eq_t2Step3_mul_rawUnitEightDenominator (r s : ℚ) :
    termTwo r s = t2Step3 r s * rawUnitEightDenominator r s := by
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
  simp only [termTwo, t2Step3, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 10
    + s ^ 9
    - s ^ 8
    + s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient1 (s : ℚ) : ℚ :=
  2 * s ^ 12
    - 8 * s ^ 11
    + 14 * s ^ 10
    - 2 * s ^ 9
    - 3 * s ^ 8
    + 11 * s ^ 7
    - 21 * s ^ 6
    + 10 * s ^ 5
    - 4 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 14
    + 7 * s ^ 13
    - 19 * s ^ 12
    + s ^ 11
    + 96 * s ^ 10
    - 243 * s ^ 9
    + 293 * s ^ 8
    - 350 * s ^ 7
    + 310 * s ^ 6
    - 134 * s ^ 5
    + 52 * s ^ 4
    - 11 * s ^ 3
    - s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient3 (s : ℚ) : ℚ :=
  -4 * s ^ 14
    + 46 * s ^ 13
    - 235 * s ^ 12
    + 705 * s ^ 11
    - 1343 * s ^ 10
    + 1808 * s ^ 9
    - 1981 * s ^ 8
    + 2097 * s ^ 7
    - 1470 * s ^ 6
    + 549 * s ^ 5
    - 212 * s ^ 4
    + 23 * s ^ 3
    + 17 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient4 (s : ℚ) : ℚ :=
  s ^ 16
    - 13 * s ^ 15
    + 84 * s ^ 14
    - 335 * s ^ 13
    + 890 * s ^ 12
    - 1649 * s ^ 11
    + 2314 * s ^ 10
    - 3036 * s ^ 9
    + 4079 * s ^ 8
    - 4380 * s ^ 7
    + 2309 * s ^ 6
    - 511 * s ^ 5
    + 218 * s ^ 4
    + 138 * s ^ 3
    - 107 * s ^ 2
    - 2 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient5 (s : ℚ) : ℚ :=
  -2 * s ^ 15
    + 23 * s ^ 14
    - 129 * s ^ 13
    + 409 * s ^ 12
    - 665 * s ^ 11
    - 11 * s ^ 10
    + 2408 * s ^ 9
    - 4732 * s ^ 8
    + 3554 * s ^ 7
    + 290 * s ^ 6
    - 1116 * s ^ 5
    + 427 * s ^ 4
    - 801 * s ^ 3
    + 322 * s ^ 2
    + 23 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 15
    + 17 * s ^ 14
    - 133 * s ^ 13
    + 643 * s ^ 12
    - 2062 * s ^ 11
    + 4402 * s ^ 10
    - 5788 * s ^ 9
    + 3224 * s ^ 8
    + 2455 * s ^ 7
    - 5187 * s ^ 6
    + 2640 * s ^ 5
    - 1508 * s ^ 4
    + 1898 * s ^ 3
    - 498 * s ^ 2
    - 101 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient7 (s : ℚ) : ℚ :=
  s ^ 14
    - 16 * s ^ 13
    + 129 * s ^ 12
    - 667 * s ^ 11
    + 2338 * s ^ 10
    - 5639 * s ^ 9
    + 9134 * s ^ 8
    - 9235 * s ^ 7
    + 4923 * s ^ 6
    - 1382 * s ^ 5
    + 2480 * s ^ 4
    - 2582 * s ^ 3
    + 276 * s ^ 2
    + 233 * s
    + 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient8 (s : ℚ) : ℚ :=
  s ^ 12
    - 22 * s ^ 11
    + 183 * s ^ 10
    - 833 * s ^ 9
    + 2342 * s ^ 8
    - 4050 * s ^ 7
    + 3689 * s ^ 6
    - 118 * s ^ 5
    - 3109 * s ^ 4
    + 1895 * s ^ 3
    + 345 * s ^ 2
    - 302 * s
    - 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 11
    + 16 * s ^ 10
    - 116 * s ^ 9
    + 513 * s ^ 8
    - 1517 * s ^ 7
    + 3022 * s ^ 6
    - 3865 * s ^ 5
    + 2650 * s ^ 4
    - 220 * s ^ 3
    - 711 * s ^ 2
    + 195 * s
    + 34

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient10 (s : ℚ) : ℚ :=
  2 * s ^ 8
    - 26 * s ^ 7
    + 143 * s ^ 6
    - 440 * s ^ 5
    + 816 * s ^ 4
    - 864 * s ^ 3
    + 415 * s ^ 2
    - 16 * s
    - 30

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceLeftCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 5
    + 10 * s ^ 4
    - 37 * s ^ 3
    + 62 * s ^ 2
    - 46 * s
    + 12

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
    differenceLeftCoefficient11 s * r ^ 11

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_0 (s : ℚ) :
    differenceLeftCoefficient0 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient0,
    rawUnitEightNumeratorCoefficient0,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_1 (s : ℚ) :
    differenceLeftCoefficient1 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient1,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_2 (s : ℚ) :
    differenceLeftCoefficient2 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient2,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_3 (s : ℚ) :
    differenceLeftCoefficient3 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient1 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient0 s
    := by
  simp only [differenceLeftCoefficient3,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1,
    rawUnitFourDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_4 (s : ℚ) :
    differenceLeftCoefficient4 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient2 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient1 s
    := by
  simp only [differenceLeftCoefficient4,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2,
    rawUnitFourDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_5 (s : ℚ) :
    differenceLeftCoefficient5 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient3 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient2 s
    := by
  simp only [differenceLeftCoefficient5,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3,
    rawUnitFourDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_6 (s : ℚ) :
    differenceLeftCoefficient6 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient4 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient3 s
    := by
  simp only [differenceLeftCoefficient6,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4,
    rawUnitFourDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_7 (s : ℚ) :
    differenceLeftCoefficient7 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient5 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient4 s
    := by
  simp only [differenceLeftCoefficient7,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5,
    rawUnitFourDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_8 (s : ℚ) :
    differenceLeftCoefficient8 s =
    rawUnitEightNumeratorCoefficient0 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient6 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient5 s
    := by
  simp only [differenceLeftCoefficient8,
    rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6,
    rawUnitFourDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_9 (s : ℚ) :
    differenceLeftCoefficient9 s =
    rawUnitEightNumeratorCoefficient1 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient7 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient6 s
    := by
  simp only [differenceLeftCoefficient9,
    rawUnitEightNumeratorCoefficient1,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7,
    rawUnitFourDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_10 (s : ℚ) :
    differenceLeftCoefficient10 s =
    rawUnitEightNumeratorCoefficient2 s *
        rawUnitFourDenominatorCoefficient8 s
      + rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient7 s
    := by
  simp only [differenceLeftCoefficient10,
    rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient8,
    rawUnitFourDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceLeftCoefficient_product_certificate_11 (s : ℚ) :
    differenceLeftCoefficient11 s =
    rawUnitEightNumeratorCoefficient3 s *
        rawUnitFourDenominatorCoefficient8 s
    := by
  simp only [differenceLeftCoefficient11,
    rawUnitEightNumeratorCoefficient3,
    rawUnitFourDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem differenceLeft_eq_rawUnitEightNumerator_mul_rawUnitFourDenominator (r s : ℚ) :
    differenceLeft r s = rawUnitEightNumerator r s * rawUnitFourDenominator r s := by
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
  simp only [differenceLeft, rawUnitEightNumerator, rawUnitFourDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient1 (s : ℚ) : ℚ :=
  s ^ 12
    - 3 * s ^ 11
    + 6 * s ^ 10
    - 8 * s ^ 9
    + 8 * s ^ 8
    - 6 * s ^ 7
    + 3 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceRightCoefficient2 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient3 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient4 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient5 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient6 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient7 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient8 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient9 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient10 (s : ℚ) : ℚ :=
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
def differenceRightCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 5
    + 9 * s ^ 4
    - 29 * s ^ 3
    + 40 * s ^ 2
    - 22 * s
    + 3

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
    differenceRightCoefficient11 s * r ^ 11

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_0 (s : ℚ) :
    differenceRightCoefficient0 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient0,
    rawUnitFourNumeratorCoefficient0,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_1 (s : ℚ) :
    differenceRightCoefficient1 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient1,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_2 (s : ℚ) :
    differenceRightCoefficient2 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient2,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1,
    rawUnitEightDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_3 (s : ℚ) :
    differenceRightCoefficient3 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient3,
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
theorem differenceRightCoefficient_product_certificate_4 (s : ℚ) :
    differenceRightCoefficient4 s =
    rawUnitFourNumeratorCoefficient1 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient4,
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
theorem differenceRightCoefficient_product_certificate_5 (s : ℚ) :
    differenceRightCoefficient5 s =
    rawUnitFourNumeratorCoefficient2 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient5,
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
theorem differenceRightCoefficient_product_certificate_6 (s : ℚ) :
    differenceRightCoefficient6 s =
    rawUnitFourNumeratorCoefficient3 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient6,
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
theorem differenceRightCoefficient_product_certificate_7 (s : ℚ) :
    differenceRightCoefficient7 s =
    rawUnitFourNumeratorCoefficient4 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient7,
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
theorem differenceRightCoefficient_product_certificate_8 (s : ℚ) :
    differenceRightCoefficient8 s =
    rawUnitFourNumeratorCoefficient5 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient1 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient0 s
    := by
  simp only [differenceRightCoefficient8,
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
theorem differenceRightCoefficient_product_certificate_9 (s : ℚ) :
    differenceRightCoefficient9 s =
    rawUnitFourNumeratorCoefficient6 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient2 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient1 s
    := by
  simp only [differenceRightCoefficient9,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2,
    rawUnitEightDenominatorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_10 (s : ℚ) :
    differenceRightCoefficient10 s =
    rawUnitFourNumeratorCoefficient7 s *
        rawUnitEightDenominatorCoefficient3 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient2 s
    := by
  simp only [differenceRightCoefficient10,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitEightDenominatorCoefficient3,
    rawUnitEightDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem differenceRightCoefficient_product_certificate_11 (s : ℚ) :
    differenceRightCoefficient11 s =
    rawUnitFourNumeratorCoefficient8 s *
        rawUnitEightDenominatorCoefficient3 s
    := by
  simp only [differenceRightCoefficient11,
    rawUnitFourNumeratorCoefficient8,
    rawUnitEightDenominatorCoefficient3]
  ring

/-- Checked staged polynomial-product identity. -/
theorem differenceRight_eq_rawUnitFourNumerator_mul_rawUnitEightDenominator (r s : ℚ) :
    differenceRight r s = rawUnitFourNumerator r s * rawUnitEightDenominator r s := by
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
  simp only [differenceRight, rawUnitFourNumerator, rawUnitEightDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 10
    + s ^ 9
    - s ^ 8
    + s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient1 (s : ℚ) : ℚ :=
  s ^ 12
    - 5 * s ^ 11
    + 8 * s ^ 10
    + 6 * s ^ 9
    - 11 * s ^ 8
    + 17 * s ^ 7
    - 24 * s ^ 6
    + 11 * s ^ 5
    - 4 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 15
    + 5 * s ^ 14
    - 14 * s ^ 13
    + 31 * s ^ 12
    - 78 * s ^ 11
    + 191 * s ^ 10
    - 322 * s ^ 9
    + 334 * s ^ 8
    - 347 * s ^ 7
    + 278 * s ^ 6
    - 101 * s ^ 5
    + 31 * s ^ 4
    - 5 * s ^ 3
    - 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 15
    + 9 * s ^ 14
    - 14 * s ^ 13
    - 45 * s ^ 12
    + 264 * s ^ 11
    - 581 * s ^ 10
    + 719 * s ^ 9
    - 705 * s ^ 8
    + 828 * s ^ 7
    - 433 * s ^ 6
    - 109 * s ^ 5
    + 100 * s ^ 4
    - 63 * s ^ 3
    + 31 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient4 (s : ℚ) : ℚ :=
  -2 * s ^ 15
    + 26 * s ^ 14
    - 134 * s ^ 13
    + 341 * s ^ 12
    - 473 * s ^ 11
    + 222 * s ^ 10
    + 203 * s ^ 9
    - 93 * s ^ 8
    + 111 * s ^ 7
    - 1490 * s ^ 6
    + 1899 * s ^ 5
    - 851 * s ^ 4
    + 374 * s ^ 3
    - 120 * s ^ 2
    - 14 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient5 (s : ℚ) : ℚ :=
  -s ^ 15
    + 20 * s ^ 14
    - 153 * s ^ 13
    + 609 * s ^ 12
    - 1419 * s ^ 11
    + 2070 * s ^ 10
    - 1831 * s ^ 9
    + 1658 * s ^ 8
    - 3862 * s ^ 7
    + 6516 * s ^ 6
    - 4732 * s ^ 5
    + 1573 * s ^ 4
    - 656 * s ^ 3
    + 102 * s ^ 2
    + 114 * s
    - 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient6 (s : ℚ) : ℚ :=
  4 * s ^ 14
    - 58 * s ^ 13
    + 352 * s ^ 12
    - 1153 * s ^ 11
    + 2128 * s ^ 10
    - 1593 * s ^ 9
    - 2585 * s ^ 8
    + 8383 * s ^ 7
    - 8860 * s ^ 6
    + 3197 * s ^ 5
    + 166 * s ^ 4
    - 84 * s ^ 3
    + 480 * s ^ 2
    - 404 * s
    + 27

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient7 (s : ℚ) : ℚ :=
  s ^ 14
    - 21 * s ^ 13
    + 184 * s ^ 12
    - 914 * s ^ 11
    + 2927 * s ^ 10
    - 6431 * s ^ 9
    + 9556 * s ^ 8
    - 8081 * s ^ 7
    + 1071 * s ^ 6
    + 4562 * s ^ 5
    - 3804 * s ^ 4
    + 1855 * s ^ 3
    - 1655 * s ^ 2
    + 798 * s
    - 48

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 13
    + 17 * s ^ 12
    - 129 * s ^ 11
    + 596 * s ^ 10
    - 1939 * s ^ 9
    + 4743 * s ^ 8
    - 8538 * s ^ 7
    + 10434 * s ^ 6
    - 8044 * s ^ 5
    + 4191 * s ^ 4
    - 2880 * s ^ 3
    + 2437 * s ^ 2
    - 931 * s
    + 44

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient9 (s : ℚ) : ℚ :=
  s ^ 11
    - 14 * s ^ 10
    + 78 * s ^ 9
    - 207 * s ^ 8
    + 214 * s ^ 7
    + 72 * s ^ 6
    - 14 * s ^ 5
    - 1151 * s ^ 4
    + 2390 * s ^ 3
    - 1966 * s ^ 2
    + 609 * s
    - 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient10 (s : ℚ) : ℚ :=
  -s ^ 9
    + 16 * s ^ 8
    - 111 * s ^ 7
    + 433 * s ^ 6
    - 1036 * s ^ 5
    + 1568 * s ^ 4
    - 1484 * s ^ 3
    + 791 * s ^ 2
    - 164 * s
    - 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def differenceCoefficient11 (s : ℚ) : ℚ :=
  s ^ 4
    - 8 * s ^ 3
    + 22 * s ^ 2
    - 24 * s
    + 9

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
    differenceCoefficient11 s * r ^ 11

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
  simp only [difference, differenceLeft, differenceRight]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient1 (s : ℚ) : ℚ :=
  s ^ 16
    - 3 * s ^ 15
    + 6 * s ^ 14
    - 8 * s ^ 13
    + 8 * s ^ 12
    - 6 * s ^ 11
    + 3 * s ^ 10
    - s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient2 (s : ℚ) : ℚ :=
  s ^ 19
    - 6 * s ^ 18
    + 21 * s ^ 17
    - 48 * s ^ 16
    + 63 * s ^ 15
    - 47 * s ^ 14
    - 18 * s ^ 13
    + 101 * s ^ 12
    - 164 * s ^ 11
    + 176 * s ^ 10
    - 133 * s ^ 9
    + 75 * s ^ 8
    - 27 * s ^ 7
    + 7 * s ^ 6
    - s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient3 (s : ℚ) : ℚ :=
  3 * s ^ 19
    - 36 * s ^ 18
    + 177 * s ^ 17
    - 581 * s ^ 16
    + 1368 * s ^ 15
    - 2365 * s ^ 14
    + 3241 * s ^ 13
    - 3499 * s ^ 12
    + 3008 * s ^ 11
    - 1929 * s ^ 10
    + 728 * s ^ 9
    + 72 * s ^ 8
    - 370 * s ^ 7
    + 284 * s ^ 6
    - 138 * s ^ 5
    + 45 * s ^ 4
    - 9 * s ^ 3
    + s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 21
    + 13 * s ^ 20
    - 84 * s ^ 19
    + 332 * s ^ 18
    - 870 * s ^ 17
    + 1584 * s ^ 16
    - 1672 * s ^ 15
    - 95 * s ^ 14
    + 4235 * s ^ 13
    - 10568 * s ^ 12
    + 17132 * s ^ 11
    - 21866 * s ^ 10
    + 22615 * s ^ 9
    - 18864 * s ^ 8
    + 12677 * s ^ 7
    - 6581 * s ^ 6
    + 2675 * s ^ 5
    - 805 * s ^ 4
    + 161 * s ^ 3
    - 18 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient5 (s : ℚ) : ℚ :=
  -s ^ 21
    + 21 * s ^ 20
    - 189 * s ^ 19
    + 1048 * s ^ 18
    - 4059 * s ^ 17
    + 11914 * s ^ 16
    - 28005 * s ^ 15
    + 53814 * s ^ 14
    - 87506 * s ^ 13
    + 124133 * s ^ 12
    - 153568 * s ^ 11
    + 165800 * s ^ 10
    - 152587 * s ^ 9
    + 117232 * s ^ 8
    - 73820 * s ^ 7
    + 36770 * s ^ 6
    - 14449 * s ^ 5
    + 4114 * s ^ 4
    - 709 * s ^ 3
    + 33 * s ^ 2
    + 15 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient6 (s : ℚ) : ℚ :=
  -s ^ 22
    + 17 * s ^ 21
    - 142 * s ^ 20
    + 770 * s ^ 19
    - 3064 * s ^ 18
    + 9620 * s ^ 17
    - 25107 * s ^ 16
    + 56090 * s ^ 15
    - 109336 * s ^ 14
    + 189813 * s ^ 13
    - 290606 * s ^ 12
    + 383539 * s ^ 11
    - 430751 * s ^ 10
    + 401740 * s ^ 9
    - 307498 * s ^ 8
    + 189750 * s ^ 7
    - 91247 * s ^ 6
    + 33461 * s ^ 5
    - 7559 * s ^ 4
    + 150 * s ^ 3
    + 521 * s ^ 2
    - 172 * s
    + 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient7 (s : ℚ) : ℚ :=
  s ^ 21
    - 9 * s ^ 20
    + 13 * s ^ 19
    + 265 * s ^ 18
    - 2399 * s ^ 17
    + 11629 * s ^ 16
    - 39805 * s ^ 15
    + 105939 * s ^ 14
    - 226288 * s ^ 13
    + 388214 * s ^ 12
    - 540151 * s ^ 11
    + 612888 * s ^ 10
    - 560182 * s ^ 9
    + 410696 * s ^ 8
    - 233092 * s ^ 7
    + 94036 * s ^ 6
    - 20139 * s ^ 5
    - 7427 * s ^ 4
    + 8805 * s ^ 3
    - 3833 * s ^ 2
    + 905 * s
    - 66

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient8 (s : ℚ) : ℚ :=
  s ^ 21
    - 19 * s ^ 20
    + 172 * s ^ 19
    - 1021 * s ^ 18
    + 4512 * s ^ 17
    - 15847 * s ^ 16
    + 45640 * s ^ 15
    - 108242 * s ^ 14
    + 208556 * s ^ 13
    - 324528 * s ^ 12
    + 410618 * s ^ 11
    - 415206 * s ^ 10
    + 320176 * s ^ 9
    - 171060 * s ^ 8
    + 26722 * s ^ 7
    + 60434 * s ^ 6
    - 82891 * s ^ 5
    + 68467 * s ^ 4
    - 37036 * s ^ 3
    + 13211 * s ^ 2
    - 2878 * s
    + 219

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient9 (s : ℚ) : ℚ :=
  -5 * s ^ 19
    + 81 * s ^ 18
    - 614 * s ^ 17
    + 2891 * s ^ 16
    - 9232 * s ^ 15
    + 20348 * s ^ 14
    - 30100 * s ^ 13
    + 25460 * s ^ 12
    + 8468 * s ^ 11
    - 83444 * s ^ 10
    + 184820 * s ^ 9
    - 275389 * s ^ 8
    + 327817 * s ^ 7
    - 316508 * s ^ 6
    + 254206 * s ^ 5
    - 168770 * s ^ 4
    + 82825 * s ^ 3
    - 28490 * s ^ 2
    + 6121 * s
    - 485

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient10 (s : ℚ) : ℚ :=
  -s ^ 19
    + 21 * s ^ 18
    - 202 * s ^ 17
    + 1221 * s ^ 16
    - 5247 * s ^ 15
    + 16933 * s ^ 14
    - 42661 * s ^ 13
    + 88432 * s ^ 12
    - 159771 * s ^ 11
    + 255746 * s ^ 10
    - 357747 * s ^ 9
    + 442636 * s ^ 8
    - 485647 * s ^ 7
    + 459255 * s ^ 6
    - 371734 * s ^ 5
    + 245451 * s ^ 4
    - 120111 * s ^ 3
    + 41763 * s ^ 2
    - 9085 * s
    + 748

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient11 (s : ℚ) : ℚ :=
  2 * s ^ 17
    - 34 * s ^ 16
    + 274 * s ^ 15
    - 1490 * s ^ 14
    + 6314 * s ^ 13
    - 21349 * s ^ 12
    + 56550 * s ^ 11
    - 118253 * s ^ 10
    + 204441 * s ^ 9
    - 302963 * s ^ 8
    + 380482 * s ^ 7
    - 399047 * s ^ 6
    + 347021 * s ^ 5
    - 236771 * s ^ 4
    + 118706 * s ^ 3
    - 42577 * s ^ 2
    + 9506 * s
    - 812

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient12 (s : ℚ) : ℚ :=
  s ^ 16
    - 23 * s ^ 15
    + 227 * s ^ 14
    - 1310 * s ^ 13
    + 5144 * s ^ 12
    - 15407 * s ^ 11
    + 38308 * s ^ 10
    - 80980 * s ^ 9
    + 141564 * s ^ 8
    - 200560 * s ^ 7
    + 231561 * s ^ 6
    - 214753 * s ^ 5
    + 151864 * s ^ 4
    - 79108 * s ^ 3
    + 29756 * s ^ 2
    - 6895 * s
    + 611

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient13 (s : ℚ) : ℚ :=
  -2 * s ^ 14
    + 42 * s ^ 13
    - 391 * s ^ 12
    + 2148 * s ^ 11
    - 7839 * s ^ 10
    + 20434 * s ^ 9
    - 40419 * s ^ 8
    + 63727 * s ^ 7
    - 81036 * s ^ 6
    + 80324 * s ^ 5
    - 59791 * s ^ 4
    + 33320 * s ^ 3
    - 13512 * s ^ 2
    + 3299 * s
    - 304

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient14 (s : ℚ) : ℚ :=
  s ^ 12
    - 20 * s ^ 11
    + 179 * s ^ 10
    - 944 * s ^ 9
    + 3239 * s ^ 8
    - 7538 * s ^ 7
    + 12148 * s ^ 6
    - 13889 * s ^ 5
    + 11770 * s ^ 4
    - 7645 * s ^ 3
    + 3543 * s ^ 2
    - 934 * s
    + 90

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step1Coefficient15 (s : ℚ) : ℚ :=
  -s ^ 8
    + 15 * s ^ 7
    - 93 * s ^ 6
    + 308 * s ^ 5
    - 588 * s ^ 4
    + 651 * s ^ 3
    - 398 * s ^ 2
    + 118 * s
    - 12

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
    t3Step1Coefficient10 s * r ^ 10 +
    t3Step1Coefficient11 s * r ^ 11 +
    t3Step1Coefficient12 s * r ^ 12 +
    t3Step1Coefficient13 s * r ^ 13 +
    t3Step1Coefficient14 s * r ^ 14 +
    t3Step1Coefficient15 s * r ^ 15

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_0 (s : ℚ) :
    t3Step1Coefficient0 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient0,
    rawUnitFourNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_1 (s : ℚ) :
    t3Step1Coefficient1 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitOneNumeratorCoefficient1 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient1,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_2 (s : ℚ) :
    t3Step1Coefficient2 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitOneNumeratorCoefficient2 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitOneNumeratorCoefficient1 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient2,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_3 (s : ℚ) :
    t3Step1Coefficient3 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitOneNumeratorCoefficient3 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitOneNumeratorCoefficient2 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitOneNumeratorCoefficient1 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient3,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_4 (s : ℚ) :
    t3Step1Coefficient4 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitOneNumeratorCoefficient4 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitOneNumeratorCoefficient3 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitOneNumeratorCoefficient2 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitOneNumeratorCoefficient1 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient4,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_5 (s : ℚ) :
    t3Step1Coefficient5 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitOneNumeratorCoefficient5 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitOneNumeratorCoefficient4 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitOneNumeratorCoefficient3 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitOneNumeratorCoefficient2 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitOneNumeratorCoefficient1 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient5,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_6 (s : ℚ) :
    t3Step1Coefficient6 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitOneNumeratorCoefficient6 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitOneNumeratorCoefficient5 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitOneNumeratorCoefficient4 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitOneNumeratorCoefficient3 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitOneNumeratorCoefficient2 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitOneNumeratorCoefficient1 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient6,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_7 (s : ℚ) :
    t3Step1Coefficient7 s =
    rawUnitFourNumeratorCoefficient0 s *
        rawUnitOneNumeratorCoefficient7 s
      + rawUnitFourNumeratorCoefficient1 s *
        rawUnitOneNumeratorCoefficient6 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitOneNumeratorCoefficient5 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitOneNumeratorCoefficient4 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitOneNumeratorCoefficient3 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitOneNumeratorCoefficient2 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitOneNumeratorCoefficient1 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient7,
    rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_8 (s : ℚ) :
    t3Step1Coefficient8 s =
    rawUnitFourNumeratorCoefficient1 s *
        rawUnitOneNumeratorCoefficient7 s
      + rawUnitFourNumeratorCoefficient2 s *
        rawUnitOneNumeratorCoefficient6 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitOneNumeratorCoefficient5 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitOneNumeratorCoefficient4 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitOneNumeratorCoefficient3 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitOneNumeratorCoefficient2 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitOneNumeratorCoefficient1 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitOneNumeratorCoefficient0 s
    := by
  simp only [t3Step1Coefficient8,
    rawUnitFourNumeratorCoefficient1,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1,
    rawUnitOneNumeratorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_9 (s : ℚ) :
    t3Step1Coefficient9 s =
    rawUnitFourNumeratorCoefficient2 s *
        rawUnitOneNumeratorCoefficient7 s
      + rawUnitFourNumeratorCoefficient3 s *
        rawUnitOneNumeratorCoefficient6 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitOneNumeratorCoefficient5 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitOneNumeratorCoefficient4 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitOneNumeratorCoefficient3 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitOneNumeratorCoefficient2 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitOneNumeratorCoefficient1 s
    := by
  simp only [t3Step1Coefficient9,
    rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient1]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_10 (s : ℚ) :
    t3Step1Coefficient10 s =
    rawUnitFourNumeratorCoefficient3 s *
        rawUnitOneNumeratorCoefficient7 s
      + rawUnitFourNumeratorCoefficient4 s *
        rawUnitOneNumeratorCoefficient6 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitOneNumeratorCoefficient5 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitOneNumeratorCoefficient4 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitOneNumeratorCoefficient3 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitOneNumeratorCoefficient2 s
    := by
  simp only [t3Step1Coefficient10,
    rawUnitFourNumeratorCoefficient3,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient3,
    rawUnitOneNumeratorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_11 (s : ℚ) :
    t3Step1Coefficient11 s =
    rawUnitFourNumeratorCoefficient4 s *
        rawUnitOneNumeratorCoefficient7 s
      + rawUnitFourNumeratorCoefficient5 s *
        rawUnitOneNumeratorCoefficient6 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitOneNumeratorCoefficient5 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitOneNumeratorCoefficient4 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitOneNumeratorCoefficient3 s
    := by
  simp only [t3Step1Coefficient11,
    rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_12 (s : ℚ) :
    t3Step1Coefficient12 s =
    rawUnitFourNumeratorCoefficient5 s *
        rawUnitOneNumeratorCoefficient7 s
      + rawUnitFourNumeratorCoefficient6 s *
        rawUnitOneNumeratorCoefficient6 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitOneNumeratorCoefficient5 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitOneNumeratorCoefficient4 s
    := by
  simp only [t3Step1Coefficient12,
    rawUnitFourNumeratorCoefficient5,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient5,
    rawUnitOneNumeratorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_13 (s : ℚ) :
    t3Step1Coefficient13 s =
    rawUnitFourNumeratorCoefficient6 s *
        rawUnitOneNumeratorCoefficient7 s
      + rawUnitFourNumeratorCoefficient7 s *
        rawUnitOneNumeratorCoefficient6 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitOneNumeratorCoefficient5 s
    := by
  simp only [t3Step1Coefficient13,
    rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_14 (s : ℚ) :
    t3Step1Coefficient14 s =
    rawUnitFourNumeratorCoefficient7 s *
        rawUnitOneNumeratorCoefficient7 s
      + rawUnitFourNumeratorCoefficient8 s *
        rawUnitOneNumeratorCoefficient6 s
    := by
  simp only [t3Step1Coefficient14,
    rawUnitFourNumeratorCoefficient7,
    rawUnitFourNumeratorCoefficient8,
    rawUnitOneNumeratorCoefficient7,
    rawUnitOneNumeratorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step1Coefficient_product_certificate_15 (s : ℚ) :
    t3Step1Coefficient15 s =
    rawUnitFourNumeratorCoefficient8 s *
        rawUnitOneNumeratorCoefficient7 s
    := by
  simp only [t3Step1Coefficient15,
    rawUnitFourNumeratorCoefficient8,
    rawUnitOneNumeratorCoefficient7]
  ring

/-- Checked staged polynomial-product identity. -/
theorem t3Step1_eq_rawUnitFourNumerator_mul_rawUnitOneNumerator (r s : ℚ) :
    t3Step1 r s = rawUnitFourNumerator r s * rawUnitOneNumerator r s := by
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
  have h11 := t3Step1Coefficient_product_certificate_11 s
  have h12 := t3Step1Coefficient_product_certificate_12 s
  have h13 := t3Step1Coefficient_product_certificate_13 s
  have h14 := t3Step1Coefficient_product_certificate_14 s
  have h15 := t3Step1Coefficient_product_certificate_15 s
  simp only [t3Step1, rawUnitFourNumerator, rawUnitOneNumerator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient1 (s : ℚ) : ℚ :=
  -s ^ 26
    + 4 * s ^ 25
    - 10 * s ^ 24
    + 18 * s ^ 23
    - 25 * s ^ 22
    + 28 * s ^ 21
    - 25 * s ^ 20
    + 18 * s ^ 19
    - 10 * s ^ 18
    + 4 * s ^ 17
    - s ^ 16

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient2 (s : ℚ) : ℚ :=
  -s ^ 29
    + 8 * s ^ 28
    - 36 * s ^ 27
    + 105 * s ^ 26
    - 194 * s ^ 25
    + 246 * s ^ 24
    - 164 * s ^ 23
    - 101 * s ^ 22
    + 493 * s ^ 21
    - 871 * s ^ 20
    + 1057 * s ^ 19
    - 996 * s ^ 18
    + 743 * s ^ 17
    - 437 * s ^ 16
    + 199 * s ^ 15
    - 64 * s ^ 14
    + 15 * s ^ 13
    - 2 * s ^ 12

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient3 (s : ℚ) : ℚ :=
  -3 * s ^ 30
    + 21 * s ^ 29
    - 45 * s ^ 28
    - 95 * s ^ 27
    + 1029 * s ^ 26
    - 3842 * s ^ 25
    + 9142 * s ^ 24
    - 16399 * s ^ 23
    + 23167 * s ^ 22
    - 26239 * s ^ 21
    + 23491 * s ^ 20
    - 15303 * s ^ 19
    + 5079 * s ^ 18
    + 3387 * s ^ 17
    - 7572 * s ^ 16
    + 7564 * s ^ 15
    - 5302 * s ^ 14
    + 2753 * s ^ 13
    - 1109 * s ^ 12
    + 341 * s ^ 11
    - 76 * s ^ 10
    + 12 * s ^ 9
    - s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient4 (s : ℚ) : ℚ :=
  -s ^ 34
    + 11 * s ^ 33
    - 65 * s ^ 32
    + 271 * s ^ 31
    - 914 * s ^ 30
    + 2776 * s ^ 29
    - 7800 * s ^ 28
    + 19415 * s ^ 27
    - 40398 * s ^ 26
    + 66149 * s ^ 25
    - 79365 * s ^ 24
    + 55525 * s ^ 23
    + 26152 * s ^ 22
    - 162088 * s ^ 21
    + 318495 * s ^ 20
    - 441839 * s ^ 19
    + 484191 * s ^ 18
    - 434895 * s ^ 17
    + 319863 * s ^ 16
    - 188396 * s ^ 15
    + 83327 * s ^ 14
    - 21846 * s ^ 13
    - 1860 * s ^ 12
    + 5912 * s ^ 11
    - 3786 * s ^ 10
    + 1534 * s ^ 9
    - 450 * s ^ 8
    + 94 * s ^ 7
    - 13 * s ^ 6
    + s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient5 (s : ℚ) : ℚ :=
  -4 * s ^ 34
    + 65 * s ^ 33
    - 470 * s ^ 32
    + 2181 * s ^ 31
    - 7496 * s ^ 30
    + 21257 * s ^ 29
    - 55673 * s ^ 28
    + 144011 * s ^ 27
    - 360726 * s ^ 26
    + 821703 * s ^ 25
    - 1624170 * s ^ 24
    + 2751530 * s ^ 23
    - 4012801 * s ^ 22
    + 5036266 * s ^ 21
    - 5417091 * s ^ 20
    + 4907263 * s ^ 19
    - 3584671 * s ^ 18
    + 1867122 * s ^ 17
    - 284131 * s ^ 16
    - 744854 * s ^ 15
    + 1106825 * s ^ 14
    - 974534 * s ^ 13
    + 635863 * s ^ 12
    - 327969 * s ^ 11
    + 135222 * s ^ 10
    - 44020 * s ^ 9
    + 11098 * s ^ 8
    - 2008 * s ^ 7
    + 219 * s ^ 6
    - 5 * s ^ 5
    - 2 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient6 (s : ℚ) : ℚ :=
  s ^ 36
    - 18 * s ^ 35
    + 158 * s ^ 34
    - 865 * s ^ 33
    + 3339 * s ^ 32
    - 10382 * s ^ 31
    + 30389 * s ^ 30
    - 93710 * s ^ 29
    + 290421 * s ^ 28
    - 804293 * s ^ 27
    + 1858325 * s ^ 26
    - 3486839 * s ^ 25
    + 5228060 * s ^ 24
    - 6042656 * s ^ 23
    + 4549601 * s ^ 22
    + 450343 * s ^ 21
    - 9104604 * s ^ 20
    + 20024406 * s ^ 19
    - 30367345 * s ^ 18
    + 36935513 * s ^ 17
    - 37753041 * s ^ 16
    + 32862912 * s ^ 15
    - 24405982 * s ^ 14
    + 15369707 * s ^ 13
    - 8114752 * s ^ 12
    + 3557699 * s ^ 11
    - 1260688 * s ^ 10
    + 342908 * s ^ 9
    - 64062 * s ^ 8
    + 4305 * s ^ 7
    + 1678 * s ^ 6
    - 613 * s ^ 5
    + 86 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient7 (s : ℚ) : ℚ :=
  2 * s ^ 36
    - 48 * s ^ 35
    + 515 * s ^ 34
    - 3345 * s ^ 33
    + 14638 * s ^ 32
    - 45623 * s ^ 31
    + 106197 * s ^ 30
    - 204700 * s ^ 29
    + 441778 * s ^ 28
    - 1358442 * s ^ 27
    + 4564934 * s ^ 26
    - 13251558 * s ^ 25
    + 31832680 * s ^ 24
    - 64500983 * s ^ 23
    + 113313423 * s ^ 22
    - 175823874 * s ^ 21
    + 243042133 * s ^ 20
    - 300355466 * s ^ 19
    + 331490974 * s ^ 18
    - 325626953 * s ^ 17
    + 282911113 * s ^ 16
    - 214909796 * s ^ 15
    + 140634584 * s ^ 14
    - 77585786 * s ^ 13
    + 34953923 * s ^ 12
    - 12161425 * s ^ 11
    + 2698732 * s ^ 10
    + 36949 * s ^ 9
    - 350174 * s ^ 8
    + 180587 * s ^ 7
    - 54036 * s ^ 6
    + 9979 * s ^ 5
    - 899 * s ^ 4
    - 36 * s ^ 3
    + 3 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient8 (s : ℚ) : ℚ :=
  s ^ 37
    - 19 * s ^ 36
    + 159 * s ^ 35
    - 720 * s ^ 34
    + 1679 * s ^ 33
    - 1629 * s ^ 32
    + 13145 * s ^ 31
    - 176233 * s ^ 30
    + 1163718 * s ^ 29
    - 5098079 * s ^ 28
    + 16849342 * s ^ 27
    - 44889790 * s ^ 26
    + 100599782 * s ^ 25
    - 195732979 * s ^ 24
    + 338727221 * s ^ 23
    - 529085614 * s ^ 22
    + 748896422 * s ^ 21
    - 958320435 * s ^ 20
    + 1103174938 * s ^ 19
    - 1133606714 * s ^ 18
    + 1028931978 * s ^ 17
    - 810760545 * s ^ 16
    + 538250492 * s ^ 15
    - 285138176 * s ^ 14
    + 104100673 * s ^ 13
    - 8328122 * s ^ 12
    - 23150638 * s ^ 11
    + 22620935 * s ^ 10
    - 13180340 * s ^ 9
    + 5547792 * s ^ 8
    - 1745070 * s ^ 7
    + 383959 * s ^ 6
    - 47551 * s ^ 5
    - 846 * s ^ 4
    + 1345 * s ^ 3
    - 81 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient9 (s : ℚ) : ℚ :=
  s ^ 37
    - 24 * s ^ 36
    + 222 * s ^ 35
    - 758 * s ^ 34
    - 3851 * s ^ 33
    + 64323 * s ^ 32
    - 435582 * s ^ 31
    + 2000789 * s ^ 30
    - 7047578 * s ^ 29
    + 20202204 * s ^ 28
    - 49062632 * s ^ 27
    + 104504271 * s ^ 26
    - 201358013 * s ^ 25
    + 358700275 * s ^ 24
    - 594053414 * s ^ 23
    + 904384626 * s ^ 22
    - 1242579510 * s ^ 21
    + 1515059813 * s ^ 20
    - 1610067779 * s ^ 19
    + 1447121216 * s ^ 18
    - 1028948998 * s ^ 17
    + 457956007 * s ^ 16
    + 92138015 * s ^ 15
    - 457436963 * s ^ 14
    + 574323487 * s ^ 13
    - 494229987 * s ^ 12
    + 330433551 * s ^ 11
    - 178390639 * s ^ 10
    + 77300677 * s ^ 9
    - 26125160 * s ^ 8
    + 6433050 * s ^ 7
    - 854200 * s ^ 6
    - 83762 * s ^ 5
    + 70358 * s ^ 4
    - 14681 * s ^ 3
    + 618 * s ^ 2
    + 29 * s
    - 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient10 (s : ℚ) : ℚ :=
  2 * s ^ 37
    - 61 * s ^ 36
    + 857 * s ^ 35
    - 7368 * s ^ 34
    + 43468 * s ^ 33
    - 186217 * s ^ 32
    + 595125 * s ^ 31
    - 1427615 * s ^ 30
    + 2541703 * s ^ 29
    - 3356963 * s ^ 28
    + 4271608 * s ^ 27
    - 11133144 * s ^ 26
    + 40117796 * s ^ 25
    - 112685630 * s ^ 24
    + 229997129 * s ^ 23
    - 337203921 * s ^ 22
    + 315502709 * s ^ 21
    - 21997146 * s ^ 20
    - 645138481 * s ^ 19
    + 1671335064 * s ^ 18
    - 2867573517 * s ^ 17
    + 3890321792 * s ^ 16
    - 4365631214 * s ^ 15
    + 4109218194 * s ^ 14
    - 3259007426 * s ^ 13
    + 2173514303 * s ^ 12
    - 1212914910 * s ^ 11
    + 557163290 * s ^ 10
    - 199736979 * s ^ 9
    + 49079086 * s ^ 8
    - 3716716 * s ^ 7
    - 3498607 * s ^ 6
    + 1990226 * s ^ 5
    - 554540 * s ^ 4
    + 78842 * s ^ 3
    - 185 * s ^ 2
    - 574 * s
    + 20

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient11 (s : ℚ) : ℚ :=
  s ^ 37
    - 40 * s ^ 36
    + 702 * s ^ 35
    - 7390 * s ^ 34
    + 53134 * s ^ 33
    - 279780 * s ^ 32
    + 1123770 * s ^ 31
    - 3525483 * s ^ 30
    + 8737002 * s ^ 29
    - 17137337 * s ^ 28
    + 26759047 * s ^ 27
    - 36271669 * s ^ 26
    + 61161666 * s ^ 25
    - 165581443 * s ^ 24
    + 489894248 * s ^ 23
    - 1234926930 * s ^ 22
    + 2590473268 * s ^ 21
    - 4650440924 * s ^ 20
    + 7331739954 * s ^ 19
    - 10270322412 * s ^ 18
    + 12777443847 * s ^ 17
    - 14007963838 * s ^ 16
    + 13373973795 * s ^ 15
    - 10991806762 * s ^ 14
    + 7683233907 * s ^ 13
    - 4486192360 * s ^ 12
    + 2117979928 * s ^ 11
    - 735262232 * s ^ 10
    + 115648689 * s ^ 9
    + 61911912 * s ^ 8
    - 64060415 * s ^ 7
    + 32260447 * s ^ 6
    - 10614616 * s ^ 5
    + 2219971 * s ^ 4
    - 198733 * s ^ 3
    - 28117 * s ^ 2
    + 5382 * s
    - 189

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient12 (s : ℚ) : ℚ :=
  -7 * s ^ 36
    + 218 * s ^ 35
    - 3175 * s ^ 34
    + 28839 * s ^ 33
    - 183426 * s ^ 32
    + 866133 * s ^ 31
    - 3119471 * s ^ 30
    + 8540789 * s ^ 29
    - 16629311 * s ^ 28
    + 15361939 * s ^ 27
    + 39007100 * s ^ 26
    - 249257731 * s ^ 25
    + 793284856 * s ^ 24
    - 1906267090 * s ^ 23
    + 3830958659 * s ^ 22
    - 6764471377 * s ^ 21
    + 10776083785 * s ^ 20
    - 15593884236 * s ^ 19
    + 20331430294 * s ^ 18
    - 23523682992 * s ^ 17
    + 23731131502 * s ^ 16
    - 20480075754 * s ^ 15
    + 14777923424 * s ^ 14
    - 8555357068 * s ^ 13
    + 3548144200 * s ^ 12
    - 525390620 * s ^ 11
    - 739158573 * s ^ 10
    + 907966092 * s ^ 9
    - 622904273 * s ^ 8
    + 309618863 * s ^ 7
    - 116166752 * s ^ 6
    + 30789186 * s ^ 5
    - 4627417 * s ^ 4
    - 164353 * s ^ 3
    + 238346 * s ^ 2
    - 31718 * s
    + 1119

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient13 (s : ℚ) : ℚ :=
  -2 * s ^ 36
    + 81 * s ^ 35
    - 1470 * s ^ 34
    + 16337 * s ^ 33
    - 126999 * s ^ 32
    + 744728 * s ^ 31
    - 3462288 * s ^ 30
    + 13230844 * s ^ 29
    - 42735399 * s ^ 28
    + 119262162 * s ^ 27
    - 292771350 * s ^ 26
    + 643393640 * s ^ 25
    - 1292915389 * s ^ 24
    + 2434633728 * s ^ 23
    - 4374888093 * s ^ 22
    + 7490158312 * s ^ 21
    - 11928045473 * s ^ 20
    + 17079974892 * s ^ 19
    - 21316306682 * s ^ 18
    + 22538500341 * s ^ 17
    - 19453166317 * s ^ 16
    + 12687918159 * s ^ 15
    - 4636922443 * s ^ 14
    - 2009919467 * s ^ 13
    + 5694910112 * s ^ 12
    - 6439532565 * s ^ 11
    + 5299725791 * s ^ 10
    - 3465836869 * s ^ 9
    + 1817223858 * s ^ 8
    - 758186513 * s ^ 7
    + 239461690 * s ^ 6
    - 46955397 * s ^ 5
    + 137480 * s ^ 4
    + 3494052 * s ^ 3
    - 1140275 * s ^ 2
    + 131423 * s
    - 4639

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient14 (s : ℚ) : ℚ :=
  6 * s ^ 35
    - 191 * s ^ 34
    + 2839 * s ^ 33
    - 26372 * s ^ 32
    + 172597 * s ^ 31
    - 848861 * s ^ 30
    + 3256028 * s ^ 29
    - 9902695 * s ^ 28
    + 23554642 * s ^ 27
    - 39676596 * s ^ 26
    + 22016525 * s ^ 25
    + 148542205 * s ^ 24
    - 731458352 * s ^ 23
    + 2095562408 * s ^ 22
    - 4456642011 * s ^ 21
    + 7392285142 * s ^ 20
    - 9526791099 * s ^ 19
    + 8938649324 * s ^ 18
    - 4326858920 * s ^ 17
    - 3795697614 * s ^ 16
    + 12937983222 * s ^ 15
    - 19950359012 * s ^ 14
    + 22795172073 * s ^ 13
    - 21325758222 * s ^ 12
    + 16919632461 * s ^ 11
    - 11468199383 * s ^ 10
    + 6522385924 * s ^ 9
    - 3008613936 * s ^ 8
    + 1066960959 * s ^ 7
    - 239165111 * s ^ 6
    - 7737216 * s ^ 5
    + 33878107 * s ^ 4
    - 15719692 * s ^ 3
    + 3792206 * s ^ 2
    - 405634 * s
    + 14249

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient15 (s : ℚ) : ℚ :=
  s ^ 35
    - 40 * s ^ 34
    + 719 * s ^ 33
    - 7922 * s ^ 32
    + 61271 * s ^ 31
    - 360933 * s ^ 30
    + 1718229 * s ^ 29
    - 6930744 * s ^ 28
    + 24536204 * s ^ 27
    - 77528670 * s ^ 26
    + 217568962 * s ^ 25
    - 530627462 * s ^ 24
    + 1089174678 * s ^ 23
    - 1793338198 * s ^ 22
    + 2125709800 * s ^ 21
    - 1036334301 * s ^ 20
    - 2731832737 * s ^ 19
    + 9850161100 * s ^ 18
    - 19599850359 * s ^ 17
    + 29711518430 * s ^ 16
    - 37243674746 * s ^ 15
    + 40050154096 * s ^ 14
    - 37664959022 * s ^ 13
    + 31172951317 * s ^ 12
    - 22571237011 * s ^ 11
    + 13968170529 * s ^ 10
    - 7028461637 * s ^ 9
    + 2614830591 * s ^ 8
    - 500312789 * s ^ 7
    - 190050161 * s ^ 6
    + 243375411 * s ^ 5
    - 130508290 * s ^ 4
    + 44584313 * s ^ 3
    - 9430751 * s ^ 2
    + 963561 * s
    - 33439

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient16 (s : ℚ) : ℚ :=
  -s ^ 34
    + 27 * s ^ 33
    - 297 * s ^ 32
    + 1429 * s ^ 31
    + 2080 * s ^ 30
    - 80578 * s ^ 29
    + 621798 * s ^ 28
    - 2833422 * s ^ 27
    + 8048500 * s ^ 26
    - 9121177 * s ^ 25
    - 41051069 * s ^ 24
    + 297284886 * s ^ 23
    - 1105501338 * s ^ 22
    + 3016204869 * s ^ 21
    - 6616583412 * s ^ 20
    + 12176896514 * s ^ 19
    - 19291936603 * s ^ 18
    + 26765239522 * s ^ 17
    - 32907843812 * s ^ 16
    + 36192951338 * s ^ 15
    - 35804413991 * s ^ 14
    + 31739271295 * s ^ 13
    - 24770138135 * s ^ 12
    + 16383826681 * s ^ 11
    - 8432219677 * s ^ 10
    + 2561349212 * s ^ 9
    + 539181362 * s ^ 8
    - 1444496889 * s ^ 7
    + 1234810301 * s ^ 6
    - 716852816 * s ^ 5
    + 303062839 * s ^ 4
    - 92095821 * s ^ 3
    + 18149237 * s ^ 2
    - 1793710 * s
    + 60858

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient17 (s : ℚ) : ℚ :=
  -s ^ 33
    + 48 * s ^ 32
    - 1019 * s ^ 31
    + 13183 * s ^ 30
    - 119092 * s ^ 29
    + 809683 * s ^ 28
    - 4337160 * s ^ 27
    + 18854673 * s ^ 26
    - 67894590 * s ^ 25
    + 205705905 * s ^ 24
    - 531487085 * s ^ 23
    + 1185993433 * s ^ 22
    - 2315329547 * s ^ 21
    + 4008927841 * s ^ 20
    - 6241401555 * s ^ 19
    + 8834902929 * s ^ 18
    - 11444366521 * s ^ 17
    + 13591147112 * s ^ 16
    - 14716487766 * s ^ 15
    + 14208199676 * s ^ 14
    - 11605269121 * s ^ 13
    + 7083262374 * s ^ 12
    - 1719231747 * s ^ 11
    - 2861397175 * s ^ 10
    + 5319100751 * s ^ 9
    - 5466025944 * s ^ 8
    + 4214571630 * s ^ 7
    - 2618086993 * s ^ 6
    + 1306358084 * s ^ 5
    - 507114167 * s ^ 4
    + 145627102 * s ^ 3
    - 27475810 * s ^ 2
    + 2636957 * s
    - 86088

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient18 (s : ℚ) : ℚ :=
  s ^ 32
    - 36 * s ^ 31
    + 610 * s ^ 30
    - 6566 * s ^ 29
    + 50976 * s ^ 28
    - 305510 * s ^ 27
    + 1466924 * s ^ 26
    - 5751373 * s ^ 25
    + 18582330 * s ^ 24
    - 49676326 * s ^ 23
    + 109850614 * s ^ 22
    - 199567782 * s ^ 21
    + 292692599 * s ^ 20
    - 334297196 * s ^ 19
    + 274897050 * s ^ 18
    - 136830027 * s ^ 17
    + 90973346 * s ^ 16
    - 516445558 * s ^ 15
    + 1912251029 * s ^ 14
    - 4519192089 * s ^ 13
    + 7899316605 * s ^ 12
    - 10944535283 * s ^ 11
    + 12407427110 * s ^ 10
    - 11688993356 * s ^ 9
    + 9285058957 * s ^ 8
    - 6300398137 * s ^ 7
    + 3630729016 * s ^ 6
    - 1722596624 * s ^ 5
    + 645116729 * s ^ 4
    - 179739346 * s ^ 3
    + 32884919 * s ^ 2
    - 3057111 * s
    + 93505

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient19 (s : ℚ) : ℚ :=
  -2 * s ^ 30
    + 59 * s ^ 29
    - 793 * s ^ 28
    + 6519 * s ^ 27
    - 37618 * s ^ 26
    + 169535 * s ^ 25
    - 661695 * s ^ 24
    + 2419331 * s ^ 23
    - 8453530 * s ^ 22
    + 27580143 * s ^ 21
    - 81838160 * s ^ 20
    + 217825908 * s ^ 19
    - 519550944 * s ^ 18
    + 1122239715 * s ^ 17
    - 2224973360 * s ^ 16
    + 4056629495 * s ^ 15
    - 6712299446 * s ^ 14
    + 9910961094 * s ^ 13
    - 12914636528 * s ^ 12
    + 14759904900 * s ^ 11
    - 14729383484 * s ^ 10
    + 12819116376 * s ^ 9
    - 9757725179 * s ^ 8
    + 6479886915 * s ^ 7
    - 3677176476 * s ^ 6
    + 1719303711 * s ^ 5
    - 634790550 * s ^ 4
    + 173768192 * s ^ 3
    - 30971110 * s ^ 2
    + 2762163 * s
    - 75181

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient20 (s : ℚ) : ℚ :=
  -s ^ 29
    + 41 * s ^ 28
    - 762 * s ^ 27
    + 8650 * s ^ 26
    - 68176 * s ^ 25
    + 402918 * s ^ 24
    - 1888264 * s ^ 23
    + 7337141 * s ^ 22
    - 24480735 * s ^ 21
    + 71942548 * s ^ 20
    - 189471364 * s ^ 19
    + 452357750 * s ^ 18
    - 984054731 * s ^ 17
    + 1944752514 * s ^ 16
    - 3461109212 * s ^ 15
    + 5500812364 * s ^ 14
    - 7774921230 * s ^ 13
    + 9760290782 * s ^ 12
    - 10867951278 * s ^ 11
    + 10720940233 * s ^ 10
    - 9373680864 * s ^ 9
    + 7250438802 * s ^ 8
    - 4893774234 * s ^ 7
    + 2800644867 * s ^ 6
    - 1311134199 * s ^ 5
    + 482258336 * s ^ 4
    - 130396104 * s ^ 3
    + 22596361 * s ^ 2
    - 1892558 * s
    + 40405

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient21 (s : ℚ) : ℚ :=
  3 * s ^ 27
    - 114 * s ^ 26
    + 2015 * s ^ 25
    - 22151 * s ^ 24
    + 171085 * s ^ 23
    - 996322 * s ^ 22
    + 4593644 * s ^ 21
    - 17397726 * s ^ 20
    + 55637585 * s ^ 19
    - 153048799 * s ^ 18
    + 366083930 * s ^ 17
    - 766480076 * s ^ 16
    + 1413376334 * s ^ 15
    - 2310745538 * s ^ 14
    + 3366982102 * s ^ 13
    - 4380270167 * s ^ 12
    + 5085330590 * s ^ 11
    - 5265556503 * s ^ 10
    + 4850343805 * s ^ 9
    - 3931825770 * s ^ 8
    + 2742255310 * s ^ 7
    - 1597749385 * s ^ 6
    + 754311410 * s ^ 5
    - 277724610 * s ^ 4
    + 74183751 * s ^ 3
    - 12372611 * s ^ 2
    + 927084 * s
    - 8876

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient22 (s : ℚ) : ℚ :=
  -4 * s ^ 25
    + 146 * s ^ 24
    - 2489 * s ^ 23
    + 26402 * s ^ 22
    - 196026 * s ^ 21
    + 1088255 * s ^ 20
    - 4723652 * s ^ 19
    + 16597383 * s ^ 18
    - 48605781 * s ^ 17
    + 121499029 * s ^ 16
    - 263573565 * s ^ 15
    + 500469628 * s ^ 14
    - 834240526 * s ^ 13
    + 1222937086 * s ^ 12
    - 1580379809 * s ^ 11
    + 1800460644 * s ^ 10
    - 1794729834 * s ^ 9
    + 1539282357 * s ^ 8
    - 1111185559 * s ^ 7
    + 660401004 * s ^ 6
    - 315553665 * s ^ 5
    + 116501335 * s ^ 4
    - 30563242 * s ^ 3
    + 4774611 * s ^ 2
    - 277272 * s
    - 6456

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient23 (s : ℚ) : ℚ :=
  3 * s ^ 23
    - 108 * s ^ 22
    + 1823 * s ^ 21
    - 19180 * s ^ 20
    + 141083 * s ^ 19
    - 772001 * s ^ 18
    + 3269102 * s ^ 17
    - 11026071 * s ^ 16
    + 30340230 * s ^ 15
    - 69619794 * s ^ 14
    + 135852927 * s ^ 13
    - 228669106 * s ^ 12
    + 333655662 * s ^ 11
    - 419723083 * s ^ 10
    + 449481572 * s ^ 9
    - 403864915 * s ^ 8
    + 300537888 * s ^ 7
    - 182851806 * s ^ 6
    + 88965693 * s ^ 5
    - 32922041 * s ^ 4
    + 8316158 * s ^ 3
    - 1117506 * s ^ 2
    + 15931 * s
    + 7539

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient24 (s : ℚ) : ℚ :=
  -s ^ 21
    + 36 * s ^ 20
    - 611 * s ^ 19
    + 6488 * s ^ 18
    - 48231 * s ^ 17
    + 266157 * s ^ 16
    - 1128550 * s ^ 15
    + 3757234 * s ^ 14
    - 9961568 * s ^ 13
    + 21238522 * s ^ 12
    - 36679057 * s ^ 11
    + 51629050 * s ^ 10
    - 59578061 * s ^ 9
    + 56648986 * s ^ 8
    - 44435298 * s ^ 7
    + 28452882 * s ^ 6
    - 14352560 * s ^ 5
    + 5262285 * s ^ 4
    - 1173350 * s ^ 3
    + 74608 * s ^ 2
    + 24711 * s
    - 3672

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient25 (s : ℚ) : ℚ :=
  s ^ 17
    - 30 * s ^ 16
    + 416 * s ^ 15
    - 3533 * s ^ 14
    + 20530 * s ^ 13
    - 86406 * s ^ 12
    + 272104 * s ^ 11
    - 653337 * s ^ 10
    + 1206973 * s ^ 9
    - 1714926 * s ^ 8
    + 1850057 * s ^ 7
    - 1465785 * s ^ 6
    + 790816 * s ^ 5
    - 233536 * s ^ 4
    - 6499 * s ^ 3
    + 32215 * s ^ 2
    - 10014 * s
    + 954

/-- Coefficient of the indicated power of the raw chart variable. -/
def t3Step2Coefficient26 (s : ℚ) : ℚ :=
  -s ^ 12
    + 23 * s ^ 11
    - 235 * s ^ 10
    + 1406 * s ^ 9
    - 5467 * s ^ 8
    + 14498 * s ^ 7
    - 26771 * s ^ 6
    + 34508 * s ^ 5
    - 30628 * s ^ 4
    + 18103 * s ^ 3
    - 6678 * s ^ 2
    + 1350 * s
    - 108

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
    t3Step2Coefficient25 s * r ^ 25 +
    t3Step2Coefficient26 s * r ^ 26

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
      + t3Step1Coefficient11 s *
        differenceCoefficient0 s
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
    t3Step1Coefficient11,
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
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_12 (s : ℚ) :
    t3Step2Coefficient12 s =
    t3Step1Coefficient1 s *
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
      + t3Step1Coefficient11 s *
        differenceCoefficient1 s
      + t3Step1Coefficient12 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient12,
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
    t3Step1Coefficient11,
    t3Step1Coefficient12,
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
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_13 (s : ℚ) :
    t3Step2Coefficient13 s =
    t3Step1Coefficient2 s *
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
      + t3Step1Coefficient11 s *
        differenceCoefficient2 s
      + t3Step1Coefficient12 s *
        differenceCoefficient1 s
      + t3Step1Coefficient13 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient13,
    t3Step1Coefficient2,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
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
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_14 (s : ℚ) :
    t3Step2Coefficient14 s =
    t3Step1Coefficient3 s *
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
      + t3Step1Coefficient11 s *
        differenceCoefficient3 s
      + t3Step1Coefficient12 s *
        differenceCoefficient2 s
      + t3Step1Coefficient13 s *
        differenceCoefficient1 s
      + t3Step1Coefficient14 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient14,
    t3Step1Coefficient3,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
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
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_15 (s : ℚ) :
    t3Step2Coefficient15 s =
    t3Step1Coefficient4 s *
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
      + t3Step1Coefficient11 s *
        differenceCoefficient4 s
      + t3Step1Coefficient12 s *
        differenceCoefficient3 s
      + t3Step1Coefficient13 s *
        differenceCoefficient2 s
      + t3Step1Coefficient14 s *
        differenceCoefficient1 s
      + t3Step1Coefficient15 s *
        differenceCoefficient0 s
    := by
  simp only [t3Step2Coefficient15,
    t3Step1Coefficient4,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
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
    differenceCoefficient1,
    differenceCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_16 (s : ℚ) :
    t3Step2Coefficient16 s =
    t3Step1Coefficient5 s *
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
      + t3Step1Coefficient11 s *
        differenceCoefficient5 s
      + t3Step1Coefficient12 s *
        differenceCoefficient4 s
      + t3Step1Coefficient13 s *
        differenceCoefficient3 s
      + t3Step1Coefficient14 s *
        differenceCoefficient2 s
      + t3Step1Coefficient15 s *
        differenceCoefficient1 s
    := by
  simp only [t3Step2Coefficient16,
    t3Step1Coefficient5,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
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
theorem t3Step2Coefficient_product_certificate_17 (s : ℚ) :
    t3Step2Coefficient17 s =
    t3Step1Coefficient6 s *
        differenceCoefficient11 s
      + t3Step1Coefficient7 s *
        differenceCoefficient10 s
      + t3Step1Coefficient8 s *
        differenceCoefficient9 s
      + t3Step1Coefficient9 s *
        differenceCoefficient8 s
      + t3Step1Coefficient10 s *
        differenceCoefficient7 s
      + t3Step1Coefficient11 s *
        differenceCoefficient6 s
      + t3Step1Coefficient12 s *
        differenceCoefficient5 s
      + t3Step1Coefficient13 s *
        differenceCoefficient4 s
      + t3Step1Coefficient14 s *
        differenceCoefficient3 s
      + t3Step1Coefficient15 s *
        differenceCoefficient2 s
    := by
  simp only [t3Step2Coefficient17,
    t3Step1Coefficient6,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
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
theorem t3Step2Coefficient_product_certificate_18 (s : ℚ) :
    t3Step2Coefficient18 s =
    t3Step1Coefficient7 s *
        differenceCoefficient11 s
      + t3Step1Coefficient8 s *
        differenceCoefficient10 s
      + t3Step1Coefficient9 s *
        differenceCoefficient9 s
      + t3Step1Coefficient10 s *
        differenceCoefficient8 s
      + t3Step1Coefficient11 s *
        differenceCoefficient7 s
      + t3Step1Coefficient12 s *
        differenceCoefficient6 s
      + t3Step1Coefficient13 s *
        differenceCoefficient5 s
      + t3Step1Coefficient14 s *
        differenceCoefficient4 s
      + t3Step1Coefficient15 s *
        differenceCoefficient3 s
    := by
  simp only [t3Step2Coefficient18,
    t3Step1Coefficient7,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
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
theorem t3Step2Coefficient_product_certificate_19 (s : ℚ) :
    t3Step2Coefficient19 s =
    t3Step1Coefficient8 s *
        differenceCoefficient11 s
      + t3Step1Coefficient9 s *
        differenceCoefficient10 s
      + t3Step1Coefficient10 s *
        differenceCoefficient9 s
      + t3Step1Coefficient11 s *
        differenceCoefficient8 s
      + t3Step1Coefficient12 s *
        differenceCoefficient7 s
      + t3Step1Coefficient13 s *
        differenceCoefficient6 s
      + t3Step1Coefficient14 s *
        differenceCoefficient5 s
      + t3Step1Coefficient15 s *
        differenceCoefficient4 s
    := by
  simp only [t3Step2Coefficient19,
    t3Step1Coefficient8,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
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
theorem t3Step2Coefficient_product_certificate_20 (s : ℚ) :
    t3Step2Coefficient20 s =
    t3Step1Coefficient9 s *
        differenceCoefficient11 s
      + t3Step1Coefficient10 s *
        differenceCoefficient10 s
      + t3Step1Coefficient11 s *
        differenceCoefficient9 s
      + t3Step1Coefficient12 s *
        differenceCoefficient8 s
      + t3Step1Coefficient13 s *
        differenceCoefficient7 s
      + t3Step1Coefficient14 s *
        differenceCoefficient6 s
      + t3Step1Coefficient15 s *
        differenceCoefficient5 s
    := by
  simp only [t3Step2Coefficient20,
    t3Step1Coefficient9,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6,
    differenceCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_21 (s : ℚ) :
    t3Step2Coefficient21 s =
    t3Step1Coefficient10 s *
        differenceCoefficient11 s
      + t3Step1Coefficient11 s *
        differenceCoefficient10 s
      + t3Step1Coefficient12 s *
        differenceCoefficient9 s
      + t3Step1Coefficient13 s *
        differenceCoefficient8 s
      + t3Step1Coefficient14 s *
        differenceCoefficient7 s
      + t3Step1Coefficient15 s *
        differenceCoefficient6 s
    := by
  simp only [t3Step2Coefficient21,
    t3Step1Coefficient10,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7,
    differenceCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_22 (s : ℚ) :
    t3Step2Coefficient22 s =
    t3Step1Coefficient11 s *
        differenceCoefficient11 s
      + t3Step1Coefficient12 s *
        differenceCoefficient10 s
      + t3Step1Coefficient13 s *
        differenceCoefficient9 s
      + t3Step1Coefficient14 s *
        differenceCoefficient8 s
      + t3Step1Coefficient15 s *
        differenceCoefficient7 s
    := by
  simp only [t3Step2Coefficient22,
    t3Step1Coefficient11,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8,
    differenceCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_23 (s : ℚ) :
    t3Step2Coefficient23 s =
    t3Step1Coefficient12 s *
        differenceCoefficient11 s
      + t3Step1Coefficient13 s *
        differenceCoefficient10 s
      + t3Step1Coefficient14 s *
        differenceCoefficient9 s
      + t3Step1Coefficient15 s *
        differenceCoefficient8 s
    := by
  simp only [t3Step2Coefficient23,
    t3Step1Coefficient12,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9,
    differenceCoefficient8]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_24 (s : ℚ) :
    t3Step2Coefficient24 s =
    t3Step1Coefficient13 s *
        differenceCoefficient11 s
      + t3Step1Coefficient14 s *
        differenceCoefficient10 s
      + t3Step1Coefficient15 s *
        differenceCoefficient9 s
    := by
  simp only [t3Step2Coefficient24,
    t3Step1Coefficient13,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
    differenceCoefficient11,
    differenceCoefficient10,
    differenceCoefficient9]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_25 (s : ℚ) :
    t3Step2Coefficient25 s =
    t3Step1Coefficient14 s *
        differenceCoefficient11 s
      + t3Step1Coefficient15 s *
        differenceCoefficient10 s
    := by
  simp only [t3Step2Coefficient25,
    t3Step1Coefficient14,
    t3Step1Coefficient15,
    differenceCoefficient11,
    differenceCoefficient10]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem t3Step2Coefficient_product_certificate_26 (s : ℚ) :
    t3Step2Coefficient26 s =
    t3Step1Coefficient15 s *
        differenceCoefficient11 s
    := by
  simp only [t3Step2Coefficient26,
    t3Step1Coefficient15,
    differenceCoefficient11]
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
  have h26 := t3Step2Coefficient_product_certificate_26 s
  simp only [t3Step2, t3Step1, difference]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 34
    + 4 * s ^ 33
    - 10 * s ^ 32
    + 18 * s ^ 31
    - 25 * s ^ 30
    + 28 * s ^ 29
    - 25 * s ^ 28
    + 18 * s ^ 27
    - 10 * s ^ 26
    + 4 * s ^ 25
    - s ^ 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient2 (s : ℚ) : ℚ :=
  -s ^ 37
    + 8 * s ^ 36
    - 36 * s ^ 35
    + 102 * s ^ 34
    - 165 * s ^ 33
    + 138 * s ^ 32
    + 106 * s ^ 31
    - 609 * s ^ 30
    + 1255 * s ^ 29
    - 1814 * s ^ 28
    + 2030 * s ^ 27
    - 1843 * s ^ 26
    + 1364 * s ^ 25
    - 819 * s ^ 24
    + 395 * s ^ 23
    - 146 * s ^ 22
    + 43 * s ^ 21
    - 9 * s ^ 20
    + s ^ 19

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient3 (s : ℚ) : ℚ :=
  -3 * s ^ 38
    + 17 * s ^ 37
    + 6 * s ^ 36
    - 404 * s ^ 35
    + 2254 * s ^ 34
    - 7223 * s ^ 33
    + 15765 * s ^ 32
    - 25982 * s ^ 31
    + 32739 * s ^ 30
    - 30464 * s ^ 29
    + 16927 * s ^ 28
    + 4603 * s ^ 27
    - 25727 * s ^ 26
    + 38821 * s ^ 25
    - 40414 * s ^ 24
    + 32851 * s ^ 23
    - 21702 * s ^ 22
    + 11720 * s ^ 21
    - 5268 * s ^ 20
    + 1950 * s ^ 19
    - 579 * s ^ 18
    + 133 * s ^ 17
    - 22 * s ^ 16
    + 2 * s ^ 15

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 42
    + 11 * s ^ 41
    - 66 * s ^ 40
    + 285 * s ^ 39
    - 1028 * s ^ 38
    + 3429 * s ^ 37
    - 10360 * s ^ 36
    + 26001 * s ^ 35
    - 49315 * s ^ 34
    + 58208 * s ^ 33
    - 1190 * s ^ 32
    - 178998 * s ^ 31
    + 507374 * s ^ 30
    - 927218 * s ^ 29
    + 1304694 * s ^ 28
    - 1485772 * s ^ 27
    + 1379608 * s ^ 26
    - 1026516 * s ^ 25
    + 563153 * s ^ 24
    - 152924 * s ^ 23
    - 101714 * s ^ 22
    + 192319 * s ^ 21
    - 173010 * s ^ 20
    + 114766 * s ^ 19
    - 61098 * s ^ 18
    + 26722 * s ^ 17
    - 9644 * s ^ 16
    + 2847 * s ^ 15
    - 668 * s ^ 14
    + 119 * s ^ 13
    - 15 * s ^ 12
    + s ^ 11

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient5 (s : ℚ) : ℚ :=
  -7 * s ^ 42
    + 112 * s ^ 41
    - 823 * s ^ 40
    + 3983 * s ^ 39
    - 14823 * s ^ 38
    + 47864 * s ^ 37
    - 146705 * s ^ 36
    + 428681 * s ^ 35
    - 1130587 * s ^ 34
    + 2552763 * s ^ 33
    - 4782010 * s ^ 32
    + 7343580 * s ^ 31
    - 9131376 * s ^ 30
    + 8717433 * s ^ 29
    - 5189054 * s ^ 28
    - 1140470 * s ^ 27
    + 8565631 * s ^ 26
    - 14650274 * s ^ 25
    + 17532847 * s ^ 24
    - 16708714 * s ^ 23
    + 13172750 * s ^ 22
    - 8667501 * s ^ 21
    + 4709665 * s ^ 20
    - 2051901 * s ^ 19
    + 642291 * s ^ 18
    - 73241 * s ^ 17
    - 71500 * s ^ 16
    + 65368 * s ^ 15
    - 33746 * s ^ 14
    + 12778 * s ^ 13
    - 3731 * s ^ 12
    + 843 * s ^ 11
    - 141 * s ^ 10
    + 16 * s ^ 9
    - s ^ 8

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 45
    + 18 * s ^ 44
    - 170 * s ^ 43
    + 1088 * s ^ 42
    - 5117 * s ^ 41
    + 18651 * s ^ 40
    - 56349 * s ^ 39
    + 152651 * s ^ 38
    - 393815 * s ^ 37
    + 949064 * s ^ 36
    - 1919354 * s ^ 35
    + 2646661 * s ^ 34
    - 394645 * s ^ 33
    - 10548476 * s ^ 32
    + 37355911 * s ^ 31
    - 84554463 * s ^ 30
    + 149369731 * s ^ 29
    - 218841988 * s ^ 28
    + 272936698 * s ^ 27
    - 292359212 * s ^ 26
    + 268241417 * s ^ 25
    - 207583153 * s ^ 24
    + 129470471 * s ^ 23
    - 56600894 * s ^ 22
    + 4985493 * s ^ 21
    + 20995435 * s ^ 20
    - 26718014 * s ^ 19
    + 21733724 * s ^ 18
    - 13859334 * s ^ 17
    + 7300142 * s ^ 16
    - 3227320 * s ^ 15
    + 1196062 * s ^ 14
    - 365761 * s ^ 13
    + 89501 * s ^ 12
    - 16529 * s ^ 11
    + 1951 * s ^ 10
    - 52 * s ^ 9
    - 26 * s ^ 8
    + 4 * s ^ 7

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient7 (s : ℚ) : ℚ :=
  -4 * s ^ 45
    + 96 * s ^ 44
    - 1094 * s ^ 43
    + 8139 * s ^ 42
    - 44431 * s ^ 41
    + 188777 * s ^ 40
    - 655050 * s ^ 39
    + 1962740 * s ^ 38
    - 5409328 * s ^ 37
    + 14408659 * s ^ 36
    - 37233136 * s ^ 35
    + 89925184 * s ^ 34
    - 194638488 * s ^ 33
    + 367619786 * s ^ 32
    - 599021942 * s ^ 31
    + 838638742 * s ^ 30
    - 999339134 * s ^ 29
    + 983114613 * s ^ 28
    - 728380696 * s ^ 27
    + 250331749 * s ^ 26
    + 346280614 * s ^ 25
    - 902290368 * s ^ 24
    + 1272079577 * s ^ 23
    - 1379795472 * s ^ 22
    + 1246733878 * s ^ 21
    - 966260500 * s ^ 20
    + 650707885 * s ^ 19
    - 383327431 * s ^ 18
    + 197112877 * s ^ 17
    - 87624644 * s ^ 16
    + 33081171 * s ^ 15
    - 10247150 * s ^ 14
    + 2411797 * s ^ 13
    - 337313 * s ^ 12
    - 21184 * s ^ 11
    + 28321 * s ^ 10
    - 8517 * s ^ 9
    + 1380 * s ^ 8
    - 99 * s ^ 7
    - 4 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient8 (s : ℚ) : ℚ :=
  s ^ 47
    - 24 * s ^ 46
    + 288 * s ^ 45
    - 2246 * s ^ 44
    + 12623 * s ^ 43
    - 54242 * s ^ 42
    + 186512 * s ^ 41
    - 547799 * s ^ 40
    + 1541504 * s ^ 39
    - 4641696 * s ^ 38
    + 14606311 * s ^ 37
    - 42575389 * s ^ 36
    + 104358519 * s ^ 35
    - 201933962 * s ^ 34
    + 281139280 * s ^ 33
    - 184679241 * s ^ 32
    - 351479186 * s ^ 31
    + 1626641015 * s ^ 30
    - 3849138750 * s ^ 29
    + 6986225199 * s ^ 28
    - 10650884912 * s ^ 27
    + 14132392308 * s ^ 26
    - 16586869658 * s ^ 25
    + 17358960036 * s ^ 24
    - 16252406927 * s ^ 23
    + 13603493009 * s ^ 22
    - 10155055065 * s ^ 21
    + 6732712009 * s ^ 20
    - 3940007967 * s ^ 19
    + 2013335926 * s ^ 18
    - 874916490 * s ^ 17
    + 305227737 * s ^ 16
    - 72230802 * s ^ 15
    + 965904 * s ^ 14
    + 10018484 * s ^ 13
    - 6245032 * s ^ 12
    + 2392327 * s ^ 11
    - 644734 * s ^ 10
    + 115865 * s ^ 9
    - 10372 * s ^ 8
    - 610 * s ^ 7
    + 250 * s ^ 6
    - 3 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient9 (s : ℚ) : ℚ :=
  2 * s ^ 47
    - 62 * s ^ 46
    + 894 * s ^ 45
    - 8158 * s ^ 44
    + 53055 * s ^ 43
    - 261244 * s ^ 42
    + 1008693 * s ^ 41
    - 3133477 * s ^ 40
    + 8154802 * s ^ 39
    - 19608563 * s ^ 38
    + 51449040 * s ^ 37
    - 158439303 * s ^ 36
    + 506127759 * s ^ 35
    - 1471059197 * s ^ 34
    + 3701154371 * s ^ 33
    - 8029042770 * s ^ 32
    + 15200125311 * s ^ 31
    - 25515312161 * s ^ 30
    + 38496703369 * s ^ 29
    - 52627072070 * s ^ 28
    + 65396076490 * s ^ 27
    - 73881934871 * s ^ 26
    + 75717506283 * s ^ 25
    - 70104878780 * s ^ 24
    + 58226964798 * s ^ 23
    - 42900414914 * s ^ 22
    + 27589497412 * s ^ 21
    - 15043734110 * s ^ 20
    + 6502282721 * s ^ 19
    - 1720616025 * s ^ 18
    - 359380740 * s ^ 17
    + 876173084 * s ^ 16
    - 719906281 * s ^ 15
    + 419539535 * s ^ 14
    - 190946698 * s ^ 13
    + 68397387 * s ^ 12
    - 18616190 * s ^ 11
    + 3429080 * s ^ 10
    - 212617 * s ^ 9
    - 94134 * s ^ 8
    + 32235 * s ^ 7
    - 3886 * s ^ 6
    - 77 * s ^ 5
    + 7 * s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient10 (s : ℚ) : ℚ :=
  s ^ 48
    - 25 * s ^ 47
    + 290 * s ^ 46
    - 2005 * s ^ 45
    + 8688 * s ^ 44
    - 20897 * s ^ 43
    + 6843 * s ^ 42
    + 46033 * s ^ 41
    + 1063934 * s ^ 40
    - 12801911 * s ^ 39
    + 78677460 * s ^ 38
    - 341809746 * s ^ 37
    + 1160631502 * s ^ 36
    - 3232192698 * s ^ 35
    + 7605843839 * s ^ 34
    - 15475568264 * s ^ 33
    + 27795690146 * s ^ 32
    - 44909461491 * s ^ 31
    + 66212606100 * s ^ 30
    - 89603852006 * s ^ 29
    + 110974311283 * s ^ 28
    - 124752596825 * s ^ 27
    + 125760480281 * s ^ 26
    - 111521514002 * s ^ 25
    + 83922721411 * s ^ 24
    - 49001592031 * s ^ 23
    + 15107511711 * s ^ 22
    + 10354982156 * s ^ 21
    - 24077203277 * s ^ 20
    + 27213511454 * s ^ 19
    - 23578282391 * s ^ 18
    + 17138661833 * s ^ 17
    - 10655286883 * s ^ 16
    + 5652825802 * s ^ 15
    - 2521309775 * s ^ 14
    + 911237812 * s ^ 13
    - 244784444 * s ^ 12
    + 36109181 * s ^ 11
    + 5244220 * s ^ 10
    - 5359877 * s ^ 9
    + 1746929 * s ^ 8
    - 298293 * s ^ 7
    + 14106 * s ^ 6
    + 4026 * s ^ 5
    - 198 * s ^ 4
    - 2 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient11 (s : ℚ) : ℚ :=
  s ^ 48
    - 32 * s ^ 47
    + 434 * s ^ 46
    - 3168 * s ^ 45
    + 10200 * s ^ 44
    + 43222 * s ^ 43
    - 813500 * s ^ 42
    + 6136771 * s ^ 41
    - 32197640 * s ^ 40
    + 131371102 * s ^ 39
    - 435532892 * s ^ 38
    + 1199742207 * s ^ 37
    - 2784782753 * s ^ 36
    + 5512404054 * s ^ 35
    - 9450497493 * s ^ 34
    + 14380241684 * s ^ 33
    - 20092421128 * s ^ 32
    + 26497295506 * s ^ 31
    - 32572034867 * s ^ 30
    + 34439932275 * s ^ 29
    - 25153451072 * s ^ 28
    - 2182537152 * s ^ 27
    + 50100402422 * s ^ 26
    - 113823790461 * s ^ 25
    + 180989436357 * s ^ 24
    - 234928823692 * s ^ 23
    + 260576027681 * s ^ 22
    - 252126172795 * s ^ 21
    + 216068337151 * s ^ 20
    - 165852686068 * s ^ 19
    + 114658149887 * s ^ 18
    - 70831224913 * s ^ 17
    + 38124017876 * s ^ 16
    - 17226183797 * s ^ 15
    + 6086480335 * s ^ 14
    - 1333792596 * s ^ 13
    - 106202397 * s ^ 12
    + 268802654 * s ^ 11
    - 145032410 * s ^ 10
    + 48441690 * s ^ 9
    - 10041421 * s ^ 8
    + 826356 * s ^ 7
    + 175355 * s ^ 6
    - 54402 * s ^ 5
    + 1292 * s ^ 4
    + 139 * s ^ 3
    - 2 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient12 (s : ℚ) : ℚ :=
  2 * s ^ 48
    - 75 * s ^ 47
    + 1321 * s ^ 46
    - 14558 * s ^ 45
    + 112969 * s ^ 44
    - 655173 * s ^ 43
    + 2913912 * s ^ 42
    - 9859496 * s ^ 41
    + 23508291 * s ^ 40
    - 25155162 * s ^ 39
    - 90352973 * s ^ 38
    + 649682813 * s ^ 37
    - 2349982250 * s ^ 36
    + 6212767387 * s ^ 35
    - 13117238964 * s ^ 34
    + 23205794587 * s ^ 33
    - 36404247748 * s ^ 32
    + 55215198936 * s ^ 31
    - 88197118906 * s ^ 30
    + 149149983668 * s ^ 29
    - 249384420773 * s ^ 28
    + 388762581103 * s ^ 27
    - 552416042093 * s ^ 26
    + 712260402803 * s ^ 25
    - 832136118523 * s ^ 24
    + 878556145838 * s ^ 23
    - 835928919059 * s ^ 22
    + 718203033171 * s ^ 21
    - 560510728747 * s ^ 20
    + 398002079188 * s ^ 19
    - 254006296507 * s ^ 18
    + 139995555090 * s ^ 17
    - 61202112991 * s ^ 16
    + 16747587709 * s ^ 15
    + 1941526027 * s ^ 14
    - 6081676795 * s ^ 13
    + 4531097790 * s ^ 12
    - 2210128974 * s ^ 11
    + 772004496 * s ^ 10
    - 181980920 * s ^ 9
    + 18103074 * s ^ 8
    + 5005592 * s ^ 7
    - 2398390 * s ^ 6
    + 356550 * s ^ 5
    + 9252 * s ^ 4
    - 2515 * s ^ 3
    + 22 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient13 (s : ℚ) : ℚ :=
  s ^ 48
    - 50 * s ^ 47
    + 1101 * s ^ 46
    - 14763 * s ^ 45
    + 138304 * s ^ 44
    - 977153 * s ^ 43
    + 5455178 * s ^ 42
    - 24754546 * s ^ 41
    + 92672910 * s ^ 40
    - 287231939 * s ^ 39
    + 731299984 * s ^ 38
    - 1495231082 * s ^ 37
    + 2336062567 * s ^ 36
    - 2482879889 * s ^ 35
    + 1319582853 * s ^ 34
    - 1211770430 * s ^ 33
    + 12294538642 * s ^ 32
    - 55188166631 * s ^ 31
    + 155284198780 * s ^ 30
    - 328218406315 * s ^ 29
    + 567999180034 * s ^ 28
    - 848457149850 * s ^ 27
    + 1129898754457 * s ^ 26
    - 1360117379412 * s ^ 25
    + 1481186544702 * s ^ 24
    - 1453986219593 * s ^ 23
    + 1286665424252 * s ^ 22
    - 1034105502057 * s ^ 21
    + 756898509435 * s ^ 20
    - 491229116940 * s ^ 19
    + 257613034528 * s ^ 18
    - 76628721405 * s ^ 17
    - 32473858819 * s ^ 16
    + 71267486430 * s ^ 15
    - 64970161445 * s ^ 14
    + 42007096133 * s ^ 13
    - 20676584135 * s ^ 12
    + 7639857981 * s ^ 11
    - 1918886924 * s ^ 10
    + 172927780 * s ^ 9
    + 106132029 * s ^ 8
    - 58336440 * s ^ 7
    + 13703049 * s ^ 6
    - 1060742 * s ^ 5
    - 213710 * s ^ 4
    + 23012 * s ^ 3
    + 155 * s ^ 2
    - 27 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient14 (s : ℚ) : ℚ :=
  -9 * s ^ 47
    + 346 * s ^ 46
    - 6307 * s ^ 45
    + 73294 * s ^ 44
    - 615451 * s ^ 43
    + 4003864 * s ^ 42
    - 21047059 * s ^ 41
    + 91575072 * s ^ 40
    - 333097825 * s ^ 39
    + 1009802008 * s ^ 38
    - 2501839151 * s ^ 37
    + 4799005890 * s ^ 36
    - 5912904041 * s ^ 35
    - 957187519 * s ^ 34
    + 29786148244 * s ^ 33
    - 99427653395 * s ^ 32
    + 223660483649 * s ^ 31
    - 399208672662 * s ^ 30
    + 606135558196 * s ^ 29
    - 824900815806 * s ^ 28
    + 1045776762541 * s ^ 27
    - 1247171199077 * s ^ 26
    + 1373190394695 * s ^ 25
    - 1360609347038 * s ^ 24
    + 1197571697632 * s ^ 23
    - 941356336091 * s ^ 22
    + 659389423427 * s ^ 21
    - 365516294108 * s ^ 20
    + 52124247055 * s ^ 19
    + 241661131263 * s ^ 18
    - 434292608483 * s ^ 17
    + 471390051663 * s ^ 16
    - 381849755133 * s ^ 15
    + 245241186417 * s ^ 14
    - 125340565274 * s ^ 13
    + 48533076535 * s ^ 12
    - 12043545019 * s ^ 11
    + 130652548 * s ^ 10
    + 1626108090 * s ^ 9
    - 910915516 * s ^ 8
    + 274449419 * s ^ 7
    - 41357190 * s ^ 6
    - 1716964 * s ^ 5
    + 1775225 * s ^ 4
    - 123110 * s ^ 3
    - 5195 * s ^ 2
    + 350 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient15 (s : ℚ) : ℚ :=
  -2 * s ^ 47
    + 104 * s ^ 46
    - 2352 * s ^ 45
    + 32372 * s ^ 44
    - 314014 * s ^ 43
    + 2337931 * s ^ 42
    - 14120871 * s ^ 41
    + 71695798 * s ^ 40
    - 312267298 * s ^ 39
    + 1176803334 * s ^ 38
    - 3840935558 * s ^ 37
    + 10820097816 * s ^ 36
    - 26143577914 * s ^ 35
    + 53677418436 * s ^ 34
    - 92393216989 * s ^ 33
    + 130919758057 * s ^ 32
    - 150011416724 * s ^ 31
    + 141250409623 * s ^ 30
    - 130900055440 * s ^ 29
    + 171479401927 * s ^ 28
    - 281188359126 * s ^ 27
    + 391189933563 * s ^ 26
    - 391686648669 * s ^ 25
    + 246753005207 * s ^ 24
    - 29887831834 * s ^ 23
    - 183892977038 * s ^ 22
    + 439070306186 * s ^ 21
    - 838426432345 * s ^ 20
    + 1342794491740 * s ^ 19
    - 1727810668456 * s ^ 18
    + 1771625628120 * s ^ 17
    - 1453655200019 * s ^ 16
    + 960724118660 * s ^ 15
    - 506240826054 * s ^ 14
    + 197093698888 * s ^ 13
    - 39687490351 * s ^ 12
    - 13211564797 * s ^ 11
    + 17569234820 * s ^ 10
    - 9667100141 * s ^ 9
    + 3416414276 * s ^ 8
    - 714863277 * s ^ 7
    + 26026091 * s ^ 6
    + 33704229 * s ^ 5
    - 9045772 * s ^ 4
    + 344618 * s ^ 3
    + 56144 * s ^ 2
    - 2899 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient16 (s : ℚ) : ℚ :=
  9 * s ^ 46
    - 341 * s ^ 45
    + 6008 * s ^ 44
    - 66795 * s ^ 43
    + 539615 * s ^ 42
    - 3480777 * s ^ 41
    + 19224218 * s ^ 40
    - 94818686 * s ^ 39
    + 421945288 * s ^ 38
    - 1673962758 * s ^ 37
    + 5814736126 * s ^ 36
    - 17416892842 * s ^ 35
    + 44419589007 * s ^ 34
    - 95074765115 * s ^ 33
    + 166952183452 * s ^ 32
    - 230478869480 * s ^ 31
    + 226397978991 * s ^ 30
    - 105878367470 * s ^ 29
    - 93516424742 * s ^ 28
    + 219213048681 * s ^ 27
    - 111675358222 * s ^ 26
    - 224397828845 * s ^ 25
    + 612419966953 * s ^ 24
    - 932759836531 * s ^ 23
    + 1331862065617 * s ^ 22
    - 2092198764336 * s ^ 21
    + 3212335744655 * s ^ 20
    - 4209725570885 * s ^ 19
    + 4481578548041 * s ^ 18
    - 3828659993385 * s ^ 17
    + 2597385055412 * s ^ 16
    - 1354287915700 * s ^ 15
    + 465962615079 * s ^ 14
    + 471662483 * s ^ 13
    - 147925061474 * s ^ 12
    + 130888547237 * s ^ 11
    - 72169906825 * s ^ 10
    + 28192932121 * s ^ 9
    - 7242101511 * s ^ 8
    + 614329749 * s ^ 7
    + 379352922 * s ^ 6
    - 180817017 * s ^ 5
    + 30856428 * s ^ 4
    + 238702 * s ^ 3
    - 380232 * s ^ 2
    + 17174 * s
    + 1

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient17 (s : ℚ) : ℚ :=
  s ^ 46
    - 47 * s ^ 45
    + 882 * s ^ 44
    - 8802 * s ^ 43
    + 47755 * s ^ 42
    - 79348 * s ^ 41
    - 803900 * s ^ 40
    + 6821281 * s ^ 39
    - 20117650 * s ^ 38
    - 46120306 * s ^ 37
    + 815957684 * s ^ 36
    - 4908700687 * s ^ 35
    + 20137762641 * s ^ 34
    - 63543800130 * s ^ 33
    + 160273688453 * s ^ 32
    - 325295343589 * s ^ 31
    + 522193894551 * s ^ 30
    - 627591411847 * s ^ 29
    + 471263284854 * s ^ 28
    + 12769876076 * s ^ 27
    - 648602504031 * s ^ 26
    + 1129523438827 * s ^ 25
    - 1392337486944 * s ^ 24
    + 1858680269674 * s ^ 23
    - 3126793394107 * s ^ 22
    + 5252086440009 * s ^ 21
    - 7359277170248 * s ^ 20
    + 8192874910536 * s ^ 19
    - 7159301490086 * s ^ 18
    + 4776728347864 * s ^ 17
    - 2184285242368 * s ^ 16
    + 288394796742 * s ^ 15
    + 662096410902 * s ^ 14
    - 870647419543 * s ^ 13
    + 674978292231 * s ^ 12
    - 380528655314 * s ^ 11
    + 159854760689 * s ^ 10
    - 46111529700 * s ^ 9
    + 4959743529 * s ^ 8
    + 3237098283 * s ^ 7
    - 2110491898 * s ^ 6
    + 598181194 * s ^ 5
    - 66313756 * s ^ 4
    - 7723666 * s ^ 3
    + 1860381 * s ^ 2
    - 77051 * s
    - 21

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient18 (s : ℚ) : ℚ :=
  -s ^ 45
    - 10 * s ^ 44
    + 1436 * s ^ 43
    - 35513 * s ^ 42
    + 485920 * s ^ 41
    - 4493599 * s ^ 40
    + 30634969 * s ^ 39
    - 161419125 * s ^ 38
    + 674719773 * s ^ 37
    - 2257833852 * s ^ 36
    + 5968943024 * s ^ 35
    - 11686319414 * s ^ 34
    + 12524040940 * s ^ 33
    + 16512865383 * s ^ 32
    - 129233302798 * s ^ 31
    + 395109745564 * s ^ 30
    - 833617063800 * s ^ 29
    + 1316257642855 * s ^ 28
    - 1560622594319 * s ^ 27
    + 1364770042141 * s ^ 26
    - 994631643208 * s ^ 25
    + 1286702317883 * s ^ 24
    - 3091444050592 * s ^ 23
    + 6336935932463 * s ^ 22
    - 9605400073081 * s ^ 21
    + 10911363705602 * s ^ 20
    - 9223610979865 * s ^ 19
    + 5287170151674 * s ^ 18
    - 968723548677 * s ^ 17
    - 2103535356382 * s ^ 16
    + 3391344615394 * s ^ 15
    - 3276982252707 * s ^ 14
    + 2419893673992 * s ^ 13
    - 1405112909402 * s ^ 12
    + 622446133456 * s ^ 11
    - 187142029286 * s ^ 10
    + 14931686788 * s ^ 9
    + 23437035514 * s ^ 8
    - 17077172752 * s ^ 7
    + 6401427115 * s ^ 6
    - 1313857524 * s ^ 5
    + 43777011 * s ^ 4
    + 44073871 * s ^ 3
    - 6987276 * s ^ 2
    + 270206 * s
    + 209

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient19 (s : ℚ) : ℚ :=
  -10 * s ^ 44
    + 541 * s ^ 43
    - 13194 * s ^ 42
    + 196895 * s ^ 41
    - 2046967 * s ^ 40
    + 15950599 * s ^ 39
    - 97663430 * s ^ 38
    + 485449702 * s ^ 37
    - 2004148314 * s ^ 36
    + 6973298416 * s ^ 35
    - 20568106599 * s ^ 34
    + 51139254880 * s ^ 33
    - 104706421122 * s ^ 32
    + 166164037690 * s ^ 31
    - 168027149200 * s ^ 30
    - 20435536634 * s ^ 29
    + 511784412380 * s ^ 28
    - 1186572292080 * s ^ 27
    + 1481895108324 * s ^ 26
    - 510786853638 * s ^ 25
    - 2290744939840 * s ^ 24
    + 6348523076898 * s ^ 23
    - 9772819657631 * s ^ 22
    + 10329880194647 * s ^ 21
    - 7065435352540 * s ^ 20
    + 1187196392756 * s ^ 19
    + 4736167886450 * s ^ 18
    - 8514338375273 * s ^ 17
    + 9461573305237 * s ^ 16
    - 8242591817938 * s ^ 15
    + 5964394145659 * s ^ 14
    - 3540547822834 * s ^ 13
    + 1604429838777 * s ^ 12
    - 444703126368 * s ^ 11
    - 41291991857 * s ^ 10
    + 142356916810 * s ^ 9
    - 101441390557 * s ^ 8
    + 45099747604 * s ^ 7
    - 12757662080 * s ^ 6
    + 1636049682 * s ^ 5
    + 298956174 * s ^ 4
    - 161893298 * s ^ 3
    + 20795912 * s ^ 2
    - 753321 * s
    - 1308

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient20 (s : ℚ) : ℚ :=
  -s ^ 44
    + 73 * s ^ 43
    - 2209 * s ^ 42
    + 39171 * s ^ 41
    - 471714 * s ^ 40
    + 4193854 * s ^ 39
    - 29087693 * s ^ 38
    + 163839840 * s ^ 37
    - 773062152 * s ^ 36
    + 3129082975 * s ^ 35
    - 11040119270 * s ^ 34
    + 34176583363 * s ^ 33
    - 92440604776 * s ^ 32
    + 215081753367 * s ^ 31
    - 417724198130 * s ^ 30
    + 637426299649 * s ^ 29
    - 640472046759 * s ^ 28
    + 2342897263 * s ^ 27
    + 1684072654833 * s ^ 26
    - 4345988588261 * s ^ 25
    + 7018754795774 * s ^ 24
    - 7991574459765 * s ^ 23
    + 5722464167218 * s ^ 22
    - 47791781397 * s ^ 21
    - 7309785531634 * s ^ 20
    + 13615050160679 * s ^ 19
    - 16792116310937 * s ^ 18
    + 16451560451674 * s ^ 17
    - 13601972841372 * s ^ 16
    + 9651784519442 * s ^ 15
    - 5683522383696 * s ^ 14
    + 2421469288128 * s ^ 13
    - 334146627579 * s ^ 12
    - 555928447099 * s ^ 11
    + 658454105093 * s ^ 10
    - 449754379491 * s ^ 9
    + 221259874769 * s ^ 8
    - 77040789228 * s ^ 7
    + 15449090081 * s ^ 6
    + 556886071 * s ^ 5
    - 1495114348 * s ^ 4
    + 444395521 * s ^ 3
    - 49917528 * s ^ 2
    + 1680443 * s
    + 5758

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient21 (s : ℚ) : ℚ :=
  3 * s ^ 43
    - 153 * s ^ 42
    + 3559 * s ^ 41
    - 50825 * s ^ 40
    + 505662 * s ^ 39
    - 3777580 * s ^ 38
    + 22414441 * s ^ 37
    - 111295042 * s ^ 36
    + 488023099 * s ^ 35
    - 1982155865 * s ^ 34
    + 7623136638 * s ^ 33
    - 27408813992 * s ^ 32
    + 89232676798 * s ^ 31
    - 255086241894 * s ^ 30
    + 626168758050 * s ^ 29
    - 1297285520957 * s ^ 28
    + 2223230645505 * s ^ 27
    - 3035390850514 * s ^ 26
    + 2975752261452 * s ^ 25
    - 1150105698866 * s ^ 24
    - 2896957941303 * s ^ 23
    + 8614402393615 * s ^ 22
    - 14387641519012 * s ^ 21
    + 18267306259801 * s ^ 20
    - 19088134501581 * s ^ 19
    + 17039953730183 * s ^ 18
    - 13229942047909 * s ^ 17
    + 8822203095540 * s ^ 16
    - 4575250179066 * s ^ 15
    + 990838987142 * s ^ 14
    + 1422125201983 * s ^ 13
    - 2376257696700 * s ^ 12
    + 2170121846143 * s ^ 11
    - 1462002139546 * s ^ 10
    + 770696728319 * s ^ 9
    - 308380457390 * s ^ 8
    + 79542360056 * s ^ 7
    - 2559628324 * s ^ 6
    - 8498130748 * s ^ 5
    + 4154498279 * s ^ 4
    - 959360342 * s ^ 3
    + 97488032 * s ^ 2
    - 2987803 * s
    - 18888

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient22 (s : ℚ) : ℚ :=
  -2 * s ^ 42
    + 65 * s ^ 41
    - 692 * s ^ 40
    - 2342 * s ^ 39
    + 158421 * s ^ 38
    - 2332143 * s ^ 37
    + 21336555 * s ^ 36
    - 141677756 * s ^ 35
    + 723372142 * s ^ 34
    - 2906829689 * s ^ 33
    + 9196404858 * s ^ 32
    - 22199323618 * s ^ 31
    + 36096474110 * s ^ 30
    - 13262940320 * s ^ 29
    - 153330034901 * s ^ 28
    + 665548750203 * s ^ 27
    - 1779193410103 * s ^ 26
    + 3657991793599 * s ^ 25
    - 6169268756857 * s ^ 24
    + 8766511018215 * s ^ 23
    - 10613164888935 * s ^ 22
    + 10978000794625 * s ^ 21
    - 9690572294542 * s ^ 20
    + 7246567229402 * s ^ 19
    - 4384187027009 * s ^ 18
    + 1556672619893 * s ^ 17
    + 1138750680772 * s ^ 16
    - 3583278535731 * s ^ 15
    + 5317561469271 * s ^ 14
    - 5777497227247 * s ^ 13
    + 4921444279870 * s ^ 12
    - 3378062748844 * s ^ 11
    + 1886471036470 * s ^ 10
    - 828970364458 * s ^ 9
    + 245677142653 * s ^ 8
    - 11549471565 * s ^ 7
    - 36873482815 * s ^ 6
    + 24075831154 * s ^ 5
    - 8362922828 * s ^ 4
    + 1664885872 * s ^ 3
    - 155209214 * s ^ 2
    + 4155773 * s
    + 47688

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient23 (s : ℚ) : ℚ :=
  -2 * s ^ 41
    + 133 * s ^ 40
    - 3877 * s ^ 39
    + 68499 * s ^ 38
    - 840914 * s ^ 37
    + 7733572 * s ^ 36
    - 55825901 * s ^ 35
    + 326137781 * s ^ 34
    - 1573956875 * s ^ 33
    + 6362954821 * s ^ 32
    - 21752451161 * s ^ 31
    + 63278146826 * s ^ 30
    - 157194272911 * s ^ 29
    + 333708267175 * s ^ 28
    - 603565126390 * s ^ 27
    + 921377968804 * s ^ 26
    - 1159789641130 * s ^ 25
    + 1129057157099 * s ^ 24
    - 657692914997 * s ^ 23
    - 291342071302 * s ^ 22
    + 1544644402016 * s ^ 21
    - 2794446916101 * s ^ 20
    + 3848076235146 * s ^ 19
    - 4822616199430 * s ^ 18
    + 5995581600056 * s ^ 17
    - 7391203190780 * s ^ 16
    + 8529111986156 * s ^ 15
    - 8671171962260 * s ^ 14
    + 7464251232748 * s ^ 13
    - 5336823976373 * s ^ 12
    + 3131702557880 * s ^ 11
    - 1447190039851 * s ^ 10
    + 433953752414 * s ^ 9
    + 23882610329 * s ^ 8
    - 134805776462 * s ^ 7
    + 99362665309 * s ^ 6
    - 44370294760 * s ^ 5
    + 13055967448 * s ^ 4
    - 2342039554 * s ^ 3
    + 200448254 * s ^ 2
    - 4297138 * s
    - 94297

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient24 (s : ℚ) : ℚ :=
  3 * s ^ 40
    - 153 * s ^ 39
    + 3699 * s ^ 38
    - 56911 * s ^ 37
    + 630068 * s ^ 36
    - 5369186 * s ^ 35
    + 36694855 * s ^ 34
    - 206471466 * s ^ 33
    + 973140619 * s ^ 32
    - 3888516189 * s ^ 31
    + 13294261628 * s ^ 30
    - 39185304544 * s ^ 29
    + 100252318842 * s ^ 28
    - 224047678750 * s ^ 27
    + 440239149938 * s ^ 26
    - 766056288089 * s ^ 25
    + 1189910417549 * s ^ 24
    - 1664270128714 * s ^ 23
    + 2121346493230 * s ^ 22
    - 2527170772058 * s ^ 21
    + 2963246719859 * s ^ 20
    - 3646166342561 * s ^ 19
    + 4774062526732 * s ^ 18
    - 6259189413428 * s ^ 17
    + 7600746202651 * s ^ 16
    - 8093266750518 * s ^ 15
    + 7302301555113 * s ^ 14
    - 5446266369184 * s ^ 13
    + 3261476454537 * s ^ 12
    - 1441822381862 * s ^ 11
    + 273519788666 * s ^ 10
    + 283928645812 * s ^ 9
    - 406010594029 * s ^ 8
    + 305464776018 * s ^ 7
    - 160573602584 * s ^ 6
    + 61048747716 * s ^ 5
    - 16186980051 * s ^ 4
    + 2668600185 * s ^ 3
    - 207047855 * s ^ 2
    + 2793466 * s
    + 146946

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient25 (s : ℚ) : ℚ :=
  -s ^ 39
    + 44 * s ^ 38
    - 944 * s ^ 37
    + 13340 * s ^ 36
    - 140626 * s ^ 35
    + 1175800 * s ^ 34
    - 8027520 * s ^ 33
    + 45339451 * s ^ 32
    - 213338113 * s ^ 31
    + 841192145 * s ^ 30
    - 2795731324 * s ^ 29
    + 7871453669 * s ^ 28
    - 18821554025 * s ^ 27
    + 38124503142 * s ^ 26
    - 64572746696 * s ^ 25
    + 87510388487 * s ^ 24
    - 78611827693 * s ^ 23
    - 20005550545 * s ^ 22
    + 306008879075 * s ^ 21
    - 897807997108 * s ^ 20
    + 1852333199455 * s ^ 19
    - 3046528161805 * s ^ 18
    + 4131825923373 * s ^ 17
    - 4652811463378 * s ^ 16
    + 4301454923501 * s ^ 15
    - 3151058696655 * s ^ 14
    + 1651077483587 * s ^ 13
    - 325197268726 * s ^ 12
    - 539770526462 * s ^ 11
    + 921746490979 * s ^ 10
    - 923464968811 * s ^ 9
    + 697045480210 * s ^ 8
    - 411238419805 * s ^ 7
    + 188524732466 * s ^ 6
    - 65247257502 * s ^ 5
    + 16016687124 * s ^ 4
    - 2439894317 * s ^ 3
    + 165934721 * s ^ 2
    - 48920 * s
    - 179593

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient26 (s : ℚ) : ℚ :=
  22 * s ^ 36
    - 919 * s ^ 35
    + 18005 * s ^ 34
    - 220477 * s ^ 33
    + 1899488 * s ^ 32
    - 12310215 * s ^ 31
    + 62817021 * s ^ 30
    - 261660353 * s ^ 29
    + 918515946 * s ^ 28
    - 2800780910 * s ^ 27
    + 7645178067 * s ^ 26
    - 19245324512 * s ^ 25
    + 45787723341 * s ^ 24
    - 103855856252 * s ^ 23
    + 221409021338 * s ^ 22
    - 430596087966 * s ^ 21
    + 740636752254 * s ^ 20
    - 1099394756950 * s ^ 19
    + 1378095139839 * s ^ 18
    - 1410521604944 * s ^ 17
    + 1081139568554 * s ^ 16
    - 417146407469 * s ^ 15
    - 390001307140 * s ^ 14
    + 1086109223298 * s ^ 13
    - 1505712134501 * s ^ 12
    + 1620401612273 * s ^ 11
    - 1474965837547 * s ^ 10
    + 1145493969536 * s ^ 9
    - 745770147447 * s ^ 8
    + 397462562089 * s ^ 7
    - 168607693791 * s ^ 6
    + 54623619412 * s ^ 5
    - 12549947195 * s ^ 4
    + 1753028969 * s ^ 3
    - 96202908 * s ^ 2
    - 2536642 * s
    + 168686

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient27 (s : ℚ) : ℚ :=
  s ^ 36
    - 46 * s ^ 35
    + 965 * s ^ 34
    - 12221 * s ^ 33
    + 103673 * s ^ 32
    - 611213 * s ^ 31
    + 2436969 * s ^ 30
    - 5190496 * s ^ 29
    - 8504589 * s ^ 28
    + 138304420 * s ^ 27
    - 752604158 * s ^ 26
    + 2865925483 * s ^ 25
    - 8577998553 * s ^ 24
    + 20815082998 * s ^ 23
    - 40793762397 * s ^ 22
    + 62203583049 * s ^ 21
    - 64741592057 * s ^ 20
    + 13695999703 * s ^ 19
    + 129390133837 * s ^ 18
    - 386712461242 * s ^ 17
    + 742023227502 * s ^ 16
    - 1130561315040 * s ^ 15
    + 1460327407863 * s ^ 14
    - 1658304943527 * s ^ 13
    + 1695654197640 * s ^ 12
    - 1571368321140 * s ^ 11
    + 1301089946016 * s ^ 10
    - 937445082727 * s ^ 9
    + 571714035187 * s ^ 8
    - 287487639816 * s ^ 7
    + 115598973455 * s ^ 6
    - 35467556799 * s ^ 5
    + 7622177636 * s ^ 4
    - 949443006 * s ^ 3
    + 31988796 * s ^ 2
    + 3629420 * s
    - 115586

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient28 (s : ℚ) : ℚ :=
  -3 * s ^ 34
    + 139 * s ^ 33
    - 3028 * s ^ 32
    + 41342 * s ^ 31
    - 398282 * s ^ 30
    + 2894821 * s ^ 29
    - 16616657 * s ^ 28
    + 78106187 * s ^ 27
    - 310248652 * s ^ 26
    + 1070058982 * s ^ 25
    - 3270686351 * s ^ 24
    + 8960052742 * s ^ 23
    - 22074330331 * s ^ 22
    + 48924952555 * s ^ 21
    - 97792646696 * s ^ 20
    + 177367918182 * s ^ 19
    - 294008741606 * s ^ 18
    + 447386443888 * s ^ 17
    - 625571143208 * s ^ 16
    + 804582504090 * s ^ 15
    - 955344060896 * s ^ 14
    + 1050370251770 * s ^ 13
    - 1063441556193 * s ^ 12
    + 974054846451 * s ^ 11
    - 787301549739 * s ^ 10
    + 547888969005 * s ^ 9
    - 321177797987 * s ^ 8
    + 155020709884 * s ^ 7
    - 59676385439 * s ^ 6
    + 17362668249 * s ^ 5
    - 3437626539 * s ^ 4
    + 352658636 * s ^ 3
    + 3713622 * s ^ 2
    - 3048219 * s
    + 49281

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient29 (s : ℚ) : ℚ :=
  4 * s ^ 32
    - 184 * s ^ 31
    + 4000 * s ^ 30
    - 54698 * s ^ 29
    + 528527 * s ^ 28
    - 3846032 * s ^ 27
    + 21962714 * s ^ 26
    - 101461740 * s ^ 25
    + 389029351 * s ^ 24
    - 1267982515 * s ^ 23
    + 3595059737 * s ^ 22
    - 9050166556 * s ^ 21
    + 20525634497 * s ^ 20
    - 42219035863 * s ^ 19
    + 78808907688 * s ^ 18
    - 133454702183 * s ^ 17
    + 205504201874 * s ^ 16
    - 289033470897 * s ^ 15
    + 371819461846 * s ^ 14
    - 434664984025 * s ^ 13
    + 455105064136 * s ^ 12
    - 419127796566 * s ^ 11
    + 333747390889 * s ^ 10
    - 226363641426 * s ^ 9
    + 128750542546 * s ^ 8
    - 60084576385 * s ^ 7
    + 22176739892 * s ^ 6
    - 6049076559 * s ^ 5
    + 1050078997 * s ^ 4
    - 63639272 * s ^ 3
    - 11878606 * s ^ 2
    + 1709229 * s
    - 2420

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient30 (s : ℚ) : ℚ :=
  -3 * s ^ 30
    + 139 * s ^ 29
    - 3059 * s ^ 28
    + 42538 * s ^ 27
    - 419524 * s ^ 26
    + 3123057 * s ^ 25
    - 18244976 * s ^ 24
    + 85928946 * s ^ 23
    - 333038534 * s ^ 22
    + 1080984087 * s ^ 21
    - 2987900409 * s ^ 20
    + 7153752829 * s ^ 19
    - 15090379394 * s ^ 18
    + 28455312518 * s ^ 17
    - 48364217713 * s ^ 16
    + 74063784867 * s ^ 15
    - 101368659566 * s ^ 14
    + 122538213980 * s ^ 13
    - 129306712920 * s ^ 12
    + 117960857033 * s ^ 11
    - 92267011939 * s ^ 10
    + 61298935971 * s ^ 9
    - 34070942926 * s ^ 8
    + 15416021130 * s ^ 7
    - 5398507653 * s ^ 6
    + 1318403047 * s ^ 5
    - 162806842 * s ^ 4
    - 13294187 * s ^ 3
    + 7409213 * s ^ 2
    - 615715 * s
    - 13995

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient31 (s : ℚ) : ℚ :=
  s ^ 28
    - 47 * s ^ 27
    + 1055 * s ^ 26
    - 15040 * s ^ 25
    + 152744 * s ^ 24
    - 1175039 * s ^ 23
    + 7108425 * s ^ 22
    - 34659717 * s ^ 21
    + 138542184 * s ^ 20
    - 459509688 * s ^ 19
    + 1275859186 * s ^ 18
    - 2985406990 * s ^ 17
    + 5918131465 * s ^ 16
    - 9983229842 * s ^ 15
    + 14387793373 * s ^ 14
    - 17780331124 * s ^ 13
    + 18896272541 * s ^ 12
    - 17286554840 * s ^ 11
    + 13565178609 * s ^ 10
    - 9026281983 * s ^ 9
    + 4968693201 * s ^ 8
    - 2159305128 * s ^ 7
    + 672720150 * s ^ 6
    - 110785108 * s ^ 5
    - 12805505 * s ^ 4
    + 11933224 * s ^ 3
    - 2446888 * s ^ 2
    + 109570 * s
    + 11211

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient32 (s : ℚ) : ℚ :=
  -s ^ 24
    + 41 * s ^ 23
    - 794 * s ^ 22
    + 9653 * s ^ 21
    - 82598 * s ^ 20
    + 528658 * s ^ 19
    - 2626045 * s ^ 18
    + 10369399 * s ^ 17
    - 33073451 * s ^ 16
    + 86110878 * s ^ 15
    - 184169235 * s ^ 14
    + 324340362 * s ^ 13
    - 469496208 * s ^ 12
    + 554623759 * s ^ 11
    - 526583128 * s ^ 10
    + 389914267 * s ^ 9
    - 210846067 * s ^ 8
    + 67969065 * s ^ 7
    + 2889747 * s ^ 6
    - 17511836 * s ^ 5
    + 10259145 * s ^ 4
    - 3016115 * s ^ 3
    + 385389 * s ^ 2
    + 9741 * s
    - 4626

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient33 (s : ℚ) : ℚ :=
  s ^ 19
    - 34 * s ^ 18
    + 537 * s ^ 17
    - 5230 * s ^ 16
    + 35165 * s ^ 15
    - 173183 * s ^ 14
    + 646869 * s ^ 13
    - 1872180 * s ^ 12
    + 4253286 * s ^ 11
    - 7637865 * s ^ 10
    + 10864789 * s ^ 9
    - 12210774 * s ^ 8
    + 10747878 * s ^ 7
    - 7269163 * s ^ 6
    + 3634203 * s ^ 5
    - 1236646 * s ^ 4
    + 228532 * s ^ 3
    + 1741 * s ^ 2
    - 8988 * s
    + 1062

/-- Coefficient of the indicated power of the raw chart variable. -/
def termThreeCoefficient34 (s : ℚ) : ℚ :=
  -s ^ 12
    + 23 * s ^ 11
    - 235 * s ^ 10
    + 1406 * s ^ 9
    - 5467 * s ^ 8
    + 14498 * s ^ 7
    - 26771 * s ^ 6
    + 34508 * s ^ 5
    - 30628 * s ^ 4
    + 18103 * s ^ 3
    - 6678 * s ^ 2
    + 1350 * s
    - 108

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
    termThreeCoefficient34 s * r ^ 34

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_0 (s : ℚ) :
    termThreeCoefficient0 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient0,
    t3Step2Coefficient0,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_1 (s : ℚ) :
    termThreeCoefficient1 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient1,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_2 (s : ℚ) :
    termThreeCoefficient2 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient2,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_3 (s : ℚ) :
    termThreeCoefficient3 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient3,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_4 (s : ℚ) :
    termThreeCoefficient4 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient4,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_5 (s : ℚ) :
    termThreeCoefficient5 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient5,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_6 (s : ℚ) :
    termThreeCoefficient6 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient0 s
    := by
  simp only [termThreeCoefficient6,
    t3Step2Coefficient0,
    t3Step2Coefficient1,
    t3Step2Coefficient2,
    t3Step2Coefficient3,
    t3Step2Coefficient4,
    t3Step2Coefficient5,
    t3Step2Coefficient6,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2,
    rawUnitTwoDenominatorCoefficient1,
    rawUnitTwoDenominatorCoefficient0]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_7 (s : ℚ) :
    termThreeCoefficient7 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_8 (s : ℚ) :
    termThreeCoefficient8 s =
    t3Step2Coefficient0 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_9 (s : ℚ) :
    termThreeCoefficient9 s =
    t3Step2Coefficient1 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_10 (s : ℚ) :
    termThreeCoefficient10 s =
    t3Step2Coefficient2 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_11 (s : ℚ) :
    termThreeCoefficient11 s =
    t3Step2Coefficient3 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_12 (s : ℚ) :
    termThreeCoefficient12 s =
    t3Step2Coefficient4 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_13 (s : ℚ) :
    termThreeCoefficient13 s =
    t3Step2Coefficient5 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_14 (s : ℚ) :
    termThreeCoefficient14 s =
    t3Step2Coefficient6 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_15 (s : ℚ) :
    termThreeCoefficient15 s =
    t3Step2Coefficient7 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_16 (s : ℚ) :
    termThreeCoefficient16 s =
    t3Step2Coefficient8 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_17 (s : ℚ) :
    termThreeCoefficient17 s =
    t3Step2Coefficient9 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_18 (s : ℚ) :
    termThreeCoefficient18 s =
    t3Step2Coefficient10 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_19 (s : ℚ) :
    termThreeCoefficient19 s =
    t3Step2Coefficient11 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_20 (s : ℚ) :
    termThreeCoefficient20 s =
    t3Step2Coefficient12 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_21 (s : ℚ) :
    termThreeCoefficient21 s =
    t3Step2Coefficient13 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_22 (s : ℚ) :
    termThreeCoefficient22 s =
    t3Step2Coefficient14 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_23 (s : ℚ) :
    termThreeCoefficient23 s =
    t3Step2Coefficient15 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_24 (s : ℚ) :
    termThreeCoefficient24 s =
    t3Step2Coefficient16 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_25 (s : ℚ) :
    termThreeCoefficient25 s =
    t3Step2Coefficient17 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient0 s
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
theorem termThreeCoefficient_product_certificate_26 (s : ℚ) :
    termThreeCoefficient26 s =
    t3Step2Coefficient18 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient1 s
      + t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient0 s
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
    t3Step2Coefficient26,
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
theorem termThreeCoefficient_product_certificate_27 (s : ℚ) :
    termThreeCoefficient27 s =
    t3Step2Coefficient19 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient2 s
      + t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient1 s
    := by
  simp only [termThreeCoefficient27,
    t3Step2Coefficient19,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    t3Step2Coefficient26,
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
theorem termThreeCoefficient_product_certificate_28 (s : ℚ) :
    termThreeCoefficient28 s =
    t3Step2Coefficient20 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient3 s
      + t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient2 s
    := by
  simp only [termThreeCoefficient28,
    t3Step2Coefficient20,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    t3Step2Coefficient26,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3,
    rawUnitTwoDenominatorCoefficient2]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_29 (s : ℚ) :
    termThreeCoefficient29 s =
    t3Step2Coefficient21 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient4 s
      + t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient3 s
    := by
  simp only [termThreeCoefficient29,
    t3Step2Coefficient21,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    t3Step2Coefficient26,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4,
    rawUnitTwoDenominatorCoefficient3]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_30 (s : ℚ) :
    termThreeCoefficient30 s =
    t3Step2Coefficient22 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient5 s
      + t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient4 s
    := by
  simp only [termThreeCoefficient30,
    t3Step2Coefficient22,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    t3Step2Coefficient26,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5,
    rawUnitTwoDenominatorCoefficient4]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_31 (s : ℚ) :
    termThreeCoefficient31 s =
    t3Step2Coefficient23 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient6 s
      + t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient5 s
    := by
  simp only [termThreeCoefficient31,
    t3Step2Coefficient23,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    t3Step2Coefficient26,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6,
    rawUnitTwoDenominatorCoefficient5]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_32 (s : ℚ) :
    termThreeCoefficient32 s =
    t3Step2Coefficient24 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient7 s
      + t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient6 s
    := by
  simp only [termThreeCoefficient32,
    t3Step2Coefficient24,
    t3Step2Coefficient25,
    t3Step2Coefficient26,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7,
    rawUnitTwoDenominatorCoefficient6]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_33 (s : ℚ) :
    termThreeCoefficient33 s =
    t3Step2Coefficient25 s *
        rawUnitTwoDenominatorCoefficient8 s
      + t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient7 s
    := by
  simp only [termThreeCoefficient33,
    t3Step2Coefficient25,
    t3Step2Coefficient26,
    rawUnitTwoDenominatorCoefficient8,
    rawUnitTwoDenominatorCoefficient7]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem termThreeCoefficient_product_certificate_34 (s : ℚ) :
    termThreeCoefficient34 s =
    t3Step2Coefficient26 s *
        rawUnitTwoDenominatorCoefficient8 s
    := by
  simp only [termThreeCoefficient34,
    t3Step2Coefficient26,
    rawUnitTwoDenominatorCoefficient8]
  ring

/-- Checked staged polynomial-product identity. -/
theorem termThree_eq_t3Step2_mul_rawUnitTwoDenominator (r s : ℚ) :
    termThree r s = t3Step2 r s * rawUnitTwoDenominator r s := by
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
  simp only [termThree, t3Step2, rawUnitTwoDenominator]
  linear_combination
    h0 + r * h1 + r ^ 2 * h2 + r ^ 3 * h3 + r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 +
    r ^ 7 * h7 + r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 + r ^ 12 * h12 +
    r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15 + r ^ 16 * h16 + r ^ 17 * h17 +
    r ^ 18 * h18 + r ^ 19 * h19 + r ^ 20 * h20 + r ^ 21 * h21 + r ^ 22 * h22 +
    r ^ 23 * h23 + r ^ 24 * h24 + r ^ 25 * h25 + r ^ 26 * h26 + r ^ 27 * h27 +
    r ^ 28 * h28 + r ^ 29 * h29 + r ^ 30 * h30 + r ^ 31 * h31 + r ^ 32 * h32 +
    r ^ 33 * h33 + r ^ 34 * h34

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient1 (s : ℚ) : ℚ :=
  s ^ 34
    - 4 * s ^ 33
    + 10 * s ^ 32
    - 18 * s ^ 31
    + 25 * s ^ 30
    - 28 * s ^ 29
    + 25 * s ^ 28
    - 18 * s ^ 27
    + 10 * s ^ 26
    - 4 * s ^ 25
    + s ^ 24

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 37
    - 7 * s ^ 36
    + 29 * s ^ 35
    - 73 * s ^ 34
    + 78 * s ^ 33
    + 67 * s ^ 32
    - 503 * s ^ 31
    + 1258 * s ^ 30
    - 2168 * s ^ 29
    + 2934 * s ^ 28
    - 3240 * s ^ 27
    + 3003 * s ^ 26
    - 2356 * s ^ 25
    + 1578 * s ^ 24
    - 914 * s ^ 23
    + 461 * s ^ 22
    - 210 * s ^ 21
    + 84 * s ^ 20
    - 28 * s ^ 19
    + 7 * s ^ 18
    - s ^ 17

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient3 (s : ℚ) : ℚ :=
  s ^ 39
    - 9 * s ^ 38
    + 58 * s ^ 37
    - 323 * s ^ 36
    + 1387 * s ^ 35
    - 4639 * s ^ 34
    + 11845 * s ^ 33
    - 22925 * s ^ 32
    + 34569 * s ^ 31
    - 39686 * s ^ 30
    + 31239 * s ^ 29
    - 7136 * s ^ 28
    - 27167 * s ^ 27
    + 59807 * s ^ 26
    - 79994 * s ^ 25
    + 82755 * s ^ 24
    - 71000 * s ^ 23
    + 52265 * s ^ 22
    - 33624 * s ^ 21
    + 19282 * s ^ 20
    - 9865 * s ^ 19
    + 4442 * s ^ 18
    - 1710 * s ^ 17
    + 537 * s ^ 16
    - 129 * s ^ 15
    + 22 * s ^ 14
    - 2 * s ^ 13

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient4 (s : ℚ) : ℚ :=
  s ^ 42
    - 13 * s ^ 41
    + 93 * s ^ 40
    - 469 * s ^ 39
    + 1835 * s ^ 38
    - 5901 * s ^ 37
    + 15598 * s ^ 36
    - 32166 * s ^ 35
    + 44543 * s ^ 34
    - 9956 * s ^ 33
    - 151093 * s ^ 32
    + 517332 * s ^ 31
    - 1108147 * s ^ 30
    + 1820405 * s ^ 29
    - 2441671 * s ^ 28
    + 2738102 * s ^ 27
    - 2576653 * s ^ 26
    + 2014042 * s ^ 25
    - 1251873 * s ^ 24
    + 534526 * s ^ 23
    - 27724 * s ^ 22
    - 230362 * s ^ 21
    + 294855 * s ^ 20
    - 255858 * s ^ 19
    + 181945 * s ^ 18
    - 111145 * s ^ 17
    + 58648 * s ^ 16
    - 26363 * s ^ 15
    + 9878 * s ^ 14
    - 3019 * s ^ 13
    + 725 * s ^ 12
    - 130 * s ^ 11
    + 16 * s ^ 10
    - s ^ 9

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient5 (s : ℚ) : ℚ :=
  s ^ 43
    - 8 * s ^ 42
    - 11 * s ^ 41
    + 503 * s ^ 40
    - 4173 * s ^ 39
    + 22352 * s ^ 38
    - 92685 * s ^ 37
    + 319609 * s ^ 36
    - 937722 * s ^ 35
    + 2343597 * s ^ 34
    - 4954831 * s ^ 33
    + 8767099 * s ^ 32
    - 12854019 * s ^ 31
    + 15309013 * s ^ 30
    - 13836367 * s ^ 29
    + 7058638 * s ^ 28
    + 4395439 * s ^ 27
    - 17707117 * s ^ 26
    + 28960808 * s ^ 25
    - 35080379 * s ^ 24
    + 35063547 * s ^ 23
    - 30171241 * s ^ 22
    + 22875571 * s ^ 21
    - 15514526 * s ^ 20
    + 9508714 * s ^ 19
    - 5246780 * s ^ 18
    + 2548184 * s ^ 17
    - 1033430 * s ^ 16
    + 307649 * s ^ 15
    - 34693 * s ^ 14
    - 29083 * s ^ 13
    + 24799 * s ^ 12
    - 11409 * s ^ 11
    + 3700 * s ^ 10
    - 884 * s ^ 9
    + 151 * s ^ 8
    - 17 * s ^ 7
    + s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient6 (s : ℚ) : ℚ :=
  s ^ 45
    - 20 * s ^ 44
    + 217 * s ^ 43
    - 1652 * s ^ 42
    + 9526 * s ^ 41
    - 43466 * s ^ 40
    + 162535 * s ^ 39
    - 510130 * s ^ 38
    + 1357865 * s ^ 37
    - 3028997 * s ^ 36
    + 5369590 * s ^ 35
    - 6332486 * s ^ 34
    - 171176 * s ^ 33
    + 25344419 * s ^ 32
    - 82512957 * s ^ 31
    + 179793547 * s ^ 30
    - 311799139 * s ^ 29
    + 455181510 * s ^ 28
    - 574099582 * s ^ 27
    + 633782991 * s ^ 26
    - 616554092 * s ^ 25
    + 530354886 * s ^ 24
    - 403246712 * s ^ 23
    + 270058638 * s ^ 22
    - 157426319 * s ^ 21
    + 76854965 * s ^ 20
    - 26949086 * s ^ 19
    + 37326 * s ^ 18
    + 11551908 * s ^ 17
    - 13792304 * s ^ 16
    + 11235025 * s ^ 15
    - 7236293 * s ^ 14
    + 3813785 * s ^ 13
    - 1657451 * s ^ 12
    + 590206 * s ^ 11
    - 169606 * s ^ 10
    + 38269 * s ^ 9
    - 6426 * s ^ 8
    + 728 * s ^ 7
    - 43 * s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient7 (s : ℚ) : ℚ :=
  s ^ 46
    - 19 * s ^ 45
    + 169 * s ^ 44
    - 884 * s ^ 43
    + 2239 * s ^ 42
    + 6074 * s ^ 41
    - 100602 * s ^ 40
    + 638688 * s ^ 39
    - 2913785 * s ^ 38
    + 10826958 * s ^ 37
    - 34400874 * s ^ 36
    + 95247022 * s ^ 35
    - 230818052 * s ^ 34
    + 489123742 * s ^ 33
    - 905022918 * s ^ 32
    + 1462328726 * s ^ 31
    - 2065852525 * s ^ 30
    + 2547407404 * s ^ 29
    - 2716705852 * s ^ 28
    + 2446993924 * s ^ 27
    - 1746441227 * s ^ 26
    + 774999818 * s ^ 25
    + 218829184 * s ^ 24
    - 1007219356 * s ^ 23
    + 1466658238 * s ^ 22
    - 1604384106 * s ^ 21
    + 1512949869 * s ^ 20
    - 1300616168 * s ^ 19
    + 1044387200 * s ^ 18
    - 783074022 * s ^ 17
    + 539854592 * s ^ 16
    - 335190746 * s ^ 15
    + 183743740 * s ^ 14
    - 87433968 * s ^ 13
    + 35562775 * s ^ 12
    - 12146009 * s ^ 11
    + 3406154 * s ^ 10
    - 758669 * s ^ 9
    + 126723 * s ^ 8
    - 14277 * s ^ 7
    + 815 * s ^ 6
    + 4 * s ^ 5

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 47
    + 29 * s ^ 46
    - 432 * s ^ 45
    + 4274 * s ^ 44
    - 31361 * s ^ 43
    + 181808 * s ^ 42
    - 866425 * s ^ 41
    + 3492152 * s ^ 40
    - 12172795 * s ^ 39
    + 37283046 * s ^ 38
    - 101093456 * s ^ 37
    + 242192265 * s ^ 36
    - 506763129 * s ^ 35
    + 906355942 * s ^ 34
    - 1332701201 * s ^ 33
    + 1465805876 * s ^ 32
    - 763600240 * s ^ 31
    - 1397322321 * s ^ 30
    + 5455619912 * s ^ 29
    - 11364561519 * s ^ 28
    + 18413391675 * s ^ 27
    - 25343642878 * s ^ 26
    + 30756194784 * s ^ 25
    - 33661546702 * s ^ 24
    + 33831849082 * s ^ 23
    - 31754519322 * s ^ 22
    + 28284950265 * s ^ 21
    - 24187362987 * s ^ 20
    + 19898985133 * s ^ 19
    - 15597857899 * s ^ 18
    + 11432192933 * s ^ 17
    - 7672047850 * s ^ 16
    + 4625117658 * s ^ 15
    - 2464443059 * s ^ 14
    + 1144305990 * s ^ 13
    - 456425537 * s ^ 12
    + 153677174 * s ^ 11
    - 42678163 * s ^ 10
    + 9437968 * s ^ 9
    - 1564653 * s ^ 8
    + 173318 * s ^ 7
    - 9221 * s ^ 6
    - 132 * s ^ 5
    - s ^ 4

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 48
    + 27 * s ^ 47
    - 361 * s ^ 46
    + 3165 * s ^ 45
    - 20268 * s ^ 44
    + 100002 * s ^ 43
    - 388947 * s ^ 42
    + 1182506 * s ^ 41
    - 2590475 * s ^ 40
    + 2255215 * s ^ 39
    + 14091253 * s ^ 38
    - 103232346 * s ^ 37
    + 443349432 * s ^ 36
    - 1488607695 * s ^ 35
    + 4176086450 * s ^ 34
    - 10047758491 * s ^ 33
    + 21066630137 * s ^ 32
    - 39014862244 * s ^ 31
    + 64655406699 * s ^ 30
    - 97010219759 * s ^ 29
    + 133079280280 * s ^ 28
    - 168371362572 * s ^ 27
    + 198290302098 * s ^ 26
    - 219728164556 * s ^ 25
    + 231962895120 * s ^ 24
    - 236066921625 * s ^ 23
    + 233342361614 * s ^ 22
    - 223969734872 * s ^ 21
    + 206800038219 * s ^ 20
    - 180795420566 * s ^ 19
    + 146959700048 * s ^ 18
    - 109185045887 * s ^ 17
    + 73098164948 * s ^ 16
    - 43576845045 * s ^ 15
    + 22885188773 * s ^ 14
    - 10473666089 * s ^ 13
    + 4124148664 * s ^ 12
    - 1373636093 * s ^ 11
    + 377874857 * s ^ 10
    - 82703174 * s ^ 9
    + 13493747 * s ^ 8
    - 1440215 * s ^ 7
    + 65536 * s ^ 6
    + 2481 * s ^ 5
    + 9 * s ^ 4
    + s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient10 (s : ℚ) : ℚ :=
  -2 * s ^ 48
    + 68 * s ^ 47
    - 1114 * s ^ 46
    + 11921 * s ^ 45
    - 94521 * s ^ 44
    + 595494 * s ^ 43
    - 3120595 * s ^ 42
    + 14062557 * s ^ 41
    - 55902854 * s ^ 40
    + 199688781 * s ^ 39
    - 647490025 * s ^ 38
    + 1909460625 * s ^ 37
    - 5103579720 * s ^ 36
    + 12304744580 * s ^ 35
    - 26696352121 * s ^ 34
    + 52219815350 * s ^ 33
    - 92705309933 * s ^ 32
    + 150946494743 * s ^ 31
    - 228250214611 * s ^ 30
    + 324534138877 * s ^ 29
    - 439005775616 * s ^ 28
    + 571548587242 * s ^ 27
    - 723524336748 * s ^ 26
    + 895800482228 * s ^ 25
    - 1083305742722 * s ^ 24
    + 1268424533468 * s ^ 23
    - 1419108422106 * s ^ 22
    + 1495514397731 * s ^ 21
    - 1464677021347 * s ^ 20
    + 1317593642586 * s ^ 19
    - 1077850759661 * s ^ 18
    + 794971622396 * s ^ 17
    - 524661913207 * s ^ 16
    + 307550662648 * s ^ 15
    - 158842952097 * s ^ 14
    + 71592693577 * s ^ 13
    - 27806226656 * s ^ 12
    + 9144124316 * s ^ 11
    - 2481632682 * s ^ 10
    + 533292566 * s ^ 9
    - 84218977 * s ^ 8
    + 8278659 * s ^ 7
    - 229608 * s ^ 6
    - 33708 * s ^ 5
    + 251 * s ^ 4
    - 33 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient11 (s : ℚ) : ℚ :=
  -s ^ 49
    + 32 * s ^ 48
    - 507 * s ^ 47
    + 5340 * s ^ 46
    - 42434 * s ^ 45
    + 273668 * s ^ 44
    - 1502699 * s ^ 43
    + 7252267 * s ^ 42
    - 31331298 * s ^ 41
    + 121938304 * s ^ 40
    - 426424752 * s ^ 39
    + 1331005643 * s ^ 38
    - 3686359479 * s ^ 37
    + 9046611423 * s ^ 36
    - 19785802104 * s ^ 35
    + 39164928009 * s ^ 34
    - 72029634320 * s ^ 33
    + 127234950741 * s ^ 32
    - 222082081895 * s ^ 31
    + 387218109749 * s ^ 30
    - 669642133488 * s ^ 29
    + 1131870311504 * s ^ 28
    - 1843098632719 * s ^ 27
    + 2855434754668 * s ^ 26
    - 4164848860429 * s ^ 25
    + 5670532456574 * s ^ 24
    - 7158377032498 * s ^ 23
    + 8333394267765 * s ^ 22
    - 8903220963086 * s ^ 21
    + 8688100116586 * s ^ 20
    - 7706715465714 * s ^ 19
    + 6183568705281 * s ^ 18
    - 4465144595781 * s ^ 17
    + 2886086254920 * s ^ 16
    - 1659360592030 * s ^ 15
    + 842213429684 * s ^ 14
    - 373668950628 * s ^ 13
    + 142981727063 * s ^ 12
    - 46285344781 * s ^ 11
    + 12314041921 * s ^ 10
    - 2564299542 * s ^ 9
    + 379966308 * s ^ 8
    - 30755049 * s ^ 7
    - 619761 * s ^ 6
    + 321602 * s ^ 5
    - 4453 * s ^ 4
    + 392 * s ^ 3
    + 4 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient12 (s : ℚ) : ℚ :=
  3 * s ^ 48
    - 66 * s ^ 47
    + 585 * s ^ 46
    - 1453 * s ^ 45
    - 23488 * s ^ 44
    + 343726 * s ^ 43
    - 2618518 * s ^ 42
    + 14031568 * s ^ 41
    - 57066380 * s ^ 40
    + 180549627 * s ^ 39
    - 447616798 * s ^ 38
    + 890702952 * s ^ 37
    - 1664920016 * s ^ 36
    + 4387975664 * s ^ 35
    - 16825236024 * s ^ 34
    + 63544108348 * s ^ 33
    - 203450128614 * s ^ 32
    + 551661517281 * s ^ 31
    - 1300276436867 * s ^ 30
    + 2729117030272 * s ^ 29
    - 5187407629473 * s ^ 28
    + 9015591001370 * s ^ 27
    - 14390572697045 * s ^ 26
    + 21129064918456 * s ^ 25
    - 28539228253888 * s ^ 24
    + 35433518798723 * s ^ 23
    - 40374199179496 * s ^ 22
    + 42117144504504 * s ^ 21
    - 40098089531476 * s ^ 20
    + 34715350015746 * s ^ 19
    - 27220164710495 * s ^ 18
    + 19243360647089 * s ^ 17
    - 12202172808109 * s ^ 16
    + 6896012540553 * s ^ 15
    - 3445574226802 * s ^ 14
    + 1505752967866 * s ^ 13
    - 566908003968 * s ^ 12
    + 179860425855 * s ^ 11
    - 46438377362 * s ^ 10
    + 9157417947 * s ^ 9
    - 1191527941 * s ^ 8
    + 50266976 * s ^ 7
    + 13321348 * s ^ 6
    - 2114810 * s ^ 5
    + 24920 * s ^ 4
    - 2209 * s ^ 3
    - 80 * s ^ 2
    - s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient13 (s : ℚ) : ℚ :=
  3 * s ^ 48
    - 99 * s ^ 47
    + 1488 * s ^ 46
    - 13445 * s ^ 45
    + 77680 * s ^ 44
    - 247601 * s ^ 43
    - 208129 * s ^ 42
    + 7804672 * s ^ 41
    - 51498950 * s ^ 40
    + 199917236 * s ^ 39
    - 419956424 * s ^ 38
    - 415068276 * s ^ 37
    + 8268123258 * s ^ 36
    - 44073382839 * s ^ 35
    + 165181637835 * s ^ 34
    - 502737780289 * s ^ 33
    + 1317914870462 * s ^ 32
    - 3076060806255 * s ^ 31
    + 6523501116982 * s ^ 30
    - 12714977063160 * s ^ 29
    + 22893332337449 * s ^ 28
    - 38126619812831 * s ^ 27
    + 58713964906754 * s ^ 26
    - 83540827115313 * s ^ 25
    + 109702760729976 * s ^ 24
    - 132744636767024 * s ^ 23
    + 147691196772354 * s ^ 22
    - 150669880152640 * s ^ 21
    + 140485862426727 * s ^ 20
    - 119295002210998 * s ^ 19
    + 91892702856192 * s ^ 18
    - 63923727812068 * s ^ 17
    + 39941202328534 * s ^ 16
    - 22263618242406 * s ^ 15
    + 10972705069471 * s ^ 14
    - 4723337481665 * s ^ 13
    + 1744663441536 * s ^ 12
    - 538217150157 * s ^ 11
    + 132413884087 * s ^ 10
    - 23577486764 * s ^ 9
    + 2205142723 * s ^ 8
    + 176223199 * s ^ 7
    - 88991467 * s ^ 6
    + 9563782 * s ^ 5
    + 10594 * s ^ 4
    + 5161 * s ^ 3
    + 617 * s ^ 2
    + 28 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient14 (s : ℚ) : ℚ :=
  2 * s ^ 48
    - 88 * s ^ 47
    + 1734 * s ^ 46
    - 20590 * s ^ 45
    + 162278 * s ^ 44
    - 830501 * s ^ 43
    + 1847455 * s ^ 42
    + 12129907 * s ^ 41
    - 171982880 * s ^ 40
    + 1203139785 * s ^ 39
    - 6189613338 * s ^ 38
    + 25833816537 * s ^ 37
    - 91613114930 * s ^ 36
    + 284426243442 * s ^ 35
    - 790991888471 * s ^ 34
    + 2006375093011 * s ^ 33
    - 4702147943631 * s ^ 32
    + 10255105507933 * s ^ 31
    - 20856020261268 * s ^ 30
    + 39505108429945 * s ^ 29
    - 69538795624979 * s ^ 28
    + 113531797872648 * s ^ 27
    - 171694813861350 * s ^ 26
    + 240253270151261 * s ^ 25
    - 310636763077820 * s ^ 24
    + 370403019035931 * s ^ 23
    - 406317874004006 * s ^ 22
    + 408868412361272 * s ^ 21
    - 376242233029001 * s ^ 20
    + 315526036359762 * s ^ 19
    - 240221824452917 * s ^ 18
    + 165274706604541 * s ^ 17
    - 102164941091289 * s ^ 16
    + 56312940242523 * s ^ 15
    - 27394865381934 * s ^ 14
    + 11591055573597 * s ^ 13
    - 4172255734719 * s ^ 12
    + 1232011093638 * s ^ 11
    - 277886609454 * s ^ 10
    + 39189452624 * s ^ 9
    + 156290763 * s ^ 8
    - 1613511577 * s ^ 7
    + 370426083 * s ^ 6
    - 28824808 * s ^ 5
    - 976494 * s ^ 4
    + 956 * s ^ 3
    - 1210 * s ^ 2
    - 373 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient15 (s : ℚ) : ℚ :=
  3 * s ^ 48
    - 156 * s ^ 47
    + 3847 * s ^ 46
    - 60449 * s ^ 45
    + 684961 * s ^ 44
    - 5991025 * s ^ 43
    + 42209950 * s ^ 42
    - 246747941 * s ^ 41
    + 1224419186 * s ^ 40
    - 5260244645 * s ^ 39
    + 19934415784 * s ^ 38
    - 67879404086 * s ^ 37
    + 211345193688 * s ^ 36
    - 610374724820 * s ^ 35
    + 1649655291862 * s ^ 34
    - 4182673959098 * s ^ 33
    + 9924881574666 * s ^ 32
    - 21942350911971 * s ^ 31
    + 45022607103942 * s ^ 30
    - 85546903154643 * s ^ 29
    + 150426313406451 * s ^ 28
    - 244816031058219 * s ^ 27
    + 368761231855373 * s ^ 26
    - 513730010208292 * s ^ 25
    + 660941133908347 * s ^ 24
    - 783648006580634 * s ^ 23
    + 854172690211741 * s ^ 22
    - 853668827496782 * s ^ 21
    + 780050460938972 * s ^ 20
    - 649615934322005 * s ^ 19
    + 491155523899489 * s ^ 18
    - 335490352514089 * s ^ 17
    + 205690614746608 * s ^ 16
    - 112197490658749 * s ^ 15
    + 53772491534322 * s ^ 14
    - 22222707093168 * s ^ 13
    + 7681836624597 * s ^ 12
    - 2097448795121 * s ^ 11
    + 390760660190 * s ^ 10
    - 18901835417 * s ^ 9
    - 16713839847 * s ^ 8
    + 6377819274 * s ^ 7
    - 1062346724 * s ^ 6
    + 48697945 * s ^ 5
    + 6701418 * s ^ 4
    + 60295 * s ^ 3
    - 18178 * s ^ 2
    + 3148 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient16 (s : ℚ) : ℚ :=
  s ^ 49
    - 46 * s ^ 48
    + 1037 * s ^ 47
    - 15227 * s ^ 46
    + 163642 * s ^ 45
    - 1373684 * s ^ 44
    + 9407875 * s ^ 43
    - 54384621 * s ^ 42
    + 273571316 * s ^ 41
    - 1232863243 * s ^ 40
    + 5108660073 * s ^ 39
    - 19820340253 * s ^ 38
    + 72447578733 * s ^ 37
    - 248357924023 * s ^ 36
    + 790924008562 * s ^ 35
    - 2319477178324 * s ^ 34
    + 6231947377267 * s ^ 33
    - 15321743564694 * s ^ 32
    + 34527017649277 * s ^ 31
    - 71536712582673 * s ^ 30
    + 136719574820882 * s ^ 29
    - 241598489230892 * s ^ 28
    + 395125543740328 * s ^ 27
    - 597805744108321 * s ^ 26
    + 835496519663165 * s ^ 25
    - 1076593468810242 * s ^ 24
    + 1276390712335379 * s ^ 23
    - 1389430680635266 * s ^ 22
    + 1385708173319700 * s ^ 21
    - 1263021395574375 * s ^ 20
    + 1048807794532655 * s ^ 19
    - 790183912158255 * s ^ 18
    + 537104280339700 * s ^ 17
    - 326812193062261 * s ^ 16
    + 176055700544908 * s ^ 15
    - 82593541764128 * s ^ 14
    + 32851242656325 * s ^ 13
    - 10542285568821 * s ^ 12
    + 2419576406732 * s ^ 11
    - 214132290288 * s ^ 10
    - 113338745545 * s ^ 9
    + 64263811957 * s ^ 8
    - 16602819976 * s ^ 7
    + 2088916843 * s ^ 6
    + 11397457 * s ^ 5
    - 24826518 * s ^ 4
    - 1269152 * s ^ 3
    + 205915 * s ^ 2
    - 18901 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient17 (s : ℚ) : ℚ :=
  -2 * s ^ 48
    + 78 * s ^ 47
    - 1412 * s ^ 46
    + 15005 * s ^ 45
    - 90064 * s ^ 44
    + 51920 * s ^ 43
    + 5342905 * s ^ 42
    - 68998196 * s ^ 41
    + 556708964 * s ^ 40
    - 3436651366 * s ^ 39
    + 17386997402 * s ^ 38
    - 74690211961 * s ^ 37
    + 278726065392 * s ^ 36
    - 919141446498 * s ^ 35
    + 2715944564976 * s ^ 34
    - 7275449201414 * s ^ 33
    + 17836460177107 * s ^ 32
    - 40296868179963 * s ^ 31
    + 84241012344254 * s ^ 30
    - 163182176960984 * s ^ 29
    + 292708488769538 * s ^ 28
    - 485331704562384 * s ^ 27
    + 742321906823476 * s ^ 26
    - 1045477050922141 * s ^ 25
    + 1353903507069436 * s ^ 24
    - 1610243987414562 * s ^ 23
    + 1756630940426691 * s ^ 22
    - 1754833172424086 * s ^ 21
    + 1601438491612503 * s ^ 20
    - 1330381044451193 * s ^ 19
    + 1001049581786502 * s ^ 18
    - 677434561049609 * s ^ 17
    + 408132348220653 * s ^ 16
    - 215610442955115 * s ^ 15
    + 97443137780692 * s ^ 14
    - 35981154718002 * s ^ 13
    + 9718336008804 * s ^ 12
    - 1131988604435 * s ^ 11
    - 562666896390 * s ^ 10
    + 424501107679 * s ^ 9
    - 149428802536 * s ^ 8
    + 30425802293 * s ^ 7
    - 2459103675 * s ^ 6
    - 322908432 * s ^ 5
    + 50501569 * s ^ 4
    + 9499479 * s ^ 3
    - 1208809 * s ^ 2
    + 85911 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient18 (s : ℚ) : ℚ :=
  -2 * s ^ 48
    + 99 * s ^ 47
    - 2398 * s ^ 46
    + 37890 * s ^ 45
    - 439125 * s ^ 44
    + 3979462 * s ^ 43
    - 29365159 * s ^ 42
    + 181554726 * s ^ 41
    - 961497759 * s ^ 40
    + 4444033209 * s ^ 39
    - 18233194074 * s ^ 38
    + 67463875959 * s ^ 37
    - 228334602990 * s ^ 36
    + 714957230409 * s ^ 35
    - 2085663518763 * s ^ 34
    + 5680587085154 * s ^ 33
    - 14417321038311 * s ^ 32
    + 33953570099679 * s ^ 31
    - 73856929594437 * s ^ 30
    + 147837289204545 * s ^ 29
    - 271682943586401 * s ^ 28
    + 457953447401203 * s ^ 27
    - 708085859838079 * s ^ 26
    + 1004807717182187 * s ^ 25
    - 1309224801743529 * s ^ 24
    + 1566289202261057 * s ^ 23
    - 1719094035650873 * s ^ 22
    + 1727736007596864 * s ^ 21
    - 1584965077047860 * s ^ 20
    + 1320874050249244 * s ^ 19
    - 993238829805246 * s ^ 18
    + 667351538142537 * s ^ 17
    - 394817118880570 * s ^ 16
    + 200784630983179 * s ^ 15
    - 83845709163573 * s ^ 14
    + 25664799839089 * s ^ 13
    - 3232933289640 * s ^ 12
    - 2222773100787 * s ^ 11
    + 1957744716593 * s ^ 10
    - 866442581605 * s ^ 9
    + 243365148898 * s ^ 8
    - 38236759610 * s ^ 7
    + 356310088 * s ^ 6
    + 921141298 * s ^ 5
    - 3579863 * s ^ 4
    - 44440312 * s ^ 3
    + 4954625 * s ^ 2
    - 307028 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient19 (s : ℚ) : ℚ :=
  2 * s ^ 47
    - 85 * s ^ 46
    + 1735 * s ^ 45
    - 22285 * s ^ 44
    + 195982 * s ^ 43
    - 1161889 * s ^ 42
    + 3507728 * s ^ 41
    + 13817870 * s ^ 40
    - 286050165 * s ^ 39
    + 2415027945 * s ^ 38
    - 14691914386 * s ^ 37
    + 72013052291 * s ^ 36
    - 297523802196 * s ^ 35
    + 1061621637348 * s ^ 34
    - 3322652634478 * s ^ 33
    + 9223181442606 * s ^ 32
    - 22904091311696 * s ^ 31
    + 51251486836721 * s ^ 30
    - 103981507722163 * s ^ 29
    + 192302841122249 * s ^ 28
    - 325617454306255 * s ^ 27
    + 506446113525089 * s ^ 26
    - 724918635216909 * s ^ 25
    + 955400548948481 * s ^ 24
    - 1158323078180542 * s ^ 23
    + 1288991570632472 * s ^ 22
    - 1311868327611943 * s ^ 21
    + 1214933736749382 * s ^ 20
    - 1016759033617110 * s ^ 19
    + 761385403770858 * s ^ 18
    - 502600480195522 * s ^ 17
    + 285222701726006 * s ^ 16
    - 132405746690956 * s ^ 15
    + 44008571045350 * s ^ 14
    - 4298577363025 * s ^ 13
    - 7064150136528 * s ^ 12
    + 6522194152058 * s ^ 11
    - 3420346386617 * s ^ 10
    + 1223238287443 * s ^ 9
    - 282221973534 * s ^ 8
    + 28056853824 * s ^ 7
    + 4386791653 * s ^ 6
    - 1049903405 * s ^ 5
    - 378884224 * s ^ 4
    + 150559370 * s ^ 3
    - 15482799 * s ^ 2
    + 884249 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient20 (s : ℚ) : ℚ :=
  s ^ 47
    - 52 * s ^ 46
    + 1330 * s ^ 45
    - 22318 * s ^ 44
    + 276227 * s ^ 43
    - 2685997 * s ^ 42
    + 21336891 * s ^ 41
    - 142157587 * s ^ 40
    + 809531802 * s ^ 39
    - 3997168655 * s ^ 38
    + 17309745108 * s ^ 37
    - 66373865244 * s ^ 36
    + 227248327242 * s ^ 35
    - 700018225755 * s ^ 34
    + 1954019611751 * s ^ 33
    - 4976196984843 * s ^ 32
    + 11633786513032 * s ^ 31
    - 25102097531929 * s ^ 30
    + 50183619375990 * s ^ 29
    - 93149116546782 * s ^ 28
    + 160550576612699 * s ^ 27
    - 256551289514192 * s ^ 26
    + 379019455220471 * s ^ 25
    - 515898855075810 * s ^ 24
    + 644417195768214 * s ^ 23
    - 735367179152836 * s ^ 22
    + 762440453340654 * s ^ 21
    - 713173033066805 * s ^ 20
    + 595778363039999 * s ^ 19
    - 437470511409300 * s ^ 18
    + 274450628573625 * s ^ 17
    - 138415005702088 * s ^ 16
    + 46396352651120 * s ^ 15
    + 1535984981592 * s ^ 14
    - 17186795241478 * s ^ 13
    + 15852729400382 * s ^ 12
    - 9461532679364 * s ^ 11
    + 4099471887023 * s ^ 10
    - 1249833826866 * s ^ 9
    + 223877226573 * s ^ 8
    - 3635105691 * s ^ 7
    - 6027120738 * s ^ 6
    - 1484415315 * s ^ 5
    + 1581316016 * s ^ 4
    - 393569575 * s ^ 3
    + 38417777 * s ^ 2
    - 2086299 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient21 (s : ℚ) : ℚ :=
  -2 * s ^ 45
    + 88 * s ^ 44
    - 1914 * s ^ 43
    + 27611 * s ^ 42
    - 299195 * s ^ 41
    + 2612831 * s ^ 40
    - 19221338 * s ^ 39
    + 122528599 * s ^ 38
    - 688576629 * s ^ 37
    + 3444631848 * s ^ 36
    - 15416397966 * s ^ 35
    + 61877399140 * s ^ 34
    - 223017605156 * s ^ 33
    + 722392049011 * s ^ 32
    - 2104642019770 * s ^ 31
    + 5520100350904 * s ^ 30
    - 13048224654238 * s ^ 29
    + 27832315674572 * s ^ 28
    - 53648175167909 * s ^ 27
    + 93575648990947 * s ^ 26
    - 147846383445644 * s ^ 25
    + 211632660226361 * s ^ 24
    - 274146430001861 * s ^ 23
    + 320399521086514 * s ^ 22
    - 335907864780648 * s ^ 21
    + 312736493726786 * s ^ 20
    - 253870178692259 * s ^ 19
    + 173242647119134 * s ^ 18
    - 90785453364354 * s ^ 17
    + 24627335271288 * s ^ 16
    + 15490304028162 * s ^ 15
    - 30269847428078 * s ^ 14
    + 27927318648902 * s ^ 13
    - 18559404004141 * s ^ 12
    + 9447337023178 * s ^ 11
    - 3605497900531 * s ^ 10
    + 935989213026 * s ^ 9
    - 121202587667 * s ^ 8
    - 1690327328 * s ^ 7
    - 7734180419 * s ^ 6
    + 9688817675 * s ^ 5
    - 4075850017 * s ^ 4
    + 820393931 * s ^ 3
    - 77389845 * s ^ 2
    + 4076401 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient22 (s : ℚ) : ℚ :=
  -2 * s ^ 44
    + 104 * s ^ 43
    - 2616 * s ^ 42
    + 42577 * s ^ 41
    - 505517 * s ^ 40
    + 4676886 * s ^ 39
    - 35146602 * s ^ 38
    + 220695591 * s ^ 37
    - 1181547701 * s ^ 36
    + 5474277349 * s ^ 35
    - 22198979605 * s ^ 34
    + 79488175394 * s ^ 33
    - 253117431983 * s ^ 32
    + 721067727332 * s ^ 31
    - 1847188103912 * s ^ 30
    + 4274750413389 * s ^ 29
    - 8971622119734 * s ^ 28
    + 17126975237104 * s ^ 27
    - 29787301882003 * s ^ 26
    + 47185014211022 * s ^ 25
    - 67903640643293 * s ^ 24
    + 88315797191422 * s ^ 23
    - 102910939761298 * s ^ 22
    + 105877160726840 * s ^ 21
    - 93592281606090 * s ^ 20
    + 66926497703257 * s ^ 19
    - 31910273150075 * s ^ 18
    - 2176316423671 * s ^ 17
    + 26673096901028 * s ^ 16
    - 37229112931038 * s ^ 15
    + 35176666977808 * s ^ 14
    - 25865423098560 * s ^ 13
    + 15229429045073 * s ^ 12
    - 7075693861379 * s ^ 11
    + 2462576042928 * s ^ 10
    - 590463496806 * s ^ 9
    + 110718030660 * s ^ 8
    - 56972196977 * s ^ 7
    + 47032536753 * s ^ 6
    - 24724691617 * s ^ 5
    + 7784203051 * s ^ 4
    - 1388750984 * s ^ 3
    + 128155322 * s ^ 2
    - 6639427 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient23 (s : ℚ) : ℚ :=
  4 * s ^ 42
    - 186 * s ^ 41
    + 4203 * s ^ 40
    - 61593 * s ^ 39
    + 659388 * s ^ 38
    - 5510194 * s ^ 37
    + 37512341 * s ^ 36
    - 214378346 * s ^ 35
    + 1051382481 * s ^ 34
    - 4499000811 * s ^ 33
    + 17007088785 * s ^ 32
    - 57295404239 * s ^ 31
    + 172969723966 * s ^ 30
    - 469128191638 * s ^ 29
    + 1143287239369 * s ^ 28
    - 2499478608940 * s ^ 27
    + 4887240239434 * s ^ 26
    - 8509632551866 * s ^ 25
    + 13110488235348 * s ^ 24
    - 17681690737590 * s ^ 23
    + 20438580770745 * s ^ 22
    - 19287973478897 * s ^ 21
    + 12806858156185 * s ^ 20
    - 1351465485847 * s ^ 19
    - 12476025641695 * s ^ 18
    + 24622613229787 * s ^ 17
    - 31404146199239 * s ^ 16
    + 31305231038285 * s ^ 15
    - 25610658046160 * s ^ 14
    + 17408463301725 * s ^ 13
    - 9762255859005 * s ^ 12
    + 4425497485243 * s ^ 11
    - 1620843916146 * s ^ 10
    + 564962137929 * s ^ 9
    - 284252082840 * s ^ 8
    + 188190242130 * s ^ 7
    - 105988781871 * s ^ 6
    + 42971156519 * s ^ 5
    - 11656486525 * s ^ 4
    + 1927342729 * s ^ 3
    - 175565272 * s ^ 2
    + 9042304 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient24 (s : ℚ) : ℚ :=
  s ^ 41
    - 54 * s ^ 40
    + 1393 * s ^ 39
    - 22962 * s ^ 38
    + 272533 * s ^ 37
    - 2487002 * s ^ 36
    + 18192725 * s ^ 35
    - 109787453 * s ^ 34
    + 557865789 * s ^ 33
    - 2422239147 * s ^ 32
    + 9082477776 * s ^ 31
    - 29634594843 * s ^ 30
    + 84599740181 * s ^ 29
    - 212073220740 * s ^ 28
    + 467565092218 * s ^ 27
    - 905444426474 * s ^ 26
    + 1529995956744 * s ^ 25
    - 2216359965292 * s ^ 24
    + 2629416600244 * s ^ 23
    - 2210068004110 * s ^ 22
    + 327633493525 * s ^ 21
    + 3363625128773 * s ^ 20
    - 8521963290234 * s ^ 19
    + 13991895093819 * s ^ 18
    - 18161526822490 * s ^ 17
    + 19685770602001 * s ^ 16
    - 18181875146843 * s ^ 15
    + 14417758138152 * s ^ 14
    - 9827457617031 * s ^ 13
    + 5764140748074 * s ^ 12
    - 2987606285596 * s ^ 11
    + 1520767855509 * s ^ 10
    - 884346752912 * s ^ 9
    + 569103245449 * s ^ 8
    - 335678103992 * s ^ 7
    + 159148169139 * s ^ 6
    - 56496066311 * s ^ 5
    + 13997478340 * s ^ 4
    - 2200319093 * s ^ 3
    + 199296789 * s ^ 2
    - 10296595 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient25 (s : ℚ) : ℚ :=
  -s ^ 39
    + 48 * s ^ 38
    - 1123 * s ^ 37
    + 16900 * s ^ 36
    - 182409 * s ^ 35
    + 1498281 * s ^ 34
    - 9742859 * s ^ 33
    + 51671170 * s ^ 32
    - 228693945 * s ^ 31
    + 858313861 * s ^ 30
    - 2751623357 * s ^ 29
    + 7502637573 * s ^ 28
    - 17004133082 * s ^ 27
    + 29942271783 * s ^ 26
    - 31326605083 * s ^ 25
    - 27691754473 * s ^ 24
    + 252654743711 * s ^ 23
    - 805858426918 * s ^ 22
    + 1851687683038 * s ^ 21
    - 3448833918590 * s ^ 20
    + 5447101781215 * s ^ 19
    - 7462886819903 * s ^ 18
    + 8974755874332 * s ^ 17
    - 9531894418662 * s ^ 16
    + 8979252717657 * s ^ 15
    - 7536119645694 * s ^ 14
    + 5678737890712 * s ^ 13
    - 3928212246261 * s ^ 12
    + 2623835641671 * s ^ 11
    - 1786002543253 * s ^ 10
    + 1221314635911 * s ^ 9
    - 771083375271 * s ^ 8
    + 413411393389 * s ^ 7
    - 177705861363 * s ^ 6
    + 58194866742 * s ^ 5
    - 13579067382 * s ^ 4
    + 2062641764 * s ^ 3
    - 186991982 * s ^ 2
    + 9771853 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient26 (s : ℚ) : ℚ :=
  -s ^ 37
    + 35 * s ^ 36
    - 511 * s ^ 35
    + 3811 * s ^ 34
    - 12381 * s ^ 33
    - 11370 * s ^ 32
    + 4195 * s ^ 31
    + 4389604 * s ^ 30
    - 55319415 * s ^ 29
    + 398664988 * s ^ 28
    - 2075362083 * s ^ 27
    + 8513236008 * s ^ 26
    - 28751324102 * s ^ 25
    + 82028035248 * s ^ 24
    - 201266642323 * s ^ 23
    + 431274595902 * s ^ 22
    - 818978224184 * s ^ 21
    + 1395623773048 * s ^ 20
    - 2150529947402 * s ^ 19
    + 3002241879572 * s ^ 18
    - 3793629539995 * s ^ 17
    + 4337945374876 * s ^ 16
    - 4497583856292 * s ^ 15
    + 4248008637784 * s ^ 14
    - 3696938873128 * s ^ 13
    + 3030234147049 * s ^ 12
    - 2389851092567 * s ^ 11
    + 1802246719595 * s ^ 10
    - 1246984717045 * s ^ 9
    + 751578362057 * s ^ 8
    - 377946738159 * s ^ 7
    + 152749118955 * s ^ 6
    - 47433666843 * s ^ 5
    + 10618830525 * s ^ 4
    - 1576798386 * s ^ 3
    + 144030505 * s ^ 2
    - 7677570 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient27 (s : ℚ) : ℚ :=
  -s ^ 36
    + 52 * s ^ 35
    - 1245 * s ^ 34
    + 18402 * s ^ 33
    - 190041 * s ^ 32
    + 1473662 * s ^ 31
    - 9025079 * s ^ 30
    + 45430515 * s ^ 29
    - 194284822 * s ^ 28
    + 724746455 * s ^ 27
    - 2404207559 * s ^ 26
    + 7187285301 * s ^ 25
    - 19548361113 * s ^ 24
    + 48702641158 * s ^ 23
    - 111417314889 * s ^ 22
    + 233226624668 * s ^ 21
    - 443225087737 * s ^ 20
    + 758969148567 * s ^ 19
    - 1167290515430 * s ^ 18
    + 1615303589483 * s ^ 17
    - 2020562480072 * s ^ 16
    + 2298102528636 * s ^ 15
    - 2396239322836 * s ^ 14
    + 2318620690887 * s ^ 13
    - 2103722735069 * s ^ 12
    + 1782360240526 * s ^ 11
    - 1376400958219 * s ^ 10
    + 936340333888 * s ^ 9
    - 543610441801 * s ^ 8
    + 262015471271 * s ^ 7
    - 101690951256 * s ^ 6
    + 30453768831 * s ^ 5
    - 6623541830 * s ^ 4
    + 970495901 * s ^ 3
    - 90008913 * s ^ 2
    + 4939709 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient28 (s : ℚ) : ℚ :=
  3 * s ^ 34
    - 146 * s ^ 33
    + 3335 * s ^ 32
    - 47736 * s ^ 31
    + 482690 * s ^ 30
    - 3690074 * s ^ 29
    + 22324283 * s ^ 28
    - 110625126 * s ^ 27
    + 461546757 * s ^ 26
    - 1656802168 * s ^ 25
    + 5196895562 * s ^ 24
    - 14378455876 * s ^ 23
    + 35263658917 * s ^ 22
    - 76932274007 * s ^ 21
    + 150012109215 * s ^ 20
    - 263258069056 * s ^ 19
    + 418976312591 * s ^ 18
    - 608408272098 * s ^ 17
    + 809390899381 * s ^ 16
    - 990474191278 * s ^ 15
    + 1120976111952 * s ^ 14
    - 1176947799819 * s ^ 13
    + 1139146097378 * s ^ 12
    - 998079346923 * s ^ 11
    + 772613140254 * s ^ 10
    - 516382533299 * s ^ 9
    + 292136697911 * s ^ 8
    - 137028808236 * s ^ 7
    + 51801904159 * s ^ 6
    - 15138218123 * s ^ 5
    + 3229860509 * s ^ 4
    - 471163359 * s ^ 3
    + 44812479 * s ^ 2
    - 2560052 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient29 (s : ℚ) : ℚ :=
  -4 * s ^ 32
    + 188 * s ^ 31
    - 4166 * s ^ 30
    + 57975 * s ^ 29
    - 569591 * s ^ 28
    + 4213763 * s ^ 27
    - 24474065 * s ^ 26
    + 115085673 * s ^ 25
    - 449371256 * s ^ 24
    + 1490360610 * s ^ 23
    - 4285978572 * s ^ 22
    + 10876276737 * s ^ 21
    - 24656614533 * s ^ 20
    + 50252332971 * s ^ 19
    - 92281282971 * s ^ 18
    + 152967050598 * s ^ 17
    - 229799699003 * s ^ 16
    + 314464376270 * s ^ 15
    - 392580334733 * s ^ 14
    + 444324899299 * s ^ 13
    - 449719862518 * s ^ 12
    + 400382250864 * s ^ 11
    - 308886659461 * s ^ 10
    + 203921976928 * s ^ 9
    - 113709007805 * s ^ 8
    + 52569634117 * s ^ 7
    - 19580630685 * s ^ 6
    + 5638071937 * s ^ 5
    - 1190604210 * s ^ 4
    + 174754223 * s ^ 3
    - 17291299 * s ^ 2
    + 1042719 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient30 (s : ℚ) : ℚ :=
  3 * s ^ 30
    - 140 * s ^ 29
    + 3096 * s ^ 28
    - 43180 * s ^ 27
    + 426476 * s ^ 26
    - 3175812 * s ^ 25
    + 18543722 * s ^ 24
    - 87242257 * s ^ 23
    + 337641052 * s ^ 22
    - 1094044518 * s ^ 21
    + 3017789839 * s ^ 20
    - 7205587701 * s ^ 19
    + 15137262218 * s ^ 18
    - 28358023793 * s ^ 17
    + 47721055818 * s ^ 16
    - 72067543018 * s ^ 15
    + 96914751891 * s ^ 14
    - 114822438724 * s ^ 13
    + 118686716360 * s ^ 12
    - 106263589771 * s ^ 11
    + 81957521351 * s ^ 10
    - 54087853424 * s ^ 9
    + 30181993023 * s ^ 8
    - 13951664628 * s ^ 7
    + 5180836627 * s ^ 6
    - 1484487863 * s ^ 5
    + 313566762 * s ^ 4
    - 47047801 * s ^ 3
    + 4955794 * s ^ 2
    - 321402 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient31 (s : ℚ) : ℚ :=
  -s ^ 28
    + 47 * s ^ 27
    - 1053 * s ^ 26
    + 14961 * s ^ 25
    - 151258 * s ^ 24
    + 1157304 * s ^ 23
    - 6957523 * s ^ 22
    + 33685104 * s ^ 21
    - 133578537 * s ^ 20
    + 439081974 * s ^ 19
    - 1206850587 * s ^ 18
    + 2792229157 * s ^ 17
    - 5467926973 * s ^ 16
    + 9109004186 * s ^ 15
    - 12976560857 * s ^ 14
    + 15895965640 * s ^ 13
    - 16831379468 * s ^ 12
    + 15453791616 * s ^ 11
    - 12284005442 * s ^ 10
    + 8377766761 * s ^ 9
    - 4816869344 * s ^ 8
    + 2275944867 * s ^ 7
    - 856059052 * s ^ 6
    + 247397563 * s ^ 5
    - 53200981 * s ^ 4
    + 8415414 * s ^ 3
    - 983988 * s ^ 2
    + 70470 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient32 (s : ℚ) : ℚ :=
  s ^ 24
    - 42 * s ^ 23
    + 831 * s ^ 22
    - 10299 * s ^ 21
    + 89674 * s ^ 20
    - 583161 * s ^ 19
    + 2939490 * s ^ 18
    - 11763699 * s ^ 17
    + 37977605 * s ^ 16
    - 99946120 * s ^ 15
    + 215795218 * s ^ 14
    - 383467145 * s ^ 13
    + 561015689 * s ^ 12
    - 674190801 * s ^ 11
    + 662191296 * s ^ 10
    - 527398876 * s ^ 9
    + 336812215 * s ^ 8
    - 169964584 * s ^ 7
    + 66619055 * s ^ 6
    - 19987475 * s ^ 5
    + 4598402 * s ^ 4
    - 836438 * s ^ 3
    + 118956 * s ^ 2
    - 9792 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient33 (s : ℚ) : ℚ :=
  -s ^ 14
    + 25 * s ^ 13
    - 283 * s ^ 12
    + 1919 * s ^ 11
    - 8687 * s ^ 10
    + 27682 * s ^ 9
    - 63761 * s ^ 8
    + 107217 * s ^ 7
    - 131216 * s ^ 6
    + 115007 * s ^ 5
    - 69868 * s ^ 4
    + 27726 * s ^ 3
    - 6408 * s ^ 2
    + 648 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def structuralNumeratorCoefficient34 (_s : ℚ) : ℚ :=
  0

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
        - 0
        - termThreeCoefficient34 s
      := by
  simp only [structuralNumeratorCoefficient34,
    termOneCoefficient34,
    termThreeCoefficient34]
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
def multiplierCoefficient0 (_s : ℚ) : ℚ :=
  0

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient1 (s : ℚ) : ℚ :=
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
def multiplierCoefficient2 (s : ℚ) : ℚ :=
  s ^ 27
    - 7 * s ^ 26
    + 29 * s ^ 25
    - 79 * s ^ 24
    + 130 * s ^ 23
    - 126 * s ^ 22
    - 16 * s ^ 21
    + 324 * s ^ 20
    - 726 * s ^ 19
    + 1078 * s ^ 18
    - 1216 * s ^ 17
    + 1102 * s ^ 16
    - 805 * s ^ 15
    + 469 * s ^ 14
    - 213 * s ^ 13
    + 69 * s ^ 12
    - 16 * s ^ 11
    + 2 * s ^ 10

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient3 (s : ℚ) : ℚ :=
  s ^ 28
    - 3 * s ^ 27
    - 35 * s ^ 26
    + 303 * s ^ 25
    - 1340 * s ^ 24
    + 3953 * s ^ 23
    - 8435 * s ^ 22
    + 14108 * s ^ 21
    - 18828 * s ^ 20
    + 20067 * s ^ 19
    - 16396 * s ^ 18
    + 8530 * s ^ 17
    + 422 * s ^ 16
    - 7237 * s ^ 15
    + 9948 * s ^ 14
    - 8903 * s ^ 13
    + 6002 * s ^ 12
    - 3095 * s ^ 11
    + 1247 * s ^ 10
    - 382 * s ^ 9
    + 85 * s ^ 8
    - 13 * s ^ 7
    + s ^ 6

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient4 (s : ℚ) : ℚ :=
  s ^ 30
    - 14 * s ^ 29
    + 111 * s ^ 28
    - 624 * s ^ 27
    + 2515 * s ^ 26
    - 7361 * s ^ 25
    + 15790 * s ^ 24
    - 23118 * s ^ 23
    + 16588 * s ^ 22
    + 19963 * s ^ 21
    - 98512 * s ^ 20
    + 212847 * s ^ 19
    - 335631 * s ^ 18
    + 426157 * s ^ 17
    - 448893 * s ^ 16
    + 396813 * s ^ 15
    - 291343 * s ^ 14
    + 172909 * s ^ 13
    - 77422 * s ^ 12
    + 20424 * s ^ 11
    + 2312 * s ^ 10
    - 6309 * s ^ 9
    + 4070 * s ^ 8
    - 1679 * s ^ 7
    + 496 * s ^ 6
    - 103 * s ^ 5
    + 14 * s ^ 4
    - s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient5 (s : ℚ) : ℚ :=
  s ^ 31
    - 14 * s ^ 30
    + 87 * s ^ 29
    - 274 * s ^ 28
    - 136 * s ^ 27
    + 6491 * s ^ 26
    - 38601 * s ^ 25
    + 143922 * s ^ 24
    - 398966 * s ^ 23
    + 873966 * s ^ 22
    - 1575809 * s ^ 21
    + 2404909 * s ^ 20
    - 3135459 * s ^ 19
    + 3493387 * s ^ 18
    - 3272214 * s ^ 17
    + 2464520 * s ^ 16
    - 1307352 * s ^ 15
    + 160890 * s ^ 14
    + 641953 * s ^ 13
    - 963358 * s ^ 12
    + 884818 * s ^ 11
    - 609733 * s ^ 10
    + 333829 * s ^ 9
    - 146608 * s ^ 8
    + 51292 * s ^ 7
    - 14021 * s ^ 6
    + 2841 * s ^ 5
    - 389 * s ^ 4
    + 28 * s ^ 3

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 32
    + 22 * s ^ 31
    - 257 * s ^ 30
    + 2002 * s ^ 29
    - 11473 * s ^ 28
    + 50995 * s ^ 27
    - 180066 * s ^ 26
    + 512018 * s ^ 25
    - 1186226 * s ^ 24
    + 2254807 * s ^ 23
    - 3514833 * s ^ 22
    + 4423974 * s ^ 21
    - 4135999 * s ^ 20
    + 1713740 * s ^ 19
    + 3346529 * s ^ 18
    - 10649249 * s ^ 17
    + 18641892 * s ^ 16
    - 25061348 * s ^ 15
    + 27938429 * s ^ 14
    - 26453481 * s ^ 13
    + 21441697 * s ^ 12
    - 14858903 * s ^ 11
    + 8752463 * s ^ 10
    - 4357116 * s ^ 9
    + 1807226 * s ^ 8
    - 612653 * s ^ 7
    + 164773 * s ^ 6
    - 33146 * s ^ 5
    + 4490 * s ^ 4
    - 302 * s ^ 3
    - 4 * s ^ 2

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient7 (s : ℚ) : ℚ :=
  -s ^ 33
    + 22 * s ^ 32
    - 240 * s ^ 31
    + 1712 * s ^ 30
    - 8771 * s ^ 29
    + 33317 * s ^ 28
    - 91724 * s ^ 27
    + 157160 * s ^ 26
    - 1474 * s ^ 25
    - 1103315 * s ^ 24
    + 4718173 * s ^ 23
    - 13347430 * s ^ 22
    + 30144089 * s ^ 21
    - 58188702 * s ^ 20
    + 98868948 * s ^ 19
    - 149610939 * s ^ 18
    + 202642600 * s ^ 17
    - 245796148 * s ^ 16
    + 266669608 * s ^ 15
    - 257943244 * s ^ 14
    + 221111924 * s ^ 13
    - 166807611 * s ^ 12
    + 109780703 * s ^ 11
    - 62438553 * s ^ 10
    + 30383024 * s ^ 9
    - 12437598 * s ^ 8
    + 4191236 * s ^ 7
    - 1123357 * s ^ 6
    + 224354 * s ^ 5
    - 29533 * s ^ 4
    + 1694 * s ^ 3
    + 75 * s ^ 2
    + s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient8 (s : ℚ) : ℚ :=
  -s ^ 33
    + 32 * s ^ 32
    - 473 * s ^ 31
    + 4495 * s ^ 30
    - 31247 * s ^ 29
    + 169385 * s ^ 28
    - 743127 * s ^ 27
    + 2703740 * s ^ 26
    - 8321690 * s ^ 25
    + 22098192 * s ^ 24
    - 51624582 * s ^ 23
    + 107944048 * s ^ 22
    - 204601362 * s ^ 21
    + 353609596 * s ^ 20
    - 556990532 * s ^ 19
    + 797592830 * s ^ 18
    - 1035558873 * s ^ 17
    + 1215140589 * s ^ 16
    - 1283947500 * s ^ 15
    + 1215284568 * s ^ 14
    - 1023576517 * s ^ 13
    + 761666118 * s ^ 12
    - 496563495 * s ^ 11
    + 281122631 * s ^ 10
    - 136683863 * s ^ 9
    + 56063155 * s ^ 8
    - 18952675 * s ^ 7
    + 5079145 * s ^ 6
    - 1002032 * s ^ 5
    + 125165 * s ^ 4
    - 5080 * s ^ 3
    - 617 * s ^ 2
    - 23 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 34
    + 28 * s ^ 33
    - 392 * s ^ 32
    + 3644 * s ^ 31
    - 25219 * s ^ 30
    + 137981 * s ^ 29
    - 619428 * s ^ 28
    + 2344489 * s ^ 27
    - 7657607 * s ^ 26
    + 22054756 * s ^ 25
    - 57053848 * s ^ 24
    + 134183308 * s ^ 23
    - 288197747 * s ^ 22
    + 564433818 * s ^ 21
    - 1003878518 * s ^ 20
    + 1616206859 * s ^ 19
    - 2352561364 * s ^ 18
    + 3093219903 * s ^ 17
    - 3666479652 * s ^ 16
    + 3905205020 * s ^ 15
    - 3719145124 * s ^ 14
    + 3148737324 * s ^ 13
    - 2355347255 * s ^ 12
    + 1545433625 * s ^ 11
    - 882163519 * s ^ 10
    + 432868881 * s ^ 9
    - 179167960 * s ^ 8
    + 61002876 * s ^ 7
    - 16337666 * s ^ 6
    + 3156005 * s ^ 5
    - 361203 * s ^ 4
    + 4947 * s ^ 3
    + 2791 * s ^ 2
    + 248 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient10 (s : ℚ) : ℚ :=
  s ^ 34
    - 26 * s ^ 33
    + 346 * s ^ 32
    - 3119 * s ^ 31
    + 21336 * s ^ 30
    - 118198 * s ^ 29
    + 554860 * s ^ 28
    - 2279420 * s ^ 27
    + 8351329 * s ^ 26
    - 27454169 * s ^ 25
    + 80776318 * s ^ 24
    - 211727207 * s ^ 23
    + 493297557 * s ^ 22
    - 1022778145 * s ^ 21
    + 1894192379 * s ^ 20
    - 3148241700 * s ^ 19
    + 4711047775 * s ^ 18
    - 6349228024 * s ^ 17
    + 7691637463 * s ^ 16
    - 8346340343 * s ^ 15
    + 8076203688 * s ^ 14
    - 6937327525 * s ^ 13
    + 5263909533 * s ^ 12
    - 3506120105 * s ^ 11
    + 2033270167 * s ^ 10
    - 1013013109 * s ^ 9
    + 424924299 * s ^ 8
    - 145978307 * s ^ 7
    + 38968545 * s ^ 6
    - 7283720 * s ^ 5
    + 726010 * s ^ 4
    + 19489 * s ^ 3
    - 6310 * s ^ 2
    - 1668 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient11 (s : ℚ) : ℚ :=
  -15 * s ^ 32
    + 405 * s ^ 31
    - 5581 * s ^ 30
    + 51601 * s ^ 29
    - 355454 * s ^ 28
    + 1925895 * s ^ 27
    - 8490313 * s ^ 26
    + 31213005 * s ^ 25
    - 97642000 * s ^ 24
    + 264582141 * s ^ 23
    - 630733700 * s ^ 22
    + 1339315083 * s ^ 21
    - 2554454834 * s ^ 20
    + 4391951361 * s ^ 19
    - 6802233261 * s ^ 18
    + 9461756146 * s ^ 17
    - 11780592956 * s ^ 16
    + 13087432255 * s ^ 15
    - 12935040213 * s ^ 14
    + 11343139587 * s ^ 13
    - 8791756654 * s ^ 12
    + 5986985213 * s ^ 11
    - 3549592116 * s ^ 10
    + 1804427117 * s ^ 9
    - 769723541 * s ^ 8
    + 267145121 * s ^ 7
    - 70862756 * s ^ 6
    + 12674327 * s ^ 5
    - 1047742 * s ^ 4
    - 72191 * s ^ 3
    - 3776 * s ^ 2
    + 7846 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient12 (s : ℚ) : ℚ :=
  -2 * s ^ 33
    + 61 * s ^ 32
    - 919 * s ^ 31
    + 9121 * s ^ 30
    - 66836 * s ^ 29
    + 384737 * s ^ 28
    - 1813692 * s ^ 27
    + 7231935 * s ^ 26
    - 25056893 * s ^ 25
    + 77068957 * s ^ 24
    - 213379129 * s ^ 23
    + 534639269 * s ^ 22
    - 1210390295 * s ^ 21
    + 2463337388 * s ^ 20
    - 4481801378 * s ^ 19
    + 7262054844 * s ^ 18
    - 10465325183 * s ^ 17
    + 13415139782 * s ^ 16
    - 15301382257 * s ^ 15
    + 15529351446 * s ^ 14
    - 14006273069 * s ^ 13
    + 11182167416 * s ^ 12
    - 7847773275 * s ^ 11
    + 4788023814 * s ^ 10
    - 2496012605 * s ^ 9
    + 1087251734 * s ^ 8
    - 382216409 * s ^ 7
    + 100824600 * s ^ 6
    - 17389108 * s ^ 5
    + 1339305 * s ^ 4
    - 2745 * s ^ 3
    + 86791 * s ^ 2
    - 27405 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient13 (s : ℚ) : ℚ :=
  s ^ 32
    - 18 * s ^ 31
    + 93 * s ^ 30
    + 896 * s ^ 29
    - 21102 * s ^ 28
    + 214313 * s ^ 27
    - 1484417 * s ^ 26
    + 7836338 * s ^ 25
    - 33141090 * s ^ 24
    + 115586770 * s ^ 23
    - 339106344 * s ^ 22
    + 849483679 * s ^ 21
    - 1839098632 * s ^ 20
    + 3476617684 * s ^ 19
    - 5790946985 * s ^ 18
    + 8562315517 * s ^ 17
    - 11292520350 * s ^ 16
    + 13315318496 * s ^ 15
    - 14037205483 * s ^ 14
    + 13190279387 * s ^ 13
    - 10976663480 * s ^ 12
    + 8015502763 * s ^ 11
    - 5068694046 * s ^ 10
    + 2726789889 * s ^ 9
    - 1221368803 * s ^ 8
    + 438474030 * s ^ 7
    - 117042726 * s ^ 6
    + 21097866 * s ^ 5
    - 2637028 * s ^ 4
    + 704998 * s ^ 3
    - 365816 * s ^ 2
    + 73600 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient14 (s : ℚ) : ℚ :=
  s ^ 32
    - 34 * s ^ 31
    + 569 * s ^ 30
    - 6254 * s ^ 29
    + 50527 * s ^ 28
    - 318136 * s ^ 27
    + 1618513 * s ^ 26
    - 6823441 * s ^ 25
    + 24307538 * s ^ 24
    - 74375378 * s ^ 23
    + 198301803 * s ^ 22
    - 466622935 * s ^ 21
    + 979654351 * s ^ 20
    - 1850660457 * s ^ 19
    + 3161582049 * s ^ 18
    - 4888521228 * s ^ 17
    + 6825394644 * s ^ 16
    - 8571799939 * s ^ 15
    + 9631988829 * s ^ 14
    - 9613600178 * s ^ 13
    + 8450588186 * s ^ 12
    - 6479694490 * s ^ 11
    + 4279961013 * s ^ 10
    - 2399705836 * s ^ 9
    + 1121114115 * s ^ 8
    - 420520151 * s ^ 7
    + 120580743 * s ^ 6
    - 27698053 * s ^ 5
    + 7133010 * s ^ 4
    - 2742115 * s ^ 3
    + 967885 * s ^ 2
    - 155151 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient15 (s : ℚ) : ℚ :=
  -2 * s ^ 30
    + 54 * s ^ 29
    - 740 * s ^ 28
    + 7002 * s ^ 27
    - 51605 * s ^ 26
    + 312530 * s ^ 25
    - 1592134 * s ^ 24
    + 6891360 * s ^ 23
    - 25477092 * s ^ 22
    + 80824240 * s ^ 21
    - 221145975 * s ^ 20
    + 524348707 * s ^ 19
    - 1081702789 * s ^ 18
    + 1949112468 * s ^ 17
    - 3079799126 * s ^ 16
    + 4277829098 * s ^ 15
    - 5219892739 * s ^ 14
    + 5579694972 * s ^ 13
    - 5206693821 * s ^ 12
    + 4218670198 * s ^ 11
    - 2943677123 * s ^ 10
    + 1753440598 * s ^ 9
    - 878899372 * s ^ 8
    + 361609260 * s ^ 7
    - 124246903 * s ^ 6
    + 41863522 * s ^ 5
    - 16111896 * s ^ 4
    + 6287179 * s ^ 3
    - 1859467 * s ^ 2
    + 259596 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient16 (s : ℚ) : ℚ :=
  -2 * s ^ 29
    + 68 * s ^ 28
    - 1088 * s ^ 27
    + 11094 * s ^ 26
    - 81827 * s ^ 25
    + 467387 * s ^ 24
    - 2155716 * s ^ 23
    + 8260120 * s ^ 22
    - 26837803 * s ^ 21
    + 75029702 * s ^ 20
    - 182375025 * s ^ 19
    + 388482065 * s ^ 18
    - 729488387 * s ^ 17
    + 1210811365 * s ^ 16
    - 1774329343 * s ^ 15
    + 2289256127 * s ^ 14
    - 2596421072 * s ^ 13
    + 2584829863 * s ^ 12
    - 2249373252 * s ^ 11
    + 1702328385 * s ^ 10
    - 1114830192 * s ^ 9
    + 625248632 * s ^ 8
    - 300939239 * s ^ 7
    + 133801673 * s ^ 6
    - 60871181 * s ^ 5
    + 26984479 * s ^ 4
    - 10180041 * s ^ 3
    + 2719248 * s ^ 2
    - 346040 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient17 (s : ℚ) : ℚ :=
  5 * s ^ 27
    - 148 * s ^ 26
    + 2095 * s ^ 25
    - 19152 * s ^ 24
    + 128094 * s ^ 23
    - 668826 * s ^ 22
    + 2829558 * s ^ 21
    - 9937163 * s ^ 20
    + 29491557 * s ^ 19
    - 74911911 * s ^ 18
    + 164055181 * s ^ 17
    - 310938310 * s ^ 16
    + 512288928 * s ^ 15
    - 738590220 * s ^ 14
    + 936753197 * s ^ 13
    - 1044719811 * s ^ 12
    + 1020746045 * s ^ 11
    - 871856374 * s ^ 10
    + 649005454 * s ^ 9
    - 420766281 * s ^ 8
    + 245245314 * s ^ 7
    - 136971969 * s ^ 6
    + 72874599 * s ^ 5
    - 33616775 * s ^ 4
    + 12286221 * s ^ 3
    - 3075660 * s ^ 2
    + 366352 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient18 (s : ℚ) : ℚ :=
  s ^ 26
    - 38 * s ^ 25
    + 637 * s ^ 24
    - 6477 * s ^ 23
    + 46024 * s ^ 22
    - 248315 * s ^ 21
    + 1071267 * s ^ 20
    - 3810305 * s ^ 19
    + 11375285 * s ^ 18
    - 28898641 * s ^ 17
    + 63363689 * s ^ 16
    - 121348901 * s ^ 15
    + 203776517 * s ^ 14
    - 298758478 * s ^ 13
    + 380622186 * s ^ 12
    - 421848802 * s ^ 11
    + 408174838 * s ^ 10
    - 345847757 * s ^ 9
    + 260873649 * s ^ 8
    - 181834779 * s ^ 7
    + 118141102 * s ^ 6
    - 67392086 * s ^ 5
    + 31383276 * s ^ 4
    - 11217664 * s ^ 3
    + 2688601 * s ^ 2
    - 304829 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient19 (s : ℚ) : ℚ :=
  -3 * s ^ 24
    + 96 * s ^ 23
    - 1406 * s ^ 22
    + 12671 * s ^ 21
    - 79912 * s ^ 20
    + 381203 * s ^ 19
    - 1451206 * s ^ 18
    + 4567121 * s ^ 17
    - 12097897 * s ^ 16
    + 27125495 * s ^ 15
    - 51626020 * s ^ 14
    + 84079533 * s ^ 13
    - 118773971 * s ^ 12
    + 147207748 * s ^ 11
    - 160928007 * s ^ 10
    + 156602507 * s ^ 9
    - 138416795 * s ^ 8
    + 111749768 * s ^ 7
    - 79280126 * s ^ 6
    + 46621249 * s ^ 5
    - 21789672 * s ^ 4
    + 7692282 * s ^ 3
    - 1790057 * s ^ 2
    + 195399 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient20 (s : ℚ) : ℚ :=
  4 * s ^ 22
    - 120 * s ^ 21
    + 1652 * s ^ 20
    - 13912 * s ^ 19
    + 80754 * s ^ 18
    - 346475 * s ^ 17
    + 1157334 * s ^ 16
    - 3148283 * s ^ 15
    + 7242597 * s ^ 14
    - 14416048 * s ^ 13
    + 24949146 * s ^ 12
    - 37453885 * s ^ 11
    + 49063914 * s ^ 10
    - 56936368 * s ^ 9
    + 58708149 * s ^ 8
    - 52388931 * s ^ 7
    + 38831973 * s ^ 6
    - 23200783 * s ^ 5
    + 10935453 * s ^ 4
    - 3852775 * s ^ 3
    + 879856 * s ^ 2
    - 93252 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient21 (s : ℚ) : ℚ :=
  -3 * s ^ 20
    + 89 * s ^ 19
    - 1220 * s ^ 18
    + 10265 * s ^ 17
    - 59415 * s ^ 16
    + 251671 * s ^ 15
    - 813062 * s ^ 14
    + 2074399 * s ^ 13
    - 4330864 * s ^ 12
    + 7667608 * s ^ 11
    - 11796461 * s ^ 10
    + 15760563 * s ^ 9
    - 17859089 * s ^ 8
    + 16689364 * s ^ 7
    - 12651291 * s ^ 6
    + 7730749 * s ^ 5
    - 3734531 * s ^ 4
    + 1331366 * s ^ 3
    - 301368 * s ^ 2
    + 31230 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient22 (s : ℚ) : ℚ :=
  s ^ 18
    - 30 * s ^ 17
    + 420 * s ^ 16
    - 3637 * s ^ 15
    + 21750 * s ^ 14
    - 94961 * s ^ 13
    + 312239 * s ^ 12
    - 787476 * s ^ 11
    + 1541453 * s ^ 10
    - 2365087 * s ^ 9
    + 2878471 * s ^ 8
    - 2824297 * s ^ 7
    + 2269386 * s ^ 6
    - 1490336 * s ^ 5
    + 767436 * s ^ 4
    - 283016 * s ^ 3
    + 64236 * s ^ 2
    - 6552 * s

/-- Coefficient of the indicated power of the raw chart variable. -/
def multiplierCoefficient23 (s : ℚ) : ℚ :=
  -s ^ 14
    + 25 * s ^ 13
    - 283 * s ^ 12
    + 1919 * s ^ 11
    - 8687 * s ^ 10
    + 27682 * s ^ 9
    - 63761 * s ^ 8
    + 107217 * s ^ 7
    - 131216 * s ^ 6
    + 115007 * s ^ 5
    - 69868 * s ^ 4
    + 27726 * s ^ 3
    - 6408 * s ^ 2
    + 648 * s

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
    multiplierCoefficient23 s * r ^ 23

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
    sutherlandPolynomialCoefficient1 s *
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
    multiplierCoefficient14]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_25 (s : ℚ) :
    structuralNumeratorCoefficient25 s =
    sutherlandPolynomialCoefficient2 s *
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
    multiplierCoefficient15]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_26 (s : ℚ) :
    structuralNumeratorCoefficient26 s =
    sutherlandPolynomialCoefficient3 s *
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
    multiplierCoefficient16]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_27 (s : ℚ) :
    structuralNumeratorCoefficient27 s =
    sutherlandPolynomialCoefficient4 s *
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
    multiplierCoefficient17]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_28 (s : ℚ) :
    structuralNumeratorCoefficient28 s =
    sutherlandPolynomialCoefficient5 s *
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
    multiplierCoefficient18]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_29 (s : ℚ) :
    structuralNumeratorCoefficient29 s =
    sutherlandPolynomialCoefficient6 s *
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
    sutherlandPolynomialCoefficient6,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20,
    multiplierCoefficient19]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_30 (s : ℚ) :
    structuralNumeratorCoefficient30 s =
    sutherlandPolynomialCoefficient7 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient21 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient20 s
    := by
  simp only [structuralNumeratorCoefficient30,
    sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21,
    multiplierCoefficient20]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_31 (s : ℚ) :
    structuralNumeratorCoefficient31 s =
    sutherlandPolynomialCoefficient8 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient22 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient21 s
    := by
  simp only [structuralNumeratorCoefficient31,
    sutherlandPolynomialCoefficient8,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient23,
    multiplierCoefficient22,
    multiplierCoefficient21]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_32 (s : ℚ) :
    structuralNumeratorCoefficient32 s =
    sutherlandPolynomialCoefficient9 s *
        multiplierCoefficient23 s
      + sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient22 s
    := by
  simp only [structuralNumeratorCoefficient32,
    sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient23,
    multiplierCoefficient22]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_33 (s : ℚ) :
    structuralNumeratorCoefficient33 s =
    sutherlandPolynomialCoefficient10 s *
        multiplierCoefficient23 s
    := by
  simp only [structuralNumeratorCoefficient33,
    sutherlandPolynomialCoefficient10,
    multiplierCoefficient23]
  ring

/-- Checked coefficient identity for the polynomial product. -/
theorem structuralNumeratorCoefficient_product_certificate_34 (s : ℚ) :
    structuralNumeratorCoefficient34 s =
    0
    := by
  simp only [structuralNumeratorCoefficient34]

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

/-- The normalized second cyclic unit relation vanishes on the raw curve. -/
theorem relation_eq_zero
    (r s : ℚ)
    (hCurve : sutherlandPolynomial r s = 0)
    (hOne : rawUnitOneDenominator r s ≠ 0)
    (hTwo : rawUnitTwoDenominator r s ≠ 0)
    (hFour : rawUnitFourDenominator r s ≠ 0)
    (hEight : rawUnitEightDenominator r s ≠ 0) :
    rawUnitFourNumerator r s / rawUnitFourDenominator r s -
        rawUnitTwoNumerator r s / rawUnitTwoDenominator r s -
      (rawUnitFourNumerator r s / rawUnitFourDenominator r s) *
        (rawUnitOneNumerator r s / rawUnitOneDenominator r s) *
        (rawUnitEightNumerator r s / rawUnitEightDenominator r s -
          rawUnitFourNumerator r s / rawUnitFourDenominator r s) =
      0 := by
  have hStructural :=
    structuralNumerator_eq_sutherlandPolynomial_mul_multiplier r s
  simp only [structuralNumerator_eq_linearCombination,
    t1Step1_eq_rawUnitFourNumerator_mul_rawUnitFourDenominator,
    t1Step2_eq_t1Step1_mul_rawUnitTwoDenominator,
    t1Step3_eq_t1Step2_mul_rawUnitOneDenominator,
    termOne_eq_t1Step3_mul_rawUnitEightDenominator,
    t2Step1_eq_rawUnitTwoNumerator_mul_rawUnitFourDenominator,
    t2Step2_eq_t2Step1_mul_rawUnitFourDenominator,
    t2Step3_eq_t2Step2_mul_rawUnitOneDenominator,
    termTwo_eq_t2Step3_mul_rawUnitEightDenominator,
    t3Step1_eq_rawUnitFourNumerator_mul_rawUnitOneNumerator,
    t3Step2_eq_t3Step1_mul_difference,
    termThree_eq_t3Step2_mul_rawUnitTwoDenominator,
    difference_eq_linearCombination,
    differenceLeft_eq_rawUnitEightNumerator_mul_rawUnitFourDenominator,
    differenceRight_eq_rawUnitFourNumerator_mul_rawUnitEightDenominator] at hStructural
  rw [hCurve, zero_mul] at hStructural
  field_simp [hOne, hTwo, hFour, hEight]
  linear_combination hStructural

end MazurTorsion.Kubert.OrderTwentyFiveRawOrbitRelationTwoData
