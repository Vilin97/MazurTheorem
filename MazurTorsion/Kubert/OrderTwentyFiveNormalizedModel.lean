/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunault
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import MazurTorsion.Kubert.OrderTwentyFiveRawOrbitData
import MazurTorsion.Kubert.OrderTwentyFiveRawOrbitNormData
import MazurTorsion.Kubert.OrderTwentyFiveRawOrbitRelationTwoData
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# A normalized affine model for the order-twenty-five recurrence

The fraction-free recurrence in `OrderTwentyFive` is denominator-safe but grows
quickly. Here ten explicitly checked division-sequence polynomials normalize
all coordinates from `2P` through `13P`. Their denominators occur as squares
for abscissas and cubes for ordinates.

The cross-product of the normalized abscissas of `13P` and `12P` has one
obvious cuspidal factor `b-c`. After cancelling it, the remaining fixed
polynomial `orderTwentyFiveNoncuspidalFactor` has total degree 40. Every
cancellation used below is justified by the nonzero recurrence abscissas
already supplied by exact order 25.

This file is a forward reduction. It does not classify the rational points of
the degree-40 affine model.
-/

namespace MazurTorsion.Kubert

open scoped WeierstrassCurve.Affine

private def twentyFiveA (b c : ℚ) : ℚ :=
  b - c ^ 2 - c

private def twentyFiveB (b c : ℚ) : ℚ :=
  b ^ 2 - b * c - c ^ 3

private def twentyFiveC (b c : ℚ) : ℚ :=
  2 * b ^ 2 - b * c ^ 2 - 3 * b * c + c ^ 2

private def twentyFiveD (b c : ℚ) : ℚ :=
  b ^ 3 - 3 * b ^ 2 * c + b * c ^ 3 + 3 * b * c ^ 2 -
    c ^ 5 - c ^ 4 - c ^ 3

private def twentyFiveE (b c : ℚ) : ℚ :=
  b ^ 3 - 3 * b ^ 2 * c ^ 2 - 2 * b ^ 2 * c + b * c ^ 4 +
    3 * b * c ^ 3 + b * c ^ 2 + c ^ 5

private def twentyFiveF (b c : ℚ) : ℚ :=
  b ^ 5 - 3 * b ^ 4 * c - 4 * b ^ 3 * c ^ 3 + 3 * b ^ 3 * c ^ 2 +
    3 * b ^ 2 * c ^ 5 + 9 * b ^ 2 * c ^ 4 - b ^ 2 * c ^ 3 -
    b * c ^ 7 - 3 * b * c ^ 6 - 6 * b * c ^ 5 + c ^ 6

private def twentyFiveG (b c : ℚ) : ℚ :=
  3 * b ^ 4 - b ^ 3 * c ^ 2 - 9 * b ^ 3 * c + 10 * b ^ 2 * c ^ 2 +
    b * c ^ 4 - 5 * b * c ^ 3 + c ^ 6 + c ^ 4

private def twentyFiveH (b c : ℚ) : ℚ :=
  b ^ 7 - 6 * b ^ 6 * c + 4 * b ^ 5 * c ^ 3 + 15 * b ^ 5 * c ^ 2 -
    9 * b ^ 4 * c ^ 5 - 15 * b ^ 4 * c ^ 4 - 20 * b ^ 4 * c ^ 3 +
    5 * b ^ 3 * c ^ 7 + 24 * b ^ 3 * c ^ 6 + 21 * b ^ 3 * c ^ 5 +
    15 * b ^ 3 * c ^ 4 - b ^ 2 * c ^ 9 - 6 * b ^ 2 * c ^ 8 -
    21 * b ^ 2 * c ^ 7 - 13 * b ^ 2 * c ^ 6 - 6 * b ^ 2 * c ^ 5 +
    6 * b * c ^ 8 + 3 * b * c ^ 7 + b * c ^ 6 + c ^ 10

private def twentyFiveI (b c : ℚ) : ℚ :=
  b ^ 6 - 6 * b ^ 5 * c ^ 2 - 5 * b ^ 5 * c + 5 * b ^ 4 * c ^ 4 +
    25 * b ^ 4 * c ^ 3 + 10 * b ^ 4 * c ^ 2 - b ^ 3 * c ^ 6 -
    16 * b ^ 3 * c ^ 5 - 40 * b ^ 3 * c ^ 4 - 10 * b ^ 3 * c ^ 3 +
    4 * b ^ 2 * c ^ 7 + 17 * b ^ 2 * c ^ 6 + 30 * b ^ 2 * c ^ 5 +
    5 * b ^ 2 * c ^ 4 - b * c ^ 9 - 3 * b * c ^ 8 - 6 * b * c ^ 7 -
    10 * b * c ^ 6 - b * c ^ 5 + c ^ 7

private def twentyFiveJ (b c : ℚ) : ℚ :=
  b ^ 8 - 5 * b ^ 7 * c - 10 * b ^ 6 * c ^ 3 + 10 * b ^ 6 * c ^ 2 +
    19 * b ^ 5 * c ^ 5 + 45 * b ^ 5 * c ^ 4 - 10 * b ^ 5 * c ^ 3 -
    18 * b ^ 4 * c ^ 7 - 62 * b ^ 4 * c ^ 6 - 81 * b ^ 4 * c ^ 5 +
    5 * b ^ 4 * c ^ 4 + 7 * b ^ 3 * c ^ 9 + 36 * b ^ 3 * c ^ 8 +
    73 * b ^ 3 * c ^ 7 + 74 * b ^ 3 * c ^ 6 - b ^ 3 * c ^ 5 -
    b ^ 2 * c ^ 11 - 3 * b ^ 2 * c ^ 10 - 19 * b ^ 2 * c ^ 9 -
    37 * b ^ 2 * c ^ 8 - 36 * b ^ 2 * c ^ 7 - b * c ^ 12 -
    3 * b * c ^ 11 + 2 * b * c ^ 10 + 8 * b * c ^ 9 + 9 * b * c ^ 8 -
    c ^ 13 - c ^ 12 - c ^ 11 - c ^ 10 - c ^ 9

private structure TwentyFiveNormalizedDatum where
  xNum : ℚ
  yNum : ℚ
  den : ℚ

/-- Integral numerator and common square/cube denominator data for `(n+2)P`,
through `13P`. -/
private def twentyFiveNormalizedDatum (b c : ℚ) : ℕ → TwentyFiveNormalizedDatum
  | 0 => ⟨b, b * c, 1⟩
  | 1 => ⟨c, b - c, 1⟩
  | 2 => ⟨b * (b - c), -twentyFiveA b c * b ^ 2, c⟩
  | 3 => ⟨-c * b * twentyFiveA b c,
      b * twentyFiveB b c * c ^ 2, b - c⟩
  | 4 => ⟨(b - c) * twentyFiveB b c,
      c * twentyFiveC b c * (b - c) ^ 2, twentyFiveA b c⟩
  | 5 => ⟨c * b * twentyFiveA b c * twentyFiveC b c,
      twentyFiveD b c * b ^ 2 * twentyFiveA b c ^ 2, twentyFiveB b c⟩
  | 6 => ⟨b * twentyFiveB b c * twentyFiveD b c,
      -b * (b - c) * twentyFiveE b c * twentyFiveB b c ^ 2,
      c * twentyFiveC b c⟩
  | 7 => ⟨-c * (b - c) * twentyFiveC b c * twentyFiveE b c,
      twentyFiveF b c * c ^ 2 * twentyFiveC b c ^ 2, twentyFiveD b c⟩
  | 8 => ⟨b * twentyFiveD b c * twentyFiveF b c,
      c * twentyFiveA b c * twentyFiveG b c * b ^ 2 * twentyFiveD b c ^ 2,
      (b - c) * twentyFiveE b c⟩
  | 9 => ⟨c * b * (b - c) * twentyFiveA b c * twentyFiveE b c * twentyFiveG b c,
      b * twentyFiveH b c * (b - c) ^ 2 * twentyFiveE b c ^ 2,
      twentyFiveF b c⟩
  | 10 => ⟨twentyFiveF b c * twentyFiveH b c,
      -twentyFiveB b c * twentyFiveI b c * twentyFiveF b c ^ 2,
      c * twentyFiveA b c * twentyFiveG b c⟩
  | 11 => ⟨-c * b * twentyFiveA b c * twentyFiveB b c *
        twentyFiveG b c * twentyFiveI b c,
      (b - c) * twentyFiveJ b c * c ^ 2 * b ^ 2 *
        twentyFiveA b c ^ 2 * twentyFiveG b c ^ 2,
      twentyFiveH b c⟩
  | _ => ⟨0, 0, 0⟩

/-- The degree-40 noncuspidal factor is split into small elaboration units. -/
private def orderTwentyFiveNoncuspidalFactorChunk0 (b c : ℚ) : ℚ :=
  b ^ 25
  - 20 * b ^ 24 * c
  + 35 * b ^ 23 * c ^ 3
  + 190 * b ^ 23 * c ^ 2
  - 294 * b ^ 22 * c ^ 5
  - 595 * b ^ 22 * c ^ 4
  - 1140 * b ^ 22 * c ^ 3
  + 968 * b ^ 21 * c ^ 7
  + 4662 * b ^ 21 * c ^ 6
  + 4781 * b ^ 21 * c ^ 5
  + 4845 * b ^ 21 * c ^ 4
  - 1732 * b ^ 20 * c ^ 9
  - 13936 * b ^ 20 * c ^ 8
  - 34848 * b ^ 20 * c ^ 7
  - 24129 * b ^ 20 * c ^ 6
  - 15504 * b ^ 20 * c ^ 5
  + 1836 * b ^ 19 * c ^ 11
  + 22103 * b ^ 19 * c ^ 10
  + 93894 * b ^ 19 * c ^ 9
  + 163107 * b ^ 19 * c ^ 8
  + 85716 * b ^ 19 * c ^ 7
  + 38760 * b ^ 19 * c ^ 6
  - 1205 * b ^ 18 * c ^ 13
  - 20019 * b ^ 18 * c ^ 12
  - 130372 * b ^ 18 * c ^ 11
  - 392460 * b ^ 18 * c ^ 10
  - 535473 * b ^ 18 * c ^ 9
  - 227619 * b ^ 18 * c ^ 8
  - 77520 * b ^ 18 * c ^ 7
  + 494 * b ^ 17 * c ^ 15
  + 10660 * b ^ 17 * c ^ 14
  + 98421 * b ^ 17 * c ^ 13
  + 468205 * b ^ 17 * c ^ 12
  + 1136487 * b ^ 17 * c ^ 11
  + 1308684 * b ^ 17 * c ^ 10
  + 468286 * b ^ 17 * c ^ 9
  + 125970 * b ^ 17 * c ^ 8
  - 123 * b ^ 16 * c ^ 17
  - 3262 * b ^ 16 * c ^ 16

private def orderTwentyFiveNoncuspidalFactorChunk1 (b c : ℚ) : ℚ :=
  - 40426 * b ^ 16 * c ^ 15
  - 279858 * b ^ 16 * c ^ 14
  - 1129769 * b ^ 16 * c ^ 13
  - 2408509 * b ^ 16 * c ^ 12
  - 2465814 * b ^ 16 * c ^ 11
  - 763217 * b ^ 16 * c ^ 10
  - 167960 * b ^ 16 * c ^ 9
  + 17 * b ^ 15 * c ^ 19
  + 516 * b ^ 15 * c ^ 18
  + 8168 * b ^ 15 * c ^ 17
  + 71764 * b ^ 15 * c ^ 16
  + 468651 * b ^ 15 * c ^ 15
  + 1886674 * b ^ 15 * c ^ 14
  + 3838627 * b ^ 15 * c ^ 13
  + 3658941 * b ^ 15 * c ^ 12
  + 998998 * b ^ 15 * c ^ 11
  + 184756 * b ^ 15 * c ^ 10
  - b ^ 14 * c ^ 21
  - 28 * b ^ 14 * c ^ 20
  - 519 * b ^ 14 * c ^ 19
  + 7438 * b ^ 14 * c ^ 18
  + 23389 * b ^ 14 * c ^ 17
  - 305592 * b ^ 14 * c ^ 16
  - 2098031 * b ^ 14 * c ^ 15
  - 4635863 * b ^ 14 * c ^ 14
  - 4329039 * b ^ 14 * c ^ 13
  - 1058057 * b ^ 14 * c ^ 12
  - 167960 * b ^ 14 * c ^ 11
  - b ^ 13 * c ^ 22
  - 28 * b ^ 13 * c ^ 21
  - 15891 * b ^ 13 * c ^ 20
  - 140192 * b ^ 13 * c ^ 19
  - 500071 * b ^ 13 * c ^ 18
  - 633822 * b ^ 13 * c ^ 17
  + 1188769 * b ^ 13 * c ^ 16
  + 4178994 * b ^ 13 * c ^ 15
  + 4107246 * b ^ 13 * c ^ 14
  + 908908 * b ^ 13 * c ^ 13
  + 125970 * b ^ 13 * c ^ 12

private def orderTwentyFiveNoncuspidalFactorChunk2 (b c : ℚ) : ℚ :=
  - b ^ 12 * c ^ 23
  + 11638 * b ^ 12 * c ^ 22
  + 120525 * b ^ 12 * c ^ 21
  + 563119 * b ^ 12 * c ^ 20
  + 1517609 * b ^ 12 * c ^ 19
  + 2293518 * b ^ 12 * c ^ 18
  + 632668 * b ^ 12 * c ^ 17
  - 2643497 * b ^ 12 * c ^ 16
  - 3124836 * b ^ 12 * c ^ 15
  - 631787 * b ^ 12 * c ^ 14
  - 77520 * b ^ 12 * c ^ 13
  - 6503 * b ^ 11 * c ^ 24
  - 75959 * b ^ 11 * c ^ 23
  - 408288 * b ^ 11 * c ^ 22
  - 1310235 * b ^ 11 * c ^ 21
  - 2767285 * b ^ 11 * c ^ 20
  - 3867390 * b ^ 11 * c ^ 19
  - 2340965 * b ^ 11 * c ^ 18
  + 905113 * b ^ 11 * c ^ 17
  + 1895517 * b ^ 11 * c ^ 16
  + 352716 * b ^ 11 * c ^ 15
  + 38760 * b ^ 11 * c ^ 14
  + 2655 * b ^ 10 * c ^ 26
  + 34222 * b ^ 10 * c ^ 25
  + 211735 * b ^ 10 * c ^ 24
  + 801705 * b ^ 10 * c ^ 23
  + 2011320 * b ^ 10 * c ^ 22
  + 3497590 * b ^ 10 * c ^ 21
  + 4378848 * b ^ 10 * c ^ 20
  + 2977348 * b ^ 10 * c ^ 19
  + 220429 * b ^ 10 * c ^ 18
  - 905463 * b ^ 10 * c ^ 17
  - 156009 * b ^ 10 * c ^ 16
  - 15504 * b ^ 10 * c ^ 15
  - 770 * b ^ 9 * c ^ 28
  - 10530 * b ^ 9 * c ^ 27
  - 72725 * b ^ 9 * c ^ 26
  - 323700 * b ^ 9 * c ^ 25
  - 992925 * b ^ 9 * c ^ 24

private def orderTwentyFiveNoncuspidalFactorChunk3 (b c : ℚ) : ℚ :=
  - 2123925 * b ^ 9 * c ^ 23
  - 3189100 * b ^ 9 * c ^ 22
  - 3597549 * b ^ 9 * c ^ 21
  - 2466272 * b ^ 9 * c ^ 20
  - 551706 * b ^ 9 * c ^ 19
  + 333432 * b ^ 9 * c ^ 18
  + 53466 * b ^ 9 * c ^ 17
  + 4845 * b ^ 9 * c ^ 16
  + 151 * b ^ 8 * c ^ 30
  + 2065 * b ^ 8 * c ^ 29
  + 15405 * b ^ 8 * c ^ 28
  + 78125 * b ^ 8 * c ^ 27
  + 289875 * b ^ 8 * c ^ 26
  + 793809 * b ^ 8 * c ^ 25
  + 1558300 * b ^ 8 * c ^ 24
  + 2115200 * b ^ 8 * c ^ 23
  + 2191026 * b ^ 8 * c ^ 22
  + 1471103 * b ^ 8 * c ^ 21
  + 419817 * b ^ 8 * c ^ 20
  - 91398 * b ^ 8 * c ^ 19
  - 13699 * b ^ 8 * c ^ 18
  - 1140 * b ^ 8 * c ^ 17
  - 18 * b ^ 7 * c ^ 32
  - 212 * b ^ 7 * c ^ 31
  - 1624 * b ^ 7 * c ^ 30
  - 9375 * b ^ 7 * c ^ 29
  - 41875 * b ^ 7 * c ^ 28
  - 147447 * b ^ 7 * c ^ 27
  - 400098 * b ^ 7 * c ^ 26
  - 785054 * b ^ 7 * c ^ 25
  - 1011950 * b ^ 7 * c ^ 24
  - 988449 * b ^ 7 * c ^ 23
  - 648076 * b ^ 7 * c ^ 22
  - 203267 * b ^ 7 * c ^ 21
  + 17571 * b ^ 7 * c ^ 20
  + 2471 * b ^ 7 * c ^ 19
  + 190 * b ^ 7 * c ^ 18
  + b ^ 6 * c ^ 34
  + 3 * b ^ 6 * c ^ 33

private def orderTwentyFiveNoncuspidalFactorChunk4 (b c : ℚ) : ℚ :=
  19 * b ^ 6 * c ^ 32
  + 147 * b ^ 6 * c ^ 31
  + 1251 * b ^ 6 * c ^ 30
  + 7754 * b ^ 6 * c ^ 29
  + 34987 * b ^ 6 * c ^ 28
  + 115557 * b ^ 6 * c ^ 27
  + 262762 * b ^ 6 * c ^ 26
  + 342221 * b ^ 6 * c ^ 25
  + 326004 * b ^ 6 * c ^ 24
  + 210737 * b ^ 6 * c ^ 23
  + 69179 * b ^ 6 * c ^ 22
  - 2115 * b ^ 6 * c ^ 21
  - 280 * b ^ 6 * c ^ 20
  - 20 * b ^ 6 * c ^ 19
  + b ^ 5 * c ^ 35
  + 3 * b ^ 5 * c ^ 34
  + 19 * b ^ 5 * c ^ 33
  + 147 * b ^ 5 * c ^ 32
  + 516 * b ^ 5 * c ^ 31
  + 929 * b ^ 5 * c ^ 30
  - 752 * b ^ 5 * c ^ 29
  - 13971 * b ^ 5 * c ^ 28
  - 55738 * b ^ 5 * c ^ 27
  - 79879 * b ^ 5 * c ^ 26
  - 77124 * b ^ 5 * c ^ 25
  - 49915 * b ^ 5 * c ^ 24
  - 16870 * b ^ 5 * c ^ 23
  + 120 * b ^ 5 * c ^ 22
  + 15 * b ^ 5 * c ^ 21
  + b ^ 5 * c ^ 20
  + b ^ 4 * c ^ 36
  + 3 * b ^ 4 * c ^ 35
  + 19 * b ^ 4 * c ^ 34
  + 112 * b ^ 4 * c ^ 33
  + 411 * b ^ 4 * c ^ 32
  + 851 * b ^ 4 * c ^ 31
  + 703 * b ^ 4 * c ^ 30
  + 69 * b ^ 4 * c ^ 29
  + 7787 * b ^ 4 * c ^ 28

private def orderTwentyFiveNoncuspidalFactorChunk5 (b c : ℚ) : ℚ :=
  12961 * b ^ 4 * c ^ 27
  + 12930 * b ^ 4 * c ^ 26
  + 8450 * b ^ 4 * c ^ 25
  + 2925 * b ^ 4 * c ^ 24
  + b ^ 3 * c ^ 37
  + 3 * b ^ 3 * c ^ 36
  - 17 * b ^ 3 * c ^ 35
  - 133 * b ^ 3 * c ^ 34
  - 459 * b ^ 3 * c ^ 33
  - 1024 * b ^ 3 * c ^ 32
  - 1447 * b ^ 3 * c ^ 31
  - 618 * b ^ 3 * c ^ 30
  - 1183 * b ^ 3 * c ^ 29
  - 1649 * b ^ 3 * c ^ 28
  - 1560 * b ^ 3 * c ^ 27
  - 1000 * b ^ 3 * c ^ 26
  - 351 * b ^ 3 * c ^ 25
  + b ^ 2 * c ^ 38
  + 6 * b ^ 2 * c ^ 37
  + 21 * b ^ 2 * c ^ 36
  + 56 * b ^ 2 * c ^ 35
  + 126 * b ^ 2 * c ^ 34
  + 251 * b ^ 2 * c ^ 33
  + 434 * b ^ 2 * c ^ 32
  + 273 * b ^ 2 * c ^ 31
  + 216 * b ^ 2 * c ^ 30
  + 181 * b ^ 2 * c ^ 29
  + 135 * b ^ 2 * c ^ 28
  + 78 * b ^ 2 * c ^ 27
  + 27 * b ^ 2 * c ^ 26
  - b * c ^ 34
  - 28 * b * c ^ 33
  - 21 * b * c ^ 32
  - 15 * b * c ^ 31
  - 10 * b * c ^ 30
  - 6 * b * c ^ 29
  - 3 * b * c ^ 28
  - b * c ^ 27
  - c ^ 35

/-- The degree-40 noncuspidal factor of the normalized `12P/13P` collision. -/
def orderTwentyFiveNoncuspidalFactor (b c : ℚ) : ℚ :=
  orderTwentyFiveNoncuspidalFactorChunk0 b c +
    orderTwentyFiveNoncuspidalFactorChunk1 b c +
    orderTwentyFiveNoncuspidalFactorChunk2 b c +
    orderTwentyFiveNoncuspidalFactorChunk3 b c +
    orderTwentyFiveNoncuspidalFactorChunk4 b c +
    orderTwentyFiveNoncuspidalFactorChunk5 b c

/- The raw `X₁(25)` equation tabulated as `F25` in Andrew Sutherland's
database.  It is kept private: the checked consumer below immediately
identifies its noncuspidal Tate substitution with the public degree-40
factor.  The durable source, retrieval date, and content hash are recorded
in `docs/PRIOR_ART.md`.  The displayed identity is independently checked by
Lean's ring normalizer. -/
private def orderTwentyFiveRawSutherlandCoefficient0 (s : ℚ) : ℚ :=
  s ^ 10

private def orderTwentyFiveRawSutherlandCoefficient1 (s : ℚ) : ℚ :=
  6 * s ^ 10 - 28 * s ^ 9 + 21 * s ^ 8 - 15 * s ^ 7 +
    10 * s ^ 6 - 6 * s ^ 5 + 3 * s ^ 4 - s ^ 3

private def orderTwentyFiveRawSutherlandCoefficient2 (s : ℚ) : ℚ :=
  s ^ 15 - 6 * s ^ 14 + 21 * s ^ 13 - 56 * s ^ 12 + 126 * s ^ 11 -
    231 * s ^ 10 + 266 * s ^ 9 - 126 * s ^ 8 + 96 * s ^ 7 -
    91 * s ^ 6 + 75 * s ^ 5 - 45 * s ^ 4 + 15 * s ^ 3

private def orderTwentyFiveRawSutherlandCoefficient3 (s : ℚ) : ℚ :=
  s ^ 15 - 9 * s ^ 14 + 25 * s ^ 13 - 35 * s ^ 12 + 45 * s ^ 11 -
    181 * s ^ 10 + 569 * s ^ 9 - 705 * s ^ 8 + 5 * s ^ 7 +
    470 * s ^ 6 - 540 * s ^ 5 + 340 * s ^ 4 - 105 * s ^ 3

private def orderTwentyFiveRawSutherlandCoefficient4 (s : ℚ) : ℚ :=
  s ^ 15 - 12 * s ^ 14 + 48 * s ^ 13 - 49 * s ^ 12 - 165 * s ^ 11 +
    609 * s ^ 10 - 433 * s ^ 9 - 1623 * s ^ 8 + 4299 * s ^ 7 -
    4615 * s ^ 6 + 3435 * s ^ 5 - 1740 * s ^ 4 + 455 * s ^ 3

private def orderTwentyFiveRawSutherlandCoefficient5 (s : ℚ) : ℚ :=
  s ^ 15 - 15 * s ^ 14 + 90 * s ^ 13 - 245 * s ^ 12 + 90 * s ^ 11 +
    1587 * s ^ 10 - 6145 * s ^ 9 + 12270 * s ^ 8 - 15060 * s ^ 7 +
    12520 * s ^ 6 - 8214 * s ^ 5 + 3660 * s ^ 4 - 685 * s ^ 3 -
    120 * s ^ 2 + 15 * s - 1

private def orderTwentyFiveRawSutherlandCoefficient6 (s : ℚ) : ℚ :=
  s ^ 15 - 18 * s ^ 14 + 151 * s ^ 13 - 770 * s ^ 12 + 2655 * s ^ 11 -
    6558 * s ^ 10 + 11834 * s ^ 9 - 15408 * s ^ 8 + 14630 * s ^ 7 -
    11195 * s ^ 6 + 7227 * s ^ 5 - 2441 * s ^ 4 - 388 * s ^ 3 +
    555 * s ^ 2 - 70 * s + 5

private def orderTwentyFiveRawSutherlandCoefficient7 (s : ℚ) : ℚ :=
  -21 * s ^ 10 + 161 * s ^ 9 - 351 * s ^ 8 - 144 * s ^ 7 +
    1289 * s ^ 6 - 789 * s ^ 5 - 1551 * s ^ 4 + 2166 * s ^ 3 -
    996 * s ^ 2 + 126 * s - 10

private def orderTwentyFiveRawSutherlandCoefficient8 (s : ℚ) : ℚ :=
  -6 * s ^ 10 + 74 * s ^ 9 - 345 * s ^ 8 + 690 * s ^ 7 -
    185 * s ^ 6 - 1659 * s ^ 5 + 3051 * s ^ 4 - 2320 * s ^ 3 +
    840 * s ^ 2 - 105 * s + 10

private def orderTwentyFiveRawSutherlandCoefficient9 (s : ℚ) : ℚ :=
  -s ^ 10 + 17 * s ^ 9 - 123 * s ^ 8 + 494 * s ^ 7 - 1205 * s ^ 6 +
    1836 * s ^ 5 - 1732 * s ^ 4 + 968 * s ^ 3 - 294 * s ^ 2 +
    35 * s - 5

private def orderTwentyFiveRawSutherlandCoefficient10 (_s : ℚ) : ℚ :=
  1

private def orderTwentyFiveRawSutherlandPolynomialChunk0 (r s : ℚ) : ℚ :=
  orderTwentyFiveRawSutherlandCoefficient10 s * r ^ 10 +
    orderTwentyFiveRawSutherlandCoefficient9 s * r ^ 9 +
    orderTwentyFiveRawSutherlandCoefficient8 s * r ^ 8

private def orderTwentyFiveRawSutherlandPolynomialChunk1 (r s : ℚ) : ℚ :=
  orderTwentyFiveRawSutherlandCoefficient7 s * r ^ 7 +
    orderTwentyFiveRawSutherlandCoefficient6 s * r ^ 6

private def orderTwentyFiveRawSutherlandPolynomialChunk2 (r s : ℚ) : ℚ :=
  orderTwentyFiveRawSutherlandCoefficient5 s * r ^ 5

private def orderTwentyFiveRawSutherlandPolynomialChunk3 (r s : ℚ) : ℚ :=
  orderTwentyFiveRawSutherlandCoefficient4 s * r ^ 4

private def orderTwentyFiveRawSutherlandPolynomialChunk4 (r s : ℚ) : ℚ :=
  orderTwentyFiveRawSutherlandCoefficient3 s * r ^ 3 +
    orderTwentyFiveRawSutherlandCoefficient2 s * r ^ 2

private def orderTwentyFiveRawSutherlandPolynomialChunk5 (r s : ℚ) : ℚ :=
  orderTwentyFiveRawSutherlandCoefficient1 s * r +
    orderTwentyFiveRawSutherlandCoefficient0 s

private def orderTwentyFiveRawSutherlandPolynomial (r s : ℚ) : ℚ :=
  orderTwentyFiveRawSutherlandPolynomialChunk0 r s +
    orderTwentyFiveRawSutherlandPolynomialChunk1 r s +
    orderTwentyFiveRawSutherlandPolynomialChunk2 r s +
    orderTwentyFiveRawSutherlandPolynomialChunk3 r s +
    orderTwentyFiveRawSutherlandPolynomialChunk4 r s +
    orderTwentyFiveRawSutherlandPolynomialChunk5 r s

/- Factorized abscissas on Sutherland's raw Tate chart.  These remain
private implementation data for the checked Brunault bridge. -/
private def orderTwentyFiveRawXTwo (r s : ℚ) : ℚ :=
  r * s * (r - 1)

private def orderTwentyFiveRawXThree (r s : ℚ) : ℚ :=
  s * (r - 1)

private def orderTwentyFiveRawXFour (r _s : ℚ) : ℚ :=
  r * (r - 1)

private def orderTwentyFiveRawXSix (r s : ℚ) : ℚ :=
  s * (r - 1) * (r - s) / (s - 1) ^ 2

private def orderTwentyFiveRawXSeven (r s : ℚ) : ℚ :=
  r * s * (r - 1) * (s - 1) * (r * s - 2 * r + 1) / (r - s) ^ 2

private def orderTwentyFiveRawXEight (r s : ℚ) : ℚ :=
  r * (r - 1) * (r - s) * (r - s ^ 2 + s - 1) /
    (r * s - 2 * r + 1) ^ 2

private def orderTwentyFiveRawXNine (r s : ℚ) : ℚ :=
  s * (r - 1) * (r * s - 2 * r + 1) *
      (r * s ^ 2 - 3 * r * s + r + s ^ 2) /
    (r - s ^ 2 + s - 1) ^ 2

private def orderTwentyFiveRawXEleven (r s : ℚ) : ℚ :=
  r * s * (r - 1) * (s - 1) *
      (r * s ^ 2 - 3 * r * s + r + s ^ 2) *
      (r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) /
    (r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s) ^ 2

private def orderTwentyFiveRawXTwelve (r s : ℚ) : ℚ :=
  (r - 1) *
      (r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s) *
      (r ^ 3 - r ^ 2 * s ^ 4 + 5 * r ^ 2 * s ^ 3 -
        9 * r ^ 2 * s ^ 2 + 4 * r ^ 2 * s - 2 * r ^ 2 -
        r * s ^ 3 + 6 * r * s ^ 2 - 3 * r * s + r - s ^ 3) /
    ((s - 1) ^ 2 *
      (r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) ^ 2)

private def orderTwentyFiveRawYFour (r s : ℚ) : ℚ :=
  ((orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwo r s) /
      (orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwelve r s)) *
    ((orderTwentyFiveRawXThree r s - orderTwentyFiveRawXEleven r s) /
      (orderTwentyFiveRawXThree r s - orderTwentyFiveRawXNine r s))

private def orderTwentyFiveRawYSeven (r s : ℚ) : ℚ :=
  ((orderTwentyFiveRawXSeven r s - orderTwentyFiveRawXNine r s) /
      (orderTwentyFiveRawXSeven r s - orderTwentyFiveRawXFour r s)) *
    ((0 - orderTwentyFiveRawXTwelve r s) /
      (0 - orderTwentyFiveRawXThree r s))

private def orderTwentyFiveRawYTwo (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawXTwo r s /
      (orderTwentyFiveRawXTwo r s - orderTwentyFiveRawXSix r s)) *
    ((orderTwentyFiveRawXEleven r s - orderTwentyFiveRawXSeven r s) /
      (orderTwentyFiveRawXEleven r s - orderTwentyFiveRawXEight r s))

private def orderTwentyFiveRawYEight (r s : ℚ) : ℚ :=
  ((orderTwentyFiveRawXEight r s - orderTwentyFiveRawXFour r s) /
      orderTwentyFiveRawXEight r s) *
    ((orderTwentyFiveRawXSix r s - orderTwentyFiveRawXThree r s) /
      (orderTwentyFiveRawXSix r s - orderTwentyFiveRawXSeven r s))

private def orderTwentyFiveRawYNine (r s : ℚ) : ℚ :=
  ((orderTwentyFiveRawXNine r s - orderTwentyFiveRawXEight r s) /
      (orderTwentyFiveRawXNine r s - orderTwentyFiveRawXTwo r s)) *
    ((orderTwentyFiveRawXTwelve r s - orderTwentyFiveRawXSix r s) /
      (orderTwentyFiveRawXTwelve r s - orderTwentyFiveRawXEleven r s))

private def orderTwentyFiveRawYThree (r s : ℚ) : ℚ :=
  ((orderTwentyFiveRawXThree r s - orderTwentyFiveRawXEleven r s) /
      (orderTwentyFiveRawXThree r s - orderTwentyFiveRawXNine r s)) *
    ((orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwo r s) /
      (orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwelve r s))

private def orderTwentyFiveRawBrunaultU (r s : ℚ) : ℚ :=
  orderTwentyFiveRawYFour r s * orderTwentyFiveRawYSeven r s

private def orderTwentyFiveRawBrunaultV (r s : ℚ) : ℚ :=
  -(orderTwentyFiveRawYNine r s * orderTwentyFiveRawYThree r s)

private def orderTwentyFiveRawYRelationZero (r s : ℚ) : ℚ :=
  orderTwentyFiveRawYSeven r s - orderTwentyFiveRawYNine r s -
    orderTwentyFiveRawYSeven r s * orderTwentyFiveRawYEight r s *
      (orderTwentyFiveRawYTwo r s - orderTwentyFiveRawYSeven r s)

private theorem orderTwentyFiveRawSutherlandPolynomial_eq_orbitData
    (r s : ℚ) :
    orderTwentyFiveRawSutherlandPolynomial r s =
      OrderTwentyFiveRawOrbitData.sutherlandPolynomial r s := by
  simp only [orderTwentyFiveRawSutherlandPolynomial,
    orderTwentyFiveRawSutherlandPolynomialChunk0,
    orderTwentyFiveRawSutherlandPolynomialChunk1,
    orderTwentyFiveRawSutherlandPolynomialChunk2,
    orderTwentyFiveRawSutherlandPolynomialChunk3,
    orderTwentyFiveRawSutherlandPolynomialChunk4,
    orderTwentyFiveRawSutherlandPolynomialChunk5,
    orderTwentyFiveRawSutherlandCoefficient0,
    orderTwentyFiveRawSutherlandCoefficient1,
    orderTwentyFiveRawSutherlandCoefficient2,
    orderTwentyFiveRawSutherlandCoefficient3,
    orderTwentyFiveRawSutherlandCoefficient4,
    orderTwentyFiveRawSutherlandCoefficient5,
    orderTwentyFiveRawSutherlandCoefficient6,
    orderTwentyFiveRawSutherlandCoefficient7,
    orderTwentyFiveRawSutherlandCoefficient8,
    orderTwentyFiveRawSutherlandCoefficient9,
    orderTwentyFiveRawSutherlandCoefficient10,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomial,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient0,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient1,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient2,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient3,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient4,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient5,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient6,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient7,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient8,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient9,
    OrderTwentyFiveRawOrbitData.sutherlandPolynomialCoefficient10]
  ring

private theorem orderTwentyFiveRawXEleven_sub_XEight_eq_poleFactor
    (r s : ℚ)
    (hC : r * s - 2 * r + 1 ≠ 0)
    (hE : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0) :
    orderTwentyFiveRawXEleven r s - orderTwentyFiveRawXEight r s =
      -(r * (r - 1) * OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactor r s) /
        ((r * s - 2 * r + 1) ^ 2 *
          (r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s) ^ 2) := by
  have hC' : r * (s - 2) + 1 ≠ 0 := by
    intro hz
    apply hC
    linear_combination hz
  have hE' : r * (r - s ^ 3 + s ^ 2 * 3 - s * 4) + s ≠ 0 := by
    intro hz
    apply hE
    linear_combination hz
  simp only [orderTwentyFiveRawXEight, orderTwentyFiveRawXEleven]
  field_simp [hC, hC', hE, hE']
  simp only [OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactor,
    OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactorCoefficient6]
  ring

private theorem orderTwentyFiveRawXSix_sub_XSeven_eq_poleFactor
    (r s : ℚ) (hs1 : s - 1 ≠ 0) (hrs : r - s ≠ 0) :
    orderTwentyFiveRawXSix r s - orderTwentyFiveRawXSeven r s =
      s * (r - 1) * OrderTwentyFiveRawOrbitData.rawUnitEightPoleFactor r s /
        ((s - 1) ^ 2 * (r - s) ^ 2) := by
  simp only [orderTwentyFiveRawXSix, orderTwentyFiveRawXSeven]
  field_simp [hs1, hrs]
  simp only [OrderTwentyFiveRawOrbitData.rawUnitEightPoleFactor,
    OrderTwentyFiveRawOrbitData.rawUnitEightPoleFactorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitEightPoleFactorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitEightPoleFactorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitEightPoleFactorCoefficient3]
  ring

private theorem orderTwentyFiveRawXTwelve_sub_XEleven_eq_poleFactor
    (r s : ℚ) (hs1 : s - 1 ≠ 0)
    (hE : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0)
    (hG : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0) :
    orderTwentyFiveRawXTwelve r s - orderTwentyFiveRawXEleven r s =
      (r - 1) * OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactor r s /
        ((s - 1) ^ 2 *
          (r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s) ^ 2 *
          (r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) ^ 2) := by
  have hE' : r * (r - s ^ 3 + s ^ 2 * 3 - s * 4) + s ≠ 0 := by
    intro hz
    apply hE
    linear_combination hz
  have hG' : r * (r * (s - 3) + s + 3) - s ^ 2 - 1 ≠ 0 := by
    intro hz
    apply hG
    linear_combination hz
  simp only [orderTwentyFiveRawXEleven, orderTwentyFiveRawXTwelve]
  field_simp [hs1, hE, hE', hG, hG']
  simp only [OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactor,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient7,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient8,
    OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactorCoefficient9]
  ring

private theorem orderTwentyFiveRawXFour_sub_XTwelve_eq_poleFactor
    (r s : ℚ) (hs1 : s - 1 ≠ 0)
    (hG : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0) :
    orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwelve r s =
      (r - 1) * (r * s - 2 * r + 1) ^ 2 *
          OrderTwentyFiveRawOrbitData.rawUnitFourPoleFactor r s /
        ((s - 1) ^ 2 *
          (r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1) ^ 2) := by
  have hG' : r * (r * (s - 3) + s + 3) - s ^ 2 - 1 ≠ 0 := by
    intro hz
    apply hG
    linear_combination hz
  simp only [orderTwentyFiveRawXFour, orderTwentyFiveRawXTwelve]
  field_simp [hs1, hG, hG']
  simp only [OrderTwentyFiveRawOrbitData.rawUnitFourPoleFactor]
  ring

private theorem orderTwentyFiveRawYSeven_eq_orbitData
    (r s : ℚ)
    (hs1 : s - 1 ≠ 0) (hrs : r - s ≠ 0)
    (hD : r - s ^ 2 + s - 1 ≠ 0)
    (hG : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0)
    (h74 : orderTwentyFiveRawXSeven r s -
      orderTwentyFiveRawXFour r s ≠ 0)
    (h3 : orderTwentyFiveRawXThree r s ≠ 0)
    (hden : OrderTwentyFiveRawOrbitData.rawUnitOneDenominator r s ≠ 0) :
    orderTwentyFiveRawYSeven r s =
      OrderTwentyFiveRawOrbitData.rawUnitOneNumerator r s /
        OrderTwentyFiveRawOrbitData.rawUnitOneDenominator r s := by
  simp only [orderTwentyFiveRawYSeven]
  rw [div_mul_div_comm]
  have hneg3 : 0 - orderTwentyFiveRawXThree r s ≠ 0 := by
    simpa only [zero_sub, neg_ne_zero] using h3
  apply (div_eq_div_iff (mul_ne_zero h74 hneg3) hden).2
  simp only [orderTwentyFiveRawXThree, orderTwentyFiveRawXFour,
    orderTwentyFiveRawXSeven, orderTwentyFiveRawXNine,
    orderTwentyFiveRawXTwelve]
  have hs1sq := pow_ne_zero 2 hs1
  have hrssq := pow_ne_zero 2 hrs
  have hDsq := pow_ne_zero 2 hD
  have hGsq := pow_ne_zero 2 hG
  have hG' : r * (r * (s - 3) + s + 3) - s ^ 2 - 1 ≠ 0 := by
    intro hz
    apply hG
    linear_combination hz
  field_simp [hs1, hrs, hD, hG, hG', hs1sq, hrssq, hDsq, hGsq]
  simp only [OrderTwentyFiveRawOrbitData.rawUnitOneNumerator,
    OrderTwentyFiveRawOrbitData.rawUnitOneNumeratorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitOneNumeratorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitOneNumeratorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitOneNumeratorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitOneNumeratorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitOneNumeratorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitOneNumeratorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitOneNumeratorCoefficient7,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominator,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominatorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominatorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominatorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominatorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominatorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominatorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominatorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitOneDenominatorCoefficient7]
  ring

private theorem orderTwentyFiveRawYTwo_eq_orbitData
    (r s : ℚ)
    (hs1 : s - 1 ≠ 0) (hrs : r - s ≠ 0)
    (hC : r * s - 2 * r + 1 ≠ 0)
    (hE : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0)
    (h26 : orderTwentyFiveRawXTwo r s -
      orderTwentyFiveRawXSix r s ≠ 0)
    (h118 : orderTwentyFiveRawXEleven r s -
      orderTwentyFiveRawXEight r s ≠ 0)
    (hden : OrderTwentyFiveRawOrbitData.rawUnitTwoDenominator r s ≠ 0) :
    orderTwentyFiveRawYTwo r s =
      OrderTwentyFiveRawOrbitData.rawUnitTwoNumerator r s /
        OrderTwentyFiveRawOrbitData.rawUnitTwoDenominator r s := by
  simp only [orderTwentyFiveRawYTwo]
  rw [div_mul_div_comm]
  apply (div_eq_div_iff (mul_ne_zero h26 h118) hden).2
  simp only [orderTwentyFiveRawXTwo, orderTwentyFiveRawXSix,
    orderTwentyFiveRawXSeven, orderTwentyFiveRawXEight,
    orderTwentyFiveRawXEleven]
  have hs1sq := pow_ne_zero 2 hs1
  have hrssq := pow_ne_zero 2 hrs
  have hCsq := pow_ne_zero 2 hC
  have hEsq := pow_ne_zero 2 hE
  have hC' : r * (s - 2) + 1 ≠ 0 := by
    intro hz
    apply hC
    linear_combination hz
  have hE' : r * (r - s ^ 3 + s ^ 2 * 3 - s * 4) + s ≠ 0 := by
    intro hz
    apply hE
    linear_combination hz
  field_simp [hs1, hrs, hC, hC', hE, hE', hs1sq, hrssq, hCsq, hEsq]
  simp only [OrderTwentyFiveRawOrbitData.rawUnitTwoNumerator,
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumeratorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumeratorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumeratorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumeratorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumeratorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumeratorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumeratorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumeratorCoefficient7,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominator,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient7,
    OrderTwentyFiveRawOrbitData.rawUnitTwoDenominatorCoefficient8]
  ring

private theorem orderTwentyFiveRawYFour_eq_orbitData
    (r s : ℚ)
    (hs1 : s - 1 ≠ 0)
    (hC : r * s - 2 * r + 1 ≠ 0)
    (hD : r - s ^ 2 + s - 1 ≠ 0)
    (hE : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0)
    (hG : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0)
    (h412 : orderTwentyFiveRawXFour r s -
      orderTwentyFiveRawXTwelve r s ≠ 0)
    (h39 : orderTwentyFiveRawXThree r s -
      orderTwentyFiveRawXNine r s ≠ 0)
    (hden : OrderTwentyFiveRawOrbitData.rawUnitFourDenominator r s ≠ 0) :
    orderTwentyFiveRawYFour r s =
      OrderTwentyFiveRawOrbitData.rawUnitFourNumerator r s /
        OrderTwentyFiveRawOrbitData.rawUnitFourDenominator r s := by
  simp only [orderTwentyFiveRawYFour]
  rw [div_mul_div_comm]
  apply (div_eq_div_iff (mul_ne_zero h412 h39) hden).2
  simp only [orderTwentyFiveRawXTwo, orderTwentyFiveRawXThree,
    orderTwentyFiveRawXFour, orderTwentyFiveRawXNine,
    orderTwentyFiveRawXEleven, orderTwentyFiveRawXTwelve]
  have hs1sq := pow_ne_zero 2 hs1
  have hCsq := pow_ne_zero 2 hC
  have hDsq := pow_ne_zero 2 hD
  have hEsq := pow_ne_zero 2 hE
  have hGsq := pow_ne_zero 2 hG
  have hC' : r * (s - 2) + 1 ≠ 0 := by
    intro hz
    apply hC
    linear_combination hz
  have hE' : r * (r - s ^ 3 + s ^ 2 * 3 - s * 4) + s ≠ 0 := by
    intro hz
    apply hE
    linear_combination hz
  have hG' : r * (r * (s - 3) + s + 3) - s ^ 2 - 1 ≠ 0 := by
    intro hz
    apply hG
    linear_combination hz
  field_simp [hs1, hC, hC', hD, hE, hE', hG, hG',
    hs1sq, hCsq, hDsq, hEsq, hGsq]
  simp only [OrderTwentyFiveRawOrbitData.rawUnitFourNumerator,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient7,
    OrderTwentyFiveRawOrbitData.rawUnitFourNumeratorCoefficient8,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominator,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient7,
    OrderTwentyFiveRawOrbitData.rawUnitFourDenominatorCoefficient8]
  ring

private theorem orderTwentyFiveRawYEight_eq_orbitData
    (r s : ℚ)
    (hs1 : s - 1 ≠ 0) (hrs : r - s ≠ 0)
    (hC : r * s - 2 * r + 1 ≠ 0)
    (h8 : orderTwentyFiveRawXEight r s ≠ 0)
    (h67 : orderTwentyFiveRawXSix r s -
      orderTwentyFiveRawXSeven r s ≠ 0)
    (hden : OrderTwentyFiveRawOrbitData.rawUnitEightDenominator r s ≠ 0) :
    orderTwentyFiveRawYEight r s =
      OrderTwentyFiveRawOrbitData.rawUnitEightNumerator r s /
        OrderTwentyFiveRawOrbitData.rawUnitEightDenominator r s := by
  simp only [orderTwentyFiveRawYEight]
  rw [div_mul_div_comm]
  apply (div_eq_div_iff (mul_ne_zero h8 h67) hden).2
  simp only [orderTwentyFiveRawXThree, orderTwentyFiveRawXFour,
    orderTwentyFiveRawXSix, orderTwentyFiveRawXSeven,
    orderTwentyFiveRawXEight]
  have hs1sq := pow_ne_zero 2 hs1
  have hrssq := pow_ne_zero 2 hrs
  have hCsq := pow_ne_zero 2 hC
  have hC' : r * (s - 2) + 1 ≠ 0 := by
    intro hz
    apply hC
    linear_combination hz
  field_simp [hs1, hrs, hC, hC', hs1sq, hrssq, hCsq]
  simp only [OrderTwentyFiveRawOrbitData.rawUnitEightNumerator,
    OrderTwentyFiveRawOrbitData.rawUnitEightNumeratorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitEightNumeratorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitEightNumeratorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitEightNumeratorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitEightDenominator,
    OrderTwentyFiveRawOrbitData.rawUnitEightDenominatorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitEightDenominatorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitEightDenominatorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitEightDenominatorCoefficient3]
  ring

private theorem orderTwentyFiveRawYNine_eq_orbitData
    (r s : ℚ)
    (hs1 : s - 1 ≠ 0)
    (hC : r * s - 2 * r + 1 ≠ 0)
    (hD : r - s ^ 2 + s - 1 ≠ 0)
    (hE : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0)
    (hG : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0)
    (h92 : orderTwentyFiveRawXNine r s -
      orderTwentyFiveRawXTwo r s ≠ 0)
    (h1211 : orderTwentyFiveRawXTwelve r s -
      orderTwentyFiveRawXEleven r s ≠ 0)
    (hden : OrderTwentyFiveRawOrbitData.rawUnitNineDenominator r s ≠ 0) :
    orderTwentyFiveRawYNine r s =
      OrderTwentyFiveRawOrbitData.rawUnitNineNumerator r s /
        OrderTwentyFiveRawOrbitData.rawUnitNineDenominator r s := by
  simp only [orderTwentyFiveRawYNine]
  rw [div_mul_div_comm]
  apply (div_eq_div_iff (mul_ne_zero h92 h1211) hden).2
  simp only [orderTwentyFiveRawXTwo, orderTwentyFiveRawXSix,
    orderTwentyFiveRawXEight, orderTwentyFiveRawXNine,
    orderTwentyFiveRawXEleven, orderTwentyFiveRawXTwelve]
  have hs1sq := pow_ne_zero 2 hs1
  have hCsq := pow_ne_zero 2 hC
  have hDsq := pow_ne_zero 2 hD
  have hEsq := pow_ne_zero 2 hE
  have hGsq := pow_ne_zero 2 hG
  have hC' : r * (s - 2) + 1 ≠ 0 := by
    intro hz
    apply hC
    linear_combination hz
  have hE' : r * (r - s ^ 3 + s ^ 2 * 3 - s * 4) + s ≠ 0 := by
    intro hz
    apply hE
    linear_combination hz
  have hG' : r * (r * (s - 3) + s + 3) - s ^ 2 - 1 ≠ 0 := by
    intro hz
    apply hG
    linear_combination hz
  field_simp [hs1, hC, hC', hD, hE, hE', hG, hG',
    hs1sq, hCsq, hDsq, hEsq, hGsq]
  simp only [OrderTwentyFiveRawOrbitData.rawUnitNineNumerator,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient7,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient8,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient9,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient10,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient11,
    OrderTwentyFiveRawOrbitData.rawUnitNineNumeratorCoefficient12,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominator,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient0,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient1,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient2,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient3,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient4,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient5,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient6,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient7,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient8,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient9,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient10,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient11,
    OrderTwentyFiveRawOrbitData.rawUnitNineDenominatorCoefficient12]
  ring

private theorem orderTwentyFiveRawYRelationZero_of_curve
    (r s : ℚ)
    (hs1 : s - 1 ≠ 0) (hrs : r - s ≠ 0)
    (hC : r * s - 2 * r + 1 ≠ 0)
    (hD : r - s ^ 2 + s - 1 ≠ 0)
    (hE : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0)
    (hG : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0)
    (h74 : orderTwentyFiveRawXSeven r s -
      orderTwentyFiveRawXFour r s ≠ 0)
    (h3 : orderTwentyFiveRawXThree r s ≠ 0)
    (h26 : orderTwentyFiveRawXTwo r s -
      orderTwentyFiveRawXSix r s ≠ 0)
    (h118 : orderTwentyFiveRawXEleven r s -
      orderTwentyFiveRawXEight r s ≠ 0)
    (h8 : orderTwentyFiveRawXEight r s ≠ 0)
    (h67 : orderTwentyFiveRawXSix r s -
      orderTwentyFiveRawXSeven r s ≠ 0)
    (h92 : orderTwentyFiveRawXNine r s -
      orderTwentyFiveRawXTwo r s ≠ 0)
    (h1211 : orderTwentyFiveRawXTwelve r s -
      orderTwentyFiveRawXEleven r s ≠ 0)
    (hden1 : OrderTwentyFiveRawOrbitData.rawUnitOneDenominator r s ≠ 0)
    (hden2 : OrderTwentyFiveRawOrbitData.rawUnitTwoDenominator r s ≠ 0)
    (hden8 : OrderTwentyFiveRawOrbitData.rawUnitEightDenominator r s ≠ 0)
    (hden9 : OrderTwentyFiveRawOrbitData.rawUnitNineDenominator r s ≠ 0)
    (hCurve : orderTwentyFiveRawSutherlandPolynomial r s = 0) :
    orderTwentyFiveRawYRelationZero r s = 0 := by
  simp only [orderTwentyFiveRawYRelationZero]
  rw [orderTwentyFiveRawYSeven_eq_orbitData r s hs1 hrs hD hG h74 h3 hden1,
    orderTwentyFiveRawYTwo_eq_orbitData r s hs1 hrs hC hE h26 h118 hden2,
    orderTwentyFiveRawYEight_eq_orbitData r s hs1 hrs hC h8 h67 hden8,
    orderTwentyFiveRawYNine_eq_orbitData r s hs1 hC hD hE hG h92 h1211 hden9]
  refine OrderTwentyFiveRawOrbitData.RelationZeroCertificate.relation_eq_zero
    r s ?_ hden1 hden9 hden8 hden2
  rw [← orderTwentyFiveRawSutherlandPolynomial_eq_orbitData]
  exact hCurve

/- The numerator left by the exceptional diagonal `u = 1` on the raw
Sutherland chart.  The generated Bézout identity is checked below by `ring`. -/
private def orderTwentyFiveRawDiagonalNumeratorCoefficient0 (s : ℚ) : ℚ :=
  -s ^ 4 + s ^ 3 - s ^ 2

private def orderTwentyFiveRawDiagonalNumeratorCoefficient1 (s : ℚ) : ℚ :=
  -s ^ 8 + s ^ 7 + 2 * s ^ 6 - 10 * s ^ 5 + 21 * s ^ 4 -
    19 * s ^ 3 + 12 * s ^ 2

private def orderTwentyFiveRawDiagonalNumeratorCoefficient2 (s : ℚ) : ℚ :=
  s ^ 9 - 8 * s ^ 8 + 33 * s ^ 7 - 72 * s ^ 6 + 119 * s ^ 5 -
    144 * s ^ 4 + 108 * s ^ 3 - 50 * s ^ 2 - 2 * s

private def orderTwentyFiveRawDiagonalNumeratorCoefficient3 (s : ℚ) : ℚ :=
  -s ^ 9 + 7 * s ^ 8 - 26 * s ^ 7 + 69 * s ^ 6 - 154 * s ^ 5 +
    204 * s ^ 4 - 146 * s ^ 3 + 45 * s ^ 2 + 23 * s - 1

private def orderTwentyFiveRawDiagonalNumeratorCoefficient4 (s : ℚ) : ℚ :=
  -s ^ 8 + 12 * s ^ 7 - 53 * s ^ 6 + 114 * s ^ 5 - 106 * s ^ 4 +
    23 * s ^ 3 + 48 * s ^ 2 - 54 * s + 2

private def orderTwentyFiveRawDiagonalNumeratorCoefficient5 (s : ℚ) : ℚ :=
  s ^ 7 - 10 * s ^ 6 + 42 * s ^ 5 - 94 * s ^ 4 + 117 * s ^ 3 -
    94 * s ^ 2 + 44 * s

private def orderTwentyFiveRawDiagonalNumeratorCoefficient6 (s : ℚ) : ℚ :=
  -s ^ 3 + 4 * s ^ 2 - 2 * s - 2

private def orderTwentyFiveRawDiagonalNumerator (r s : ℚ) : ℚ :=
  orderTwentyFiveRawDiagonalNumeratorCoefficient6 s * r ^ 6 +
    orderTwentyFiveRawDiagonalNumeratorCoefficient5 s * r ^ 5 +
    orderTwentyFiveRawDiagonalNumeratorCoefficient4 s * r ^ 4 +
    orderTwentyFiveRawDiagonalNumeratorCoefficient3 s * r ^ 3 +
    orderTwentyFiveRawDiagonalNumeratorCoefficient2 s * r ^ 2 +
    orderTwentyFiveRawDiagonalNumeratorCoefficient1 s * r +
    orderTwentyFiveRawDiagonalNumeratorCoefficient0 s

private def orderTwentyFiveRawDiagonalEliminant (s : ℚ) : ℚ :=
  5 * s ^ 8 + 5 * s ^ 7 - 40 * s ^ 6 + 55 * s ^ 5 - 19 * s ^ 4 -
    15 * s ^ 3 + 11 * s ^ 2 - 1

private def orderTwentyFiveRawDiagonalA0 (s : ℚ) : ℚ :=
  5 * s ^ 55 - 260 * s ^ 54 + 6585 * s ^ 53 - 108075 * s ^ 52 + 1289556 * s ^ 51
  - 11889018 * s ^ 50 + 87777019 * s ^ 49 - 529878616 * s ^ 48 + 2639016427 * s ^ 47
  - 10794094099 * s ^ 46 + 35208459397 * s ^ 45 - 82510233229 * s ^ 44 + 70463536193 * s ^ 43
  + 544705767623 * s ^ 42 - 3953027733014 * s ^ 41 + 16948963172816 * s ^ 40
  - 56777667331325 * s ^ 39 + 159862561783535 * s ^ 38 - 389806513287637 * s ^ 37
  + 835148565611300 * s ^ 36 - 1583050861505539 * s ^ 35 + 2660440673020414 * s ^ 34
  - 3955860379246326 * s ^ 33 + 5167633023676815 * s ^ 32 - 5841756929104010 * s ^ 31
  + 5533951216410430 * s ^ 30 - 4048653995136280 * s ^ 29 + 1621177893653521 * s ^ 28
  + 1101480074137532 * s ^ 27 - 3318494217903915 * s ^ 26 + 4442819914088731 * s ^ 25
  - 4356490159165396 * s ^ 24 + 3400978449026804 * s ^ 23 - 2134095775679969 * s ^ 22
  + 1033272949445251 * s ^ 21 - 324854691329686 * s ^ 20 - 5424853699141 * s ^ 19
  + 93192548166380 * s ^ 18 - 76814694101462 * s ^ 17 + 40600022833972 * s ^ 16
  - 15687640856801 * s ^ 15 + 4346664937539 * s ^ 14 - 691348955407 * s ^ 13
  - 57551094261 * s ^ 12 + 82489938008 * s ^ 11 - 31533240305 * s ^ 10 + 7771125559 * s ^ 9
  - 1351853575 * s ^ 8 + 161588143 * s ^ 7 - 11096299 * s ^ 6 - 29978 * s ^ 5 + 92916 * s ^ 4
  - 9229 * s ^ 3 + 387 * s ^ 2 - 5 * s

private def orderTwentyFiveRawDiagonalA1 (s : ℚ) : ℚ :=
  -5 * s ^ 56 + 295 * s ^ 55 - 8545 * s ^ 54 + 161800 * s ^ 53 - 2249816 * s ^ 52
  + 24466960 * s ^ 51 - 216412653 * s ^ 50 + 1598391367 * s ^ 49 - 10041808808 * s ^ 48
  + 54376860453 * s ^ 47 - 256177198094 * s ^ 46 + 1056410040713 * s ^ 45
  - 3824448602956 * s ^ 44 + 12145938836979 * s ^ 43 - 33633623288661 * s ^ 42
  + 79926451927128 * s ^ 41 - 156761741762428 * s ^ 40 + 225713531539000 * s ^ 39
  - 108689334520452 * s ^ 38 - 689784296346775 * s ^ 37 + 3225381297255442 * s ^ 36
  - 9310063267685645 * s ^ 35 + 21432419655331414 * s ^ 34 - 42133987195480350 * s ^ 33
  + 72746195852065709 * s ^ 32 - 111821884104599645 * s ^ 31 + 154093638565495262 * s ^ 30
  - 190947044426538974 * s ^ 29 + 212848843654004234 * s ^ 28 - 213014315950220024 * s ^ 27
  + 190538518171189660 * s ^ 26 - 151145201015087306 * s ^ 25 + 104927950002194556 * s ^ 24
  - 62247578218896616 * s ^ 23 + 30020563917614264 * s ^ 22 - 10200744164274702 * s ^ 21
  + 725380461895700 * s ^ 20 + 2223253569331829 * s ^ 19 - 2157834009337425 * s ^ 18
  + 1294449487316775 * s ^ 17 - 580935437480168 * s ^ 16 + 199801571429621 * s ^ 15
  - 49644053379547 * s ^ 14 + 6443691588699 * s ^ 13 + 1225098413434 * s ^ 12
  - 1079319597774 * s ^ 11 + 387994336503 * s ^ 10 - 95646176124 * s ^ 9 + 17574332539 * s ^ 8
  - 2439084737 * s ^ 7 + 251752980 * s ^ 6 - 18649006 * s ^ 5 + 945538 * s ^ 4 - 32472 * s ^ 3
  + 858 * s ^ 2 - 8 * s - 1

private def orderTwentyFiveRawDiagonalA2 (s : ℚ) : ℚ :=
  5 * s ^ 56 - 290 * s ^ 55 + 8255 * s ^ 54 - 153660 * s ^ 53 + 2102531 * s ^ 52
  - 22537259 * s ^ 51 + 196927100 * s ^ 50 - 1440892929 * s ^ 49 + 8997890974 * s ^ 48
  - 48617157237 * s ^ 47 + 229521762491 * s ^ 46 - 952947846508 * s ^ 45
  + 3491355592773 * s ^ 44 - 11285460601786 * s ^ 43 + 32018006839135 * s ^ 42
  - 78626999549976 * s ^ 41 + 161633110049790 * s ^ 40 - 253167245021444 * s ^ 39
  + 186825508696373 * s ^ 38 + 549217277148447 * s ^ 37 - 3134942094882461 * s ^ 36
  + 9758204810127719 * s ^ 35 - 23696339340241151 * s ^ 34 + 48725859707059042 * s ^ 33
  - 87554349403540396 * s ^ 32 + 139497204056179869 * s ^ 31 - 198450140032547951 * s ^ 30
  + 252766609391421403 * s ^ 29 - 288191019911387501 * s ^ 28 + 293312577845490384 * s ^ 27
  - 264987329073606702 * s ^ 26 + 210464580172248499 * s ^ 25 - 144554093543642989 * s ^ 24
  + 83247619434120552 * s ^ 23 - 37471025666218069 * s ^ 22 + 10295313089376957 * s ^ 21
  + 1645628157731378 * s ^ 20 - 4418840845688165 * s ^ 19 + 3403918669728858 * s ^ 18
  - 1770298983863620 * s ^ 17 + 675422453577328 * s ^ 16 - 178608965061538 * s ^ 15
  + 21288023814454 * s ^ 14 + 7363527147660 * s ^ 13 - 5415961085865 * s ^ 12
  + 1803075073207 * s ^ 11 - 368201969870 * s ^ 10 + 35915570826 * s ^ 9 + 4593722272 * s ^ 8
  - 2634705880 * s ^ 7 + 559668176 * s ^ 6 - 72412333 * s ^ 5 + 5765412 * s ^ 4 - 224189 * s ^ 3
  - 2658 * s ^ 2 + 581 * s - 14

private def orderTwentyFiveRawDiagonalA3 (s : ℚ) : ℚ :=
  5 * s ^ 55 - 315 * s ^ 54 + 9665 * s ^ 53 - 192470 * s ^ 52 + 2796471 * s ^ 51
  - 31587584 * s ^ 50 + 288550437 * s ^ 49 - 2188848445 * s ^ 48 + 14044641877 * s ^ 47
  - 77221840306 * s ^ 46 + 367045876835 * s ^ 45 - 1515917512849 * s ^ 44
  + 5447035833825 * s ^ 43 - 16964626392931 * s ^ 42 + 45244053823795 * s ^ 41
  - 100259441031170 * s ^ 40 + 169766700768616 * s ^ 39 - 148883604603611 * s ^ 38
  - 311303238183141 * s ^ 37 + 2039457736937835 * s ^ 36 - 6571670332804027 * s ^ 35
  + 16131364544967237 * s ^ 34 - 33033856244304653 * s ^ 33 + 58351865616875473 * s ^ 32
  - 90204608037878508 * s ^ 31 + 122705865615229159 * s ^ 30 - 146828513876502888 * s ^ 29
  + 153642166681510584 * s ^ 28 - 138712745644912900 * s ^ 27 + 105081304602708086 * s ^ 26
  - 62561939764380400 * s ^ 25 + 23336875556976120 * s ^ 24 + 3578020946004172 * s ^ 23
  - 15632458305942609 * s ^ 22 + 16170004033539614 * s ^ 21 - 11101648463991013 * s ^ 20
  + 5440294959403912 * s ^ 19 - 1646533604387155 * s ^ 18 - 50022913000082 * s ^ 17
  + 438299218729176 * s ^ 16 - 325069639741963 * s ^ 15 + 152126765926588 * s ^ 14
  - 50223363009854 * s ^ 13 + 10842399246282 * s ^ 12 - 682021852802 * s ^ 11
  - 577687154293 * s ^ 10 + 299510754818 * s ^ 9 - 86314967099 * s ^ 8 + 17441946042 * s ^ 7
  - 2571159099 * s ^ 6 + 271467047 * s ^ 5 - 19045915 * s ^ 4 + 701977 * s ^ 3 + 3732 * s ^ 2
  - 1340 * s + 32

private def orderTwentyFiveRawDiagonalA4 (s : ℚ) : ℚ :=
  -5 * s ^ 54 + 305 * s ^ 53 - 9100 * s ^ 52 + 176885 * s ^ 51 - 2517076 * s ^ 50
  + 27932217 * s ^ 49 - 251403697 * s ^ 48 + 1884223682 * s ^ 47 - 11977991351 * s ^ 46
  + 65431181032 * s ^ 45 - 309905872806 * s ^ 44 + 1279682687396 * s ^ 43
  - 4615843497333 * s ^ 42 + 14507878043648 * s ^ 41 - 39359792601896 * s ^ 40
  + 90025835264273 * s ^ 39 - 163228234433331 * s ^ 38 + 186358671607460 * s ^ 37
  + 109302007425070 * s ^ 36 - 1404471111571186 * s ^ 35 + 5046200089079066 * s ^ 34
  - 13165324130330912 * s ^ 33 + 28367477866984353 * s ^ 32 - 52752287159609996 * s ^ 31
  + 86353926155909040 * s ^ 30 - 125666740152691718 * s ^ 29 + 163343131623210366 * s ^ 28
  - 189909390175044293 * s ^ 27 + 197264783142838858 * s ^ 26 - 182373406952226098 * s ^ 25
  + 148997431470926150 * s ^ 24 - 106246178572062140 * s ^ 23 + 64655810463537615 * s ^ 22
  - 32047491466964804 * s ^ 21 + 11362040573761582 * s ^ 20 - 1165160869508341 * s ^ 19
  - 2167409392778824 * s ^ 18 + 2222365930304598 * s ^ 17 - 1355986947557923 * s ^ 16
  + 612254379764459 * s ^ 15 - 210255701607807 * s ^ 14 + 51602981967894 * s ^ 13
  - 6316305937309 * s ^ 12 - 1469892927871 * s ^ 11 + 1175692880899 * s ^ 10
  - 409729123105 * s ^ 9 + 98035004963 * s ^ 8 - 17322873935 * s ^ 7 + 2264646559 * s ^ 6
  - 210323601 * s ^ 5 + 12429262 * s ^ 4 - 312169 * s ^ 3 - 9690 * s ^ 2 + 692 * s - 2

private def orderTwentyFiveRawDiagonalA5 (s : ℚ) : ℚ :=
  5 * s ^ 50 - 275 * s ^ 49 + 7370 * s ^ 48 - 128165 * s ^ 47 + 1624581 * s ^ 46
  - 15981926 * s ^ 45 + 126825415 * s ^ 44 - 832762911 * s ^ 43 + 4602783678 * s ^ 42
  - 21655082538 * s ^ 41 + 87258305065 * s ^ 40 - 301395987220 * s ^ 39 + 886746844929 * s ^ 38
  - 2179427458059 * s ^ 37 + 4247007158689 * s ^ 36 - 5467291269192 * s ^ 35
  - 816998773307 * s ^ 34 + 31779481107811 * s ^ 33 - 120513677916727 * s ^ 32
  + 315320771822790 * s ^ 31 - 664784261419200 * s ^ 30 + 1185565517901084 * s ^ 29
  - 1824287321872791 * s ^ 28 + 2441013197518964 * s ^ 27 - 2842383249810436 * s ^ 26
  + 2865211137107768 * s ^ 25 - 2468592981430169 * s ^ 24 + 1770954193881441 * s ^ 23
  - 997187345205998 * s ^ 22 + 365437956279265 * s ^ 21 + 11164305257725 * s ^ 20
  - 147813050200539 * s ^ 19 + 137581971315284 * s ^ 18 - 78456811726880 * s ^ 17
  + 28648723952337 * s ^ 16 - 3760817439765 * s ^ 15 - 3206333637207 * s ^ 14
  + 2841862134904 * s ^ 13 - 1285080596534 * s ^ 12 + 371827570075 * s ^ 11
  - 57413476534 * s ^ 10 - 5383429075 * s ^ 9 + 6446993444 * s ^ 8 - 2203971557 * s ^ 7
  + 478316676 * s ^ 6 - 72113939 * s ^ 5 + 7443347 * s ^ 4 - 474186 * s ^ 3 + 12032 * s ^ 2
  + 482 * s - 32

private def orderTwentyFiveRawDiagonalA (r s : ℚ) : ℚ :=
  orderTwentyFiveRawDiagonalA5 s * r ^ 5
    + orderTwentyFiveRawDiagonalA4 s * r ^ 4
    + orderTwentyFiveRawDiagonalA3 s * r ^ 3
    + orderTwentyFiveRawDiagonalA2 s * r ^ 2
    + orderTwentyFiveRawDiagonalA1 s * r
    + orderTwentyFiveRawDiagonalA0 s

private def orderTwentyFiveRawDiagonalB0 (s : ℚ) : ℚ :=
  -10 * s ^ 58 + 605 * s ^ 57 - 17925 * s ^ 56 + 346320 * s ^ 55 - 4902987 * s ^ 54
  + 54197973 * s ^ 53 - 486797546 * s ^ 52 + 3650738476 * s ^ 51 - 23314534268 * s ^ 50
  + 128679826084 * s ^ 49 - 620864432330 * s ^ 48 + 2642407263822 * s ^ 47
  - 9991888228152 * s ^ 46 + 33764625222456 * s ^ 45 - 102443384435327 * s ^ 44
  + 280133333684465 * s ^ 43 - 692521554518203 * s ^ 42 + 1551481413852568 * s ^ 41
  - 3155945425750555 * s ^ 40 + 5837211995267796 * s ^ 39 - 9827005162967994 * s ^ 38
  + 15068365388666805 * s ^ 37 - 21051729426390816 * s ^ 36 + 26797934425656259 * s ^ 35
  - 31073623126572169 * s ^ 34 + 32802226817509279 * s ^ 33 - 31492168334425730 * s ^ 32
  + 27453560172506246 * s ^ 31 - 21675840936782092 * s ^ 30 + 15433315796359723 * s ^ 29
  - 9833937099795210 * s ^ 28 + 5527029319552767 * s ^ 27 - 2658003345743010 * s ^ 26
  + 1012251983037219 * s ^ 25 - 221776246871601 * s ^ 24 - 69711291182377 * s ^ 23
  + 123798024796996 * s ^ 22 - 94665911753933 * s ^ 21 + 54104371870705 * s ^ 20
  - 25369939938099 * s ^ 19 + 9988942603200 * s ^ 18 - 3279542104548 * s ^ 17
  + 861203150972 * s ^ 16 - 156578307431 * s ^ 15 + 4527098102 * s ^ 14 + 10926750861 * s ^ 13
  - 5679464570 * s ^ 12 + 1882432266 * s ^ 11 - 481261893 * s ^ 10 + 99547137 * s ^ 9
  - 16843223 * s ^ 8 + 2316814 * s ^ 7 - 254115 * s ^ 6 + 21462 * s ^ 5 - 1314 * s ^ 4
  + 52 * s ^ 3 - s ^ 2

private def orderTwentyFiveRawDiagonalB1 (s : ℚ) : ℚ :=
  5 * s ^ 62 - 285 * s ^ 61 + 7975 * s ^ 60 - 145980 * s ^ 59 + 1965061 * s ^ 58
  - 20732503 * s ^ 57 + 178415432 * s ^ 56 - 1286626505 * s ^ 55 + 7925927279 * s ^ 54
  - 42294107173 * s ^ 53 + 197471137678 * s ^ 52 - 812220382292 * s ^ 51
  + 2953795532466 * s ^ 50 - 9497837024926 * s ^ 49 + 26861021882615 * s ^ 48
  - 65839383937730 * s ^ 47 + 134863004783991 * s ^ 46 - 207379668716365 * s ^ 45
  + 126292010497548 * s ^ 44 + 609247266741466 * s ^ 43 - 3219933851363996 * s ^ 42
  + 10151668088318754 * s ^ 41 - 25497896050216853 * s ^ 40 + 54892439012485857 * s ^ 39
  - 104312909808384944 * s ^ 38 + 177510769039853555 * s ^ 37 - 272595135629888741 * s ^ 36
  + 379362376124375789 * s ^ 35 - 479493867088832377 * s ^ 34 + 550903411507788857 * s ^ 33
  - 575274604509644590 * s ^ 32 + 545448560972616158 * s ^ 31 - 468682371728421784 * s ^ 30
  + 363800041773680642 * s ^ 29 - 253747262933709537 * s ^ 28 + 157561279769008543 * s ^ 27
  - 85554773566291464 * s ^ 26 + 39056941318482692 * s ^ 25 - 13405419867270423 * s ^ 24
  + 1766434497845817 * s ^ 23 + 2054763499909166 * s ^ 22 - 2380195700662567 * s ^ 21
  + 1632146120629415 * s ^ 20 - 866405573459254 * s ^ 19 + 375577174079134 * s ^ 18
  - 132852840652107 * s ^ 17 + 36683301251575 * s ^ 16 - 6727305217373 * s ^ 15
  + 68168538618 * s ^ 14 + 542028399585 * s ^ 13 - 259233899976 * s ^ 12 + 78186796185 * s ^ 11
  - 17521628406 * s ^ 10 + 3024764041 * s ^ 9 - 402022783 * s ^ 8 + 40333454 * s ^ 7
  - 2956826 * s ^ 6 + 154287 * s ^ 5 - 6116 * s ^ 4 + 234 * s ^ 3 - 7 * s ^ 2

private def orderTwentyFiveRawDiagonalB2 (s : ℚ) : ℚ :=
  5 * s ^ 62 - 300 * s ^ 61 + 8760 * s ^ 60 - 165915 * s ^ 59 + 2291576 * s ^ 58
  - 24597221 * s ^ 57 + 213484936 * s ^ 56 - 1538838165 * s ^ 55 + 9387889194 * s ^ 54
  - 49139023620 * s ^ 53 + 222874773720 * s ^ 52 - 881979057226 * s ^ 51
  + 3057884443817 * s ^ 50 - 9299115266139 * s ^ 49 + 24725103695280 * s ^ 48
  - 56835298155496 * s ^ 47 + 109513265340991 * s ^ 46 - 160561939050229 * s ^ 45
  + 101016826049637 * s ^ 44 + 405217874302199 * s ^ 43 - 2213105434830863 * s ^ 42
  + 7234873578414603 * s ^ 41 - 19268735566182127 * s ^ 40 + 44908535382759716 * s ^ 39
  - 93794633375765910 * s ^ 38 + 176888449997689215 * s ^ 37 - 301548744313894934 * s ^ 36
  + 463819725724525430 * s ^ 35 - 641426711997254477 * s ^ 34 + 793480677008152123 * s ^ 33
  - 871566026946495620 * s ^ 32 + 840325380891662047 * s ^ 31 - 697316619719335904 * s ^ 30
  + 478944847227946349 * s ^ 29 - 246284217667581707 * s ^ 28 + 57870772290976774 * s ^ 27
  + 54305622153391745 * s ^ 26 - 92149541249955549 * s ^ 25 + 80916034161095386 * s ^ 24
  - 50860370529840550 * s ^ 23 + 23245190764699206 * s ^ 22 - 6365813139287007 * s ^ 21
  - 675282346674228 * s ^ 20 + 2091810946600462 * s ^ 19 - 1488492397989458 * s ^ 18
  + 699881879901766 * s ^ 17 - 238825206391851 * s ^ 16 + 55746094604873 * s ^ 15
  - 5364993073497 * s ^ 14 - 2252692864504 * s ^ 13 + 1420518898563 * s ^ 12
  - 449217224655 * s ^ 11 + 97214445016 * s ^ 10 - 14843367328 * s ^ 9 + 1463777761 * s ^ 8
  - 51792379 * s ^ 7 - 9587498 * s ^ 6 + 1878216 * s ^ 5 - 162578 * s ^ 4 + 7807 * s ^ 3
  - 205 * s ^ 2 + 3 * s

private def orderTwentyFiveRawDiagonalB3 (s : ℚ) : ℚ :=
  5 * s ^ 62 - 315 * s ^ 61 + 9640 * s ^ 60 - 190870 * s ^ 59 + 2746831 * s ^ 58
  - 30591039 * s ^ 57 + 273982474 * s ^ 56 - 2023497583 * s ^ 55 + 12528215584 * s ^ 54
  - 65682647651 * s ^ 53 + 292845570630 * s ^ 52 - 1107661659052 * s ^ 51
  + 3509854957746 * s ^ 50 - 9009608379486 * s ^ 49 + 17018311483395 * s ^ 48
  - 14532117288855 * s ^ 47 - 47669954027296 * s ^ 46 + 282075622945170 * s ^ 45
  - 825755883948984 * s ^ 44 + 1553548031407678 * s ^ 43 - 1270643215626437 * s ^ 42
  - 3699005074856059 * s ^ 41 + 20779644103822479 * s ^ 40 - 60016040699879351 * s ^ 39
  + 127181708408072808 * s ^ 38 - 209325523394533947 * s ^ 37 + 257158866912641985 * s ^ 36
  - 177661677457694488 * s ^ 35 - 145671143686877326 * s ^ 34 + 797942253410706176 * s ^ 33
  - 1762041672811021732 * s ^ 32 + 2875787965145055990 * s ^ 31 - 3860210831569271333 * s ^ 30
  + 4424094844894968481 * s ^ 29 - 4395380380898657914 * s ^ 28 + 3802236285780066587 * s ^ 27
  - 2853588721804008219 * s ^ 26 + 1833732301788842325 * s ^ 25 - 978221511016199332 * s ^ 24
  + 399813512061239783 * s ^ 23 - 89530967124811588 * s ^ 22 - 31307279423728632 * s ^ 21
  + 52028968267466050 * s ^ 20 - 37085579871504472 * s ^ 19 + 18942009997431442 * s ^ 18
  - 7485941243009433 * s ^ 17 + 2267302711466226 * s ^ 16 - 472558393003561 * s ^ 15
  + 30703287777484 * s ^ 14 + 25183170471769 * s ^ 13 - 13923310017338 * s ^ 12
  + 4385579949752 * s ^ 11 - 1003285217170 * s ^ 10 + 175763880481 * s ^ 9 - 23803249730 * s ^ 8
  + 2474503127 * s ^ 7 - 195603230 * s ^ 6 + 11883471 * s ^ 5 - 586018 * s ^ 4 + 23181 * s ^ 3
  - 369 * s ^ 2 - 25 * s + 1

private def orderTwentyFiveRawDiagonalB4 (s : ℚ) : ℚ :=
  5 * s ^ 62 - 330 * s ^ 61 + 10615 * s ^ 60 - 221580 * s ^ 59 + 3371281 * s ^ 58
  - 39800162 * s ^ 57 + 378836236 * s ^ 56 - 2980785831 * s ^ 55 + 19705793498 * s ^ 54
  - 110516041137 * s ^ 53 + 527527482210 * s ^ 52 - 2132798935929 * s ^ 51
  + 7165488193654 * s ^ 50 - 18943377821287 * s ^ 49 + 32284184682559 * s ^ 48
  + 13889621548454 * s ^ 47 - 391987866089396 * s ^ 46 + 1964397062093938 * s ^ 45
  - 6844240257062375 * s ^ 44 + 18981754785885813 * s ^ 43 - 43194214122668400 * s ^ 42
  + 79296223972794516 * s ^ 41 - 106530519770164109 * s ^ 40 + 55377267033630507 * s ^ 39
  + 227381742236817355 * s ^ 38 - 998655513993626988 * s ^ 37 + 2588333795280021346 * s ^ 36
  - 5287506225033410982 * s ^ 35 + 9164877812215843108 * s ^ 34 - 13885693237953620618 * s ^ 33
  + 18655134763696345646 * s ^ 32 - 22383612727385484852 * s ^ 31
  + 24058297989971285623 * s ^ 30 - 23162135535740441201 * s ^ 29
  + 19915103877066562067 * s ^ 28 - 15191900854179268398 * s ^ 27
  + 10155839191490134371 * s ^ 26 - 5811459497545748881 * s ^ 25 + 2703997696904873248 * s ^ 24
  - 876811030650054935 * s ^ 23 + 37108389996373398 * s ^ 22 + 211871829316118655 * s ^ 21
  - 198735080972297025 * s ^ 20 + 119292036948665706 * s ^ 19 - 54481874226279899 * s ^ 18
  + 19391896628815706 * s ^ 17 - 5124487905955281 * s ^ 16 + 788629034599670 * s ^ 15
  + 75416478928135 * s ^ 14 - 101919393958858 * s ^ 13 + 40329207314291 * s ^ 12
  - 10525519535844 * s ^ 11 + 1974681117980 * s ^ 10 - 257641139047 * s ^ 9
  + 18720632930 * s ^ 8 + 524333325 * s ^ 7 - 333132049 * s ^ 6 + 43168366 * s ^ 5
  - 2786641 * s ^ 4 + 53060 * s ^ 3 + 5300 * s ^ 2 - 422 * s + 11

private def orderTwentyFiveRawDiagonalB5 (s : ℚ) : ℚ :=
  5 * s ^ 62 - 345 * s ^ 61 + 11685 * s ^ 60 - 258780 * s ^ 59 + 4211646 * s ^ 58
  - 53674340 * s ^ 57 + 557325742 * s ^ 56 - 4843532146 * s ^ 55 + 35913100928 * s ^ 54
  - 230403497646 * s ^ 53 + 1292386369376 * s ^ 52 - 6386407507083 * s ^ 51
  + 27946695836848 * s ^ 50 - 108606901183717 * s ^ 49 + 374932630985354 * s ^ 48
  - 1146093223609621 * s ^ 47 + 3074691209315518 * s ^ 46 - 7095091469542481 * s ^ 45
  + 13413365368654813 * s ^ 44 - 17752786460895800 * s ^ 43 + 1831173961633512 * s ^ 42
  + 85205352669721328 * s ^ 41 - 354604297428501802 * s ^ 40 + 1006665395982791700 * s ^ 39
  - 2338639191068693035 * s ^ 38 + 4700434497662635966 * s ^ 37 - 8374349826666194295 * s ^ 36
  + 13391173710771469196 * s ^ 35 - 19351870165997694287 * s ^ 34
  + 25367031258837234685 * s ^ 33 - 30209444228835570513 * s ^ 32
  + 32679949567371909961 * s ^ 31 - 32054252831307731534 * s ^ 30
  + 28396450436935172560 * s ^ 29 - 22566052975475292683 * s ^ 28
  + 15900498880318039371 * s ^ 27 - 9729280089495137754 * s ^ 26 + 4955321963143303333 * s ^ 25
  - 1878394584154586651 * s ^ 24 + 286076039815481232 * s ^ 23 + 297102776349110573 * s ^ 22
  - 356690119154190423 * s ^ 21 + 237639777540605615 * s ^ 20 - 115008868518107617 * s ^ 19
  + 40999926263011997 * s ^ 18 - 9255562100147679 * s ^ 17 - 42375665224113 * s ^ 16
  + 1195588263949536 * s ^ 15 - 642584236718911 * s ^ 14 + 205718176598974 * s ^ 13
  - 40852058425745 * s ^ 12 + 2309485697575 * s ^ 11 + 1739966804151 * s ^ 10
  - 796978559480 * s ^ 9 + 202370988665 * s ^ 8 - 36023145468 * s ^ 7 + 4688271798 * s ^ 6
  - 439256108 * s ^ 5 + 27540002 * s ^ 4 - 894790 * s ^ 3 - 11153 * s ^ 2 + 2299 * s - 70

private def orderTwentyFiveRawDiagonalB6 (s : ℚ) : ℚ :=
  -105 * s ^ 57 + 6160 * s ^ 56 - 175950 * s ^ 55 + 3257930 * s ^ 54 - 43920231 * s ^ 53
  + 458895223 * s ^ 52 - 3861445005 * s ^ 51 + 26833368829 * s ^ 50 - 156579314901 * s ^ 49
  + 775341829692 * s ^ 48 - 3274734859424 * s ^ 47 + 11787688855710 * s ^ 46
  - 35822069345952 * s ^ 45 + 89520671254529 * s ^ 44 - 171075198147099 * s ^ 43
  + 184825998304426 * s ^ 42 + 241775407561543 * s ^ 41 - 2035547739534371 * s ^ 40
  + 6835586501755932 * s ^ 39 - 16502540680026256 * s ^ 38 + 31356096714656076 * s ^ 37
  - 47279932883821660 * s ^ 36 + 53770693859634259 * s ^ 35 - 36988238701792040 * s ^ 34
  - 9044549388038180 * s ^ 33 + 66215852332637716 * s ^ 32 - 83424469528049444 * s ^ 31
  - 9474870138060774 * s ^ 30 + 261316196487261456 * s ^ 29 - 653189275064280401 * s ^ 28
  + 1082351211278470276 * s ^ 27 - 1400104295547953310 * s ^ 26 + 1487966632182585403 * s ^ 25
  - 1322374230562837765 * s ^ 24 + 982685420934319118 * s ^ 23 - 599697764384124115 * s ^ 22
  + 284903140048565352 * s ^ 21 - 87554655757120697 * s ^ 20 - 2974273240479849 * s ^ 19
  + 26546568352785016 * s ^ 18 - 21735392004961066 * s ^ 17 + 11608729791368371 * s ^ 16
  - 4611090931329404 * s ^ 15 + 1358843119579290 * s ^ 14 - 260253677051194 * s ^ 13
  + 6297649829900 * s ^ 12 + 18341003464340 * s ^ 11 - 8657737070480 * s ^ 10
  + 2502401753314 * s ^ 9 - 531029507274 * s ^ 8 + 86195364226 * s ^ 7 - 10701548046 * s ^ 6
  + 988437779 * s ^ 5 - 63284455 * s ^ 4 + 2276802 * s ^ 3 + 5230 * s ^ 2 - 4516 * s + 150

private def orderTwentyFiveRawDiagonalB7 (s : ℚ) : ℚ :=
  -30 * s ^ 57 + 1900 * s ^ 56 - 58635 * s ^ 55 + 1174415 * s ^ 54 - 17153881 * s ^ 53
  + 194607541 * s ^ 52 - 1783006139 * s ^ 51 + 13539479745 * s ^ 50 - 86743246732 * s ^ 49
  + 474580020292 * s ^ 48 - 2234085555816 * s ^ 47 + 9078237602663 * s ^ 46
  - 31781840854076 * s ^ 45 + 94927946191765 * s ^ 44 - 235845524338365 * s ^ 43
  + 455335811268445 * s ^ 42 - 522035979280067 * s ^ 41 - 519699796137693 * s ^ 40
  + 5206020294660431 * s ^ 39 - 18500180532755871 * s ^ 38 + 47337108580300816 * s ^ 37
  - 96627681590439501 * s ^ 36 + 159896815639807645 * s ^ 35 - 206217598610312272 * s ^ 34
  + 171565238045613776 * s ^ 33 + 32175613477969951 * s ^ 32 - 481207878015722426 * s ^ 31
  + 1184621185910771923 * s ^ 30 - 2040393939491033345 * s ^ 29 + 2841285315741371989 * s ^ 28
  - 3346905617565492972 * s ^ 27 + 3392792020637172838 * s ^ 26 - 2972770959112114532 * s ^ 25
  + 2240665701224502571 * s ^ 24 - 1429920470800269897 * s ^ 23 + 744243176287279906 * s ^ 22
  - 285121295250826299 * s ^ 21 + 46980034392965866 * s ^ 20 + 37849599863633407 * s ^ 19
  - 45604002315975323 * s ^ 18 + 29327975728715779 * s ^ 17 - 13766643768715798 * s ^ 16
  + 4954469113350830 * s ^ 15 - 1321332413694187 * s ^ 14 + 213017280474830 * s ^ 13
  + 11488815004459 * s ^ 12 - 22503605667716 * s ^ 11 + 9261296949835 * s ^ 10
  - 2531032604701 * s ^ 9 + 521168778987 * s ^ 8 - 83364471153 * s ^ 7 + 10335763929 * s ^ 6
  - 967249953 * s ^ 5 + 64025638 * s ^ 4 - 2498264 * s ^ 3 + 9354 * s ^ 2 + 4237 * s - 155

private def orderTwentyFiveRawDiagonalB8 (s : ℚ) : ℚ :=
  -5 * s ^ 57 + 340 * s ^ 56 - 11290 * s ^ 55 + 243920 * s ^ 54 - 3854191 * s ^ 53
  + 47463409 * s ^ 52 - 473975362 * s ^ 51 + 3942446279 * s ^ 50 - 27837505187 * s ^ 49
  + 169167184056 * s ^ 48 - 893570580252 * s ^ 47 + 4130817783455 * s ^ 46
  - 16779704307397 * s ^ 45 + 59953075158102 * s ^ 44 - 187867659011919 * s ^ 43
  + 511571415305111 * s ^ 42 - 1184400652865087 * s ^ 41 + 2207112817401543 * s ^ 40
  - 2738580613653014 * s ^ 39 - 565770452864818 * s ^ 38 + 16556682779118777 * s ^ 37
  - 63510212904026077 * s ^ 36 + 171852618748148757 * s ^ 35 - 381654926185659809 * s ^ 34
  + 730605382646285072 * s ^ 33 - 1231888921629641741 * s ^ 32 + 1849340366299705079 * s ^ 31
  - 2485163587247803065 * s ^ 30 + 2995729188650341106 * s ^ 29 - 3238365509313520288 * s ^ 28
  + 3131281353369271761 * s ^ 27 - 2694425117409047849 * s ^ 26 + 2045175577601455589 * s ^ 25
  - 1348731605839424754 * s ^ 24 + 751064771794603670 * s ^ 23 - 331127966012466697 * s ^ 22
  + 92867748496265683 * s ^ 21 + 9183432522488213 * s ^ 20 - 33768184803651930 * s ^ 19
  + 27153688264007139 * s ^ 18 - 14939067892169994 * s ^ 17 + 6327223398095354 * s ^ 16
  - 2086570095239708 * s ^ 15 + 504469297409972 * s ^ 14 - 65574807421541 * s ^ 13
  - 11291877455308 * s ^ 12 + 10479030869059 * s ^ 11 - 3916557119362 * s ^ 10
  + 1028111025671 * s ^ 9 - 208292085063 * s ^ 8 + 33381728015 * s ^ 7 - 4221894404 * s ^ 6
  + 411275585 * s ^ 5 - 29085663 * s ^ 4 + 1276210 * s ^ 3 - 13372 * s ^ 2 - 1850 * s + 79

private def orderTwentyFiveRawDiagonalB9 (s : ℚ) : ℚ :=
  5 * s ^ 47 - 255 * s ^ 46 + 6340 * s ^ 45 - 102305 * s ^ 44 + 1203191 * s ^ 43
  - 10977232 * s ^ 42 + 80714715 * s ^ 41 - 490355969 * s ^ 40 + 2501884836 * s ^ 39
  - 10828260686 * s ^ 38 + 39922204587 * s ^ 37 - 125054417172 * s ^ 36 + 328341288439 * s ^ 35
  - 695797879133 * s ^ 34 + 1057241899623 * s ^ 33 - 503410489312 * s ^ 32
  - 3553528771535 * s ^ 31 + 16457703201049 * s ^ 30 - 46568986590837 * s ^ 29
  + 103236476600414 * s ^ 28 - 191615788237968 * s ^ 27 + 305767384930058 * s ^ 26
  - 424459158877451 * s ^ 25 + 514873368624980 * s ^ 24 - 545506227415730 * s ^ 23
  + 502357807949790 * s ^ 22 - 397896032049509 * s ^ 21 + 265666904615285 * s ^ 20
  - 143443278545420 * s ^ 19 + 56123096966033 * s ^ 18 - 8790559017873 * s ^ 17
  - 8334923113257 * s ^ 16 + 9577202965936 * s ^ 15 - 5897035600876 * s ^ 14
  + 2576021843475 * s ^ 13 - 817064795985 * s ^ 12 + 167434693655 * s ^ 11 - 6313185456 * s ^ 10
  - 11073133698 * s ^ 9 + 5292018885 * s ^ 8 - 1472762686 * s ^ 7 + 287749807 * s ^ 6
  - 40519726 * s ^ 5 + 3975297 * s ^ 4 - 242298 * s ^ 3 + 5727 * s ^ 2 + 257 * s - 16

private def orderTwentyFiveRawDiagonalB (r s : ℚ) : ℚ :=
  orderTwentyFiveRawDiagonalB9 s * r ^ 9
    + orderTwentyFiveRawDiagonalB8 s * r ^ 8
    + orderTwentyFiveRawDiagonalB7 s * r ^ 7
    + orderTwentyFiveRawDiagonalB6 s * r ^ 6
    + orderTwentyFiveRawDiagonalB5 s * r ^ 5
    + orderTwentyFiveRawDiagonalB4 s * r ^ 4
    + orderTwentyFiveRawDiagonalB3 s * r ^ 3
    + orderTwentyFiveRawDiagonalB2 s * r ^ 2
    + orderTwentyFiveRawDiagonalB1 s * r
    + orderTwentyFiveRawDiagonalB0 s

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_0 (s : ℚ) :
    s ^ 4 * (s - 1) ^ 53 * orderTwentyFiveRawDiagonalEliminant s =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient0 s
      + orderTwentyFiveRawDiagonalB0 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalEliminant,
      orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient0,
      orderTwentyFiveRawDiagonalB0,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_1 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient1 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient0 s
      + orderTwentyFiveRawDiagonalB0 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB1 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient1,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient0,
      orderTwentyFiveRawDiagonalB0,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB1,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_2 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient2 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient1 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient0 s
      + orderTwentyFiveRawDiagonalB0 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB1 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB2 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient2,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient1,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient0,
      orderTwentyFiveRawDiagonalB0,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB1,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB2,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_3 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient3 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient2 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient1 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient0 s
      + orderTwentyFiveRawDiagonalB0 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB1 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB2 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB3 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient3,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient2,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient1,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient0,
      orderTwentyFiveRawDiagonalB0,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB1,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB2,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB3,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_4 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient4 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient3 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient2 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient1 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient0 s
      + orderTwentyFiveRawDiagonalB0 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB1 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB2 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB3 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB4 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient4,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient3,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient2,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient1,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient0,
      orderTwentyFiveRawDiagonalB0,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB1,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB2,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB3,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB4,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_5 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient5 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient4 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient3 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient2 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient1 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient0 s
      + orderTwentyFiveRawDiagonalB0 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB1 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB2 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB3 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB4 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB5 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient5,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient4,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient3,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient2,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient1,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient0,
      orderTwentyFiveRawDiagonalB0,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB1,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB2,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB3,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB4,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB5,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_6 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient6 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient5 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient4 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient3 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient2 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient1 s
      + orderTwentyFiveRawDiagonalB0 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB1 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB2 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB3 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB4 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB5 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB6 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient6,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient5,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient4,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient3,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient2,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient1,
      orderTwentyFiveRawDiagonalB0,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB1,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB2,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB3,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB4,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB5,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB6,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_7 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient7 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient6 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient5 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient4 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient3 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient2 s
      + orderTwentyFiveRawDiagonalB1 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB2 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB3 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB4 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB5 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB6 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB7 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient7,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient6,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient5,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient4,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient3,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient2,
      orderTwentyFiveRawDiagonalB1,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB2,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB3,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB4,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB5,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB6,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB7,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_8 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient8 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient7 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient6 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient5 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient4 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient3 s
      + orderTwentyFiveRawDiagonalB2 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB3 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB4 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB5 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB6 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB7 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB8 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient8,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient7,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient6,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient5,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient4,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient3,
      orderTwentyFiveRawDiagonalB2,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB3,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB4,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB5,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB6,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB7,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB8,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_9 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient9 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient8 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient7 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient6 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient5 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient4 s
      + orderTwentyFiveRawDiagonalB3 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB4 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB5 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB6 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB7 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB8 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s
      + orderTwentyFiveRawDiagonalB9 s * orderTwentyFiveRawDiagonalNumeratorCoefficient0 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient9,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient8,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient7,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient6,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient5,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient4,
      orderTwentyFiveRawDiagonalB3,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB4,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB5,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB6,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB7,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB8,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1,
      orderTwentyFiveRawDiagonalB9,
      orderTwentyFiveRawDiagonalNumeratorCoefficient0]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_10 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA0 s * orderTwentyFiveRawSutherlandCoefficient10 s
      + orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient9 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient8 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient7 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient6 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient5 s
      + orderTwentyFiveRawDiagonalB4 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB5 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB6 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB7 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB8 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s
      + orderTwentyFiveRawDiagonalB9 s * orderTwentyFiveRawDiagonalNumeratorCoefficient1 s := by
  simp only [
    orderTwentyFiveRawDiagonalA0,
      orderTwentyFiveRawSutherlandCoefficient10,
      orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient9,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient8,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient7,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient6,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient5,
      orderTwentyFiveRawDiagonalB4,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB5,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB6,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB7,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB8,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2,
      orderTwentyFiveRawDiagonalB9,
      orderTwentyFiveRawDiagonalNumeratorCoefficient1]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_11 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA1 s * orderTwentyFiveRawSutherlandCoefficient10 s
      + orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient9 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient8 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient7 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient6 s
      + orderTwentyFiveRawDiagonalB5 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB6 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB7 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB8 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s
      + orderTwentyFiveRawDiagonalB9 s * orderTwentyFiveRawDiagonalNumeratorCoefficient2 s := by
  simp only [
    orderTwentyFiveRawDiagonalA1,
      orderTwentyFiveRawSutherlandCoefficient10,
      orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient9,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient8,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient7,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient6,
      orderTwentyFiveRawDiagonalB5,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB6,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB7,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB8,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3,
      orderTwentyFiveRawDiagonalB9,
      orderTwentyFiveRawDiagonalNumeratorCoefficient2]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_12 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA2 s * orderTwentyFiveRawSutherlandCoefficient10 s
      + orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient9 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient8 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient7 s
      + orderTwentyFiveRawDiagonalB6 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB7 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB8 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s
      + orderTwentyFiveRawDiagonalB9 s * orderTwentyFiveRawDiagonalNumeratorCoefficient3 s := by
  simp only [
    orderTwentyFiveRawDiagonalA2,
      orderTwentyFiveRawSutherlandCoefficient10,
      orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient9,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient8,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient7,
      orderTwentyFiveRawDiagonalB6,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB7,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB8,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4,
      orderTwentyFiveRawDiagonalB9,
      orderTwentyFiveRawDiagonalNumeratorCoefficient3]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_13 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA3 s * orderTwentyFiveRawSutherlandCoefficient10 s
      + orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient9 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient8 s
      + orderTwentyFiveRawDiagonalB7 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB8 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s
      + orderTwentyFiveRawDiagonalB9 s * orderTwentyFiveRawDiagonalNumeratorCoefficient4 s := by
  simp only [
    orderTwentyFiveRawDiagonalA3,
      orderTwentyFiveRawSutherlandCoefficient10,
      orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient9,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient8,
      orderTwentyFiveRawDiagonalB7,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB8,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5,
      orderTwentyFiveRawDiagonalB9,
      orderTwentyFiveRawDiagonalNumeratorCoefficient4]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_14 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA4 s * orderTwentyFiveRawSutherlandCoefficient10 s
      + orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient9 s
      + orderTwentyFiveRawDiagonalB8 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s
      + orderTwentyFiveRawDiagonalB9 s * orderTwentyFiveRawDiagonalNumeratorCoefficient5 s := by
  simp only [
    orderTwentyFiveRawDiagonalA4,
      orderTwentyFiveRawSutherlandCoefficient10,
      orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient9,
      orderTwentyFiveRawDiagonalB8,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6,
      orderTwentyFiveRawDiagonalB9,
      orderTwentyFiveRawDiagonalNumeratorCoefficient5]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate_coefficient_15 (s : ℚ) :
    0 =
      orderTwentyFiveRawDiagonalA5 s * orderTwentyFiveRawSutherlandCoefficient10 s
      + orderTwentyFiveRawDiagonalB9 s * orderTwentyFiveRawDiagonalNumeratorCoefficient6 s := by
  simp only [
    orderTwentyFiveRawDiagonalA5,
      orderTwentyFiveRawSutherlandCoefficient10,
      orderTwentyFiveRawDiagonalB9,
      orderTwentyFiveRawDiagonalNumeratorCoefficient6]
  ring

private theorem orderTwentyFiveRawDiagonal_certificate (r s : ℚ) :
    s ^ 4 * (s - 1) ^ 53 * orderTwentyFiveRawDiagonalEliminant s =
      orderTwentyFiveRawDiagonalA r s * orderTwentyFiveRawSutherlandPolynomial r s +
        orderTwentyFiveRawDiagonalB r s * orderTwentyFiveRawDiagonalNumerator r s := by
  have h0 := orderTwentyFiveRawDiagonal_certificate_coefficient_0 s
  have h1 := orderTwentyFiveRawDiagonal_certificate_coefficient_1 s
  have h2 := orderTwentyFiveRawDiagonal_certificate_coefficient_2 s
  have h3 := orderTwentyFiveRawDiagonal_certificate_coefficient_3 s
  have h4 := orderTwentyFiveRawDiagonal_certificate_coefficient_4 s
  have h5 := orderTwentyFiveRawDiagonal_certificate_coefficient_5 s
  have h6 := orderTwentyFiveRawDiagonal_certificate_coefficient_6 s
  have h7 := orderTwentyFiveRawDiagonal_certificate_coefficient_7 s
  have h8 := orderTwentyFiveRawDiagonal_certificate_coefficient_8 s
  have h9 := orderTwentyFiveRawDiagonal_certificate_coefficient_9 s
  have h10 := orderTwentyFiveRawDiagonal_certificate_coefficient_10 s
  have h11 := orderTwentyFiveRawDiagonal_certificate_coefficient_11 s
  have h12 := orderTwentyFiveRawDiagonal_certificate_coefficient_12 s
  have h13 := orderTwentyFiveRawDiagonal_certificate_coefficient_13 s
  have h14 := orderTwentyFiveRawDiagonal_certificate_coefficient_14 s
  have h15 := orderTwentyFiveRawDiagonal_certificate_coefficient_15 s
  simp only [orderTwentyFiveRawDiagonalNumerator,
    orderTwentyFiveRawDiagonalA,
    orderTwentyFiveRawDiagonalB,
    orderTwentyFiveRawSutherlandPolynomial,
    orderTwentyFiveRawSutherlandPolynomialChunk0,
    orderTwentyFiveRawSutherlandPolynomialChunk1,
    orderTwentyFiveRawSutherlandPolynomialChunk2,
    orderTwentyFiveRawSutherlandPolynomialChunk3,
    orderTwentyFiveRawSutherlandPolynomialChunk4,
    orderTwentyFiveRawSutherlandPolynomialChunk5]
  linear_combination
    h0 + r ^ 1 * h1 + r ^ 2 * h2 + r ^ 3 * h3 +
    r ^ 4 * h4 + r ^ 5 * h5 + r ^ 6 * h6 + r ^ 7 * h7 +
    r ^ 8 * h8 + r ^ 9 * h9 + r ^ 10 * h10 + r ^ 11 * h11 +
    r ^ 12 * h12 + r ^ 13 * h13 + r ^ 14 * h14 + r ^ 15 * h15

private noncomputable def orderTwentyFiveRawDiagonalIntegralPolynomial :
    Polynomial ℤ :=
  Polynomial.X ^ 8 + Polynomial.C 5 * Polynomial.X ^ 7 -
    Polynomial.C 200 * Polynomial.X ^ 6 +
    Polynomial.C 1375 * Polynomial.X ^ 5 -
    Polynomial.C 2375 * Polynomial.X ^ 4 -
    Polynomial.C 9375 * Polynomial.X ^ 3 +
    Polynomial.C 34375 * Polynomial.X ^ 2 - Polynomial.C 78125

private theorem orderTwentyFiveRawDiagonalIntegralPolynomial_monic :
    Polynomial.Monic orderTwentyFiveRawDiagonalIntegralPolynomial := by
  unfold orderTwentyFiveRawDiagonalIntegralPolynomial
  monicity!

private theorem orderTwentyFiveRawDiagonalIntegralPolynomial_no_root_mod_two :
    ∀ z : ZMod 2,
      z ^ 8 + 5 * z ^ 7 - 200 * z ^ 6 + 1375 * z ^ 5 -
        2375 * z ^ 4 - 9375 * z ^ 3 + 34375 * z ^ 2 - 78125 ≠ 0 := by
  decide

private theorem orderTwentyFiveRawDiagonalEliminant_ne_zero (s : ℚ) :
    orderTwentyFiveRawDiagonalEliminant s ≠ 0 := by
  intro hs
  have hscaled :
      (5 * s) ^ 8 + 5 * (5 * s) ^ 7 - 200 * (5 * s) ^ 6 +
          1375 * (5 * s) ^ 5 - 2375 * (5 * s) ^ 4 -
          9375 * (5 * s) ^ 3 + 34375 * (5 * s) ^ 2 - 78125 = 0 := by
    simp only [orderTwentyFiveRawDiagonalEliminant] at hs
    linear_combination 78125 * hs
  have hroot :
      Polynomial.aeval (5 * s) orderTwentyFiveRawDiagonalIntegralPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [orderTwentyFiveRawDiagonalIntegralPolynomial]
    exact hscaled
  obtain ⟨z, hsz, -⟩ :=
    exists_integer_of_is_root_of_monic
      orderTwentyFiveRawDiagonalIntegralPolynomial_monic hroot
  have hzrat :
      (z : ℚ) ^ 8 + 5 * (z : ℚ) ^ 7 - 200 * (z : ℚ) ^ 6 +
          1375 * (z : ℚ) ^ 5 - 2375 * (z : ℚ) ^ 4 -
          9375 * (z : ℚ) ^ 3 + 34375 * (z : ℚ) ^ 2 - 78125 = 0 := by
    have hzcast : (z : ℚ) = 5 * s := by
      simpa using hsz.symm
    rw [hzcast]
    exact hscaled
  have hzint :
      z ^ 8 + 5 * z ^ 7 - 200 * z ^ 6 + 1375 * z ^ 5 -
          2375 * z ^ 4 - 9375 * z ^ 3 + 34375 * z ^ 2 - 78125 = 0 := by
    exact_mod_cast hzrat
  apply orderTwentyFiveRawDiagonalIntegralPolynomial_no_root_mod_two (z : ZMod 2)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 2)) hzint

private def orderTwentyFiveRawDiagonalDenominator (r s : ℚ) : ℚ :=
  (s - 1) * (r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s) ^ 2 *
    (r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1)

private def orderTwentyFiveRawUCrossNumerator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwo r s) *
    (orderTwentyFiveRawXThree r s - orderTwentyFiveRawXEleven r s) *
    (orderTwentyFiveRawXSeven r s - orderTwentyFiveRawXNine r s) *
    (0 - orderTwentyFiveRawXTwelve r s)

private def orderTwentyFiveRawUCrossDenominator (r s : ℚ) : ℚ :=
  (orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwelve r s) *
    (orderTwentyFiveRawXThree r s - orderTwentyFiveRawXNine r s) *
    (orderTwentyFiveRawXSeven r s - orderTwentyFiveRawXFour r s) *
    (0 - orderTwentyFiveRawXThree r s)

private theorem orderTwentyFiveRawBrunaultU_sub_one
    (r s : ℚ)
    (hrs : r - s ≠ 0)
    (hrss : r - s ^ 2 + s - 1 ≠ 0)
    (hs1 : s - 1 ≠ 0)
    (hD : r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0)
    (hE : r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0)
    (h4twelve : orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwelve r s ≠ 0)
    (hthreeNine : orderTwentyFiveRawXThree r s - orderTwentyFiveRawXNine r s ≠ 0)
    (hsevenFour : orderTwentyFiveRawXSeven r s - orderTwentyFiveRawXFour r s ≠ 0)
    (hzeroThree : 0 - orderTwentyFiveRawXThree r s ≠ 0) :
    orderTwentyFiveRawBrunaultU r s - 1 =
      orderTwentyFiveRawDiagonalNumerator r s /
        orderTwentyFiveRawDiagonalDenominator r s := by
  have hcross : orderTwentyFiveRawUCrossDenominator r s ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero h4twelve hthreeNine) hsevenFour) hzeroThree
  have hdiag : orderTwentyFiveRawDiagonalDenominator r s ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hs1 (pow_ne_zero 2 hD)) hE
  have hcombine :
      orderTwentyFiveRawBrunaultU r s =
        orderTwentyFiveRawUCrossNumerator r s /
          orderTwentyFiveRawUCrossDenominator r s := by
    unfold orderTwentyFiveRawBrunaultU orderTwentyFiveRawYFour
      orderTwentyFiveRawYSeven orderTwentyFiveRawUCrossNumerator
      orderTwentyFiveRawUCrossDenominator
    field_simp [h4twelve, hthreeNine, hsevenFour, hzeroThree]
  rw [hcombine]
  field_simp [hcross, hdiag]
  unfold orderTwentyFiveRawUCrossNumerator
    orderTwentyFiveRawUCrossDenominator
  unfold orderTwentyFiveRawXTwo orderTwentyFiveRawXThree
    orderTwentyFiveRawXFour orderTwentyFiveRawXSeven
    orderTwentyFiveRawXNine orderTwentyFiveRawXEleven
    orderTwentyFiveRawXTwelve
  unfold orderTwentyFiveRawDiagonalNumerator
    orderTwentyFiveRawDiagonalNumeratorCoefficient0
    orderTwentyFiveRawDiagonalNumeratorCoefficient1
    orderTwentyFiveRawDiagonalNumeratorCoefficient2
    orderTwentyFiveRawDiagonalNumeratorCoefficient3
    orderTwentyFiveRawDiagonalNumeratorCoefficient4
    orderTwentyFiveRawDiagonalNumeratorCoefficient5
    orderTwentyFiveRawDiagonalNumeratorCoefficient6
    orderTwentyFiveRawDiagonalDenominator
  have hD' : r * (r - s ^ 3 + s ^ 2 * 3 - s * 4) + s ≠ 0 := by
    intro h
    apply hD
    linear_combination h
  have hE' : r * (r * (s - 3) + s + 3) - s ^ 2 - 1 ≠ 0 := by
    intro h
    apply hE
    linear_combination h
  field_simp [hrs, hrss, hs1, hD, hE, hD', hE']
  ring

private theorem orderTwentyFiveRawDiagonalNumerator_ne_zero
    (r s : ℚ)
    (hs : s ≠ 0) (hs1 : s - 1 ≠ 0)
    (hF : orderTwentyFiveRawSutherlandPolynomial r s = 0) :
    orderTwentyFiveRawDiagonalNumerator r s ≠ 0 := by
  intro hN
  have hcertificate := orderTwentyFiveRawDiagonal_certificate r s
  rw [hF, hN] at hcertificate
  simp only [mul_zero, add_zero] at hcertificate
  exact (mul_ne_zero
    (mul_ne_zero (pow_ne_zero 4 hs) (pow_ne_zero 53 hs1))
    (orderTwentyFiveRawDiagonalEliminant_ne_zero s)) hcertificate


private def orderTwentyFiveRawClearedChunk0 (b c : ℚ) : ℚ :=
  b ^ 10 * (b - c) ^ 15 - b ^ 9 * c ^ 21 * (b - c) ^ 5 +
    17 * b ^ 9 * c ^ 19 * (b - c) ^ 6 -
    123 * b ^ 9 * c ^ 17 * (b - c) ^ 7 +
    494 * b ^ 9 * c ^ 15 * (b - c) ^ 8 -
    1205 * b ^ 9 * c ^ 13 * (b - c) ^ 9 +
    1836 * b ^ 9 * c ^ 11 * (b - c) ^ 10 -
    1732 * b ^ 9 * c ^ 9 * (b - c) ^ 11 +
    968 * b ^ 9 * c ^ 7 * (b - c) ^ 12 -
    294 * b ^ 9 * c ^ 5 * (b - c) ^ 13 +
    35 * b ^ 9 * c ^ 3 * (b - c) ^ 14 -
    5 * b ^ 9 * c * (b - c) ^ 15 -
    6 * b ^ 8 * c ^ 22 * (b - c) ^ 5 +
    74 * b ^ 8 * c ^ 20 * (b - c) ^ 6 -
    345 * b ^ 8 * c ^ 18 * (b - c) ^ 7 +
    690 * b ^ 8 * c ^ 16 * (b - c) ^ 8 -
    185 * b ^ 8 * c ^ 14 * (b - c) ^ 9 -
    1659 * b ^ 8 * c ^ 12 * (b - c) ^ 10 +
    3051 * b ^ 8 * c ^ 10 * (b - c) ^ 11 -
    2320 * b ^ 8 * c ^ 8 * (b - c) ^ 12 +
    840 * b ^ 8 * c ^ 6 * (b - c) ^ 13 -
    105 * b ^ 8 * c ^ 4 * (b - c) ^ 14 +
    10 * b ^ 8 * c ^ 2 * (b - c) ^ 15

private def orderTwentyFiveRawClearedChunk1 (b c : ℚ) : ℚ :=
  -21 * b ^ 7 * c ^ 23 * (b - c) ^ 5 +
    161 * b ^ 7 * c ^ 21 * (b - c) ^ 6 -
    351 * b ^ 7 * c ^ 19 * (b - c) ^ 7 -
    144 * b ^ 7 * c ^ 17 * (b - c) ^ 8 +
    1289 * b ^ 7 * c ^ 15 * (b - c) ^ 9 -
    789 * b ^ 7 * c ^ 13 * (b - c) ^ 10 -
    1551 * b ^ 7 * c ^ 11 * (b - c) ^ 11 +
    2166 * b ^ 7 * c ^ 9 * (b - c) ^ 12 -
    996 * b ^ 7 * c ^ 7 * (b - c) ^ 13 +
    126 * b ^ 7 * c ^ 5 * (b - c) ^ 14 -
    10 * b ^ 7 * c ^ 3 * (b - c) ^ 15 +
    b ^ 6 * c ^ 34 - 18 * b ^ 6 * c ^ 32 * (b - c) +
    151 * b ^ 6 * c ^ 30 * (b - c) ^ 2 -
    770 * b ^ 6 * c ^ 28 * (b - c) ^ 3 +
    2655 * b ^ 6 * c ^ 26 * (b - c) ^ 4 -
    6558 * b ^ 6 * c ^ 24 * (b - c) ^ 5 +
    11834 * b ^ 6 * c ^ 22 * (b - c) ^ 6 -
    15408 * b ^ 6 * c ^ 20 * (b - c) ^ 7 +
    14630 * b ^ 6 * c ^ 18 * (b - c) ^ 8 -
    11195 * b ^ 6 * c ^ 16 * (b - c) ^ 9 +
    7227 * b ^ 6 * c ^ 14 * (b - c) ^ 10 -
    2441 * b ^ 6 * c ^ 12 * (b - c) ^ 11 -
    388 * b ^ 6 * c ^ 10 * (b - c) ^ 12 +
    555 * b ^ 6 * c ^ 8 * (b - c) ^ 13 -
    70 * b ^ 6 * c ^ 6 * (b - c) ^ 14 +
    5 * b ^ 6 * c ^ 4 * (b - c) ^ 15

private def orderTwentyFiveRawClearedChunk2 (b c : ℚ) : ℚ :=
  b ^ 5 * c ^ 35 - 15 * b ^ 5 * c ^ 33 * (b - c) +
    90 * b ^ 5 * c ^ 31 * (b - c) ^ 2 -
    245 * b ^ 5 * c ^ 29 * (b - c) ^ 3 +
    90 * b ^ 5 * c ^ 27 * (b - c) ^ 4 +
    1587 * b ^ 5 * c ^ 25 * (b - c) ^ 5 -
    6145 * b ^ 5 * c ^ 23 * (b - c) ^ 6 +
    12270 * b ^ 5 * c ^ 21 * (b - c) ^ 7 -
    15060 * b ^ 5 * c ^ 19 * (b - c) ^ 8 +
    12520 * b ^ 5 * c ^ 17 * (b - c) ^ 9 -
    8214 * b ^ 5 * c ^ 15 * (b - c) ^ 10 +
    3660 * b ^ 5 * c ^ 13 * (b - c) ^ 11 -
    685 * b ^ 5 * c ^ 11 * (b - c) ^ 12 -
    120 * b ^ 5 * c ^ 9 * (b - c) ^ 13 +
    15 * b ^ 5 * c ^ 7 * (b - c) ^ 14 -
    b ^ 5 * c ^ 5 * (b - c) ^ 15

private def orderTwentyFiveRawClearedChunk3 (b c : ℚ) : ℚ :=
  b ^ 4 * c ^ 36 - 12 * b ^ 4 * c ^ 34 * (b - c) +
    48 * b ^ 4 * c ^ 32 * (b - c) ^ 2 -
    49 * b ^ 4 * c ^ 30 * (b - c) ^ 3 -
    165 * b ^ 4 * c ^ 28 * (b - c) ^ 4 +
    609 * b ^ 4 * c ^ 26 * (b - c) ^ 5 -
    433 * b ^ 4 * c ^ 24 * (b - c) ^ 6 -
    1623 * b ^ 4 * c ^ 22 * (b - c) ^ 7 +
    4299 * b ^ 4 * c ^ 20 * (b - c) ^ 8 -
    4615 * b ^ 4 * c ^ 18 * (b - c) ^ 9 +
    3435 * b ^ 4 * c ^ 16 * (b - c) ^ 10 -
    1740 * b ^ 4 * c ^ 14 * (b - c) ^ 11 +
    455 * b ^ 4 * c ^ 12 * (b - c) ^ 12

private def orderTwentyFiveRawClearedChunk4 (b c : ℚ) : ℚ :=
  b ^ 3 * c ^ 37 - 9 * b ^ 3 * c ^ 35 * (b - c) +
    25 * b ^ 3 * c ^ 33 * (b - c) ^ 2 -
    35 * b ^ 3 * c ^ 31 * (b - c) ^ 3 +
    45 * b ^ 3 * c ^ 29 * (b - c) ^ 4 -
    181 * b ^ 3 * c ^ 27 * (b - c) ^ 5 +
    569 * b ^ 3 * c ^ 25 * (b - c) ^ 6 -
    705 * b ^ 3 * c ^ 23 * (b - c) ^ 7 +
    5 * b ^ 3 * c ^ 21 * (b - c) ^ 8 +
    470 * b ^ 3 * c ^ 19 * (b - c) ^ 9 -
    540 * b ^ 3 * c ^ 17 * (b - c) ^ 10 +
    340 * b ^ 3 * c ^ 15 * (b - c) ^ 11 -
    105 * b ^ 3 * c ^ 13 * (b - c) ^ 12 +
    b ^ 2 * c ^ 38 - 6 * b ^ 2 * c ^ 36 * (b - c) +
    21 * b ^ 2 * c ^ 34 * (b - c) ^ 2 -
    56 * b ^ 2 * c ^ 32 * (b - c) ^ 3 +
    126 * b ^ 2 * c ^ 30 * (b - c) ^ 4 -
    231 * b ^ 2 * c ^ 28 * (b - c) ^ 5 +
    266 * b ^ 2 * c ^ 26 * (b - c) ^ 6 -
    126 * b ^ 2 * c ^ 24 * (b - c) ^ 7 +
    96 * b ^ 2 * c ^ 22 * (b - c) ^ 8 -
    91 * b ^ 2 * c ^ 20 * (b - c) ^ 9 +
    75 * b ^ 2 * c ^ 18 * (b - c) ^ 10 -
    45 * b ^ 2 * c ^ 16 * (b - c) ^ 11 +
    15 * b ^ 2 * c ^ 14 * (b - c) ^ 12

private def orderTwentyFiveRawClearedChunk5 (b c : ℚ) : ℚ :=
  6 * b * c ^ 29 * (b - c) ^ 5 -
    28 * b * c ^ 27 * (b - c) ^ 6 +
    21 * b * c ^ 25 * (b - c) ^ 7 -
    15 * b * c ^ 23 * (b - c) ^ 8 +
    10 * b * c ^ 21 * (b - c) ^ 9 -
    6 * b * c ^ 19 * (b - c) ^ 10 +
    3 * b * c ^ 17 * (b - c) ^ 11 -
    b * c ^ 15 * (b - c) ^ 12 + c ^ 30 * (b - c) ^ 5

private def orderTwentyFiveRawClearedPolynomial (b c : ℚ) : ℚ :=
  orderTwentyFiveRawClearedChunk0 b c +
    orderTwentyFiveRawClearedChunk1 b c +
    orderTwentyFiveRawClearedChunk2 b c +
    orderTwentyFiveRawClearedChunk3 b c +
    orderTwentyFiveRawClearedChunk4 b c +
    orderTwentyFiveRawClearedChunk5 b c

private theorem orderTwentyFiveRawSutherlandPolynomial_chunk0_substitution
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    (c ^ 10 * (b - c) ^ 15) *
        orderTwentyFiveRawSutherlandPolynomialChunk0
          (b / c) (c ^ 2 / (b - c)) =
      orderTwentyFiveRawClearedChunk0 b c := by
  simp only [orderTwentyFiveRawSutherlandPolynomialChunk0,
    orderTwentyFiveRawSutherlandCoefficient8,
    orderTwentyFiveRawSutherlandCoefficient9,
    orderTwentyFiveRawSutherlandCoefficient10,
    orderTwentyFiveRawClearedChunk0]
  field_simp [hc, sub_ne_zero.mpr hbc]; ring

private theorem orderTwentyFiveRawSutherlandPolynomial_chunk1_substitution
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    (c ^ 10 * (b - c) ^ 15) *
        orderTwentyFiveRawSutherlandPolynomialChunk1
          (b / c) (c ^ 2 / (b - c)) =
      orderTwentyFiveRawClearedChunk1 b c := by
  simp only [orderTwentyFiveRawSutherlandPolynomialChunk1,
    orderTwentyFiveRawSutherlandCoefficient6,
    orderTwentyFiveRawSutherlandCoefficient7,
    orderTwentyFiveRawClearedChunk1]
  field_simp [hc, sub_ne_zero.mpr hbc]; ring

private theorem orderTwentyFiveRawSutherlandPolynomial_chunk2_substitution
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    (c ^ 10 * (b - c) ^ 15) *
        orderTwentyFiveRawSutherlandPolynomialChunk2
          (b / c) (c ^ 2 / (b - c)) =
      orderTwentyFiveRawClearedChunk2 b c := by
  simp only [orderTwentyFiveRawSutherlandPolynomialChunk2,
    orderTwentyFiveRawSutherlandCoefficient5,
    orderTwentyFiveRawClearedChunk2]
  field_simp [hc, sub_ne_zero.mpr hbc]

private theorem orderTwentyFiveRawSutherlandPolynomial_chunk3_substitution
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    (c ^ 10 * (b - c) ^ 15) *
        orderTwentyFiveRawSutherlandPolynomialChunk3
          (b / c) (c ^ 2 / (b - c)) =
      orderTwentyFiveRawClearedChunk3 b c := by
  simp only [orderTwentyFiveRawSutherlandPolynomialChunk3,
    orderTwentyFiveRawSutherlandCoefficient4,
    orderTwentyFiveRawClearedChunk3]
  field_simp [hc, sub_ne_zero.mpr hbc]

private theorem orderTwentyFiveRawSutherlandPolynomial_chunk4_substitution
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    (c ^ 10 * (b - c) ^ 15) *
        orderTwentyFiveRawSutherlandPolynomialChunk4
          (b / c) (c ^ 2 / (b - c)) =
      orderTwentyFiveRawClearedChunk4 b c := by
  simp only [orderTwentyFiveRawSutherlandPolynomialChunk4,
    orderTwentyFiveRawSutherlandCoefficient2,
    orderTwentyFiveRawSutherlandCoefficient3,
    orderTwentyFiveRawClearedChunk4]
  field_simp [hc, sub_ne_zero.mpr hbc]; ring

private theorem orderTwentyFiveRawSutherlandPolynomial_chunk5_substitution
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    (c ^ 10 * (b - c) ^ 15) *
        orderTwentyFiveRawSutherlandPolynomialChunk5
          (b / c) (c ^ 2 / (b - c)) =
      orderTwentyFiveRawClearedChunk5 b c := by
  simp only [orderTwentyFiveRawSutherlandPolynomialChunk5,
    orderTwentyFiveRawSutherlandCoefficient0,
    orderTwentyFiveRawSutherlandCoefficient1,
    orderTwentyFiveRawClearedChunk5]
  field_simp [hc, sub_ne_zero.mpr hbc]

private theorem orderTwentyFiveRawSutherlandPolynomial_cleared_substitution
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    (c ^ 10 * (b - c) ^ 15) *
        orderTwentyFiveRawSutherlandPolynomial
          (b / c) (c ^ 2 / (b - c)) =
      orderTwentyFiveRawClearedPolynomial b c := by
  simp only [orderTwentyFiveRawSutherlandPolynomial,
    orderTwentyFiveRawClearedPolynomial, mul_add,
    orderTwentyFiveRawSutherlandPolynomial_chunk0_substitution b c hc hbc,
    orderTwentyFiveRawSutherlandPolynomial_chunk1_substitution b c hc hbc,
    orderTwentyFiveRawSutherlandPolynomial_chunk2_substitution b c hc hbc,
    orderTwentyFiveRawSutherlandPolynomial_chunk3_substitution b c hc hbc,
    orderTwentyFiveRawSutherlandPolynomial_chunk4_substitution b c hc hbc,
    orderTwentyFiveRawSutherlandPolynomial_chunk5_substitution b c hc hbc]

private theorem orderTwentyFiveRawClearedPolynomial_eq_noncuspidalFactor
    (b c : ℚ) :
    orderTwentyFiveRawClearedPolynomial b c =
      orderTwentyFiveNoncuspidalFactor b c := by
  simp only [orderTwentyFiveRawClearedPolynomial,
    orderTwentyFiveRawClearedChunk0, orderTwentyFiveRawClearedChunk1,
    orderTwentyFiveRawClearedChunk2, orderTwentyFiveRawClearedChunk3,
    orderTwentyFiveRawClearedChunk4, orderTwentyFiveRawClearedChunk5,
    orderTwentyFiveNoncuspidalFactor,
    orderTwentyFiveNoncuspidalFactorChunk0,
    orderTwentyFiveNoncuspidalFactorChunk1,
    orderTwentyFiveNoncuspidalFactorChunk2,
    orderTwentyFiveNoncuspidalFactorChunk3,
    orderTwentyFiveNoncuspidalFactorChunk4,
    orderTwentyFiveNoncuspidalFactorChunk5]
  ring

/- The exact change of variables `r=b/c`, `s=c²/(b-c)` sends Sutherland's
raw equation to the normalized noncuspidal factor.  Six separately checked
denominator-clearing identities keep the final ring normalization small. -/
private theorem orderTwentyFiveRawSutherlandPolynomial_substitution
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    orderTwentyFiveRawSutherlandPolynomial (b / c) (c ^ 2 / (b - c)) =
      orderTwentyFiveNoncuspidalFactor b c /
        (c ^ 10 * (b - c) ^ 15) := by
  have hden : c ^ 10 * (b - c) ^ 15 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 10 hc)
      (pow_ne_zero 15 (sub_ne_zero.mpr hbc))
  apply (eq_div_iff hden).mpr
  rw [← orderTwentyFiveRawClearedPolynomial_eq_noncuspidalFactor]
  simpa [mul_comm] using
    orderTwentyFiveRawSutherlandPolynomial_cleared_substitution b c hc hbc

/-- The integral cross-product of the normalized abscissas of `13P` and
`12P`, before removing its cuspidal factor. -/
def orderTwentyFiveNormalizedCollision (b c : ℚ) : ℚ :=
  (-c * b * twentyFiveA b c * twentyFiveB b c *
      twentyFiveG b c * twentyFiveI b c) *
      (c * twentyFiveA b c * twentyFiveG b c) ^ 2 -
    (twentyFiveF b c * twentyFiveH b c) * twentyFiveH b c ^ 2


private theorem twentyFiveNormalizedDatum_next_den_ne_zero
    (b c : ℚ) (n : ℕ) (hn : n ≤ 10)
    (hxNum : (twentyFiveNormalizedDatum b c n).xNum ≠ 0) :
    (twentyFiveNormalizedDatum b c (n + 1)).den ≠ 0 := by
  interval_cases n <;>
    norm_num [twentyFiveNormalizedDatum, twentyFiveA, twentyFiveB,
      twentyFiveC, twentyFiveD, twentyFiveE, twentyFiveF, twentyFiveG,
      twentyFiveH, mul_ne_zero_iff] at hxNum ⊢ <;>
    aesop

private theorem twentyFiveNormalizedDatum_next_spec_0
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 0).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 0).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 1).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 0
    let next := twentyFiveNormalizedDatum b c 1
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  constructor <;> field_simp [_hxNum, _hden, _hnextDen]
  all_goals
    ring

private theorem twentyFiveNormalizedDatum_next_spec_1
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 1).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 1).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 2).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 1
    let next := twentyFiveNormalizedDatum b c 2
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  constructor <;> field_simp [_hxNum, _hden, _hnextDen]
  all_goals
    try unfold twentyFiveA
    try unfold twentyFiveB
    ring

private theorem twentyFiveNormalizedDatum_next_spec_2
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 2).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 2).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 3).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 2
    let next := twentyFiveNormalizedDatum b c 3
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  constructor <;> field_simp [_hxNum, _hden, _hnextDen]
  all_goals
    try unfold twentyFiveA
    try unfold twentyFiveB
    try unfold twentyFiveE
    try unfold twentyFiveF
    try unfold twentyFiveG
    try unfold twentyFiveH
    try unfold twentyFiveI
    try unfold twentyFiveJ
    ring

private theorem twentyFiveNormalizedDatum_next_spec_3
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 3).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 3).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 4).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 3
    let next := twentyFiveNormalizedDatum b c 4
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff, neg_ne_zero] at _hxNum _hden _hnextDen
  constructor <;> field_simp [_hxNum, _hden, _hnextDen]
  all_goals
    try unfold twentyFiveA
    try unfold twentyFiveB
    try unfold twentyFiveC
    try unfold twentyFiveD
    try unfold twentyFiveE
    try unfold twentyFiveF
    try unfold twentyFiveG
    try unfold twentyFiveH
    try unfold twentyFiveI
    try unfold twentyFiveJ
    ring

private theorem twentyFiveNormalizedDatum_next_spec_4
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 4).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 4).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 5).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 4
    let next := twentyFiveNormalizedDatum b c 5
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  constructor <;> field_simp [_hxNum, _hden, _hnextDen]
  all_goals
    try unfold twentyFiveA
    try unfold twentyFiveB
    try unfold twentyFiveC
    try unfold twentyFiveD
    try unfold twentyFiveE
    try unfold twentyFiveF
    try unfold twentyFiveG
    try unfold twentyFiveH
    try unfold twentyFiveI
    try unfold twentyFiveJ
    ring

private theorem twentyFiveNormalizedDatum_next_spec_5
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 5).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 5).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 6).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 5
    let next := twentyFiveNormalizedDatum b c 6
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  constructor <;> field_simp [_hxNum, _hden, _hnextDen]
  all_goals
    try unfold twentyFiveA
    try unfold twentyFiveB
    try unfold twentyFiveC
    try unfold twentyFiveD
    try unfold twentyFiveE
    try unfold twentyFiveF
    try unfold twentyFiveG
    try unfold twentyFiveH
    try unfold twentyFiveI
    try unfold twentyFiveJ
    ring

private theorem twentyFiveNormalizedDatum_next_spec_6
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 6).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 6).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 7).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 6
    let next := twentyFiveNormalizedDatum b c 7
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  constructor <;> field_simp [_hxNum, _hden, _hnextDen]
  all_goals
    try unfold twentyFiveA
    try unfold twentyFiveB
    try unfold twentyFiveC
    try unfold twentyFiveD
    try unfold twentyFiveE
    try unfold twentyFiveF
    try unfold twentyFiveG
    try unfold twentyFiveH
    try unfold twentyFiveI
    try unfold twentyFiveJ
    ring

private theorem twentyFiveNormalizedDatum_next_spec_7
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 7).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 7).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 8).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 7
    let next := twentyFiveNormalizedDatum b c 8
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff, neg_ne_zero] at _hxNum _hden _hnextDen
  constructor <;> field_simp [_hxNum, _hden, _hnextDen]
  all_goals
    try unfold twentyFiveA
    try unfold twentyFiveB
    try unfold twentyFiveC
    try unfold twentyFiveD
    try unfold twentyFiveE
    try unfold twentyFiveF
    try unfold twentyFiveG
    try unfold twentyFiveH
    try unfold twentyFiveI
    try unfold twentyFiveJ
    ring

private theorem twentyFiveNormalizedDatum_next_spec_8_slope
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 8).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 8).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 9).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 8
    (Q.yNum / Q.den ^ 3) / (Q.xNum / Q.den ^ 2) =
      c * twentyFiveA b c * twentyFiveG b c * b * twentyFiveD b c /
        ((b - c) * twentyFiveE b c * twentyFiveF b c) := by
  simp only [twentyFiveNormalizedDatum] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  field_simp [_hxNum, _hden, _hnextDen]

private theorem twentyFiveNormalizedDatum_next_spec_8_x
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 8).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 8).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 9).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 8
    let next := twentyFiveNormalizedDatum b c 9
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
      next.xNum / next.den ^ 2 := by
  have hslope :=
    twentyFiveNormalizedDatum_next_spec_8_slope b c _hxNum _hden _hnextDen
  simp only [twentyFiveNormalizedDatum] at _hxNum _hden _hnextDen hslope ⊢
  simp only [tateNextX]
  rw [hslope]
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  field_simp [_hxNum, _hden, _hnextDen]
  unfold twentyFiveA twentyFiveD twentyFiveE twentyFiveF twentyFiveG
  ring

private theorem twentyFiveNormalizedDatum_next_spec_8_y
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 8).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 8).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 9).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 8
    let next := twentyFiveNormalizedDatum b c 9
    tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
      next.yNum / next.den ^ 3 := by
  have hxNext :=
    twentyFiveNormalizedDatum_next_spec_8_x b c _hxNum _hden _hnextDen
  have hslope :=
    twentyFiveNormalizedDatum_next_spec_8_slope b c _hxNum _hden _hnextDen
  simp only [twentyFiveNormalizedDatum] at _hxNum _hden _hnextDen hxNext hslope ⊢
  simp only [tateNextY]
  rw [hslope, hxNext]
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  field_simp [_hxNum, _hden, _hnextDen]
  unfold twentyFiveA twentyFiveD twentyFiveE twentyFiveF twentyFiveG
    twentyFiveH
  ring

private theorem twentyFiveNormalizedDatum_next_spec_8
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 8).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 8).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 9).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 8
    let next := twentyFiveNormalizedDatum b c 9
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  exact ⟨twentyFiveNormalizedDatum_next_spec_8_x b c _hxNum _hden _hnextDen,
    twentyFiveNormalizedDatum_next_spec_8_y b c _hxNum _hden _hnextDen⟩

private theorem twentyFiveNormalizedDatum_next_spec_9_x
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 9).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 9).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 10).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 9
    let next := twentyFiveNormalizedDatum b c 10
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
      next.xNum / next.den ^ 2 := by
  simp only [twentyFiveNormalizedDatum, tateNextX] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  field_simp [_hxNum, _hden, _hnextDen]
  unfold twentyFiveA twentyFiveE twentyFiveF twentyFiveG twentyFiveH
  ring

private theorem twentyFiveI_recurrence (b c : ℚ) :
    twentyFiveB b c * twentyFiveI b c * twentyFiveF b c ^ 2 +
        b * (c * twentyFiveA b c * twentyFiveG b c) ^ 3 =
      (b - c) * twentyFiveE b c * twentyFiveH b c ^ 2 +
        (1 - c) * twentyFiveF b c * twentyFiveH b c *
          (c * twentyFiveA b c * twentyFiveG b c) := by
  unfold twentyFiveA twentyFiveB twentyFiveE twentyFiveF twentyFiveG
    twentyFiveH twentyFiveI
  ring

private theorem twentyFiveNormalizedDatum_next_spec_9_y
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 9).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 9).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 10).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 9
    let next := twentyFiveNormalizedDatum b c 10
    tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
      next.yNum / next.den ^ 3 := by
  have hxNext :=
    twentyFiveNormalizedDatum_next_spec_9_x b c _hxNum _hden _hnextDen
  simp only [twentyFiveNormalizedDatum] at _hxNum _hden _hnextDen hxNext ⊢
  simp only [tateNextY]
  rw [hxNext]
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  field_simp [_hxNum, _hden, _hnextDen]
  linear_combination twentyFiveF b c ^ 3 * twentyFiveI_recurrence b c

private theorem twentyFiveNormalizedDatum_next_spec_9
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 9).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 9).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 10).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 9
    let next := twentyFiveNormalizedDatum b c 10
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  exact ⟨twentyFiveNormalizedDatum_next_spec_9_x b c _hxNum _hden _hnextDen,
    twentyFiveNormalizedDatum_next_spec_9_y b c _hxNum _hden _hnextDen⟩

private theorem twentyFiveNormalizedDatum_next_spec_10_x
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 10).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 10).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 11).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 10
    let next := twentyFiveNormalizedDatum b c 11
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
      next.xNum / next.den ^ 2 := by
  simp only [twentyFiveNormalizedDatum, tateNextX] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  field_simp [_hxNum, _hden, _hnextDen]
  unfold twentyFiveA twentyFiveB twentyFiveF twentyFiveG twentyFiveH twentyFiveI
  ring

private theorem twentyFiveJ_recurrence (b c : ℚ) :
    -(twentyFiveB b c) ^ 2 * twentyFiveI b c ^ 2 * twentyFiveF b c +
        twentyFiveB b c * twentyFiveI b c *
          (c * twentyFiveA b c * twentyFiveG b c) * (1 - c) *
          twentyFiveH b c +
        twentyFiveH b c ^ 3 =
      (b - c) * twentyFiveJ b c * b *
        (c * twentyFiveA b c * twentyFiveG b c) ^ 2 := by
  unfold twentyFiveA twentyFiveB twentyFiveF twentyFiveG twentyFiveH
    twentyFiveI twentyFiveJ
  ring

private theorem twentyFiveNormalizedDatum_next_spec_10_y
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 10).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 10).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 11).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 10
    let next := twentyFiveNormalizedDatum b c 11
    tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
      next.yNum / next.den ^ 3 := by
  have hxNext :=
    twentyFiveNormalizedDatum_next_spec_10_x b c _hxNum _hden _hnextDen
  simp only [twentyFiveNormalizedDatum] at _hxNum _hden _hnextDen hxNext ⊢
  simp only [tateNextY]
  rw [hxNext]
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  field_simp [_hxNum, _hden, _hnextDen]
  linear_combination
    b * (c * twentyFiveA b c * twentyFiveG b c) ^ 3 *
      twentyFiveJ_recurrence b c

private theorem twentyFiveNormalizedDatum_next_spec_10
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 10).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 10).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 11).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 10
    let next := twentyFiveNormalizedDatum b c 11
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  exact ⟨twentyFiveNormalizedDatum_next_spec_10_x b c _hxNum _hden _hnextDen,
    twentyFiveNormalizedDatum_next_spec_10_y b c _hxNum _hden _hnextDen⟩

private theorem twentyFiveNormalizedDatum_next_spec
    (b c : ℚ) (n : ℕ) (hn : n ≤ 10)
    (hxNum : (twentyFiveNormalizedDatum b c n).xNum ≠ 0)
    (hden : (twentyFiveNormalizedDatum b c n).den ≠ 0)
    (hnextDen : (twentyFiveNormalizedDatum b c (n + 1)).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c n
    let next := twentyFiveNormalizedDatum b c (n + 1)
    tateNextX b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.xNum / next.den ^ 2 ∧
      tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
        next.yNum / next.den ^ 3 := by
  interval_cases n
  · exact twentyFiveNormalizedDatum_next_spec_0 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_1 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_2 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_3 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_4 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_5 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_6 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_7 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_8 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_9 b c hxNum hden hnextDen
  · exact twentyFiveNormalizedDatum_next_spec_10 b c hxNum hden hnextDen

private theorem twentyFiveNormalizedDatum_spec
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (n : ℕ) (hn : n ≤ 11) :
    let Q := twentyFiveNormalizedDatum b c n
    Q.den ≠ 0 ∧
      tateSuccessiveX b c n = Q.xNum / Q.den ^ 2 ∧
      tateSuccessiveY b c n = Q.yNum / Q.den ^ 3 := by
  induction n with
  | zero =>
      norm_num [twentyFiveNormalizedDatum]
  | succ n ih =>
      have hn10 : n ≤ 10 := by omega
      obtain ⟨hden, hxEq, hyEq⟩ := ih (by omega)
      have hxNum : (twentyFiveNormalizedDatum b c n).xNum ≠ 0 := by
        intro hxNum
        apply hx n hn10
        rw [hxEq, hxNum]
        simp
      have hnextDen :=
        twentyFiveNormalizedDatum_next_den_ne_zero b c n hn10 hxNum
      obtain ⟨hnextX, hnextY⟩ :=
        twentyFiveNormalizedDatum_next_spec b c n hn10 hxNum hden hnextDen
      refine ⟨hnextDen, ?_, ?_⟩
      · simpa [Nat.succ_eq_add_one] using
          (tateSuccessiveX_succ b c n).trans (by rw [hxEq, hyEq, hnextX])
      · simpa [Nat.succ_eq_add_one] using
          (tateSuccessiveY_succ b c n).trans (by rw [hxEq, hyEq, hnextY])

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXTwo
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 0 =
      orderTwentyFiveRawXTwo (b / c) (c ^ 2 / (b - c)) := by
  rw [(twentyFiveNormalizedDatum_spec b c hx 0 (by omega)).2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXTwo]
  field_simp [hc, sub_ne_zero.mpr hbc]

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXThree
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 1 =
      orderTwentyFiveRawXThree (b / c) (c ^ 2 / (b - c)) := by
  rw [(twentyFiveNormalizedDatum_spec b c hx 1 (by omega)).2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXThree]
  field_simp [hc, sub_ne_zero.mpr hbc]

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXFour
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 2 =
      orderTwentyFiveRawXFour (b / c) (c ^ 2 / (b - c)) := by
  rw [(twentyFiveNormalizedDatum_spec b c hx 2 (by omega)).2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXFour]
  field_simp [hc, sub_ne_zero.mpr hbc]

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXSix
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 4 =
      orderTwentyFiveRawXSix (b / c) (c ^ 2 / (b - c)) := by
  have hspec := twentyFiveNormalizedDatum_spec b c hx 4 (by omega)
  rw [hspec.2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXSix]
  field_simp [hc, sub_ne_zero.mpr hbc, hspec.1]
  unfold twentyFiveA twentyFiveB
  ring

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXSeven
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 5 =
      orderTwentyFiveRawXSeven (b / c) (c ^ 2 / (b - c)) := by
  have hspec := twentyFiveNormalizedDatum_spec b c hx 5 (by omega)
  rw [hspec.2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXSeven]
  field_simp [hc, sub_ne_zero.mpr hbc, hspec.1]
  unfold twentyFiveA twentyFiveB twentyFiveC
  ring

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXEight
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 6 =
      orderTwentyFiveRawXEight (b / c) (c ^ 2 / (b - c)) := by
  have hspec := twentyFiveNormalizedDatum_spec b c hx 6 (by omega)
  rw [hspec.2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXEight]
  field_simp [hc, sub_ne_zero.mpr hbc, hspec.1]
  unfold twentyFiveB twentyFiveC twentyFiveD
  ring

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXNine
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 7 =
      orderTwentyFiveRawXNine (b / c) (c ^ 2 / (b - c)) := by
  have hspec := twentyFiveNormalizedDatum_spec b c hx 7 (by omega)
  rw [hspec.2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXNine]
  field_simp [hc, sub_ne_zero.mpr hbc, hspec.1]
  unfold twentyFiveC twentyFiveD twentyFiveE
  ring

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXEleven
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 9 =
      orderTwentyFiveRawXEleven (b / c) (c ^ 2 / (b - c)) := by
  have hspec := twentyFiveNormalizedDatum_spec b c hx 9 (by omega)
  rw [hspec.2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXEleven]
  field_simp [hc, sub_ne_zero.mpr hbc, hspec.1]
  unfold twentyFiveA twentyFiveE twentyFiveF twentyFiveG
  ring

private theorem tateSuccessiveX_eq_orderTwentyFiveRawXTwelve
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    tateSuccessiveX b c 10 =
      orderTwentyFiveRawXTwelve (b / c) (c ^ 2 / (b - c)) := by
  have hspec := twentyFiveNormalizedDatum_spec b c hx 10 (by omega)
  rw [hspec.2.1]
  simp only [twentyFiveNormalizedDatum, orderTwentyFiveRawXTwelve]
  field_simp [hc, sub_ne_zero.mpr hbc, hspec.1]
  unfold twentyFiveA twentyFiveF twentyFiveG twentyFiveH
  ring

private theorem orderTwentyFiveBrunault_coordinates_eq_raw
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    orderTwentyFiveBrunaultU b c =
        orderTwentyFiveRawBrunaultU (b / c) (c ^ 2 / (b - c)) ∧
      orderTwentyFiveBrunaultV b c =
        orderTwentyFiveRawBrunaultV (b / c) (c ^ 2 / (b - c)) := by
  have h2 := tateSuccessiveX_eq_orderTwentyFiveRawXTwo b c hx hc hbc
  have h3 := tateSuccessiveX_eq_orderTwentyFiveRawXThree b c hx hc hbc
  have h4 := tateSuccessiveX_eq_orderTwentyFiveRawXFour b c hx hc hbc
  have h6 := tateSuccessiveX_eq_orderTwentyFiveRawXSix b c hx hc hbc
  have h7 := tateSuccessiveX_eq_orderTwentyFiveRawXSeven b c hx hc hbc
  have h8 := tateSuccessiveX_eq_orderTwentyFiveRawXEight b c hx hc hbc
  have h9 := tateSuccessiveX_eq_orderTwentyFiveRawXNine b c hx hc hbc
  have h11 := tateSuccessiveX_eq_orderTwentyFiveRawXEleven b c hx hc hbc
  have h12 := tateSuccessiveX_eq_orderTwentyFiveRawXTwelve b c hx hc hbc
  simp only [orderTwentyFiveBrunaultU, orderTwentyFiveBrunaultV,
    orderTwentyFiveBrunaultYFour, orderTwentyFiveBrunaultYSeven,
    orderTwentyFiveBrunaultYNine, orderTwentyFiveBrunaultYThree,
    orderTwentyFiveRawBrunaultU, orderTwentyFiveRawBrunaultV,
    orderTwentyFiveRawYFour, orderTwentyFiveRawYSeven,
    orderTwentyFiveRawYNine, orderTwentyFiveRawYThree,
    h2, h3, h4, h6, h7, h8, h9, h11, h12]
  exact ⟨trivial, trivial⟩

private theorem orderTwentyFiveBrunault_orbitUnits_eq_raw
    (b c : ℚ) (hx : ∀ k ≤ 10, tateSuccessiveX b c k ≠ 0)
    (hc : c ≠ 0) (hbc : b ≠ c) :
    orderTwentyFiveBrunaultYOne b c =
        orderTwentyFiveRawYSeven (b / c) (c ^ 2 / (b - c)) ∧
      orderTwentyFiveBrunaultYTwo b c =
        orderTwentyFiveRawYTwo (b / c) (c ^ 2 / (b - c)) ∧
      orderTwentyFiveBrunaultYFour b c =
        orderTwentyFiveRawYFour (b / c) (c ^ 2 / (b - c)) ∧
      orderTwentyFiveBrunaultYEight b c =
        orderTwentyFiveRawYEight (b / c) (c ^ 2 / (b - c)) ∧
      orderTwentyFiveBrunaultYNine b c =
        orderTwentyFiveRawYNine (b / c) (c ^ 2 / (b - c)) := by
  have h2 := tateSuccessiveX_eq_orderTwentyFiveRawXTwo b c hx hc hbc
  have h3 := tateSuccessiveX_eq_orderTwentyFiveRawXThree b c hx hc hbc
  have h4 := tateSuccessiveX_eq_orderTwentyFiveRawXFour b c hx hc hbc
  have h6 := tateSuccessiveX_eq_orderTwentyFiveRawXSix b c hx hc hbc
  have h7 := tateSuccessiveX_eq_orderTwentyFiveRawXSeven b c hx hc hbc
  have h8 := tateSuccessiveX_eq_orderTwentyFiveRawXEight b c hx hc hbc
  have h9 := tateSuccessiveX_eq_orderTwentyFiveRawXNine b c hx hc hbc
  have h11 := tateSuccessiveX_eq_orderTwentyFiveRawXEleven b c hx hc hbc
  have h12 := tateSuccessiveX_eq_orderTwentyFiveRawXTwelve b c hx hc hbc
  simp only [orderTwentyFiveBrunaultYOne, orderTwentyFiveBrunaultYTwo,
    orderTwentyFiveBrunaultYFour, orderTwentyFiveBrunaultYEight,
    orderTwentyFiveBrunaultYNine, orderTwentyFiveRawYSeven,
    orderTwentyFiveRawYTwo, orderTwentyFiveRawYFour,
    orderTwentyFiveRawYEight, orderTwentyFiveRawYNine,
    h2, h3, h4, h6, h7, h8, h9, h11, h12, sub_zero]
  simp

/-- The normalized collision is exactly the cusp factor `b-c` times the
degree-40 factor, with no unrecorded scalar. -/
theorem orderTwentyFive_normalized_collision_factorization (b c : ℚ) :
    orderTwentyFiveNormalizedCollision b c =
      -((b - c) * orderTwentyFiveNoncuspidalFactor b c) := by
  simp only [orderTwentyFiveNormalizedCollision, twentyFiveA, twentyFiveB,
    twentyFiveF, twentyFiveG, twentyFiveH, twentyFiveI,
    orderTwentyFiveNoncuspidalFactor,
    orderTwentyFiveNoncuspidalFactorChunk0,
    orderTwentyFiveNoncuspidalFactorChunk1,
    orderTwentyFiveNoncuspidalFactorChunk2,
    orderTwentyFiveNoncuspidalFactorChunk3,
    orderTwentyFiveNoncuspidalFactorChunk4,
    orderTwentyFiveNoncuspidalFactorChunk5]
  ring

/-- Any denominator-checked zero of the `12P/13P` recurrence lies on the
noncuspidal degree-40 model. The same calculation proves `c ≠ 0` and
`b ≠ c`, rather than cancelling either cusp factor silently. -/
theorem orderTwentyFiveNoncuspidalFactor_eq_zero_of_recurrence
    (b c : ℚ) (hx : ∀ n ≤ 10, tateSuccessiveX b c n ≠ 0)
    (hrecurrence : orderTwentyFiveRecurrenceEquation b c = 0) :
    c ≠ 0 ∧ b ≠ c ∧ orderTwentyFiveNoncuspidalFactor b c = 0 := by
  have hfour := twentyFiveNormalizedDatum_spec b c hx 2 (by omega)
  have hfive := twentyFiveNormalizedDatum_spec b c hx 3 (by omega)
  have htwelve := twentyFiveNormalizedDatum_spec b c hx 10 (by omega)
  have hthirteen := twentyFiveNormalizedDatum_spec b c hx 11 (by omega)
  have hc : c ≠ 0 := by
    simpa [twentyFiveNormalizedDatum] using hfour.1
  have hbc : b ≠ c := by
    exact sub_ne_zero.mp (by
      simpa [twentyFiveNormalizedDatum] using hfive.1)
  have hcollision : tateSuccessiveX b c 11 = tateSuccessiveX b c 10 :=
    sub_eq_zero.mp hrecurrence
  rw [hthirteen.2.1, htwelve.2.1] at hcollision
  have hcross :
      (twentyFiveNormalizedDatum b c 11).xNum *
            (twentyFiveNormalizedDatum b c 10).den ^ 2 -
          (twentyFiveNormalizedDatum b c 10).xNum *
            (twentyFiveNormalizedDatum b c 11).den ^ 2 = 0 :=
    sub_eq_zero.mpr <|
      (div_eq_div_iff (pow_ne_zero 2 hthirteen.1)
        (pow_ne_zero 2 htwelve.1)).mp hcollision
  change orderTwentyFiveNormalizedCollision b c = 0 at hcross
  rw [orderTwentyFive_normalized_collision_factorization] at hcross
  have hfactor : (b - c) * orderTwentyFiveNoncuspidalFactor b c = 0 :=
    neg_eq_zero.mp hcross
  exact ⟨hc, hbc, (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hbc)⟩

/-- Exact order 25 of the marked Tate point forces the noncuspidal degree-40
affine equation. -/
theorem orderTwentyFiveNoncuspidalFactor_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    c ≠ 0 ∧ b ≠ c ∧ orderTwentyFiveNoncuspidalFactor b c = 0 := by
  exact orderTwentyFiveNoncuspidalFactor_eq_zero_of_recurrence b c
    (tateSuccessiveX_ne_zero_of_marked_order_twentyFive b c hb h00 horder)
    (orderTwentyFiveRecurrenceEquation_eq_zero_of_marked_order b c hb h00 horder)

/-- The first Brunault modular-unit coordinate of an exact-order-25 marked
Tate point avoids the exceptional diagonal value `1`.  This is the public
characteristic-zero consumer of the raw Sutherland equation and its checked
degree-eight diagonal eliminant. -/
theorem orderTwentyFiveBrunaultU_ne_one_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveBrunaultU b c ≠ 1 := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hx :=
    tateSuccessiveX_ne_zero_of_marked_order_twentyFive b c hb h00 horder
  obtain ⟨hc, hbc, hfactor⟩ :=
    orderTwentyFiveNoncuspidalFactor_eq_zero_of_marked_order
      b c hb h00 horder
  have hF : orderTwentyFiveRawSutherlandPolynomial r s = 0 := by
    dsimp [r, s]
    rw [orderTwentyFiveRawSutherlandPolynomial_substitution b c hc hbc,
      hfactor]
    simp
  have hs : s ≠ 0 := by
    dsimp [s]
    exact div_ne_zero (pow_ne_zero 2 hc) (sub_ne_zero.mpr hbc)
  have hthree :=
    tateSuccessiveX_eq_orderTwentyFiveRawXThree b c hx hc hbc
  have hfour :=
    tateSuccessiveX_eq_orderTwentyFiveRawXFour b c hx hc hbc
  have hseven :=
    tateSuccessiveX_eq_orderTwentyFiveRawXSeven b c hx hc hbc
  have hnine :=
    tateSuccessiveX_eq_orderTwentyFiveRawXNine b c hx hc hbc
  have heleven :=
    tateSuccessiveX_eq_orderTwentyFiveRawXEleven b c hx hc hbc
  have htwelve :=
    tateSuccessiveX_eq_orderTwentyFiveRawXTwelve b c hx hc hbc
  have hrs : r - s ≠ 0 := by
    intro hrs
    have hraw : orderTwentyFiveRawXSeven r s = 0 := by
      simp [orderTwentyFiveRawXSeven, hrs]
    exact hx 5 (by omega) (hseven.trans hraw)
  have hrss : r - s ^ 2 + s - 1 ≠ 0 := by
    intro hrss
    have hraw : orderTwentyFiveRawXNine r s = 0 := by
      simp [orderTwentyFiveRawXNine, hrss]
    exact hx 7 (by omega) (hnine.trans hraw)
  have hs1 : s - 1 ≠ 0 := by
    intro hs1
    have hraw : orderTwentyFiveRawXTwelve r s = 0 := by
      simp [orderTwentyFiveRawXTwelve, hs1]
    exact hx 10 (by omega) (htwelve.trans hraw)
  have hD :
      r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0 := by
    intro hD
    have hraw : orderTwentyFiveRawXEleven r s = 0 := by
      simp [orderTwentyFiveRawXEleven, hD]
    exact hx 9 (by omega) (heleven.trans hraw)
  have hE :
      r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0 := by
    intro hE
    have hraw : orderTwentyFiveRawXTwelve r s = 0 := by
      simp [orderTwentyFiveRawXTwelve, hE]
    exact hx 10 (by omega) (htwelve.trans hraw)
  obtain ⟨hd13, hd74, hd4twelve, hd39, -, -⟩ :=
    orderTwentyFiveBrunault_denominators_ne_zero b c hb h00 horder
  have h4twelveRaw :
      orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwelve r s ≠ 0 := by
    rw [← hfour, ← htwelve]
    exact hd4twelve
  have hthreeNineRaw :
      orderTwentyFiveRawXThree r s - orderTwentyFiveRawXNine r s ≠ 0 := by
    rw [← hthree, ← hnine]
    exact hd39
  have hsevenFourRaw :
      orderTwentyFiveRawXSeven r s - orderTwentyFiveRawXFour r s ≠ 0 := by
    rw [← hseven, ← hfour]
    exact hd74
  have hzeroThreeRaw : 0 - orderTwentyFiveRawXThree r s ≠ 0 := by
    rw [← hthree]
    exact hd13
  have hdiagDen : orderTwentyFiveRawDiagonalDenominator r s ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hs1 (pow_ne_zero 2 hD)) hE
  have hrawU : orderTwentyFiveRawBrunaultU r s ≠ 1 := by
    intro hU
    have hsub : orderTwentyFiveRawBrunaultU r s - 1 = 0 := sub_eq_zero.mpr hU
    rw [orderTwentyFiveRawBrunaultU_sub_one r s hrs hrss hs1 hD hE
      h4twelveRaw hthreeNineRaw hsevenFourRaw hzeroThreeRaw] at hsub
    have hN : orderTwentyFiveRawDiagonalNumerator r s = 0 :=
      (div_eq_zero_iff.mp hsub).resolve_right hdiagDen
    exact orderTwentyFiveRawDiagonalNumerator_ne_zero r s hs hs1 hF hN
  have hcoordinates := orderTwentyFiveBrunault_coordinates_eq_raw b c hx hc hbc
  rw [hcoordinates.1]
  exact hrawU

private structure OrderTwentyFiveNormalizedOrbitData
    (b c r s : ℚ) : Prop where
  curve : OrderTwentyFiveRawOrbitData.sutherlandPolynomial r s = 0
  oneDenominator : OrderTwentyFiveRawOrbitData.rawUnitOneDenominator r s ≠ 0
  twoDenominator : OrderTwentyFiveRawOrbitData.rawUnitTwoDenominator r s ≠ 0
  fourDenominator : OrderTwentyFiveRawOrbitData.rawUnitFourDenominator r s ≠ 0
  eightDenominator : OrderTwentyFiveRawOrbitData.rawUnitEightDenominator r s ≠ 0
  nineDenominator : OrderTwentyFiveRawOrbitData.rawUnitNineDenominator r s ≠ 0
  one : orderTwentyFiveBrunaultYOne b c =
    OrderTwentyFiveRawOrbitData.rawUnitOneNumerator r s /
      OrderTwentyFiveRawOrbitData.rawUnitOneDenominator r s
  two : orderTwentyFiveBrunaultYTwo b c =
    OrderTwentyFiveRawOrbitData.rawUnitTwoNumerator r s /
      OrderTwentyFiveRawOrbitData.rawUnitTwoDenominator r s
  four : orderTwentyFiveBrunaultYFour b c =
    OrderTwentyFiveRawOrbitData.rawUnitFourNumerator r s /
      OrderTwentyFiveRawOrbitData.rawUnitFourDenominator r s
  eight : orderTwentyFiveBrunaultYEight b c =
    OrderTwentyFiveRawOrbitData.rawUnitEightNumerator r s /
      OrderTwentyFiveRawOrbitData.rawUnitEightDenominator r s
  nine : orderTwentyFiveBrunaultYNine b c =
    OrderTwentyFiveRawOrbitData.rawUnitNineNumerator r s /
      OrderTwentyFiveRawOrbitData.rawUnitNineDenominator r s

private theorem orderTwentyFive_normalizedOrbitData_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    OrderTwentyFiveNormalizedOrbitData b c
      (b / c) (c ^ 2 / (b - c)) := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hx :=
    tateSuccessiveX_ne_zero_of_marked_order_twentyFive b c hb h00 horder
  have hxy :=
    tateSuccessiveX_ne_of_marked_order_twentyFive b c hb h00 horder
  obtain ⟨hc, hbc, hfactor⟩ :=
    orderTwentyFiveNoncuspidalFactor_eq_zero_of_marked_order
      b c hb h00 horder
  have hF : orderTwentyFiveRawSutherlandPolynomial r s = 0 := by
    dsimp [r, s]
    rw [orderTwentyFiveRawSutherlandPolynomial_substitution b c hc hbc,
      hfactor]
    simp
  have hr : r ≠ 0 := by
    dsimp [r]
    exact div_ne_zero hb hc
  have hs : s ≠ 0 := by
    dsimp [s]
    exact div_ne_zero (pow_ne_zero 2 hc) (sub_ne_zero.mpr hbc)
  have h2 := tateSuccessiveX_eq_orderTwentyFiveRawXTwo b c hx hc hbc
  have h3 := tateSuccessiveX_eq_orderTwentyFiveRawXThree b c hx hc hbc
  have h4 := tateSuccessiveX_eq_orderTwentyFiveRawXFour b c hx hc hbc
  have h6 := tateSuccessiveX_eq_orderTwentyFiveRawXSix b c hx hc hbc
  have h7 := tateSuccessiveX_eq_orderTwentyFiveRawXSeven b c hx hc hbc
  have h8 := tateSuccessiveX_eq_orderTwentyFiveRawXEight b c hx hc hbc
  have h9 := tateSuccessiveX_eq_orderTwentyFiveRawXNine b c hx hc hbc
  have h11 := tateSuccessiveX_eq_orderTwentyFiveRawXEleven b c hx hc hbc
  have h12 := tateSuccessiveX_eq_orderTwentyFiveRawXTwelve b c hx hc hbc
  have hrs : r - s ≠ 0 := by
    intro hrs
    have hraw : orderTwentyFiveRawXSeven r s = 0 := by
      simp [orderTwentyFiveRawXSeven, hrs]
    exact hx 5 (by omega) (h7.trans hraw)
  have hD : r - s ^ 2 + s - 1 ≠ 0 := by
    intro hD
    have hraw : orderTwentyFiveRawXNine r s = 0 := by
      simp [orderTwentyFiveRawXNine, hD]
    exact hx 7 (by omega) (h9.trans hraw)
  have hs1 : s - 1 ≠ 0 := by
    intro hs1
    have hraw : orderTwentyFiveRawXTwelve r s = 0 := by
      simp [orderTwentyFiveRawXTwelve, hs1]
    exact hx 10 (by omega) (h12.trans hraw)
  have hC : r * s - 2 * r + 1 ≠ 0 := by
    intro hC
    have hraw : orderTwentyFiveRawXEight r s = 0 := by
      simp [orderTwentyFiveRawXEight, hC]
    exact hx 6 (by omega) (h8.trans hraw)
  have hE :
      r ^ 2 - r * s ^ 3 + 3 * r * s ^ 2 - 4 * r * s + s ≠ 0 := by
    intro hE
    have hraw : orderTwentyFiveRawXEleven r s = 0 := by
      simp [orderTwentyFiveRawXEleven, hE]
    exact hx 9 (by omega) (h11.trans hraw)
  have hG :
      r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1 ≠ 0 := by
    intro hG
    have hraw : orderTwentyFiveRawXTwelve r s = 0 := by
      simp [orderTwentyFiveRawXTwelve, hG]
    exact hx 10 (by omega) (h12.trans hraw)
  have h74 :
      orderTwentyFiveRawXSeven r s - orderTwentyFiveRawXFour r s ≠ 0 := by
    rw [← h7, ← h4]
    exact sub_ne_zero.mpr (hxy 5 2 (by omega) (by omega) (by omega))
  have h3raw : orderTwentyFiveRawXThree r s ≠ 0 := by
    rw [← h3]
    exact hx 1 (by omega)
  have h26 :
      orderTwentyFiveRawXTwo r s - orderTwentyFiveRawXSix r s ≠ 0 := by
    rw [← h2, ← h6]
    exact sub_ne_zero.mpr (hxy 0 4 (by omega) (by omega) (by omega))
  have h118 :
      orderTwentyFiveRawXEleven r s - orderTwentyFiveRawXEight r s ≠ 0 := by
    rw [← h11, ← h8]
    exact sub_ne_zero.mpr (hxy 9 6 (by omega) (by omega) (by omega))
  have h8raw : orderTwentyFiveRawXEight r s ≠ 0 := by
    rw [← h8]
    exact hx 6 (by omega)
  have h67 :
      orderTwentyFiveRawXSix r s - orderTwentyFiveRawXSeven r s ≠ 0 := by
    rw [← h6, ← h7]
    exact sub_ne_zero.mpr (hxy 4 5 (by omega) (by omega) (by omega))
  have h92 :
      orderTwentyFiveRawXNine r s - orderTwentyFiveRawXTwo r s ≠ 0 := by
    rw [← h9, ← h2]
    exact sub_ne_zero.mpr (hxy 7 0 (by omega) (by omega) (by omega))
  have h1211 :
      orderTwentyFiveRawXTwelve r s - orderTwentyFiveRawXEleven r s ≠ 0 := by
    rw [← h12, ← h11]
    exact sub_ne_zero.mpr (hxy 10 9 (by omega) (by omega) (by omega))
  have hpole2 : OrderTwentyFiveRawOrbitData.rawUnitTwoPoleFactor r s ≠ 0 := by
    intro hpole2
    apply h118
    rw [orderTwentyFiveRawXEleven_sub_XEight_eq_poleFactor r s hC hE]
    simp [hpole2]
  have hpole8 : OrderTwentyFiveRawOrbitData.rawUnitEightPoleFactor r s ≠ 0 := by
    intro hpole8
    apply h67
    rw [orderTwentyFiveRawXSix_sub_XSeven_eq_poleFactor r s hs1 hrs]
    simp [hpole8]
  have hpole9 : OrderTwentyFiveRawOrbitData.rawUnitNinePoleFactor r s ≠ 0 := by
    intro hpole9
    apply h1211
    rw [orderTwentyFiveRawXTwelve_sub_XEleven_eq_poleFactor r s hs1 hE hG]
    simp [hpole9]
  have h412 :
      orderTwentyFiveRawXFour r s - orderTwentyFiveRawXTwelve r s ≠ 0 := by
    rw [← h4, ← h12]
    exact sub_ne_zero.mpr (hxy 2 10 (by omega) (by omega) (by omega))
  have h39 :
      orderTwentyFiveRawXThree r s - orderTwentyFiveRawXNine r s ≠ 0 := by
    rw [← h3, ← h9]
    exact sub_ne_zero.mpr (hxy 1 7 (by omega) (by omega) (by omega))
  have hpole4 : OrderTwentyFiveRawOrbitData.rawUnitFourPoleFactor r s ≠ 0 := by
    intro hpole4
    apply h412
    rw [orderTwentyFiveRawXFour_sub_XTwelve_eq_poleFactor r s hs1 hG]
    simp [hpole4]
  have hden1 : OrderTwentyFiveRawOrbitData.rawUnitOneDenominator r s ≠ 0 := by
    rw [OrderTwentyFiveRawOrbitData.rawUnitOneDenominator_factorization]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hs1) hr)
        (pow_ne_zero 2 hD))
      (pow_ne_zero 2 hG)
  have hden2 : OrderTwentyFiveRawOrbitData.rawUnitTwoDenominator r s ≠ 0 := by
    rw [OrderTwentyFiveRawOrbitData.rawUnitTwoDenominator_factorization]
    exact mul_ne_zero (pow_ne_zero 2 hrs) hpole2
  have hden4 : OrderTwentyFiveRawOrbitData.rawUnitFourDenominator r s ≠ 0 := by
    rw [OrderTwentyFiveRawOrbitData.rawUnitFourDenominator_factorization]
    exact mul_ne_zero (mul_ne_zero hC (pow_ne_zero 2 hE)) hpole4
  have hden8 : OrderTwentyFiveRawOrbitData.rawUnitEightDenominator r s ≠ 0 := by
    rw [OrderTwentyFiveRawOrbitData.rawUnitEightDenominator_factorization]
    exact hpole8
  have hden9 : OrderTwentyFiveRawOrbitData.rawUnitNineDenominator r s ≠ 0 := by
    rw [OrderTwentyFiveRawOrbitData.rawUnitNineDenominator_factorization]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero hs hrs) (pow_ne_zero 2 hC)) hpole9
  have hunits := orderTwentyFiveBrunault_orbitUnits_eq_raw b c hx hc hbc
  have hone := orderTwentyFiveRawYSeven_eq_orbitData
    r s hs1 hrs hD hG h74 h3raw hden1
  have htwo := orderTwentyFiveRawYTwo_eq_orbitData
    r s hs1 hrs hC hE h26 h118 hden2
  have hfour := orderTwentyFiveRawYFour_eq_orbitData
    r s hs1 hC hD hE hG h412 h39 hden4
  have height := orderTwentyFiveRawYEight_eq_orbitData
    r s hs1 hrs hC h8raw h67 hden8
  have hnine := orderTwentyFiveRawYNine_eq_orbitData
    r s hs1 hC hD hE hG h92 h1211 hden9
  have hcurve : OrderTwentyFiveRawOrbitData.sutherlandPolynomial r s = 0 := by
    rw [← orderTwentyFiveRawSutherlandPolynomial_eq_orbitData]
    exact hF
  have hData : OrderTwentyFiveNormalizedOrbitData b c r s := {
    curve := hcurve
    oneDenominator := hden1
    twoDenominator := hden2
    fourDenominator := hden4
    eightDenominator := hden8
    nineDenominator := hden9
    one := hunits.1.trans hone
    two := hunits.2.1.trans htwo
    four := hunits.2.2.1.trans hfour
    eight := hunits.2.2.2.1.trans height
    nine := hunits.2.2.2.2.trans hnine
  }
  simpa only [r, s] using hData

/-- The first of Lécacheux's five orbit relations holds for the actual
Brunault units attached to an exact-order-25 marked Tate point. -/
theorem orderTwentyFiveOrbitRelationZero_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveOrbitRelationZero
        (orderTwentyFiveBrunaultXZero b c)
        (orderTwentyFiveBrunaultXOne b c)
        (orderTwentyFiveBrunaultXTwo b c)
        (orderTwentyFiveBrunaultXThree b c)
        (orderTwentyFiveBrunaultXFour b c) = 0 := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hData : OrderTwentyFiveNormalizedOrbitData b c r s := by
    simpa only [r, s] using
      orderTwentyFive_normalizedOrbitData_of_marked_order b c hb h00 horder
  have hraw := OrderTwentyFiveRawOrbitData.RelationZeroCertificate.relation_eq_zero
    r s hData.curve hData.oneDenominator hData.nineDenominator
      hData.eightDenominator hData.twoDenominator
  have hy :
      orderTwentyFiveBrunaultYOne b c - orderTwentyFiveBrunaultYNine b c -
          orderTwentyFiveBrunaultYOne b c * orderTwentyFiveBrunaultYEight b c *
            (orderTwentyFiveBrunaultYTwo b c -
              orderTwentyFiveBrunaultYOne b c) = 0 := by
    rw [hData.one, hData.nine, hData.eight, hData.two]
    exact hraw
  simp only [orderTwentyFiveOrbitRelationZero,
    orderTwentyFiveBrunaultXZero, orderTwentyFiveBrunaultXOne,
    orderTwentyFiveBrunaultXTwo, orderTwentyFiveBrunaultXThree]
  linear_combination orderTwentyFiveBrunaultYFour b c * hy

/-- The third of Lécacheux's five orbit relations holds for the actual
Brunault units attached to an exact-order-25 marked Tate point. -/
theorem orderTwentyFiveOrbitRelationTwo_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveOrbitRelationTwo
        (orderTwentyFiveBrunaultXZero b c)
        (orderTwentyFiveBrunaultXOne b c)
        (orderTwentyFiveBrunaultXTwo b c)
        (orderTwentyFiveBrunaultXThree b c)
        (orderTwentyFiveBrunaultXFour b c) = 0 := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hData : OrderTwentyFiveNormalizedOrbitData b c r s := by
    simpa only [r, s] using
      orderTwentyFive_normalizedOrbitData_of_marked_order b c hb h00 horder
  have hraw := OrderTwentyFiveRawOrbitRelationTwoData.relation_eq_zero
    r s hData.curve hData.oneDenominator hData.twoDenominator
      hData.fourDenominator hData.eightDenominator
  have hy :
      orderTwentyFiveBrunaultYFour b c - orderTwentyFiveBrunaultYTwo b c -
          orderTwentyFiveBrunaultYFour b c * orderTwentyFiveBrunaultYOne b c *
            (orderTwentyFiveBrunaultYEight b c -
              orderTwentyFiveBrunaultYFour b c) = 0 := by
    rw [hData.four, hData.two, hData.one, hData.eight]
    exact hraw
  simp only [orderTwentyFiveOrbitRelationTwo,
    orderTwentyFiveBrunaultXZero, orderTwentyFiveBrunaultXTwo,
    orderTwentyFiveBrunaultXThree,
    orderTwentyFiveBrunaultXFour]
  linear_combination orderTwentyFiveBrunaultYNine b c * hy

/-- Lécacheux's norm-one orbit relation holds for the actual Brunault units
attached to an exact-order-25 marked Tate point. -/
theorem orderTwentyFiveOrbitRelationFive_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 25) :
    orderTwentyFiveOrbitRelationFive
        (orderTwentyFiveBrunaultXZero b c)
        (orderTwentyFiveBrunaultXOne b c)
        (orderTwentyFiveBrunaultXTwo b c)
        (orderTwentyFiveBrunaultXThree b c)
        (orderTwentyFiveBrunaultXFour b c) = 0 := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hData : OrderTwentyFiveNormalizedOrbitData b c r s := by
    simpa only [r, s] using
      orderTwentyFive_normalizedOrbitData_of_marked_order b c hb h00 horder
  have hraw := OrderTwentyFiveRawOrbitNormData.relation_eq_zero
    r s hData.curve hData.oneDenominator hData.twoDenominator
      hData.fourDenominator hData.eightDenominator hData.nineDenominator
  have hy :
      orderTwentyFiveBrunaultYOne b c * orderTwentyFiveBrunaultYTwo b c *
            orderTwentyFiveBrunaultYFour b c *
            orderTwentyFiveBrunaultYEight b c *
            orderTwentyFiveBrunaultYNine b c -
          1 = 0 := by
    rw [hData.one, hData.two, hData.four, hData.eight, hData.nine]
    exact hraw
  have hproduct :
      orderTwentyFiveBrunaultYOne b c * orderTwentyFiveBrunaultYTwo b c *
          orderTwentyFiveBrunaultYFour b c *
          orderTwentyFiveBrunaultYEight b c *
          orderTwentyFiveBrunaultYNine b c = 1 :=
    sub_eq_zero.mp hy
  simp only [orderTwentyFiveOrbitRelationFive,
    orderTwentyFiveBrunaultXZero, orderTwentyFiveBrunaultXOne,
    orderTwentyFiveBrunaultXTwo, orderTwentyFiveBrunaultXThree,
    orderTwentyFiveBrunaultXFour]
  calc
    orderTwentyFiveBrunaultYOne b c * orderTwentyFiveBrunaultYFour b c *
              (orderTwentyFiveBrunaultYTwo b c *
                orderTwentyFiveBrunaultYEight b c) *
            (orderTwentyFiveBrunaultYFour b c *
              orderTwentyFiveBrunaultYNine b c) *
          (orderTwentyFiveBrunaultYEight b c *
            orderTwentyFiveBrunaultYOne b c) *
        (orderTwentyFiveBrunaultYNine b c *
            orderTwentyFiveBrunaultYTwo b c) -
        1 =
        (orderTwentyFiveBrunaultYOne b c * orderTwentyFiveBrunaultYTwo b c *
            orderTwentyFiveBrunaultYFour b c *
            orderTwentyFiveBrunaultYEight b c *
            orderTwentyFiveBrunaultYNine b c) ^ 2 - 1 := by ring
    _ = 0 := by rw [hproduct]; norm_num

/-- An arbitrary rational point of exact order 25 produces a genuinely
noncuspidal point on the fixed degree-40 affine model, while retaining the
checked discriminant scaling from Tate normalization. -/
theorem exists_tateOrderTwentyFive_noncuspidal_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 25) :
    ∃ b c u : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      orderTwentyFiveNoncuspidalFactor b c = 0 ∧
      u ^ 12 * E.Δ = (tateNormalCurve b c).Δ := by
  obtain ⟨b, c, u, hu, hb, hx, hrecurrence, -, hdisc⟩ :=
    exists_tateOrderTwentyFive_recurrence_certificate E P hP
  obtain ⟨hc, hbc, hfactor⟩ :=
    orderTwentyFiveNoncuspidalFactor_eq_zero_of_recurrence b c hx hrecurrence
  exact ⟨b, c, u, hu, hb, hc, hbc, hfactor, hdisc⟩

end MazurTorsion.Kubert
