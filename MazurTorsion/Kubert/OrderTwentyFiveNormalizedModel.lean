/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFive

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
    try unfold twentyFiveC
    try unfold twentyFiveD
    try unfold twentyFiveE
    try unfold twentyFiveF
    try unfold twentyFiveG
    try unfold twentyFiveH
    try unfold twentyFiveI
    try unfold twentyFiveJ
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
    try unfold twentyFiveC
    try unfold twentyFiveD
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

private theorem twentyFiveNormalizedDatum_next_spec_10_y
    (b c : ℚ)
    (_hxNum : (twentyFiveNormalizedDatum b c 10).xNum ≠ 0)
    (_hden : (twentyFiveNormalizedDatum b c 10).den ≠ 0)
    (_hnextDen : (twentyFiveNormalizedDatum b c 11).den ≠ 0) :
    let Q := twentyFiveNormalizedDatum b c 10
    let next := twentyFiveNormalizedDatum b c 11
    tateNextY b c (Q.xNum / Q.den ^ 2) (Q.yNum / Q.den ^ 3) =
      next.yNum / next.den ^ 3 := by
  simp only [twentyFiveNormalizedDatum, tateNextX, tateNextY] at _hxNum _hden _hnextDen ⊢
  try simp only [mul_ne_zero_iff] at _hxNum _hden _hnextDen
  field_simp [_hxNum, _hden, _hnextDen]
  unfold twentyFiveA twentyFiveB twentyFiveF twentyFiveG twentyFiveH
    twentyFiveI twentyFiveJ
  ring

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
