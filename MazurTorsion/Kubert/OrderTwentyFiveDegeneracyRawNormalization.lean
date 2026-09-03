/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveDegeneracyFinalCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitExclusion
import MazurTorsion.Kubert.OrderTwentyFiveDegeneracy
import MazurTorsion.Kubert.OrderTwentyFiveRawOrbitData
import MazurTorsion.Kubert.TateNormalFormMultiples
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Raw normalization for the order-twenty-five degeneracy comparison

The two first Lécacheux orbit units and the Tate parameter obtained by
normalizing at `5P` are expressed on the same raw chart.  The generated
coefficient certificates then identify their Hauptmodul degeneracy values.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveDegeneracyRawNormalization

open OrderTwentyFiveRawOrbitData
open OrderTwentyFiveDegeneracyCertificate
open OrderTwentyFiveDegeneracyPairCertificate
open OrderTwentyFiveDegeneracyPowerCertificate
open OrderTwentyFiveDegeneracyFinalCertificate


private def rawOrbitZeroNumeratorChunk0 (r s : ℚ) : ℚ :=
  - s ^ 5
    + r * s ^ 2
    - 3 * r * s ^ 3
    + 6 * r * s ^ 4
    + 6 * r * s ^ 5
    - 6 * r * s ^ 6
    + 3 * r * s ^ 7
    - r * s ^ 8
    - 9 * r ^ 2 * s ^ 2
    + 32 * r ^ 2 * s ^ 3
    - 78 * r ^ 2 * s ^ 4
    + 58 * r ^ 2 * s ^ 5
    - 26 * r ^ 2 * s ^ 6
    + 9 * r ^ 2 * s ^ 7
    - r ^ 2 * s ^ 8
    - r ^ 3
    + 9 * r ^ 3 * s
    - 9 * r ^ 3 * s ^ 2
    - 6 * r ^ 3 * s ^ 3
    + 99 * r ^ 3 * s ^ 4

private def rawOrbitZeroNumeratorChunk1 (r s : ℚ) : ℚ :=
  - 120 * r ^ 3 * s ^ 5
    + 71 * r ^ 3 * s ^ 6
    - 30 * r ^ 3 * s ^ 7
    + 8 * r ^ 3 * s ^ 8
    - r ^ 3 * s ^ 9
    + 3 * r ^ 4
    - 25 * r ^ 4 * s
    + 55 * r ^ 4 * s ^ 2
    - 102 * r ^ 4 * s ^ 3
    + 59 * r ^ 4 * s ^ 4
    + 2 * r ^ 4 * s ^ 5
    - 9 * r ^ 4 * s ^ 6
    + 2 * r ^ 4 * s ^ 7
    - 3 * r ^ 5
    + 22 * r ^ 5 * s
    - 43 * r ^ 5 * s ^ 2
    + 79 * r ^ 5 * s ^ 3
    - 80 * r ^ 5 * s ^ 4
    + 40 * r ^ 5 * s ^ 5
    - 10 * r ^ 5 * s ^ 6

private def rawOrbitZeroNumeratorChunk2 (r s : ℚ) : ℚ :=
  r ^ 5 * s ^ 7
    + r ^ 6
    - 6 * r ^ 6 * s
    + 5 * r ^ 6 * s ^ 2
    - r ^ 6 * s ^ 3

def rawOrbitZeroNumerator (r s : ℚ) : ℚ :=
  rawOrbitZeroNumeratorChunk0 r s +
    rawOrbitZeroNumeratorChunk1 r s +
    rawOrbitZeroNumeratorChunk2 r s

private def rawOrbitZeroDenominatorChunk0 (r s : ℚ) : ℚ :=
  s ^ 2
    - s ^ 3
    + s ^ 4
    - s ^ 5
    - 11 * r * s ^ 2
    + 16 * r * s ^ 3
    - 15 * r * s ^ 4
    + 16 * r * s ^ 5
    - 8 * r * s ^ 6
    + 2 * r * s ^ 7
    + 2 * r ^ 2 * s
    + 41 * r ^ 2 * s ^ 2
    - 76 * r ^ 2 * s ^ 3
    + 66 * r ^ 2 * s ^ 4
    - 61 * r ^ 2 * s ^ 5
    + 46 * r ^ 2 * s ^ 6
    - 24 * r ^ 2 * s ^ 7
    + 7 * r ^ 2 * s ^ 8
    - r ^ 2 * s ^ 9
    - 14 * r ^ 3 * s

private def rawOrbitZeroDenominatorChunk1 (r s : ℚ) : ℚ :=
  - 54 * r ^ 3 * s ^ 2
    + 140 * r ^ 3 * s ^ 3
    - 105 * r ^ 3 * s ^ 4
    + 34 * r ^ 3 * s ^ 5
    + 2 * r ^ 3 * s ^ 6
    - 4 * r ^ 3 * s ^ 7
    + r ^ 3 * s ^ 8
    + r ^ 4
    + 29 * r ^ 4 * s
    + 7 * r ^ 4 * s ^ 2
    - 125 * r ^ 4 * s ^ 3
    + 165 * r ^ 4 * s ^ 4
    - 112 * r ^ 4 * s ^ 5
    + 44 * r ^ 4 * s ^ 6
    - 10 * r ^ 4 * s ^ 7
    + r ^ 4 * s ^ 8
    - 3 * r ^ 5
    - 22 * r ^ 5 * s
    + 51 * r ^ 5 * s ^ 2
    - 38 * r ^ 5 * s ^ 3

private def rawOrbitZeroDenominatorChunk2 (r s : ℚ) : ℚ :=
  14 * r ^ 5 * s ^ 4
    - 2 * r ^ 5 * s ^ 5
    + 3 * r ^ 6
    - 4 * r ^ 6 * s
    + r ^ 6 * s ^ 2

def rawOrbitZeroDenominator (r s : ℚ) : ℚ :=
  rawOrbitZeroDenominatorChunk0 r s +
    rawOrbitZeroDenominatorChunk1 r s +
    rawOrbitZeroDenominatorChunk2 r s

private def rawOrbitOneNumeratorChunk0 (r s : ℚ) : ℚ :=
  r * s ^ 2
    - 4 * r * s ^ 3
    + 8 * r * s ^ 4
    - 12 * r * s ^ 5
    + 15 * r * s ^ 6
    - 16 * r * s ^ 7
    + 15 * r * s ^ 8
    - 12 * r * s ^ 9
    + 8 * r * s ^ 10
    - 4 * r * s ^ 11
    + r * s ^ 12
    - 14 * r ^ 2 * s ^ 2
    + 58 * r ^ 2 * s ^ 3
    - 111 * r ^ 2 * s ^ 4
    + 141 * r ^ 2 * s ^ 5
    - 133 * r ^ 2 * s ^ 6
    + 91 * r ^ 2 * s ^ 7
    - 42 * r ^ 2 * s ^ 8
    + 8 * r ^ 2 * s ^ 9
    + r ^ 2 * s ^ 10

private def rawOrbitOneNumeratorChunk1 (r s : ℚ) : ℚ :=
  5 * r ^ 2 * s ^ 11
    - 5 * r ^ 2 * s ^ 12
    + r ^ 2 * s ^ 13
    + 90 * r ^ 3 * s ^ 2
    - 406 * r ^ 3 * s ^ 3
    + 840 * r ^ 3 * s ^ 4
    - 1131 * r ^ 3 * s ^ 5
    + 1145 * r ^ 3 * s ^ 6
    - 905 * r ^ 3 * s ^ 7
    + 558 * r ^ 3 * s ^ 8
    - 232 * r ^ 3 * s ^ 9
    + 19 * r ^ 3 * s ^ 10
    + 33 * r ^ 3 * s ^ 11
    - 12 * r ^ 3 * s ^ 12
    + r ^ 3 * s ^ 13
    + r ^ 4
    - 13 * r ^ 4 * s
    - 262 * r ^ 4 * s ^ 2
    + 1402 * r ^ 4 * s ^ 3
    - 3144 * r ^ 4 * s ^ 4

private def rawOrbitOneNumeratorChunk2 (r s : ℚ) : ℚ :=
  4384 * r ^ 4 * s ^ 5
    - 4477 * r ^ 4 * s ^ 6
    + 3623 * r ^ 4 * s ^ 7
    - 2495 * r ^ 4 * s ^ 8
    + 1513 * r ^ 4 * s ^ 9
    - 711 * r ^ 4 * s ^ 10
    + 209 * r ^ 4 * s ^ 11
    - 32 * r ^ 4 * s ^ 12
    + 2 * r ^ 4 * s ^ 13
    - 7 * r ^ 5
    + 91 * r ^ 5 * s
    + 273 * r ^ 5 * s ^ 2
    - 2474 * r ^ 5 * s ^ 3
    + 6316 * r ^ 5 * s ^ 4
    - 9176 * r ^ 5 * s ^ 5
    + 9098 * r ^ 5 * s ^ 6
    - 6541 * r ^ 5 * s ^ 7
    + 3533 * r ^ 5 * s ^ 8
    - 1647 * r ^ 5 * s ^ 9
    + 778 * r ^ 5 * s ^ 10

private def rawOrbitOneNumeratorChunk3 (r s : ℚ) : ℚ :=
  - 319 * r ^ 5 * s ^ 11
    + 88 * r ^ 5 * s ^ 12
    - 14 * r ^ 5 * s ^ 13
    + r ^ 5 * s ^ 14
    + 20 * r ^ 6
    - 262 * r ^ 6 * s
    + 303 * r ^ 6 * s ^ 2
    + 1827 * r ^ 6 * s ^ 3
    - 6689 * r ^ 6 * s ^ 4
    + 11091 * r ^ 6 * s ^ 5
    - 11817 * r ^ 6 * s ^ 6
    + 8847 * r ^ 6 * s ^ 7
    - 4542 * r ^ 6 * s ^ 8
    + 1438 * r ^ 6 * s ^ 9
    - 212 * r ^ 6 * s ^ 10
    - 12 * r ^ 6 * s ^ 11
    + 9 * r ^ 6 * s ^ 12
    - r ^ 6 * s ^ 13
    - 29 * r ^ 7
    + 386 * r ^ 7 * s

private def rawOrbitOneNumeratorChunk4 (r s : ℚ) : ℚ :=
  - 1111 * r ^ 7 * s ^ 2
    + 695 * r ^ 7 * s ^ 3
    + 2139 * r ^ 7 * s ^ 4
    - 5605 * r ^ 7 * s ^ 5
    + 7069 * r ^ 7 * s ^ 6
    - 6133 * r ^ 7 * s ^ 7
    + 3959 * r ^ 7 * s ^ 8
    - 1866 * r ^ 7 * s ^ 9
    + 612 * r ^ 7 * s ^ 10
    - 132 * r ^ 7 * s ^ 11
    + 17 * r ^ 7 * s ^ 12
    - r ^ 7 * s ^ 13
    + 21 * r ^ 8
    - 285 * r ^ 8 * s
    + 1075 * r ^ 8 * s ^ 2
    - 1861 * r ^ 8 * s ^ 3
    + 1632 * r ^ 8 * s ^ 4
    - 614 * r ^ 8 * s ^ 5
    - 73 * r ^ 8 * s ^ 6
    + 147 * r ^ 8 * s ^ 7

private def rawOrbitOneNumeratorChunk5 (r s : ℚ) : ℚ :=
  - 47 * r ^ 8 * s ^ 8
    + 5 * r ^ 8 * s ^ 9
    - 6 * r ^ 9
    + 83 * r ^ 9 * s
    - 354 * r ^ 9 * s ^ 2
    + 751 * r ^ 9 * s ^ 3
    - 925 * r ^ 9 * s ^ 4
    + 702 * r ^ 9 * s ^ 5
    - 332 * r ^ 9 * s ^ 6
    + 95 * r ^ 9 * s ^ 7
    - 15 * r ^ 9 * s ^ 8
    + r ^ 9 * s ^ 9

def rawOrbitOneNumerator (r s : ℚ) : ℚ :=
  rawOrbitOneNumeratorChunk0 r s +
    rawOrbitOneNumeratorChunk1 r s +
    rawOrbitOneNumeratorChunk2 r s +
    rawOrbitOneNumeratorChunk3 r s +
    rawOrbitOneNumeratorChunk4 r s +
    rawOrbitOneNumeratorChunk5 r s

private def rawOrbitOneDenominatorChunk0 (r s : ℚ) : ℚ :=
  s ^ 10
    - r * s ^ 5
    + 3 * r * s ^ 6
    - 7 * r * s ^ 7
    + 13 * r * s ^ 8
    - 22 * r * s ^ 9
    + 4 * r * s ^ 10
    + r ^ 2 * s ^ 2
    - 6 * r ^ 2 * s ^ 3
    + 22 * r ^ 2 * s ^ 4
    - 43 * r ^ 2 * s ^ 5
    + 73 * r ^ 2 * s ^ 6
    - 100 * r ^ 2 * s ^ 7
    + 95 * r ^ 2 * s ^ 8
    + 38 * r ^ 2 * s ^ 9
    - 52 * r ^ 2 * s ^ 10
    + 22 * r ^ 2 * s ^ 11
    - 6 * r ^ 2 * s ^ 12
    + r ^ 2 * s ^ 13
    - r ^ 3 * s

private def rawOrbitOneDenominatorChunk1 (r s : ℚ) : ℚ :=
  - 3 * r ^ 3 * s ^ 2
    + 28 * r ^ 3 * s ^ 3
    - 114 * r ^ 3 * s ^ 4
    + 210 * r ^ 3 * s ^ 5
    - 329 * r ^ 3 * s ^ 6
    + 532 * r ^ 3 * s ^ 7
    - 873 * r ^ 3 * s ^ 8
    + 620 * r ^ 3 * s ^ 9
    - 244 * r ^ 3 * s ^ 10
    + 66 * r ^ 3 * s ^ 11
    - 13 * r ^ 3 * s ^ 12
    + r ^ 3 * s ^ 13
    + 9 * r ^ 4 * s
    - 13 * r ^ 4 * s ^ 2
    - 27 * r ^ 4 * s ^ 3
    + 235 * r ^ 4 * s ^ 4
    - 338 * r ^ 4 * s ^ 5
    + 68 * r ^ 4 * s ^ 6
    + 385 * r ^ 4 * s ^ 7
    + 244 * r ^ 4 * s ^ 8

private def rawOrbitOneDenominatorChunk2 (r s : ℚ) : ℚ :=
  - 700 * r ^ 4 * s ^ 9
    + 504 * r ^ 4 * s ^ 10
    - 206 * r ^ 4 * s ^ 11
    + 59 * r ^ 4 * s ^ 12
    - 11 * r ^ 4 * s ^ 13
    + r ^ 4 * s ^ 14
    - 36 * r ^ 5 * s
    + 97 * r ^ 5 * s ^ 2
    - 97 * r ^ 5 * s ^ 3
    - 416 * r ^ 5 * s ^ 4
    + 1162 * r ^ 5 * s ^ 5
    - 1174 * r ^ 5 * s ^ 6
    - 510 * r ^ 5 * s ^ 7
    + 1318 * r ^ 5 * s ^ 8
    - 789 * r ^ 5 * s ^ 9
    + 231 * r ^ 5 * s ^ 10
    - 45 * r ^ 5 * s ^ 11
    + 8 * r ^ 5 * s ^ 12
    - r ^ 5 * s ^ 13
    + 85 * r ^ 6 * s

private def rawOrbitOneDenominatorChunk3 (r s : ℚ) : ℚ :=
  - 306 * r ^ 6 * s ^ 2
    + 646 * r ^ 6 * s ^ 3
    - 324 * r ^ 6 * s ^ 4
    - 1068 * r ^ 6 * s ^ 5
    + 2913 * r ^ 6 * s ^ 6
    - 2610 * r ^ 6 * s ^ 7
    + 966 * r ^ 6 * s ^ 8
    - 29 * r ^ 6 * s ^ 9
    - 85 * r ^ 6 * s ^ 10
    + 24 * r ^ 6 * s ^ 11
    - 2 * r ^ 6 * s ^ 12
    - r ^ 7
    - 111 * r ^ 7 * s
    + 456 * r ^ 7 * s ^ 2
    - 1204 * r ^ 7 * s ^ 3
    + 1852 * r ^ 7 * s ^ 4
    - 1741 * r ^ 7 * s ^ 5
    + 253 * r ^ 7 * s ^ 6
    + 1080 * r ^ 7 * s ^ 7
    - 1106 * r ^ 7 * s ^ 8

private def rawOrbitOneDenominatorChunk4 (r s : ℚ) : ℚ :=
  518 * r ^ 7 * s ^ 9
    - 133 * r ^ 7 * s ^ 10
    + 18 * r ^ 7 * s ^ 11
    - r ^ 7 * s ^ 12
    + 3 * r ^ 8
    + 71 * r ^ 8 * s
    - 292 * r ^ 8 * s ^ 2
    + 776 * r ^ 8 * s ^ 3
    - 1358 * r ^ 8 * s ^ 4
    + 1857 * r ^ 8 * s ^ 5
    - 1773 * r ^ 8 * s ^ 6
    + 1111 * r ^ 8 * s ^ 7
    - 447 * r ^ 8 * s ^ 8
    + 112 * r ^ 8 * s ^ 9
    - 16 * r ^ 8 * s ^ 10
    + r ^ 8 * s ^ 11
    - 3 * r ^ 9
    - 17 * r ^ 9 * s
    + 60 * r ^ 9 * s ^ 2
    - 116 * r ^ 9 * s ^ 3

private def rawOrbitOneDenominatorChunk5 (r s : ℚ) : ℚ :=
  104 * r ^ 9 * s ^ 4
    - 48 * r ^ 9 * s ^ 5
    + 11 * r ^ 9 * s ^ 6
    - r ^ 9 * s ^ 7
    + r ^ 10

def rawOrbitOneDenominator (r s : ℚ) : ℚ :=
  rawOrbitOneDenominatorChunk0 r s +
    rawOrbitOneDenominatorChunk1 r s +
    rawOrbitOneDenominatorChunk2 r s +
    rawOrbitOneDenominatorChunk3 r s +
    rawOrbitOneDenominatorChunk4 r s +
    rawOrbitOneDenominatorChunk5 r s

private def rawOrbitZeroDenominatorMultiplierChunk0 (r s : ℚ) : ℚ :=
  r * s ^ 4
    - 3 * r * s ^ 5
    + 6 * r * s ^ 6
    - 8 * r * s ^ 7
    + 8 * r * s ^ 8
    - 6 * r * s ^ 9
    + 3 * r * s ^ 10
    - r * s ^ 11
    + r ^ 2
    - 6 * r ^ 2 * s
    + 21 * r ^ 2 * s ^ 2
    - 54 * r ^ 2 * s ^ 3
    + 95 * r ^ 2 * s ^ 4
    - 132 * r ^ 2 * s ^ 5
    + 143 * r ^ 2 * s ^ 6
    - 126 * r ^ 2 * s ^ 7
    + 89 * r ^ 2 * s ^ 8
    - 46 * r ^ 2 * s ^ 9
    + 17 * r ^ 2 * s ^ 10
    - 2 * r ^ 2 * s ^ 11

private def rawOrbitZeroDenominatorMultiplierChunk1 (r s : ℚ) : ℚ :=
  - 9 * r ^ 3
    + 48 * r ^ 3 * s
    - 147 * r ^ 3 * s ^ 2
    + 340 * r ^ 3 * s ^ 3
    - 556 * r ^ 3 * s ^ 4
    + 713 * r ^ 3 * s ^ 5
    - 719 * r ^ 3 * s ^ 6
    + 592 * r ^ 3 * s ^ 7
    - 417 * r ^ 3 * s ^ 8
    + 242 * r ^ 3 * s ^ 9
    - 121 * r ^ 3 * s ^ 10
    + 42 * r ^ 3 * s ^ 11
    - 9 * r ^ 3 * s ^ 12
    + r ^ 3 * s ^ 13
    + 36 * r ^ 4
    - 172 * r ^ 4 * s
    + 453 * r ^ 4 * s ^ 2
    - 926 * r ^ 4 * s ^ 3
    + 1359 * r ^ 4 * s ^ 4
    - 1536 * r ^ 4 * s ^ 5

private def rawOrbitZeroDenominatorMultiplierChunk2 (r s : ℚ) : ℚ :=
  1317 * r ^ 4 * s ^ 6
    - 820 * r ^ 4 * s ^ 7
    + 369 * r ^ 4 * s ^ 8
    - 84 * r ^ 4 * s ^ 9
    + r ^ 4 * s ^ 10
    + 4 * r ^ 4 * s ^ 11
    - r ^ 4 * s ^ 12
    - 83 * r ^ 5
    + 361 * r ^ 5 * s
    - 807 * r ^ 5 * s ^ 2
    + 1424 * r ^ 5 * s ^ 3
    - 1871 * r ^ 5 * s ^ 4
    + 1940 * r ^ 5 * s ^ 5
    - 1633 * r ^ 5 * s ^ 6
    + 1068 * r ^ 5 * s ^ 7
    - 584 * r ^ 5 * s ^ 8
    + 241 * r ^ 5 * s ^ 9
    - 67 * r ^ 5 * s ^ 10
    + 12 * r ^ 5 * s ^ 11
    - r ^ 5 * s ^ 12

private def rawOrbitZeroDenominatorMultiplierChunk3 (r s : ℚ) : ℚ :=
  119 * r ^ 6
    - 482 * r ^ 6 * s
    + 907 * r ^ 6 * s ^ 2
    - 1294 * r ^ 6 * s ^ 3
    + 1378 * r ^ 6 * s ^ 4
    - 1096 * r ^ 6 * s ^ 5
    + 702 * r ^ 6 * s ^ 6
    - 304 * r ^ 6 * s ^ 7
    + 86 * r ^ 6 * s ^ 8
    - 18 * r ^ 6 * s ^ 9
    + 2 * r ^ 6 * s ^ 10
    - 106 * r ^ 7
    + 413 * r ^ 7 * s
    - 677 * r ^ 7 * s ^ 2
    + 768 * r ^ 7 * s ^ 3
    - 650 * r ^ 7 * s ^ 4
    + 370 * r ^ 7 * s ^ 5
    - 168 * r ^ 7 * s ^ 6
    + 62 * r ^ 7 * s ^ 7
    - 13 * r ^ 7 * s ^ 8

private def rawOrbitZeroDenominatorMultiplierChunk4 (r s : ℚ) : ℚ :=
  r ^ 7 * s ^ 9
    + 54 * r ^ 8
    - 208 * r ^ 8 * s
    + 311 * r ^ 8 * s ^ 2
    - 284 * r ^ 8 * s ^ 3
    + 199 * r ^ 8 * s ^ 4
    - 92 * r ^ 8 * s ^ 5
    + 22 * r ^ 8 * s ^ 6
    - 2 * r ^ 8 * s ^ 7
    - 12 * r ^ 9
    + 46 * r ^ 9 * s
    - 62 * r ^ 9 * s ^ 2
    + 37 * r ^ 9 * s ^ 3
    - 10 * r ^ 9 * s ^ 4
    + r ^ 9 * s ^ 5

def rawOrbitZeroDenominatorMultiplier (r s : ℚ) : ℚ :=
  rawOrbitZeroDenominatorMultiplierChunk0 r s +
    rawOrbitZeroDenominatorMultiplierChunk1 r s +
    rawOrbitZeroDenominatorMultiplierChunk2 r s +
    rawOrbitZeroDenominatorMultiplierChunk3 r s +
    rawOrbitZeroDenominatorMultiplierChunk4 r s

private def rawOrbitOneDenominatorMultiplierChunk0 (r s : ℚ) : ℚ :=
  - s
    + r

def rawOrbitOneDenominatorMultiplier (r s : ℚ) : ℚ :=
  rawOrbitOneDenominatorMultiplierChunk0 r s

private def rawOrbitZeroNumeratorFactored (r s : ℚ) : ℚ :=
  -1 *
    (- s + r) *
    (s + r - 7 * r * s + 6 * r * s ^ 2 - 3 * r * s ^ 3 + r * s ^ 4 - r ^ 2 +
      6 * r ^ 2 * s - 5 * r ^ 2 * s ^ 2 + r ^ 2 * s ^ 3) *
    (- s ^ 3 + r - 3 * r * s + 6 * r * s ^ 2 - r * s ^ 3 - 2 * r ^ 2 +
      4 * r ^ 2 * s - 9 * r ^ 2 * s ^ 2 + 5 * r ^ 2 * s ^ 3 - r ^ 2 * s ^ 4 +
      r ^ 3)

private def rawOrbitZeroDenominatorFactored (r s : ℚ) : ℚ :=
  (- 1 + s) *
    (- 1 - s ^ 2 + 3 * r + r * s - 3 * r ^ 2 + r ^ 2 * s) *
    (s - 4 * r * s + 3 * r * s ^ 2 - r * s ^ 3 + r ^ 2) ^ 2

private def rawOrbitOneNumeratorFactored (r s : ℚ) : ℚ :=
  (- 1 + s) ^ 4 *
    (r) *
    (- 1 + s - s ^ 2 + r) *
    (1 - 2 * r + r * s) *
    (- 1 - s ^ 2 + 3 * r + r * s - 3 * r ^ 2 + r ^ 2 * s) *
    (s ^ 2 + s ^ 3 + s ^ 4 - 8 * r * s ^ 2 - 5 * r * s ^ 3 + r * s ^ 4 +
      28 * r ^ 2 * s ^ 2 - 11 * r ^ 2 * s ^ 3 + r ^ 2 * s ^ 4 + r ^ 3 -
      8 * r ^ 3 * s - 19 * r ^ 3 * s ^ 2 + 20 * r ^ 3 * s ^ 3 -
      7 * r ^ 3 * s ^ 4 + r ^ 3 * s ^ 5 - r ^ 4 + 9 * r ^ 4 * s -
      6 * r ^ 4 * s ^ 2 + r ^ 4 * s ^ 3)

private def rawOrbitOneDenominatorFactored (r s : ℚ) : ℚ :=
  (- s + r) *
    (- s ^ 3 + r - 3 * r * s + 6 * r * s ^ 2 - r * s ^ 3 - 2 * r ^ 2 +
      4 * r ^ 2 * s - 9 * r ^ 2 * s ^ 2 + 5 * r ^ 2 * s ^ 3 - r ^ 2 * s ^ 4 +
      r ^ 3) *
    (s ^ 6 - r * s + 3 * r * s ^ 2 - 6 * r * s ^ 3 + 10 * r * s ^ 4 -
      15 * r * s ^ 5 + 3 * r * s ^ 6 + 7 * r ^ 2 * s - 18 * r ^ 2 * s ^ 2 +
      25 * r ^ 2 * s ^ 3 - 31 * r ^ 2 * s ^ 4 + 66 * r ^ 2 * s ^ 5 -
      50 * r ^ 2 * s ^ 6 + 21 * r ^ 2 * s ^ 7 - 6 * r ^ 2 * s ^ 8 +
      r ^ 2 * s ^ 9 - 21 * r ^ 3 * s + 51 * r ^ 3 * s ^ 2 -
      41 * r ^ 3 * s ^ 3 - 30 * r ^ 3 * s ^ 4 + 21 * r ^ 3 * s ^ 5 +
      3 * r ^ 3 * s ^ 6 - 3 * r ^ 3 * s ^ 7 + 35 * r ^ 4 * s -
      105 * r ^ 4 * s ^ 2 + 144 * r ^ 4 * s ^ 3 - 60 * r ^ 4 * s ^ 4 -
      9 * r ^ 4 * s ^ 5 + 12 * r ^ 4 * s ^ 6 - 2 * r ^ 4 * s ^ 7 - r ^ 5 -
      20 * r ^ 5 * s + 69 * r ^ 5 * s ^ 2 - 121 * r ^ 5 * s ^ 3 +
      105 * r ^ 5 * s ^ 4 - 48 * r ^ 5 * s ^ 5 + 11 * r ^ 5 * s ^ 6 -
      r ^ 5 * s ^ 7 + r ^ 6)

private def rawOrbitZeroDenominatorMultiplierFactored (r s : ℚ) : ℚ :=
  (- 1 + s) *
    (r) *
    (1 - 2 * r + r * s) *
    (- 1 + s - s ^ 2 + r) ^ 2 *
    (- 1 - s ^ 2 + 3 * r + r * s - 3 * r ^ 2 + r ^ 2 * s) *
    (s ^ 4 + r - 3 * r * s + 6 * r * s ^ 2 - 10 * r * s ^ 3 +
      4 * r * s ^ 4 - r * s ^ 5 - 2 * r ^ 2 + 2 * r ^ 2 * s +
      3 * r ^ 2 * s ^ 2 + 2 * r ^ 3 - 4 * r ^ 3 * s + r ^ 3 * s ^ 2)

private def rawOrbitOneDenominatorMultiplierFactored (r s : ℚ) : ℚ :=
  (- s + r)

private def rawUnitOneNumeratorFactored (r s : ℚ) : ℚ :=
  (1 - 2 * r + r * s) *
    (- s ^ 3 + r - 3 * r * s + 6 * r * s ^ 2 - r * s ^ 3 - 2 * r ^ 2 +
      4 * r ^ 2 * s - 9 * r ^ 2 * s ^ 2 + 5 * r ^ 2 * s ^ 3 - r ^ 2 * s ^ 4 +
      r ^ 3) *
    (s ^ 4 + r - 3 * r * s + 6 * r * s ^ 2 - 10 * r * s ^ 3 +
      4 * r * s ^ 4 - r * s ^ 5 - 2 * r ^ 2 + 2 * r ^ 2 * s +
      3 * r ^ 2 * s ^ 2 + 2 * r ^ 3 - 4 * r ^ 3 * s + r ^ 3 * s ^ 2)

private def rawUnitFourNumeratorFactored (r s : ℚ) : ℚ :=
  -1 *
    (- 1 + s) *
    (r) *
    (- s + r) *
    (- 1 + s - s ^ 2 + r) ^ 2 *
    (s + r - 7 * r * s + 6 * r * s ^ 2 - 3 * r * s ^ 3 + r * s ^ 4 - r ^ 2 +
      6 * r ^ 2 * s - 5 * r ^ 2 * s ^ 2 + r ^ 2 * s ^ 3) *
    (- 1 - s ^ 2 + 3 * r + r * s - 3 * r ^ 2 + r ^ 2 * s)

private def rawUnitTwoNumeratorFactored (r s : ℚ) : ℚ :=
  -1 *
    (- 1 + s) ^ 3 *
    (r) *
    (- 1 + s - s ^ 2 + r) *
    (1 - 2 * r + r * s) *
    (s ^ 2 + s ^ 3 + s ^ 4 - 8 * r * s ^ 2 - 5 * r * s ^ 3 + r * s ^ 4 +
      28 * r ^ 2 * s ^ 2 - 11 * r ^ 2 * s ^ 3 + r ^ 2 * s ^ 4 + r ^ 3 -
      8 * r ^ 3 * s - 19 * r ^ 3 * s ^ 2 + 20 * r ^ 3 * s ^ 3 -
      7 * r ^ 3 * s ^ 4 + r ^ 3 * s ^ 5 - r ^ 4 + 9 * r ^ 4 * s -
      6 * r ^ 4 * s ^ 2 + r ^ 4 * s ^ 3)

private def rawUnitEightNumeratorFactored (r s : ℚ) : ℚ :=
  -1 *
    (- 1 + s) *
    (- s + r) *
    (- 1 - s ^ 2 + 3 * r + r * s - 3 * r ^ 2 + r ^ 2 * s)

private theorem rawOrbitZeroNumerator_factorization (r s : ℚ) :
    rawOrbitZeroNumerator r s = rawOrbitZeroNumeratorFactored r s := by
  simp only [rawOrbitZeroNumerator, rawOrbitZeroNumeratorChunk0,
    rawOrbitZeroNumeratorChunk1, rawOrbitZeroNumeratorChunk2,
    rawOrbitZeroNumeratorFactored]
  ring

private theorem rawOrbitZeroDenominator_factorization (r s : ℚ) :
    rawOrbitZeroDenominator r s = rawOrbitZeroDenominatorFactored r s := by
  simp only [rawOrbitZeroDenominator, rawOrbitZeroDenominatorChunk0,
    rawOrbitZeroDenominatorChunk1, rawOrbitZeroDenominatorChunk2,
    rawOrbitZeroDenominatorFactored]
  ring

private theorem rawOrbitOneNumerator_factorization (r s : ℚ) :
    rawOrbitOneNumerator r s = rawOrbitOneNumeratorFactored r s := by
  simp only [rawOrbitOneNumerator, rawOrbitOneNumeratorChunk0,
    rawOrbitOneNumeratorChunk1, rawOrbitOneNumeratorChunk2,
    rawOrbitOneNumeratorChunk3, rawOrbitOneNumeratorChunk4,
    rawOrbitOneNumeratorChunk5, rawOrbitOneNumeratorFactored]
  ring

private theorem rawOrbitOneDenominator_factorization (r s : ℚ) :
    rawOrbitOneDenominator r s = rawOrbitOneDenominatorFactored r s := by
  simp only [rawOrbitOneDenominator, rawOrbitOneDenominatorChunk0,
    rawOrbitOneDenominatorChunk1, rawOrbitOneDenominatorChunk2,
    rawOrbitOneDenominatorChunk3, rawOrbitOneDenominatorChunk4,
    rawOrbitOneDenominatorChunk5, rawOrbitOneDenominatorFactored]
  ring

private theorem rawOrbitZeroDenominatorMultiplier_factorization (r s : ℚ) :
    rawOrbitZeroDenominatorMultiplier r s = rawOrbitZeroDenominatorMultiplierFactored r s := by
  simp only [rawOrbitZeroDenominatorMultiplier,
    rawOrbitZeroDenominatorMultiplierChunk0,
    rawOrbitZeroDenominatorMultiplierChunk1,
    rawOrbitZeroDenominatorMultiplierChunk2,
    rawOrbitZeroDenominatorMultiplierChunk3,
    rawOrbitZeroDenominatorMultiplierChunk4,
    rawOrbitZeroDenominatorMultiplierFactored]
  ring

private theorem rawOrbitOneDenominatorMultiplier_factorization (r s : ℚ) :
    rawOrbitOneDenominatorMultiplier r s = rawOrbitOneDenominatorMultiplierFactored r s := by
  simp only [rawOrbitOneDenominatorMultiplier,
    rawOrbitOneDenominatorMultiplierChunk0,
    rawOrbitOneDenominatorMultiplierFactored]

private theorem rawUnitOneNumerator_factorization (r s : ℚ) :
    rawUnitOneNumerator r s = rawUnitOneNumeratorFactored r s := by
  simp only [rawUnitOneNumerator, rawUnitOneNumeratorCoefficient0,
    rawUnitOneNumeratorCoefficient1, rawUnitOneNumeratorCoefficient2,
    rawUnitOneNumeratorCoefficient3, rawUnitOneNumeratorCoefficient4,
    rawUnitOneNumeratorCoefficient5, rawUnitOneNumeratorCoefficient6,
    rawUnitOneNumeratorCoefficient7, rawUnitOneNumeratorFactored]
  all_goals ring

private theorem rawUnitFourNumerator_factorization (r s : ℚ) :
    rawUnitFourNumerator r s = rawUnitFourNumeratorFactored r s := by
  simp only [rawUnitFourNumerator, rawUnitFourNumeratorCoefficient0,
    rawUnitFourNumeratorCoefficient1, rawUnitFourNumeratorCoefficient2,
    rawUnitFourNumeratorCoefficient3, rawUnitFourNumeratorCoefficient4,
    rawUnitFourNumeratorCoefficient5, rawUnitFourNumeratorCoefficient6,
    rawUnitFourNumeratorCoefficient7, rawUnitFourNumeratorCoefficient8,
    rawUnitFourNumeratorFactored]
  all_goals ring

private theorem rawUnitTwoNumerator_factorization (r s : ℚ) :
    rawUnitTwoNumerator r s = rawUnitTwoNumeratorFactored r s := by
  simp only [rawUnitTwoNumerator, rawUnitTwoNumeratorCoefficient0,
    rawUnitTwoNumeratorCoefficient1, rawUnitTwoNumeratorCoefficient2,
    rawUnitTwoNumeratorCoefficient3, rawUnitTwoNumeratorCoefficient4,
    rawUnitTwoNumeratorCoefficient5, rawUnitTwoNumeratorCoefficient6,
    rawUnitTwoNumeratorCoefficient7, rawUnitTwoNumeratorFactored]
  all_goals ring

private theorem rawUnitEightNumerator_factorization (r s : ℚ) :
    rawUnitEightNumerator r s = rawUnitEightNumeratorFactored r s := by
  simp only [rawUnitEightNumerator, rawUnitEightNumeratorCoefficient0,
    rawUnitEightNumeratorCoefficient1, rawUnitEightNumeratorCoefficient2,
    rawUnitEightNumeratorCoefficient3, rawUnitEightNumeratorFactored]
  all_goals ring

theorem rawOrbitZeroDenominator_product_factorization (r s : ℚ) :
    rawUnitOneDenominator r s * rawUnitFourDenominator r s =
      rawOrbitZeroDenominator r s *
        rawOrbitZeroDenominatorMultiplier r s := by
  rw [rawUnitOneDenominator_factorization,
    rawUnitFourDenominator_factorization,
    rawOrbitZeroDenominator_factorization,
    rawOrbitZeroDenominatorMultiplier_factorization]
  simp only [rawOrbitZeroDenominatorFactored,
    rawOrbitZeroDenominatorMultiplierFactored, rawUnitFourPoleFactor]
  ring

theorem rawOrbitOneDenominator_product_factorization (r s : ℚ) :
    rawUnitTwoDenominator r s * rawUnitEightDenominator r s =
      rawOrbitOneDenominator r s *
        rawOrbitOneDenominatorMultiplier r s := by
  rw [rawUnitTwoDenominator_factorization,
    rawUnitEightDenominator_factorization,
    rawOrbitOneDenominator_factorization,
    rawOrbitOneDenominatorMultiplier_factorization]
  simp only [rawOrbitOneDenominatorFactored,
    rawOrbitOneDenominatorMultiplierFactored,
    rawUnitTwoPoleFactor, rawUnitTwoPoleFactorCoefficient0,
    rawUnitTwoPoleFactorCoefficient1, rawUnitTwoPoleFactorCoefficient2,
    rawUnitTwoPoleFactorCoefficient3, rawUnitTwoPoleFactorCoefficient4,
    rawUnitTwoPoleFactorCoefficient5, rawUnitTwoPoleFactorCoefficient6,
    rawUnitEightPoleFactor, rawUnitEightPoleFactorCoefficient0,
    rawUnitEightPoleFactorCoefficient1, rawUnitEightPoleFactorCoefficient2,
    rawUnitEightPoleFactorCoefficient3]
  ring

theorem rawOrbitZero_spec (r s : ℚ)
    (hOne : rawUnitOneDenominator r s ≠ 0)
    (hFour : rawUnitFourDenominator r s ≠ 0) :
    (rawUnitOneNumerator r s / rawUnitOneDenominator r s) *
        (rawUnitFourNumerator r s / rawUnitFourDenominator r s) =
      rawOrbitZeroNumerator r s / rawOrbitZeroDenominator r s := by
  have hproduct := mul_ne_zero hOne hFour
  rw [rawOrbitZeroDenominator_product_factorization] at hproduct
  have hden := (mul_ne_zero_iff.mp hproduct).1
  field_simp [hOne, hFour, hden]
  rw [rawUnitOneNumerator_factorization,
    rawUnitFourNumerator_factorization,
    rawUnitOneDenominator_factorization,
    rawUnitFourDenominator_factorization,
    rawOrbitZeroNumerator_factorization,
    rawOrbitZeroDenominator_factorization]
  simp only [rawUnitOneNumeratorFactored,
    rawUnitFourNumeratorFactored, rawOrbitZeroNumeratorFactored,
    rawOrbitZeroDenominatorFactored, rawUnitFourPoleFactor]
  ring

theorem rawOrbitOne_spec (r s : ℚ)
    (hTwo : rawUnitTwoDenominator r s ≠ 0)
    (hEight : rawUnitEightDenominator r s ≠ 0) :
    (rawUnitTwoNumerator r s / rawUnitTwoDenominator r s) *
        (rawUnitEightNumerator r s / rawUnitEightDenominator r s) =
      rawOrbitOneNumerator r s / rawOrbitOneDenominator r s := by
  have hproduct := mul_ne_zero hTwo hEight
  rw [rawOrbitOneDenominator_product_factorization] at hproduct
  have hden := (mul_ne_zero_iff.mp hproduct).1
  field_simp [hTwo, hEight, hden]
  rw [rawUnitTwoNumerator_factorization,
    rawUnitEightNumerator_factorization,
    rawUnitTwoDenominator_factorization,
    rawUnitEightDenominator_factorization,
    rawOrbitOneNumerator_factorization,
    rawOrbitOneDenominator_factorization]
  simp only [rawUnitTwoNumeratorFactored,
    rawUnitEightNumeratorFactored, rawOrbitOneNumeratorFactored,
    rawOrbitOneDenominatorFactored,
    rawUnitTwoPoleFactor, rawUnitTwoPoleFactorCoefficient0,
    rawUnitTwoPoleFactorCoefficient1, rawUnitTwoPoleFactorCoefficient2,
    rawUnitTwoPoleFactorCoefficient3, rawUnitTwoPoleFactorCoefficient4,
    rawUnitTwoPoleFactorCoefficient5, rawUnitTwoPoleFactorCoefficient6,
    rawUnitEightPoleFactor, rawUnitEightPoleFactorCoefficient0,
    rawUnitEightPoleFactorCoefficient1, rawUnitEightPoleFactorCoefficient2,
    rawUnitEightPoleFactorCoefficient3]
  ring


private def rawBetaChunk0 (r s : ℚ) : ℚ :=
  - r * s ^ 3
    - r ^ 2 * s
    + 3 * r ^ 2 * s ^ 2
    - r ^ 2 * s ^ 3

def rawBeta (r s : ℚ) : ℚ :=
  rawBetaChunk0 r s

private def rawLambdaNumeratorChunk0 (r s : ℚ) : ℚ :=
  - s ^ 2
    - s ^ 3
    + 5 * r * s ^ 2
    - 2 * r * s ^ 3
    - 2 * r ^ 2 * s
    + r ^ 2 * s ^ 2

def rawLambdaNumerator (r s : ℚ) : ℚ :=
  rawLambdaNumeratorChunk0 r s

private def rawAlphaNumeratorChunk0 (r s : ℚ) : ℚ :=
  r * s ^ 2
    - r * s ^ 3
    + r * s ^ 4
    - r * s ^ 5
    + r * s ^ 6
    - 5 * r ^ 2 * s ^ 2
    + 5 * r ^ 2 * s ^ 3
    - 4 * r ^ 2 * s ^ 5
    + r ^ 2 * s ^ 6
    + 10 * r ^ 3 * s ^ 2
    - 19 * r ^ 3 * s ^ 3
    + 18 * r ^ 3 * s ^ 4
    - 7 * r ^ 3 * s ^ 5
    + r ^ 3 * s ^ 6
    - r ^ 4 * s

def rawAlphaNumerator (r s : ℚ) : ℚ :=
  rawAlphaNumeratorChunk0 r s

private def rawPointNumeratorChunk0 (r s : ℚ) : ℚ :=
  - s ^ 3
    + r * s
    - 3 * r * s ^ 2
    + 16 * r * s ^ 3
    - 15 * r * s ^ 4
    + 10 * r * s ^ 5
    - 6 * r * s ^ 6
    + 3 * r * s ^ 7
    - r * s ^ 8
    - 5 * r ^ 2 * s
    + 10 * r ^ 2 * s ^ 2
    - 50 * r ^ 2 * s ^ 3
    + 60 * r ^ 2 * s ^ 4
    - 35 * r ^ 2 * s ^ 5
    + 10 * r ^ 2 * s ^ 6
    + 10 * r ^ 3 * s

private def rawPointNumeratorChunk1 (r s : ℚ) : ℚ :=
  - 9 * r ^ 3 * s ^ 2
    + 51 * r ^ 3 * s ^ 3
    - 85 * r ^ 3 * s ^ 4
    + 70 * r ^ 3 * s ^ 5
    - 35 * r ^ 3 * s ^ 6
    + 9 * r ^ 3 * s ^ 7
    - r ^ 3 * s ^ 8
    - 10 * r ^ 4 * s
    + 5 * r ^ 4 * s ^ 3
    + 5 * r ^ 5 * s
    - 5 * r ^ 5 * s ^ 2
    + r ^ 5 * s ^ 3

def rawPointNumerator (r s : ℚ) : ℚ :=
  rawPointNumeratorChunk0 r s +
    rawPointNumeratorChunk1 r s

def rawTangentFactor (r s : ℚ) : ℚ :=
  r * s ^ 2 - 3 * r * s + r + s ^ 2

def rawLambda (r s : ℚ) : ℚ :=
  rawLambdaNumerator r s / rawTangentFactor r s

def rawAlpha (r s : ℚ) : ℚ :=
  rawAlphaNumerator r s / rawTangentFactor r s ^ 2

def rawPointDenominator (r s : ℚ) : ℚ :=
  rawTangentFactor r s ^ 4

private theorem raw_sub_ne_zero (r s : ℚ) (hs : s ≠ 0)
    (hr : r - 1 ≠ 0) :
    r * s * (r - 1) - s * (r - 1) ≠ 0 := by
  rw [show r * s * (r - 1) - s * (r - 1) = s * (r - 1) ^ 2 by ring]
  exact mul_ne_zero hs (pow_ne_zero 2 hr)

private theorem rawBeta_factorization (r s : ℚ) :
    rawBeta r s = -(r * s * rawTangentFactor r s) := by
  simp only [rawBeta, rawBetaChunk0, rawTangentFactor]
  ring

private theorem rawBeta_ne_zero (r s : ℚ) (hr0 : r ≠ 0) (hs : s ≠ 0)
    (hK : rawTangentFactor r s ≠ 0) :
    rawBeta r s ≠ 0 := by
  rw [rawBeta_factorization]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hr0 hs) hK)

theorem pointTateBeta_raw (r s : ℚ) (hs : s ≠ 0)
    (hr : r - 1 ≠ 0) :
    pointTateBeta
        (tateNormalCurve (r * s * (r - 1)) (s * (r - 1)))
        (tateFiveX (r * s * (r - 1)) (s * (r - 1)))
        (tateFiveY (r * s * (r - 1)) (s * (r - 1))) =
      rawBeta r s := by
  simp only [pointTateBeta, tateNormalCurve_a₁, tateNormalCurve_a₃,
    tateFiveX, tateFiveY, rawBeta, rawBetaChunk0]
  field_simp [raw_sub_ne_zero r s hs hr]
  ring

theorem pointTateLambda_raw (r s : ℚ) (hr0 : r ≠ 0) (hs : s ≠ 0)
    (hr : r - 1 ≠ 0)
    (hK : rawTangentFactor r s ≠ 0) :
    pointTateLambda
        (tateNormalCurve (r * s * (r - 1)) (s * (r - 1)))
        (tateFiveX (r * s * (r - 1)) (s * (r - 1)))
        (tateFiveY (r * s * (r - 1)) (s * (r - 1))) =
      rawLambda r s := by
  have hSub := raw_sub_ne_zero r s hs hr
  have hBeta := rawBeta_ne_zero r s hr0 hs hK
  rw [pointTateLambda, pointTateBeta_raw r s hs hr]
  simp only [tateNormalCurve_a₁, tateNormalCurve_a₂,
    tateNormalCurve_a₄, tateFiveX, tateFiveY, rawLambda]
  field_simp [hSub, hBeta, hK]
  simp only [rawBeta, rawBetaChunk0, rawLambdaNumerator,
    rawLambdaNumeratorChunk0, rawTangentFactor]
  ring

theorem pointTateAlpha_raw (r s : ℚ) (hr0 : r ≠ 0) (hs : s ≠ 0)
    (hr : r - 1 ≠ 0)
    (hK : rawTangentFactor r s ≠ 0) :
    pointTateAlpha
        (tateNormalCurve (r * s * (r - 1)) (s * (r - 1)))
        (tateFiveX (r * s * (r - 1)) (s * (r - 1)))
        (tateFiveY (r * s * (r - 1)) (s * (r - 1))) =
      rawAlpha r s := by
  have hSub := raw_sub_ne_zero r s hs hr
  rw [pointTateAlpha, pointTateLambda_raw r s hr0 hs hr hK]
  simp only [tateNormalCurve_a₁, tateNormalCurve_a₂, tateFiveX,
    rawLambda, rawAlpha]
  field_simp [hSub, hK]
  simp only [rawLambdaNumerator, rawLambdaNumeratorChunk0,
    rawAlphaNumerator, rawAlphaNumeratorChunk0, rawTangentFactor]
  ring

theorem pointTateC_raw (r s : ℚ) (hr0 : r ≠ 0) (hs : s ≠ 0)
    (hr : r - 1 ≠ 0)
    (hK : rawTangentFactor r s ≠ 0) :
    pointTateC
        (tateNormalCurve (r * s * (r - 1)) (s * (r - 1)))
        (tateFiveX (r * s * (r - 1)) (s * (r - 1)))
        (tateFiveY (r * s * (r - 1)) (s * (r - 1))) =
      rawPointNumerator r s / rawPointDenominator r s := by
  have hBeta := rawBeta_ne_zero r s hr0 hs hK
  rw [pointTateC, pointTateBeta_raw r s hs hr,
    pointTateAlpha_raw r s hr0 hs hr hK,
    pointTateLambda_raw r s hr0 hs hr hK]
  simp only [tateNormalCurve_a₁, rawLambda, rawAlpha,
    rawPointDenominator]
  field_simp [hBeta, hK]
  simp only [rawBeta, rawBetaChunk0,
    rawLambdaNumerator, rawLambdaNumeratorChunk0,
    rawAlphaNumerator, rawAlphaNumeratorChunk0,
    rawPointNumerator, rawPointNumeratorChunk0,
    rawPointNumeratorChunk1, rawTangentFactor]
  ring


theorem rawOrbitZeroDenominator_ne_zero (r s : ℚ)
    (hOne : rawUnitOneDenominator r s ≠ 0)
    (hFour : rawUnitFourDenominator r s ≠ 0) :
    rawOrbitZeroDenominator r s ≠ 0 := by
  have hproduct := mul_ne_zero hOne hFour
  rw [rawOrbitZeroDenominator_product_factorization] at hproduct
  exact (mul_ne_zero_iff.mp hproduct).1

theorem rawOrbitOneDenominator_ne_zero (r s : ℚ)
    (hTwo : rawUnitTwoDenominator r s ≠ 0)
    (hEight : rawUnitEightDenominator r s ≠ 0) :
    rawOrbitOneDenominator r s ≠ 0 := by
  have hproduct := mul_ne_zero hTwo hEight
  rw [rawOrbitOneDenominator_product_factorization] at hproduct
  exact (mul_ne_zero_iff.mp hproduct).1

theorem rawOrbitZeroNumerator_eq_table (r s : ℚ) :
    rawOrbitZeroNumerator r s = evaluateTableSum aTable r s := by
  norm_num [evaluateTableSum, aTable, aTableChunk0, tableCoefficient,
    rawCoefficient, rawOrbitZeroNumerator, rawOrbitZeroNumeratorChunk0,
    rawOrbitZeroNumeratorChunk1, rawOrbitZeroNumeratorChunk2,
    Finset.sum_range_succ]; ring

theorem rawOrbitZeroDenominator_eq_table (r s : ℚ) :
    rawOrbitZeroDenominator r s = evaluateTableSum bTable r s := by
  norm_num [evaluateTableSum, bTable, bTableChunk0, tableCoefficient,
    rawCoefficient, rawOrbitZeroDenominator,
    rawOrbitZeroDenominatorChunk0, rawOrbitZeroDenominatorChunk1,
    rawOrbitZeroDenominatorChunk2, Finset.sum_range_succ]; ring

theorem rawOrbitOneNumerator_eq_table (r s : ℚ) :
    rawOrbitOneNumerator r s = evaluateTableSum cTable r s := by
  norm_num [evaluateTableSum, cTable, cTableChunk0, cTableChunk1,
    tableCoefficient, rawCoefficient, rawOrbitOneNumerator,
    rawOrbitOneNumeratorChunk0, rawOrbitOneNumeratorChunk1,
    rawOrbitOneNumeratorChunk2, rawOrbitOneNumeratorChunk3,
    rawOrbitOneNumeratorChunk4, rawOrbitOneNumeratorChunk5,
    Finset.sum_range_succ]; ring

theorem rawOrbitOneDenominator_eq_table (r s : ℚ) :
    rawOrbitOneDenominator r s = evaluateTableSum dTable r s := by
  norm_num [evaluateTableSum, dTable, dTableChunk0, dTableChunk1,
    tableCoefficient, rawCoefficient, rawOrbitOneDenominator,
    rawOrbitOneDenominatorChunk0, rawOrbitOneDenominatorChunk1,
    rawOrbitOneDenominatorChunk2, rawOrbitOneDenominatorChunk3,
    rawOrbitOneDenominatorChunk4, rawOrbitOneDenominatorChunk5,
    Finset.sum_range_succ]; ring

theorem curveTable_evaluation (r s : ℚ) :
    evaluateTableSum curveTable r s = sutherlandPolynomial r s := by
  norm_num [evaluateTableSum, curveTable, curveTableChunk0, curveTableChunk1,
    tableCoefficient, rawCoefficient, sutherlandPolynomial,
    sutherlandPolynomialCoefficient0, sutherlandPolynomialCoefficient1,
    sutherlandPolynomialCoefficient2, sutherlandPolynomialCoefficient3,
    sutherlandPolynomialCoefficient4, sutherlandPolynomialCoefficient5,
    sutherlandPolynomialCoefficient6, sutherlandPolynomialCoefficient7,
    sutherlandPolynomialCoefficient8, sutherlandPolynomialCoefficient9,
    sutherlandPolynomialCoefficient10, Finset.sum_range_succ]; ring

theorem rawPointNumerator_eq_table (r s : ℚ) :
    rawPointNumerator r s = evaluateTableSum pointNumeratorTable r s := by
  norm_num [evaluateTableSum, pointNumeratorTable, pointNumeratorTableChunk0,
    tableCoefficient, rawCoefficient, rawPointNumerator,
    rawPointNumeratorChunk0, rawPointNumeratorChunk1,
    Finset.sum_range_succ]; ring

theorem rawPointDenominator_eq_table (r s : ℚ) :
    rawPointDenominator r s = evaluateTableSum pointDenominatorTable r s := by
  norm_num [evaluateTableSum, pointDenominatorTable,
    pointDenominatorTableChunk0, tableCoefficient, rawCoefficient,
    rawPointDenominator, rawTangentFactor, Finset.sum_range_succ]; ring

theorem reducedDenominator_evaluation (r s : ℚ) :
    evaluateTableSum reducedDenominatorTable r s =
      s ^ 4 * (s - 1) ^ 31 := by
  norm_num [evaluateTableSum, reducedDenominatorTable,
    reducedDenominatorTableChunk0, tableCoefficient, rawCoefficient,
    Finset.sum_range_succ]; ring

private theorem pairParameter_eq_of_cross_mul
    (A B C D N M : ℚ)
    (hB : B ≠ 0) (hD : D ≠ 0) (hM : M ≠ 0)
    (hpair : orderTwentyFiveOrbitPairDenominator (A / B) (C / D) ≠ 0)
    (hcross :
      (2 * B ^ 2 * D - 2 * A * C * B - A ^ 2 * D + C * B ^ 2) * M =
        (B * (B * D - A * D - A * C)) * N) :
    orderTwentyFiveOrbitPairParameter (A / B) (C / D) = N / M := by
  rw [orderTwentyFiveOrbitPairParameter, div_eq_iff hpair]
  simp only [orderTwentyFiveOrbitPairDenominator]
  field_simp [hB, hD, hM]
  linear_combination hcross

private theorem degeneracy_eq_of_cross_mul
    (P R T N M : ℚ)
    (hP : P ≠ 0) (hR : R ≠ 0) (hM : M ≠ 0)
    (hT : T = P ^ 2 - 11 * P * R - R ^ 2)
    (hbridge :
      T * M ^ 5 + P * R *
        (N ^ 5 - 5 * N ^ 4 * M + 15 * N ^ 3 * M ^ 2 -
          25 * N ^ 2 * M ^ 3 + 25 * N * M ^ 4) = 0) :
    orderFiveXZeroParameter (P / R) =
      orderTwentyFiveSecondDegeneracyParameter (-(N / M)) := by
  simp only [orderFiveXZeroParameter,
    orderTwentyFiveSecondDegeneracyParameter,
    orderTwentyFiveHauptmodulDenominator]
  field_simp [hP, hR, hM]
  rw [hT] at hbridge
  linear_combination hbridge

private theorem pairParameter_table_eq_reduced
    (r s : ℚ)
    (hcurve : evaluateTableSum curveTable r s = 0)
    (hB : evaluateTableSum bTable r s ≠ 0)
    (hD : evaluateTableSum dTable r s ≠ 0)
    (hM : evaluateTableSum reducedDenominatorTable r s ≠ 0)
    (hpair : orderTwentyFiveOrbitPairDenominator
      (evaluateTableSum aTable r s / evaluateTableSum bTable r s)
      (evaluateTableSum cTable r s / evaluateTableSum dTable r s) ≠ 0) :
    orderTwentyFiveOrbitPairParameter
        (evaluateTableSum aTable r s / evaluateTableSum bTable r s)
        (evaluateTableSum cTable r s / evaluateTableSum dTable r s) =
      evaluateTableSum reducedNumeratorTable r s /
        evaluateTableSum reducedDenominatorTable r s := by
  let A := evaluateTableSum aTable r s
  let B := evaluateTableSum bTable r s
  let C := evaluateTableSum cTable r s
  let D := evaluateTableSum dTable r s
  let A2 := evaluateTableSum aSquaredTable r s
  let B2 := evaluateTableSum bSquaredTable r s
  let AC := evaluateTableSum acTable r s
  let BD := evaluateTableSum bdTable r s
  let AD := evaluateTableSum adTable r s
  let denominatorInner := evaluateTableSum pairDenominatorInnerTable r s
  let pairNumerator := evaluateTableSum pairNumeratorTable r s
  let pairDenominator := evaluateTableSum pairDenominatorTable r s
  let N := evaluateTableSum reducedNumeratorTable r s
  let M := evaluateTableSum reducedDenominatorTable r s
  have hA2 := aSquared_evaluation r s
  have hB2 := bSquared_evaluation r s
  have hAC := ac_evaluation r s
  have hBD := bd_evaluation r s
  have hAD := ad_evaluation r s
  simp only [aSquaredLeftExpression, aSquaredRightExpression,
    bSquaredLeftExpression, bSquaredRightExpression,
    acLeftExpression, acRightExpression, bdLeftExpression,
    bdRightExpression, adLeftExpression, adRightExpression,
    evaluateExpression] at hA2 hB2 hAC hBD hAD
  change A2 = A * A at hA2
  change B2 = B * B at hB2
  change AC = A * C at hAC
  change BD = B * D at hBD
  change AD = A * D at hAD
  have hInner := pairDenominatorInner_evaluation r s
  simp only [pairDenominatorInnerLeftExpression,
    pairDenominatorInnerRightExpression, evaluateExpression] at hInner
  change denominatorInner = BD + -AD + -AC at hInner
  have hNumerator := pairNumerator_evaluation r s
  norm_num [pairNumeratorLeftExpression, pairNumeratorRightExpression,
    evaluateExpression] at hNumerator
  change pairNumerator =
    2 * (B2 * D) + -(2 * (AC * B)) + -(A2 * D) + C * B2 at hNumerator
  have hDenominator := pairDenominator_evaluation r s
  simp only [pairDenominatorLeftExpression, pairDenominatorRightExpression,
    evaluateExpression] at hDenominator
  change pairDenominator = B * denominatorInner at hDenominator
  have hComparison := pairComparison_evaluation r s
  simp only [pairComparisonLeftExpression, pairComparisonRightExpression,
    evaluateExpression] at hComparison
  change pairNumerator * M + -(pairDenominator * N) =
    evaluateTableSum curveTable r s *
      evaluateTableSum pairQuotientTable r s at hComparison
  rw [hcurve] at hComparison
  have hCross :
      (2 * B ^ 2 * D - 2 * A * C * B - A ^ 2 * D + C * B ^ 2) * M =
        (B * (B * D - A * D - A * C)) * N := by
    rw [hNumerator, hDenominator, hInner, hA2, hB2, hAC, hBD, hAD]
      at hComparison
    linear_combination hComparison
  exact pairParameter_eq_of_cross_mul A B C D N M hB hD hM hpair hCross

/-- On the raw order-twenty-five curve, the first two orbit units recover the
reduced Hauptmodul used by the final degeneracy certificate. -/
theorem rawPairParameter_eq_reduced
    (r s : ℚ) (hs : s ≠ 0) (hs1 : s - 1 ≠ 0)
    (hcurve : sutherlandPolynomial r s = 0)
    (hB : rawOrbitZeroDenominator r s ≠ 0)
    (hD : rawOrbitOneDenominator r s ≠ 0)
    (hpair : orderTwentyFiveOrbitPairDenominator
      (rawOrbitZeroNumerator r s / rawOrbitZeroDenominator r s)
      (rawOrbitOneNumerator r s / rawOrbitOneDenominator r s) ≠ 0) :
    orderTwentyFiveOrbitPairParameter
        (rawOrbitZeroNumerator r s / rawOrbitZeroDenominator r s)
        (rawOrbitOneNumerator r s / rawOrbitOneDenominator r s) =
      evaluateTableSum reducedNumeratorTable r s /
        evaluateTableSum reducedDenominatorTable r s := by
  have hM : evaluateTableSum reducedDenominatorTable r s ≠ 0 := by
    rw [reducedDenominator_evaluation]
    exact mul_ne_zero (pow_ne_zero 4 hs) (pow_ne_zero 31 hs1)
  have h := pairParameter_table_eq_reduced r s
    ((curveTable_evaluation r s).trans hcurve) ?_ ?_ hM ?_
  · simpa only [rawOrbitZeroNumerator_eq_table,
      rawOrbitZeroDenominator_eq_table, rawOrbitOneNumerator_eq_table,
      rawOrbitOneDenominator_eq_table] using h
  · simpa only [← rawOrbitZeroDenominator_eq_table] using hB
  · simpa only [← rawOrbitOneDenominator_eq_table] using hD
  · simpa only [← rawOrbitZeroNumerator_eq_table,
      ← rawOrbitZeroDenominator_eq_table,
      ← rawOrbitOneNumerator_eq_table,
      ← rawOrbitOneDenominator_eq_table] using hpair

private theorem pointParameter_table_eq_reduced
    (r s : ℚ)
    (hcurve : evaluateTableSum curveTable r s = 0)
    (hP : evaluateTableSum pointNumeratorTable r s ≠ 0)
    (hR : evaluateTableSum pointDenominatorTable r s ≠ 0)
    (hM : evaluateTableSum reducedDenominatorTable r s ≠ 0) :
    orderFiveXZeroParameter
        (evaluateTableSum pointNumeratorTable r s /
          evaluateTableSum pointDenominatorTable r s) =
      orderTwentyFiveSecondDegeneracyParameter
        (-(evaluateTableSum reducedNumeratorTable r s /
          evaluateTableSum reducedDenominatorTable r s)) := by
  let F := evaluateTableSum curveTable r s
  let N := evaluateTableSum reducedNumeratorTable r s
  let M := evaluateTableSum reducedDenominatorTable r s
  let R2 := evaluateTableSum powerTwoRemainderTable r s
  let R3 := evaluateTableSum powerThreeRemainderTable r s
  let R4 := evaluateTableSum powerFourRemainderTable r s
  let R5 := evaluateTableSum powerFiveRemainderTable r s
  let T := evaluateTableSum tangentNumeratorTable r s
  let Tr := evaluateTableSum tangentRemainderTable r s
  let M2 := evaluateTableSum denominatorSquareTable r s
  let M3 := evaluateTableSum denominatorCubeTable r s
  let M4 := evaluateTableSum denominatorFourthTable r s
  let M5 := evaluateTableSum denominatorFifthTable r s
  let P := evaluateTableSum pointNumeratorTable r s
  let R := evaluateTableSum pointDenominatorTable r s
  let P2 := evaluateTableSum pointNumeratorSquareTable r s
  let PR := evaluateTableSum pointProductTable r s
  let Rsquare := evaluateTableSum pointDenominatorSquareTable r s
  let R4M := evaluateTableSum bridgeR4MTable r s
  let R3M := evaluateTableSum bridgeR3MTable r s
  let R3M2 := evaluateTableSum bridgeR3M2Table r s
  let R2M := evaluateTableSum bridgeR2MTable r s
  let R2M2 := evaluateTableSum bridgeR2M2Table r s
  let R2M3 := evaluateTableSum bridgeR2M3Table r s
  let NM := evaluateTableSum bridgeNMTable r s
  let NM2 := evaluateTableSum bridgeNM2Table r s
  let NM3 := evaluateTableSum bridgeNM3Table r s
  let NM4 := evaluateTableSum bridgeNM4Table r s
  let bridgeInner := evaluateTableSum bridgeInnerTable r s
  have hPowerTwo := powerTwoReduction_evaluation r s
  have hPowerThree := powerThreeReduction_evaluation r s
  have hPowerFour := powerFourReduction_evaluation r s
  have hPowerFive := powerFiveReduction_evaluation r s
  simp only [powerTwoReductionLeftExpression,
    powerTwoReductionRightExpression, powerThreeReductionLeftExpression,
    powerThreeReductionRightExpression, powerFourReductionLeftExpression,
    powerFourReductionRightExpression, powerFiveReductionLeftExpression,
    powerFiveReductionRightExpression, evaluateExpression]
    at hPowerTwo hPowerThree hPowerFour hPowerFive
  change N * N = F * evaluateTableSum powerTwoQuotientTable r s + R2 at hPowerTwo
  change N * R2 = F * evaluateTableSum powerThreeQuotientTable r s + R3 at hPowerThree
  change N * R3 = F * evaluateTableSum powerFourQuotientTable r s + R4 at hPowerFour
  change N * R4 = F * evaluateTableSum powerFiveQuotientTable r s + R5 at hPowerFive
  change F = 0 at hcurve
  rw [hcurve] at hPowerTwo hPowerThree hPowerFour hPowerFive
  norm_num at hPowerTwo hPowerThree hPowerFour hPowerFive
  have hR2 : R2 = N ^ 2 := by
    calc
      R2 = N * N := hPowerTwo.symm
      _ = N ^ 2 := by ring
  have hR3 : R3 = N ^ 3 := by
    calc
      R3 = N * R2 := hPowerThree.symm
      _ = N ^ 3 := by rw [hR2]; ring
  have hR4 : R4 = N ^ 4 := by
    calc
      R4 = N * R3 := hPowerFour.symm
      _ = N ^ 4 := by rw [hR3]; ring
  have hR5 : R5 = N ^ 5 := by
    calc
      R5 = N * R4 := hPowerFive.symm
      _ = N ^ 5 := by rw [hR4]; ring
  have hTangentReduction := tangentReduction_evaluation r s
  simp only [tangentReductionLeftExpression, tangentReductionRightExpression,
    evaluateExpression] at hTangentReduction
  change T = F * evaluateTableSum tangentQuotientTable r s + Tr at hTangentReduction
  rw [hcurve] at hTangentReduction
  norm_num at hTangentReduction
  have hTr : Tr = T := hTangentReduction.symm
  have hM2 := denominatorSquare_evaluation r s
  have hM3 := denominatorCube_evaluation r s
  have hM4 := denominatorFourth_evaluation r s
  have hM5 := denominatorFifth_evaluation r s
  simp only [denominatorSquareLeftExpression,
    denominatorSquareRightExpression, denominatorCubeLeftExpression,
    denominatorCubeRightExpression, denominatorFourthLeftExpression,
    denominatorFourthRightExpression, denominatorFifthLeftExpression,
    denominatorFifthRightExpression, evaluateExpression] at hM2 hM3 hM4 hM5
  change M2 = M * M at hM2
  change M3 = M * M2 at hM3
  change M4 = M * M3 at hM4
  change M5 = M * M4 at hM5
  have hM2Power : M2 = M ^ 2 := by rw [hM2]; ring
  have hM3Power : M3 = M ^ 3 := by rw [hM3, hM2Power]; ring
  have hM4Power : M4 = M ^ 4 := by rw [hM4, hM3Power]; ring
  have hM5Power : M5 = M ^ 5 := by rw [hM5, hM4Power]; ring
  have hP2 := pointNumeratorSquare_evaluation r s
  have hPR := pointProduct_evaluation r s
  have hRsquare := pointDenominatorSquare_evaluation r s
  simp only [pointNumeratorSquareLeftExpression,
    pointNumeratorSquareRightExpression, pointProductLeftExpression,
    pointProductRightExpression, pointDenominatorSquareLeftExpression,
    pointDenominatorSquareRightExpression, evaluateExpression] at hP2 hPR hRsquare
  change P2 = P * P at hP2
  change PR = P * R at hPR
  change Rsquare = R * R at hRsquare
  have hT := tangentNumerator_evaluation r s
  norm_num [tangentNumeratorLeftExpression, tangentNumeratorRightExpression,
    evaluateExpression] at hT
  change T = P2 + -(11 * PR) + -Rsquare at hT
  have hTFormula : T = P ^ 2 - 11 * P * R - R ^ 2 := by
    rw [hT, hP2, hPR, hRsquare]
    ring
  have hR4M := bridgeR4M_evaluation r s
  have hR3M := bridgeR3M_evaluation r s
  have hR3M2 := bridgeR3M2_evaluation r s
  have hR2M := bridgeR2M_evaluation r s
  have hR2M2 := bridgeR2M2_evaluation r s
  have hR2M3 := bridgeR2M3_evaluation r s
  have hNM := bridgeNM_evaluation r s
  have hNM2 := bridgeNM2_evaluation r s
  have hNM3 := bridgeNM3_evaluation r s
  have hNM4 := bridgeNM4_evaluation r s
  simp only [bridgeR4MLeftExpression, bridgeR4MRightExpression,
    bridgeR3MLeftExpression, bridgeR3MRightExpression,
    bridgeR3M2LeftExpression, bridgeR3M2RightExpression,
    bridgeR2MLeftExpression, bridgeR2MRightExpression,
    bridgeR2M2LeftExpression, bridgeR2M2RightExpression,
    bridgeR2M3LeftExpression, bridgeR2M3RightExpression,
    bridgeNMLeftExpression, bridgeNMRightExpression,
    bridgeNM2LeftExpression, bridgeNM2RightExpression,
    bridgeNM3LeftExpression, bridgeNM3RightExpression,
    bridgeNM4LeftExpression, bridgeNM4RightExpression, evaluateExpression]
    at hR4M hR3M hR3M2 hR2M hR2M2 hR2M3 hNM hNM2 hNM3 hNM4
  change R4M = M * R4 at hR4M
  change R3M = M * R3 at hR3M
  change R3M2 = M * R3M at hR3M2
  change R2M = M * R2 at hR2M
  change R2M2 = M * R2M at hR2M2
  change R2M3 = M * R2M2 at hR2M3
  change NM = M * N at hNM
  change NM2 = M * NM at hNM2
  change NM3 = M * NM2 at hNM3
  change NM4 = M * NM3 at hNM4
  have hR4MValue : R4M = N ^ 4 * M := by rw [hR4M, hR4]; ring
  have hR3MValue : R3M = N ^ 3 * M := by rw [hR3M, hR3]; ring
  have hR3M2Value : R3M2 = N ^ 3 * M ^ 2 := by
    rw [hR3M2, hR3MValue]
    ring
  have hR2MValue : R2M = N ^ 2 * M := by rw [hR2M, hR2]; ring
  have hR2M2Value : R2M2 = N ^ 2 * M ^ 2 := by
    rw [hR2M2, hR2MValue]
    ring
  have hR2M3Value : R2M3 = N ^ 2 * M ^ 3 := by
    rw [hR2M3, hR2M2Value]
    ring
  have hNMValue : NM = N * M := by rw [hNM]; ring
  have hNM2Value : NM2 = N * M ^ 2 := by rw [hNM2, hNMValue]; ring
  have hNM3Value : NM3 = N * M ^ 3 := by rw [hNM3, hNM2Value]; ring
  have hNM4Value : NM4 = N * M ^ 4 := by rw [hNM4, hNM3Value]; ring
  have hBridgeInner := bridgeInner_evaluation r s
  norm_num [bridgeInnerLeftExpression, bridgeInnerRightExpression,
    evaluateExpression] at hBridgeInner
  change bridgeInner =
    R5 + -(5 * R4M) + 15 * R3M2 + -(25 * R2M3) + 25 * NM4 at hBridgeInner
  have hBridgeInnerValue : bridgeInner =
      N ^ 5 - 5 * N ^ 4 * M + 15 * N ^ 3 * M ^ 2 -
        25 * N ^ 2 * M ^ 3 + 25 * N * M ^ 4 := by
    rw [hBridgeInner, hR5, hR4MValue, hR3M2Value,
      hR2M3Value, hNM4Value]
    ring
  have hFinal := finalBridge_evaluation r s
  simp only [finalBridgeLeftExpression, finalBridgeRightExpression,
    evaluateExpression] at hFinal
  change Tr * M5 + PR * bridgeInner =
    F * evaluateTableSum finalQuotientTable r s at hFinal
  rw [hcurve] at hFinal
  norm_num at hFinal
  have hBridge :
      T * M ^ 5 + P * R *
        (N ^ 5 - 5 * N ^ 4 * M + 15 * N ^ 3 * M ^ 2 -
          25 * N ^ 2 * M ^ 3 + 25 * N * M ^ 4) = 0 := by
    rw [← hTr, ← hM5Power, ← hPR, ← hBridgeInnerValue]
    exact hFinal
  exact degeneracy_eq_of_cross_mul P R T N M hP hR hM hTFormula hBridge

/-- The normalized fifth-multiple Tate parameter has the second degeneracy
value of the reduced raw Hauptmodul. -/
theorem rawPointXZeroParameter_eq_reduced
    (r s : ℚ) (hs : s ≠ 0) (hs1 : s - 1 ≠ 0)
    (hK : rawTangentFactor r s ≠ 0)
    (hcurve : sutherlandPolynomial r s = 0)
    (hpoint : rawPointNumerator r s / rawPointDenominator r s ≠ 0) :
    orderFiveXZeroParameter
        (rawPointNumerator r s / rawPointDenominator r s) =
      orderTwentyFiveSecondDegeneracyParameter
        (-(evaluateTableSum reducedNumeratorTable r s /
          evaluateTableSum reducedDenominatorTable r s)) := by
  have hP : evaluateTableSum pointNumeratorTable r s ≠ 0 := by
    have hPraw := (div_ne_zero_iff.mp hpoint).1
    simpa only [← rawPointNumerator_eq_table] using hPraw
  have hRraw : rawPointDenominator r s ≠ 0 := by
    exact pow_ne_zero 4 hK
  have hR : evaluateTableSum pointDenominatorTable r s ≠ 0 := by
    simpa only [← rawPointDenominator_eq_table] using hRraw
  have hM : evaluateTableSum reducedDenominatorTable r s ≠ 0 := by
    rw [reducedDenominator_evaluation]
    exact mul_ne_zero (pow_ne_zero 4 hs) (pow_ne_zero 31 hs1)
  have h := pointParameter_table_eq_reduced r s
    ((curveTable_evaluation r s).trans hcurve) hP hR hM
  simpa only [rawPointNumerator_eq_table,
    rawPointDenominator_eq_table] using h


end MazurTorsion.Kubert.OrderTwentyFiveDegeneracyRawNormalization
