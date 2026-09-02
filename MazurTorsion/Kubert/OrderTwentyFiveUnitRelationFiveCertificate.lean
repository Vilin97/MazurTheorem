/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# An internal coefficient certificate for the order-25 unit relation

The polynomial tables below are exact division and convolution witnesses.
They remain private; the single internal theorem is consumed by the checked
actual-coordinate orbit proof in `OrderTwentyFiveNormalizedModel`.
-/

namespace MazurTorsion.Kubert.Internal

private def A (r s : ℚ) : ℚ :=
  r
  - s

private def B (_r s : ℚ) : ℚ :=
  s
  - 1

private def C (r s : ℚ) : ℚ :=
  r * s
  - 2 * r
  + 1

private def K (r s : ℚ) : ℚ :=
  r
  - s ^ 2
  + s
  - 1

private def D (r s : ℚ) : ℚ :=
  r ^ 2
  - r * s ^ 3
  + 3 * r * s ^ 2
  - 4 * r * s
  + s

private def E (r s : ℚ) : ℚ :=
  r ^ 2 * s
  - 3 * r ^ 2
  + r * s
  + 3 * r
  - s ^ 2
  - 1

private def G (r s : ℚ) : ℚ :=
  r * s ^ 2
  - 3 * r * s
  + r
  + s ^ 2

private def L (r s : ℚ) : ℚ :=
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

private def J (r s : ℚ) : ℚ :=
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

private def T (r s : ℚ) : ℚ :=
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

private def M (r s : ℚ) : ℚ :=
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

private def N (r s : ℚ) : ℚ :=
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

private def P6 (r s : ℚ) : ℚ :=
  D r s ^ 2 * A r s * K r s -
    C r s ^ 2 * s * B r s * G r s * E r s

private def P9 (r s : ℚ) : ℚ :=
  D r s ^ 3 * L r s - r * s * B r s ^ 3 * G r s * E r s ^ 3

private def y1 (r s : ℚ) : ℚ :=
  C r s * L r s * J r s / (r * B r s ^ 2 * K r s ^ 2 * E r s ^ 2)

private def y2 (r s : ℚ) : ℚ :=
  -(r * B r s ^ 3 * C r s * K r s * M r s) / (A r s ^ 2 * P6 r s)

private def y4 (r s : ℚ) : ℚ :=
  -(r * A r s * B r s * K r s ^ 2 * E r s * T r s) /
    (C r s * D r s ^ 2 * J r s)

private def y8 (r s : ℚ) : ℚ :=
  -(A r s * B r s * E r s) / L r s

private def y9 (r s : ℚ) : ℚ :=
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

private def F (r s : ℚ) : ℚ :=
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

private def term0 (r s : ℚ) : ℚ :=
  B r s ^ 3 * K r s ^ 2 * M r s ^ 2 * N r s * T r s * r

private def term0C0 (_s : ℚ) : ℚ :=
  0

private def term0C1 (s : ℚ) : ℚ :=
  -s ^ 19
  + 3 * s ^ 18
  - 5 * s ^ 17
  + 7 * s ^ 16
  - 9 * s ^ 15
  + 11 * s ^ 14
  - 11 * s ^ 13
  + 9 * s ^ 12
  - 7 * s ^ 11
  + 5 * s ^ 10
  - 3 * s ^ 9
  + s ^ 8

private def term0C2 (s : ℚ) : ℚ :=
  s ^ 23
  - 7 * s ^ 22
  + 26 * s ^ 21
  - 70 * s ^ 20
  + 146 * s ^ 19
  - 227 * s ^ 18
  + 303 * s ^ 17
  - 393 * s ^ 16
  + 485 * s ^ 15
  - 535 * s ^ 14
  + 497 * s ^ 13
  - 417 * s ^ 12
  + 340 * s ^ 11
  - 244 * s ^ 10
  + 133 * s ^ 9
  - 39 * s ^ 8
  + s ^ 7

private def term0C3 (s : ℚ) : ℚ :=
  s ^ 26
  - 9 * s ^ 25
  + 44 * s ^ 24
  - 151 * s ^ 23
  + 387 * s ^ 22
  - 785 * s ^ 21
  + 1329 * s ^ 20
  - 1938 * s ^ 19
  + 2633 * s ^ 18
  - 3867 * s ^ 17
  + 5740 * s ^ 16
  - 7478 * s ^ 15
  + 8259 * s ^ 14
  - 8055 * s ^ 13
  + 7592 * s ^ 12
  - 6675 * s ^ 11
  + 4725 * s ^ 10
  - 2321 * s ^ 9
  + 563 * s ^ 8
  + 14 * s ^ 7
  - 9 * s ^ 6
  + s ^ 5

private def term0C4 (s : ℚ) : ℚ :=
  2 * s ^ 26
  - 30 * s ^ 25
  + 180 * s ^ 24
  - 680 * s ^ 23
  + 1843 * s ^ 22
  - 3621 * s ^ 21
  + 4905 * s ^ 20
  - 3086 * s ^ 19
  - 5707 * s ^ 18
  + 23275 * s ^ 17
  - 44061 * s ^ 16
  + 60456 * s ^ 15
  - 71532 * s ^ 14
  + 80972 * s ^ 13
  - 86818 * s ^ 12
  + 77550 * s ^ 11
  - 50799 * s ^ 10
  + 21057 * s ^ 9
  - 3135 * s ^ 8
  - 1040 * s ^ 7
  + 305 * s ^ 6
  - 37 * s ^ 5
  + s ^ 4

private def term0C5 (s : ℚ) : ℚ :=
  3 * s ^ 26
  - 64 * s ^ 25
  + 554 * s ^ 24
  - 2786 * s ^ 23
  + 10008 * s ^ 22
  - 28114 * s ^ 21
  + 64234 * s ^ 20
  - 123217 * s ^ 19
  + 201982 * s ^ 18
  - 283085 * s ^ 17
  + 349973 * s ^ 16
  - 424219 * s ^ 15
  + 542882 * s ^ 14
  - 681291 * s ^ 13
  + 728927 * s ^ 12
  - 590662 * s ^ 11
  + 325560 * s ^ 10
  - 93402 * s ^ 9
  - 11410 * s ^ 8
  + 18100 * s ^ 7
  - 4515 * s ^ 6
  + 564 * s ^ 5
  - 22 * s ^ 4

private def term0C6 (s : ℚ) : ℚ :=
  2 * s ^ 27
  - 32 * s ^ 26
  + 229 * s ^ 25
  - 930 * s ^ 24
  + 2406 * s ^ 23
  - 4374 * s ^ 22
  + 5572 * s ^ 21
  - 5466 * s ^ 20
  + 13240 * s ^ 19
  - 63179 * s ^ 18
  + 247313 * s ^ 17
  - 758008 * s ^ 16
  + 1777290 * s ^ 15
  - 3125776 * s ^ 14
  + 4110822 * s ^ 13
  - 3970239 * s ^ 12
  + 2646042 * s ^ 11
  - 987895 * s ^ 10
  - 74430 * s ^ 9
  + 324060 * s ^ 8
  - 170874 * s ^ 7
  + 38796 * s ^ 6
  - 4766 * s ^ 5
  + 195 * s ^ 4
  + 2 * s ^ 3

private def term0C7 (s : ℚ) : ℚ :=
  2 * s ^ 27
  - 45 * s ^ 26
  + 428 * s ^ 25
  - 2319 * s ^ 24
  + 7869 * s ^ 23
  - 16509 * s ^ 22
  + 11510 * s ^ 21
  + 76044 * s ^ 20
  - 435137 * s ^ 19
  + 1457569 * s ^ 18
  - 3758113 * s ^ 17
  + 7843177 * s ^ 16
  - 13173751 * s ^ 15
  + 17444295 * s ^ 14
  - 17632042 * s ^ 13
  + 12608552 * s ^ 12
  - 4842568 * s ^ 11
  - 1311543 * s ^ 10
  + 3439882 * s ^ 9
  - 2519329 * s ^ 8
  + 982531 * s ^ 7
  - 202213 * s ^ 6
  + 22219 * s ^ 5
  - 433 * s ^ 4
  - 78 * s ^ 3
  + 2 * s ^ 2

private def term0C8 (s : ℚ) : ℚ :=
  2 * s ^ 27
  - 60 * s ^ 26
  + 782 * s ^ 25
  - 6119 * s ^ 24
  + 33421 * s ^ 23
  - 140737 * s ^ 22
  + 491233 * s ^ 21
  - 1479638 * s ^ 20
  + 3891296 * s ^ 19
  - 8909171 * s ^ 18
  + 17506597 * s ^ 17
  - 28748847 * s ^ 16
  + 37988495 * s ^ 15
  - 38031571 * s ^ 14
  + 24622367 * s ^ 13
  - 1985184 * s ^ 12
  - 18218791 * s ^ 11
  + 25915939 * s ^ 10
  - 20854443 * s ^ 9
  + 10857614 * s ^ 8
  - 3495056 * s ^ 7
  + 608214 * s ^ 6
  - 42192 * s ^ 5
  - 5050 * s ^ 4
  + 929 * s ^ 3
  - 30 * s ^ 2

private def term0C9 (s : ℚ) : ℚ :=
  s ^ 28
  - 25 * s ^ 27
  + 302 * s ^ 26
  - 2360 * s ^ 25
  + 13689 * s ^ 24
  - 64396 * s ^ 23
  + 258486 * s ^ 22
  - 897539 * s ^ 21
  + 2671751 * s ^ 20
  - 6718765 * s ^ 19
  + 14006145 * s ^ 18
  - 23373247 * s ^ 17
  + 28898779 * s ^ 16
  - 20248239 * s ^ 15
  - 10343179 * s ^ 14
  + 57868260 * s ^ 13
  - 101841948 * s ^ 12
  + 118490386 * s ^ 11
  - 100158031 * s ^ 10
  + 61707487 * s ^ 9
  - 26285767 * s ^ 8
  + 6748006 * s ^ 7
  - 659004 * s ^ 6
  - 113536 * s ^ 5
  + 48153 * s ^ 4
  - 5593 * s ^ 3
  + 183 * s ^ 2
  + s

private def term0C10 (s : ℚ) : ℚ :=
  -12 * s ^ 26
  + 300 * s ^ 25
  - 3534 * s ^ 24
  + 25825 * s ^ 23
  - 130204 * s ^ 22
  + 474816 * s ^ 21
  - 1253265 * s ^ 20
  + 2165298 * s ^ 19
  - 913118 * s ^ 18
  - 8994467 * s ^ 17
  + 38374425 * s ^ 16
  - 96157863 * s ^ 15
  + 177439939 * s ^ 14
  - 255917749 * s ^ 13
  + 293360562 * s ^ 12
  - 266004864 * s ^ 11
  + 186418066 * s ^ 10
  - 95715200 * s ^ 9
  + 31533972 * s ^ 8
  - 3754864 * s ^ 7
  - 1615869 * s ^ 6
  + 827111 * s ^ 5
  - 175043 * s ^ 4
  + 15930 * s ^ 3
  - 152 * s ^ 2
  - 41 * s
  + 1

private def term0C11 (s : ℚ) : ℚ :=
  -s ^ 27
  + 22 * s ^ 26
  - 201 * s ^ 25
  + 774 * s ^ 24
  + 2109 * s ^ 23
  - 48478 * s ^ 22
  + 358958 * s ^ 21
  - 1792799 * s ^ 20
  + 6899028 * s ^ 19
  - 21462818 * s ^ 18
  + 55006201 * s ^ 17
  - 117000353 * s ^ 16
  + 207188031 * s ^ 15
  - 305330074 * s ^ 14
  + 372114840 * s ^ 13
  - 369318411 * s ^ 12
  + 289735499 * s ^ 11
  - 169078421 * s ^ 10
  + 62148864 * s ^ 9
  - 3373748 * s ^ 8
  - 11140445 * s ^ 7
  + 6741595 * s ^ 6
  - 1940699 * s ^ 5
  + 307389 * s ^ 4
  - 14809 * s ^ 3
  - 2334 * s ^ 2
  + 289 * s
  - 8

private def term0C12 (s : ℚ) : ℚ :=
  -s ^ 27
  + 30 * s ^ 26
  - 438 * s ^ 25
  + 4165 * s ^ 24
  - 29142 * s ^ 23
  + 160501 * s ^ 22
  - 724015 * s ^ 21
  + 2732551 * s ^ 20
  - 8703183 * s ^ 19
  + 23427712 * s ^ 18
  - 53243870 * s ^ 17
  + 101995673 * s ^ 16
  - 164106130 * s ^ 15
  + 219730094 * s ^ 14
  - 239887016 * s ^ 13
  + 204676444 * s ^ 12
  - 123035351 * s ^ 11
  + 32561541 * s ^ 10
  + 26478623 * s ^ 9
  - 40335730 * s ^ 8
  + 26324944 * s ^ 7
  - 9945471 * s ^ 6
  + 2127241 * s ^ 5
  - 186107 * s ^ 4
  - 32673 * s ^ 3
  + 10537 * s ^ 2
  - 957 * s
  + 28

private def term0C13 (s : ℚ) : ℚ :=
  -s ^ 26
  + 33 * s ^ 25
  - 519 * s ^ 24
  + 5173 * s ^ 23
  - 36606 * s ^ 22
  + 195199 * s ^ 21
  - 813033 * s ^ 20
  + 2708439 * s ^ 19
  - 7333961 * s ^ 18
  + 16297596 * s ^ 17
  - 29729054 * s ^ 16
  + 43802648 * s ^ 15
  - 49582825 * s ^ 14
  + 36749172 * s ^ 13
  - 2705636 * s ^ 12
  - 40375053 * s ^ 11
  + 70615979 * s ^ 10
  - 72678712 * s ^ 9
  + 50640640 * s ^ 8
  - 23416280 * s ^ 7
  + 6368228 * s ^ 6
  - 555522 * s ^ 5
  - 255166 * s ^ 4
  + 119561 * s ^ 3
  - 22086 * s ^ 2
  + 1842 * s
  - 56

private def term0C14 (s : ℚ) : ℚ :=
  2 * s ^ 23
  - 48 * s ^ 22
  + 542 * s ^ 21
  - 3953 * s ^ 20
  + 22080 * s ^ 19
  - 106304 * s ^ 18
  + 460379 * s ^ 17
  - 1737808 * s ^ 16
  + 5445244 * s ^ 15
  - 13759610 * s ^ 14
  + 27781970 * s ^ 13
  - 44787471 * s ^ 12
  + 57484632 * s ^ 11
  - 57900221 * s ^ 10
  + 44111535 * s ^ 9
  - 23452388 * s ^ 8
  + 6956888 * s ^ 7
  + 296260 * s ^ 6
  - 1283220 * s ^ 5
  + 616490 * s ^ 4
  - 170130 * s ^ 3
  + 27287 * s ^ 2
  - 2226 * s
  + 70

private def term0C15 (s : ℚ) : ℚ :=
  2 * s ^ 22
  - 62 * s ^ 21
  + 900 * s ^ 20
  - 8129 * s ^ 19
  + 51140 * s ^ 18
  - 237631 * s ^ 17
  + 844706 * s ^ 16
  - 2351256 * s ^ 15
  + 5209648 * s ^ 14
  - 9277861 * s ^ 13
  + 13264679 * s ^ 12
  - 14900211 * s ^ 11
  + 12343869 * s ^ 10
  - 6199347 * s ^ 9
  - 135503 * s ^ 8
  + 3292303 * s ^ 7
  - 3044919 * s ^ 6
  + 1584368 * s ^ 5
  - 552802 * s ^ 4
  + 135369 * s ^ 3
  - 20928 * s ^ 2
  + 1721 * s
  - 56

private def term0C16 (s : ℚ) : ℚ :=
  -s ^ 19
  + 18 * s ^ 18
  - 124 * s ^ 17
  + 359 * s ^ 16
  - 295 * s ^ 15
  + 3187 * s ^ 14
  - 45493 * s ^ 13
  + 262378 * s ^ 12
  - 888259 * s ^ 11
  + 2005855 * s ^ 10
  - 3182051 * s ^ 9
  + 3619989 * s ^ 8
  - 2972157 * s ^ 7
  + 1768599 * s ^ 6
  - 773879 * s ^ 5
  + 255078 * s ^ 4
  - 62192 * s ^ 3
  + 9789 * s ^ 2
  - 829 * s
  + 28

private def term0C17 (s : ℚ) : ℚ :=
  -s ^ 18
  + 29 * s ^ 17
  - 385 * s ^ 16
  + 3101 * s ^ 15
  - 16933 * s ^ 14
  + 66354 * s ^ 13
  - 192671 * s ^ 12
  + 422027 * s ^ 11
  - 703229 * s ^ 10
  + 892983 * s ^ 9
  - 862484 * s ^ 8
  + 633541 * s ^ 7
  - 357737 * s ^ 6
  + 159400 * s ^ 5
  - 56799 * s ^ 4
  + 15134 * s ^ 3
  - 2549 * s ^ 2
  + 227 * s
  - 8

private def term0C18 (s : ℚ) : ℚ :=
  s ^ 12
  - 20 * s ^ 11
  + 174 * s ^ 10
  - 865 * s ^ 9
  + 2715 * s ^ 8
  - 5613 * s ^ 7
  + 7740 * s ^ 6
  - 7053 * s ^ 5
  + 4116 * s ^ 4
  - 1450 * s ^ 3
  + 281 * s ^ 2
  - 27 * s
  + 1

private def term0Expanded (r s : ℚ) : ℚ :=
  term0C18 s * r ^ 18
    + term0C17 s * r ^ 17
    + term0C16 s * r ^ 16
    + term0C15 s * r ^ 15
    + term0C14 s * r ^ 14
    + term0C13 s * r ^ 13
    + term0C12 s * r ^ 12
    + term0C11 s * r ^ 11
    + term0C10 s * r ^ 10
    + term0C9 s * r ^ 9
    + term0C8 s * r ^ 8
    + term0C7 s * r ^ 7
    + term0C6 s * r ^ 6
    + term0C5 s * r ^ 5
    + term0C4 s * r ^ 4
    + term0C3 s * r ^ 3
    + term0C2 s * r ^ 2
    + term0C1 s * r
    + term0C0 s

private theorem term0_expansion (r s : ℚ) :
    term0 r s = term0Expanded r s := by
  simp only [term0, term0Expanded, term0C0, term0C1, term0C2, term0C3, term0C4, term0C5, term0C6,
    term0C7, term0C8, term0C9, term0C10, term0C11, term0C12, term0C13, term0C14, term0C15, term0C16,
    term0C17, term0C18, B, K, T, M, N]
  ring

private def term1 (r s : ℚ) : ℚ :=
  -A r s * C r s * D r s * P6 r s * P9 r s * s

private def term1C0 (s : ℚ) : ℚ :=
  -s ^ 15

private def term1C1 (s : ℚ) : ℚ :=
  s ^ 21
  - 3 * s ^ 20
  + 6 * s ^ 19
  - 10 * s ^ 18
  + 16 * s ^ 17
  - 25 * s ^ 16
  + 24 * s ^ 15
  + 16 * s ^ 14
  - 10 * s ^ 13
  + 6 * s ^ 12
  - 3 * s ^ 11
  + s ^ 10

private def term1C2 (s : ℚ) : ℚ :=
  -s ^ 23
  + 7 * s ^ 22
  - 20 * s ^ 21
  + 18 * s ^ 20
  - 2 * s ^ 19
  - 22 * s ^ 18
  + 71 * s ^ 17
  - 250 * s ^ 16
  + 680 * s ^ 15
  - 1004 * s ^ 14
  + 550 * s ^ 13
  - 289 * s ^ 12
  + 124 * s ^ 11
  - 32 * s ^ 10
  - s ^ 9

private def term1C3 (s : ℚ) : ℚ :=
  -5 * s ^ 23
  + 64 * s ^ 22
  - 326 * s ^ 21
  + 932 * s ^ 20
  - 1784 * s ^ 19
  + 3163 * s ^ 18
  - 5717 * s ^ 17
  + 9635 * s ^ 16
  - 12502 * s ^ 15
  + 9688 * s ^ 14
  - 2735 * s ^ 13
  + 356 * s ^ 12
  + 630 * s ^ 11
  - 833 * s ^ 10
  + 531 * s ^ 9
  - 165 * s ^ 8
  + 45 * s ^ 7
  - 9 * s ^ 6
  + s ^ 5

private def term1C4 (s : ℚ) : ℚ :=
  -s ^ 26
  + 13 * s ^ 25
  - 90 * s ^ 24
  + 427 * s ^ 23
  - 1451 * s ^ 22
  + 3556 * s ^ 21
  - 6828 * s ^ 20
  + 12644 * s ^ 19
  - 25224 * s ^ 18
  + 43961 * s ^ 17
  - 55480 * s ^ 16
  + 36990 * s ^ 15
  + 11937 * s ^ 14
  - 46446 * s ^ 13
  + 39721 * s ^ 12
  - 29910 * s ^ 11
  + 19183 * s ^ 10
  - 9045 * s ^ 9
  + 2798 * s ^ 8
  - 765 * s ^ 7
  + 148 * s ^ 6
  - 13 * s ^ 5
  - s ^ 4

private def term1C5 (s : ℚ) : ℚ :=
  -s ^ 27
  + 13 * s ^ 26
  - 80 * s ^ 25
  + 315 * s ^ 24
  - 855 * s ^ 23
  + 1645 * s ^ 22
  - 3122 * s ^ 21
  + 10278 * s ^ 20
  - 33828 * s ^ 19
  + 68000 * s ^ 18
  - 56200 * s ^ 17
  - 80366 * s ^ 16
  + 341599 * s ^ 15
  - 557654 * s ^ 14
  + 539850 * s ^ 13
  - 372970 * s ^ 12
  + 254715 * s ^ 11
  - 148851 * s ^ 10
  + 64014 * s ^ 9
  - 19310 * s ^ 8
  + 5326 * s ^ 7
  - 935 * s ^ 6
  + 22 * s ^ 5
  + 23 * s ^ 4

private def term1C6 (s : ℚ) : ℚ :=
  -s ^ 27
  + 20 * s ^ 26
  - 158 * s ^ 25
  + 705 * s ^ 24
  - 1903 * s ^ 23
  + 2149 * s ^ 22
  + 5152 * s ^ 21
  - 22286 * s ^ 20
  - 4009 * s ^ 19
  + 246477 * s ^ 18
  - 915811 * s ^ 17
  + 1962051 * s ^ 16
  - 2869073 * s ^ 15
  + 2961179 * s ^ 14
  - 2248903 * s ^ 13
  + 1516071 * s ^ 12
  - 1083902 * s ^ 11
  + 616445 * s ^ 10
  - 244693 * s ^ 9
  + 70200 * s ^ 8
  - 19569 * s ^ 7
  + 2350 * s ^ 6
  + 611 * s ^ 5
  - 233 * s ^ 4
  - s ^ 3

private def term1C7 (s : ℚ) : ℚ :=
  -s ^ 27
  + 26 * s ^ 26
  - 275 * s ^ 25
  + 1594 * s ^ 24
  - 5460 * s ^ 23
  + 7510 * s ^ 22
  + 34958 * s ^ 21
  - 284282 * s ^ 20
  + 1090912 * s ^ 19
  - 2818259 * s ^ 18
  + 5300894 * s ^ 17
  - 7447496 * s ^ 16
  + 7837183 * s ^ 15
  - 6246246 * s ^ 14
  + 4365303 * s ^ 13
  - 3582755 * s ^ 12
  + 2936155 * s ^ 11
  - 1573368 * s ^ 10
  + 533659 * s ^ 9
  - 135878 * s ^ 8
  + 36665 * s ^ 7
  + 4215 * s ^ 6
  - 6091 * s ^ 5
  + 1407 * s ^ 4
  + 18 * s ^ 3

private def term1C8 (s : ℚ) : ℚ :=
  -2 * s ^ 27
  + 57 * s ^ 26
  - 763 * s ^ 25
  + 6366 * s ^ 24
  - 37655 * s ^ 23
  + 169745 * s ^ 22
  - 602341 * s ^ 21
  + 1692713 * s ^ 20
  - 3741944 * s ^ 19
  + 6426543 * s ^ 18
  - 8415412 * s ^ 17
  + 8164895 * s ^ 16
  - 5821149 * s ^ 15
  + 4062369 * s ^ 14
  - 5277158 * s ^ 13
  + 7279921 * s ^ 12
  - 5984301 * s ^ 11
  + 2460516 * s ^ 10
  - 492360 * s ^ 9
  + 64369 * s ^ 8
  + 3804 * s ^ 7
  - 59230 * s ^ 6
  + 31284 * s ^ 5
  - 5696 * s ^ 4
  - 153 * s ^ 3

private def term1C9 (s : ℚ) : ℚ :=
  -s ^ 28
  + 25 * s ^ 27
  - 306 * s ^ 26
  + 2423 * s ^ 25
  - 13881 * s ^ 24
  + 60844 * s ^ 23
  - 208132 * s ^ 22
  + 549317 * s ^ 21
  - 1070080 * s ^ 20
  + 1366954 * s ^ 19
  - 607114 * s ^ 18
  - 1616507 * s ^ 17
  + 3780113 * s ^ 16
  - 2295564 * s ^ 15
  - 5028272 * s ^ 14
  + 13885574 * s ^ 13
  - 15412609 * s ^ 12
  + 8067357 * s ^ 11
  - 819906 * s ^ 10
  - 864116 * s ^ 9
  + 401769 * s ^ 8
  - 261160 * s ^ 7
  + 266170 * s ^ 6
  - 107513 * s ^ 5
  + 16175 * s ^ 4
  + 818 * s ^ 3

private def term1C10 (s : ℚ) : ℚ :=
  s ^ 27
  - 22 * s ^ 26
  + 254 * s ^ 25
  - 2078 * s ^ 24
  + 13465 * s ^ 23
  - 70485 * s ^ 22
  + 290871 * s ^ 21
  - 916846 * s ^ 20
  + 2131627 * s ^ 19
  - 3390020 * s ^ 18
  + 2618684 * s ^ 17
  + 3266390 * s ^ 16
  - 15117251 * s ^ 15
  + 27199162 * s ^ 14
  - 28548960 * s ^ 13
  + 15027935 * s ^ 12
  + 1464867 * s ^ 11
  - 6924157 * s ^ 10
  + 3666098 * s ^ 9
  - 1238570 * s ^ 8
  + 982791 * s ^ 7
  - 776591 * s ^ 6
  + 265467 * s ^ 5
  - 31949 * s ^ 4
  - 3060 * s ^ 3
  - s ^ 2

private def term1C11 (s : ℚ) : ℚ :=
  2 * s ^ 26
  - 51 * s ^ 25
  + 575 * s ^ 24
  - 3624 * s ^ 23
  + 12105 * s ^ 22
  - 1937 * s ^ 21
  - 203554 * s ^ 20
  + 1204519 * s ^ 19
  - 4211536 * s ^ 18
  + 10471985 * s ^ 17
  - 19331331 * s ^ 16
  + 25841198 * s ^ 15
  - 21742223 * s ^ 14
  + 3791783 * s ^ 13
  + 17037960 * s ^ 12
  - 23424472 * s ^ 11
  + 13932612 * s ^ 10
  - 4012482 * s ^ 9
  + 1922022 * s ^ 8
  - 2427932 * s ^ 7
  + 1648827 * s ^ 6
  - 476974 * s ^ 5
  + 39722 * s ^ 4
  + 8375 * s ^ 3
  + 13 * s ^ 2

private def term1C12 (s : ℚ) : ℚ :=
  s ^ 26
  - 32 * s ^ 25
  + 479 * s ^ 24
  - 4452 * s ^ 23
  + 28648 * s ^ 22
  - 134672 * s ^ 21
  + 476138 * s ^ 20
  - 1280849 * s ^ 19
  + 2581116 * s ^ 18
  - 3545180 * s ^ 17
  + 1739116 * s ^ 16
  + 6258590 * s ^ 15
  - 20968041 * s ^ 14
  + 34860609 * s ^ 13
  - 35407425 * s ^ 12
  + 20146356 * s ^ 11
  - 3757251 * s ^ 10
  - 286825 * s ^ 9
  - 3494235 * s ^ 8
  + 4773890 * s ^ 7
  - 2605629 * s ^ 6
  + 601698 * s ^ 5
  - 15345 * s ^ 4
  - 17017 * s ^ 3
  - 76 * s ^ 2

private def term1C13 (s : ℚ) : ℚ :=
  -s ^ 25
  + 30 * s ^ 24
  - 432 * s ^ 23
  + 3937 * s ^ 22
  - 25343 * s ^ 21
  + 122797 * s ^ 20
  - 469421 * s ^ 19
  + 1467405 * s ^ 18
  - 3822360 * s ^ 17
  + 8242675 * s ^ 16
  - 14194721 * s ^ 15
  + 18152794 * s ^ 14
  - 14627908 * s ^ 13
  + 2788419 * s ^ 12
  + 8266480 * s ^ 11
  - 7848592 * s ^ 10
  - 1759185 * s ^ 9
  + 8416428 * s ^ 8
  - 7089417 * s ^ 7
  + 2879413 * s ^ 6
  - 451279 * s ^ 5
  - 50343 * s ^ 4
  + 25491 * s ^ 3
  + 265 * s ^ 2

private def term1C14 (s : ℚ) : ℚ :=
  -5 * s ^ 22
  + 148 * s ^ 21
  - 1855 * s ^ 20
  + 12897 * s ^ 19
  - 52589 * s ^ 18
  + 105747 * s ^ 17
  + 94479 * s ^ 16
  - 1388168 * s ^ 15
  + 4844011 * s ^ 14
  - 9847963 * s ^ 13
  + 12297033 * s ^ 12
  - 7397254 * s ^ 11
  - 3465573 * s ^ 10
  + 11872483 * s ^ 9
  - 11859895 * s ^ 8
  + 6436509 * s ^ 7
  - 1786464 * s ^ 6
  + 33891 * s ^ 5
  + 118554 * s ^ 4
  - 26998 * s ^ 3
  - 616 * s ^ 2

private def term1C15 (s : ℚ) : ℚ :=
  -s ^ 22
  + 37 * s ^ 21
  - 601 * s ^ 20
  + 5760 * s ^ 19
  - 36630 * s ^ 18
  + 163501 * s ^ 17
  - 523024 * s ^ 16
  + 1180411 * s ^ 15
  - 1708197 * s ^ 14
  + 854765 * s ^ 13
  + 2670251 * s ^ 12
  - 8161328 * s ^ 11
  + 12178303 * s ^ 10
  - 11545384 * s ^ 9
  + 7053580 * s ^ 8
  - 2445315 * s ^ 7
  + 131619 * s ^ 6
  + 290328 * s ^ 5
  - 123284 * s ^ 4
  + 18120 * s ^ 3
  + 964 * s ^ 2
  + s

private def term1C16 (s : ℚ) : ℚ :=
  s ^ 21
  - 31 * s ^ 20
  + 448 * s ^ 19
  - 4015 * s ^ 18
  + 25016 * s ^ 17
  - 114953 * s ^ 16
  + 402452 * s ^ 15
  - 1091089 * s ^ 14
  + 2300369 * s ^ 13
  - 3746869 * s ^ 12
  + 4624549 * s ^ 11
  - 4150227 * s ^ 10
  + 2448072 * s ^ 9
  - 606265 * s ^ 8
  - 389939 * s ^ 7
  + 492425 * s ^ 6
  - 247111 * s ^ 5
  + 62862 * s ^ 4
  - 5709 * s ^ 3
  - 950 * s ^ 2
  - 5 * s

private def term1C17 (s : ℚ) : ℚ :=
  -s ^ 18
  + 28 * s ^ 17
  - 359 * s ^ 16
  + 2792 * s ^ 15
  - 14710 * s ^ 14
  + 55544 * s ^ 13
  - 155105 * s ^ 12
  + 325921 * s ^ 11
  - 519583 * s ^ 10
  + 629319 * s ^ 9
  - 576349 * s ^ 8
  + 393724 * s ^ 7
  - 194080 * s ^ 6
  + 63315 * s ^ 5
  - 10347 * s ^ 4
  - 466 * s ^ 3
  + 519 * s ^ 2
  + 9 * s

private def term1C18 (s : ℚ) : ℚ :=
  s ^ 11
  - 17 * s ^ 10
  + 125 * s ^ 9
  - 520 * s ^ 8
  + 1344 * s ^ 7
  - 2229 * s ^ 6
  + 2364 * s ^ 5
  - 1545 * s ^ 4
  + 582 * s ^ 3
  - 117 * s ^ 2
  - 7 * s

private def term1C19 (s : ℚ) : ℚ :=
  -s ^ 2
  + 2 * s

private def term1Expanded (r s : ℚ) : ℚ :=
  term1C19 s * r ^ 19
    + term1C18 s * r ^ 18
    + term1C17 s * r ^ 17
    + term1C16 s * r ^ 16
    + term1C15 s * r ^ 15
    + term1C14 s * r ^ 14
    + term1C13 s * r ^ 13
    + term1C12 s * r ^ 12
    + term1C11 s * r ^ 11
    + term1C10 s * r ^ 10
    + term1C9 s * r ^ 9
    + term1C8 s * r ^ 8
    + term1C7 s * r ^ 7
    + term1C6 s * r ^ 6
    + term1C5 s * r ^ 5
    + term1C4 s * r ^ 4
    + term1C3 s * r ^ 3
    + term1C2 s * r ^ 2
    + term1C1 s * r
    + term1C0 s

private theorem term1_expansion (r s : ℚ) :
    term1 r s = term1Expanded r s := by
  simp only [term1, term1Expanded, term1C0, term1C1, term1C2, term1C3, term1C4, term1C5, term1C6,
    term1C7, term1C8, term1C9, term1C10, term1C11, term1C12, term1C13, term1C14, term1C15, term1C16,
    term1C17, term1C18, term1C19, A, B, C, K, D, E, G, L, P6, P9]
  ring

private def nC0 (s : ℚ) : ℚ :=
  -s ^ 15

private def nC1 (s : ℚ) : ℚ :=
  s ^ 21
  - 3 * s ^ 20
  + 5 * s ^ 19
  - 7 * s ^ 18
  + 11 * s ^ 17
  - 18 * s ^ 16
  + 15 * s ^ 15
  + 27 * s ^ 14
  - 21 * s ^ 13
  + 15 * s ^ 12
  - 10 * s ^ 11
  + 6 * s ^ 10
  - 3 * s ^ 9
  + s ^ 8

private def nC2 (s : ℚ) : ℚ :=
  6 * s ^ 21
  - 52 * s ^ 20
  + 144 * s ^ 19
  - 249 * s ^ 18
  + 374 * s ^ 17
  - 643 * s ^ 16
  + 1165 * s ^ 15
  - 1539 * s ^ 14
  + 1047 * s ^ 13
  - 706 * s ^ 12
  + 464 * s ^ 11
  - 276 * s ^ 10
  + 132 * s ^ 9
  - 39 * s ^ 8
  + s ^ 7

private def nC3 (s : ℚ) : ℚ :=
  s ^ 26
  - 9 * s ^ 25
  + 44 * s ^ 24
  - 156 * s ^ 23
  + 451 * s ^ 22
  - 1111 * s ^ 21
  + 2261 * s ^ 20
  - 3722 * s ^ 19
  + 5796 * s ^ 18
  - 9584 * s ^ 17
  + 15375 * s ^ 16
  - 19980 * s ^ 15
  + 17947 * s ^ 14
  - 10790 * s ^ 13
  + 7948 * s ^ 12
  - 6045 * s ^ 11
  + 3892 * s ^ 10
  - 1790 * s ^ 9
  + 398 * s ^ 8
  + 59 * s ^ 7
  - 18 * s ^ 6
  + 2 * s ^ 5

private def nC4 (s : ℚ) : ℚ :=
  s ^ 26
  - 17 * s ^ 25
  + 90 * s ^ 24
  - 253 * s ^ 23
  + 392 * s ^ 22
  - 65 * s ^ 21
  - 1923 * s ^ 20
  + 9558 * s ^ 19
  - 30931 * s ^ 18
  + 67236 * s ^ 17
  - 99541 * s ^ 16
  + 97446 * s ^ 15
  - 59595 * s ^ 14
  + 34526 * s ^ 13
  - 47097 * s ^ 12
  + 47640 * s ^ 11
  - 31616 * s ^ 10
  + 12012 * s ^ 9
  - 337 * s ^ 8
  - 1805 * s ^ 7
  + 453 * s ^ 6
  - 50 * s ^ 5

private def nC5 (s : ℚ) : ℚ :=
  -s ^ 27
  + 16 * s ^ 26
  - 144 * s ^ 25
  + 869 * s ^ 24
  - 3641 * s ^ 23
  + 11653 * s ^ 22
  - 31236 * s ^ 21
  + 74512 * s ^ 20
  - 157045 * s ^ 19
  + 269982 * s ^ 18
  - 339285 * s ^ 17
  + 269607 * s ^ 16
  - 82620 * s ^ 15
  - 14772 * s ^ 14
  - 141441 * s ^ 13
  + 355957 * s ^ 12
  - 335947 * s ^ 11
  + 176709 * s ^ 10
  - 29388 * s ^ 9
  - 30720 * s ^ 8
  + 23426 * s ^ 7
  - 5450 * s ^ 6
  + 586 * s ^ 5
  + s ^ 4

private def nC6 (s : ℚ) : ℚ :=
  s ^ 27
  - 12 * s ^ 26
  + 71 * s ^ 25
  - 225 * s ^ 24
  + 503 * s ^ 23
  - 2225 * s ^ 22
  + 10724 * s ^ 21
  - 27752 * s ^ 20
  + 9231 * s ^ 19
  + 183298 * s ^ 18
  - 668498 * s ^ 17
  + 1204043 * s ^ 16
  - 1091783 * s ^ 15
  - 164597 * s ^ 14
  + 1861919 * s ^ 13
  - 2454168 * s ^ 12
  + 1562140 * s ^ 11
  - 371450 * s ^ 10
  - 319123 * s ^ 9
  + 394260 * s ^ 8
  - 190443 * s ^ 7
  + 41146 * s ^ 6
  - 4155 * s ^ 5
  - 38 * s ^ 4
  + s ^ 3

private def nC7 (s : ℚ) : ℚ :=
  s ^ 27
  - 19 * s ^ 26
  + 153 * s ^ 25
  - 725 * s ^ 24
  + 2409 * s ^ 23
  - 8999 * s ^ 22
  + 46468 * s ^ 21
  - 208238 * s ^ 20
  + 655775 * s ^ 19
  - 1360690 * s ^ 18
  + 1542781 * s ^ 17
  + 395681 * s ^ 16
  - 5336568 * s ^ 15
  + 11198049 * s ^ 14
  - 13266739 * s ^ 13
  + 9025797 * s ^ 12
  - 1906413 * s ^ 11
  - 2884911 * s ^ 10
  + 3973541 * s ^ 9
  - 2655207 * s ^ 8
  + 1019196 * s ^ 7
  - 197998 * s ^ 6
  + 16128 * s ^ 5
  + 974 * s ^ 4
  - 60 * s ^ 3
  + 2 * s ^ 2

private def nC8 (s : ℚ) : ℚ :=
  -3 * s ^ 26
  + 19 * s ^ 25
  + 247 * s ^ 24
  - 4234 * s ^ 23
  + 29008 * s ^ 22
  - 111108 * s ^ 21
  + 213075 * s ^ 20
  + 149352 * s ^ 19
  - 2482628 * s ^ 18
  + 9091185 * s ^ 17
  - 20583952 * s ^ 16
  + 32167346 * s ^ 15
  - 33969202 * s ^ 14
  + 19345209 * s ^ 13
  + 5294737 * s ^ 12
  - 24203092 * s ^ 11
  + 28376455 * s ^ 10
  - 21346803 * s ^ 9
  + 10921983 * s ^ 8
  - 3491252 * s ^ 7
  + 548984 * s ^ 6
  - 10908 * s ^ 5
  - 10746 * s ^ 4
  + 776 * s ^ 3
  - 30 * s ^ 2

private def nC9 (s : ℚ) : ℚ :=
  -4 * s ^ 26
  + 63 * s ^ 25
  - 192 * s ^ 24
  - 3552 * s ^ 23
  + 50354 * s ^ 22
  - 348222 * s ^ 21
  + 1601671 * s ^ 20
  - 5351811 * s ^ 19
  + 13399031 * s ^ 18
  - 24989754 * s ^ 17
  + 32678892 * s ^ 16
  - 22543803 * s ^ 15
  - 15371451 * s ^ 14
  + 71753834 * s ^ 13
  - 117254557 * s ^ 12
  + 126557743 * s ^ 11
  - 100977937 * s ^ 10
  + 60843371 * s ^ 9
  - 25883998 * s ^ 8
  + 6486846 * s ^ 7
  - 392834 * s ^ 6
  - 221049 * s ^ 5
  + 64328 * s ^ 4
  - 4775 * s ^ 3
  + 183 * s ^ 2
  + s

private def nC10 (s : ℚ) : ℚ :=
  s ^ 27
  - 34 * s ^ 26
  + 554 * s ^ 25
  - 5612 * s ^ 24
  + 39290 * s ^ 23
  - 200689 * s ^ 22
  + 765687 * s ^ 21
  - 2170111 * s ^ 20
  + 4296925 * s ^ 19
  - 4303138 * s ^ 18
  - 6375783 * s ^ 17
  + 41640815 * s ^ 16
  - 111275114 * s ^ 15
  + 204639101 * s ^ 14
  - 284466709 * s ^ 13
  + 308388497 * s ^ 12
  - 264539997 * s ^ 11
  + 179493909 * s ^ 10
  - 92049102 * s ^ 9
  + 30295402 * s ^ 8
  - 2772073 * s ^ 7
  - 2392460 * s ^ 6
  + 1092578 * s ^ 5
  - 206992 * s ^ 4
  + 12870 * s ^ 3
  - 153 * s ^ 2
  - 41 * s
  + 1

private def nC11 (s : ℚ) : ℚ :=
  -s ^ 27
  + 24 * s ^ 26
  - 252 * s ^ 25
  + 1349 * s ^ 24
  - 1515 * s ^ 23
  - 36373 * s ^ 22
  + 357021 * s ^ 21
  - 1996353 * s ^ 20
  + 8103547 * s ^ 19
  - 25674354 * s ^ 18
  + 65478186 * s ^ 17
  - 136331684 * s ^ 16
  + 233029229 * s ^ 15
  - 327072297 * s ^ 14
  + 375906623 * s ^ 13
  - 352280451 * s ^ 12
  + 266311027 * s ^ 11
  - 155145809 * s ^ 10
  + 58136382 * s ^ 9
  - 1451726 * s ^ 8
  - 13568377 * s ^ 7
  + 8390422 * s ^ 6
  - 2417673 * s ^ 5
  + 347111 * s ^ 4
  - 6434 * s ^ 3
  - 2321 * s ^ 2
  + 289 * s
  - 8

private def nC12 (s : ℚ) : ℚ :=
  -s ^ 27
  + 31 * s ^ 26
  - 470 * s ^ 25
  + 4644 * s ^ 24
  - 33594 * s ^ 23
  + 189149 * s ^ 22
  - 858687 * s ^ 21
  + 3208689 * s ^ 20
  - 9984032 * s ^ 19
  + 26008828 * s ^ 18
  - 56789050 * s ^ 17
  + 103734789 * s ^ 16
  - 157847540 * s ^ 15
  + 198762053 * s ^ 14
  - 205026407 * s ^ 13
  + 169269019 * s ^ 12
  - 102888995 * s ^ 11
  + 28804290 * s ^ 10
  + 26191798 * s ^ 9
  - 43829965 * s ^ 8
  + 31098834 * s ^ 7
  - 12551100 * s ^ 6
  + 2728939 * s ^ 5
  - 201452 * s ^ 4
  - 49690 * s ^ 3
  + 10461 * s ^ 2
  - 957 * s
  + 28

private def nC13 (s : ℚ) : ℚ :=
  -s ^ 26
  + 32 * s ^ 25
  - 489 * s ^ 24
  + 4741 * s ^ 23
  - 32669 * s ^ 22
  + 169856 * s ^ 21
  - 690236 * s ^ 20
  + 2239018 * s ^ 19
  - 5866556 * s ^ 18
  + 12475236 * s ^ 17
  - 21486379 * s ^ 16
  + 29607927 * s ^ 15
  - 31430031 * s ^ 14
  + 22121264 * s ^ 13
  + 82783 * s ^ 12
  - 32108573 * s ^ 11
  + 62767387 * s ^ 10
  - 74437897 * s ^ 9
  + 59057068 * s ^ 8
  - 30505697 * s ^ 7
  + 9247641 * s ^ 6
  - 1006801 * s ^ 5
  - 305509 * s ^ 4
  + 145052 * s ^ 3
  - 21821 * s ^ 2
  + 1842 * s
  - 56

private def nC14 (s : ℚ) : ℚ :=
  2 * s ^ 23
  - 53 * s ^ 22
  + 690 * s ^ 21
  - 5808 * s ^ 20
  + 34977 * s ^ 19
  - 158893 * s ^ 18
  + 566126 * s ^ 17
  - 1643329 * s ^ 16
  + 4057076 * s ^ 15
  - 8915599 * s ^ 14
  + 17934007 * s ^ 13
  - 32490438 * s ^ 12
  + 50087378 * s ^ 11
  - 61365794 * s ^ 10
  + 55984018 * s ^ 9
  - 35312283 * s ^ 8
  + 13393397 * s ^ 7
  - 1490204 * s ^ 6
  - 1249329 * s ^ 5
  + 735044 * s ^ 4
  - 197128 * s ^ 3
  + 26671 * s ^ 2
  - 2226 * s
  + 70

private def nC15 (s : ℚ) : ℚ :=
  s ^ 22
  - 25 * s ^ 21
  + 299 * s ^ 20
  - 2369 * s ^ 19
  + 14510 * s ^ 18
  - 74130 * s ^ 17
  + 321682 * s ^ 16
  - 1170845 * s ^ 15
  + 3501451 * s ^ 14
  - 8423096 * s ^ 13
  + 15934930 * s ^ 12
  - 23061539 * s ^ 11
  + 24522172 * s ^ 10
  - 17744731 * s ^ 9
  + 6918077 * s ^ 8
  + 846988 * s ^ 7
  - 2913300 * s ^ 6
  + 1874696 * s ^ 5
  - 676086 * s ^ 4
  + 153489 * s ^ 3
  - 19964 * s ^ 2
  + 1722 * s
  - 56

private def nC16 (s : ℚ) : ℚ :=
  s ^ 21
  - 31 * s ^ 20
  + 447 * s ^ 19
  - 3997 * s ^ 18
  + 24892 * s ^ 17
  - 114594 * s ^ 16
  + 402157 * s ^ 15
  - 1087902 * s ^ 14
  + 2254876 * s ^ 13
  - 3484491 * s ^ 12
  + 3736290 * s ^ 11
  - 2144372 * s ^ 10
  - 733979 * s ^ 9
  + 3013724 * s ^ 8
  - 3362096 * s ^ 7
  + 2261024 * s ^ 6
  - 1020990 * s ^ 5
  + 317940 * s ^ 4
  - 67901 * s ^ 3
  + 8839 * s ^ 2
  - 834 * s
  + 28

private def nC17 (s : ℚ) : ℚ :=
  -2 * s ^ 18
  + 57 * s ^ 17
  - 744 * s ^ 16
  + 5893 * s ^ 15
  - 31643 * s ^ 14
  + 121898 * s ^ 13
  - 347776 * s ^ 12
  + 747948 * s ^ 11
  - 1222812 * s ^ 10
  + 1522302 * s ^ 9
  - 1438833 * s ^ 8
  + 1027265 * s ^ 7
  - 551817 * s ^ 6
  + 222715 * s ^ 5
  - 67146 * s ^ 4
  + 14668 * s ^ 3
  - 2030 * s ^ 2
  + 236 * s
  - 8

private def nC18 (s : ℚ) : ℚ :=
  s ^ 12
  - 19 * s ^ 11
  + 157 * s ^ 10
  - 740 * s ^ 9
  + 2195 * s ^ 8
  - 4269 * s ^ 7
  + 5511 * s ^ 6
  - 4689 * s ^ 5
  + 2571 * s ^ 4
  - 868 * s ^ 3
  + 164 * s ^ 2
  - 34 * s
  + 1

private def nC19 (s : ℚ) : ℚ :=
  -s ^ 2
  + 2 * s

private def numerator (r s : ℚ) : ℚ :=
  nC19 s * r ^ 19
    + nC18 s * r ^ 18
    + nC17 s * r ^ 17
    + nC16 s * r ^ 16
    + nC15 s * r ^ 15
    + nC14 s * r ^ 14
    + nC13 s * r ^ 13
    + nC12 s * r ^ 12
    + nC11 s * r ^ 11
    + nC10 s * r ^ 10
    + nC9 s * r ^ 9
    + nC8 s * r ^ 8
    + nC7 s * r ^ 7
    + nC6 s * r ^ 6
    + nC5 s * r ^ 5
    + nC4 s * r ^ 4
    + nC3 s * r ^ 3
    + nC2 s * r ^ 2
    + nC1 s * r
    + nC0 s

private def lhsC0 (s : ℚ) : ℚ :=
  term0C0 s + term1C0 s

private theorem lhs_coefficient_0 (s : ℚ) :
    lhsC0 s = nC0 s := by
  simp only [lhsC0, term0C0, term1C0, nC0]
  ring

private def lhsC1 (s : ℚ) : ℚ :=
  term0C1 s + term1C1 s

private theorem lhs_coefficient_1 (s : ℚ) :
    lhsC1 s = nC1 s := by
  simp only [lhsC1, term0C1, term1C1, nC1]
  ring

private def lhsC2 (s : ℚ) : ℚ :=
  term0C2 s + term1C2 s

private theorem lhs_coefficient_2 (s : ℚ) :
    lhsC2 s = nC2 s := by
  simp only [lhsC2, term0C2, term1C2, nC2]
  ring

private def lhsC3 (s : ℚ) : ℚ :=
  term0C3 s + term1C3 s

private theorem lhs_coefficient_3 (s : ℚ) :
    lhsC3 s = nC3 s := by
  simp only [lhsC3, term0C3, term1C3, nC3]
  ring

private def lhsC4 (s : ℚ) : ℚ :=
  term0C4 s + term1C4 s

private theorem lhs_coefficient_4 (s : ℚ) :
    lhsC4 s = nC4 s := by
  simp only [lhsC4, term0C4, term1C4, nC4]
  ring

private def lhsC5 (s : ℚ) : ℚ :=
  term0C5 s + term1C5 s

private theorem lhs_coefficient_5 (s : ℚ) :
    lhsC5 s = nC5 s := by
  simp only [lhsC5, term0C5, term1C5, nC5]
  ring

private def lhsC6 (s : ℚ) : ℚ :=
  term0C6 s + term1C6 s

private theorem lhs_coefficient_6 (s : ℚ) :
    lhsC6 s = nC6 s := by
  simp only [lhsC6, term0C6, term1C6, nC6]
  ring

private def lhsC7 (s : ℚ) : ℚ :=
  term0C7 s + term1C7 s

private theorem lhs_coefficient_7 (s : ℚ) :
    lhsC7 s = nC7 s := by
  simp only [lhsC7, term0C7, term1C7, nC7]
  ring

private def lhsC8 (s : ℚ) : ℚ :=
  term0C8 s + term1C8 s

private theorem lhs_coefficient_8 (s : ℚ) :
    lhsC8 s = nC8 s := by
  simp only [lhsC8, term0C8, term1C8, nC8]
  ring

private def lhsC9 (s : ℚ) : ℚ :=
  term0C9 s + term1C9 s

private theorem lhs_coefficient_9 (s : ℚ) :
    lhsC9 s = nC9 s := by
  simp only [lhsC9, term0C9, term1C9, nC9]
  ring

private def lhsC10 (s : ℚ) : ℚ :=
  term0C10 s + term1C10 s

private theorem lhs_coefficient_10 (s : ℚ) :
    lhsC10 s = nC10 s := by
  simp only [lhsC10, term0C10, term1C10, nC10]
  ring

private def lhsC11 (s : ℚ) : ℚ :=
  term0C11 s + term1C11 s

private theorem lhs_coefficient_11 (s : ℚ) :
    lhsC11 s = nC11 s := by
  simp only [lhsC11, term0C11, term1C11, nC11]
  ring

private def lhsC12 (s : ℚ) : ℚ :=
  term0C12 s + term1C12 s

private theorem lhs_coefficient_12 (s : ℚ) :
    lhsC12 s = nC12 s := by
  simp only [lhsC12, term0C12, term1C12, nC12]
  ring

private def lhsC13 (s : ℚ) : ℚ :=
  term0C13 s + term1C13 s

private theorem lhs_coefficient_13 (s : ℚ) :
    lhsC13 s = nC13 s := by
  simp only [lhsC13, term0C13, term1C13, nC13]
  ring

private def lhsC14 (s : ℚ) : ℚ :=
  term0C14 s + term1C14 s

private theorem lhs_coefficient_14 (s : ℚ) :
    lhsC14 s = nC14 s := by
  simp only [lhsC14, term0C14, term1C14, nC14]
  ring

private def lhsC15 (s : ℚ) : ℚ :=
  term0C15 s + term1C15 s

private theorem lhs_coefficient_15 (s : ℚ) :
    lhsC15 s = nC15 s := by
  simp only [lhsC15, term0C15, term1C15, nC15]
  ring

private def lhsC16 (s : ℚ) : ℚ :=
  term0C16 s + term1C16 s

private theorem lhs_coefficient_16 (s : ℚ) :
    lhsC16 s = nC16 s := by
  simp only [lhsC16, term0C16, term1C16, nC16]
  ring

private def lhsC17 (s : ℚ) : ℚ :=
  term0C17 s + term1C17 s

private theorem lhs_coefficient_17 (s : ℚ) :
    lhsC17 s = nC17 s := by
  simp only [lhsC17, term0C17, term1C17, nC17]
  ring

private def lhsC18 (s : ℚ) : ℚ :=
  term0C18 s + term1C18 s

private theorem lhs_coefficient_18 (s : ℚ) :
    lhsC18 s = nC18 s := by
  simp only [lhsC18, term0C18, term1C18, nC18]
  ring

private def lhsC19 (s : ℚ) : ℚ :=
  term1C19 s

private theorem lhs_coefficient_19 (s : ℚ) :
    lhsC19 s = nC19 s := by
  simp only [lhsC19, term1C19, nC19]

private def lhs (r s : ℚ) : ℚ :=
  lhsC19 s * r ^ 19
    + lhsC18 s * r ^ 18
    + lhsC17 s * r ^ 17
    + lhsC16 s * r ^ 16
    + lhsC15 s * r ^ 15
    + lhsC14 s * r ^ 14
    + lhsC13 s * r ^ 13
    + lhsC12 s * r ^ 12
    + lhsC11 s * r ^ 11
    + lhsC10 s * r ^ 10
    + lhsC9 s * r ^ 9
    + lhsC8 s * r ^ 8
    + lhsC7 s * r ^ 7
    + lhsC6 s * r ^ 6
    + lhsC5 s * r ^ 5
    + lhsC4 s * r ^ 4
    + lhsC3 s * r ^ 3
    + lhsC2 s * r ^ 2
    + lhsC1 s * r
    + lhsC0 s

private theorem terms_eq_lhs (r s : ℚ) :
    term0 r s + term1 r s = lhs r s := by
  rw [term0_expansion, term1_expansion]
  simp only [term0Expanded, term1Expanded, lhs, lhsC0, lhsC1, lhsC2, lhsC3, lhsC4, lhsC5, lhsC6,
    lhsC7, lhsC8, lhsC9, lhsC10, lhsC11, lhsC12, lhsC13, lhsC14, lhsC15, lhsC16, lhsC17, lhsC18,
    lhsC19]
  ring

private theorem lhs_eq_numerator (r s : ℚ) :
    lhs r s = numerator r s := by
  simp only [lhs, numerator, lhs_coefficient_0, lhs_coefficient_1, lhs_coefficient_2,
    lhs_coefficient_3, lhs_coefficient_4, lhs_coefficient_5, lhs_coefficient_6, lhs_coefficient_7,
    lhs_coefficient_8, lhs_coefficient_9, lhs_coefficient_10, lhs_coefficient_11,
    lhs_coefficient_12, lhs_coefficient_13, lhs_coefficient_14, lhs_coefficient_15,
    lhs_coefficient_16, lhs_coefficient_17, lhs_coefficient_18, lhs_coefficient_19]

private theorem terms_eq_numerator (r s : ℚ) :
    term0 r s + term1 r s = numerator r s := by
  rw [terms_eq_lhs, lhs_eq_numerator]

private def qC0 (s : ℚ) : ℚ :=
  -s ^ 5

private def qC1 (s : ℚ) : ℚ :=
  s ^ 11
  - 3 * s ^ 10
  + 5 * s ^ 9
  - 7 * s ^ 8
  + 11 * s ^ 7
  - 18 * s ^ 6
  + 21 * s ^ 5
  - s ^ 4

private def qC2 (s : ℚ) : ℚ :=
  -5 * s ^ 10
  + 3 * s ^ 9
  + 32 * s ^ 8
  - 104 * s ^ 7
  + 157 * s ^ 6
  - 103 * s ^ 5
  - 26 * s ^ 4
  + 12 * s ^ 3
  - 2 * s ^ 2

private def qC3 (s : ℚ) : ℚ :=
  -s ^ 12
  + 9 * s ^ 11
  - 49 * s ^ 10
  + 193 * s ^ 9
  - 444 * s ^ 8
  + 640 * s ^ 7
  - 507 * s ^ 6
  + 5 * s ^ 5
  + 341 * s ^ 4
  - 123 * s ^ 3
  + 20 * s ^ 2

private def qC4 (s : ℚ) : ℚ :=
  2 * s ^ 12
  - 19 * s ^ 11
  + 93 * s ^ 10
  - 253 * s ^ 9
  + 323 * s ^ 8
  + 37 * s ^ 7
  - 1007 * s ^ 6
  + 1952 * s ^ 5
  - 1697 * s ^ 4
  + 522 * s ^ 3
  - 78 * s ^ 2
  - s

private def qC5 (s : ℚ) : ℚ :=
  -4 * s ^ 11
  + 46 * s ^ 10
  - 280 * s ^ 9
  + 1030 * s ^ 8
  - 2493 * s ^ 7
  + 4208 * s ^ 6
  - 4669 * s ^ 5
  + 2915 * s ^ 4
  - 695 * s ^ 3
  + 48 * s ^ 2
  + 21 * s
  - 1

private def qC6 (s : ℚ) : ℚ :=
  -s ^ 12
  + 14 * s ^ 11
  - 96 * s ^ 10
  + 418 * s ^ 9
  - 1243 * s ^ 8
  + 2620 * s ^ 7
  - 3853 * s ^ 6
  + 3565 * s ^ 5
  - 1617 * s ^ 4
  + 10 * s ^ 3
  + 155 * s ^ 2
  - 59 * s
  + 3

private def qC7 (s : ℚ) : ℚ :=
  -s ^ 11
  + 14 * s ^ 10
  - 86 * s ^ 9
  + 307 * s ^ 8
  - 688 * s ^ 7
  + 913 * s ^ 6
  - 513 * s ^ 5
  - 256 * s ^ 4
  + 519 * s ^ 3
  - 231 * s ^ 2
  + 61 * s
  - 3

private def qC8 (s : ℚ) : ℚ :=
  2 * s ^ 8
  - 23 * s ^ 7
  + 107 * s ^ 6
  - 257 * s ^ 5
  + 341 * s ^ 4
  - 245 * s ^ 3
  + 89 * s ^ 2
  - 24 * s
  + 1

private def qC9 (s : ℚ) : ℚ :=
  -s ^ 2
  + 2 * s

private def Q (r s : ℚ) : ℚ :=
  qC9 s * r ^ 9
    + qC8 s * r ^ 8
    + qC7 s * r ^ 7
    + qC6 s * r ^ 6
    + qC5 s * r ^ 5
    + qC4 s * r ^ 4
    + qC3 s * r ^ 3
    + qC2 s * r ^ 2
    + qC1 s * r
    + qC0 s

private def convC0 (s : ℚ) : ℚ :=
  fC0 s * qC0 s

private theorem conv_coefficient_0 (s : ℚ) :
    convC0 s = nC0 s := by
  simp only [convC0, fC0, qC0, nC0]
  ring

private def convC1 (s : ℚ) : ℚ :=
  fC0 s * qC1 s + fC1 s * qC0 s

private theorem conv_coefficient_1 (s : ℚ) :
    convC1 s = nC1 s := by
  simp only [convC1, fC0, fC1, qC1, qC0, nC1]
  ring

private def convC2 (s : ℚ) : ℚ :=
  fC0 s * qC2 s + fC1 s * qC1 s + fC2 s * qC0 s

private theorem conv_coefficient_2 (s : ℚ) :
    convC2 s = nC2 s := by
  simp only [convC2, fC0, fC1, fC2, qC2, qC1, qC0, nC2]
  ring

private def convC3 (s : ℚ) : ℚ :=
  fC0 s * qC3 s + fC1 s * qC2 s + fC2 s * qC1 s + fC3 s * qC0 s

private theorem conv_coefficient_3 (s : ℚ) :
    convC3 s = nC3 s := by
  simp only [convC3, fC0, fC1, fC2, fC3, qC3, qC2, qC1, qC0, nC3]
  ring

private def convC4 (s : ℚ) : ℚ :=
  fC0 s * qC4 s + fC1 s * qC3 s + fC2 s * qC2 s + fC3 s * qC1 s + fC4 s * qC0 s

private theorem conv_coefficient_4 (s : ℚ) :
    convC4 s = nC4 s := by
  simp only [convC4, fC0, fC1, fC2, fC3, fC4, qC4, qC3, qC2, qC1, qC0, nC4]
  ring

private def convC5 (s : ℚ) : ℚ :=
  fC0 s * qC5 s + fC1 s * qC4 s + fC2 s * qC3 s + fC3 s * qC2 s + fC4 s * qC1 s + fC5 s * qC0 s

private theorem conv_coefficient_5 (s : ℚ) :
    convC5 s = nC5 s := by
  simp only [convC5, fC0, fC1, fC2, fC3, fC4, fC5, qC5, qC4, qC3, qC2, qC1, qC0, nC5]
  ring

private def convC6 (s : ℚ) : ℚ :=
  fC0 s * qC6 s + fC1 s * qC5 s + fC2 s * qC4 s + fC3 s * qC3 s + fC4 s * qC2 s + fC5 s * qC1 s
    + fC6 s * qC0 s

private theorem conv_coefficient_6 (s : ℚ) :
    convC6 s = nC6 s := by
  simp only [convC6, fC0, fC1, fC2, fC3, fC4, fC5, fC6, qC6, qC5, qC4, qC3, qC2, qC1, qC0, nC6]
  ring

private def convC7 (s : ℚ) : ℚ :=
  fC0 s * qC7 s + fC1 s * qC6 s + fC2 s * qC5 s + fC3 s * qC4 s + fC4 s * qC3 s + fC5 s * qC2 s
    + fC6 s * qC1 s + fC7 s * qC0 s

private theorem conv_coefficient_7 (s : ℚ) :
    convC7 s = nC7 s := by
  simp only [convC7, fC0, fC1, fC2, fC3, fC4, fC5, fC6, fC7, qC7, qC6, qC5, qC4, qC3, qC2, qC1, qC0,
    nC7]
  ring

private def convC8 (s : ℚ) : ℚ :=
  fC0 s * qC8 s + fC1 s * qC7 s + fC2 s * qC6 s + fC3 s * qC5 s + fC4 s * qC4 s + fC5 s * qC3 s
    + fC6 s * qC2 s + fC7 s * qC1 s + fC8 s * qC0 s

private theorem conv_coefficient_8 (s : ℚ) :
    convC8 s = nC8 s := by
  simp only [convC8, fC0, fC1, fC2, fC3, fC4, fC5, fC6, fC7, fC8, qC8, qC7, qC6, qC5, qC4, qC3, qC2,
    qC1, qC0, nC8]
  ring

private def convC9 (s : ℚ) : ℚ :=
  fC0 s * qC9 s + fC1 s * qC8 s + fC2 s * qC7 s + fC3 s * qC6 s + fC4 s * qC5 s + fC5 s * qC4 s
    + fC6 s * qC3 s + fC7 s * qC2 s + fC8 s * qC1 s + fC9 s * qC0 s

private theorem conv_coefficient_9 (s : ℚ) :
    convC9 s = nC9 s := by
  simp only [convC9, fC0, fC1, fC2, fC3, fC4, fC5, fC6, fC7, fC8, fC9, qC9, qC8, qC7, qC6, qC5, qC4,
    qC3, qC2, qC1, qC0, nC9]
  ring

private def convC10 (s : ℚ) : ℚ :=
  fC1 s * qC9 s + fC2 s * qC8 s + fC3 s * qC7 s + fC4 s * qC6 s + fC5 s * qC5 s + fC6 s * qC4 s
    + fC7 s * qC3 s + fC8 s * qC2 s + fC9 s * qC1 s + fC10 s * qC0 s

private theorem conv_coefficient_10 (s : ℚ) :
    convC10 s = nC10 s := by
  simp only [convC10, fC1, fC2, fC3, fC4, fC5, fC6, fC7, fC8, fC9, fC10, qC9, qC8, qC7, qC6, qC5,
    qC4, qC3, qC2, qC1, qC0, nC10]
  ring

private def convC11 (s : ℚ) : ℚ :=
  fC2 s * qC9 s + fC3 s * qC8 s + fC4 s * qC7 s + fC5 s * qC6 s + fC6 s * qC5 s + fC7 s * qC4 s
    + fC8 s * qC3 s + fC9 s * qC2 s + fC10 s * qC1 s

private theorem conv_coefficient_11 (s : ℚ) :
    convC11 s = nC11 s := by
  simp only [convC11, fC2, fC3, fC4, fC5, fC6, fC7, fC8, fC9, fC10, qC9, qC8, qC7, qC6, qC5, qC4,
    qC3, qC2, qC1, nC11]
  ring

private def convC12 (s : ℚ) : ℚ :=
  fC3 s * qC9 s + fC4 s * qC8 s + fC5 s * qC7 s + fC6 s * qC6 s + fC7 s * qC5 s + fC8 s * qC4 s
    + fC9 s * qC3 s + fC10 s * qC2 s

private theorem conv_coefficient_12 (s : ℚ) :
    convC12 s = nC12 s := by
  simp only [convC12, fC3, fC4, fC5, fC6, fC7, fC8, fC9, fC10, qC9, qC8, qC7, qC6, qC5, qC4, qC3,
    qC2, nC12]
  ring

private def convC13 (s : ℚ) : ℚ :=
  fC4 s * qC9 s + fC5 s * qC8 s + fC6 s * qC7 s + fC7 s * qC6 s + fC8 s * qC5 s + fC9 s * qC4 s
    + fC10 s * qC3 s

private theorem conv_coefficient_13 (s : ℚ) :
    convC13 s = nC13 s := by
  simp only [convC13, fC4, fC5, fC6, fC7, fC8, fC9, fC10, qC9, qC8, qC7, qC6, qC5, qC4, qC3, nC13]
  ring

private def convC14 (s : ℚ) : ℚ :=
  fC5 s * qC9 s + fC6 s * qC8 s + fC7 s * qC7 s + fC8 s * qC6 s + fC9 s * qC5 s + fC10 s * qC4 s

private theorem conv_coefficient_14 (s : ℚ) :
    convC14 s = nC14 s := by
  simp only [convC14, fC5, fC6, fC7, fC8, fC9, fC10, qC9, qC8, qC7, qC6, qC5, qC4, nC14]
  ring

private def convC15 (s : ℚ) : ℚ :=
  fC6 s * qC9 s + fC7 s * qC8 s + fC8 s * qC7 s + fC9 s * qC6 s + fC10 s * qC5 s

private theorem conv_coefficient_15 (s : ℚ) :
    convC15 s = nC15 s := by
  simp only [convC15, fC6, fC7, fC8, fC9, fC10, qC9, qC8, qC7, qC6, qC5, nC15]
  ring

private def convC16 (s : ℚ) : ℚ :=
  fC7 s * qC9 s + fC8 s * qC8 s + fC9 s * qC7 s + fC10 s * qC6 s

private theorem conv_coefficient_16 (s : ℚ) :
    convC16 s = nC16 s := by
  simp only [convC16, fC7, fC8, fC9, fC10, qC9, qC8, qC7, qC6, nC16]
  ring

private def convC17 (s : ℚ) : ℚ :=
  fC8 s * qC9 s + fC9 s * qC8 s + fC10 s * qC7 s

private theorem conv_coefficient_17 (s : ℚ) :
    convC17 s = nC17 s := by
  simp only [convC17, fC8, fC9, fC10, qC9, qC8, qC7, nC17]
  ring

private def convC18 (s : ℚ) : ℚ :=
  fC9 s * qC9 s + fC10 s * qC8 s

private theorem conv_coefficient_18 (s : ℚ) :
    convC18 s = nC18 s := by
  simp only [convC18, fC9, fC10, qC9, qC8, nC18]
  ring

private def convC19 (s : ℚ) : ℚ :=
  fC10 s * qC9 s

private theorem conv_coefficient_19 (s : ℚ) :
    convC19 s = nC19 s := by
  simp only [convC19, fC10, qC9, nC19]
  ring

private def convolution (r s : ℚ) : ℚ :=
  convC19 s * r ^ 19
    + convC18 s * r ^ 18
    + convC17 s * r ^ 17
    + convC16 s * r ^ 16
    + convC15 s * r ^ 15
    + convC14 s * r ^ 14
    + convC13 s * r ^ 13
    + convC12 s * r ^ 12
    + convC11 s * r ^ 11
    + convC10 s * r ^ 10
    + convC9 s * r ^ 9
    + convC8 s * r ^ 8
    + convC7 s * r ^ 7
    + convC6 s * r ^ 6
    + convC5 s * r ^ 5
    + convC4 s * r ^ 4
    + convC3 s * r ^ 3
    + convC2 s * r ^ 2
    + convC1 s * r
    + convC0 s

private theorem F_mul_Q_eq_convolution (r s : ℚ) :
    F r s * Q r s = convolution r s := by
  simp only [F, Q, convolution, convC0, convC1, convC2, convC3, convC4, convC5, convC6, convC7,
    convC8, convC9, convC10, convC11, convC12, convC13, convC14, convC15, convC16, convC17, convC18,
    convC19]
  ring

private theorem convolution_eq_numerator (r s : ℚ) :
    convolution r s = numerator r s := by
  simp only [convolution, numerator, conv_coefficient_0, conv_coefficient_1, conv_coefficient_2,
    conv_coefficient_3, conv_coefficient_4, conv_coefficient_5, conv_coefficient_6,
    conv_coefficient_7, conv_coefficient_8, conv_coefficient_9, conv_coefficient_10,
    conv_coefficient_11, conv_coefficient_12, conv_coefficient_13, conv_coefficient_14,
    conv_coefficient_15, conv_coefficient_16, conv_coefficient_17, conv_coefficient_18,
    conv_coefficient_19]

private theorem polynomial_certificate (r s : ℚ) :
    term0 r s + term1 r s = F r s * Q r s := by
  rw [terms_eq_numerator, F_mul_Q_eq_convolution, convolution_eq_numerator]

/-- Internal exact coefficient certificate consumed by the
actual-coordinate order-25 orbit proof. -/
theorem orderTwentyFiveUnitRelationFiveCertificate
    (r s : ℚ) (hs : s ≠ 0) (hA : A r s ≠ 0) (hC : C r s ≠ 0) (hD : D r s ≠ 0) (hE : E r s ≠ 0)
    (hL : L r s ≠ 0) (hJ : J r s ≠ 0) (hP6 : P6 r s ≠ 0) (hP9 : P9 r s ≠ 0)
    (hF : F r s = 0) :
    y1 r s * y2 r s * y4 r s * y8 r s * y9 r s - 1 = 0 := by
  have hpoly : term0 r s + term1 r s = 0 := by
    rw [polynomial_certificate, hF]
    ring
  simp only [y1, y2, y4, y8, y9]
  field_simp [hs, hA, hC, hD, hE, hL, hJ, hP6, hP9]
  simp only [term0, term1] at hpoly
  linear_combination hpoly

end MazurTorsion.Kubert.Internal
