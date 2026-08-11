/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawOrbitFactors

/-!
# Shared semantic data for the fifth raw order-25 orbit relation

This is the small cross-module interface for the split RelationFour
certificate. The aggregate coefficient expressions are mechanically preserved
from the frozen monolith with SHA-256
`06dbf703610c933644c83d7fbd34aaabe7b3757f7e0812bc8167cf068d903b46`.
Generated coefficient rows are exposed only through aggregate functions.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

def A (r s : ℚ) : ℚ :=
  r
  - s

def B (_r s : ℚ) : ℚ :=
  s
  - 1

def C (r s : ℚ) : ℚ :=
  r * s
  - 2 * r
  + 1

def K (r s : ℚ) : ℚ :=
  r
  - s ^ 2
  + s
  - 1

def D (r s : ℚ) : ℚ :=
  r ^ 2
  - r * s ^ 3
  + 3 * r * s ^ 2
  - 4 * r * s
  + s

def E (r s : ℚ) : ℚ :=
  r ^ 2 * s
  - 3 * r ^ 2
  + r * s
  + 3 * r
  - s ^ 2
  - 1

def G (r s : ℚ) : ℚ :=
  r * s ^ 2
  - 3 * r * s
  + r
  + s ^ 2

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

def P6 (r s : ℚ) : ℚ :=
  D r s ^ 2 * A r s * K r s -
    C r s ^ 2 * s * B r s * G r s * E r s

def P9 (r s : ℚ) : ℚ :=
  D r s ^ 3 * L r s - r * s * B r s ^ 3 * G r s * E r s ^ 3

def y1 (r s : ℚ) : ℚ :=
  C r s * L r s * J r s / (r * B r s ^ 2 * K r s ^ 2 * E r s ^ 2)

def y2 (r s : ℚ) : ℚ :=
  -(r * B r s ^ 3 * C r s * K r s * M r s) / (A r s ^ 2 * P6 r s)

def y4 (r s : ℚ) : ℚ :=
  -(r * A r s * B r s * K r s ^ 2 * E r s * T r s) /
    (C r s * D r s ^ 2 * J r s)

def y8 (r s : ℚ) : ℚ :=
  -(A r s * B r s * E r s) / L r s

def y9 (r s : ℚ) : ℚ :=
  -(K r s * D r s * M r s * N r s) / (s * A r s * C r s ^ 2 * P9 r s)


def term0 (r s : ℚ) : ℚ :=
  -B r s * C r s ^ 3 * D r s ^ 2 * E r s * J r s * K r s * L r s * M r s * N r s * P9 r s * s


def term1 (r s : ℚ) : ℚ :=
  A r s ^ 2 * B r s ^ 2 * C r s ^ 5 * D r s * E r s ^ 2 * J r s * P9 r s ^ 2 * s ^ 2


def term2 (r s : ℚ) : ℚ :=
  -A r s * C r s ^ 3 * J r s * K r s * L r s ^ 2 * M r s * N r s * P9 r s * T r s * s


def term3 (r s : ℚ) : ℚ :=
  -B r s ^ 2 * D r s * E r s ^ 2 * K r s ^ 4 * L r s * M r s ^ 2 * N r s ^ 2 * T r s * r


def fCoefficient (n : Nat) (s : ℚ) : ℚ :=
  match n with
  | 0 => s ^ 10
  | 1 =>
      6 * s ^ 10
        - 28 * s ^ 9
        + 21 * s ^ 8
        - 15 * s ^ 7
        + 10 * s ^ 6
        - 6 * s ^ 5
        + 3 * s ^ 4
        - s ^ 3
  | 2 =>
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
  | 3 =>
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
  | 4 =>
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
  | 5 =>
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
  | 6 =>
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
  | 7 =>
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
  | 8 =>
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
  | 9 =>
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
  | 10 => 1
  | _ => 0

def evalEleven (c : Nat → ℚ) (r : ℚ) : ℚ :=
  c 10 * r ^ 10
    + c 9 * r ^ 9
    + c 8 * r ^ 8
    + c 7 * r ^ 7
    + c 6 * r ^ 6
    + c 5 * r ^ 5
    + c 4 * r ^ 4
    + c 3 * r ^ 3
    + c 2 * r ^ 2
    + c 1 * r
    + c 0

def evalTwentyFive (c : Nat → ℚ) (r : ℚ) : ℚ :=
  c 24 * r ^ 24
    + c 23 * r ^ 23
    + c 22 * r ^ 22
    + c 21 * r ^ 21
    + c 20 * r ^ 20
    + c 19 * r ^ 19
    + c 18 * r ^ 18
    + c 17 * r ^ 17
    + c 16 * r ^ 16
    + c 15 * r ^ 15
    + c 14 * r ^ 14
    + c 13 * r ^ 13
    + c 12 * r ^ 12
    + c 11 * r ^ 11
    + c 10 * r ^ 10
    + c 9 * r ^ 9
    + c 8 * r ^ 8
    + c 7 * r ^ 7
    + c 6 * r ^ 6
    + c 5 * r ^ 5
    + c 4 * r ^ 4
    + c 3 * r ^ 3
    + c 2 * r ^ 2
    + c 1 * r
    + c 0

def evalThirtyFive (c : Nat → ℚ) (r : ℚ) : ℚ :=
  c 34 * r ^ 34
    + c 33 * r ^ 33
    + c 32 * r ^ 32
    + c 31 * r ^ 31
    + c 30 * r ^ 30
    + c 29 * r ^ 29
    + c 28 * r ^ 28
    + c 27 * r ^ 27
    + c 26 * r ^ 26
    + c 25 * r ^ 25
    + c 24 * r ^ 24
    + c 23 * r ^ 23
    + c 22 * r ^ 22
    + c 21 * r ^ 21
    + c 20 * r ^ 20
    + c 19 * r ^ 19
    + c 18 * r ^ 18
    + c 17 * r ^ 17
    + c 16 * r ^ 16
    + c 15 * r ^ 15
    + c 14 * r ^ 14
    + c 13 * r ^ 13
    + c 12 * r ^ 12
    + c 11 * r ^ 11
    + c 10 * r ^ 10
    + c 9 * r ^ 9
    + c 8 * r ^ 8
    + c 7 * r ^ 7
    + c 6 * r ^ 6
    + c 5 * r ^ 5
    + c 4 * r ^ 4
    + c 3 * r ^ 3
    + c 2 * r ^ 2
    + c 1 * r
    + c 0

def F (r s : ℚ) : ℚ :=
  evalEleven (fun n => fCoefficient n s) r

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal
