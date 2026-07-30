/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentySevenLegs

/-!
# The trisection condition on the order-nine family

If a rational point of the parametrized `X₁(9)` family triples to the
marked origin, its abscissa is a root of the explicit trisection
polynomial

`T(f, ξ) = ξ·ψ₃(ξ)² - ψ₂²(ξ)·ω(ξ)`.

The proof composes the affine doubling and addition formulas and
eliminates the intermediate coordinates through staged certified
`linear_combination`s: the ordinate of the double is removed first,
the resulting eliminant is reduced modulo the curve equation to a
cubic in the abscissa of the double whose coefficients no longer
involve the ordinate, and the doubling relation clears that abscissa.
A final two-variable polynomial identity recognises the outcome as
`ψ₂² · T`; the two-division value `ψ₂²` is nonzero because the point
is not killed by two.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The two-division value `4ξ³ + b₂ξ² + 2b₄ξ + b₆` of the family. -/
def famTwoDivision (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f - 4) + 2 * ξ + 8) - 6 * ξ - 10) + ξ * (ξ + 8) + 8)
    + ξ * (-6 * ξ - 8) - 4) + ξ * (9 * ξ + 6) + 1) + ξ * (-10 * ξ - 4)) + ξ * (6 * ξ + 2))
    + ξ ^ 2 * (4 * ξ + 1)

/-- The trisection polynomial of the family: a point triples to an
abscissa-zero point only if this vanishes. -/
def trisectionPoly (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (
    f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 13) + 3 * ξ + 84) - 39 * ξ
    - 358) + ξ * (3 * ξ + 249) + 1126) + ξ * (-45 * ξ - 1044) - 2772) + ξ * (ξ * (ξ + 309) + 3231)
    + 5531) + ξ * (ξ * (-18 * ξ - 1341) - 7851) - 9143) + ξ * (ξ * (144 * ξ + 4200) + 15543) + 12696
    ) + ξ * (ξ * (-702 * ξ - 10182) - 25668) - 14932) + ξ * (ξ * (2426 * ξ + 19929) + 35898) + 14932
    ) + ξ * (ξ * (-6435 * ξ - 32373) - 42912) - 12696) + ξ * (ξ * (ξ * (12 * ξ + 13688) + 44478)
    + 44046) + 9143) + ξ * (ξ * (ξ * (-144 * ξ - 23955) - 52374) - 38838) - 5531) + ξ * (ξ * (ξ * (
    756 * ξ + 35022) + 53328) + 29313) + 2772) + ξ * (ξ * (ξ * (-2487 * ξ - 43163) - 47184) - 18783)
    - 1126) + ξ * (ξ * (ξ * (5853 * ξ + 45091) + 36297) + 10077) + 358) + ξ * (ξ * (ξ * (ξ * (-6 * ξ
    - 10476) - 40068) - 24159) - 4428) - 84) + ξ * (ξ * (ξ * (ξ * (90 * ξ + 14730) + 30372) + 13749)
    + 1539) + 13) + ξ * (ξ * (ξ * (ξ * (ξ * (-ξ - 426) - 16539) - 19699) - 6549) - 399) - 1) + ξ * (
    ξ * (ξ * (ξ * (ξ * (9 * ξ + 1164) + 14922) + 10962) + 2520) + 69)) + ξ * (ξ * (ξ * (ξ * (ξ * (
    -31 * ξ - 2166) - 10818) - 5227) - 738) - 6)) + ξ ^ 2 * (ξ * (ξ * (ξ * (65 * ξ + 2916) + 6279)
    + 2103) + 147)) + ξ ^ 2 * (ξ * (ξ * (ξ * (-123 * ξ - 2916) - 2916) - 681) - 15)) + ξ ^ 3 * (
    ξ * (ξ * (210 * ξ + 2166) + 1098) + 159)) + ξ ^ 3 * (ξ * (ξ * (ξ * (-6 * ξ - 297) - 1170) - 345)
    - 20)) + ξ ^ 4 * (ξ * (ξ * (18 * ξ + 321) + 444) + 90)) + ξ ^ 4 * (ξ * (ξ * (-24 * ξ - 243)
    - 114) - 15)) + ξ ^ 5 * (ξ * (24 * ξ + 122) + 24)) + ξ ^ 5 * (ξ * (-18 * ξ - 33) - 6))
    + ξ ^ 6 * (12 * ξ + 2)) + ξ ^ 6 * (-6 * ξ - 1)) + ξ ^ 9

/-- Curve-reduced numerator `ξ·ψ₂² - ψ₃` of the doubling abscissa. -/
private def trisU (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 6) + 18) - 35) + 48)
    - 2 * ξ - 48) + 8 * ξ + 35) + ξ * (-ξ - 16) - 18) + ξ * (3 * ξ + 20) + 6) + ξ * (-4 * ξ - 16)
    - 1) + ξ * (4 * ξ + 8)) + ξ * (-3 * ξ - 2)) + 2 * ξ ^ 2) - ξ ^ 2) + ξ ^ 4

/-- Quadratic coefficient of the curve-reduced tripling cubic. -/
private def trisA₂ (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 6) + 18) - 35) + 48) + ξ
    - 48) - 4 * ξ + 35) + ξ * (5 * ξ + 8) - 18) + ξ * (-15 * ξ - 10) + 6) + ξ * (ξ * (3 * ξ + 20)
    + 8) - 1) + ξ * (ξ * (-18 * ξ - 20) - 4)) + ξ * (ξ * (27 * ξ + 15) + 1)) + ξ ^ 2 * (-30 * ξ - 10
    )) + ξ ^ 2 * (18 * ξ + 5)) + ξ ^ 3 * (13 * ξ + 3)

/-- Linear coefficient of the curve-reduced tripling cubic. -/
private def trisA₁ (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 7) + 3 * ξ
    + 24) - 24 * ξ - 54) + ξ * (3 * ξ + 87) + 89) + ξ * (-27 * ξ - 204) - 114) + ξ * (ξ * (ξ + 93)
    + 348) + 118) + ξ * (ξ * (-12 * ξ - 195) - 450) - 101) + ξ * (ξ * (54 * ξ + 304) + 450) + 72)
    + ξ * (ξ * (-128 * ξ - 370) - 348) - 42) + ξ * (ξ * (225 * ξ + 371) + 207) + 19) + ξ * (ξ * (
    -288 * ξ - 313) - 96) - 6) + ξ * (ξ * (ξ * (7 * ξ + 258) + 209) + 36) + 1) + ξ * (ξ * (ξ * (
    -42 * ξ - 180) - 106) - 12)) + ξ * (ξ * (ξ * (63 * ξ + 90) + 34) + 3)) + ξ ^ 2 * (ξ * (-70 * ξ
    - 44) - 6)) + ξ ^ 2 * (ξ * (42 * ξ + 24) + 3)) + ξ ^ 3 * (ξ * (10 * ξ + 7) + 1)

/-- Constant coefficient of the curve-reduced tripling cubic. -/
private def trisA₀ (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f
    - 8) + 3 * ξ + 32) - 21 * ξ - 84) + ξ * (3 * ξ + 72) + 160) + ξ * (-21 * ξ - 162) - 232) + ξ * (
    ξ * (ξ + 69) + 267) + 262) + ξ * (ξ * (-9 * ξ - 150) - 342) - 232) + ξ * (ξ * (31 * ξ + 243)
    + 354) + 160) + ξ * (ξ * (-65 * ξ - 306) - 303) - 84) + ξ * (ξ * (100 * ξ + 306) + 216) + 32)
    + ξ * (ξ * (-118 * ξ - 243) - 126) - 8) + ξ * (ξ * (ξ * (ξ + 113) + 153) + 57) + 1) + ξ * (ξ * (
    ξ * (-3 * ξ - 91) - 78) - 18)) + ξ * (ξ * (ξ * (ξ * (-ξ + 4) + 59) + 33) + 3)) + ξ ^ 2 * (ξ * (
    ξ * (6 * ξ - 4) - 30) - 12)) + ξ ^ 2 * (ξ * (ξ * (-9 * ξ + 3) + 10) + 3)) + ξ ^ 3 * (ξ * (10 * ξ
    - 2) - 2)) + ξ ^ 3 * (ξ * (-6 * ξ + 1) + 1)) + ξ ^ 5 * (-3 * ξ - 1)

/-- Intermediate eliminant after removing the ordinate of the double. -/
private def trisG₁ (f ξ η x₂ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f
    - 8) + 3 * ξ + x₂ + 32) - 21 * ξ - 7 * x₂ - 84) + ξ * (3 * ξ + 3 * x₂ + 72) + 24 * x₂ + 160)
    + ξ * (-13 * ξ - 24 * x₂ - 162) - 8 * η + x₂ * (x₂ - 54) - 232) + ξ * (ξ * (ξ + 3 * x₂ + 21)
    + 87 * x₂ + 267) + 48 * η + x₂ * (-6 * x₂ + 89) + 262) + ξ * (ξ * (3 * ξ - 23 * x₂ - 6) - 20 * η
    - 204 * x₂ - 342) + η * (-4 * x₂ - 144) + x₂ * (18 * x₂ - 114) - 232) + ξ * (ξ * (ξ * (x₂ - 29)
    + 73 * x₂ - 37) + 100 * η + 348 * x₂ + 354) + η * (20 * x₂ + 280) + x₂ * (-35 * x₂ + 118) + 160)
    + ξ * (ξ * (ξ * (3 * ξ - 6 * x₂ + 79) - 15 * η + x₂ * (-x₂ - 147) + 78) + η * (-10 * x₂ - 240)
    - 450 * x₂ - 303) + η * (x₂ * (x₂ - 48) - 384) + x₂ * (48 * x₂ - 101) - 84) + ξ * (ξ * (ξ * (
    -8 * ξ + 6 * x₂ - 136) + 40 * η + x₂ * (8 * x₂ + 228) - 78) + η * (64 * x₂ + 380) + x₂ * (x₂
    + 450) + 216) + η * (24 * η + x₂ * (-8 * x₂ + 76) + 384) + x₂ * (x₂ * (-x₂ - 48) + 72) + 32)
    + ξ * (ξ * (ξ * (5 * ξ - 3 * η + 10 * x₂ + 178) + η * (-6 * x₂ - 25) + x₂ * (-23 * x₂ - 282)
    + 37) + η * (x₂ * (x₂ - 166) - 440) + x₂ * (-4 * x₂ - 348) - 126) + η * (-96 * η + x₂ * (23 * x₂
    - 88) - 280) + x₂ * (x₂ * (4 * x₂ + 35) - 42) - 8) + ξ * (ξ * (ξ * (-6 * ξ - 11 * η - 25 * x₂
    - 191) + η * (42 * x₂ - 25) + x₂ * (46 * x₂ + 291) + 9) + η * (44 * η + x₂ * (-7 * x₂ + 282)
    + 400) + x₂ * (x₂ * (-2 * x₂ + 8) + 207) + 57) + η * (η * (4 * x₂ + 192) + x₂ * (-41 * x₂ + 80)
    + 144) + x₂ * (x₂ * (-8 * x₂ - 18) + 19) + 1) + ξ * (ξ * (ξ * (23 * ξ + 51 * η + 24 * x₂ + 169)
    + η * (-90 * x₂ + 50) + x₂ * (-65 * x₂ - 253) - 30) + η * (-132 * η + x₂ * (15 * x₂ - 340) - 300
    ) + x₂ * (x₂ * (6 * x₂ - 10) - 96) - 18) + η * (η * (-12 * x₂ - 240) + x₂ * (50 * x₂ - 60) - 48)
    + x₂ * (x₂ * (10 * x₂ + 6) - 6)) + ξ * (ξ * (ξ * (ξ * (-4 * ξ + x₂ - 39) - 68 * η + x₂ * (4 * x₂
    - 4) - 113) + η * (19 * η + 120 * x₂ - 25) + x₂ * (x₂ * (-x₂ + 61) + 173) + 25) + η * (η * (
    6 * x₂ + 176) + x₂ * (-20 * x₂ + 282) + 180) + x₂ * (x₂ * (-8 * x₂ + 8) + 36) + 3) + η * (η * (
    x₂ * (-x₂ + 16) + 192) + x₂ * (-41 * x₂ + 36) + 8) + x₂ * (x₂ * (-8 * x₂ - 1) + 1)) + ξ * (ξ * (
    ξ * (ξ * (-4 * ξ + 22 * x₂ + 49) + 90 * η + x₂ * (-20 * x₂ - 26) + 50) + η * (-18 * η - 160 * x₂
    - 25) + x₂ * (x₂ * (2 * x₂ - 43) - 90) - 12) + η * (η * (-36 * x₂ - 176) + x₂ * (18 * x₂ - 166)
    - 80) + x₂ * (x₂ * (8 * x₂ - 4) - 12)) + η * (η * (-32 * η + x₂ * (6 * x₂ - 16) - 96) + x₂ * (
    x₂ * (4 * x₂ + 23) - 16)) + 4 * x₂ ^ 3) + ξ * (ξ * (ξ * (ξ * (20 * ξ - 47 * x₂ - 41) - 107 * η
    + x₂ * (28 * x₂ + 30) - 10) + η * (-21 * η + 146 * x₂ + 40) + x₂ * (x₂ * (-x₂ + 23) + 30) + 3)
    + η * (η * (54 * x₂ + 132) + x₂ * (-7 * x₂ + 64) + 20) + x₂ * (x₂ * (-6 * x₂ + 1) + 3)) + η * (
    η * (64 * η + x₂ * (-9 * x₂ + 12) + 24) + x₂ * (x₂ * (-8 * x₂ - 8) + 4)) - x₂ ^ 3) + ξ * (ξ * (
    ξ * (ξ * (-16 * ξ + 28 * η + 46 * x₂ + 28) + η * (-28 * x₂ + 87) + x₂ * (-32 * x₂ - 24) - 2)
    + η * (2 * η + x₂ * (-4 * x₂ - 122) - 30) + x₂ * (x₂ * (2 * x₂ - 12) - 6)) + η * (η * (-32 * η
    - 60 * x₂ - 88) + x₂ * (x₂ * (4 * x₂ + 3) - 20)) + 4 * x₂ ^ 3) + η * (η * (-64 * η + x₂ * (
    10 * x₂ - 8)) + x₂ ^ 2 * (8 * x₂ + 2))) + ξ * (ξ * (ξ * (ξ * (4 * ξ - 28 * η - 22 * x₂ - 14)
    + η * (28 * x₂ - 39) + x₂ * (20 * x₂ + 14) + 1) + η * (18 * η + x₂ * (4 * x₂ + 70) + 15)
    + x₂ * (x₂ * (-2 * x₂ + 6) + 3)) + η * (η * (32 * η + 36 * x₂ + 44) + x₂ * (x₂ * (-4 * x₂ - 3)
    + 10)) - 2 * x₂ ^ 3) + η * (η * (32 * η + x₂ * (-6 * x₂ + 4)) + x₂ ^ 2 * (-4 * x₂ - 1))) + ξ * (
    ξ * (ξ * (ξ * (ξ * (9 * ξ - 18 * x₂ - 4) - 28 * η + x₂ * (9 * x₂ + 1)) + η * (-28 * η + 28 * x₂
    + 3) + x₂ * (4 * x₂ + 1)) + η * (η * (28 * x₂ + 19) + x₂ * (4 * x₂ + 6)) - x₂ ^ 3) + η * (η * (
    32 * η + x₂ * (4 * x₂ + 6)) + x₂ ^ 2 * (-4 * x₂ - 1))) + η ^ 2 * (16 * η ^ 2 + x₂ ^ 2 * (-4 * x₂
    - 1))

private lemma tris_stage₁ (f ξ η x₂ y₂ : ℚ)
    (hH2 : y₂ * (2 * η + (1 - nineC f) * ξ - nineB f) +
        (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) * (x₂ - ξ) +
        (η + (1 - nineC f) * x₂ - nineB f) *
          (2 * η + (1 - nineC f) * ξ - nineB f) = 0)
    (hH3 : (y₂ - η) ^ 2 +
        (1 - nineC f) * (y₂ - η) * (x₂ - ξ) -
        (-(nineB f) + x₂ + ξ) * (x₂ - ξ) ^ 2 = 0) :
    trisG₁ f ξ η x₂ = 0 := by
  unfold trisG₁
  simp only [nineB, nineC] at hH2 hH3
  linear_combination
    (2 * η + (1 - f ^ 2 * (f - 1)) * ξ - f ^ 2 * (f - 1) * (f ^ 2 - f + 1)) ^ 2 * hH3 -
    (f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (-f + 4) - 2 * ξ - 8) + 6 * ξ + 10) + ξ * (-ξ - 8)
      - 8) + ξ * (2 * x₂ + 8) + 5 * η - y₂ + 4) + ξ * (3 * ξ - 4 * x₂ - 6) - 10 * η + 2 * y₂
      - 1) + ξ * (-2 * ξ + 6 * η + 4 * x₂ - y₂ + 4) + η * (-x₂ + 10) - 2 * y₂) + ξ * (-6 * η
      - 2 * x₂ + y₂ - 2) + η * (x₂ - 5) + y₂) + ξ * (ξ * (3 * ξ - 3 * x₂ - 1) - 6 * η + y₂)
      + η * (-6 * η + x₂ + 2 * y₂)) * hH2

private lemma tris_reduce (f ξ η x₂ : ℚ)
    (hG1 : trisG₁ f ξ η x₂ = 0)
    (hcurve : η ^ 2 + (1 - nineC f) * ξ * η - nineB f * η -
        ξ ^ 3 + nineB f * ξ ^ 2 = 0) :
    -famTwoDivision f ξ * x₂ ^ 3 + trisA₂ f ξ * x₂ ^ 2 + trisA₁ f ξ * x₂ +
      trisA₀ f ξ = 0 := by
  unfold trisG₁ at hG1
  unfold famTwoDivision trisA₂ trisA₁ trisA₀
  simp only [nineB, nineC] at hcurve
  linear_combination hG1 -
    (f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (8 * f - 32) + 12 * ξ + 4 * x₂ + 64) - 36 * ξ
      - 12 * x₂ - 80) + ξ * (3 * ξ + 6 * x₂ + 48) + x₂ * (-x₂ + 16) + 64) + ξ * (-2 * ξ
      - 36 * x₂ - 48) - 16 * η + x₂ * (6 * x₂ - 16) - 32) + ξ * (-5 * ξ + 54 * x₂ + 36)
      + 32 * η + x₂ * (-9 * x₂ + 12) + 8) + ξ * (2 * ξ - 16 * η - 60 * x₂ - 24) - 32 * η
      + x₂ * (10 * x₂ - 8)) + ξ * (2 * ξ + 16 * η + 36 * x₂ + 12) + 16 * η + x₂ * (-6 * x₂
      + 4)) + ξ * (ξ * (-12 * ξ + 28 * x₂ + 3) + 16 * η + x₂ * (4 * x₂ + 6)) + 16 * η ^ 2
      + x₂ ^ 2 * (-4 * x₂ - 1)) * hcurve

private lemma tris_hx (f ξ η x₂ : ℚ)
    (hH1 : x₂ * (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2 =
        (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) ^ 2 +
        (1 - nineC f) *
          (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
            2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) *
          (2 * η + (1 - nineC f) * ξ - nineB f) -
        (-(nineB f) + 2 * ξ) *
          (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2)
    (hcurve : η ^ 2 + (1 - nineC f) * ξ * η - nineB f * η -
        ξ ^ 3 + nineB f * ξ ^ 2 = 0) :
    x₂ * famTwoDivision f ξ = trisU f ξ := by
  unfold famTwoDivision trisU
  simp only [nineB, nineC] at hH1 hcurve
  linear_combination hH1 +
    (f ^ 2 * (f * (f * (f * (-f + 6) - 9) + 10) - 6) - 8 * ξ - 4 * x₂ - 1) * hcurve

private lemma tris_cubic_elim (A₂ A₁ A₀ E U x₂ : ℚ)
    (h : -E * x₂ ^ 3 + A₂ * x₂ ^ 2 + A₁ * x₂ + A₀ = 0)
    (hx : x₂ * E = U) :
    -U ^ 3 + A₂ * U ^ 2 + A₁ * U * E + A₀ * E ^ 2 = 0 := by
  linear_combination E ^ 2 * h +
    ((x₂ * E) ^ 2 + x₂ * E * U + U ^ 2 - A₂ * (x₂ * E + U) - A₁ * E) * hx

private lemma tris_main_identity (f ξ : ℚ) :
    -trisU f ξ ^ 3 + trisA₂ f ξ * trisU f ξ ^ 2 +
      trisA₁ f ξ * trisU f ξ * famTwoDivision f ξ +
      trisA₀ f ξ * famTwoDivision f ξ ^ 2 =
    famTwoDivision f ξ * trisectionPoly f ξ := by
  unfold trisU trisA₂ trisA₁ trisA₀ famTwoDivision trisectionPoly
  ring

/-- Tripling to the marked origin forces the trisection polynomial to
vanish. -/
theorem trisectionPoly_eq_zero_of_three_nsmul
    (f ξ η : ℚ)
    (hQ : (tateNormalCurve (nineB f) (nineC f)).toAffine.Nonsingular ξ η)
    (h00 : (tateNormalCurve (nineB f)
      (nineC f)).toAffine.Nonsingular 0 0)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some ξ η hQ :
        (tateNormalCurve (nineB f) (nineC f)).toAffine.Point) = 27)
    (h3Q : (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some ξ η hQ :
          (tateNormalCurve (nineB f) (nineC f)).toAffine.Point) =
      WeierstrassCurve.Affine.Point.some 0 0 h00) :
    trisectionPoly f ξ = 0 := by
  set P : (tateNormalCurve (nineB f) (nineC f)).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some ξ η hQ with hP
  -- the curve equation
  have hcurve : η ^ 2 + (1 - nineC f) * ξ * η - nineB f * η -
      ξ ^ 3 + nineB f * ξ ^ 2 = 0 := by
    have heq := hQ.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    simp only [tateNormalCurve_a₁, tateNormalCurve_a₂, tateNormalCurve_a₃,
      tateNormalCurve_a₄, tateNormalCurve_a₆] at heq
    linear_combination heq
  -- the point is not killed by two
  have hden : 2 * η + (1 - nineC f) * ξ - nineB f ≠ 0 := by
    intro hzero
    have hvert : η = (tateNormalCurve (nineB f)
        (nineC f)).toAffine.negY ξ η := by
      simp only [WeierstrassCurve.Affine.negY, tateNormalCurve_a₁,
        tateNormalCurve_a₃]
      linarith
    have h2P : P + P = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hvert
    have h2P' : (2 : ℕ) • P = 0 := by
      rw [two_nsmul]
      exact h2P
    have := addOrderOf_dvd_of_nsmul_eq_zero h2P'
    rw [horder] at this
    omega
  have hvertne : η ≠ (tateNormalCurve (nineB f)
      (nineC f)).toAffine.negY ξ η := by
    intro hvert
    apply hden
    simp only [WeierstrassCurve.Affine.negY, tateNormalCurve_a₁,
      tateNormalCurve_a₃] at hvert
    linarith
  -- doubling data
  have hslope₁ : (tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η =
      (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) /
        (2 * η + (1 - nineC f) * ξ - nineB f) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hvertne]
    simp only [WeierstrassCurve.Affine.negY, tateNormalCurve_a₁,
      tateNormalCurve_a₂, tateNormalCurve_a₃, tateNormalCurve_a₄,
      nineB, nineC]
    ring
  have hS : (tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η *
      (2 * η + (1 - nineC f) * ξ - nineB f) =
      -2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
        2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η := by
    rw [hslope₁]
    exact div_mul_cancel₀ _ hden
  set x₂ : ℚ := (tateNormalCurve (nineB f) (nineC f)).toAffine.addX ξ ξ
    ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η) with hx₂def
  set y₂ : ℚ := (tateNormalCurve (nineB f) (nineC f)).toAffine.addY ξ ξ η
    ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η) with hy₂def
  have hdouble : P + P =
      WeierstrassCurve.Affine.Point.some x₂ y₂
        (WeierstrassCurve.Affine.nonsingular_add hQ hQ
          (fun hc ↦ hvertne hc.2)) := by
    rw [hP]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hvertne
  -- coordinates of the double, with the slope kept atomic
  have hx₂val : x₂ =
      (tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η ^ 2 +
        (1 - nineC f) *
          (tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η +
        nineB f - 2 * ξ := by
    rw [hx₂def, WeierstrassCurve.Affine.addX]
    simp only [tateNormalCurve_a₁, tateNormalCurve_a₂]
    ring
  have hy₂val : y₂ =
      -((tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η *
          (x₂ - ξ) + η) -
        (1 - nineC f) * x₂ + nineB f := by
    rw [hy₂def, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, ← hx₂def]
    simp only [WeierstrassCurve.Affine.negY, tateNormalCurve_a₁,
      tateNormalCurve_a₃]
    ring
  -- cleared coordinates of the double
  have hH1 : x₂ * (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2 =
      (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
        2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) ^ 2 +
      (1 - nineC f) *
        (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) *
        (2 * η + (1 - nineC f) * ξ - nineB f) -
      (-(nineB f) + 2 * ξ) *
        (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2 := by
    rw [hx₂val]
    linear_combination
      ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η *
          (2 * η + (1 - nineC f) * ξ - nineB f) +
        (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) +
        (1 - nineC f) * (2 * η + (1 - nineC f) * ξ - nineB f)) * hS
  have hH2 : y₂ * (2 * η + (1 - nineC f) * ξ - nineB f) +
      (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
        2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) * (x₂ - ξ) +
      (η + (1 - nineC f) * x₂ - nineB f) *
        (2 * η + (1 - nineC f) * ξ - nineB f) = 0 := by
    rw [hy₂val]
    linear_combination (-(x₂ - ξ)) * hS
  -- the double is distinct in abscissa from the point
  have hxne : x₂ ≠ ξ := by
    intro hxeq
    have hPP : P + P = P ∨ P + P = -P := by
      rw [hdouble]
      apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
      simpa using hxeq
    rcases hPP with h | h
    · have hP0 : P = 0 := add_right_cancel (h.trans (zero_add P).symm)
      exact WeierstrassCurve.Affine.Point.some_ne_zero hQ (hP ▸ hP0)
    · have h3 : (3 : ℕ) • P = 0 := by
        rw [show (3 : ℕ) • P = P + P + P by abel, h]
        abel
      rw [h3Q] at h3
      exact WeierstrassCurve.Affine.Point.some_ne_zero h00 h3
  -- the triple has abscissa zero
  have hH3 : (y₂ - η) ^ 2 +
      (1 - nineC f) * (y₂ - η) * (x₂ - ξ) -
      (-(nineB f) + x₂ + ξ) * (x₂ - ξ) ^ 2 = 0 := by
    have hxne' : x₂ - ξ ≠ 0 := sub_ne_zero.mpr hxne
    have hS₂ : (tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η *
        (x₂ - ξ) = y₂ - η := by
      rw [WeierstrassCurve.Affine.slope_of_X_ne hxne]
      exact div_mul_cancel₀ _ hxne'
    have htriple : (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some
          ((tateNormalCurve (nineB f) (nineC f)).toAffine.addX x₂ ξ
            ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η))
          ((tateNormalCurve (nineB f) (nineC f)).toAffine.addY x₂ ξ y₂
            ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η))
          (WeierstrassCurve.Affine.nonsingular_add
            (WeierstrassCurve.Affine.nonsingular_add hQ hQ
              (fun hc ↦ hvertne hc.2)) hQ
            (fun hc ↦ hxne hc.1)) := by
      rw [show (3 : ℕ) • P = P + P + P by abel, hdouble]
      exact WeierstrassCurve.Affine.Point.add_of_X_ne hxne
    rw [h3Q] at htriple
    have hx3 : (tateNormalCurve (nineB f) (nineC f)).toAffine.addX x₂ ξ
        ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η) =
        0 := by
      have := (WeierstrassCurve.Affine.Point.some.injEq
        _ _ _ _ _ _).mp htriple.symm
      exact this.1
    rw [WeierstrassCurve.Affine.addX] at hx3
    simp only [tateNormalCurve_a₁, tateNormalCurve_a₂] at hx3
    linear_combination (x₂ - ξ) ^ 2 * hx3 -
      (y₂ - η +
        (tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η *
          (x₂ - ξ) +
        (1 - nineC f) * (x₂ - ξ)) * hS₂
  -- eliminate the double through the staged certificates
  have hG1 := tris_stage₁ f ξ η x₂ y₂ hH2 hH3
  have hred := tris_reduce f ξ η x₂ hG1 hcurve
  have hx := tris_hx f ξ η x₂ hH1 hcurve
  have hcube := tris_cubic_elim (trisA₂ f ξ) (trisA₁ f ξ) (trisA₀ f ξ)
    (famTwoDivision f ξ) (trisU f ξ) x₂ hred hx
  have key : famTwoDivision f ξ * trisectionPoly f ξ = 0 :=
    (tris_main_identity f ξ).symm.trans hcube
  -- the two-division value is nonzero
  have hE2 : famTwoDivision f ξ ≠ 0 := by
    have hsq : famTwoDivision f ξ =
        (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2 -
          4 * (η ^ 2 + (1 - nineC f) * ξ * η - nineB f * η -
            ξ ^ 3 + nineB f * ξ ^ 2) := by
      unfold famTwoDivision
      simp only [nineB, nineC]
      ring
    rw [hsq, hcurve, mul_zero, sub_zero]
    exact pow_ne_zero 2 hden
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hE2
  · exact h

end MazurTorsion.Kubert
