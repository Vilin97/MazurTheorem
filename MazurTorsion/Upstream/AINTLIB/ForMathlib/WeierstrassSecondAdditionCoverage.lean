/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The AINTLIB Authors

This file selectively adapts declarations from AINTLIB's
`EllipticCurve/AdditionLaw.lean`, `AdditionLawField.lean`, and
`AdditionLawOnCurve.lean`, exact source blobs
`c6ea88db42629fd166902494bb5617d4511e309b`,
`2d2dedf5639d707f9dda0a0e26a25a123b842c0d`, and
`6cdd1aa98921c9fbf607b855e3243de316fdca6d`. The source blobs are present at
AINTLIB's Apache-2.0 licensed default commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.WeierstrassSecondAdditionLaw
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point

/-!
# Coverage by the two Bosma–Lenstra addition laws

The three certified cross-minors identify the two addition triples wherever
both are defined. Over a field, they imply that the second triple lies on the
curve; the two triples are jointly nonzero on nonsingular inputs. The final
endpoint records both on-curve statements and joint nonvanishing for an
elliptic Weierstrass curve. Scheme-level gluing remains downstream.
-/

local notation3 "x" => (0 : Fin 3)
local notation3 "y" => (1 : Fin 3)
local notation3 "z" => (2 : Fin 3)

namespace WeierstrassCurve.Projective

local macro "law_simp" : tactic =>
  `(tactic| simp only [addX, addY, negAddY, addZ, dblAddX, dblAddY, dblAddZ, dblX, dblY,
    negDblY, dblZ, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons])

section CrossMinors

variable {R : Type*} [CommRing R] {W' : Projective R}

/-- The `XY` cross-minor of the two addition laws vanishes on curve points. -/
lemma addX_mul_dblAddY {P Q : Fin 3 → R}
    (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * W'.dblAddY P Q = W'.addY P Q * W'.dblAddX P Q := by
  linear_combination (norm := (law_simp; ring1))
    (
    -W'.a₁ ^ 2 * W'.a₂ * P x * Q x ^ 4 + 3 * W'.a₁ * W'.a₃ * P x * Q x ^ 4 - W'.a₂ ^ 2 * P x *
      Q x ^ 4 - 3 * W'.a₄ * P x * Q x ^ 4 - 3 * W'.a₁ * W'.a₂ * P x * Q x ^ 3 * Q y + 3 *
      W'.a₃ * P x * Q x ^ 3 * Q y - W'.a₁ ^ 3 * W'.a₃ * P x * Q x ^ 3 * Q z - W'.a₁ ^ 2 *
      W'.a₄ * P x * Q x ^ 3 * Q z - W'.a₁ * W'.a₂ * W'.a₃ * P x * Q x ^ 3 * Q z - 7 * W'.a₂ *
      W'.a₄ * P x * Q x ^ 3 * Q z - 3 * W'.a₃ ^ 2 * P x * Q x ^ 3 * Q z - 9 * W'.a₆ * P x * Q
      x ^ 3 * Q z - 3 * W'.a₂ * P x * Q x ^ 2 * Q y ^ 2 - 6 * W'.a₁ ^ 2 * W'.a₃ * P x * Q x ^
      2 * Q y * Q z - 3 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * P x * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₁ * W'.a₃
      * W'.a₄ * P x * Q x ^ 2 * Q z ^ 2 - 6 * W'.a₂ * W'.a₃ ^ 2 * P x * Q x ^ 2 * Q z ^ 2 - 18
      * W'.a₂ * W'.a₆ * P x * Q x ^ 2 * Q z ^ 2 - 6 * W'.a₄ ^ 2 * P x * Q x ^ 2 * Q z ^ 2 - 9
      * W'.a₁ * W'.a₃ * P x * Q x * Q y ^ 2 * Q z - 3 * W'.a₁ * W'.a₃ ^ 2 * P x * Q x * Q y *
      Q z ^ 2 + 9 * W'.a₁ * W'.a₆ * P x * Q x * Q y * Q z ^ 2 + 3 * W'.a₃ * W'.a₄ * P x * Q x
      * Q y * Q z ^ 2 - W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P x * Q x * Q z ^ 3 + W'.a₁ * W'.a₂ *
      W'.a₃ * W'.a₄ * P x * Q x * Q z ^ 3 - 3 * W'.a₁ * W'.a₃ ^ 3 * P x * Q x * Q z ^ 3 - 6 *
      W'.a₁ * W'.a₃ * W'.a₆ * P x * Q x * Q z ^ 3 - W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * Q x * Q z ^
      3 - 4 * W'.a₂ ^ 2 * W'.a₆ * P x * Q x * Q z ^ 3 + W'.a₂ * W'.a₄ ^ 2 * P x * Q x * Q z ^
      3 - 6 * W'.a₃ ^ 2 * W'.a₄ * P x * Q x * Q z ^ 3 - 21 * W'.a₄ * W'.a₆ * P x * Q x * Q z ^
      3 - 3 * W'.a₃ * P x * Q y ^ 3 * Q z + 9 * W'.a₆ * P x * Q y ^ 2 * Q z ^ 2 + 3 * W'.a₃ ^
      3 * P x * Q y * Q z ^ 3 + 12 * W'.a₃ * W'.a₆ * P x * Q y * Q z ^ 3 - W'.a₁ ^ 3 * W'.a₃ *
      W'.a₆ * P x * Q z ^ 4 + W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * P x * Q z ^ 4 - W'.a₁ ^ 2 *
      W'.a₄ * W'.a₆ * P x * Q z ^ 4 - W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * P x * Q z ^ 4 - 4 * W'.a₁ *
      W'.a₂ * W'.a₃ * W'.a₆ * P x * Q z ^ 4 + 2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P x * Q z ^ 4 -
      W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P x * Q z ^ 4 - 4 * W'.a₂ * W'.a₄ * W'.a₆ * P x * Q z ^ 4 -
      3 * W'.a₃ ^ 2 * W'.a₆ * P x * Q z ^ 4 + W'.a₄ ^ 3 * P x * Q z ^ 4 - 9 * W'.a₆ ^ 2 * P x
      * Q z ^ 4 + W'.a₁ ^ 3 * P y * Q x ^ 4 + W'.a₁ * W'.a₂ * P y * Q x ^ 4 + 4 * W'.a₁ ^ 2 *
      P y * Q x ^ 3 * Q y + W'.a₂ * P y * Q x ^ 3 * Q y + 3 * W'.a₁ ^ 2 * W'.a₃ * P y * Q x ^
      3 * Q z + 3 * W'.a₁ * W'.a₄ * P y * Q x ^ 3 * Q z + 6 * W'.a₁ * P y * Q x ^ 2 * Q y ^ 2
      + 6 * W'.a₁ * W'.a₃ * P y * Q x ^ 2 * Q y * Q z + 3 * W'.a₄ * P y * Q x ^ 2 * Q y * Q z
      + 3 * W'.a₁ * W'.a₃ ^ 2 * P y * Q x ^ 2 * Q z ^ 2 + 9 * W'.a₁ * W'.a₆ * P y * Q x ^ 2 *
      Q z ^ 2 + 3 * P y * Q x * Q y ^ 3 + 3 * W'.a₃ * P y * Q x * Q y ^ 2 * Q z + 3 * W'.a₃ ^
      2 * P y * Q x * Q y * Q z ^ 2 + 9 * W'.a₆ * P y * Q x * Q y * Q z ^ 2 + W'.a₁ ^ 3 *
      W'.a₆ * P y * Q x * Q z ^ 3 - W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * Q x * Q z ^ 3 + W'.a₁ *
      W'.a₂ * W'.a₃ ^ 2 * P y * Q x * Q z ^ 3 + 4 * W'.a₁ * W'.a₂ * W'.a₆ * P y * Q x * Q z ^
      3 - W'.a₁ * W'.a₄ ^ 2 * P y * Q x * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₆ * P y * Q y * Q z ^ 3 -
      W'.a₁ * W'.a₃ * W'.a₄ * P y * Q y * Q z ^ 3 + W'.a₂ * W'.a₃ ^ 2 * P y * Q y * Q z ^ 3 +
      4 * W'.a₂ * W'.a₆ * P y * Q y * Q z ^ 3 - W'.a₄ ^ 2 * P y * Q y * Q z ^ 3 - W'.a₁ ^ 2 *
      W'.a₄ * P z * Q x ^ 4 - W'.a₂ * W'.a₄ * P z * Q x ^ 4 - 3 * W'.a₁ * W'.a₄ * P z * Q x ^
      3 * Q y - W'.a₁ ^ 2 * W'.a₃ ^ 2 * P z * Q x ^ 3 * Q z - 3 * W'.a₁ ^ 2 * W'.a₆ * P z * Q
      x ^ 3 * Q z - 3 * W'.a₁ * W'.a₃ * W'.a₄ * P z * Q x ^ 3 * Q z - W'.a₂ * W'.a₃ ^ 2 * P z
      * Q x ^ 3 * Q z - 3 * W'.a₂ * W'.a₆ * P z * Q x ^ 3 * Q z - 3 * W'.a₄ ^ 2 * P z * Q x ^
      3 * Q z - 3 * W'.a₄ * P z * Q x ^ 2 * Q y ^ 2 - 3 * W'.a₁ * W'.a₃ ^ 2 * P z * Q x ^ 2 *
      Q y * Q z - 9 * W'.a₁ * W'.a₆ * P z * Q x ^ 2 * Q y * Q z - 3 * W'.a₃ * W'.a₄ * P z * Q
      x ^ 2 * Q y * Q z - 3 * W'.a₁ * W'.a₃ ^ 3 * P z * Q x ^ 2 * Q z ^ 2 - 9 * W'.a₁ * W'.a₃
      * W'.a₆ * P z * Q x ^ 2 * Q z ^ 2 - 6 * W'.a₃ ^ 2 * W'.a₄ * P z * Q x ^ 2 * Q z ^ 2 - 18
      * W'.a₄ * W'.a₆ * P z * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₃ ^ 2 * P z * Q x * Q y ^ 2 * Q z -
      9 * W'.a₆ * P z * Q x * Q y ^ 2 * Q z - 3 * W'.a₃ ^ 3 * P z * Q x * Q y * Q z ^ 2 - 9 *
      W'.a₃ * W'.a₆ * P z * Q x * Q y * Q z ^ 2 - W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P z * Q x * Q z
      ^ 3 + W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z * Q x * Q z ^ 3 - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z
      * Q x * Q z ^ 3 - 4 * W'.a₂ * W'.a₄ * W'.a₆ * P z * Q x * Q z ^ 3 - 3 * W'.a₃ ^ 4 * P z
      * Q x * Q z ^ 3 - 18 * W'.a₃ ^ 2 * W'.a₆ * P z * Q x * Q z ^ 3 + W'.a₄ ^ 3 * P z * Q x *
      Q z ^ 3 - 27 * W'.a₆ ^ 2 * P z * Q x * Q z ^ 3 - W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₆ * P z * Q
      z ^ 4 - 3 * W'.a₁ ^ 2 * W'.a₆ ^ 2 * P z * Q z ^ 4 + W'.a₁ * W'.a₃ ^ 3 * W'.a₄ * P z * Q
      z ^ 4 + 3 * W'.a₁ * W'.a₃ * W'.a₄ * W'.a₆ * P z * Q z ^ 4 - W'.a₂ * W'.a₃ ^ 4 * P z * Q
      z ^ 4 - 7 * W'.a₂ * W'.a₃ ^ 2 * W'.a₆ * P z * Q z ^ 4 - 12 * W'.a₂ * W'.a₆ ^ 2 * P z * Q
      z ^ 4 + W'.a₃ ^ 2 * W'.a₄ ^ 2 * P z * Q z ^ 4 + 3 * W'.a₄ ^ 2 * W'.a₆ * P z * Q z ^ 4
    ) * (equation_iff P).mp hP + (
    W'.a₁ ^ 2 * W'.a₂ * P x ^ 4 * Q x - 3 * W'.a₁ * W'.a₃ * P x ^ 4 * Q x + W'.a₂ ^ 2 * P x ^
      4 * Q x + 3 * W'.a₄ * P x ^ 4 * Q x - 3 * W'.a₃ * P x ^ 4 * Q y + W'.a₁ ^ 3 * W'.a₃ * P
      x ^ 4 * Q z + W'.a₁ ^ 2 * W'.a₄ * P x ^ 4 * Q z + W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 4 * Q z
      + W'.a₂ * W'.a₄ * P x ^ 4 * Q z + 3 * W'.a₃ ^ 2 * P x ^ 4 * Q z + 9 * W'.a₆ * P x ^ 4 *
      Q z - W'.a₁ ^ 3 * P x ^ 3 * P y * Q x + 2 * W'.a₁ * W'.a₂ * P x ^ 3 * P y * Q x - W'.a₁
      ^ 2 * P x ^ 3 * P y * Q y - W'.a₂ * P x ^ 3 * P y * Q y + 3 * W'.a₁ ^ 2 * W'.a₃ * P x ^
      3 * P y * Q z + 3 * W'.a₁ * W'.a₄ * P x ^ 3 * P y * Q z + W'.a₁ ^ 2 * W'.a₄ * P x ^ 3 *
      P z * Q x + 7 * W'.a₂ * W'.a₄ * P x ^ 3 * P z * Q x - 3 * W'.a₂ * W'.a₃ * P x ^ 3 * P z
      * Q y + 4 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * P x ^ 3 * P z * Q z + 3 * W'.a₁ ^ 2 * W'.a₆ * P x ^
      3 * P z * Q z + 6 * W'.a₁ * W'.a₃ * W'.a₄ * P x ^ 3 * P z * Q z + 4 * W'.a₂ * W'.a₃ ^ 2
      * P x ^ 3 * P z * Q z + 12 * W'.a₂ * W'.a₆ * P x ^ 3 * P z * Q z + 3 * W'.a₄ ^ 2 * P x ^
      3 * P z * Q z - 3 * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 * Q x + 3 * W'.a₂ * P x ^ 2 * P y ^ 2
      * Q x - 3 * W'.a₁ * P x ^ 2 * P y ^ 2 * Q y + 3 * W'.a₁ * W'.a₃ * P x ^ 2 * P y ^ 2 * Q
      z + 3 * W'.a₄ * P x ^ 2 * P y ^ 2 * Q z - 3 * W'.a₁ * W'.a₄ * P x ^ 2 * P y * P z * Q x
      + 3 * W'.a₂ * W'.a₃ * P x ^ 2 * P y * P z * Q x - 3 * W'.a₄ * P x ^ 2 * P y * P z * Q y
      + 3 * W'.a₁ * W'.a₃ ^ 2 * P x ^ 2 * P y * P z * Q z + 3 * W'.a₃ * W'.a₄ * P x ^ 2 * P y
      * P z * Q z + 3 * W'.a₂ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 * Q x + 9 * W'.a₂ * W'.a₆ * P x
      ^ 2 * P z ^ 2 * Q x + 6 * W'.a₄ ^ 2 * P x ^ 2 * P z ^ 2 * Q x - 3 * W'.a₃ * W'.a₄ * P x
      ^ 2 * P z ^ 2 * Q y + 6 * W'.a₁ * W'.a₃ ^ 3 * P x ^ 2 * P z ^ 2 * Q z + 18 * W'.a₁ *
      W'.a₃ * W'.a₆ * P x ^ 2 * P z ^ 2 * Q z + 9 * W'.a₃ ^ 2 * W'.a₄ * P x ^ 2 * P z ^ 2 * Q
      z + 27 * W'.a₄ * W'.a₆ * P x ^ 2 * P z ^ 2 * Q z - 3 * W'.a₁ * P x * P y ^ 3 * Q x - 3 *
      P x * P y ^ 3 * Q y - 9 * W'.a₁ * W'.a₆ * P x * P y * P z ^ 2 * Q x - 9 * W'.a₆ * P x *
      P y * P z ^ 2 * Q y + W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P x * P z ^ 3 * Q x - W'.a₁ * W'.a₂ *
      W'.a₃ * W'.a₄ * P x * P z ^ 3 * Q x - 3 * W'.a₁ * W'.a₃ * W'.a₆ * P x * P z ^ 3 * Q x +
      W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z ^ 3 * Q x + 4 * W'.a₂ ^ 2 * W'.a₆ * P x * P z ^ 3 * Q
      x - W'.a₂ * W'.a₄ ^ 2 * P x * P z ^ 3 * Q x + 3 * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 * Q
      x + 12 * W'.a₄ * W'.a₆ * P x * P z ^ 3 * Q x - 3 * W'.a₃ * W'.a₆ * P x * P z ^ 3 * Q y +
      W'.a₁ ^ 3 * W'.a₃ * W'.a₆ * P x * P z ^ 3 * Q z - W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * P x *
      P z ^ 3 * Q z + W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P x * P z ^ 3 * Q z + W'.a₁ * W'.a₂ * W'.a₃
      ^ 3 * P x * P z ^ 3 * Q z + 4 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ * P x * P z ^ 3 * Q z - 2
      * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P x * P z ^ 3 * Q z + W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P x * P
      z ^ 3 * Q z + 4 * W'.a₂ * W'.a₄ * W'.a₆ * P x * P z ^ 3 * Q z + 3 * W'.a₃ ^ 4 * P x * P
      z ^ 3 * Q z + 21 * W'.a₃ ^ 2 * W'.a₆ * P x * P z ^ 3 * Q z - W'.a₄ ^ 3 * P x * P z ^ 3 *
      Q z + 36 * W'.a₆ ^ 2 * P x * P z ^ 3 * Q z - W'.a₁ ^ 3 * W'.a₆ * P y * P z ^ 3 * Q x +
      W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * P z ^ 3 * Q x - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P y * P z
      ^ 3 * Q x - 4 * W'.a₁ * W'.a₂ * W'.a₆ * P y * P z ^ 3 * Q x + W'.a₁ * W'.a₄ ^ 2 * P y *
      P z ^ 3 * Q x - W'.a₁ ^ 2 * W'.a₆ * P y * P z ^ 3 * Q y + W'.a₁ * W'.a₃ * W'.a₄ * P y *
      P z ^ 3 * Q y - W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 * Q y - 4 * W'.a₂ * W'.a₆ * P y * P z
      ^ 3 * Q y + W'.a₄ ^ 2 * P y * P z ^ 3 * Q y + W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P z ^ 4 * Q x
      - W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 * Q x + W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4 * Q x
      + 4 * W'.a₂ * W'.a₄ * W'.a₆ * P z ^ 4 * Q x - W'.a₄ ^ 3 * P z ^ 4 * Q x + W'.a₁ ^ 2 *
      W'.a₃ ^ 2 * W'.a₆ * P z ^ 4 * Q z + 3 * W'.a₁ ^ 2 * W'.a₆ ^ 2 * P z ^ 4 * Q z - W'.a₁ *
      W'.a₃ ^ 3 * W'.a₄ * P z ^ 4 * Q z - 3 * W'.a₁ * W'.a₃ * W'.a₄ * W'.a₆ * P z ^ 4 * Q z +
      W'.a₂ * W'.a₃ ^ 4 * P z ^ 4 * Q z + 7 * W'.a₂ * W'.a₃ ^ 2 * W'.a₆ * P z ^ 4 * Q z + 12 *
      W'.a₂ * W'.a₆ ^ 2 * P z ^ 4 * Q z - W'.a₃ ^ 2 * W'.a₄ ^ 2 * P z ^ 4 * Q z - 3 * W'.a₄ ^
      2 * W'.a₆ * P z ^ 4 * Q z
    ) * (equation_iff Q).mp hQ

/-- The `XZ` cross-minor of the two addition laws vanishes on curve points. -/
lemma addX_mul_dblAddZ {P Q : Fin 3 → R}
    (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * W'.dblAddZ P Q = W'.addZ P Q * W'.dblAddX P Q := by
  linear_combination (norm := (law_simp; ring1))
    (
    3 * P x * Q x ^ 3 * Q y + W'.a₁ ^ 3 * P x * Q x ^ 3 * Q z + W'.a₁ * W'.a₂ * P x * Q x ^ 3
      * Q z + 6 * W'.a₃ * P x * Q x ^ 3 * Q z + 3 * W'.a₁ ^ 2 * P x * Q x ^ 2 * Q y * Q z + 3
      * W'.a₂ * P x * Q x ^ 2 * Q y * Q z + 3 * W'.a₁ ^ 2 * W'.a₃ * P x * Q x ^ 2 * Q z ^ 2 +
      3 * W'.a₁ * W'.a₄ * P x * Q x ^ 2 * Q z ^ 2 + 6 * W'.a₂ * W'.a₃ * P x * Q x ^ 2 * Q z ^
      2 - 3 * W'.a₁ * W'.a₃ * P x * Q x * Q y * Q z ^ 2 + 3 * W'.a₄ * P x * Q x * Q y * Q z ^
      2 + 3 * W'.a₁ * W'.a₃ ^ 2 * P x * Q x * Q z ^ 3 + 9 * W'.a₁ * W'.a₆ * P x * Q x * Q z ^
      3 + 6 * W'.a₃ * W'.a₄ * P x * Q x * Q z ^ 3 - 3 * P x * Q y ^ 3 * Q z - 9 * W'.a₃ * P x
      * Q y ^ 2 * Q z ^ 2 - 6 * W'.a₃ ^ 2 * P x * Q y * Q z ^ 3 + 3 * W'.a₆ * P x * Q y * Q z
      ^ 3 + W'.a₁ ^ 3 * W'.a₆ * P x * Q z ^ 4 - W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P x * Q z ^ 4 +
      W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P x * Q z ^ 4 + 4 * W'.a₁ * W'.a₂ * W'.a₆ * P x * Q z ^ 4 -
      W'.a₁ * W'.a₄ ^ 2 * P x * Q z ^ 4 + 6 * W'.a₃ * W'.a₆ * P x * Q z ^ 4 + W'.a₁ ^ 2 * P y
      * Q x ^ 3 * Q z + W'.a₂ * P y * Q x ^ 3 * Q z + 3 * W'.a₁ * P y * Q x ^ 2 * Q y * Q z +
      3 * W'.a₁ * W'.a₃ * P y * Q x ^ 2 * Q z ^ 2 + 3 * W'.a₄ * P y * Q x ^ 2 * Q z ^ 2 + 3 *
      P y * Q x * Q y ^ 2 * Q z + 3 * W'.a₃ * P y * Q x * Q y * Q z ^ 2 + 3 * W'.a₃ ^ 2 * P y
      * Q x * Q z ^ 3 + 9 * W'.a₆ * P y * Q x * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₆ * P y * Q z ^ 4 -
      W'.a₁ * W'.a₃ * W'.a₄ * P y * Q z ^ 4 + W'.a₂ * W'.a₃ ^ 2 * P y * Q z ^ 4 + 4 * W'.a₂ *
      W'.a₆ * P y * Q z ^ 4 - W'.a₄ ^ 2 * P y * Q z ^ 4 + W'.a₁ ^ 2 * P z * Q x ^ 3 * Q y +
      W'.a₂ * P z * Q x ^ 3 * Q y + W'.a₁ ^ 2 * W'.a₃ * P z * Q x ^ 3 * Q z + W'.a₂ * W'.a₃ *
      P z * Q x ^ 3 * Q z + 3 * W'.a₁ * P z * Q x ^ 2 * Q y ^ 2 + 6 * W'.a₁ * W'.a₃ * P z * Q
      x ^ 2 * Q y * Q z + 3 * W'.a₄ * P z * Q x ^ 2 * Q y * Q z + 3 * W'.a₁ * W'.a₃ ^ 2 * P z
      * Q x ^ 2 * Q z ^ 2 + 3 * W'.a₃ * W'.a₄ * P z * Q x ^ 2 * Q z ^ 2 + 3 * P z * Q x * Q y
      ^ 3 + 6 * W'.a₃ * P z * Q x * Q y ^ 2 * Q z + 6 * W'.a₃ ^ 2 * P z * Q x * Q y * Q z ^ 2
      + 9 * W'.a₆ * P z * Q x * Q y * Q z ^ 2 + 3 * W'.a₃ ^ 3 * P z * Q x * Q z ^ 3 + 9 *
      W'.a₃ * W'.a₆ * P z * Q x * Q z ^ 3 + W'.a₁ ^ 2 * W'.a₆ * P z * Q y * Q z ^ 3 - W'.a₁ *
      W'.a₃ * W'.a₄ * P z * Q y * Q z ^ 3 + W'.a₂ * W'.a₃ ^ 2 * P z * Q y * Q z ^ 3 + 4 *
      W'.a₂ * W'.a₆ * P z * Q y * Q z ^ 3 - W'.a₄ ^ 2 * P z * Q y * Q z ^ 3 + W'.a₁ ^ 2 *
      W'.a₃ * W'.a₆ * P z * Q z ^ 4 - W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z * Q z ^ 4 + W'.a₂ *
      W'.a₃ ^ 3 * P z * Q z ^ 4 + 4 * W'.a₂ * W'.a₃ * W'.a₆ * P z * Q z ^ 4 - W'.a₃ * W'.a₄ ^
      2 * P z * Q z ^ 4
    ) * (equation_iff P).mp hP + (
    -3 * P x ^ 4 * Q y - W'.a₁ ^ 3 * P x ^ 4 * Q z - W'.a₁ * W'.a₂ * P x ^ 4 * Q z - 6 * W'.a₃
      * P x ^ 4 * Q z - 4 * W'.a₁ ^ 2 * P x ^ 3 * P y * Q z - W'.a₂ * P x ^ 3 * P y * Q z -
      W'.a₁ ^ 2 * P x ^ 3 * P z * Q y - 4 * W'.a₂ * P x ^ 3 * P z * Q y - 4 * W'.a₁ ^ 2 *
      W'.a₃ * P x ^ 3 * P z * Q z - 3 * W'.a₁ * W'.a₄ * P x ^ 3 * P z * Q z - 7 * W'.a₂ *
      W'.a₃ * P x ^ 3 * P z * Q z - 6 * W'.a₁ * P x ^ 2 * P y ^ 2 * Q z - 3 * W'.a₁ * W'.a₃ *
      P x ^ 2 * P y * P z * Q z - 3 * W'.a₄ * P x ^ 2 * P y * P z * Q z - 3 * W'.a₁ * W'.a₃ *
      P x ^ 2 * P z ^ 2 * Q y - 6 * W'.a₄ * P x ^ 2 * P z ^ 2 * Q y - 6 * W'.a₁ * W'.a₃ ^ 2 *
      P x ^ 2 * P z ^ 2 * Q z - 9 * W'.a₁ * W'.a₆ * P x ^ 2 * P z ^ 2 * Q z - 9 * W'.a₃ *
      W'.a₄ * P x ^ 2 * P z ^ 2 * Q z - 3 * P x * P y ^ 3 * Q z - 9 * W'.a₆ * P x * P y * P z
      ^ 2 * Q z - 3 * W'.a₃ ^ 2 * P x * P z ^ 3 * Q y - 12 * W'.a₆ * P x * P z ^ 3 * Q y -
      W'.a₁ ^ 3 * W'.a₆ * P x * P z ^ 3 * Q z + W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P x * P z ^ 3 * Q
      z - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3 * Q z - 4 * W'.a₁ * W'.a₂ * W'.a₆ * P x *
      P z ^ 3 * Q z + W'.a₁ * W'.a₄ ^ 2 * P x * P z ^ 3 * Q z - 3 * W'.a₃ ^ 3 * P x * P z ^ 3
      * Q z - 15 * W'.a₃ * W'.a₆ * P x * P z ^ 3 * Q z - W'.a₁ ^ 2 * W'.a₆ * P y * P z ^ 3 * Q
      z + W'.a₁ * W'.a₃ * W'.a₄ * P y * P z ^ 3 * Q z - W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 * Q
      z - 4 * W'.a₂ * W'.a₆ * P y * P z ^ 3 * Q z + W'.a₄ ^ 2 * P y * P z ^ 3 * Q z - W'.a₁ ^
      2 * W'.a₆ * P z ^ 4 * Q y + W'.a₁ * W'.a₃ * W'.a₄ * P z ^ 4 * Q y - W'.a₂ * W'.a₃ ^ 2 *
      P z ^ 4 * Q y - 4 * W'.a₂ * W'.a₆ * P z ^ 4 * Q y + W'.a₄ ^ 2 * P z ^ 4 * Q y - W'.a₁ ^
      2 * W'.a₃ * W'.a₆ * P z ^ 4 * Q z + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4 * Q z - W'.a₂ *
      W'.a₃ ^ 3 * P z ^ 4 * Q z - 4 * W'.a₂ * W'.a₃ * W'.a₆ * P z ^ 4 * Q z + W'.a₃ * W'.a₄ ^
      2 * P z ^ 4 * Q z
    ) * (equation_iff Q).mp hQ

/-- The `YZ` cross-minor of the two addition laws vanishes on curve points. -/
lemma addY_mul_dblAddZ {P Q : Fin 3 → R}
    (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addY P Q * W'.dblAddZ P Q = W'.addZ P Q * W'.dblAddY P Q := by
  linear_combination (norm := (law_simp; ring1))
    (
    -3 * W'.a₁ ^ 2 * P x * Q x ^ 4 - 6 * W'.a₂ * P x * Q x ^ 4 - 9 * W'.a₁ * P x * Q x ^ 3 * Q
      y - W'.a₁ ^ 4 * P x * Q x ^ 3 * Q z - 2 * W'.a₁ ^ 2 * W'.a₂ * P x * Q x ^ 3 * Q z - 15 *
      W'.a₁ * W'.a₃ * P x * Q x ^ 3 * Q z - 4 * W'.a₂ ^ 2 * P x * Q x ^ 3 * Q z - 12 * W'.a₄ *
      P x * Q x ^ 3 * Q z - 9 * P x * Q x ^ 2 * Q y ^ 2 - 3 * W'.a₁ ^ 3 * P x * Q x ^ 2 * Q y
      * Q z - 9 * W'.a₃ * P x * Q x ^ 2 * Q y * Q z - 3 * W'.a₁ ^ 3 * W'.a₃ * P x * Q x ^ 2 *
      Q z ^ 2 - 3 * W'.a₁ ^ 2 * W'.a₄ * P x * Q x ^ 2 * Q z ^ 2 - 9 * W'.a₁ * W'.a₂ * W'.a₃ *
      P x * Q x ^ 2 * Q z ^ 2 - 9 * W'.a₂ * W'.a₄ * P x * Q x ^ 2 * Q z ^ 2 - 9 * W'.a₃ ^ 2 *
      P x * Q x ^ 2 * Q z ^ 2 - 27 * W'.a₆ * P x * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₁ ^ 2 * P x * Q
      x * Q y ^ 2 * Q z + 3 * W'.a₁ ^ 2 * W'.a₃ * P x * Q x * Q y * Q z ^ 2 + 3 * W'.a₁ *
      W'.a₄ * P x * Q x * Q y * Q z ^ 2 - 3 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * P x * Q x * Q z ^ 3 - 12
      * W'.a₁ ^ 2 * W'.a₆ * P x * Q x * Q z ^ 3 - 3 * W'.a₁ * W'.a₃ * W'.a₄ * P x * Q x * Q z
      ^ 3 - 6 * W'.a₂ * W'.a₃ ^ 2 * P x * Q x * Q z ^ 3 - 24 * W'.a₂ * W'.a₆ * P x * Q x * Q z
      ^ 3 + 6 * W'.a₁ * W'.a₃ * P x * Q y ^ 2 * Q z ^ 2 + 3 * W'.a₄ * P x * Q y ^ 2 * Q z ^ 2
      + 6 * W'.a₁ * W'.a₃ ^ 2 * P x * Q y * Q z ^ 3 + 3 * W'.a₃ * W'.a₄ * P x * Q y * Q z ^ 3
      - W'.a₁ ^ 4 * W'.a₆ * P x * Q z ^ 4 + W'.a₁ ^ 3 * W'.a₃ * W'.a₄ * P x * Q z ^ 4 - W'.a₁
      ^ 2 * W'.a₂ * W'.a₃ ^ 2 * P x * Q z ^ 4 - 5 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P x * Q z ^ 4
      + W'.a₁ ^ 2 * W'.a₄ ^ 2 * P x * Q z ^ 4 + W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P x * Q z ^ 4
      - 6 * W'.a₁ * W'.a₃ * W'.a₆ * P x * Q z ^ 4 - W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * Q z ^ 4 - 4
      * W'.a₂ ^ 2 * W'.a₆ * P x * Q z ^ 4 + W'.a₂ * W'.a₄ ^ 2 * P x * Q z ^ 4 - 3 * W'.a₄ *
      W'.a₆ * P x * Q z ^ 4 - W'.a₁ ^ 3 * P y * Q x ^ 3 * Q z - W'.a₁ * W'.a₂ * P y * Q x ^ 3
      * Q z - 3 * W'.a₁ ^ 2 * P y * Q x ^ 2 * Q y * Q z - 3 * W'.a₁ ^ 2 * W'.a₃ * P y * Q x ^
      2 * Q z ^ 2 - 3 * W'.a₁ * W'.a₄ * P y * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₁ * P y * Q x * Q y
      ^ 2 * Q z - 3 * W'.a₁ * W'.a₃ * P y * Q x * Q y * Q z ^ 2 - 3 * W'.a₁ * W'.a₃ ^ 2 * P y
      * Q x * Q z ^ 3 - 9 * W'.a₁ * W'.a₆ * P y * Q x * Q z ^ 3 - W'.a₁ ^ 3 * W'.a₆ * P y * Q
      z ^ 4 + W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * Q z ^ 4 - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P y * Q
      z ^ 4 - 4 * W'.a₁ * W'.a₂ * W'.a₆ * P y * Q z ^ 4 + W'.a₁ * W'.a₄ ^ 2 * P y * Q z ^ 4 -
      W'.a₁ ^ 2 * W'.a₂ * P z * Q x ^ 4 - W'.a₂ ^ 2 * P z * Q x ^ 4 - 3 * W'.a₁ * W'.a₂ * P z
      * Q x ^ 3 * Q y - W'.a₁ ^ 3 * W'.a₃ * P z * Q x ^ 3 * Q z - W'.a₁ ^ 2 * W'.a₄ * P z * Q
      x ^ 3 * Q z - 4 * W'.a₁ * W'.a₂ * W'.a₃ * P z * Q x ^ 3 * Q z - 4 * W'.a₂ * W'.a₄ * P z
      * Q x ^ 3 * Q z - 3 * W'.a₂ * P z * Q x ^ 2 * Q y ^ 2 - 3 * W'.a₁ ^ 2 * W'.a₃ * P z * Q
      x ^ 2 * Q y * Q z - 3 * W'.a₁ * W'.a₄ * P z * Q x ^ 2 * Q y * Q z - 3 * W'.a₂ * W'.a₃ *
      P z * Q x ^ 2 * Q y * Q z - 3 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * P z * Q x ^ 2 * Q z ^ 2 - 6 *
      W'.a₁ * W'.a₃ * W'.a₄ * P z * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₂ * W'.a₃ ^ 2 * P z * Q x ^ 2
      * Q z ^ 2 - 9 * W'.a₂ * W'.a₆ * P z * Q x ^ 2 * Q z ^ 2 - 3 * W'.a₄ ^ 2 * P z * Q x ^ 2
      * Q z ^ 2 - 3 * W'.a₁ * W'.a₃ * P z * Q x * Q y ^ 2 * Q z - 3 * W'.a₄ * P z * Q x * Q y
      ^ 2 * Q z - 3 * W'.a₁ * W'.a₃ ^ 2 * P z * Q x * Q y * Q z ^ 2 - 3 * W'.a₃ * W'.a₄ * P z
      * Q x * Q y * Q z ^ 2 - W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P z * Q x * Q z ^ 3 + W'.a₁ * W'.a₂
      * W'.a₃ * W'.a₄ * P z * Q x * Q z ^ 3 - 3 * W'.a₁ * W'.a₃ ^ 3 * P z * Q x * Q z ^ 3 - 9
      * W'.a₁ * W'.a₃ * W'.a₆ * P z * Q x * Q z ^ 3 - W'.a₂ ^ 2 * W'.a₃ ^ 2 * P z * Q x * Q z
      ^ 3 - 4 * W'.a₂ ^ 2 * W'.a₆ * P z * Q x * Q z ^ 3 + W'.a₂ * W'.a₄ ^ 2 * P z * Q x * Q z
      ^ 3 - 3 * W'.a₃ ^ 2 * W'.a₄ * P z * Q x * Q z ^ 3 - 9 * W'.a₄ * W'.a₆ * P z * Q x * Q z
      ^ 3 - W'.a₁ ^ 3 * W'.a₃ * W'.a₆ * P z * Q z ^ 4 + W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * P z *
      Q z ^ 4 - W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P z * Q z ^ 4 - W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * P z *
      Q z ^ 4 - 4 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ * P z * Q z ^ 4 + 2 * W'.a₁ * W'.a₃ * W'.a₄
      ^ 2 * P z * Q z ^ 4 - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z * Q z ^ 4 - 4 * W'.a₂ * W'.a₄ *
      W'.a₆ * P z * Q z ^ 4 + W'.a₄ ^ 3 * P z * Q z ^ 4
    ) * (equation_iff P).mp hP + (
    3 * W'.a₁ ^ 2 * P x ^ 4 * Q x + 6 * W'.a₂ * P x ^ 4 * Q x + W'.a₁ ^ 4 * P x ^ 4 * Q z + 2
      * W'.a₁ ^ 2 * W'.a₂ * P x ^ 4 * Q z + 6 * W'.a₁ * W'.a₃ * P x ^ 4 * Q z + W'.a₂ ^ 2 * P
      x ^ 4 * Q z + 3 * W'.a₄ * P x ^ 4 * Q z + 9 * W'.a₁ * P x ^ 3 * P y * Q x + 4 * W'.a₁ ^
      3 * P x ^ 3 * P y * Q z + 4 * W'.a₁ * W'.a₂ * P x ^ 3 * P y * Q z + W'.a₁ ^ 2 * W'.a₂ *
      P x ^ 3 * P z * Q x + 9 * W'.a₁ * W'.a₃ * P x ^ 3 * P z * Q x + 4 * W'.a₂ ^ 2 * P x ^ 3
      * P z * Q x + 9 * W'.a₄ * P x ^ 3 * P z * Q x + 4 * W'.a₁ ^ 3 * W'.a₃ * P x ^ 3 * P z *
      Q z + 4 * W'.a₁ ^ 2 * W'.a₄ * P x ^ 3 * P z * Q z + 10 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 3
      * P z * Q z + 7 * W'.a₂ * W'.a₄ * P x ^ 3 * P z * Q z + 9 * P x ^ 2 * P y ^ 2 * Q x + 6
      * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 * Q z + 3 * W'.a₂ * P x ^ 2 * P y ^ 2 * Q z + 9 * W'.a₃
      * P x ^ 2 * P y * P z * Q x + 3 * W'.a₁ ^ 2 * W'.a₃ * P x ^ 2 * P y * P z * Q z + 3 *
      W'.a₁ * W'.a₄ * P x ^ 2 * P y * P z * Q z + 3 * W'.a₂ * W'.a₃ * P x ^ 2 * P y * P z * Q
      z + 3 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 2 * P z ^ 2 * Q x + 6 * W'.a₂ * W'.a₄ * P x ^ 2 *
      P z ^ 2 * Q x + 9 * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 * Q x + 27 * W'.a₆ * P x ^ 2 * P z ^ 2
      * Q x + 6 * W'.a₁ ^ 2 * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 * Q z + 9 * W'.a₁ ^ 2 * W'.a₆ * P
      x ^ 2 * P z ^ 2 * Q z + 12 * W'.a₁ * W'.a₃ * W'.a₄ * P x ^ 2 * P z ^ 2 * Q z + 3 * W'.a₂
      * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 * Q z + 9 * W'.a₂ * W'.a₆ * P x ^ 2 * P z ^ 2 * Q z + 6
      * W'.a₄ ^ 2 * P x ^ 2 * P z ^ 2 * Q z + 3 * W'.a₁ * P x * P y ^ 3 * Q z + 9 * W'.a₁ *
      W'.a₆ * P x * P y * P z ^ 2 * Q z + 3 * W'.a₁ ^ 2 * W'.a₆ * P x * P z ^ 3 * Q x - 3 *
      W'.a₁ * W'.a₃ * W'.a₄ * P x * P z ^ 3 * Q x + 6 * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3 * Q
      x + 24 * W'.a₂ * W'.a₆ * P x * P z ^ 3 * Q x - 3 * W'.a₄ ^ 2 * P x * P z ^ 3 * Q x +
      W'.a₁ ^ 4 * W'.a₆ * P x * P z ^ 3 * Q z - W'.a₁ ^ 3 * W'.a₃ * W'.a₄ * P x * P z ^ 3 * Q
      z + W'.a₁ ^ 2 * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3 * Q z + 5 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆
      * P x * P z ^ 3 * Q z - W'.a₁ ^ 2 * W'.a₄ ^ 2 * P x * P z ^ 3 * Q z - W'.a₁ * W'.a₂ *
      W'.a₃ * W'.a₄ * P x * P z ^ 3 * Q z + 3 * W'.a₁ * W'.a₃ ^ 3 * P x * P z ^ 3 * Q z + 15 *
      W'.a₁ * W'.a₃ * W'.a₆ * P x * P z ^ 3 * Q z + W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z ^ 3 * Q
      z + 4 * W'.a₂ ^ 2 * W'.a₆ * P x * P z ^ 3 * Q z - W'.a₂ * W'.a₄ ^ 2 * P x * P z ^ 3 * Q
      z + 3 * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 * Q z + 12 * W'.a₄ * W'.a₆ * P x * P z ^ 3 * Q
      z + W'.a₁ ^ 3 * W'.a₆ * P y * P z ^ 3 * Q z - W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * P z ^ 3
      * Q z + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 * Q z + 4 * W'.a₁ * W'.a₂ * W'.a₆ * P
      y * P z ^ 3 * Q z - W'.a₁ * W'.a₄ ^ 2 * P y * P z ^ 3 * Q z + W'.a₁ ^ 2 * W'.a₂ * W'.a₆
      * P z ^ 4 * Q x - W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P z ^ 4 * Q x + W'.a₂ ^ 2 * W'.a₃ ^ 2
      * P z ^ 4 * Q x + 4 * W'.a₂ ^ 2 * W'.a₆ * P z ^ 4 * Q x - W'.a₂ * W'.a₄ ^ 2 * P z ^ 4 *
      Q x + W'.a₁ ^ 3 * W'.a₃ * W'.a₆ * P z ^ 4 * Q z - W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * P z ^
      4 * Q z + W'.a₁ ^ 2 * W'.a₄ * W'.a₆ * P z ^ 4 * Q z + W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * P z ^
      4 * Q z + 4 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₆ * P z ^ 4 * Q z - 2 * W'.a₁ * W'.a₃ * W'.a₄
      ^ 2 * P z ^ 4 * Q z + W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4 * Q z + 4 * W'.a₂ * W'.a₄ *
      W'.a₆ * P z ^ 4 * Q z - W'.a₄ ^ 3 * P z ^ 4 * Q z
    ) * (equation_iff Q).mp hQ

end CrossMinors

section CommRing

variable {R : Type*} [CommRing R] {W' : Projective R}

lemma dblAddXYZ_x (P Q : Fin 3 → R) : W'.dblAddXYZ P Q x = W'.dblAddX P Q := rfl

lemma dblAddXYZ_y (P Q : Fin 3 → R) : W'.dblAddXYZ P Q y = W'.dblAddY P Q := rfl

lemma dblAddXYZ_z (P Q : Fin 3 → R) : W'.dblAddXYZ P Q z = W'.dblAddZ P Q := rfl

lemma dblAddXYZ_smul_left (P Q : Fin 3 → R) (u : R) :
    W'.dblAddXYZ (u • P) Q = u ^ 2 • W'.dblAddXYZ P Q := by
  simpa using W'.dblAddXYZ_smul P Q u 1

/-- The zero representative satisfies the homogeneous Weierstrass equation. -/
lemma equation_zero_triple : W'.Equation (0 : Fin 3 → R) := by
  simp [equation_iff]

/-- A nonsingular projective representative is nonzero. -/
lemma Nonsingular.ne_zero {P : Fin 3 → R} (hP : W'.Nonsingular P) : P ≠ 0 := by
  rintro rfl
  rcases (nonsingular_iff _).mp hP with ⟨-, h | h | h⟩ <;> simp at h

end CommRing

section Field

variable {F : Type*} [Field F] {W : Projective F}

/-- Three vanishing cross-minors make a vector proportional to a nonzero vector over a field. -/
lemma exists_eq_smul_of_cross_eq_zero {v w : Fin 3 → F} (hw : w ≠ 0)
    (h01 : v x * w y = v y * w x) (h02 : v x * w z = v z * w x)
    (h12 : v y * w z = v z * w y) : ∃ c : F, v = c • w := by
  rcases eq_or_ne (w x) 0 with hwx | hwx
  · rcases eq_or_ne (w y) 0 with hwy | hwy
    · rcases eq_or_ne (w z) 0 with hwz | hwz
      · refine absurd (funext fun j => ?_) hw
        fin_cases j
        exacts [hwx, hwy, hwz]
      · refine ⟨v z / w z, funext fun j => ?_⟩
        fin_cases j
        · change v x = v z / w z * w x
          rw [div_mul_eq_mul_div, eq_div_iff hwz]
          linear_combination h02
        · change v y = v z / w z * w y
          rw [div_mul_eq_mul_div, eq_div_iff hwz]
          linear_combination h12
        · change v z = v z / w z * w z
          rw [div_mul_cancel₀ _ hwz]
    · refine ⟨v y / w y, funext fun j => ?_⟩
      fin_cases j
      · change v x = v y / w y * w x
        rw [div_mul_eq_mul_div, eq_div_iff hwy]
        linear_combination h01
      · change v y = v y / w y * w y
        rw [div_mul_cancel₀ _ hwy]
      · change v z = v y / w y * w z
        rw [div_mul_eq_mul_div, eq_div_iff hwy]
        linear_combination -h12
  · refine ⟨v x / w x, funext fun j => ?_⟩
    fin_cases j
    · change v x = v x / w x * w x
      rw [div_mul_cancel₀ _ hwx]
    · change v y = v x / w x * w y
      rw [div_mul_eq_mul_div, eq_div_iff hwx]
      linear_combination -h01
    · change v z = v x / w x * w z
      rw [div_mul_eq_mul_div, eq_div_iff hwx]
      linear_combination -h02

/-- The second Bosma–Lenstra triple lands on the curve for nonsingular field-valued inputs. -/
theorem equation_dblAddXYZ {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Equation (W.dblAddXYZ P Q) := by
  classical
  by_cases hPQ : P ≈ Q
  · rcases hPQ with ⟨u, rfl⟩
    change W.Equation (W.dblAddXYZ ((u : F) • Q) Q)
    rw [dblAddXYZ_smul_left, equation_smul _ (u.isUnit.pow 2), dblAddXYZ_self hQ.left]
    have h := (nonsingular_add hQ hQ).left
    rwa [add_of_equiv (Setoid.refl Q)] at h
  · have hNS := nonsingular_add hP hQ
    rw [add_of_not_equiv hPQ] at hNS
    by_cases hv : W.dblAddXYZ P Q = 0
    · rw [hv]
      exact equation_zero_triple
    · have h01 : W.dblAddXYZ P Q x * W.addXYZ P Q y
          = W.dblAddXYZ P Q y * W.addXYZ P Q x := by
        simp only [dblAddXYZ_x, dblAddXYZ_y, addXYZ, Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination -W.addX_mul_dblAddY hP.left hQ.left
      have h02 : W.dblAddXYZ P Q x * W.addXYZ P Q z
          = W.dblAddXYZ P Q z * W.addXYZ P Q x := by
        simp only [dblAddXYZ_x, dblAddXYZ_z, addXYZ, Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        linear_combination -W.addX_mul_dblAddZ hP.left hQ.left
      have h12 : W.dblAddXYZ P Q y * W.addXYZ P Q z
          = W.dblAddXYZ P Q z * W.addXYZ P Q y := by
        simp only [dblAddXYZ_y, dblAddXYZ_z, addXYZ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        linear_combination -W.addY_mul_dblAddZ hP.left hQ.left
      obtain ⟨c, hc⟩ := exists_eq_smul_of_cross_eq_zero hNS.ne_zero h01 h02 h12
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact hv hc
      rw [hc]
      exact (equation_smul _ (isUnit_iff_ne_zero.mpr hc0)).mpr hNS.left

/-- The two Bosma–Lenstra triples cannot both vanish on nonsingular field-valued inputs. -/
theorem addXYZ_ne_zero_or_dblAddXYZ_ne_zero {P Q : Fin 3 → F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.addXYZ P Q ≠ 0 ∨ W.dblAddXYZ P Q ≠ 0 := by
  classical
  by_cases hPQ : P ≈ Q
  · right
    rcases hPQ with ⟨u, rfl⟩
    change W.dblAddXYZ ((u : F) • Q) Q ≠ 0
    rw [dblAddXYZ_smul_left, dblAddXYZ_self hQ.left]
    have hdbl : W.dblXYZ Q ≠ 0 := by
      have h := nonsingular_add hQ hQ
      rw [add_of_equiv (Setoid.refl Q)] at h
      exact h.ne_zero
    exact smul_ne_zero (pow_ne_zero 2 u.ne_zero) hdbl
  · left
    have hNS := nonsingular_add hP hQ
    rw [add_of_not_equiv hPQ] at hNS
    exact hNS.ne_zero

end Field

section LawOne

variable {R : Type*} [CommRing R] {W' : Projective R}

/-- Mathlib's first addition triple vanishes on the diagonal. -/
lemma addXYZ_self' (P : Fin 3 → R) : W'.addXYZ P P = 0 := by
  funext i
  fin_cases i
  · change W'.addX P P = 0
    exact addX_self P
  · change W'.addY P P = 0
    exact addY_self P
  · change W'.addZ P P = 0
    exact addZ_self P

/-- The first addition triple is homogeneous of degree two in its first input. -/
lemma addXYZ_smul_left (P Q : Fin 3 → R) (u : R) :
    W'.addXYZ (u • P) Q = u ^ 2 • W'.addXYZ P Q := by
  simpa using W'.addXYZ_smul P Q u 1

end LawOne

section CompletePair

variable {F : Type*} [Field F] {W : Projective F}

/-- Mathlib's first Bosma–Lenstra triple also lands on the curve for nonsingular inputs. -/
theorem equation_addXYZ {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Equation (W.addXYZ P Q) := by
  classical
  by_cases hPQ : P ≈ Q
  · rcases hPQ with ⟨u, rfl⟩
    change W.Equation (W.addXYZ ((u : F) • Q) Q)
    rw [addXYZ_smul_left, addXYZ_self', smul_zero]
    exact equation_zero_triple
  · have hNS := nonsingular_add hP hQ
    rw [add_of_not_equiv hPQ] at hNS
    exact hNS.left

/-- On elliptic field-valued inputs, both Bosma–Lenstra triples lie on the curve and they
cannot vanish simultaneously. This is the algebraic coverage input for later chart gluing. -/
theorem bosmaLenstra_pair_onCurve_and_jointly_nonzero [W.IsElliptic]
    {P Q : Fin 3 → F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    W.Equation (W.addXYZ P Q) ∧ W.Equation (W.dblAddXYZ P Q) ∧
      (W.addXYZ P Q ≠ 0 ∨ W.dblAddXYZ P Q ≠ 0) :=
  ⟨equation_addXYZ hP hQ, equation_dblAddXYZ hP hQ,
    addXYZ_ne_zero_or_dblAddXYZ_ne_zero hP hQ⟩

end CompletePair

end WeierstrassCurve.Projective
