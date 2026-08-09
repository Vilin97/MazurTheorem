/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

This file selectively adapts the algebraic second-addition-law declarations from
AINTLIB's `EllipticCurve/AdditionLaw.lean`, exact source blob
`c6ea88db42629fd166902494bb5617d4511e309b`. The source blob is present at
AINTLIB's Apache-2.0 licensed default commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula

/-!
# The second Bosma–Lenstra addition law in projective coordinates

Mathlib's `WeierstrassCurve.Projective.addX/addY/addZ` is the Bosma–Lenstra
addition law associated to the line `Z = 0`. This leaf supplies the coordinate
polynomials `dblAddX/dblAddY/dblAddZ` for the complementary law associated to
`Y = 0`, together with their bihomogeneity, behavior at the zero point, and
agreement with Mathlib's doubling formulas on the diagonal.

The formulas were derived upstream from the anchor identity in Theorem 2 and
Section 5 of Bosma–Lenstra, *Complete Systems of Two Addition Laws for Elliptic
Curves*, Journal of Number Theory 53 (1995), 229–240. The exact polynomial and
certificate provenance is retained in the declaration documentation below and
in the source-of-record named in the file header.

This module is algebraic substrate for a later complete-system and scheme-level
gluing construction. It does not construct a group object.
-/

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] {W' : Projective R}

/-! ## The law of the line `Y = 0` -/

variable (W') in
/-- The `X`-coordinate of the second Bosma–Lenstra addition law (the law of the line `Y = 0`),
evaluated at two projective point representatives `P` and `Q`. Its diagonal is `dblX`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring).

**Paper-fidelity warning — do NOT "correct" this polynomial against the printed page.** In
the printed `X₃⁽²⁾` (B–L p. 237; paper coordinates `P = (X₁:Y₁:Z₁)`, `Q = (X₂:Y₂:Z₂)`), the
`a₃a₄` term is easily (mis)read as `+ a₃a₄·(X₁Z₂ − 2X₂Z₁)·X₂Z₁`. The true term, as derived
and certified here, is `− a₃a₄·(2X₁Z₂ + X₂Z₁)·X₂Z₁` — the two monomials
`- 2 * W'.a₃ * W'.a₄ * P x * P z * Q x * Q z - W'.a₃ * W'.a₄ * P z ^ 2 * Q x ^ 2` below.
The derivation is overdetermined (exact anchor ideal identity `d³Z₁Z₂·law2ᵢ ≡ N_Y·law1ᵢ`
plus 25 independent end-to-end numeric group-law samples; `derive_law2.py`), so the stored
polynomial is authoritative independently of any reading of the page — and the six
kernel-checked certificates in the source-of-record would all fail against the misread variant. -/
noncomputable def dblAddX (P Q : Fin 3 → R) : R :=
      -W'.a₁ * W'.a₂ * P x ^ 2 * Q x ^ 2 - W'.a₂ * P x ^ 2 * Q x * Q y - W'.a₁ ^ 2 * W'.a₃ * P
        x ^ 2 * Q x * Q z - 2 * W'.a₁ * W'.a₄ * P x ^ 2 * Q x * Q z - W'.a₁ * W'.a₃ * P x ^ 2
        * Q y * Q z - W'.a₄ * P x ^ 2 * Q y * Q z - W'.a₁ * W'.a₃ ^ 2 * P x ^ 2 * Q z ^ 2 - 3
        * W'.a₁ * W'.a₆ * P x ^ 2 * Q z ^ 2 + W'.a₁ ^ 2 * P x * P y * Q x ^ 2 - W'.a₂ * P x *
        P y * Q x ^ 2 + 2 * W'.a₁ * P x * P y * Q x * Q y - 2 * W'.a₄ * P x * P y * Q x * Q z
        + P x * P y * Q y ^ 2 - W'.a₃ ^ 2 * P x * P y * Q z ^ 2 - 3 * W'.a₆ * P x * P y * Q z
        ^ 2 - W'.a₁ * W'.a₄ * P x * P z * Q x ^ 2 - W'.a₂ * W'.a₃ * P x * P z * Q x ^ 2 - 2 *
        W'.a₄ * P x * P z * Q x * Q y - 2 * W'.a₁ * W'.a₃ ^ 2 * P x * P z * Q x * Q z - 6 *
        W'.a₁ * W'.a₆ * P x * P z * Q x * Q z - 2 * W'.a₃ * W'.a₄ * P x * P z * Q x * Q z - 2
        * W'.a₃ ^ 2 * P x * P z * Q y * Q z - 6 * W'.a₆ * P x * P z * Q y * Q z - W'.a₁ ^ 3 *
        W'.a₆ * P x * P z * Q z ^ 2 + W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P x * P z * Q z ^ 2 - W'.a₁
        * W'.a₂ * W'.a₃ ^ 2 * P x * P z * Q z ^ 2 - 4 * W'.a₁ * W'.a₂ * W'.a₆ * P x * P z * Q
        z ^ 2 + W'.a₁ * W'.a₄ ^ 2 * P x * P z * Q z ^ 2 - W'.a₃ ^ 3 * P x * P z * Q z ^ 2 - 3
        * W'.a₃ * W'.a₆ * P x * P z * Q z ^ 2 + W'.a₁ * P y ^ 2 * Q x ^ 2 + P y ^ 2 * Q x * Q
        y + W'.a₃ * P y ^ 2 * Q x * Q z + W'.a₁ * W'.a₃ * P y * P z * Q x ^ 2 - W'.a₄ * P y *
        P z * Q x ^ 2 + 2 * W'.a₃ * P y * P z * Q x * Q y - 6 * W'.a₆ * P y * P z * Q x * Q z
        - W'.a₁ ^ 2 * W'.a₆ * P y * P z * Q z ^ 2 + W'.a₁ * W'.a₃ * W'.a₄ * P y * P z * Q z ^
        2 - W'.a₂ * W'.a₃ ^ 2 * P y * P z * Q z ^ 2 - 4 * W'.a₂ * W'.a₆ * P y * P z * Q z ^ 2
        + W'.a₄ ^ 2 * P y * P z * Q z ^ 2 - W'.a₃ * W'.a₄ * P z ^ 2 * Q x ^ 2 - 3 * W'.a₆ * P
        z ^ 2 * Q x * Q y - W'.a₃ ^ 3 * P z ^ 2 * Q x * Q z - 6 * W'.a₃ * W'.a₆ * P z ^ 2 * Q
        x * Q z - W'.a₁ ^ 2 * W'.a₆ * P z ^ 2 * Q y * Q z + W'.a₁ * W'.a₃ * W'.a₄ * P z ^ 2 *
        Q y * Q z - W'.a₂ * W'.a₃ ^ 2 * P z ^ 2 * Q y * Q z - 4 * W'.a₂ * W'.a₆ * P z ^ 2 * Q
        y * Q z + W'.a₄ ^ 2 * P z ^ 2 * Q y * Q z - W'.a₁ ^ 2 * W'.a₃ * W'.a₆ * P z ^ 2 * Q z
        ^ 2 + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 2 * Q z ^ 2 - W'.a₂ * W'.a₃ ^ 3 * P z ^ 2 * Q
        z ^ 2 - 4 * W'.a₂ * W'.a₃ * W'.a₆ * P z ^ 2 * Q z ^ 2 + W'.a₃ * W'.a₄ ^ 2 * P z ^ 2 *
        Q z ^ 2

variable (W') in
/-- The `Y`-coordinate of the second Bosma–Lenstra addition law; diagonal `dblY`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring). -/
noncomputable def dblAddY (P Q : Fin 3 → R) : R :=
      -W'.a₂ ^ 2 * P x ^ 2 * Q x ^ 2 + 3 * W'.a₄ * P x ^ 2 * Q x ^ 2 + W'.a₁ ^ 2 * W'.a₄ * P x
        ^ 2 * Q x * Q z - 2 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 2 * Q x * Q z - W'.a₂ * W'.a₄ * P
        x ^ 2 * Q x * Q z + 3 * W'.a₃ ^ 2 * P x ^ 2 * Q x * Q z + 9 * W'.a₆ * P x ^ 2 * Q x *
        Q z + 3 * W'.a₁ ^ 2 * W'.a₆ * P x ^ 2 * Q z ^ 2 - 2 * W'.a₁ * W'.a₃ * W'.a₄ * P x ^ 2
        * Q z ^ 2 + W'.a₂ * W'.a₃ ^ 2 * P x ^ 2 * Q z ^ 2 + 3 * W'.a₂ * W'.a₆ * P x ^ 2 * Q z
        ^ 2 - W'.a₄ ^ 2 * P x ^ 2 * Q z ^ 2 + W'.a₁ * W'.a₂ * P x * P y * Q x ^ 2 - 3 * W'.a₃
        * P x * P y * Q x ^ 2 + 2 * W'.a₁ * W'.a₄ * P x * P y * Q x * Q z - 2 * W'.a₂ * W'.a₃
        * P x * P y * Q x * Q z + 3 * W'.a₁ * W'.a₆ * P x * P y * Q z ^ 2 - W'.a₃ * W'.a₄ * P
        x * P y * Q z ^ 2 - W'.a₂ * W'.a₄ * P x * P z * Q x ^ 2 + 9 * W'.a₆ * P x * P z * Q x
        ^ 2 + 6 * W'.a₁ ^ 2 * W'.a₆ * P x * P z * Q x * Q z - 4 * W'.a₁ * W'.a₃ * W'.a₄ * P x
        * P z * Q x * Q z + 2 * W'.a₂ * W'.a₃ ^ 2 * P x * P z * Q x * Q z + 12 * W'.a₂ * W'.a₆
        * P x * P z * Q x * Q z - 4 * W'.a₄ ^ 2 * P x * P z * Q x * Q z + W'.a₁ ^ 4 * W'.a₆ *
        P x * P z * Q z ^ 2 - W'.a₁ ^ 3 * W'.a₃ * W'.a₄ * P x * P z * Q z ^ 2 + W'.a₁ ^ 2 *
        W'.a₂ * W'.a₃ ^ 2 * P x * P z * Q z ^ 2 + 5 * W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P x * P z *
        Q z ^ 2 - W'.a₁ ^ 2 * W'.a₄ ^ 2 * P x * P z * Q z ^ 2 - W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄
        * P x * P z * Q z ^ 2 - W'.a₁ * W'.a₃ ^ 3 * P x * P z * Q z ^ 2 - 3 * W'.a₁ * W'.a₃ *
        W'.a₆ * P x * P z * Q z ^ 2 + W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z * Q z ^ 2 + 4 * W'.a₂
        ^ 2 * W'.a₆ * P x * P z * Q z ^ 2 - W'.a₂ * W'.a₄ ^ 2 * P x * P z * Q z ^ 2 - W'.a₃ ^
        2 * W'.a₄ * P x * P z * Q z ^ 2 - 3 * W'.a₄ * W'.a₆ * P x * P z * Q z ^ 2 + W'.a₁ * P
        y ^ 2 * Q x * Q y + P y ^ 2 * Q y ^ 2 + W'.a₃ * P y ^ 2 * Q y * Q z + W'.a₁ * W'.a₄ *
        P y * P z * Q x ^ 2 - W'.a₂ * W'.a₃ * P y * P z * Q x ^ 2 + 6 * W'.a₁ * W'.a₆ * P y *
        P z * Q x * Q z - 2 * W'.a₃ * W'.a₄ * P y * P z * Q x * Q z + W'.a₁ ^ 3 * W'.a₆ * P y
        * P z * Q z ^ 2 - W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * P z * Q z ^ 2 + W'.a₁ * W'.a₂ *
        W'.a₃ ^ 2 * P y * P z * Q z ^ 2 + 4 * W'.a₁ * W'.a₂ * W'.a₆ * P y * P z * Q z ^ 2 -
        W'.a₁ * W'.a₄ ^ 2 * P y * P z * Q z ^ 2 - W'.a₃ ^ 3 * P y * P z * Q z ^ 2 - 3 * W'.a₃
        * W'.a₆ * P y * P z * Q z ^ 2 + 3 * W'.a₂ * W'.a₆ * P z ^ 2 * Q x ^ 2 - W'.a₄ ^ 2 * P
        z ^ 2 * Q x ^ 2 + W'.a₁ ^ 2 * W'.a₂ * W'.a₆ * P z ^ 2 * Q x * Q z - W'.a₁ * W'.a₂ *
        W'.a₃ * W'.a₄ * P z ^ 2 * Q x * Q z + 3 * W'.a₁ * W'.a₃ * W'.a₆ * P z ^ 2 * Q x * Q z
        + W'.a₂ ^ 2 * W'.a₃ ^ 2 * P z ^ 2 * Q x * Q z + 4 * W'.a₂ ^ 2 * W'.a₆ * P z ^ 2 * Q x
        * Q z - W'.a₂ * W'.a₄ ^ 2 * P z ^ 2 * Q x * Q z - 2 * W'.a₃ ^ 2 * W'.a₄ * P z ^ 2 * Q
        x * Q z - 3 * W'.a₄ * W'.a₆ * P z ^ 2 * Q x * Q z + W'.a₁ ^ 3 * W'.a₃ * W'.a₆ * P z ^
        2 * Q z ^ 2 - W'.a₁ ^ 2 * W'.a₃ ^ 2 * W'.a₄ * P z ^ 2 * Q z ^ 2 + W'.a₁ ^ 2 * W'.a₄ *
        W'.a₆ * P z ^ 2 * Q z ^ 2 + W'.a₁ * W'.a₂ * W'.a₃ ^ 3 * P z ^ 2 * Q z ^ 2 + 4 * W'.a₁
        * W'.a₂ * W'.a₃ * W'.a₆ * P z ^ 2 * Q z ^ 2 - 2 * W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z ^ 2
        * Q z ^ 2 + W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 2 * Q z ^ 2 + 4 * W'.a₂ * W'.a₄ * W'.a₆
        * P z ^ 2 * Q z ^ 2 - W'.a₃ ^ 4 * P z ^ 2 * Q z ^ 2 - 6 * W'.a₃ ^ 2 * W'.a₆ * P z ^ 2
        * Q z ^ 2 - W'.a₄ ^ 3 * P z ^ 2 * Q z ^ 2 - 9 * W'.a₆ ^ 2 * P z ^ 2 * Q z ^ 2

variable (W') in
/-- The `Z`-coordinate of the second Bosma–Lenstra addition law; diagonal `dblZ`.
Source: B–L Thm 2 + §5 p. 237 (derived; see the module docstring). -/
noncomputable def dblAddZ (P Q : Fin 3 → R) : R :=
      3 * W'.a₁ * P x ^ 2 * Q x ^ 2 + 3 * P x ^ 2 * Q x * Q y + W'.a₁ ^ 3 * P x ^ 2 * Q x * Q
        z + 2 * W'.a₁ * W'.a₂ * P x ^ 2 * Q x * Q z + W'.a₁ ^ 2 * P x ^ 2 * Q y * Q z + W'.a₂
        * P x ^ 2 * Q y * Q z + W'.a₁ ^ 2 * W'.a₃ * P x ^ 2 * Q z ^ 2 + W'.a₁ * W'.a₄ * P x ^
        2 * Q z ^ 2 + 3 * P x * P y * Q x ^ 2 + 2 * W'.a₁ ^ 2 * P x * P y * Q x * Q z + 2 *
        W'.a₂ * P x * P y * Q x * Q z + 2 * W'.a₁ * P x * P y * Q y * Q z + 2 * W'.a₁ * W'.a₃
        * P x * P y * Q z ^ 2 + W'.a₄ * P x * P y * Q z ^ 2 + W'.a₁ * W'.a₂ * P x * P z * Q x
        ^ 2 + 3 * W'.a₃ * P x * P z * Q x ^ 2 + 2 * W'.a₂ * P x * P z * Q x * Q y + 2 * W'.a₁
        ^ 2 * W'.a₃ * P x * P z * Q x * Q z + 2 * W'.a₁ * W'.a₄ * P x * P z * Q x * Q z + 2 *
        W'.a₂ * W'.a₃ * P x * P z * Q x * Q z + 2 * W'.a₁ * W'.a₃ * P x * P z * Q y * Q z + 2
        * W'.a₄ * P x * P z * Q y * Q z + 2 * W'.a₁ * W'.a₃ ^ 2 * P x * P z * Q z ^ 2 + 3 *
        W'.a₁ * W'.a₆ * P x * P z * Q z ^ 2 + W'.a₃ * W'.a₄ * P x * P z * Q z ^ 2 + W'.a₁ * P
        y ^ 2 * Q x * Q z + P y ^ 2 * Q y * Q z + W'.a₃ * P y ^ 2 * Q z ^ 2 + W'.a₂ * P y * P
        z * Q x ^ 2 + 2 * W'.a₁ * W'.a₃ * P y * P z * Q x * Q z + 2 * W'.a₄ * P y * P z * Q x
        * Q z + P y * P z * Q y ^ 2 + 2 * W'.a₃ * P y * P z * Q y * Q z + 2 * W'.a₃ ^ 2 * P y
        * P z * Q z ^ 2 + 3 * W'.a₆ * P y * P z * Q z ^ 2 + W'.a₂ * W'.a₃ * P z ^ 2 * Q x ^ 2
        + W'.a₄ * P z ^ 2 * Q x * Q y + W'.a₁ * W'.a₃ ^ 2 * P z ^ 2 * Q x * Q z + 2 * W'.a₃ *
        W'.a₄ * P z ^ 2 * Q x * Q z + W'.a₃ ^ 2 * P z ^ 2 * Q y * Q z + 3 * W'.a₆ * P z ^ 2 *
        Q y * Q z + W'.a₃ ^ 3 * P z ^ 2 * Q z ^ 2 + 3 * W'.a₃ * W'.a₆ * P z ^ 2 * Q z ^ 2

variable (W') in
/-- The second Bosma–Lenstra addition law as a point representative. -/
noncomputable def dblAddXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblAddX P Q, W'.dblAddY P Q, W'.dblAddZ P Q]

/-- Unfold both addition laws and mathlib's doubling to raw polynomials (for the
`linear_combination` normalization steps below). -/
local macro "law_simp" : tactic =>
  `(tactic| simp only [addX, addY, negAddY, addZ, dblAddX, dblAddY, dblAddZ, dblX, dblY,
    negDblY, dblZ, negY, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons])

/-! ## Bihomogeneity (bidegree `(2, 2)`) -/

lemma dblAddX_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddX (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddX P Q := by
  simp only [dblAddX, smul_fin3_ext]
  ring1

lemma dblAddY_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddY (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddY P Q := by
  simp only [dblAddY, smul_fin3_ext]
  ring1

lemma dblAddZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddZ (u • P) (v • Q) = (u * v) ^ 2 * W'.dblAddZ P Q := by
  simp only [dblAddZ, smul_fin3_ext]
  ring1

/-- **(bidegree `(2,2)`, triple form)** The second Bosma-Lenstra law is bihomogeneous of bidegree
`(2,2)`, exactly as mathlib's first law (`addXYZ_smul`). This is what makes the law descend to
`P² × P² ⇢ P²`: rescaling either projective representative rescales the output triple, so the
resulting point of `P²` is unchanged. It is the reason the per-chart-product morphisms agree on
overlaps of chart-products, where the two representatives differ by the transition scalars. -/
lemma dblAddXYZ_smul (P Q : Fin 3 → R) (u v : R) :
    W'.dblAddXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.dblAddXYZ P Q := by
  rw [dblAddXYZ, dblAddX_smul, dblAddY_smul, dblAddZ_smul, smul_fin3, dblAddXYZ]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## The `O`-columns: `O + Q = Q` and `P + O = P`, projectively, with no curve hypothesis -/

lemma dblAddX_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddX ![0, Y₁, 0] Q = Y₁ ^ 2 * ((W'.a₁ * Q x + Q y + W'.a₃ * Q z) * Q x) := by
  rw [dblAddX]; matrix_simp; ring1

lemma dblAddY_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddY ![0, Y₁, 0] Q = Y₁ ^ 2 * ((W'.a₁ * Q x + Q y + W'.a₃ * Q z) * Q y) := by
  rw [dblAddY]; matrix_simp; ring1

lemma dblAddZ_zero_left (Y₁ : R) (Q : Fin 3 → R) :
    W'.dblAddZ ![0, Y₁, 0] Q = Y₁ ^ 2 * ((W'.a₁ * Q x + Q y + W'.a₃ * Q z) * Q z) := by
  rw [dblAddZ]; matrix_simp; ring1

lemma dblAddX_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddX P ![0, Y₂, 0] = Y₂ ^ 2 * (P y * P x) := by
  rw [dblAddX]; matrix_simp; ring1

lemma dblAddY_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddY P ![0, Y₂, 0] = Y₂ ^ 2 * (P y * P y) := by
  rw [dblAddY]; matrix_simp; ring1

lemma dblAddZ_zero_right (P : Fin 3 → R) (Y₂ : R) :
    W'.dblAddZ P ![0, Y₂, 0] = Y₂ ^ 2 * (P y * P z) := by
  rw [dblAddZ]; matrix_simp; ring1

/-! ## The diagonal of law 2 is mathlib's doubling -/

/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblX`. CAS-certified cofactor (3–13 terms; `cof_diag_dblAddX.txt`). -/
lemma dblAddX_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddX P P = W'.dblX P := by
  linear_combination (norm := (law_simp; ring1))
    (
    W'.a₁ ^ 3 * P x + 4 * W'.a₁ * W'.a₂ * P x + 9 * W'.a₃ * P x + 2 * W'.a₁ ^ 2 * P y + 8 *
      W'.a₂ * P y + W'.a₁ ^ 2 * W'.a₃ * P z + 4 * W'.a₂ * W'.a₃ * P z
    ) * (equation_iff P).mp hP

/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblY`. CAS-certified cofactor (`cof_diag_dblAddY.txt`). -/
lemma dblAddY_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddY P P = W'.dblY P := by
  linear_combination (norm := (law_simp; ring1))
    (
    -W'.a₁ ^ 4 * P x - 6 * W'.a₁ ^ 2 * W'.a₂ * P x - 8 * W'.a₂ ^ 2 * P x - 3 * W'.a₄ * P x -
      W'.a₁ ^ 3 * P y - 4 * W'.a₁ * W'.a₂ * P y + 12 * W'.a₃ * P y - W'.a₁ ^ 3 * W'.a₃ * P z -
      W'.a₁ ^ 2 * W'.a₄ * P z - 4 * W'.a₁ * W'.a₂ * W'.a₃ * P z - 4 * W'.a₂ * W'.a₄ * P z + 6
      * W'.a₃ ^ 2 * P z + 9 * W'.a₆ * P z
    ) * (equation_iff P).mp hP

/-- **(T-W7.0c(c3), diagonal)** On the curve, the diagonal of the second addition law is
mathlib's `dblZ`. CAS-certified cofactor (`cof_diag_dblAddZ.txt`). -/
lemma dblAddZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddZ P P = W'.dblZ P := by
  linear_combination (norm := (law_simp; ring1))
    (
    -3 * W'.a₁ * P x - 6 * P y - 3 * W'.a₃ * P z
    ) * (equation_iff P).mp hP

/-- On the curve, the diagonal of the second addition law is mathlib's doubling `dblXYZ`. -/
lemma dblAddXYZ_self {P : Fin 3 → R} (hP : W'.Equation P) : W'.dblAddXYZ P P = W'.dblXYZ P := by
  rw [dblAddXYZ, dblAddX_self hP, dblAddY_self hP, dblAddZ_self hP, dblXYZ]

end WeierstrassCurve.Projective
