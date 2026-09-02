/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenHauptmodul
public import MazurTorsion.EllipticCurve.VeluPair
import Mathlib.Tactic.FieldSimp

/-!
# The explicit first seven-isogeny on the order-seven Tate family

For the order-seven Tate family, the six nonzero points in the marked
subgroup have abscissae `0`, `b`, and `c`, each occurring twice.  Pairing
opposite points in Vélu's formula gives a compact rational map with three
double poles.  This file records that formula, verifies that it lands on the
explicit quotient model, and treats all kernel poles as points at infinity.

The map is deliberately kept as an underlying point function.  Compatibility
with addition, or just with multiplication by seven, is a separate theorem
needed by the order-`49` tower.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The `b` parameter of the order-seven Tate family. -/
@[simp, expose] public def orderSevenB (d : ℚ) : ℚ := d ^ 3 - d ^ 2

/-- The `c` parameter of the order-seven Tate family. -/
@[simp, expose] public def orderSevenC (d : ℚ) : ℚ := d ^ 2 - d

/-- The order-seven Tate family, with marked point `(0,0)`. -/
@[expose] public def orderSevenFamily (d : ℚ) : WeierstrassCurve ℚ :=
  tateNormalCurve (orderSevenB d) (orderSevenC d)

/-- The normalized coefficient model produced by Vélu's formula for the
quotient by the marked order-seven subgroup. -/
@[expose] public def orderSevenQuotient (d : ℚ) : WeierstrassCurve ℚ :=
  ⟨1 - orderSevenC d,
    -orderSevenB d,
    -orderSevenB d,
    -5 * d * (d - 1) * (d ^ 2 - d + 1) *
      (d ^ 3 + 2 * d ^ 2 - 5 * d + 1),
    -d * (d - 1) *
      (d ^ 9 + 9 * d ^ 8 - 37 * d ^ 7 + 70 * d ^ 6 -
        132 * d ^ 5 + 211 * d ^ 4 - 182 * d ^ 3 +
        76 * d ^ 2 - 18 * d + 1)⟩

/-- The discriminant of the source order-seven family. -/
public theorem orderSevenFamily_Δ (d : ℚ) :
    (orderSevenFamily d).Δ =
      d ^ 7 * (d - 1) ^ 7 *
        (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  simpa only [orderSevenFamily, orderSevenB, orderSevenC] using
    orderSeven_Δ d

/-- The discriminant of the marked order-seven quotient model. -/
public theorem orderSevenQuotient_Δ (d : ℚ) :
    (orderSevenQuotient d).Δ =
      d * (d - 1) * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ^ 7 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, orderSevenQuotient,
    orderSevenB, orderSevenC]
  ring

/-- The `c₄` invariant of the marked order-seven quotient model. -/
public theorem orderSevenQuotient_c₄ (d : ℚ) :
    (orderSevenQuotient d).c₄ =
      (d ^ 2 - d + 1) *
        (d ^ 6 + 229 * d ^ 5 + 270 * d ^ 4 - 1695 * d ^ 3 +
          1430 * d ^ 2 - 235 * d + 1) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, orderSevenQuotient,
    orderSevenB, orderSevenC]
  ring

/-- The Fricke/backtracking Hauptmodul on the quotient family.  It is
`49 / t₇` for the source-family Hauptmodul. -/
@[expose] public def orderSevenFrickeParameter (d : ℚ) : ℚ :=
  (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) / (d * (d - 1))

/-- The quotient invariants satisfy the level-seven Hauptmodul identity
for the Fricke/backtracking parameter. -/
public theorem orderSevenQuotient_hauptmodul_identity
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1) :
    orderSevenJNumerator (orderSevenFrickeParameter d) *
        (orderSevenQuotient d).Δ =
      (orderSevenQuotient d).c₄ ^ 3 *
        orderSevenFrickeParameter d ^ 7 := by
  rw [orderSevenQuotient_Δ, orderSevenQuotient_c₄]
  simp only [orderSevenJNumerator, orderSevenFrickeParameter]
  field_simp [hd0, sub_ne_zero.mpr hd1]
  ring

/-- Nonsingularity of the source family implies nonsingularity of its
explicit order-seven quotient model. -/
public noncomputable instance orderSevenQuotient_isElliptic
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    (orderSevenQuotient d).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero,
    orderSevenQuotient_Δ]
  have hsource :
      d ^ 7 * (d - 1) ^ 7 *
          (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ≠ 0 := by
    simpa only [orderSevenFamily_Δ] using
      (orderSevenFamily d).isUnit_Δ.ne_zero
  have hd0 : d ≠ 0 := by
    intro hd
    apply hsource
    simp [hd]
  have hd1 : d ≠ 1 := by
    intro hd
    apply hsource
    simp [hd]
  have hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
    intro hK
    apply hsource
    simp [hK]
  exact mul_ne_zero (mul_ne_zero hd0 (sub_ne_zero.mpr hd1))
    (pow_ne_zero 7 hK)

private def veluSevenT0 (d : ℚ) : ℚ :=
  d ^ 2 * (d - 1) * (d ^ 2 - d - 1)

private def veluSevenU0 (d : ℚ) : ℚ :=
  d ^ 4 * (d - 1) ^ 2

private def veluSevenTB (d : ℚ) : ℚ :=
  d ^ 3 * (d - 1) ^ 2 * (d ^ 2 + d - 1)

private def veluSevenUB (d : ℚ) : ℚ :=
  d ^ 6 * (d - 1) ^ 4

private def veluSevenTC (d : ℚ) : ℚ :=
  d * (d - 1) ^ 3 * (d ^ 2 - 3 * d + 1)

private def veluSevenUC (d : ℚ) : ℚ :=
  d ^ 2 * (d - 1) ^ 6
/-- The abscissa of the explicit Vélu map away from its three kernel
abscissae. -/
@[expose] public def orderSevenVeluX (d x : ℚ) : ℚ :=
  x + (d ^ 2 * (d - 1) * (d ^ 2 - d - 1)) / x +
    (d ^ 4 * (d - 1) ^ 2) / x ^ 2 +
    (d ^ 3 * (d - 1) ^ 2 * (d ^ 2 + d - 1)) /
      (x - orderSevenB d) +
    (d ^ 6 * (d - 1) ^ 4) / (x - orderSevenB d) ^ 2 +
    (d * (d - 1) ^ 3 * (d ^ 2 - 3 * d + 1)) /
      (x - orderSevenC d) +
    (d ^ 2 * (d - 1) ^ 6) / (x - orderSevenC d) ^ 2

/-- The rational differential factor of the explicit Vélu abscissa. -/
@[expose] public def orderSevenVeluDifferential (d x : ℚ) : ℚ :=
  1 - (d ^ 2 * (d - 1) * (d ^ 2 - d - 1)) / x ^ 2 -
    2 * (d ^ 4 * (d - 1) ^ 2) / x ^ 3 -
    (d ^ 3 * (d - 1) ^ 2 * (d ^ 2 + d - 1)) /
      (x - orderSevenB d) ^ 2 -
    2 * (d ^ 6 * (d - 1) ^ 4) / (x - orderSevenB d) ^ 3 -
    (d * (d - 1) ^ 3 * (d ^ 2 - 3 * d + 1)) /
      (x - orderSevenC d) ^ 2 -
    2 * (d ^ 2 * (d - 1) ^ 6) / (x - orderSevenC d) ^ 3

/-- The ordinate of the explicit Vélu map, normalized to preserve the
invariant differential. -/
@[expose] public def orderSevenVeluY (d x y : ℚ) : ℚ :=
  (orderSevenVeluDifferential d x *
        (2 * y + (1 - orderSevenC d) * x - orderSevenB d) -
      (1 - orderSevenC d) * orderSevenVeluX d x +
      orderSevenB d) / 2

/-- The completed ordinate of the Vélu image is the source completed
ordinate multiplied by the explicit differential factor. -/
public theorem orderSevenVelu_completedY (d x y : ℚ) :
    2 * orderSevenVeluY d x y +
        (orderSevenQuotient d).a₁ * orderSevenVeluX d x +
        (orderSevenQuotient d).a₃ =
      orderSevenVeluDifferential d x *
        (2 * y + (orderSevenFamily d).a₁ * x +
          (orderSevenFamily d).a₃) := by
  simp only [orderSevenVeluY, orderSevenQuotient,
    orderSevenFamily, tateNormalCurve]
  ring

/-- The residual level-seven Hauptmodul obtained by applying explicit Tate
normalization to the Vélu image of an affine source point. -/
@[expose] public def orderSevenResidualHauptmodul (d x y : ℚ) : ℚ :=
  orderSevenHauptmodulAt (orderSevenQuotient d)
    (orderSevenVeluX d x) (orderSevenVeluY d x y)

/-- The kernel polynomial whose roots are the three affine pole
abscissae. -/
@[expose] public def orderSevenKernelPolynomial (d x : ℚ) : ℚ :=
  x * (x - orderSevenB d) * (x - orderSevenC d)

/-- The cleared numerator of `orderSevenVeluX`; its denominator is the
square of `orderSevenKernelPolynomial`. -/
@[expose] public def orderSevenVeluXNumerator (d x : ℚ) : ℚ :=
  x ^ 7 - 2 * d * (d - 1) * (d + 1) * x ^ 6 +
    d * (d - 1) *
      (d ^ 5 + 2 * d ^ 4 - 3 * d ^ 3 + 5 * d ^ 2 - 7 * d + 1) *
        x ^ 5 -
    d ^ 3 * (d - 1) ^ 2 *
      (6 * d ^ 4 - 9 * d ^ 3 + 12 * d ^ 2 - 13 * d - 1) * x ^ 4 +
    d ^ 4 * (d - 1) ^ 3 *
      (d ^ 5 + d ^ 4 + 4 * d ^ 3 - 8 * d ^ 2 - 7 * d - 1) * x ^ 3 -
    d ^ 6 * (d - 1) ^ 4 * (d + 1) *
      (3 * d ^ 2 - 5 * d - 3) * x ^ 2 +
    d ^ 8 * (d - 1) ^ 5 * (d ^ 2 - 3 * d - 3) * x +
    d ^ 10 * (d - 1) ^ 6

/-- The cleared numerator of `orderSevenVeluDifferential`; its denominator
is the cube of `orderSevenKernelPolynomial`. -/
@[expose] public def orderSevenVeluDifferentialNumerator (d x : ℚ) : ℚ :=
  x ^ 9 - 3 * d * (d - 1) * (d + 1) * x ^ 8 -
    d * (d - 1) *
      (d ^ 5 - 2 * d ^ 4 - 12 * d ^ 3 + 14 * d ^ 2 - 3 * d + 1) *
        x ^ 7 -
    d ^ 2 * (d - 1) ^ 2 *
      (d ^ 6 - 9 * d ^ 5 + 25 * d ^ 4 - 22 * d ^ 3 +
        16 * d ^ 2 - 4 * d + 1) * x ^ 6 +
    3 * d ^ 4 * (d - 1) ^ 3 *
      (d ^ 4 - 7 * d ^ 3 + 13 * d ^ 2 + 2) * x ^ 5 +
    d ^ 5 * (d - 1) ^ 4 *
      (d ^ 6 - 10 * d ^ 5 + 35 * d ^ 4 - 36 * d ^ 3 -
        21 * d ^ 2 - 18 * d - 1) * x ^ 4 +
    d ^ 7 * (d - 1) ^ 5 *
      (d ^ 5 - 5 * d ^ 4 - 3 * d ^ 3 + 27 * d ^ 2 + 30 * d + 5) *
        x ^ 3 +
    3 * d ^ 9 * (d - 1) ^ 6 *
      (d ^ 3 - 2 * d ^ 2 - 8 * d - 3) * x ^ 2 -
    d ^ 11 * (d - 1) ^ 7 * (d ^ 2 - 7 * d - 7) * x -
    2 * d ^ 13 * (d - 1) ^ 8

/-- Away from the kernel abscissae, the explicit Vélu abscissa is the
cleared numerator divided by the square of the kernel polynomial. -/
public theorem orderSevenVeluX_eq_div
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d) :
    orderSevenVeluX d x =
      orderSevenVeluXNumerator d x /
        orderSevenKernelPolynomial d x ^ 2 := by
  simp only [orderSevenVeluX, orderSevenVeluXNumerator,
    orderSevenKernelPolynomial]
  field_simp [hx0, sub_ne_zero.mpr hxb, sub_ne_zero.mpr hxc]
  simp only [orderSevenB, orderSevenC]
  ring

/-- Away from the kernel abscissae, the explicit Vélu differential is the
cleared numerator divided by the cube of the kernel polynomial. -/
public theorem orderSevenVeluDifferential_eq_div
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d) :
    orderSevenVeluDifferential d x =
      orderSevenVeluDifferentialNumerator d x /
        orderSevenKernelPolynomial d x ^ 3 := by
  simp only [orderSevenVeluDifferential,
    orderSevenVeluDifferentialNumerator, orderSevenKernelPolynomial]
  field_simp [hx0, sub_ne_zero.mpr hxb, sub_ne_zero.mpr hxc]
  simp only [orderSevenB, orderSevenC]
  ring

private theorem orderSevenVeluX_eq_pairCorrections
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d) :
    orderSevenVeluX d x = x +
      Velu.pairXCorrection (orderSevenFamily d) x 0 0 +
      Velu.pairXCorrection (orderSevenFamily d) x
        (orderSevenB d) (orderSevenB d * orderSevenC d) +
      Velu.pairXCorrection (orderSevenFamily d) x
        (orderSevenC d) (orderSevenB d - orderSevenC d) := by
  simp only [orderSevenVeluX, Velu.pairXCorrection,
    orderSevenFamily, tateNormalCurve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp [hx0, sub_ne_zero.mpr hxb, sub_ne_zero.mpr hxc]
  simp only [orderSevenB, orderSevenC]
  ring

private theorem orderSevenVeluDifferential_eq_pairCorrections
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d) :
    orderSevenVeluDifferential d x = 1 +
      Velu.pairDifferentialCorrection (orderSevenFamily d) x 0 0 +
      Velu.pairDifferentialCorrection (orderSevenFamily d) x
        (orderSevenB d) (orderSevenB d * orderSevenC d) +
      Velu.pairDifferentialCorrection (orderSevenFamily d) x
        (orderSevenC d) (orderSevenB d - orderSevenC d) := by
  simp only [orderSevenVeluDifferential,
    Velu.pairDifferentialCorrection,
    orderSevenFamily, tateNormalCurve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  field_simp [hx0, sub_ne_zero.mpr hxb, sub_ne_zero.mpr hxc]
  simp only [orderSevenB, orderSevenC]
  ring

private def sevenOrbitCorrection
    {A : Type*} [AddCommGroup A] (f : A → ℚ) (P T : A) : ℚ :=
  f P + f (P + T) + f (P + (2 : ℕ) • T) +
      f (P + (3 : ℕ) • T) + f (P + (4 : ℕ) • T) +
      f (P + (5 : ℕ) • T) + f (P + (6 : ℕ) • T) -
    (f T + f ((2 : ℕ) • T) + f ((3 : ℕ) • T) +
      f ((4 : ℕ) • T) + f ((5 : ℕ) • T) + f ((6 : ℕ) • T))

private theorem sevenOrbitCorrection_add
    {A : Type*} [AddCommGroup A] (f : A → ℚ) (P T : A)
    (hT : (7 : ℕ) • T = 0) :
    sevenOrbitCorrection f (P + T) T =
      sevenOrbitCorrection f P T := by
  have hshift (n : ℕ) :
      P + T + n • T = P + (n + 1) • T := by
    rw [add_nsmul]
    simp
    abel
  have hshiftOne : P + T + T = P + (2 : ℕ) • T := by
    simp only [two_nsmul]
    abel
  simp only [sevenOrbitCorrection]
  rw [hshiftOne, hshift 2, hshift 3, hshift 4, hshift 5,
    hshift 6, hT, add_zero]
  ring

/-- The completed-square cubic identity behind the explicit Vélu map. -/
public theorem orderSevenVelu_completedSquare
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d) :
    orderSevenVeluDifferential d x ^ 2 *
        (4 * x ^ 3 + (orderSevenFamily d).b₂ * x ^ 2 +
          2 * (orderSevenFamily d).b₄ * x +
          (orderSevenFamily d).b₆) =
      4 * orderSevenVeluX d x ^ 3 +
        (orderSevenQuotient d).b₂ * orderSevenVeluX d x ^ 2 +
        2 * (orderSevenQuotient d).b₄ * orderSevenVeluX d x +
        (orderSevenQuotient d).b₆ := by
  rw [orderSevenVeluDifferential_eq_div hx0 hxb hxc,
    orderSevenVeluX_eq_div hx0 hxb hxc]
  have hkernel : orderSevenKernelPolynomial d x ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero hx0 (sub_ne_zero.mpr hxb))
      (sub_ne_zero.mpr hxc)
  field_simp [hkernel]
  simp only [orderSevenVeluDifferentialNumerator,
    orderSevenVeluXNumerator,
    orderSevenKernelPolynomial,
    orderSevenFamily,
    tateNormalCurve, orderSevenQuotient, orderSevenB, orderSevenC,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

private theorem equation_iff_completedSquare
    (W : WeierstrassCurve ℚ) (x y : ℚ) :
    W.toAffine.Equation x y ↔
      (2 * y + W.a₁ * x + W.a₃) ^ 2 =
        4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  constructor <;> intro h
  · linear_combination 4 * h
  · linear_combination (1 / 4 : ℚ) * h

/-- Away from the three kernel abscissae, the explicit Vélu functions
carry the source affine equation to the quotient affine equation. -/
public theorem orderSevenVelu_equation
    {d x y : ℚ}
    (hcurve : (orderSevenFamily d).toAffine.Equation x y)
    (hx0 : x ≠ 0) (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d) :
    (orderSevenQuotient d).toAffine.Equation
      (orderSevenVeluX d x) (orderSevenVeluY d x y) := by
  apply (equation_iff_completedSquare
    (orderSevenQuotient d) (orderSevenVeluX d x)
      (orderSevenVeluY d x y)).mpr
  have hsource :=
    (equation_iff_completedSquare (orderSevenFamily d) x y).mp hcurve
  have hy :
      2 * orderSevenVeluY d x y +
          (orderSevenQuotient d).a₁ * orderSevenVeluX d x +
          (orderSevenQuotient d).a₃ =
        orderSevenVeluDifferential d x *
          (2 * y + (orderSevenFamily d).a₁ * x +
            (orderSevenFamily d).a₃) := by
    exact orderSevenVelu_completedY d x y
  rw [hy, mul_pow, hsource]
  exact orderSevenVelu_completedSquare hx0 hxb hxc

private theorem orderSeven_tateNextX
    {d x y : ℚ} (hx : x ≠ 0)
    (hcurve : (orderSevenFamily d).toAffine.Equation x y) :
    tateNextX (orderSevenB d) (orderSevenC d) x y =
      orderSevenB d * y / x ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  simp only [orderSevenFamily, tateNormalCurve] at hcurve
  simp only [tateNextX]
  field_simp [hx]
  linear_combination hcurve

private theorem orderSeven_tateNextY
    {d x y : ℚ} (hx : x ≠ 0)
    (hcurve : (orderSevenFamily d).toAffine.Equation x y) :
    tateNextY (orderSevenB d) (orderSevenC d) x y =
      orderSevenB d ^ 2 * (x ^ 2 - y) / x ^ 3 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  simp only [orderSevenFamily, tateNormalCurve] at hcurve
  simp only [tateNextY, tateNextX]
  field_simp [hx]
  linear_combination
    (-orderSevenB d + orderSevenC d * x - x - y) * hcurve

/-- The three affine pole abscissae of the order-seven Vélu map. -/
@[expose] public def OrderSevenKernelX (d x : ℚ) : Prop :=
  x = 0 ∨ x = orderSevenB d ∨ x = orderSevenC d

public instance orderSevenKernelX_decidable (d x : ℚ) :
    Decidable (OrderSevenKernelX d x) := by
  unfold OrderSevenKernelX
  infer_instance

/-- The marked origin is nonsingular on every nonsingular member of the
order-seven family. -/
public theorem orderSevenOrigin_nonsingular
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    (orderSevenFamily d).toAffine.Nonsingular 0 0 := by
  apply (orderSevenFamily d).toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [orderSevenFamily, tateNormalCurve]

/-- The marked order-seven point `(0,0)` on the source family. -/
@[expose] public noncomputable def orderSevenOrigin
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    (orderSevenFamily d).toAffine.Point :=
  .some 0 0 (orderSevenOrigin_nonsingular d)

/-- Nonsingularity excludes the three bad parameters of the order-seven
family. -/
public theorem orderSevenFamily_parameters_ne
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    d ≠ 0 ∧ d ≠ 1 ∧
      d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
  have hsource :
      d ^ 7 * (d - 1) ^ 7 *
          (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) ≠ 0 := by
    simpa only [orderSevenFamily_Δ] using
      (orderSevenFamily d).isUnit_Δ.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    apply hsource
    simp [hd]
  · intro hd
    apply hsource
    simp [hd]
  · intro hK
    apply hsource
    simp [hK]

/-- The Fricke/backtracking Hauptmodul is nonzero on every nonsingular
member of the source family. -/
public theorem orderSevenFrickeParameter_ne_zero
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    orderSevenFrickeParameter d ≠ 0 := by
  obtain ⟨hd0, hd1, hK⟩ := orderSevenFamily_parameters_ne d
  exact div_ne_zero hK
    (mul_ne_zero hd0 (sub_ne_zero.mpr hd1))

private theorem orderSevenB_ne_zero
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    orderSevenB d ≠ 0 := by
  obtain ⟨hd0, hd1, -⟩ := orderSevenFamily_parameters_ne d
  rw [show orderSevenB d = d ^ 2 * (d - 1) by
    simp only [orderSevenB]
    ring]
  exact mul_ne_zero (pow_ne_zero 2 hd0) (sub_ne_zero.mpr hd1)

private theorem orderSevenC_ne_zero
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    orderSevenC d ≠ 0 := by
  obtain ⟨hd0, hd1, -⟩ := orderSevenFamily_parameters_ne d
  rw [show orderSevenC d = d * (d - 1) by
    simp only [orderSevenC]
    ring]
  exact mul_ne_zero hd0 (sub_ne_zero.mpr hd1)

/-- The marked origin is killed by seven on the parametrized family. -/
@[simp]
public theorem seven_nsmul_orderSevenOrigin
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    (7 : ℕ) • orderSevenOrigin d = 0 := by
  let b := orderSevenB d
  let c := orderSevenC d
  let h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0 := by
    simpa only [orderSevenFamily, b, c] using
      orderSevenOrigin_nonsingular d
  let P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  change (7 : ℕ) • P = 0
  have hb : b ≠ 0 := by simpa only [b] using orderSevenB_ne_zero d
  have hc : c ≠ 0 := by simpa only [c] using orderSevenC_ne_zero d
  have hrel : b ^ 2 - b * c - c ^ 3 = 0 := by
    simp only [b, c, orderSevenB, orderSevenC]
    ring
  obtain ⟨h₃, hthree⟩ :=
    three_nsmul_origin_coordinates b c hb h00
  obtain ⟨h₄, hfour⟩ :=
    four_mul_origin_coordinates b c hb hc h00
  have hx₄ : b * (b - c) / c ^ 2 = c := by
    field_simp [hc]
    linear_combination hrel
  have hy₄ : b ^ 2 * (c ^ 2 + c - b) / c ^ 3 = c ^ 2 := by
    field_simp [hc]
    linear_combination (-b + c ^ 2) * hrel
  have hfour' :
      (4 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2)
          (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
    rw [show (4 : ℕ) • P = P + P + P + P by abel]
    simpa only [P] using hfour
  have hthree' :
      (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
    simpa only [P] using hthree
  have hfour_neg : (4 : ℕ) • P = -((3 : ℕ) • P) := by
    rw [hfour', hthree', WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some
      (tateNormalCurve b c) hx₄ (by
        rw [hy₄]
        simp only [WeierstrassCurve.Affine.negY, tateNormalCurve]
        ring)
  calc
    (7 : ℕ) • P = (4 : ℕ) • P + (3 : ℕ) • P := by abel
    _ = 0 := by rw [hfour_neg]; exact neg_add_cancel _

/-- The marked origin has exact additive order seven. -/
public theorem addOrderOf_orderSevenOrigin
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    addOrderOf (orderSevenOrigin d) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  apply addOrderOf_eq_prime (seven_nsmul_orderSevenOrigin d)
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

private theorem orderSevenVelu_orbitFormulas
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d) :
    orderSevenVeluX d x =
        sevenOrbitCorrection
          (Velu.pointXOrZero (orderSevenFamily d))
          (WeierstrassCurve.Affine.Point.some x y hP)
          (orderSevenOrigin d) ∧
      orderSevenVeluDifferential d x *
          (2 * y + (orderSevenFamily d).a₁ * x +
            (orderSevenFamily d).a₃) =
        sevenOrbitCorrection
          (Velu.pointCompletedYOrZero (orderSevenFamily d))
          (WeierstrassCurve.Affine.Point.some x y hP)
          (orderSevenOrigin d) := by
  let P : (orderSevenFamily d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hP
  let T : (orderSevenFamily d).toAffine.Point := orderSevenOrigin d
  have hT7 : (7 : ℕ) • T = 0 := by
    simpa only [T] using seven_nsmul_orderSevenOrigin d
  have hb : orderSevenB d ≠ 0 := orderSevenB_ne_zero d
  have h00 := orderSevenOrigin_nonsingular d
  have hT0 : T = WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    dsimp only [T, orderSevenOrigin]
  obtain ⟨h₂, hT2raw⟩ :=
    two_nsmul_origin_coordinates
      (orderSevenB d) (orderSevenC d) hb h00
  obtain ⟨h₃, hT3raw⟩ :=
    three_nsmul_origin_coordinates
      (orderSevenB d) (orderSevenC d) hb h00
  let h₂' : (orderSevenFamily d).toAffine.Nonsingular
      (orderSevenB d) (orderSevenB d * orderSevenC d) := by
    simpa only [orderSevenFamily] using h₂
  let h₃' : (orderSevenFamily d).toAffine.Nonsingular
      (orderSevenC d) (orderSevenB d - orderSevenC d) := by
    simpa only [orderSevenFamily] using h₃
  have hT2 : (2 : ℕ) • T =
      WeierstrassCurve.Affine.Point.some
        (orderSevenB d) (orderSevenB d * orderSevenC d) h₂' := by
    rw [hT0]
    exact hT2raw.trans (WeierstrassCurve.Affine.Point.some_eq_some
      (orderSevenFamily d) rfl rfl)
  have hT3 : (3 : ℕ) • T =
      WeierstrassCurve.Affine.Point.some
        (orderSevenC d) (orderSevenB d - orderSevenC d) h₃' := by
    rw [hT0]
    exact hT3raw.trans (WeierstrassCurve.Affine.Point.some_eq_some
      (orderSevenFamily d) rfl rfl)
  have hT6 : (6 : ℕ) • T = -T := by
    calc
      (6 : ℕ) • T = (7 : ℕ) • T - T := by abel
      _ = -T := by rw [hT7]; simp
  have hT5 : (5 : ℕ) • T = -((2 : ℕ) • T) := by
    calc
      (5 : ℕ) • T = (7 : ℕ) • T - (2 : ℕ) • T := by abel
      _ = -((2 : ℕ) • T) := by rw [hT7]; simp
  have hT4 : (4 : ℕ) • T = -((3 : ℕ) • T) := by
    calc
      (4 : ℕ) • T = (7 : ℕ) • T - (3 : ℕ) • T := by abel
      _ = -((3 : ℕ) • T) := by rw [hT7]; simp
  have hpair0 := Velu.pointXOrZero_add_pair
    (orderSevenFamily d) hP h00 hx0
  have hpairB := Velu.pointXOrZero_add_pair
    (orderSevenFamily d) hP h₂' hxb
  have hpairC := Velu.pointXOrZero_add_pair
    (orderSevenFamily d) hP h₃' hxc
  have hpairZ0 := Velu.pointCompletedYOrZero_add_pair
    (orderSevenFamily d) hP h00 hx0
  have hpairZB := Velu.pointCompletedYOrZero_add_pair
    (orderSevenFamily d) hP h₂' hxb
  have hpairZC := Velu.pointCompletedYOrZero_add_pair
    (orderSevenFamily d) hP h₃' hxc
  constructor
  · rw [orderSevenVeluX_eq_pairCorrections hx0 hxb hxc]
    change x +
        Velu.pairXCorrection (orderSevenFamily d) x 0 0 +
        Velu.pairXCorrection (orderSevenFamily d) x
          (orderSevenB d) (orderSevenB d * orderSevenC d) +
        Velu.pairXCorrection (orderSevenFamily d) x
          (orderSevenC d) (orderSevenB d - orderSevenC d) =
      sevenOrbitCorrection (Velu.pointXOrZero (orderSevenFamily d)) P T
    simp only [sevenOrbitCorrection]
    rw [hT2, hT3, hT4, hT5, hT6, hT2, hT3]
    rw [hT0]
    simp only [P, Velu.pointXOrZero_some, Velu.pointXOrZero_neg]
    linear_combination -hpair0 - hpairB - hpairC
  · rw [orderSevenVeluDifferential_eq_pairCorrections hx0 hxb hxc]
    change (1 +
        Velu.pairDifferentialCorrection (orderSevenFamily d) x 0 0 +
        Velu.pairDifferentialCorrection (orderSevenFamily d) x
          (orderSevenB d) (orderSevenB d * orderSevenC d) +
        Velu.pairDifferentialCorrection (orderSevenFamily d) x
          (orderSevenC d) (orderSevenB d - orderSevenC d)) *
          (2 * y + (orderSevenFamily d).a₁ * x +
            (orderSevenFamily d).a₃) =
      sevenOrbitCorrection
        (Velu.pointCompletedYOrZero (orderSevenFamily d)) P T
    simp only [sevenOrbitCorrection]
    rw [hT2, hT3, hT4, hT5, hT6, hT2, hT3]
    rw [hT0]
    simp only [P, Velu.pointCompletedYOrZero_some,
      Velu.pointCompletedYOrZero_neg]
    linear_combination -hpairZ0 - hpairZB - hpairZC

/-- The denominator-safe affine value of the explicit Vélu map. -/
@[expose] public noncomputable def orderSevenVeluPoint
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hx0 : x ≠ 0) (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d) :
    (orderSevenQuotient d).toAffine.Point :=
  .some (orderSevenVeluX d x) (orderSevenVeluY d x y)
    ((orderSevenQuotient d).toAffine.equation_iff_nonsingular.mp
      (orderSevenVelu_equation hP.1 hx0 hxb hxc))

/-- Away from the kernel poles, the explicit Vélu point is invariant under
translation by the marked order-seven point. -/
public theorem orderSevenVeluPoint_add_origin
    {d x y x' y' : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hP' : (orderSevenFamily d).toAffine.Nonsingular x' y')
    (hadd :
      (WeierstrassCurve.Affine.Point.some x y hP :
          (orderSevenFamily d).toAffine.Point) + orderSevenOrigin d =
        WeierstrassCurve.Affine.Point.some x' y' hP')
    (hx0 : x ≠ 0) (hxb : x ≠ orderSevenB d)
    (hxc : x ≠ orderSevenC d)
    (hx0' : x' ≠ 0) (hxb' : x' ≠ orderSevenB d)
    (hxc' : x' ≠ orderSevenC d) :
    orderSevenVeluPoint hP' hx0' hxb' hxc' =
      orderSevenVeluPoint hP hx0 hxb hxc := by
  let P : (orderSevenFamily d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hP
  let P' : (orderSevenFamily d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x' y' hP'
  let T : (orderSevenFamily d).toAffine.Point := orderSevenOrigin d
  have hadd' : P + T = P' := by
    simpa only [P, P', T] using hadd
  have hT7 : (7 : ℕ) • T = 0 := by
    simpa only [T] using seven_nsmul_orderSevenOrigin d
  have hform := orderSevenVelu_orbitFormulas hP hx0 hxb hxc
  have hform' := orderSevenVelu_orbitFormulas hP' hx0' hxb' hxc'
  have hx : orderSevenVeluX d x' = orderSevenVeluX d x := by
    calc
      orderSevenVeluX d x' =
          sevenOrbitCorrection
            (Velu.pointXOrZero (orderSevenFamily d)) P' T := by
        simpa only [P', T] using hform'.1
      _ = sevenOrbitCorrection
          (Velu.pointXOrZero (orderSevenFamily d)) P T := by
        rw [← hadd']
        exact sevenOrbitCorrection_add _ P T hT7
      _ = orderSevenVeluX d x := by
        simpa only [P, T] using hform.1.symm
  have hcompleted :
      2 * orderSevenVeluY d x' y' +
          (orderSevenQuotient d).a₁ * orderSevenVeluX d x' +
          (orderSevenQuotient d).a₃ =
        2 * orderSevenVeluY d x y +
          (orderSevenQuotient d).a₁ * orderSevenVeluX d x +
          (orderSevenQuotient d).a₃ := by
    calc
      2 * orderSevenVeluY d x' y' +
            (orderSevenQuotient d).a₁ * orderSevenVeluX d x' +
            (orderSevenQuotient d).a₃ =
          orderSevenVeluDifferential d x' *
            (2 * y' + (orderSevenFamily d).a₁ * x' +
              (orderSevenFamily d).a₃) :=
        orderSevenVelu_completedY d x' y'
      _ = sevenOrbitCorrection
          (Velu.pointCompletedYOrZero (orderSevenFamily d)) P' T := by
        simpa only [P', T] using hform'.2
      _ = sevenOrbitCorrection
          (Velu.pointCompletedYOrZero (orderSevenFamily d)) P T := by
        rw [← hadd']
        exact sevenOrbitCorrection_add _ P T hT7
      _ = orderSevenVeluDifferential d x *
          (2 * y + (orderSevenFamily d).a₁ * x +
            (orderSevenFamily d).a₃) := by
        simpa only [P, T] using hform.2.symm
      _ = 2 * orderSevenVeluY d x y +
          (orderSevenQuotient d).a₁ * orderSevenVeluX d x +
          (orderSevenQuotient d).a₃ :=
        (orderSevenVelu_completedY d x y).symm
  have hy : orderSevenVeluY d x' y' = orderSevenVeluY d x y := by
    linear_combination
      (1 / 2 : ℚ) * hcompleted -
        ((orderSevenQuotient d).a₁ / 2) * hx
  simp only [orderSevenVeluPoint]
  exact WeierstrassCurve.Affine.Point.some_eq_some
    (orderSevenQuotient d) hx hy

/-- The total explicit Vélu point function.  The point at infinity and
the six affine kernel points are sent to infinity. -/
@[expose] public noncomputable def orderSevenPointMap
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    (orderSevenFamily d).toAffine.Point →
      (orderSevenQuotient d).toAffine.Point
  | 0 => 0
  | .some x _y hP =>
      if hx : OrderSevenKernelX d x then 0
      else orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h)))

@[simp]
public theorem orderSevenPointMap_zero
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    orderSevenPointMap d 0 = 0 :=
  rfl

/-- Evaluation of the total point map away from the kernel poles. -/
public theorem orderSevenPointMap_some_of_not_kernelX
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : ¬OrderSevenKernelX d x) :
    orderSevenPointMap d (.some x y hP) =
      orderSevenVeluPoint hP
        (fun h ↦ hx (Or.inl h))
        (fun h ↦ hx (Or.inr (Or.inl h)))
        (fun h ↦ hx (Or.inr (Or.inr h))) := by
  simp [orderSevenPointMap, hx]

/-- An affine point maps to infinity exactly at one of the three kernel
abscissae. -/
public theorem orderSevenPointMap_some_eq_zero_iff
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y) :
    orderSevenPointMap d (.some x y hP) = 0 ↔
      OrderSevenKernelX d x := by
  by_cases hx : OrderSevenKernelX d x
  · simp [orderSevenPointMap, hx]
  · rw [orderSevenPointMap_some_of_not_kernelX hP hx]
    exact ⟨fun h ↦ (WeierstrassCurve.Affine.Point.some_ne_zero _ h).elim,
      fun h ↦ (hx h).elim⟩

@[simp]
public theorem orderSevenPointMap_origin
    (d : ℚ) [(orderSevenFamily d).IsElliptic] :
    orderSevenPointMap d (orderSevenOrigin d) = 0 := by
  apply (orderSevenPointMap_some_eq_zero_iff
    (orderSevenOrigin_nonsingular d)).mpr
  exact Or.inl rfl

private theorem seven_nsmul_of_kernelX
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hx : OrderSevenKernelX d x) :
    (7 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y hP :
          (orderSevenFamily d).toAffine.Point) = 0 := by
  let P : (orderSevenFamily d).toAffine.Point := orderSevenOrigin d
  have hb : orderSevenB d ≠ 0 := orderSevenB_ne_zero d
  have h00 := orderSevenOrigin_nonsingular d
  obtain ⟨h₂, htwo⟩ :=
    two_nsmul_origin_coordinates (orderSevenB d) (orderSevenC d) hb h00
  obtain ⟨h₃, hthree⟩ :=
    three_nsmul_origin_coordinates (orderSevenB d) (orderSevenC d) hb h00
  have hseven : (7 : ℕ) • P = 0 := seven_nsmul_orderSevenOrigin d
  have hmultiple (n : ℕ) : (7 : ℕ) • (n • P) = 0 := by
    calc
      (7 : ℕ) • (n • P) = n • ((7 : ℕ) • P) := by
        simp only [← mul_nsmul, Nat.mul_comm]
      _ = 0 := by rw [hseven]; simp
  have hnegative {Q : (orderSevenFamily d).toAffine.Point}
      (hQ : (7 : ℕ) • Q = 0) : (7 : ℕ) • (-Q) = 0 := by
    rw [neg_nsmul, hQ, neg_zero]
  rcases hx with hx0 | hxb | hxc
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some 0 0 h00 ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some 0 0 h00) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (orderSevenFamily d).toAffine)).mp hx0
    rcases hxiff with h | h
    · rw [h]
      exact hseven
    · rw [h]
      exact hnegative hseven
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some
              (orderSevenB d) (orderSevenB d * orderSevenC d) h₂ ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some
              (orderSevenB d) (orderSevenB d * orderSevenC d) h₂) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (orderSevenFamily d).toAffine)).mp hxb
    rcases hxiff with h | h
    · rw [h, ← htwo]
      exact hmultiple 2
    · rw [h, ← htwo]
      exact hnegative (hmultiple 2)
  · have hxiff :
        (WeierstrassCurve.Affine.Point.some x y hP =
            WeierstrassCurve.Affine.Point.some
              (orderSevenC d) (orderSevenB d - orderSevenC d) h₃ ∨
          WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some
              (orderSevenC d) (orderSevenB d - orderSevenC d) h₃) :=
      (WeierstrassCurve.Affine.Point.X_eq_iff
        (W := (orderSevenFamily d).toAffine)).mp hxc
    rcases hxiff with h | h
    · rw [h, ← hthree]
      exact hmultiple 3
    · rw [h, ← hthree]
      exact hnegative (hmultiple 3)

/-- On an affine point of exact order `49`, the total explicit point map is
invariant under translation by the marked order-seven point. -/
private theorem orderSevenPointMap_add_origin_of_order_fortyNine_affine
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49) :
    orderSevenPointMap d
        ((WeierstrassCurve.Affine.Point.some x y hP :
          (orderSevenFamily d).toAffine.Point) + orderSevenOrigin d) =
      orderSevenPointMap d
        (WeierstrassCurve.Affine.Point.some x y hP) := by
  let P : (orderSevenFamily d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hP
  let T : (orderSevenFamily d).toAffine.Point := orderSevenOrigin d
  have h7P : (7 : ℕ) • P ≠ 0 := by
    intro hzero
    have hdvd : (49 : ℕ) ∣ 7 := by
      rw [← horder]
      exact addOrderOf_dvd_of_nsmul_eq_zero hzero
    norm_num at hdvd
  have hT7 : (7 : ℕ) • T = 0 := by
    simpa only [T] using seven_nsmul_orderSevenOrigin d
  have hsumne : P + T ≠ 0 := by
    intro hzero
    have hseven : (7 : ℕ) • (P + T) = 0 := by
      rw [hzero]
      simp
    rw [nsmul_add, hT7, add_zero] at hseven
    exact h7P hseven
  obtain ⟨x', y', hP', hadd⟩ :
      ∃ (x' y' : ℚ)
        (hP' : (orderSevenFamily d).toAffine.Nonsingular x' y'),
          P + T = WeierstrassCurve.Affine.Point.some x' y' hP' := by
    cases hsum : P + T with
    | zero => exact (hsumne hsum).elim
    | some x' y' hP' => exact ⟨x', y', hP', rfl⟩
  have hx : ¬OrderSevenKernelX d x := by
    intro hkernel
    exact h7P (seven_nsmul_of_kernelX hP hkernel)
  have h7P' :
      (7 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x' y' hP' :
          (orderSevenFamily d).toAffine.Point) ≠ 0 := by
    intro hzero
    rw [← hadd, nsmul_add, hT7, add_zero] at hzero
    exact h7P hzero
  have hx' : ¬OrderSevenKernelX d x' := by
    intro hkernel
    exact h7P' (seven_nsmul_of_kernelX hP' hkernel)
  change orderSevenPointMap d (P + T) = orderSevenPointMap d P
  rw [hadd, orderSevenPointMap_some_of_not_kernelX hP' hx',
    show P = WeierstrassCurve.Affine.Point.some x y hP by rfl,
    orderSevenPointMap_some_of_not_kernelX hP hx]
  exact orderSevenVeluPoint_add_origin hP hP'
    (by simpa only [P, T] using hadd)
    (fun h ↦ hx (Or.inl h))
    (fun h ↦ hx (Or.inr (Or.inl h)))
    (fun h ↦ hx (Or.inr (Or.inr h)))
    (fun h ↦ hx' (Or.inl h))
    (fun h ↦ hx' (Or.inr (Or.inl h)))
    (fun h ↦ hx' (Or.inr (Or.inr h)))

private theorem addOrderOf_add_nsmul_orderSevenOrigin
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) (n : ℕ) :
    addOrderOf (Q + n • orderSevenOrigin d) = 49 := by
  let T : (orderSevenFamily d).toAffine.Point := orderSevenOrigin d
  have h7Q : (7 : ℕ) • Q ≠ 0 := by
    intro hzero
    have hdvd : (49 : ℕ) ∣ 7 := by
      rw [← hQ]
      exact addOrderOf_dvd_of_nsmul_eq_zero hzero
    norm_num at hdvd
  have h49Q : (49 : ℕ) • Q = 0 := by
    rw [← hQ]
    exact addOrderOf_nsmul_eq_zero Q
  have h7T : (7 : ℕ) • T = 0 := by
    simpa only [T] using seven_nsmul_orderSevenOrigin d
  have h49T : (49 : ℕ) • T = 0 := by
    rw [show (49 : ℕ) = 7 * 7 by norm_num, mul_nsmul, h7T]
    simp
  have h7nT : (7 : ℕ) • (n • T) = 0 := by
    calc
      (7 : ℕ) • (n • T) = n • ((7 : ℕ) • T) := by
        simp only [← mul_nsmul, Nat.mul_comm]
      _ = 0 := by rw [h7T]; simp
  have h49nT : (49 : ℕ) • (n • T) = 0 := by
    calc
      (49 : ℕ) • (n • T) = n • ((49 : ℕ) • T) := by
        simp only [← mul_nsmul, Nat.mul_comm]
      _ = 0 := by rw [h49T]; simp
  have h7 : (7 : ℕ) • (Q + n • T) ≠ 0 := by
    intro hzero
    rw [nsmul_add, h7nT, add_zero] at hzero
    exact h7Q hzero
  have h49 : (49 : ℕ) • (Q + n • T) = 0 := by
    rw [nsmul_add, h49Q, h49nT, add_zero]
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hresult := addOrderOf_eq_prime_pow
    (x := Q + n • T) (p := 7) (n := 1)
    (by norm_num only [pow_one]; exact h7)
    (by
      norm_num only [Nat.reduceAdd, pow_succ, pow_one, Nat.reduceMul]
      exact h49)
  norm_num at hresult
  simpa only [T] using hresult

/-- Translation invariance at exact order `49`, stated for an arbitrary
source point. -/
public theorem orderSevenPointMap_add_origin_of_order_fortyNine
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) :
    orderSevenPointMap d (Q + orderSevenOrigin d) =
      orderSevenPointMap d Q := by
  cases Q with
  | zero =>
      have hfalse : (1 : ℕ) = 49 := by
        rw [← hQ]
        exact (addOrderOf_zero
          (G := (orderSevenFamily d).toAffine.Point)).symm
      norm_num at hfalse
  | some x y hP =>
      exact orderSevenPointMap_add_origin_of_order_fortyNine_affine
        hP hQ

/-- Repeated translation by the marked kernel point does not change the
explicit image of an exact-order-`49` point. -/
public theorem orderSevenPointMap_add_nsmul_origin_of_order_fortyNine
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49) (n : ℕ) :
    orderSevenPointMap d (Q + n • orderSevenOrigin d) =
      orderSevenPointMap d Q := by
  induction n with
  | zero => simp
  | succ n ih =>
      have horder := addOrderOf_add_nsmul_orderSevenOrigin hQ n
      calc
        orderSevenPointMap d (Q + (n + 1) • orderSevenOrigin d) =
            orderSevenPointMap d
              ((Q + n • orderSevenOrigin d) + orderSevenOrigin d) := by
          congr 1
          rw [add_nsmul]
          simp
          abel
        _ = orderSevenPointMap d (Q + n • orderSevenOrigin d) :=
          orderSevenPointMap_add_origin_of_order_fortyNine horder
        _ = orderSevenPointMap d Q := ih

/-- Every point in the zero fiber is one of the seven multiples of the
marked kernel generator. -/
public theorem exists_eq_nsmul_orderSevenOrigin_of_pointMap_eq_zero
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {R : (orderSevenFamily d).toAffine.Point}
    (hR : orderSevenPointMap d R = 0) :
    ∃ n : ℕ, n < 7 ∧ R = n • orderSevenOrigin d := by
  cases R with
  | zero => exact ⟨0, by norm_num, by rfl⟩
  | some x y hP =>
      let T : (orderSevenFamily d).toAffine.Point := orderSevenOrigin d
      have h00 := orderSevenOrigin_nonsingular d
      have hT0 : T =
          WeierstrassCurve.Affine.Point.some 0 0 h00 := by
        dsimp only [T, orderSevenOrigin]
      have hb : orderSevenB d ≠ 0 := orderSevenB_ne_zero d
      obtain ⟨h₂, htwoRaw⟩ :=
        two_nsmul_origin_coordinates
          (orderSevenB d) (orderSevenC d) hb h00
      obtain ⟨h₃, hthreeRaw⟩ :=
        three_nsmul_origin_coordinates
          (orderSevenB d) (orderSevenC d) hb h00
      have hT2 : (2 : ℕ) • T =
          WeierstrassCurve.Affine.Point.some
            (orderSevenB d) (orderSevenB d * orderSevenC d) h₂ := by
        rw [hT0]
        exact htwoRaw
      have hT3 : (3 : ℕ) • T =
          WeierstrassCurve.Affine.Point.some
            (orderSevenC d) (orderSevenB d - orderSevenC d) h₃ := by
        rw [hT0]
        exact hthreeRaw
      have hT7 : (7 : ℕ) • T = 0 := by
        simpa only [T] using seven_nsmul_orderSevenOrigin d
      have hT6 : (6 : ℕ) • T = -T := by
        calc
          (6 : ℕ) • T = (7 : ℕ) • T - T := by abel
          _ = -T := by rw [hT7]; simp
      have hT5 : (5 : ℕ) • T = -((2 : ℕ) • T) := by
        calc
          (5 : ℕ) • T = (7 : ℕ) • T - (2 : ℕ) • T := by abel
          _ = -((2 : ℕ) • T) := by rw [hT7]; simp
      have hT4 : (4 : ℕ) • T = -((3 : ℕ) • T) := by
        calc
          (4 : ℕ) • T = (7 : ℕ) • T - (3 : ℕ) • T := by abel
          _ = -((3 : ℕ) • T) := by rw [hT7]; simp
      have hx : OrderSevenKernelX d x :=
        (orderSevenPointMap_some_eq_zero_iff hP).mp hR
      rcases hx with hx0 | hxb | hxc
      · have hxiff :
            (WeierstrassCurve.Affine.Point.some x y hP =
                WeierstrassCurve.Affine.Point.some 0 0 h00 ∨
              WeierstrassCurve.Affine.Point.some x y hP =
                -WeierstrassCurve.Affine.Point.some 0 0 h00) :=
          (WeierstrassCurve.Affine.Point.X_eq_iff
            (W := (orderSevenFamily d).toAffine)).mp hx0
        rcases hxiff with h | h
        · refine ⟨1, by norm_num, ?_⟩
          simpa only [T, one_nsmul] using h.trans hT0.symm
        · refine ⟨6, by norm_num, ?_⟩
          change WeierstrassCurve.Affine.Point.some x y hP =
            (6 : ℕ) • T
          calc
            WeierstrassCurve.Affine.Point.some x y hP =
                -WeierstrassCurve.Affine.Point.some 0 0 h00 := h
            _ = -T := congrArg Neg.neg hT0.symm
            _ = (6 : ℕ) • T := hT6.symm
      · have hxiff :
            (WeierstrassCurve.Affine.Point.some x y hP =
                WeierstrassCurve.Affine.Point.some
                  (orderSevenB d) (orderSevenB d * orderSevenC d) h₂ ∨
              WeierstrassCurve.Affine.Point.some x y hP =
                -WeierstrassCurve.Affine.Point.some
                  (orderSevenB d) (orderSevenB d * orderSevenC d) h₂) :=
          (WeierstrassCurve.Affine.Point.X_eq_iff
            (W := (orderSevenFamily d).toAffine)).mp hxb
        rcases hxiff with h | h
        · exact ⟨2, by norm_num, by
            change WeierstrassCurve.Affine.Point.some x y hP =
              (2 : ℕ) • T
            exact h.trans hT2.symm⟩
        · exact ⟨5, by norm_num, by
            change WeierstrassCurve.Affine.Point.some x y hP =
              (5 : ℕ) • T
            exact h.trans ((congrArg Neg.neg hT2.symm).trans hT5.symm)⟩
      · have hxiff :
            (WeierstrassCurve.Affine.Point.some x y hP =
                WeierstrassCurve.Affine.Point.some
                  (orderSevenC d) (orderSevenB d - orderSevenC d) h₃ ∨
              WeierstrassCurve.Affine.Point.some x y hP =
                -WeierstrassCurve.Affine.Point.some
                  (orderSevenC d) (orderSevenB d - orderSevenC d) h₃) :=
          (WeierstrassCurve.Affine.Point.X_eq_iff
            (W := (orderSevenFamily d).toAffine)).mp hxc
        rcases hxiff with h | h
        · exact ⟨3, by norm_num, by
            change WeierstrassCurve.Affine.Point.some x y hP =
              (3 : ℕ) • T
            exact h.trans hT3.symm⟩
        · exact ⟨4, by norm_num, by
            change WeierstrassCurve.Affine.Point.some x y hP =
              (4 : ℕ) • T
            exact h.trans ((congrArg Neg.neg hT3.symm).trans hT4.symm)⟩

/-- Every point in the zero fiber of the explicit Vélu function is killed
by seven. -/
public theorem orderSevenPointMap_kernel_killed_by_seven
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {P : (orderSevenFamily d).toAffine.Point}
    (hP : orderSevenPointMap d P = 0) :
    (7 : ℕ) • P = 0 := by
  cases P with
  | zero => exact nsmul_zero 7
  | some x y h =>
      exact seven_nsmul_of_kernelX h
        ((orderSevenPointMap_some_eq_zero_iff h).mp hP)

/-- An affine point of exact order `49` cannot lie in the marked
order-seven kernel. -/
public theorem not_orderSevenKernelX_of_order_fortyNine
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49) :
    ¬OrderSevenKernelX d x := by
  intro hx
  have hzero : orderSevenPointMap d
      (WeierstrassCurve.Affine.Point.some x y hP) = 0 :=
    (orderSevenPointMap_some_eq_zero_iff hP).2 hx
  have hkilled := orderSevenPointMap_kernel_killed_by_seven hzero
  have hdvd : (49 : ℕ) ∣ 7 := by
    rw [← horder]
    exact addOrderOf_dvd_of_nsmul_eq_zero hkilled
  norm_num at hdvd

/-- The exact-order consequence needed at the first stage of the order-`49`
tower.  Full additivity of the explicit point function is unnecessary here:
it suffices to know compatibility with the single multiple `7 • Q`. -/
public theorem addOrderOf_orderSevenPointMap_of_order_fortyNine
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : orderSevenPointMap d ((7 : ℕ) • Q) = 0)
    (hmap : orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • orderSevenPointMap d Q) :
    addOrderOf (orderSevenPointMap d Q) = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  apply addOrderOf_eq_prime
  · rw [← hmap]
    exact hkernel
  · intro hzero
    have hkilled : (7 : ℕ) • Q = 0 :=
      orderSevenPointMap_kernel_killed_by_seven hzero
    have hdvd : (49 : ℕ) ∣ 7 := by
      rw [← hQ]
      exact addOrderOf_dvd_of_nsmul_eq_zero hkilled
    norm_num at hdvd

/-- The order-`49` image supplies the residual nonzero level-seven
Hauptmodul on the quotient.  This is the downstream consumer of the generic
exact-order-seven normalization theorem. -/
public theorem exists_orderSevenHauptmodul_of_order_fortyNine_image
    {d : ℚ} [(orderSevenFamily d).IsElliptic]
    {Q : (orderSevenFamily d).toAffine.Point}
    (hQ : addOrderOf Q = 49)
    (hkernel : orderSevenPointMap d ((7 : ℕ) • Q) = 0)
    (hmap : orderSevenPointMap d ((7 : ℕ) • Q) =
      (7 : ℕ) • orderSevenPointMap d Q) :
    ∃ B : ℚ, B ≠ 0 ∧
      orderSevenJNumerator B * (orderSevenQuotient d).Δ =
        (orderSevenQuotient d).c₄ ^ 3 * B ^ 7 := by
  exact exists_orderSevenHauptmodul_of_exactOrder
    (orderSevenQuotient d) (orderSevenPointMap d Q)
      (addOrderOf_orderSevenPointMap_of_order_fortyNine
        hQ hkernel hmap)

/-- For an affine order-`49` point, the residual Hauptmodul is the explicit
Tate-normalization expression evaluated at its Vélu image. -/
public theorem orderSevenResidualHauptmodul_spec_of_order_fortyNine
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hmap : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) =
        (7 : ℕ) • orderSevenPointMap d
          (WeierstrassCurve.Affine.Point.some x y hP)) :
    orderSevenResidualHauptmodul d x y ≠ 0 ∧
      orderSevenJNumerator (orderSevenResidualHauptmodul d x y) *
          (orderSevenQuotient d).Δ =
        (orderSevenQuotient d).c₄ ^ 3 *
          orderSevenResidualHauptmodul d x y ^ 7 := by
  have hx : ¬OrderSevenKernelX d x := by
    intro hx
    have hkilled := seven_nsmul_of_kernelX hP hx
    have hdvd : (49 : ℕ) ∣ 7 := by
      rw [← hQ]
      exact addOrderOf_dvd_of_nsmul_eq_zero hkilled
    norm_num at hdvd
  have hx0 : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxb : x ≠ orderSevenB d :=
    fun h ↦ hx (Or.inr (Or.inl h))
  have hxc : x ≠ orderSevenC d :=
    fun h ↦ hx (Or.inr (Or.inr h))
  have horderImage :=
    addOrderOf_orderSevenPointMap_of_order_fortyNine hQ hkernel hmap
  have horderVelu :
      addOrderOf (orderSevenVeluPoint hP hx0 hxb hxc) = 7 := by
    rw [← orderSevenPointMap_some_of_not_kernelX hP hx]
    exact horderImage
  have hspec := orderSevenHauptmodulAt_spec
    (orderSevenQuotient d)
    ((orderSevenQuotient d).toAffine.equation_iff_nonsingular.mp
      (orderSevenVelu_equation hP.1 hx0 hxb hxc))
    (by simpa only [orderSevenVeluPoint] using horderVelu)
  simpa only [orderSevenResidualHauptmodul] using hspec

/-- A second nonbacktracking level-seven Hauptmodul for the quotient gives
a point on the level-`49` correspondence.  This packages the cancellation
of the nonzero quotient discriminant; constructing `B` and proving that it
differs from the Fricke/backtracking parameter remain separate tasks. -/
public theorem orderSevenG7F_eq_zero_of_quotient_hauptmodul
    {d B : ℚ} [(orderSevenFamily d).IsElliptic]
    (hoff : orderSevenFrickeParameter d ≠ B)
    (hB : orderSevenJNumerator B * (orderSevenQuotient d).Δ =
      (orderSevenQuotient d).c₄ ^ 3 * B ^ 7) :
    orderSevenG7F (orderSevenFrickeParameter d) B = 0 := by
  apply (orderSevenG7F_eq_zero_iff_crossMultiply hoff).mpr
  obtain ⟨hd0, hd1, -⟩ := orderSevenFamily_parameters_ne d
  have hs := orderSevenQuotient_hauptmodul_identity d hd0 hd1
  apply mul_left_cancel₀ (orderSevenQuotient d).isUnit_Δ.ne_zero
  calc
    (orderSevenQuotient d).Δ *
          (orderSevenJNumerator (orderSevenFrickeParameter d) * B ^ 7) =
        (orderSevenJNumerator (orderSevenFrickeParameter d) *
          (orderSevenQuotient d).Δ) * B ^ 7 := by ring
    _ = ((orderSevenQuotient d).c₄ ^ 3 *
          orderSevenFrickeParameter d ^ 7) * B ^ 7 := by rw [hs]
    _ = ((orderSevenQuotient d).c₄ ^ 3 * B ^ 7) *
          orderSevenFrickeParameter d ^ 7 := by ring
    _ = (orderSevenJNumerator B * (orderSevenQuotient d).Δ) *
          orderSevenFrickeParameter d ^ 7 := by rw [hB]
    _ = (orderSevenQuotient d).Δ *
          (orderSevenJNumerator B *
            orderSevenFrickeParameter d ^ 7) := by ring

/-- The explicit residual Hauptmodul attached to an affine order-`49`
point lies on the level-`49` correspondence whenever it is not the
Fricke/backtracking parameter. -/
public theorem orderSevenG7F_residual_eq_zero_of_order_fortyNine
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hmap : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) =
        (7 : ℕ) • orderSevenPointMap d
          (WeierstrassCurve.Affine.Point.some x y hP))
    (hoff : orderSevenFrickeParameter d ≠
      orderSevenResidualHauptmodul d x y) :
    orderSevenG7F (orderSevenFrickeParameter d)
        (orderSevenResidualHauptmodul d x y) = 0 := by
  apply orderSevenG7F_eq_zero_of_quotient_hauptmodul hoff
  exact (orderSevenResidualHauptmodul_spec_of_order_fortyNine
    hP hQ hkernel hmap).2

end MazurTorsion.Kubert
