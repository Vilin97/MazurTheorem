/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenIsogeny
public import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The dual-kernel cubic for the order-seven isogeny

The cubic below is characterized in `OrderSevenDualKernelPullback`: after
substitution of the explicit Vélu abscissa and clearing its kernel
denominator, it becomes the source seventh division polynomial.  This is the
pullback identity for the kernel of the dual isogeny.  The present file
records the cubic and proves that it has no rational root on a nonsingular
member of the source family.

The proof makes the fixed real-cyclotomic cubic
`z³ + z² - 2z - 1` appear by an explicit rational change of primitive
element.  That cubic has no rational root by the rational-root theorem.
-/
@[expose] public section
namespace MazurTorsion.Kubert

private noncomputable def sevenCyclotomicCubic : Polynomial ℤ :=
  Polynomial.X ^ 3 + Polynomial.X ^ 2 -
    Polynomial.C 2 * Polynomial.X - Polynomial.C 1

private lemma sevenCyclotomicCubic_monic :
    Polynomial.Monic sevenCyclotomicCubic := by
  unfold sevenCyclotomicCubic
  monicity!

private lemma sevenCyclotomicCubic_ne_zero (z : ℚ) :
    z ^ 3 + z ^ 2 - 2 * z - 1 ≠ 0 := by
  intro hz
  have hroot : Polynomial.aeval z sevenCyclotomicCubic = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [sevenCyclotomicCubic]
    linear_combination hz
  obtain ⟨m, hzm, hdiv⟩ :=
    exists_integer_of_is_root_of_monic sevenCyclotomicCubic_monic hroot
  have hunit : IsUnit m := by
    rw [isUnit_iff_dvd_one]
    simpa [sevenCyclotomicCubic] using hdiv
  rcases Int.isUnit_iff.mp hunit with rfl | rfl
  · norm_num [hzm] at hz
  · norm_num [hzm] at hz

/-- The cubic whose geometric roots are the three nonzero abscissae of the
dual kernel of the explicit order-seven isogeny. -/
def orderSevenDualKernelPolynomial (d x : ℚ) : ℚ :=
  7 * x ^ 3 +
    (14 * d ^ 4 - 35 * d ^ 3 + 42 * d ^ 2 - 21 * d + 14) * x ^ 2 +
    (7 * d ^ 8 - 7 * d ^ 7 - 98 * d ^ 6 + 224 * d ^ 5 - 203 * d ^ 4 +
      49 * d ^ 3 + 77 * d ^ 2 - 49 * d + 7) * x +
    (d ^ 12 + 3 * d ^ 11 - 51 * d ^ 10 + 185 * d ^ 9 - 767 * d ^ 8 +
      2097 * d ^ 7 - 2835 * d ^ 6 + 1738 * d ^ 5 - 295 * d ^ 4 -
      116 * d ^ 3 + 55 * d ^ 2 - 15 * d + 1)

private def orderSevenDualKernelDiscriminantFactor (d : ℚ) : ℚ :=
  d ^ 3 - 8 * d ^ 2 + 5 * d + 1

private def orderSevenDualKernelCyclotomicNumerator (d x : ℚ) : ℚ :=
  9 * d ^ 9 - 13 * d ^ 8 - 230 * d ^ 7 + 742 * d ^ 6 - 966 * d ^ 5 +
    525 * d ^ 4 + 14 * d ^ 3 - 80 * d ^ 2 + 9 * d - 5 +
    7 * (5 * d ^ 5 - 20 * d ^ 4 + 25 * d ^ 3 - 7 * d ^ 2 + 2 * d - 2) * x +
    7 * (3 * d - 1) * x ^ 2

private def orderSevenDualKernelCyclotomicParameter (d x : ℚ) : ℚ :=
  orderSevenDualKernelCyclotomicNumerator d x /
    orderSevenDualKernelDiscriminantFactor d ^ 3

private def orderSevenDualKernelCyclotomicCofactor (d x : ℚ) : ℚ :=
  49 * (3 * d - 1) ^ 3 * x ^ 3 +
    49 * (3 * d - 1) ^ 2 *
      (9 * d ^ 5 - 43 * d ^ 4 + 52 * d ^ 3 - 6 * d ^ 2 - 3 * d - 4) * x ^ 2 +
    49 * (3 * d - 1) *
      (24 * d ^ 10 - 205 * d ^ 9 + 621 * d ^ 8 - 835 * d ^ 7 +
        206 * d ^ 6 + 463 * d ^ 5 - 185 * d ^ 4 - 128 * d ^ 3 +
        34 * d ^ 2 + 7 * d + 5) * x +
    7 * (113 * d ^ 15 - 964 * d ^ 14 + 959 * d ^ 13 + 12621 * d ^ 12 -
      49413 * d ^ 11 + 81116 * d ^ 10 - 68761 * d ^ 9 + 19534 * d ^ 8 +
      16885 * d ^ 7 - 12397 * d ^ 6 - 2716 * d ^ 5 + 2954 * d ^ 4 +
      385 * d ^ 3 - 266 * d ^ 2 - 24 * d - 13)

private theorem orderSevenDualKernelCyclotomic_identity (d x : ℚ) :
    orderSevenDualKernelCyclotomicNumerator d x ^ 3 +
        orderSevenDualKernelCyclotomicNumerator d x ^ 2 *
          orderSevenDualKernelDiscriminantFactor d ^ 3 -
        2 * orderSevenDualKernelCyclotomicNumerator d x *
          orderSevenDualKernelDiscriminantFactor d ^ 6 -
        orderSevenDualKernelDiscriminantFactor d ^ 9 =
      orderSevenDualKernelPolynomial d x *
        orderSevenDualKernelCyclotomicCofactor d x := by
  simp only [orderSevenDualKernelCyclotomicNumerator,
    orderSevenDualKernelDiscriminantFactor, orderSevenDualKernelPolynomial,
    orderSevenDualKernelCyclotomicCofactor]
  ring

private theorem orderSevenDualKernelCyclotomicParameter_isRoot
    {d x : ℚ} (hK : orderSevenDualKernelDiscriminantFactor d ≠ 0)
    (hdual : orderSevenDualKernelPolynomial d x = 0) :
    orderSevenDualKernelCyclotomicParameter d x ^ 3 +
        orderSevenDualKernelCyclotomicParameter d x ^ 2 -
        2 * orderSevenDualKernelCyclotomicParameter d x - 1 = 0 := by
  simp only [orderSevenDualKernelCyclotomicParameter]
  field_simp [hK]
  linear_combination
    orderSevenDualKernelCyclotomic_identity d x +
      orderSevenDualKernelCyclotomicCofactor d x * hdual

/-- On a nonsingular order-seven Tate curve, the dual-kernel cubic has no
rational root. -/
theorem orderSevenDualKernelPolynomial_ne_zero
    (d x : ℚ) [(orderSevenFamily d).IsElliptic] :
    orderSevenDualKernelPolynomial d x ≠ 0 := by
  intro hdual
  apply sevenCyclotomicCubic_ne_zero
    (orderSevenDualKernelCyclotomicParameter d x)
  exact orderSevenDualKernelCyclotomicParameter_isRoot
    (orderSevenFamily_parameters_ne d).2.2 hdual

end MazurTorsion.Kubert
