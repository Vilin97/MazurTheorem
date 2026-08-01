/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenDualKernelCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Pulling the order-seven dual kernel back through Vélu's map

The polynomial certificate identifies the cleared pullback of the
dual-kernel cubic with the source seventh division polynomial.  Consequently,
the three marked kernel abscissae exhaust the rational roots of the source
seventh division polynomial.  This is the dual-factor elimination used by
the order-`49` nonbacktracking argument.
-/

open Polynomial

namespace MazurTorsion.Kubert

open OrderSevenDualKernelCertificate
open OrderSevenIsogenyPolynomialData

private lemma orderSevenDualKernelHomogeneous_eval
    (d x : ℚ) (u v : ℚ[X]) :
    (dualKernelHomogeneousPolynomial d u v).eval x =
      7 * (u.eval x) ^ 3 +
        (14 * d ^ 4 - 35 * d ^ 3 + 42 * d ^ 2 - 21 * d + 14) *
          (u.eval x) ^ 2 * v.eval x +
        (7 * d ^ 8 - 7 * d ^ 7 - 98 * d ^ 6 + 224 * d ^ 5 -
          203 * d ^ 4 + 49 * d ^ 3 + 77 * d ^ 2 - 49 * d + 7) *
          u.eval x * (v.eval x) ^ 2 +
        (d ^ 12 + 3 * d ^ 11 - 51 * d ^ 10 + 185 * d ^ 9 -
          767 * d ^ 8 + 2097 * d ^ 7 - 2835 * d ^ 6 + 1738 * d ^ 5 -
          295 * d ^ 4 - 116 * d ^ 3 + 55 * d ^ 2 - 15 * d + 1) *
          (v.eval x) ^ 3 := by
  simp [dualKernelHomogeneousPolynomial]

/-- Away from the three kernel poles, pulling the dual-kernel cubic back
through the explicit Vélu abscissa gives the source seventh division
polynomial divided by the seventh power of the kernel denominator. -/
theorem orderSevenDualKernelPolynomial_veluX
    {d x : ℚ} (hx0 : x ≠ 0)
    (hxb : x ≠ orderSevenB d) (hxc : x ≠ orderSevenC d) :
    orderSevenDualKernelPolynomial d (orderSevenVeluX d x) =
      ((orderSevenFamily d).preΨ' 7).eval x /
        orderSevenKernelPolynomial d x ^ 7 := by
  have hkernel : orderSevenKernelPolynomial d x ≠ 0 := by
    simp only [orderSevenKernelPolynomial]
    exact mul_ne_zero (mul_ne_zero hx0 (sub_ne_zero.mpr hxb))
      (sub_ne_zero.mpr hxc)
  have heval := congrArg (Polynomial.eval x)
    (OrderSevenDualKernelCertificate.polynomial_identity d)
  simp only [pulledDualKernelPolynomial, Polynomial.eval_mul,
    orderSevenDualKernelHomogeneous_eval, Polynomial.eval_pow,
    OrderSevenIsogenyPolynomialData.kernelPolynomial_eval,
    OrderSevenIsogenyPolynomialData.veluXPolynomial_eval] at heval
  rw [orderSevenVeluX_eq_div hx0 hxb hxc]
  simp only [orderSevenDualKernelPolynomial]
  field_simp [hkernel]
  linear_combination heval

/-- Outside the marked kernel, a rational abscissa is not a root of the
source seventh division polynomial. -/
theorem orderSevenFamily_preΨ_seven_eval_ne_zero_of_not_kernelX
    {d x : ℚ} [(orderSevenFamily d).IsElliptic]
    (hx : ¬OrderSevenKernelX d x) :
    ((orderSevenFamily d).preΨ' 7).eval x ≠ 0 := by
  have hx0 : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxb : x ≠ orderSevenB d :=
    fun h ↦ hx (Or.inr (Or.inl h))
  have hxc : x ≠ orderSevenC d :=
    fun h ↦ hx (Or.inr (Or.inr h))
  intro hroot
  apply orderSevenDualKernelPolynomial_ne_zero d (orderSevenVeluX d x)
  rw [orderSevenDualKernelPolynomial_veluX hx0 hxb hxc, hroot]
  simp

/-- Every rational root of the source seventh division polynomial is one of
the three marked kernel abscissae. -/
theorem orderSevenFamily_kernelX_of_preΨ_seven_eval_eq_zero
    {d x : ℚ} [(orderSevenFamily d).IsElliptic]
    (hroot : ((orderSevenFamily d).preΨ' 7).eval x = 0) :
    OrderSevenKernelX d x := by
  by_contra hx
  exact orderSevenFamily_preΨ_seven_eval_ne_zero_of_not_kernelX hx hroot

end MazurTorsion.Kubert
