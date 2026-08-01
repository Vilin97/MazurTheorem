/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.DivisionPolynomialRootCriterion
import MazurTorsion.Kubert.OrderSevenBacktrackingSelection
import MazurTorsion.Kubert.OrderSevenIsogenyDoubling

/-!
# The geometric order-seven backtracking obstruction

This file isolates the lightweight geometric part of the backtracking
argument from the large factor and resultant certificates.  It turns a
non-simultaneous-vanishing statement for the two relevant polynomials into
the missing nonbacktracking hypothesis in the order-seven isogeny tower.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The image on the quotient curve of an order-`49` point satisfying the
kernel condition is a root of the quotient seventh division polynomial. -/
theorem orderSevenQuotient_preΨ_seven_eval_eq_zero_of_order_fortyNine_of_kernel
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0) :
    ((orderSevenQuotient d).preΨ' 7).eval (orderSevenVeluX d x) = 0 := by
  have hx : ¬OrderSevenKernelX d x :=
    not_orderSevenKernelX_of_order_fortyNine hP hQ
  have hx₀ : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxB : x ≠ orderSevenB d :=
    fun h ↦ hx (Or.inr (Or.inl h))
  have hxC : x ≠ orderSevenC d :=
    fun h ↦ hx (Or.inr (Or.inr h))
  let hV : (orderSevenQuotient d).toAffine.Nonsingular
      (orderSevenVeluX d x) (orderSevenVeluY d x y) :=
    (orderSevenQuotient d).toAffine.equation_iff_nonsingular.mp
      (orderSevenVelu_equation hP.1 hx₀ hxB hxC)
  let V : (orderSevenQuotient d).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some
      (orderSevenVeluX d x) (orderSevenVeluY d x y) hV
  have hmapV : orderSevenPointMap d
      (WeierstrassCurve.Affine.Point.some x y hP) = V := by
    rw [orderSevenPointMap_some_of_not_kernelX hP hx]
    simp only [V, orderSevenVeluPoint]
  have horderV : addOrderOf V = 7 := by
    rw [← hmapV]
    exact addOrderOf_orderSevenPointMap_of_order_fortyNine_of_kernel
      hQ hkernel
  have hsevenV : (7 : ℕ) • V = 0 := by
    rw [← horderV]
    exact addOrderOf_nsmul_eq_zero V
  exact _root_.MazurTorsion.DivisionPolynomialRootCriterion.hasDivisionPolynomialRootCriterion_seven
    (orderSevenQuotient d) hV hsevenV

/-- If the backtracking selection polynomial and the quotient seventh
division polynomial cannot both vanish, the residual Hauptmodul is not the
Fricke parameter. -/
theorem orderSevenResidualHauptmodul_ne_fricke_of_obstruction
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hobstruction :
      orderSevenSelectionPolynomial d (orderSevenVeluX d x) ≠ 0 ∨
        ((orderSevenQuotient d).preΨ' 7).eval
          (orderSevenVeluX d x) ≠ 0) :
    orderSevenResidualHauptmodul d x y ≠ orderSevenFrickeParameter d := by
  intro hbacktracks
  have hselection :
      orderSevenSelectionPolynomial d (orderSevenVeluX d x) = 0 :=
    orderSevenSelectionPolynomial_eq_zero_of_residual_eq_fricke
      hP hQ hbacktracks
  have hdivision :
      ((orderSevenQuotient d).preΨ' 7).eval
        (orderSevenVeluX d x) = 0 :=
    orderSevenQuotient_preΨ_seven_eval_eq_zero_of_order_fortyNine_of_kernel
      hP hQ hkernel
  exact hobstruction.elim (· hselection) (· hdivision)

/-- A polynomial nonvanishing obstruction supplies the missing
nonbacktracking hypothesis in the existing order-seven isogeny-tower theorem. -/
theorem orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hobstruction :
      orderSevenSelectionPolynomial d (orderSevenVeluX d x) ≠ 0 ∨
        ((orderSevenQuotient d).preΨ' 7).eval
          (orderSevenVeluX d x) ≠ 0) :
    orderSevenG7F (orderSevenFrickeParameter d)
        (orderSevenResidualHauptmodul d x y) = 0 := by
  apply orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_kernel
    hP hQ hkernel
  exact (orderSevenResidualHauptmodul_ne_fricke_of_obstruction
    hP hQ hkernel hobstruction).symm

end MazurTorsion.Kubert
