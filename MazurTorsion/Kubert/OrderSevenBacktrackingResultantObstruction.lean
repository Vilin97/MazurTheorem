/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.Polynomial.BoundedResultant
import MazurTorsion.Kubert.OrderSevenBacktrackingFactorCertificate
import MazurTorsion.Kubert.OrderSevenBacktrackingObstruction
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantSymmetry
import Mathlib.Tactic.NormNum

/-!
# Resultant obstruction for order-seven backtracking

This file is the stable consumer boundary between the generated resultant
certificates and the geometric backtracking argument.  Three nonzero bounded
resultants first rule out a common root of the selection cofactor and any of
the three quotient cofactors.  The factor certificates and the rational
nonvanishing of the dual-kernel cubic then lift this to the two geometric
polynomials.

Keeping this bridge separate from `OrderSevenBacktrackingObstruction` prevents
the lightweight geometric theorem from importing the memory-heavy factor
certificate chain.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open MazurTorsion.PolynomialResultant
open Internal.ResultantCertificate

/-- Nonzero bounded resultants against all three quotient cofactors rule out
their simultaneous vanishing with the selection cofactor at every rational
abscissa. -/
theorem cofactor_eval_obstruction_of_bounded_resultants
    (d : ℚ)
    (hres0 : resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (selectionCofactor d) (divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (selectionCofactor d) (divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    (selectionCofactor d).eval z ≠ 0 ∨
      (divisionCofactor0 d * divisionCofactor1 d *
        divisionCofactor2 d).eval z ≠ 0 := by
  by_cases hselection : (selectionCofactor d).eval z = 0
  · right
    simp only [eval_mul]
    have h0 : (divisionCofactor0 d).eval z ≠ 0 :=
      (eval_ne_zero_or_eval_ne_zero_of_bounded_resultant_ne_zero
          (selectionCofactor_degree d) (divisionCofactor0_natDegree d)
          (divisionCofactor0_monic d) hres0 z).resolve_left
            (fun hne ↦ hne hselection)
    have h1 : (divisionCofactor1 d).eval z ≠ 0 :=
      (eval_ne_zero_or_eval_ne_zero_of_bounded_resultant_ne_zero
          (selectionCofactor_degree d) (divisionCofactor1_natDegree d)
          (divisionCofactor1_monic d) hres1 z).resolve_left
            (fun hne ↦ hne hselection)
    have h2 : (divisionCofactor2 d).eval z ≠ 0 :=
      (eval_ne_zero_or_eval_ne_zero_of_bounded_resultant_ne_zero
          (selectionCofactor_degree d) (divisionCofactor2_natDegree d)
          (divisionCofactor2_monic d) hres2 z).resolve_left
            (fun hne ↦ hne hselection)
    exact mul_ne_zero (mul_ne_zero h0 h1) h2
  · exact Or.inl hselection

/-- The checked first and final pseudo-remainder recurrences and the five
remaining recurrence hypotheses discharge all three bounded-resultant
hypotheses in the stable cofactor obstruction. -/
theorem cofactor_eval_obstruction_of_resultant_recurrences
    (hrec1 : recurrence1) (hrec2 : recurrence2)
    (hrec3 : recurrence3)
    (hrec4 : recurrence4) (hrec5 : recurrence5)
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0)
    (z : ℚ) :
    (selectionCofactor d).eval z ≠ 0 ∨
      (divisionCofactor0 d * divisionCofactor1 d *
        divisionCofactor2 d).eval z ≠ 0 := by
  obtain ⟨hres0, hres1, hres2⟩ := bounded_resultants_ne_zero
    hrec1 hrec2 hrec3 hrec4 hrec5
    d hd0 hd1 hcubic
  exact cofactor_eval_obstruction_of_bounded_resultants
    d hres0 hres1 hres2 z

/-- Nonzero bounded resultants lift through the certified factorizations to
show that the backtracking selection polynomial and quotient seventh division
polynomial cannot both vanish at a rational abscissa. -/
theorem polynomial_eval_obstruction_of_bounded_resultants
    (d : ℚ) [(orderSevenFamily d).IsElliptic]
    (hres0 : resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (selectionCofactor d) (divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (selectionCofactor d) (divisionCofactor2 d) 33 7 ≠ 0)
    (z : ℚ) :
    orderSevenSelectionPolynomial d z ≠ 0 ∨
      ((orderSevenQuotient d).preΨ' 7).eval z ≠ 0 := by
  have hdual : orderSevenDualKernelPolynomial d z ≠ 0 :=
    orderSevenDualKernelPolynomial_ne_zero d z
  rcases cofactor_eval_obstruction_of_bounded_resultants
      d hres0 hres1 hres2 z with hselection | hdivision
  · left
    rw [orderSevenSelectionPolynomial_eval_factorization]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hdual) hselection
  · right
    rw [orderSevenQuotient_preΨ_seven_eval_factorization]
    exact mul_ne_zero hdual hdivision

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

namespace MazurTorsion.Kubert

open OrderSevenBacktrackingCertificate

/-- Three nonzero bounded resultants certify that the residual Hauptmodul of
an order-`49` point satisfying the kernel condition is not the Fricke
parameter. -/
theorem orderSevenResidualHauptmodul_ne_fricke_of_bounded_resultants
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hres0 : resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (selectionCofactor d) (divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (selectionCofactor d) (divisionCofactor2 d) 33 7 ≠ 0) :
    orderSevenResidualHauptmodul d x y ≠ orderSevenFrickeParameter d := by
  apply orderSevenResidualHauptmodul_ne_fricke_of_obstruction hP hQ hkernel
  exact polynomial_eval_obstruction_of_bounded_resultants
    d hres0 hres1 hres2 (orderSevenVeluX d x)

/-- Three nonzero bounded resultants discharge the nonbacktracking hypothesis
in the order-seven isogeny-tower equation for an order-`49` point. -/
theorem orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_bounded_resultants
    {d x y : ℚ} [(orderSevenFamily d).IsElliptic]
    (hP : (orderSevenFamily d).toAffine.Nonsingular x y)
    (hQ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderSevenFamily d).toAffine.Point) = 49)
    (hkernel : orderSevenPointMap d
      ((7 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP) = 0)
    (hres0 : resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0)
    (hres1 : resultant (selectionCofactor d) (divisionCofactor1 d) 33 7 ≠ 0)
    (hres2 : resultant (selectionCofactor d) (divisionCofactor2 d) 33 7 ≠ 0) :
    orderSevenG7F (orderSevenFrickeParameter d)
        (orderSevenResidualHauptmodul d x y) = 0 := by
  apply orderSevenG7F_residual_eq_zero_of_order_fortyNine_of_obstruction
    hP hQ hkernel
  exact polynomial_eval_obstruction_of_bounded_resultants
    d hres0 hres1 hres2 (orderSevenVeluX d x)

end MazurTorsion.Kubert
