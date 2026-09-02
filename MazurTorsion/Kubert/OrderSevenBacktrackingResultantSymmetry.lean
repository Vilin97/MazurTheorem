/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificate
import MazurTorsion.Kubert.OrderSevenBacktrackingSymmetry

/-!
# The order-three orbit of the order-seven resultant

The generic pseudo-remainder certificate computes the bounded resultant
against the first division cofactor. The order-three parameter symmetry
transports coprimality twice around its orbit, producing the other two
bounded resultants required by the stable obstruction consumer.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

open MazurTorsion.PolynomialResultant
open Internal.ResultantCertificate

/-- The seven checked recurrences make all three bounded resultants nonzero at
every nonsingular order-seven Kubert parameter. -/
theorem bounded_resultants_ne_zero
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hcubic : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0 ∧
      resultant (selectionCofactor d) (divisionCofactor1 d) 33 7 ≠ 0 ∧
      resultant (selectionCofactor d) (divisionCofactor2 d) 33 7 ≠ 0 := by
  let t := orderThreeParameter d
  let t2 := orderThreeParameter t
  have ht0 : t ≠ 0 := orderThreeParameter_ne_zero d hd1
  have ht1 : t ≠ 1 := orderThreeParameter_ne_one d hd0
  have htcubic : t ^ 3 - 8 * t ^ 2 + 5 * t + 1 ≠ 0 := by
    rw [show t = orderThreeParameter d by rfl,
      discriminantFactor_orderThreeParameter d hd1]
    exact mul_ne_zero
      (pow_ne_zero 3 (inv_ne_zero (sub_ne_zero.mpr hd1)))
      hcubic
  have ht20 : t2 ≠ 0 := orderThreeParameter_ne_zero t ht1
  have ht21 : t2 ≠ 1 := orderThreeParameter_ne_one t ht0
  have ht2cubic : t2 ^ 3 - 8 * t2 ^ 2 + 5 * t2 + 1 ≠ 0 := by
    rw [show t2 = orderThreeParameter t by rfl,
      discriminantFactor_orderThreeParameter t ht1]
    exact mul_ne_zero
      (pow_ne_zero 3 (inv_ne_zero (sub_ne_zero.mpr ht1)))
      htcubic
  have hres0 :
      resultant (selectionCofactor d) (divisionCofactor0 d) 33 7 ≠ 0 :=
    selection_divisionCofactor0_resultant_ne_zero
      d hd0 hd1 hcubic
  have hres0t :
      resultant (selectionCofactor t) (divisionCofactor0 t) 33 7 ≠ 0 :=
    selection_divisionCofactor0_resultant_ne_zero
      t ht0 ht1 htcubic
  have hcop0t : IsCoprime
      (selectionCofactor t) (divisionCofactor0 t) :=
    isCoprime_of_bounded_resultant_ne_zero
      (selectionCofactor_degree t) (divisionCofactor0_natDegree t)
      (divisionCofactor0_monic t) hres0t
  have hcop1 : IsCoprime
      (selectionCofactor d) (divisionCofactor1 d) :=
    isCoprime_selection_divisionCofactor1_of_orderThreeParameter
      d hd1 hcop0t
  have hres1 :
      resultant (selectionCofactor d) (divisionCofactor1 d) 33 7 ≠ 0 :=
    bounded_resultant_ne_zero_of_isCoprime
      (selectionCofactor_degree d) (divisionCofactor1_natDegree d)
      (divisionCofactor1_monic d) hcop1
  have hres0t2 :
      resultant (selectionCofactor t2) (divisionCofactor0 t2) 33 7 ≠ 0 :=
    selection_divisionCofactor0_resultant_ne_zero
      t2 ht20 ht21 ht2cubic
  have hcop0t2 : IsCoprime
      (selectionCofactor t2) (divisionCofactor0 t2) :=
    isCoprime_of_bounded_resultant_ne_zero
      (selectionCofactor_degree t2) (divisionCofactor0_natDegree t2)
      (divisionCofactor0_monic t2) hres0t2
  have hcop1t : IsCoprime
      (selectionCofactor t) (divisionCofactor1 t) :=
    isCoprime_selection_divisionCofactor1_of_orderThreeParameter
      t ht1 hcop0t2
  have hcop2 : IsCoprime
      (selectionCofactor d) (divisionCofactor2 d) :=
    isCoprime_selection_divisionCofactor2_of_orderThreeParameter
      d hd1 hcop1t
  have hres2 :
      resultant (selectionCofactor d) (divisionCofactor2 d) 33 7 ≠ 0 :=
    bounded_resultant_ne_zero_of_isCoprime
      (selectionCofactor_degree d) (divisionCofactor2_natDegree d)
      (divisionCofactor2_monic d) hcop2
  exact ⟨hres0, hres1, hres2⟩

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
