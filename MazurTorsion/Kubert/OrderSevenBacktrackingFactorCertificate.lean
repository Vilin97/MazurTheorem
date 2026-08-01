/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingSelectionCertificateEval7
import MazurTorsion.Kubert.OrderSevenBacktrackingDivisionCertificateEval4
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Factor certificates for order-seven backtracking

The selection identity has degree at most `36` in the abscissa and is checked
at `37` rational values.  The quotient seventh division-polynomial identity
has degree at most `24` and is checked at `25` rational values.  Their
pointwise consequences expose only the canonical cofactors needed by the
backtracking obstruction.

Both evaluation families are serial import chains so an ordinary build does
not check several memory-heavy interpolation shards concurrently.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

private theorem selection_eval_fin (d : ℚ) (i : Fin 37) :
    Internal.SelectionEvalCertificate d (i : ℚ) := by
  fin_cases i
  · simpa using Internal.selectionEvalAt0 d
  · simpa using Internal.selectionEvalAt1 d
  · simpa using Internal.selectionEvalAt2 d
  · simpa using Internal.selectionEvalAt3 d
  · simpa using Internal.selectionEvalAt4 d
  · simpa using Internal.selectionEvalAt5 d
  · simpa using Internal.selectionEvalAt6 d
  · simpa using Internal.selectionEvalAt7 d
  · simpa using Internal.selectionEvalAt8 d
  · simpa using Internal.selectionEvalAt9 d
  · simpa using Internal.selectionEvalAt10 d
  · simpa using Internal.selectionEvalAt11 d
  · simpa using Internal.selectionEvalAt12 d
  · simpa using Internal.selectionEvalAt13 d
  · simpa using Internal.selectionEvalAt14 d
  · simpa using Internal.selectionEvalAt15 d
  · simpa using Internal.selectionEvalAt16 d
  · simpa using Internal.selectionEvalAt17 d
  · simpa using Internal.selectionEvalAt18 d
  · simpa using Internal.selectionEvalAt19 d
  · simpa using Internal.selectionEvalAt20 d
  · simpa using Internal.selectionEvalAt21 d
  · simpa using Internal.selectionEvalAt22 d
  · simpa using Internal.selectionEvalAt23 d
  · simpa using Internal.selectionEvalAt24 d
  · simpa using Internal.selectionEvalAt25 d
  · simpa using Internal.selectionEvalAt26 d
  · simpa using Internal.selectionEvalAt27 d
  · simpa using Internal.selectionEvalAt28 d
  · simpa using Internal.selectionEvalAt29 d
  · simpa using Internal.selectionEvalAt30 d
  · simpa using Internal.selectionEvalAt31 d
  · simpa using Internal.selectionEvalAt32 d
  · simpa using Internal.selectionEvalAt33 d
  · simpa using Internal.selectionEvalAt34 d
  · simpa using Internal.selectionEvalAt35 d
  · simpa using Internal.selectionEvalAt36 d

private lemma dualKernelPolynomial_degree (d : ℚ) :
    (Internal.dualKernelPolynomial d).natDegree ≤ 3 := by
  unfold Internal.dualKernelPolynomial
  compute_degree

private lemma selection_factor_product_degree (d : ℚ) :
    (C (64 ^ 3 : ℚ) * Internal.dualKernelPolynomial d *
      selectionCofactor d).natDegree ≤ 36 := by
  have h0 : (C (64 ^ 3 : ℚ) *
      Internal.dualKernelPolynomial d).natDegree ≤ 3 :=
    le_trans natDegree_mul_le
      (Nat.add_le_add (by compute_degree) (dualKernelPolynomial_degree d))
  exact le_trans natDegree_mul_le
    (Nat.add_le_add h0 (selectionCofactor_degree d))

private theorem selection_polynomial_factorization (d : ℚ) :
    Internal.selectionPolynomialData d =
      C (64 ^ 3 : ℚ) * Internal.dualKernelPolynomial d *
        selectionCofactor d := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ (f := fun i : Fin 37 ↦ (i : ℚ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  · intro i
    simpa [Internal.SelectionEvalCertificate] using selection_eval_fin d i
  · simp only [Fintype.card_fin]
    have hl := Internal.selectionPolynomialData_degree d
    have hr := selection_factor_product_degree d
    omega

/-- Pointwise factorization of the backtracking selection polynomial into the
dual-kernel cubic and its degree-33 cofactor. -/
theorem orderSevenSelectionPolynomial_eval_factorization (d x : ℚ) :
    orderSevenSelectionPolynomial d x =
      64 ^ 3 * orderSevenDualKernelPolynomial d x *
        (selectionCofactor d).eval x := by
  have h := congrArg (Polynomial.eval x)
    (selection_polynomial_factorization d)
  simpa [Internal.selectionPolynomialData_eval,
    Internal.dualKernelPolynomial_eval, mul_assoc] using h

private theorem division_eval_fin (d : ℚ) (i : Fin 25) :
    Internal.DivisionEvalCertificate d (i : ℚ) := by
  fin_cases i
  · (convert Internal.divisionEvalBlock0 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock0 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock0 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock0 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock0 d (4 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock1 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock1 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock1 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock1 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock1 d (4 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock2 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock2 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock2 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock2 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock2 d (4 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock3 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock3 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock3 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock3 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock3 d (4 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock4 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock4 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock4 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock4 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.divisionEvalBlock4 d (4 : Fin 5) using 1; norm_num)

private lemma quotient_prePsi_seven_degree (d : ℚ) :
    ((orderSevenQuotient d).preΨ' 7).natDegree ≤ 24 := by
  apply le_trans ((orderSevenQuotient d).natDegree_preΨ'_le 7)
  have hodd : ¬Even (7 : ℕ) := by decide
  simp [hodd]

private lemma division_factor_product_degree (d : ℚ) :
    (Internal.dualKernelPolynomial d * divisionCofactor0 d *
      divisionCofactor1 d * divisionCofactor2 d).natDegree ≤ 24 := by
  have h0 : (Internal.dualKernelPolynomial d *
      divisionCofactor0 d).natDegree ≤ 10 :=
    le_trans natDegree_mul_le
      (Nat.add_le_add (dualKernelPolynomial_degree d)
        (divisionCofactor0_degree d))
  have h1 : (Internal.dualKernelPolynomial d * divisionCofactor0 d *
      divisionCofactor1 d).natDegree ≤ 17 :=
    le_trans natDegree_mul_le
      (Nat.add_le_add h0 (divisionCofactor1_degree d))
  exact le_trans natDegree_mul_le
    (Nat.add_le_add h1 (divisionCofactor2_degree d))

private theorem quotient_prePsi_seven_polynomial_factorization (d : ℚ) :
    (orderSevenQuotient d).preΨ' 7 =
      Internal.dualKernelPolynomial d * divisionCofactor0 d *
        divisionCofactor1 d * divisionCofactor2 d := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ (f := fun i : Fin 25 ↦ (i : ℚ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  · intro i
    exact division_eval_fin d i
  · simp only [Fintype.card_fin]
    have hl := quotient_prePsi_seven_degree d
    have hr := division_factor_product_degree d
    omega

/-- Pointwise factorization of the quotient seventh division polynomial into
the dual-kernel cubic and the three canonical degree-seven cofactors. -/
theorem orderSevenQuotient_preΨ_seven_eval_factorization (d x : ℚ) :
    ((orderSevenQuotient d).preΨ' 7).eval x =
      orderSevenDualKernelPolynomial d x *
        (divisionCofactor0 d * divisionCofactor1 d *
          divisionCofactor2 d).eval x := by
  have h := congrArg (Polynomial.eval x)
    (quotient_prePsi_seven_polynomial_factorization d)
  simpa [Internal.dualKernelPolynomial_eval, mul_assoc] using h

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
