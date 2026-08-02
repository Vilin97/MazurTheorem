/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal

local macro "solve_orderSeven_doubling_eval" : tactic =>
    `(tactic|
      (simp [EvalCertificate, veluXHomogeneousPolynomial,
        sourceDoubleXPolynomial, sourceCompletedCubicPolynomial,
        doubleXHomogeneousPolynomial, veluXPolynomial, kernelPolynomial,
        orderSevenVeluXNumerator, orderSevenKernelPolynomial,
        orderSevenFamily, orderSevenQuotient, orderSevenB, orderSevenC,
        tateNormalCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;>
       ring))

private lemma eval_12 (d : ℚ) : EvalCertificate d 12 := by
  solve_orderSeven_doubling_eval

private lemma eval_13 (d : ℚ) : EvalCertificate d 13 := by
  solve_orderSeven_doubling_eval

private lemma eval_14 (d : ℚ) : EvalCertificate d 14 := by
  solve_orderSeven_doubling_eval

private lemma eval_15 (d : ℚ) : EvalCertificate d 15 := by
  solve_orderSeven_doubling_eval

theorem evalBlock3 (d : ℚ) (i : Fin 4) :
    EvalCertificate d ((i : ℚ) + 12) := by
  fin_cases i
  · (convert eval_12 d using 1; norm_num)
  · (convert eval_13 d using 1; norm_num)
  · (convert eval_14 d using 1; norm_num)
  · (convert eval_15 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal
