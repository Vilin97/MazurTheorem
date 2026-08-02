/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval0
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

private lemma eval_4 (d : ℚ) : EvalCertificate d 4 := by
  solve_orderSeven_doubling_eval

private lemma eval_5 (d : ℚ) : EvalCertificate d 5 := by
  solve_orderSeven_doubling_eval

private lemma eval_6 (d : ℚ) : EvalCertificate d 6 := by
  solve_orderSeven_doubling_eval

private lemma eval_7 (d : ℚ) : EvalCertificate d 7 := by
  solve_orderSeven_doubling_eval

theorem evalBlock1 (d : ℚ) (i : Fin 4) :
    EvalCertificate d ((i : ℚ) + 4) := by
  fin_cases i
  · (convert eval_4 d using 1; norm_num)
  · (convert eval_5 d using 1; norm_num)
  · (convert eval_6 d using 1; norm_num)
  · (convert eval_7 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal
