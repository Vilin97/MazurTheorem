/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval5
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

private lemma eval_24 (d : ℚ) : EvalCertificate d 24 := by
  solve_orderSeven_doubling_eval

private lemma eval_25 (d : ℚ) : EvalCertificate d 25 := by
  solve_orderSeven_doubling_eval

private lemma eval_26 (d : ℚ) : EvalCertificate d 26 := by
  solve_orderSeven_doubling_eval

private lemma eval_27 (d : ℚ) : EvalCertificate d 27 := by
  solve_orderSeven_doubling_eval

theorem evalBlock6 (d : ℚ) (i : Fin 4) :
    EvalCertificate d ((i : ℚ) + 24) := by
  fin_cases i
  · (convert eval_24 d using 1; norm_num)
  · (convert eval_25 d using 1; norm_num)
  · (convert eval_26 d using 1; norm_num)
  · (convert eval_27 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal
