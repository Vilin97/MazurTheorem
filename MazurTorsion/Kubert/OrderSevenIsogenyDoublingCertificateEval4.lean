/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval3
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

private lemma eval_16 (d : ℚ) : EvalCertificate d 16 := by
  solve_orderSeven_doubling_eval

private lemma eval_17 (d : ℚ) : EvalCertificate d 17 := by
  solve_orderSeven_doubling_eval

private lemma eval_18 (d : ℚ) : EvalCertificate d 18 := by
  solve_orderSeven_doubling_eval

private lemma eval_19 (d : ℚ) : EvalCertificate d 19 := by
  solve_orderSeven_doubling_eval

theorem evalBlock4 (d : ℚ) (i : Fin 4) :
    EvalCertificate d ((i : ℚ) + 16) := by
  fin_cases i
  · (convert eval_16 d using 1; norm_num)
  · (convert eval_17 d using 1; norm_num)
  · (convert eval_18 d using 1; norm_num)
  · (convert eval_19 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal
