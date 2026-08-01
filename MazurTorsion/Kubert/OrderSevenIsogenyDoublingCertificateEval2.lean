/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval1
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal

local macro "solve_orderSeven_doubling_eval" : tactic =>
    `(tactic|
      (simp [EvalCertificate, veluXHomogeneousPolynomial,
        sourceDoubleXPolynomial, sourceCompletedCubicPolynomial,
        doubleXHomogeneousPolynomial, veluXPolynomial, kernelPolynomial,
        orderSevenFamily, orderSevenQuotient, orderSevenB, orderSevenC,
        tateNormalCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈] <;>
       ring))

private lemma eval_8 (d : ℚ) : EvalCertificate d 8 := by
  solve_orderSeven_doubling_eval

private lemma eval_9 (d : ℚ) : EvalCertificate d 9 := by
  solve_orderSeven_doubling_eval

private lemma eval_10 (d : ℚ) : EvalCertificate d 10 := by
  solve_orderSeven_doubling_eval

private lemma eval_11 (d : ℚ) : EvalCertificate d 11 := by
  solve_orderSeven_doubling_eval

theorem evalBlock2 (d : ℚ) (i : Fin 4) :
    EvalCertificate d ((i : ℚ) + 8) := by
  fin_cases i
  · (convert eval_8 d using 1; norm_num)
  · (convert eval_9 d using 1; norm_num)
  · (convert eval_10 d using 1; norm_num)
  · (convert eval_11 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal
