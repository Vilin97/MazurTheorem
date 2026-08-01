/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval4
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

private lemma eval_20 (d : ℚ) : EvalCertificate d 20 := by
  solve_orderSeven_doubling_eval

private lemma eval_21 (d : ℚ) : EvalCertificate d 21 := by
  solve_orderSeven_doubling_eval

private lemma eval_22 (d : ℚ) : EvalCertificate d 22 := by
  solve_orderSeven_doubling_eval

private lemma eval_23 (d : ℚ) : EvalCertificate d 23 := by
  solve_orderSeven_doubling_eval

theorem evalBlock5 (d : ℚ) (i : Fin 4) :
    EvalCertificate d ((i : ℚ) + 20) := by
  fin_cases i
  · (convert eval_20 d using 1; norm_num)
  · (convert eval_21 d using 1; norm_num)
  · (convert eval_22 d using 1; norm_num)
  · (convert eval_23 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal
