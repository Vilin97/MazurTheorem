/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateData
import Mathlib.Tactic.FinCases
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

private lemma eval_0 (d : ℚ) : EvalCertificate d 0 := by
  solve_orderSeven_doubling_eval

private lemma eval_1 (d : ℚ) : EvalCertificate d 1 := by
  solve_orderSeven_doubling_eval

private lemma eval_2 (d : ℚ) : EvalCertificate d 2 := by
  solve_orderSeven_doubling_eval

private lemma eval_3 (d : ℚ) : EvalCertificate d 3 := by
  solve_orderSeven_doubling_eval

theorem evalBlock0 (d : ℚ) (i : Fin 4) :
    EvalCertificate d ((i : ℚ) + 0) := by
  fin_cases i
  · simpa using eval_0 d
  · simpa using eval_1 d
  · simpa using eval_2 d
  · simpa using eval_3 d

end MazurTorsion.Kubert.OrderSevenDoublingCertificate.Internal
