/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenDualKernelCertificateEval0
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MazurTorsion.Kubert.OrderSevenDualKernelCertificate.Internal

local macro "solve_orderSeven_dualKernel_eval" : tactic =>
    `(tactic|
      (unfold EvalCertificate
       rw [source_prePsiSeven]
       simp [pulledDualKernelPolynomial, dualKernelHomogeneousPolynomial,
        OrderSevenIsogenyPolynomialData.veluXPolynomial,
        OrderSevenIsogenyPolynomialData.kernelPolynomial,
        orderSevenFamily, orderSevenB, orderSevenC, tateNormalCurve,
        WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
        WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈] <;>
       ring))

private lemma eval_5 (d : ℚ) : EvalCertificate d 5 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_6 (d : ℚ) : EvalCertificate d 6 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_7 (d : ℚ) : EvalCertificate d 7 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_8 (d : ℚ) : EvalCertificate d 8 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_9 (d : ℚ) : EvalCertificate d 9 := by
  solve_orderSeven_dualKernel_eval

theorem evalBlock1 (d : ℚ) (i : Fin 5) :
    EvalCertificate d ((i : ℚ) + 5) := by
  fin_cases i
  · (convert eval_5 d using 1; norm_num)
  · (convert eval_6 d using 1; norm_num)
  · (convert eval_7 d using 1; norm_num)
  · (convert eval_8 d using 1; norm_num)
  · (convert eval_9 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDualKernelCertificate.Internal
