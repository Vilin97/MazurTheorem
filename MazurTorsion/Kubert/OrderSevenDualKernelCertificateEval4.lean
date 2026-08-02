/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenDualKernelCertificateEval3
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

private lemma eval_20 (d : ℚ) : EvalCertificate d 20 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_21 (d : ℚ) : EvalCertificate d 21 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_22 (d : ℚ) : EvalCertificate d 22 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_23 (d : ℚ) : EvalCertificate d 23 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_24 (d : ℚ) : EvalCertificate d 24 := by
  solve_orderSeven_dualKernel_eval

theorem evalBlock4 (d : ℚ) (i : Fin 5) :
    EvalCertificate d ((i : ℚ) + 20) := by
  fin_cases i
  · (convert eval_20 d using 1; norm_num)
  · (convert eval_21 d using 1; norm_num)
  · (convert eval_22 d using 1; norm_num)
  · (convert eval_23 d using 1; norm_num)
  · (convert eval_24 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDualKernelCertificate.Internal
