/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenDualKernelCertificateEval1
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

private lemma eval_10 (d : ℚ) : EvalCertificate d 10 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_11 (d : ℚ) : EvalCertificate d 11 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_12 (d : ℚ) : EvalCertificate d 12 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_13 (d : ℚ) : EvalCertificate d 13 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_14 (d : ℚ) : EvalCertificate d 14 := by
  solve_orderSeven_dualKernel_eval

theorem evalBlock2 (d : ℚ) (i : Fin 5) :
    EvalCertificate d ((i : ℚ) + 10) := by
  fin_cases i
  · (convert eval_10 d using 1; norm_num)
  · (convert eval_11 d using 1; norm_num)
  · (convert eval_12 d using 1; norm_num)
  · (convert eval_13 d using 1; norm_num)
  · (convert eval_14 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDualKernelCertificate.Internal
