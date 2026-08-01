/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenDualKernelCertificateData
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

private lemma eval_0 (d : ℚ) : EvalCertificate d 0 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_1 (d : ℚ) : EvalCertificate d 1 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_2 (d : ℚ) : EvalCertificate d 2 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_3 (d : ℚ) : EvalCertificate d 3 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_4 (d : ℚ) : EvalCertificate d 4 := by
  solve_orderSeven_dualKernel_eval

theorem evalBlock0 (d : ℚ) (i : Fin 5) :
    EvalCertificate d ((i : ℚ) + 0) := by
  fin_cases i
  · (convert eval_0 d using 1; norm_num)
  · (convert eval_1 d using 1; norm_num)
  · (convert eval_2 d using 1; norm_num)
  · (convert eval_3 d using 1; norm_num)
  · (convert eval_4 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDualKernelCertificate.Internal
