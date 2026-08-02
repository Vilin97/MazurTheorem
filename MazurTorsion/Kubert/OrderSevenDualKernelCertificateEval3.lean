/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenDualKernelCertificateEval2
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

private lemma eval_15 (d : ℚ) : EvalCertificate d 15 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_16 (d : ℚ) : EvalCertificate d 16 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_17 (d : ℚ) : EvalCertificate d 17 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_18 (d : ℚ) : EvalCertificate d 18 := by
  solve_orderSeven_dualKernel_eval

private lemma eval_19 (d : ℚ) : EvalCertificate d 19 := by
  solve_orderSeven_dualKernel_eval

theorem evalBlock3 (d : ℚ) (i : Fin 5) :
    EvalCertificate d ((i : ℚ) + 15) := by
  fin_cases i
  · (convert eval_15 d using 1; norm_num)
  · (convert eval_16 d using 1; norm_num)
  · (convert eval_17 d using 1; norm_num)
  · (convert eval_18 d using 1; norm_num)
  · (convert eval_19 d using 1; norm_num)

end MazurTorsion.Kubert.OrderSevenDualKernelCertificate.Internal
