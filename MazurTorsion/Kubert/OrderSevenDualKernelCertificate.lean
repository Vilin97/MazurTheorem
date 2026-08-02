/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenDualKernelCertificateEval4
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Pullback certificate for the order-seven dual-kernel cubic

The cleared pullback identity has degree `24` in the source abscissa.  We
verify it at `25` distinct rational values and use the degree bound to conclude
the polynomial identity.  The pointwise ring proofs are serially sharded so
each Lean process has a modest memory bound.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDualKernelCertificate

private theorem eval_fin (d : ℚ) (i : Fin 25) :
    Internal.EvalCertificate d (i : ℚ) := by
  fin_cases i
  · (convert Internal.evalBlock0 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock0 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock0 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock0 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock0 d (4 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock1 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock1 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock1 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock1 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock1 d (4 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock2 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock2 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock2 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock2 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock2 d (4 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock3 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock3 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock3 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock3 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock3 d (4 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock4 d (0 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock4 d (1 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock4 d (2 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock4 d (3 : Fin 5) using 1; norm_num)
  · (convert Internal.evalBlock4 d (4 : Fin 5) using 1; norm_num)

/-- Clearing the Vélu denominator in the dual-kernel cubic produces the
source seventh division polynomial. -/
theorem polynomial_identity (d : ℚ) :
    pulledDualKernelPolynomial d = (orderSevenFamily d).preΨ' 7 := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ (f := fun i : Fin 25 ↦ (i : ℚ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  · intro i
    exact eval_fin d i
  · simp only [Fintype.card_fin]
    have hl := Internal.pullback_degree d
    have hr := Internal.source_degree d
    omega

end MazurTorsion.Kubert.OrderSevenDualKernelCertificate
