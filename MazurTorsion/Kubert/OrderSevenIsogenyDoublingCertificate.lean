/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenIsogenyDoublingCertificateEval7
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Polynomial certificate for order-seven isogeny doubling

The cleared Vélu abscissa commutes with tangent doubling by a homogeneous
polynomial identity of degree `28`.  We verify the identity at `29` distinct
rational values and close it with the degree bound.  The pointwise ring
certificates live in serially imported shards, keeping the memory required by
each Lean process bounded during a cold build.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingCertificate

private theorem eval_fin (d : ℚ) (i : Fin 29) :
    Internal.EvalCertificate d (i : ℚ) := by
  fin_cases i
  · (convert Internal.evalBlock0 d (0 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock0 d (1 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock0 d (2 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock0 d (3 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock1 d (0 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock1 d (1 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock1 d (2 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock1 d (3 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock2 d (0 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock2 d (1 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock2 d (2 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock2 d (3 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock3 d (0 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock3 d (1 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock3 d (2 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock3 d (3 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock4 d (0 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock4 d (1 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock4 d (2 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock4 d (3 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock5 d (0 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock5 d (1 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock5 d (2 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock5 d (3 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock6 d (0 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock6 d (1 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock6 d (2 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock6 d (3 : Fin 4) using 1; norm_num)
  · (convert Internal.evalBlock7 d (0 : Fin 1) using 1; norm_num)

/-- The degree-`28` homogeneous abscissa certificate for doubling through
the explicit order-seven Vélu map. -/
theorem polynomial_identity (d : ℚ) :
    veluXHomogeneousPolynomial d (sourceDoubleXPolynomial d)
        (sourceCompletedCubicPolynomial d) =
      doubleXHomogeneousPolynomial (orderSevenQuotient d)
        (veluXPolynomial d) (kernelPolynomial d ^ 2) := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    _ _ (f := fun i : Fin 29 ↦ (i : ℚ))
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_injective hij
  · intro i
    exact eval_fin d i
  · simp only [Fintype.card_fin]
    have hl := Internal.left_degree d
    have hr := Internal.right_degree d
    omega

end MazurTorsion.Kubert.OrderSevenDoublingCertificate
