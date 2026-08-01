/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenDualKernel
import MazurTorsion.Kubert.OrderSevenIsogenyPolynomialData
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic.ComputeDegree

/-!
# Polynomial data for the order-seven dual-kernel pullback

After substituting the cleared Vélu abscissa into the dual-kernel cubic,
homogenization gives a polynomial of degree `21`.  Multiplication by the
source kernel cubic produces the source seventh division polynomial, of
degree `24`.  This file packages both sides and the degree bounds used by the
interpolation certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDualKernelCertificate

open OrderSevenIsogenyPolynomialData

noncomputable def dualKernelHomogeneousPolynomial
    (d : ℚ) (u v : ℚ[X]) : ℚ[X] :=
  C 7 * u ^ 3 +
    C (14 * d ^ 4 - 35 * d ^ 3 + 42 * d ^ 2 - 21 * d + 14) * u ^ 2 * v +
    C (7 * d ^ 8 - 7 * d ^ 7 - 98 * d ^ 6 + 224 * d ^ 5 - 203 * d ^ 4 +
      49 * d ^ 3 + 77 * d ^ 2 - 49 * d + 7) * u * v ^ 2 +
    C (d ^ 12 + 3 * d ^ 11 - 51 * d ^ 10 + 185 * d ^ 9 - 767 * d ^ 8 +
      2097 * d ^ 7 - 2835 * d ^ 6 + 1738 * d ^ 5 - 295 * d ^ 4 -
      116 * d ^ 3 + 55 * d ^ 2 - 15 * d + 1) * v ^ 3

noncomputable def pulledDualKernelPolynomial (d : ℚ) : ℚ[X] :=
  kernelPolynomial d *
    dualKernelHomogeneousPolynomial d (veluXPolynomial d)
      (kernelPolynomial d ^ 2)

namespace Internal

lemma source_prePsiSeven (d : ℚ) :
    (orderSevenFamily d).preΨ' 7 =
      ((orderSevenFamily d).preΨ₄ * (orderSevenFamily d).Ψ₂Sq ^ 2 -
          (orderSevenFamily d).Ψ₃ ^ 3) * (orderSevenFamily d).Ψ₃ ^ 3 -
        (orderSevenFamily d).preΨ₄ ^ 3 *
          (orderSevenFamily d).Ψ₂Sq ^ 2 := by
  have hfive :
      (orderSevenFamily d).preΨ' 5 =
        (orderSevenFamily d).preΨ₄ * (orderSevenFamily d).Ψ₂Sq ^ 2 -
          (orderSevenFamily d).Ψ₃ ^ 3 := by
    rw [show (5 : ℕ) = 2 * (0 + 2) + 1 by norm_num,
      (orderSevenFamily d).preΨ'_odd 0]
    norm_num
  rw [show (7 : ℕ) = 2 * (1 + 2) + 1 by norm_num,
    (orderSevenFamily d).preΨ'_odd 1]
  norm_num [hfive]

lemma pullback_degree (d : ℚ) :
    (pulledDualKernelPolynomial d).natDegree ≤ 24 := by
  unfold pulledDualKernelPolynomial dualKernelHomogeneousPolynomial
    OrderSevenIsogenyPolynomialData.veluXPolynomial
    OrderSevenIsogenyPolynomialData.kernelPolynomial
  compute_degree

lemma source_degree (d : ℚ) :
    ((orderSevenFamily d).preΨ' 7).natDegree ≤ 24 := by
  apply le_trans ((orderSevenFamily d).natDegree_preΨ'_le 7)
  have hodd : ¬Even (7 : ℕ) := by decide
  simp [hodd]

def EvalCertificate (d n : ℚ) : Prop :=
  (pulledDualKernelPolynomial d).eval n =
    ((orderSevenFamily d).preΨ' 7).eval n

end Internal

end MazurTorsion.Kubert.OrderSevenDualKernelCertificate
