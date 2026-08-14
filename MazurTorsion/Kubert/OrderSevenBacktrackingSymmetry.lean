/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingFactorCertificate

/-!
# Order-three symmetry of the order-seven backtracking cofactors

The fractional-linear parameter transformation `d ↦ 1 / (1 - d)` cyclically permutes the
three canonical degree-seven division cofactors and preserves the selection cofactor up to scale.
The accompanying affine change of the polynomial variable is explicit, so a coprimality
certificate for one division cofactor can be transported to the other two.

The division identities check the stored coefficient tables directly.  The
selection identity instead transports the structural Tate and dual-kernel
factorizations, then cancels their certified common factor.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

noncomputable section

/-- The order-three transformation of the order-seven Hauptmodul parameter. -/
def orderThreeParameter (d : ℚ) : ℚ :=
  (1 - d)⁻¹

/-- The affine polynomial-variable change accompanying `orderThreeParameter`. -/
def orderThreeAffine (d : ℚ) : ℚ[X] :=
  C ((d - 1)⁻¹ ^ 4) * X - C (d * (d - 1)⁻¹ ^ 3)

/-- The order-three transform stays away from zero when the original
parameter stays away from one. -/
theorem orderThreeParameter_ne_zero (d : ℚ) (hd : d ≠ 1) :
    orderThreeParameter d ≠ 0 := by
  unfold orderThreeParameter
  exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm hd))

/-- The order-three transform stays away from one when the original
parameter stays away from zero. -/
theorem orderThreeParameter_ne_one (d : ℚ) (hd : d ≠ 0) :
    orderThreeParameter d ≠ 1 := by
  unfold orderThreeParameter
  rw [inv_ne_one]
  intro h
  apply hd
  linarith

/-- The cubic singular factor is preserved up to a nonzero cube by the
order-three parameter symmetry. -/
theorem discriminantFactor_orderThreeParameter (d : ℚ) (hd : d ≠ 1) :
    orderThreeParameter d ^ 3 -
        8 * orderThreeParameter d ^ 2 +
        5 * orderThreeParameter d + 1 =
      (d - 1)⁻¹ ^ 3 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  simp only [orderThreeParameter]
  field_simp [sub_ne_zero.mpr hd]
  ring

/-- The order-three parameter symmetry sends the first division cofactor to the second. -/
theorem divisionCofactor0_orderThreeParameter_comp (d : ℚ) (hd : d ≠ 1) :
    (divisionCofactor0 (orderThreeParameter d)).comp (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 28) * divisionCofactor1 d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_mul, eval_C]
  simp only [orderThreeAffine, inv_pow, map_mul, eval_sub, eval_mul, eval_C, eval_X,
    divisionCofactor0, orderThreeParameter, divisionCofactorData0,
    Internal.divisionCofactor0Coefficient0,
    Internal.divisionCofactor0Coefficient0Chunk0, zero_add,
    Internal.divisionCofactor0Coefficient0Chunk1, mul_neg,
    Internal.divisionCofactor0Coefficient0Chunk2, mul_one, map_add, map_one, map_neg, map_pow,
    Internal.divisionCofactor0Coefficient1,
    Internal.divisionCofactor0Coefficient1Chunk0,
    Internal.divisionCofactor0Coefficient1Chunk1,
    Internal.divisionCofactor0Coefficient2,
    Internal.divisionCofactor0Coefficient2Chunk0,
    Internal.divisionCofactor0Coefficient2Chunk1,
    Internal.divisionCofactor0Coefficient3,
    Internal.divisionCofactor0Coefficient3Chunk0,
    Internal.divisionCofactor0Coefficient3Chunk1,
    Internal.divisionCofactor0Coefficient4,
    Internal.divisionCofactor0Coefficient4Chunk0,
    Internal.divisionCofactor0Coefficient5, Internal.divisionCofactor0Coefficient5Chunk0,
    Internal.divisionCofactor0Coefficient6, Internal.divisionCofactor0Coefficient6Chunk0,
    Internal.divisionCofactor0Coefficient7, Internal.divisionCofactor0Coefficient7Chunk0,
    Polynomial.map_add, Polynomial.map_mul, map_C, coe_evalRingHom, Polynomial.map_one,
    Polynomial.map_neg, eval_ofNat, Polynomial.map_pow, map_X, eval_add, eval_one, eval_neg,
    eval_pow, divisionCofactor1, divisionCofactorData1,
    Internal.divisionCofactor1Coefficient0,
    Internal.divisionCofactor1Coefficient0Chunk0,
    Internal.divisionCofactor1Coefficient0Chunk1,
    Internal.divisionCofactor1Coefficient0Chunk2,
    Internal.divisionCofactor1Coefficient1,
    Internal.divisionCofactor1Coefficient1Chunk0,
    Internal.divisionCofactor1Coefficient1Chunk1,
    Internal.divisionCofactor1Coefficient2,
    Internal.divisionCofactor1Coefficient2Chunk0,
    Internal.divisionCofactor1Coefficient2Chunk1,
    Internal.divisionCofactor1Coefficient3,
    Internal.divisionCofactor1Coefficient3Chunk0,
    Internal.divisionCofactor1Coefficient3Chunk1,
    Internal.divisionCofactor1Coefficient4,
    Internal.divisionCofactor1Coefficient4Chunk0,
    Internal.divisionCofactor1Coefficient5, Internal.divisionCofactor1Coefficient5Chunk0,
    Internal.divisionCofactor1Coefficient6,
    Internal.divisionCofactor1Coefficient6Chunk0,
    Internal.divisionCofactor1Coefficient7,
    Internal.divisionCofactor1Coefficient7Chunk0]
  field_simp [sub_ne_zero.mpr hd]
  ring

/-- The order-three parameter symmetry sends the second division cofactor to the third. -/
theorem divisionCofactor1_orderThreeParameter_comp (d : ℚ) (hd : d ≠ 1) :
    (divisionCofactor1 (orderThreeParameter d)).comp (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 28) * divisionCofactor2 d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_mul, eval_C]
  simp only [orderThreeAffine, inv_pow, map_mul, eval_sub, eval_mul, eval_C, eval_X,
    divisionCofactor1, orderThreeParameter, divisionCofactorData1,
    Internal.divisionCofactor1Coefficient0,
    Internal.divisionCofactor1Coefficient0Chunk0, zero_add,
    Internal.divisionCofactor1Coefficient0Chunk1, mul_neg,
    Internal.divisionCofactor1Coefficient0Chunk2, mul_one, map_add, map_neg, map_one, map_pow,
    Internal.divisionCofactor1Coefficient1,
    Internal.divisionCofactor1Coefficient1Chunk0,
    Internal.divisionCofactor1Coefficient1Chunk1,
    Internal.divisionCofactor1Coefficient2,
    Internal.divisionCofactor1Coefficient2Chunk0,
    Internal.divisionCofactor1Coefficient2Chunk1,
    Internal.divisionCofactor1Coefficient3,
    Internal.divisionCofactor1Coefficient3Chunk0,
    Internal.divisionCofactor1Coefficient3Chunk1,
    Internal.divisionCofactor1Coefficient4,
    Internal.divisionCofactor1Coefficient4Chunk0,
    Internal.divisionCofactor1Coefficient5,
    Internal.divisionCofactor1Coefficient5Chunk0,
    Internal.divisionCofactor1Coefficient6, Internal.divisionCofactor1Coefficient6Chunk0,
    Internal.divisionCofactor1Coefficient7, Internal.divisionCofactor1Coefficient7Chunk0,
    Polynomial.map_add, Polynomial.map_mul, map_C, coe_evalRingHom, Polynomial.map_neg,
    Polynomial.map_one, eval_ofNat, Polynomial.map_pow, map_X, eval_add, eval_neg, eval_one,
    eval_pow, divisionCofactor2, divisionCofactorData2,
    Internal.divisionCofactor2Coefficient0,
    Internal.divisionCofactor2Coefficient0Chunk0,
    Internal.divisionCofactor2Coefficient0Chunk1,
    Internal.divisionCofactor2Coefficient0Chunk2,
    Internal.divisionCofactor2Coefficient1,
    Internal.divisionCofactor2Coefficient1Chunk0,
    Internal.divisionCofactor2Coefficient1Chunk1,
    Internal.divisionCofactor2Coefficient2,
    Internal.divisionCofactor2Coefficient2Chunk0,
    Internal.divisionCofactor2Coefficient2Chunk1,
    Internal.divisionCofactor2Coefficient3,
    Internal.divisionCofactor2Coefficient3Chunk0,
    Internal.divisionCofactor2Coefficient3Chunk1,
    Internal.divisionCofactor2Coefficient4,
    Internal.divisionCofactor2Coefficient4Chunk0,
    Internal.divisionCofactor2Coefficient5, Internal.divisionCofactor2Coefficient5Chunk0,
    Internal.divisionCofactor2Coefficient6,
    Internal.divisionCofactor2Coefficient6Chunk0,
    Internal.divisionCofactor2Coefficient7,
    Internal.divisionCofactor2Coefficient7Chunk0]
  field_simp [sub_ne_zero.mpr hd]
  ring

/-- The order-three parameter symmetry sends the third division cofactor back to the first. -/
theorem divisionCofactor2_orderThreeParameter_comp (d : ℚ) (hd : d ≠ 1) :
    (divisionCofactor2 (orderThreeParameter d)).comp (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 28) * divisionCofactor0 d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_mul, eval_C]
  simp only [orderThreeAffine, inv_pow, map_mul, eval_sub, eval_mul, eval_C, eval_X,
    divisionCofactor2, orderThreeParameter, divisionCofactorData2,
    Internal.divisionCofactor2Coefficient0,
    Internal.divisionCofactor2Coefficient0Chunk0, zero_add,
    Internal.divisionCofactor2Coefficient0Chunk1, mul_neg,
    Internal.divisionCofactor2Coefficient0Chunk2, mul_one, map_add, map_one, map_neg, map_pow,
    Internal.divisionCofactor2Coefficient1,
    Internal.divisionCofactor2Coefficient1Chunk0,
    Internal.divisionCofactor2Coefficient1Chunk1,
    Internal.divisionCofactor2Coefficient2,
    Internal.divisionCofactor2Coefficient2Chunk0,
    Internal.divisionCofactor2Coefficient2Chunk1,
    Internal.divisionCofactor2Coefficient3,
    Internal.divisionCofactor2Coefficient3Chunk0,
    Internal.divisionCofactor2Coefficient3Chunk1,
    Internal.divisionCofactor2Coefficient4,
    Internal.divisionCofactor2Coefficient4Chunk0,
    Internal.divisionCofactor2Coefficient5,
    Internal.divisionCofactor2Coefficient5Chunk0,
    Internal.divisionCofactor2Coefficient6, Internal.divisionCofactor2Coefficient6Chunk0,
    Internal.divisionCofactor2Coefficient7, Internal.divisionCofactor2Coefficient7Chunk0,
    Polynomial.map_add, Polynomial.map_mul, map_C, coe_evalRingHom, Polynomial.map_one,
    Polynomial.map_neg, eval_ofNat, Polynomial.map_pow, map_X, eval_add, eval_one, eval_neg,
    eval_pow, divisionCofactor0, divisionCofactorData0,
    Internal.divisionCofactor0Coefficient0,
    Internal.divisionCofactor0Coefficient0Chunk0,
    Internal.divisionCofactor0Coefficient0Chunk1,
    Internal.divisionCofactor0Coefficient0Chunk2,
    Internal.divisionCofactor0Coefficient1,
    Internal.divisionCofactor0Coefficient1Chunk0,
    Internal.divisionCofactor0Coefficient1Chunk1,
    Internal.divisionCofactor0Coefficient2,
    Internal.divisionCofactor0Coefficient2Chunk0,
    Internal.divisionCofactor0Coefficient2Chunk1,
    Internal.divisionCofactor0Coefficient3,
    Internal.divisionCofactor0Coefficient3Chunk0,
    Internal.divisionCofactor0Coefficient3Chunk1,
    Internal.divisionCofactor0Coefficient4,
    Internal.divisionCofactor0Coefficient4Chunk0,
    Internal.divisionCofactor0Coefficient5,
    Internal.divisionCofactor0Coefficient5Chunk0,
    Internal.divisionCofactor0Coefficient6,
    Internal.divisionCofactor0Coefficient6Chunk0,
    Internal.divisionCofactor0Coefficient7,
    Internal.divisionCofactor0Coefficient7Chunk0]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem completedCubic_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    Doubling.completedCubic (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 12 *
        Doubling.completedCubic (orderSevenQuotient d) x := by
  simp [Doubling.completedCubic, orderSevenQuotient,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    orderSevenB, orderSevenC, orderThreeParameter, orderThreeAffine]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem completedTateLinear_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    12 * (orderThreeAffine d).eval x +
        (orderSevenQuotient (orderThreeParameter d)).b₂ =
      (d - 1)⁻¹ ^ 4 *
        (12 * x + (orderSevenQuotient d).b₂) := by
  simp [orderSevenQuotient, WeierstrassCurve.b₂,
    orderSevenB, orderSevenC, orderThreeParameter, orderThreeAffine]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem completedTangent_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateCompletedTangentNumerator
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 8 *
        pointTateCompletedTangentNumerator (orderSevenQuotient d) x := by
  simp [pointTateCompletedTangentNumerator, orderSevenQuotient,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, orderSevenB, orderSevenC,
    orderThreeParameter, orderThreeAffine]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem tateAlpha_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateAlphaUnivariateCleared
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 16 *
        pointTateAlphaUnivariateCleared (orderSevenQuotient d) x := by
  rw [pointTateAlphaUnivariateCleared,
    completedTateLinear_orderThreeParameter d x hd,
    completedCubic_orderThreeParameter d x hd,
    completedTangent_orderThreeParameter d x hd,
    pointTateAlphaUnivariateCleared]
  ring

private theorem tateGamma_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateGammaUnivariateCleared
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 24 *
        pointTateGammaUnivariateCleared (orderSevenQuotient d) x := by
  rw [pointTateGammaUnivariateCleared,
    completedCubic_orderThreeParameter d x hd,
    tateAlpha_orderThreeParameter d x hd,
    completedTangent_orderThreeParameter d x hd,
    pointTateGammaUnivariateCleared]
  ring

private theorem tateParameterNumerator_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateParameterUnivariateNumerator
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 48 *
        pointTateParameterUnivariateNumerator (orderSevenQuotient d) x := by
  rw [pointTateParameterUnivariateNumerator,
    tateAlpha_orderThreeParameter d x hd,
    pointTateParameterUnivariateNumerator]
  ring

private theorem tateParameterDenominator_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    pointTateParameterUnivariateDenominator
        (orderSevenQuotient (orderThreeParameter d))
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 48 *
        pointTateParameterUnivariateDenominator
          (orderSevenQuotient d) x := by
  rw [pointTateParameterUnivariateDenominator,
    tateGamma_orderThreeParameter d x hd,
    completedCubic_orderThreeParameter d x hd,
    pointTateParameterUnivariateDenominator]
  ring

private theorem selectionPolynomial_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    orderSevenSelectionPolynomial (orderThreeParameter d)
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 147 * orderSevenSelectionPolynomial d x := by
  rw [orderSevenSelectionPolynomial,
    tateParameterNumerator_orderThreeParameter d x hd,
    tateParameterDenominator_orderThreeParameter d x hd,
    orderSevenSelectionPolynomial]
  simp only [orderThreeParameter,
    orderSevenParameterHauptmodulNumerator,
    orderSevenParameterCubic]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem selectionPolynomialData_orderThreeParameter
    (d : ℚ) (hd : d ≠ 1) :
    (Internal.selectionPolynomialData (orderThreeParameter d)).comp
        (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 147) *
        Internal.selectionPolynomialData d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, Internal.selectionPolynomialData_eval,
    eval_mul, eval_C]
  exact selectionPolynomial_orderThreeParameter d x hd

private theorem dualKernel_orderThreeParameter
    (d x : ℚ) (hd : d ≠ 1) :
    orderSevenDualKernelPolynomial (orderThreeParameter d)
        ((orderThreeAffine d).eval x) =
      (d - 1)⁻¹ ^ 12 *
        orderSevenDualKernelPolynomial d x := by
  simp [orderSevenDualKernelPolynomial,
    orderThreeParameter, orderThreeAffine]
  field_simp [sub_ne_zero.mpr hd]
  ring

private theorem dualKernelPolynomial_orderThreeParameter
    (d : ℚ) (hd : d ≠ 1) :
    (Internal.dualKernelPolynomial (orderThreeParameter d)).comp
        (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 12) *
        Internal.dualKernelPolynomial d := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, Internal.dualKernelPolynomial_eval,
    eval_mul, eval_C]
  exact dualKernel_orderThreeParameter d x hd

private theorem selectionPolynomial_factorization (d : ℚ) :
    Internal.selectionPolynomialData d =
      C (64 ^ 3 : ℚ) * Internal.dualKernelPolynomial d *
        selectionCofactor d := by
  apply Polynomial.funext
  intro x
  simpa [Internal.selectionPolynomialData_eval,
    Internal.dualKernelPolynomial_eval, mul_assoc] using
      orderSevenSelectionPolynomial_eval_factorization d x

/-- The selection cofactor is preserved up to scale by the order-three parameter symmetry. -/
theorem selectionCofactor_orderThreeParameter_comp (d : ℚ) (hd : d ≠ 1) :
    (selectionCofactor (orderThreeParameter d)).comp (orderThreeAffine d) =
      C ((d - 1)⁻¹ ^ 135) * selectionCofactor d := by
  have hdual : Internal.dualKernelPolynomial d ≠ 0 := by
    have hdegree :
        (Internal.dualKernelPolynomial d).natDegree = 3 := by
      unfold Internal.dualKernelPolynomial
      compute_degree
      all_goals norm_num
    intro h
    rw [h] at hdegree
    norm_num at hdegree
  have hscale : (d - 1)⁻¹ ^ 12 ≠ 0 :=
    pow_ne_zero 12 (inv_ne_zero (sub_ne_zero.mpr hd))
  have hcommon :
      C (64 ^ 3 : ℚ) * C ((d - 1)⁻¹ ^ 12) *
          Internal.dualKernelPolynomial d ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (C_ne_zero.mpr hscale)) hdual
  have hfactorTransformed :
      (Internal.selectionPolynomialData (orderThreeParameter d)).comp
          (orderThreeAffine d) =
        C (64 ^ 3 : ℚ) *
          (Internal.dualKernelPolynomial
            (orderThreeParameter d)).comp (orderThreeAffine d) *
          (selectionCofactor
            (orderThreeParameter d)).comp (orderThreeAffine d) := by
    have h := congrArg (Polynomial.compRingHom (orderThreeAffine d))
      (selectionPolynomial_factorization (orderThreeParameter d))
    simpa using h
  apply mul_left_cancel₀ hcommon
  calc
    (C (64 ^ 3 : ℚ) * C ((d - 1)⁻¹ ^ 12) *
          Internal.dualKernelPolynomial d) *
        (selectionCofactor (orderThreeParameter d)).comp
          (orderThreeAffine d) =
        (Internal.selectionPolynomialData
          (orderThreeParameter d)).comp (orderThreeAffine d) := by
      rw [hfactorTransformed,
        dualKernelPolynomial_orderThreeParameter d hd]
      ring
    _ = C ((d - 1)⁻¹ ^ 147) *
          Internal.selectionPolynomialData d :=
      selectionPolynomialData_orderThreeParameter d hd
    _ = (C (64 ^ 3 : ℚ) * C ((d - 1)⁻¹ ^ 12) *
          Internal.dualKernelPolynomial d) *
        (C ((d - 1)⁻¹ ^ 135) * selectionCofactor d) := by
      rw [selectionPolynomial_factorization,
        show 147 = 12 + 135 by norm_num, pow_add, map_mul]
      ring

/-- Coprimality with the first division cofactor at the transformed
parameter transports to coprimality with the second cofactor. -/
theorem isCoprime_selection_divisionCofactor1_of_orderThreeParameter
    (d : ℚ) (hd : d ≠ 1)
    (hcop : IsCoprime
      (selectionCofactor (orderThreeParameter d))
      (divisionCofactor0 (orderThreeParameter d))) :
    IsCoprime (selectionCofactor d) (divisionCofactor1 d) := by
  have hmap := hcop.map (Polynomial.compRingHom (orderThreeAffine d))
  change IsCoprime
    ((selectionCofactor (orderThreeParameter d)).comp (orderThreeAffine d))
    ((divisionCofactor0 (orderThreeParameter d)).comp
      (orderThreeAffine d)) at hmap
  rw [selectionCofactor_orderThreeParameter_comp d hd,
    divisionCofactor0_orderThreeParameter_comp d hd] at hmap
  exact hmap.of_mul_left_right.symm.of_mul_left_right.symm

/-- Coprimality with the second division cofactor at the transformed
parameter transports to coprimality with the third cofactor. -/
theorem isCoprime_selection_divisionCofactor2_of_orderThreeParameter
    (d : ℚ) (hd : d ≠ 1)
    (hcop : IsCoprime
      (selectionCofactor (orderThreeParameter d))
      (divisionCofactor1 (orderThreeParameter d))) :
    IsCoprime (selectionCofactor d) (divisionCofactor2 d) := by
  have hmap := hcop.map (Polynomial.compRingHom (orderThreeAffine d))
  change IsCoprime
    ((selectionCofactor (orderThreeParameter d)).comp (orderThreeAffine d))
    ((divisionCofactor1 (orderThreeParameter d)).comp
      (orderThreeAffine d)) at hmap
  rw [selectionCofactor_orderThreeParameter_comp d hd,
    divisionCofactor1_orderThreeParameter_comp d hd] at hmap
  exact hmap.of_mul_left_right.symm.of_mul_left_right.symm

end

end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
