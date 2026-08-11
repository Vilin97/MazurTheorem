/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialXFourCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialVFourCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialCompositeUData
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialFactorPowerData

/-!
# Checked shared powers for the raw order-twenty-five polynomial certificate

The large `X` and `V` cubes and fourth powers are supplied by their canonical
factor-by-factor verifiers.  This module checks only the base composites and
the remaining small powers, then exposes one semantic bundle to the final
polynomial consumer.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense
open OrderTwentyFiveDensePolynomialRectangular

private def product : List Two → Two
  | [] => [[1]]
  | p :: ps => Two.mul p (product ps)

private theorem eval_product (ps : List Two) (r s : ℚ) :
    Two.eval (product ps) r s = (ps.map (fun p => Two.eval p r s)).prod := by
  induction ps with
  | nil => norm_num [product, Two.eval, One.eval, evalWith]
  | cons p ps ih => simp [product, Two.eval_mul, ih]

private theorem xData_spec :
    rectangularize 14 19
        (product [RData, KData, KData, KData, MData, NData]) =
      rectangularize 14 19 XData := by
  decide

private theorem uData_spec :
    rectangularize 5 6 (Two.mul AData LData) =
      rectangularize 5 6 UData := by
  decide

private theorem vData_spec :
    rectangularize 16 23
        (product [SData, CData, CData, CData, JData, P9Data]) =
      rectangularize 16 23 VData := by
  decide

private theorem x2Data_spec :
    rectangularize 27 37 (Two.mul XData XData) =
      rectangularize 27 37 X2Data := by
  decide

private theorem u2Data_spec :
    rectangularize 9 11 (Two.mul UData UData) =
      rectangularize 9 11 U2Data := by
  decide

private theorem u3Data_spec :
    rectangularize 13 16 (Two.mul U2Data UData) =
      rectangularize 13 16 U3Data := by
  decide

private theorem u4Data_spec :
    rectangularize 17 21 (Two.mul U3Data UData) =
      rectangularize 17 21 U4Data := by
  decide

private theorem v2Data_spec :
    rectangularize 31 45 (Two.mul VData VData) =
      rectangularize 31 45 V2Data := by
  decide

private theorem b2Data_spec :
    rectangularize 1 3 (Two.mul BData BData) =
      rectangularize 1 3 B2Data := by
  decide

private theorem b3Data_spec :
    rectangularize 1 4 (Two.mul B2Data BData) =
      rectangularize 1 4 B3Data := by
  decide

private theorem b4Data_spec :
    rectangularize 1 5 (Two.mul B3Data BData) =
      rectangularize 1 5 B4Data := by
  decide

private theorem b5Data_spec :
    rectangularize 1 6 (Two.mul B4Data BData) =
      rectangularize 1 6 B5Data := by
  decide

private theorem d2Data_spec :
    rectangularize 5 7 (Two.mul DData DData) =
      rectangularize 5 7 D2Data := by
  decide

private theorem d3Data_spec :
    rectangularize 7 10 (Two.mul D2Data DData) =
      rectangularize 7 10 D3Data := by
  decide

private theorem d4Data_spec :
    rectangularize 9 13 (Two.mul D3Data DData) =
      rectangularize 9 13 D4Data := by
  decide

private theorem d5Data_spec :
    rectangularize 11 16 (Two.mul D4Data DData) =
      rectangularize 11 16 D5Data := by
  decide

private theorem d6Data_spec :
    rectangularize 13 19 (Two.mul D5Data DData) =
      rectangularize 13 19 D6Data := by
  decide

private theorem d7Data_spec :
    rectangularize 15 22 (Two.mul D6Data DData) =
      rectangularize 15 22 D7Data := by
  decide

private theorem d8Data_spec :
    rectangularize 17 25 (Two.mul D7Data DData) =
      rectangularize 17 25 D8Data := by
  decide

private theorem e2Data_spec :
    rectangularize 5 5 (Two.mul EData EData) =
      rectangularize 5 5 E2Data := by
  decide

private theorem e3Data_spec :
    rectangularize 7 7 (Two.mul E2Data EData) =
      rectangularize 7 7 E3Data := by
  decide

private theorem e4Data_spec :
    rectangularize 9 9 (Two.mul E3Data EData) =
      rectangularize 9 9 E4Data := by
  decide

private theorem e5Data_spec :
    rectangularize 11 11 (Two.mul E4Data EData) =
      rectangularize 11 11 E5Data := by
  decide

private theorem t2Data_spec :
    rectangularize 5 9 (Two.mul TData TData) =
      rectangularize 5 9 T2Data := by
  decide

private theorem t3Data_spec :
    rectangularize 7 13 (Two.mul T2Data TData) =
      rectangularize 7 13 T3Data := by
  decide

private theorem t4Data_spec :
    rectangularize 9 17 (Two.mul T3Data TData) =
      rectangularize 9 17 T4Data := by
  decide

private theorem t5Data_spec :
    rectangularize 11 21 (Two.mul T4Data TData) =
      rectangularize 11 21 T5Data := by
  decide

private theorem eval_mul_spec {p q target : Two} {outer inner : ℕ}
    (h : rectangularize outer inner (Two.mul p q) =
      rectangularize outer inner target) (r s : ℚ) :
    Two.eval target r s = Two.eval p r s * Two.eval q r s := by
  have hEval := congrArg (fun z => Two.eval z r s) h
  simpa only [eval_rectangularize, Two.eval_mul] using hEval.symm

private theorem eval_xData (r s : ℚ) :
    Two.eval XData r s =
      r * OrderTwentyFiveRelationZeroCertificate.Internal.K r s ^ 3 *
        OrderTwentyFiveRelationZeroCertificate.Internal.M r s *
          OrderTwentyFiveRawOrbitFactorCertificate.N r s := by
  have hEval := congrArg (fun z => Two.eval z r s) xData_spec
  simp only [eval_rectangularize] at hEval
  rw [← hEval, eval_product]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [eval_RData, eval_KData, eval_MData, eval_NData,
    OrderTwentyFiveRelationZeroCertificate.Internal.N_eq_factor]
  ring

private theorem eval_uData (r s : ℚ) :
    Two.eval UData r s =
      OrderTwentyFiveRelationZeroCertificate.Internal.A r s *
        OrderTwentyFiveRelationZeroCertificate.Internal.L r s := by
  rw [eval_mul_spec uData_spec, eval_AData, eval_LData]

private theorem eval_vData (r s : ℚ) :
    Two.eval VData r s =
      s * OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 *
        OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
          OrderTwentyFiveRawOrbitFactorCertificate.P9 r s := by
  have hEval := congrArg (fun z => Two.eval z r s) vData_spec
  simp only [eval_rectangularize] at hEval
  rw [← hEval, eval_product]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  rw [eval_SData, eval_CData, eval_JData, eval_P9Data,
    OrderTwentyFiveRelationZeroCertificate.Internal.P9_eq_factor]
  ring

/-- All checked shared-power evaluations used by the final raw certificate. -/
theorem eval_sharedPowerData (r s : ℚ) :
    Two.eval XData r s =
        r * OrderTwentyFiveRelationZeroCertificate.Internal.K r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.M r s *
            OrderTwentyFiveRawOrbitFactorCertificate.N r s ∧
    Two.eval X2Data r s = Two.eval XData r s * Two.eval XData r s ∧
    Two.eval X3Data r s = Two.eval XData r s * Two.eval X2Data r s ∧
    Two.eval X4Data r s = Two.eval XData r s * Two.eval X2Data r s *
        (r * OrderTwentyFiveRelationZeroCertificate.Internal.K r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.M r s *
            OrderTwentyFiveRawOrbitFactorCertificate.N r s) ∧
    Two.eval UData r s =
        OrderTwentyFiveRelationZeroCertificate.Internal.A r s *
          OrderTwentyFiveRelationZeroCertificate.Internal.L r s ∧
    Two.eval U2Data r s = Two.eval UData r s * Two.eval UData r s ∧
    Two.eval U3Data r s = Two.eval U2Data r s * Two.eval UData r s ∧
    Two.eval U4Data r s = Two.eval U3Data r s * Two.eval UData r s ∧
    Two.eval VData r s =
        s * OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
            OrderTwentyFiveRawOrbitFactorCertificate.P9 r s ∧
    Two.eval V2Data r s = Two.eval VData r s * Two.eval VData r s ∧
    Two.eval V3Data r s = Two.eval VData r s * Two.eval V2Data r s ∧
    Two.eval V4Data r s = Two.eval VData r s * Two.eval V2Data r s *
        (s * OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
            OrderTwentyFiveRawOrbitFactorCertificate.P9 r s) ∧
    Two.eval B2Data r s = Two.eval BData r s * Two.eval BData r s ∧
    Two.eval B3Data r s = Two.eval B2Data r s * Two.eval BData r s ∧
    Two.eval B4Data r s = Two.eval B3Data r s * Two.eval BData r s ∧
    Two.eval B5Data r s = Two.eval B4Data r s * Two.eval BData r s ∧
    Two.eval D2Data r s = Two.eval DData r s * Two.eval DData r s ∧
    Two.eval D3Data r s = Two.eval D2Data r s * Two.eval DData r s ∧
    Two.eval D4Data r s = Two.eval D3Data r s * Two.eval DData r s ∧
    Two.eval D5Data r s = Two.eval D4Data r s * Two.eval DData r s ∧
    Two.eval D6Data r s = Two.eval D5Data r s * Two.eval DData r s ∧
    Two.eval D7Data r s = Two.eval D6Data r s * Two.eval DData r s ∧
    Two.eval D8Data r s = Two.eval D7Data r s * Two.eval DData r s ∧
    Two.eval E2Data r s = Two.eval EData r s * Two.eval EData r s ∧
    Two.eval E3Data r s = Two.eval E2Data r s * Two.eval EData r s ∧
    Two.eval E4Data r s = Two.eval E3Data r s * Two.eval EData r s ∧
    Two.eval E5Data r s = Two.eval E4Data r s * Two.eval EData r s ∧
    Two.eval T2Data r s = Two.eval TData r s * Two.eval TData r s ∧
    Two.eval T3Data r s = Two.eval T2Data r s * Two.eval TData r s ∧
    Two.eval T4Data r s = Two.eval T3Data r s * Two.eval TData r s ∧
    Two.eval T5Data r s = Two.eval T4Data r s * Two.eval TData r s := by
  exact ⟨eval_xData r s,
    eval_mul_spec x2Data_spec r s,
    eval_x3Data r s,
    eval_x4Data r s,
    eval_uData r s,
    eval_mul_spec u2Data_spec r s,
    eval_mul_spec u3Data_spec r s,
    eval_mul_spec u4Data_spec r s,
    eval_vData r s,
    eval_mul_spec v2Data_spec r s,
    eval_v3Data r s,
    eval_v4Data r s,
    eval_mul_spec b2Data_spec r s,
    eval_mul_spec b3Data_spec r s,
    eval_mul_spec b4Data_spec r s,
    eval_mul_spec b5Data_spec r s,
    eval_mul_spec d2Data_spec r s,
    eval_mul_spec d3Data_spec r s,
    eval_mul_spec d4Data_spec r s,
    eval_mul_spec d5Data_spec r s,
    eval_mul_spec d6Data_spec r s,
    eval_mul_spec d7Data_spec r s,
    eval_mul_spec d8Data_spec r s,
    eval_mul_spec e2Data_spec r s,
    eval_mul_spec e3Data_spec r s,
    eval_mul_spec e4Data_spec r s,
    eval_mul_spec e5Data_spec r s,
    eval_mul_spec t2Data_spec r s,
    eval_mul_spec t3Data_spec r s,
    eval_mul_spec t4Data_spec r s,
    eval_mul_spec t5Data_spec r s⟩

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
