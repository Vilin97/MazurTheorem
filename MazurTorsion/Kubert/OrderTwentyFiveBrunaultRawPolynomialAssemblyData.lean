/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialPowerCertificate
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialDivisionData

/-!
# Shared assembly data for the raw order-twenty-five numerator

This leaf rebuilds the reduced numerator from the checked shared powers used
in Brunault's cleared equation.  The generated reduced coefficient table is
not repeated here: downstream row certificates compare `assemblyData` with
the canonical `divisionReducedData` imported above.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveRelationZeroCertificate.Dense

private def product : List Two → Two
  | [] => [[1]]
  | p :: ps => Two.mul p (product ps)

private def sum : List Two → Two
  | [] => []
  | p :: ps => Two.add p (sum ps)

private def scaledProduct (z : ℤ) (ps : List Two) : Two :=
  Two.mul [[z]] (product ps)

private theorem eval_product (ps : List Two) (r s : ℚ) :
    Two.eval (product ps) r s =
      (ps.map (fun p => Two.eval p r s)).prod := by
  induction ps with
  | nil => norm_num [product, Two.eval, One.eval, evalWith]
  | cons p ps ih => simp [product, Two.eval_mul, ih]

private theorem eval_sum (ps : List Two) (r s : ℚ) :
    Two.eval (sum ps) r s =
      (ps.map (fun p => Two.eval p r s)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sum, Two.eval_add, ih]

private theorem eval_scaledProduct (z : ℤ) (ps : List Two) (r s : ℚ) :
    Two.eval (scaledProduct z ps) r s =
      (z : ℚ) * (ps.map (fun p => Two.eval p r s)).prod := by
  rw [scaledProduct, Two.eval_mul, eval_product]
  norm_num [Two.eval, One.eval, evalWith]

private def compactNumerator (x u v b d e t : ℚ) : ℚ :=
  u ^ 4 * t ^ 5 * x ^ 2 * v ^ 2 +
    x ^ 3 * u ^ 3 * v * b ^ 2 * d * e ^ 2 * t ^ 5 -
    x ^ 2 * u ^ 3 * v ^ 2 * b * d ^ 2 * e * t ^ 4 -
    3 * x ^ 3 * u ^ 2 * v * b ^ 3 * d ^ 3 * e ^ 3 * t ^ 4 -
    x ^ 2 * u ^ 2 * v ^ 2 * b ^ 2 * d ^ 4 * e ^ 2 * t ^ 3 +
    2 * x * u ^ 2 * v ^ 3 * b * d ^ 5 * e * t ^ 2 -
    x ^ 4 * u * b ^ 5 * d ^ 4 * e ^ 5 * t ^ 4 +
    4 * x ^ 2 * u * v ^ 2 * b ^ 3 * d ^ 6 * e ^ 3 * t ^ 2 +
    x * u * v ^ 3 * b ^ 2 * d ^ 7 * e ^ 2 * t +
    u * v ^ 4 * b * d ^ 8 * e +
    x ^ 3 * v * b ^ 5 * d ^ 7 * e ^ 5 * t ^ 2

/-- The eleven raw-factor terms obtained from Brunault's cleared equation
after removing its common factor `B²D²E²T`. -/
def reducedNumerator (r s : ℚ) : ℚ :=
  let x :=
    r * OrderTwentyFiveRelationZeroCertificate.Internal.K r s ^ 3 *
      OrderTwentyFiveRelationZeroCertificate.Internal.M r s *
        OrderTwentyFiveRawOrbitFactorCertificate.N r s
  let u :=
    OrderTwentyFiveRelationZeroCertificate.Internal.A r s *
      OrderTwentyFiveRelationZeroCertificate.Internal.L r s
  let v :=
    s * OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 *
      OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
        OrderTwentyFiveRawOrbitFactorCertificate.P9 r s
  let b := OrderTwentyFiveRelationZeroCertificate.Internal.B r s
  let d := OrderTwentyFiveRelationZeroCertificate.Internal.D r s
  let e := OrderTwentyFiveRelationZeroCertificate.Internal.E r s
  let t := OrderTwentyFiveRelationZeroCertificate.Internal.T r s
  u ^ 4 * t ^ 5 * x ^ 2 * v ^ 2 +
    x ^ 3 * u ^ 3 * v * b ^ 2 * d * e ^ 2 * t ^ 5 -
    x ^ 2 * u ^ 3 * v ^ 2 * b * d ^ 2 * e * t ^ 4 -
    3 * x ^ 3 * u ^ 2 * v * b ^ 3 * d ^ 3 * e ^ 3 * t ^ 4 -
    x ^ 2 * u ^ 2 * v ^ 2 * b ^ 2 * d ^ 4 * e ^ 2 * t ^ 3 +
    2 * x * u ^ 2 * v ^ 3 * b * d ^ 5 * e * t ^ 2 -
    x ^ 4 * u * b ^ 5 * d ^ 4 * e ^ 5 * t ^ 4 +
    4 * x ^ 2 * u * v ^ 2 * b ^ 3 * d ^ 6 * e ^ 3 * t ^ 2 +
    x * u * v ^ 3 * b ^ 2 * d ^ 7 * e ^ 2 * t +
    u * v ^ 4 * b * d ^ 8 * e +
    x ^ 3 * v * b ^ 5 * d ^ 7 * e ^ 5 * t ^ 2

/-- Dense assembly of the eleven reduced-numerator terms from the checked
shared-power tables. -/
def assemblyData : Two :=
  sum [
    scaledProduct 1 [U4Data, T5Data, X2Data, V2Data],
    scaledProduct 1 [X3Data, U3Data, VData, B2Data, DData, E2Data, T5Data],
    scaledProduct (-1) [X2Data, U3Data, V2Data, BData, D2Data, EData, T4Data],
    scaledProduct (-3) [X3Data, U2Data, VData, B3Data, D3Data, E3Data, T4Data],
    scaledProduct (-1) [X2Data, U2Data, V2Data, B2Data, D4Data, E2Data, T3Data],
    scaledProduct 2 [XData, U2Data, V3Data, BData, D5Data, EData, T2Data],
    scaledProduct (-1) [X4Data, UData, B5Data, D4Data, E5Data, T4Data],
    scaledProduct 4 [X2Data, UData, V2Data, B3Data, D6Data, E3Data, T2Data],
    scaledProduct 1 [XData, UData, V3Data, B2Data, D7Data, E2Data, TData],
    scaledProduct 1 [UData, V4Data, BData, D8Data, EData],
    scaledProduct 1 [X3Data, VData, B5Data, D7Data, E5Data, T2Data]
  ]

private theorem eval_assemblyData_eq_compact (r s : ℚ) :
    Two.eval assemblyData r s =
      compactNumerator
        (r * OrderTwentyFiveRelationZeroCertificate.Internal.K r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.M r s *
            OrderTwentyFiveRawOrbitFactorCertificate.N r s)
        (OrderTwentyFiveRelationZeroCertificate.Internal.A r s *
          OrderTwentyFiveRelationZeroCertificate.Internal.L r s)
        (s * OrderTwentyFiveRelationZeroCertificate.Internal.C r s ^ 3 *
          OrderTwentyFiveRelationZeroCertificate.Internal.J r s *
            OrderTwentyFiveRawOrbitFactorCertificate.P9 r s)
        (OrderTwentyFiveRelationZeroCertificate.Internal.B r s)
        (OrderTwentyFiveRelationZeroCertificate.Internal.D r s)
        (OrderTwentyFiveRelationZeroCertificate.Internal.E r s)
        (OrderTwentyFiveRelationZeroCertificate.Internal.T r s) := by
  rcases eval_sharedPowerData r s with
    ⟨hX, hX2, hX3, hX4, hU, hU2, hU3, hU4,
      hV, hV2, hV3, hV4, hB2, hB3, hB4, hB5,
      hD2, hD3, hD4, hD5, hD6, hD7, hD8,
      hE2, hE3, hE4, hE5, hT2, hT3, hT4, hT5⟩
  simp only [assemblyData, eval_sum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, eval_scaledProduct, List.prod_cons,
    List.prod_nil, mul_one, add_zero]
  rw [hX4, hX3, hX2, hX, hU4, hU3, hU2, hU,
    hV4, hV3, hV2, hV, hB5, hB4, hB3, hB2,
    hD8, hD7, hD6, hD5, hD4, hD3, hD2,
    hE5, hE4, hE3, hE2, hT5, hT4, hT3, hT2,
    eval_BData, eval_DData, eval_EData, eval_TData]
  simp only [compactNumerator]
  ring

/-- Evaluation of the checked shared-power assembly is the scalar reduced
numerator used by the final cleared-factor bridge. -/
theorem eval_assemblyData_eq_reducedNumerator (r s : ℚ) :
    Two.eval assemblyData r s = reducedNumerator r s := by
  rw [eval_assemblyData_eq_compact]
  rfl

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
