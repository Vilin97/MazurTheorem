/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialRowCertificate
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialSupport
import Mathlib.Data.List.GetD

/-!
# Support lemmas for raw numerator assembly rows

The row certificates compare only the genuine support of each row.  This
leaf turns those bounded coefficient equalities into equality after padding,
with every later coefficient discharged structurally as a list default.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
open OrderTwentyFiveDensePolynomialSupport
open OrderTwentyFiveRelationZeroCertificate.Dense

private theorem XData_innerSupport : HasInnerSupport 19 XData := by
  apply hasInnerSupport_of_check
  decide

private theorem X2Data_innerSupport : HasInnerSupport 37 X2Data := by
  apply hasInnerSupport_of_check
  decide

private theorem X3Data_innerSupport : HasInnerSupport 55 X3Data := by
  apply hasInnerSupport_of_check
  decide

private theorem X4Data_innerSupport : HasInnerSupport 73 X4Data := by
  apply hasInnerSupport_of_check
  decide

private theorem UData_innerSupport : HasInnerSupport 6 UData := by
  apply hasInnerSupport_of_check
  decide

private theorem U2Data_innerSupport : HasInnerSupport 11 U2Data := by
  apply hasInnerSupport_of_check
  decide

private theorem U3Data_innerSupport : HasInnerSupport 16 U3Data := by
  apply hasInnerSupport_of_check
  decide

private theorem U4Data_innerSupport : HasInnerSupport 21 U4Data := by
  apply hasInnerSupport_of_check
  decide

private theorem VData_innerSupport : HasInnerSupport 23 VData := by
  apply hasInnerSupport_of_check
  decide

private theorem V2Data_innerSupport : HasInnerSupport 45 V2Data := by
  apply hasInnerSupport_of_check
  decide

private theorem V3Data_innerSupport : HasInnerSupport 67 V3Data := by
  apply hasInnerSupport_of_check
  decide

private theorem V4Data_innerSupport : HasInnerSupport 89 V4Data := by
  apply hasInnerSupport_of_check
  decide

private theorem BData_innerSupport : HasInnerSupport 2 BData := by
  apply hasInnerSupport_of_check
  decide

private theorem B2Data_innerSupport : HasInnerSupport 3 B2Data := by
  apply hasInnerSupport_of_check
  decide

private theorem B3Data_innerSupport : HasInnerSupport 4 B3Data := by
  apply hasInnerSupport_of_check
  decide

private theorem B5Data_innerSupport : HasInnerSupport 6 B5Data := by
  apply hasInnerSupport_of_check
  decide

private theorem DData_innerSupport : HasInnerSupport 4 DData := by
  apply hasInnerSupport_of_check
  decide

private theorem D2Data_innerSupport : HasInnerSupport 7 D2Data := by
  apply hasInnerSupport_of_check
  decide

private theorem D3Data_innerSupport : HasInnerSupport 10 D3Data := by
  apply hasInnerSupport_of_check
  decide

private theorem D4Data_innerSupport : HasInnerSupport 13 D4Data := by
  apply hasInnerSupport_of_check
  decide

private theorem D5Data_innerSupport : HasInnerSupport 16 D5Data := by
  apply hasInnerSupport_of_check
  decide

private theorem D6Data_innerSupport : HasInnerSupport 19 D6Data := by
  apply hasInnerSupport_of_check
  decide

private theorem D7Data_innerSupport : HasInnerSupport 22 D7Data := by
  apply hasInnerSupport_of_check
  decide

private theorem D8Data_innerSupport : HasInnerSupport 25 D8Data := by
  apply hasInnerSupport_of_check
  decide

private theorem EData_innerSupport : HasInnerSupport 3 EData := by
  apply hasInnerSupport_of_check
  decide

private theorem E2Data_innerSupport : HasInnerSupport 5 E2Data := by
  apply hasInnerSupport_of_check
  decide

private theorem E3Data_innerSupport : HasInnerSupport 7 E3Data := by
  apply hasInnerSupport_of_check
  decide

private theorem E5Data_innerSupport : HasInnerSupport 11 E5Data := by
  apply hasInnerSupport_of_check
  decide

private theorem TData_innerSupport : HasInnerSupport 5 TData := by
  apply hasInnerSupport_of_check
  decide

private theorem T2Data_innerSupport : HasInnerSupport 9 T2Data := by
  apply hasInnerSupport_of_check
  decide

private theorem T3Data_innerSupport : HasInnerSupport 13 T3Data := by
  apply hasInnerSupport_of_check
  decide

private theorem T4Data_innerSupport : HasInnerSupport 17 T4Data := by
  apply hasInnerSupport_of_check
  decide

private theorem T5Data_innerSupport : HasInnerSupport 21 T5Data := by
  apply hasInnerSupport_of_check
  decide

private def structuralProduct : List Two → Two
  | [] => [[1]]
  | p :: ps => Two.mul p (structuralProduct ps)

private def structuralSum : List Two → Two
  | [] => []
  | p :: ps => Two.add p (structuralSum ps)

private def structuralScaledProduct (z : ℤ) (ps : List Two) : Two :=
  Two.mul [[z]] (structuralProduct ps)

private theorem assemblyData_eq_structural :
    assemblyData = structuralSum [
      structuralScaledProduct 1 [U4Data, T5Data, X2Data, V2Data],
      structuralScaledProduct 1
        [X3Data, U3Data, VData, B2Data, DData, E2Data, T5Data],
      structuralScaledProduct (-1)
        [X2Data, U3Data, V2Data, BData, D2Data, EData, T4Data],
      structuralScaledProduct (-3)
        [X3Data, U2Data, VData, B3Data, D3Data, E3Data, T4Data],
      structuralScaledProduct (-1)
        [X2Data, U2Data, V2Data, B2Data, D4Data, E2Data, T3Data],
      structuralScaledProduct 2
        [XData, U2Data, V3Data, BData, D5Data, EData, T2Data],
      structuralScaledProduct (-1)
        [X4Data, UData, B5Data, D4Data, E5Data, T4Data],
      structuralScaledProduct 4
        [X2Data, UData, V2Data, B3Data, D6Data, E3Data, T2Data],
      structuralScaledProduct 1
        [XData, UData, V3Data, B2Data, D7Data, E2Data, TData],
      structuralScaledProduct 1
        [UData, V4Data, BData, D8Data, EData],
      structuralScaledProduct 1
        [X3Data, VData, B5Data, D7Data, E5Data, T2Data]
    ] := by
  rfl

private theorem structuralOne_innerSupport (z : ℤ) :
    HasInnerSupport 1 [[z]] := by
  apply hasInnerSupport_of_check
  rfl

private theorem structuralScaledProduct_innerSupport (z : ℤ)
    (ps : List Two) (hps : HasInnerSupport 121 (structuralProduct ps)) :
    HasInnerSupport 121 (structuralScaledProduct z ps) := by
  exact hasInnerSupport_mul 1 121 [[z]] (structuralProduct ps)
    (structuralOne_innerSupport z) hps

private theorem structuralTermOne_innerSupport :
    HasInnerSupport 121
      (structuralScaledProduct 1 [U4Data, T5Data, X2Data, V2Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 21 101
  · exact U4Data_innerSupport
  · apply hasInnerSupport_mul 21 81
    · exact T5Data_innerSupport
    · apply hasInnerSupport_mul 37 45
      · exact X2Data_innerSupport
      · apply hasInnerSupport_mul 45 1
        · exact V2Data_innerSupport
        · exact structuralOne_innerSupport 1

private theorem structuralTermTwo_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct 1
      [X3Data, U3Data, VData, B2Data, DData, E2Data, T5Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 55 67
  · exact X3Data_innerSupport
  · apply hasInnerSupport_mul 16 52
    · exact U3Data_innerSupport
    · apply hasInnerSupport_mul 23 30
      · exact VData_innerSupport
      · apply hasInnerSupport_mul 3 28
        · exact B2Data_innerSupport
        · apply hasInnerSupport_mul 4 25
          · exact DData_innerSupport
          · apply hasInnerSupport_mul 5 21
            · exact E2Data_innerSupport
            · apply hasInnerSupport_mul 21 1
              · exact T5Data_innerSupport
              · exact structuralOne_innerSupport 1

private theorem structuralTermThree_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct (-1)
      [X2Data, U3Data, V2Data, BData, D2Data, EData, T4Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 37 85
  · exact X2Data_innerSupport
  · apply hasInnerSupport_mul 16 70
    · exact U3Data_innerSupport
    · apply hasInnerSupport_mul 45 26
      · exact V2Data_innerSupport
      · apply hasInnerSupport_mul 2 25
        · exact BData_innerSupport
        · apply hasInnerSupport_mul 7 19
          · exact D2Data_innerSupport
          · apply hasInnerSupport_mul 3 17
            · exact EData_innerSupport
            · apply hasInnerSupport_mul 17 1
              · exact T4Data_innerSupport
              · exact structuralOne_innerSupport 1

private theorem structuralTermFour_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct (-3)
      [X3Data, U2Data, VData, B3Data, D3Data, E3Data, T4Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 55 67
  · exact X3Data_innerSupport
  · apply hasInnerSupport_mul 11 57
    · exact U2Data_innerSupport
    · apply hasInnerSupport_mul 23 35
      · exact VData_innerSupport
      · apply hasInnerSupport_mul 4 32
        · exact B3Data_innerSupport
        · apply hasInnerSupport_mul 10 23
          · exact D3Data_innerSupport
          · apply hasInnerSupport_mul 7 17
            · exact E3Data_innerSupport
            · apply hasInnerSupport_mul 17 1
              · exact T4Data_innerSupport
              · exact structuralOne_innerSupport 1

private theorem structuralTermFive_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct (-1)
      [X2Data, U2Data, V2Data, B2Data, D4Data, E2Data, T3Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 37 85
  · exact X2Data_innerSupport
  · apply hasInnerSupport_mul 11 75
    · exact U2Data_innerSupport
    · apply hasInnerSupport_mul 45 31
      · exact V2Data_innerSupport
      · apply hasInnerSupport_mul 3 29
        · exact B2Data_innerSupport
        · apply hasInnerSupport_mul 13 17
          · exact D4Data_innerSupport
          · apply hasInnerSupport_mul 5 13
            · exact E2Data_innerSupport
            · apply hasInnerSupport_mul 13 1
              · exact T3Data_innerSupport
              · exact structuralOne_innerSupport 1

private theorem structuralTermSix_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct 2
      [XData, U2Data, V3Data, BData, D5Data, EData, T2Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 19 103
  · exact XData_innerSupport
  · apply hasInnerSupport_mul 11 93
    · exact U2Data_innerSupport
    · apply hasInnerSupport_mul 67 27
      · exact V3Data_innerSupport
      · apply hasInnerSupport_mul 2 26
        · exact BData_innerSupport
        · apply hasInnerSupport_mul 16 11
          · exact D5Data_innerSupport
          · apply hasInnerSupport_mul 3 9
            · exact EData_innerSupport
            · apply hasInnerSupport_mul 9 1
              · exact T2Data_innerSupport
              · exact structuralOne_innerSupport 1

private theorem structuralTermSeven_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct (-1)
      [X4Data, UData, B5Data, D4Data, E5Data, T4Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 73 49
  · exact X4Data_innerSupport
  · apply hasInnerSupport_mul 6 44
    · exact UData_innerSupport
    · apply hasInnerSupport_mul 6 39
      · exact B5Data_innerSupport
      · apply hasInnerSupport_mul 13 27
        · exact D4Data_innerSupport
        · apply hasInnerSupport_mul 11 17
          · exact E5Data_innerSupport
          · apply hasInnerSupport_mul 17 1
            · exact T4Data_innerSupport
            · exact structuralOne_innerSupport 1

private theorem structuralTermEight_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct 4
      [X2Data, UData, V2Data, B3Data, D6Data, E3Data, T2Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 37 85
  · exact X2Data_innerSupport
  · apply hasInnerSupport_mul 6 80
    · exact UData_innerSupport
    · apply hasInnerSupport_mul 45 36
      · exact V2Data_innerSupport
      · apply hasInnerSupport_mul 4 33
        · exact B3Data_innerSupport
        · apply hasInnerSupport_mul 19 15
          · exact D6Data_innerSupport
          · apply hasInnerSupport_mul 7 9
            · exact E3Data_innerSupport
            · apply hasInnerSupport_mul 9 1
              · exact T2Data_innerSupport
              · exact structuralOne_innerSupport 1

private theorem structuralTermNine_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct 1
      [XData, UData, V3Data, B2Data, D7Data, E2Data, TData]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 19 103
  · exact XData_innerSupport
  · apply hasInnerSupport_mul 6 98
    · exact UData_innerSupport
    · apply hasInnerSupport_mul 67 32
      · exact V3Data_innerSupport
      · apply hasInnerSupport_mul 3 30
        · exact B2Data_innerSupport
        · apply hasInnerSupport_mul 22 9
          · exact D7Data_innerSupport
          · apply hasInnerSupport_mul 5 5
            · exact E2Data_innerSupport
            · apply hasInnerSupport_mul 5 1
              · exact TData_innerSupport
              · exact structuralOne_innerSupport 1

private theorem structuralTermTen_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct 1
      [UData, V4Data, BData, D8Data, EData]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 6 116
  · exact UData_innerSupport
  · apply hasInnerSupport_mul 89 28
    · exact V4Data_innerSupport
    · apply hasInnerSupport_mul 2 27
      · exact BData_innerSupport
      · apply hasInnerSupport_mul 25 3
        · exact D8Data_innerSupport
        · apply hasInnerSupport_mul 3 1
          · exact EData_innerSupport
          · exact structuralOne_innerSupport 1

private theorem structuralTermEleven_innerSupport :
    HasInnerSupport 121 (structuralScaledProduct 1
      [X3Data, VData, B5Data, D7Data, E5Data, T2Data]) := by
  apply structuralScaledProduct_innerSupport
  simp only [structuralProduct]
  apply hasInnerSupport_mul 55 67
  · exact X3Data_innerSupport
  · apply hasInnerSupport_mul 23 45
    · exact VData_innerSupport
    · apply hasInnerSupport_mul 6 40
      · exact B5Data_innerSupport
      · apply hasInnerSupport_mul 22 19
        · exact D7Data_innerSupport
        · apply hasInnerSupport_mul 11 9
          · exact E5Data_innerSupport
          · apply hasInnerSupport_mul 9 1
            · exact T2Data_innerSupport
            · exact structuralOne_innerSupport 1

/-- Every row of the raw eleven-term assembly has structural width at most
121, independently of its coefficient values. -/
theorem assemblyData_innerSupport : HasInnerSupport 121 assemblyData := by
  rw [assemblyData_eq_structural]
  simp only [structuralSum]
  apply hasInnerSupport_add 121
  · exact structuralTermOne_innerSupport
  · apply hasInnerSupport_add 121
    · exact structuralTermTwo_innerSupport
    · apply hasInnerSupport_add 121
      · exact structuralTermThree_innerSupport
      · apply hasInnerSupport_add 121
        · exact structuralTermFour_innerSupport
        · apply hasInnerSupport_add 121
          · exact structuralTermFive_innerSupport
          · apply hasInnerSupport_add 121
            · exact structuralTermSix_innerSupport
            · apply hasInnerSupport_add 121
              · exact structuralTermSeven_innerSupport
              · apply hasInnerSupport_add 121
                · exact structuralTermEight_innerSupport
                · apply hasInnerSupport_add 121
                  · exact structuralTermNine_innerSupport
                  · apply hasInnerSupport_add 121
                    · exact structuralTermTen_innerSupport
                    · apply hasInnerSupport_add 121
                      · exact structuralTermEleven_innerSupport
                      · exact fun _ h => by simp at h

/-- Every selected row of the raw assembly inherits the global 121-column
support bound. -/
theorem assemblyData_row_length_le (i : ℕ) :
    (assemblyData.getD i []).length ≤ 121 :=
  getD_length_le assemblyData_innerSupport i

/-- Exact outer support of the dense eleven-term assembly. -/
theorem assemblyData_outerSupport : assemblyData.length = 83 := by
  decide

/-- Two rows with a common support bound and equal supported coefficients
remain equal after padding to any larger width. -/
theorem padOne_eq_of_bounded_coefficients
    (inner support : ℕ) (p q : One)
    (hp : p.length ≤ support) (hq : q.length ≤ support)
    (hsi : support ≤ inner)
    (hc : ∀ j, j < support → p.getD j 0 = q.getD j 0) :
    padOne inner p = padOne inner q := by
  apply padOne_eq_of_coefficients inner p (padOne inner q)
    (hp.trans hsi)
  · simp only [padOne, List.length_append, List.length_replicate]
    omega
  · intro j hj
    rw [getD_padOne inner q j hj]
    by_cases hjs : j < support
    · exact hc j hjs
    · rw [List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
