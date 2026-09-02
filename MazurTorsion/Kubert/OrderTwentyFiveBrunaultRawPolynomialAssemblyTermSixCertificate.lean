/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultRawPolynomialAssemblyTermSixData
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialMulCertificate
import MazurTorsion.Kubert.OrderTwentyFiveDensePolynomialSupport
import Mathlib.Tactic.IntervalCases

/-!
# Checked staged assembly of the sixth reduced-numerator term

The right-associated products are cached in generated dense tables.  Each
stage is checked in the Lean kernel before later stages consume it.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal

open OrderTwentyFiveDensePolynomial
open OrderTwentyFiveDensePolynomialRectangular
open OrderTwentyFiveDensePolynomialRowCertificate
open OrderTwentyFiveDensePolynomialMulCertificate
open OrderTwentyFiveRelationZeroCertificate.Dense

theorem term6Stage1_spec :
    rectangularize 7 11 (Two.mul EData T2Data) =
      rectangularize 7 11 Term6Stage1Data := by
  decide

theorem term6Stage2_spec :
    rectangularize 17 26 (Two.mul D5Data Term6Stage1Data) =
      rectangularize 17 26 Term6Stage2Data := by
  decide

theorem term6Stage3_spec :
    rectangularize 17 27 (Two.mul BData Term6Stage2Data) =
      rectangularize 17 27 Term6Stage3Data := by
  decide

private theorem term6Stage4Row0_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 0) =
      (rectangularize 62 93 Term6Stage4Data).getD 0 [] := by
  decide

private theorem term6Stage4Row1_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 1) =
      (rectangularize 62 93 Term6Stage4Data).getD 1 [] := by
  decide

private theorem term6Stage4Row2_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 2) =
      (rectangularize 62 93 Term6Stage4Data).getD 2 [] := by
  decide

private theorem term6Stage4Row3_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 3) =
      (rectangularize 62 93 Term6Stage4Data).getD 3 [] := by
  decide

private theorem term6Stage4Row4_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 4) =
      (rectangularize 62 93 Term6Stage4Data).getD 4 [] := by
  decide

private theorem term6Stage4Row5_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 5) =
      (rectangularize 62 93 Term6Stage4Data).getD 5 [] := by
  decide

private theorem term6Stage4Row6_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 6) =
      (rectangularize 62 93 Term6Stage4Data).getD 6 [] := by
  decide

private theorem term6Stage4Row7_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 7) =
      (rectangularize 62 93 Term6Stage4Data).getD 7 [] := by
  decide

private theorem term6Stage4Row8_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 8) =
      (rectangularize 62 93 Term6Stage4Data).getD 8 [] := by
  decide

private theorem term6Stage4Row9_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 9) =
      (rectangularize 62 93 Term6Stage4Data).getD 9 [] := by
  decide

private theorem term6Stage4Row10_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 10) =
      (rectangularize 62 93 Term6Stage4Data).getD 10 [] := by
  decide

private theorem term6Stage4Row11_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 11) =
      (rectangularize 62 93 Term6Stage4Data).getD 11 [] := by
  decide

private theorem term6Stage4Row12_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 12) =
      (rectangularize 62 93 Term6Stage4Data).getD 12 [] := by
  decide

private theorem term6Stage4Row13_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 13) =
      (rectangularize 62 93 Term6Stage4Data).getD 13 [] := by
  decide

private theorem term6Stage4Row14_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 14) =
      (rectangularize 62 93 Term6Stage4Data).getD 14 [] := by
  decide

private theorem term6Stage4Row15_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 15) =
      (rectangularize 62 93 Term6Stage4Data).getD 15 [] := by
  decide

private theorem term6Stage4Row16_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 16) =
      (rectangularize 62 93 Term6Stage4Data).getD 16 [] := by
  decide

private theorem term6Stage4Row17_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 17) =
      (rectangularize 62 93 Term6Stage4Data).getD 17 [] := by
  decide

private theorem term6Stage4Row18_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 18) =
      (rectangularize 62 93 Term6Stage4Data).getD 18 [] := by
  decide

private theorem term6Stage4Row19_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 19) =
      (rectangularize 62 93 Term6Stage4Data).getD 19 [] := by
  decide

private theorem term6Stage4Row20_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 20) =
      (rectangularize 62 93 Term6Stage4Data).getD 20 [] := by
  decide

private theorem term6Stage4Row21_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 21) =
      (rectangularize 62 93 Term6Stage4Data).getD 21 [] := by
  decide

private theorem term6Stage4Row22_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 22) =
      (rectangularize 62 93 Term6Stage4Data).getD 22 [] := by
  decide

private theorem term6Stage4Row23_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 23) =
      (rectangularize 62 93 Term6Stage4Data).getD 23 [] := by
  decide

private theorem term6Stage4Row24_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 24) =
      (rectangularize 62 93 Term6Stage4Data).getD 24 [] := by
  decide

private theorem term6Stage4Row25_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 25) =
      (rectangularize 62 93 Term6Stage4Data).getD 25 [] := by
  decide

private theorem term6Stage4Row26_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 26) =
      (rectangularize 62 93 Term6Stage4Data).getD 26 [] := by
  decide

private theorem term6Stage4Row27_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 27) =
      (rectangularize 62 93 Term6Stage4Data).getD 27 [] := by
  decide

private theorem term6Stage4Row28_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 28) =
      (rectangularize 62 93 Term6Stage4Data).getD 28 [] := by
  decide

private theorem term6Stage4Row29_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 29) =
      (rectangularize 62 93 Term6Stage4Data).getD 29 [] := by
  decide

private theorem term6Stage4Row30_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 30) =
      (rectangularize 62 93 Term6Stage4Data).getD 30 [] := by
  decide

private theorem term6Stage4Row31_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 31) =
      (rectangularize 62 93 Term6Stage4Data).getD 31 [] := by
  decide

private theorem term6Stage4Row32_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 32) =
      (rectangularize 62 93 Term6Stage4Data).getD 32 [] := by
  decide

private theorem term6Stage4Row33_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 33) =
      (rectangularize 62 93 Term6Stage4Data).getD 33 [] := by
  decide

private theorem term6Stage4Row34_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 34) =
      (rectangularize 62 93 Term6Stage4Data).getD 34 [] := by
  decide

private theorem term6Stage4Row35_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 35) =
      (rectangularize 62 93 Term6Stage4Data).getD 35 [] := by
  decide

private theorem term6Stage4Row36_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 36) =
      (rectangularize 62 93 Term6Stage4Data).getD 36 [] := by
  decide

private theorem term6Stage4Row37_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 37) =
      (rectangularize 62 93 Term6Stage4Data).getD 37 [] := by
  decide

private theorem term6Stage4Row38_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 38) =
      (rectangularize 62 93 Term6Stage4Data).getD 38 [] := by
  decide

private theorem term6Stage4Row39_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 39) =
      (rectangularize 62 93 Term6Stage4Data).getD 39 [] := by
  decide

private theorem term6Stage4Row40_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 40) =
      (rectangularize 62 93 Term6Stage4Data).getD 40 [] := by
  decide

private theorem term6Stage4Row41_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 41) =
      (rectangularize 62 93 Term6Stage4Data).getD 41 [] := by
  decide

private theorem term6Stage4Row42_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 42) =
      (rectangularize 62 93 Term6Stage4Data).getD 42 [] := by
  decide

private theorem term6Stage4Row43_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 43) =
      (rectangularize 62 93 Term6Stage4Data).getD 43 [] := by
  decide

private theorem term6Stage4Row44_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 44) =
      (rectangularize 62 93 Term6Stage4Data).getD 44 [] := by
  decide

private theorem term6Stage4Row45_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 45) =
      (rectangularize 62 93 Term6Stage4Data).getD 45 [] := by
  decide

private theorem term6Stage4Row46_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 46) =
      (rectangularize 62 93 Term6Stage4Data).getD 46 [] := by
  decide

private theorem term6Stage4Row47_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 47) =
      (rectangularize 62 93 Term6Stage4Data).getD 47 [] := by
  decide

private theorem term6Stage4Row48_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 48) =
      (rectangularize 62 93 Term6Stage4Data).getD 48 [] := by
  decide

private theorem term6Stage4Row49_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 49) =
      (rectangularize 62 93 Term6Stage4Data).getD 49 [] := by
  decide

private theorem term6Stage4Row50_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 50) =
      (rectangularize 62 93 Term6Stage4Data).getD 50 [] := by
  decide

private theorem term6Stage4Row51_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 51) =
      (rectangularize 62 93 Term6Stage4Data).getD 51 [] := by
  decide

private theorem term6Stage4Row52_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 52) =
      (rectangularize 62 93 Term6Stage4Data).getD 52 [] := by
  decide

private theorem term6Stage4Row53_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 53) =
      (rectangularize 62 93 Term6Stage4Data).getD 53 [] := by
  decide

private theorem term6Stage4Row54_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 54) =
      (rectangularize 62 93 Term6Stage4Data).getD 54 [] := by
  decide

private theorem term6Stage4Row55_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 55) =
      (rectangularize 62 93 Term6Stage4Data).getD 55 [] := by
  decide

private theorem term6Stage4Row56_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 56) =
      (rectangularize 62 93 Term6Stage4Data).getD 56 [] := by
  decide

private theorem term6Stage4Row57_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 57) =
      (rectangularize 62 93 Term6Stage4Data).getD 57 [] := by
  decide

private theorem term6Stage4Row58_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 58) =
      (rectangularize 62 93 Term6Stage4Data).getD 58 [] := by
  decide

private theorem term6Stage4Row59_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 59) =
      (rectangularize 62 93 Term6Stage4Data).getD 59 [] := by
  decide

private theorem term6Stage4Row60_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 60) =
      (rectangularize 62 93 Term6Stage4Data).getD 60 [] := by
  decide

private theorem term6Stage4Row61_spec :
    padOne 93 (mulRow V3Data Term6Stage3Data 61) =
      (rectangularize 62 93 Term6Stage4Data).getD 61 [] := by
  decide

private theorem term6Stage4_rows (n : ℕ) (hn : n < 62) :
    padOne 93 (mulRow V3Data Term6Stage3Data n) =
      (rectangularize 62 93 Term6Stage4Data).getD n [] := by
  interval_cases n
  · exact term6Stage4Row0_spec
  · exact term6Stage4Row1_spec
  · exact term6Stage4Row2_spec
  · exact term6Stage4Row3_spec
  · exact term6Stage4Row4_spec
  · exact term6Stage4Row5_spec
  · exact term6Stage4Row6_spec
  · exact term6Stage4Row7_spec
  · exact term6Stage4Row8_spec
  · exact term6Stage4Row9_spec
  · exact term6Stage4Row10_spec
  · exact term6Stage4Row11_spec
  · exact term6Stage4Row12_spec
  · exact term6Stage4Row13_spec
  · exact term6Stage4Row14_spec
  · exact term6Stage4Row15_spec
  · exact term6Stage4Row16_spec
  · exact term6Stage4Row17_spec
  · exact term6Stage4Row18_spec
  · exact term6Stage4Row19_spec
  · exact term6Stage4Row20_spec
  · exact term6Stage4Row21_spec
  · exact term6Stage4Row22_spec
  · exact term6Stage4Row23_spec
  · exact term6Stage4Row24_spec
  · exact term6Stage4Row25_spec
  · exact term6Stage4Row26_spec
  · exact term6Stage4Row27_spec
  · exact term6Stage4Row28_spec
  · exact term6Stage4Row29_spec
  · exact term6Stage4Row30_spec
  · exact term6Stage4Row31_spec
  · exact term6Stage4Row32_spec
  · exact term6Stage4Row33_spec
  · exact term6Stage4Row34_spec
  · exact term6Stage4Row35_spec
  · exact term6Stage4Row36_spec
  · exact term6Stage4Row37_spec
  · exact term6Stage4Row38_spec
  · exact term6Stage4Row39_spec
  · exact term6Stage4Row40_spec
  · exact term6Stage4Row41_spec
  · exact term6Stage4Row42_spec
  · exact term6Stage4Row43_spec
  · exact term6Stage4Row44_spec
  · exact term6Stage4Row45_spec
  · exact term6Stage4Row46_spec
  · exact term6Stage4Row47_spec
  · exact term6Stage4Row48_spec
  · exact term6Stage4Row49_spec
  · exact term6Stage4Row50_spec
  · exact term6Stage4Row51_spec
  · exact term6Stage4Row52_spec
  · exact term6Stage4Row53_spec
  · exact term6Stage4Row54_spec
  · exact term6Stage4Row55_spec
  · exact term6Stage4Row56_spec
  · exact term6Stage4Row57_spec
  · exact term6Stage4Row58_spec
  · exact term6Stage4Row59_spec
  · exact term6Stage4Row60_spec
  · exact term6Stage4Row61_spec

theorem term6Stage4_spec :
    rectangularize 62 93 (Two.mul V3Data Term6Stage3Data) =
      rectangularize 62 93 Term6Stage4Data := by
  exact rectangularize_mul_eq_of_rows 62 93 V3Data Term6Stage3Data
    Term6Stage4Data (by decide) (by decide) term6Stage4_rows

theorem eval_term6Stage4Data_eq (r s : ℚ) :
    Two.eval Term6Stage4Data r s =
      Two.eval V3Data r s * Two.eval Term6Stage3Data r s := by
  exact eval_mulData_eq_mul_of_rows 62 93 V3Data Term6Stage3Data
    Term6Stage4Data (by decide) (by decide) term6Stage4_rows r s

end MazurTorsion.Kubert.OrderTwentyFiveRawPolynomialCertificate.Internal
