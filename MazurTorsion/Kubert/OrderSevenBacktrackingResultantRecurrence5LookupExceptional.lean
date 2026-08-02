/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupExceptionalData
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: exceptional coefficient lookup

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5Exceptional_coeff_0 :
    exceptional5.coeff 0 =
      (0 : ℚ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_1 :
    exceptional5.coeff 1 =
      (0 : ℚ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_2 :
    exceptional5.coeff 2 =
      (
        (1) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_3 :
    exceptional5.coeff 3 =
      (
        (-33) /
        (39988901703835833774702822118890342577443381752832020 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_4 :
    exceptional5.coeff 4 =
      (
        (-12857) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_5 :
    exceptional5.coeff 5 =
      (
        (-185833) /
        (99972254259589584436757055297225856443608454382080050 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_6 :
    exceptional5.coeff 6 =
      (
        (-5596321) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_7 :
    exceptional5.coeff 7 =
      (
        (-43625367) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_8 :
    exceptional5.coeff 8 =
      (
        (-83007371) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_9 :
    exceptional5.coeff 9 =
      (
        (73079311) /
        (9997225425958958443675705529722585644360845438208005 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_10 :
    exceptional5.coeff 10 =
      (
        (5846971117) /
        (99972254259589584436757055297225856443608454382080050 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_11 :
    exceptional5.coeff 11 =
      (
        (2375957204) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_12 :
    exceptional5.coeff 12 =
      (
        (-245447424547) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_13 :
    exceptional5.coeff 13 =
      (
        (-770033174521) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_14 :
    exceptional5.coeff 14 =
      (
        (726141228332) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_15 :
    exceptional5.coeff 15 =
      (
        (14370548777889) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_16 :
    exceptional5.coeff 16 =
      (
        (-2928518330931) /
        (19994450851917916887351411059445171288721690876416010 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_17 :
    exceptional5.coeff 17 =
      (
        (-165270662414299) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_18 :
    exceptional5.coeff 18 =
      (
        (165172173113061) /
        (99972254259589584436757055297225856443608454382080050 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_19 :
    exceptional5.coeff 19 =
      (
        (1263901517563683) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_20 :
    exceptional5.coeff 20 =
      (
        (-182052086108446) /
        (9997225425958958443675705529722585644360845438208005 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_21 :
    exceptional5.coeff 21 =
      (
        (-4744288554171373) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_22 :
    exceptional5.coeff 22 =
      (
        (7169936665586104) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_23 :
    exceptional5.coeff 23 =
      (
        (-17807823205029481) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_24 :
    exceptional5.coeff 24 =
      (
        (-109135034667591369) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_25 :
    exceptional5.coeff 25 =
      (
        (140996562775716843) /
        (99972254259589584436757055297225856443608454382080050 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_26 :
    exceptional5.coeff 26 =
      (
        (-154750981476043511) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_27 :
    exceptional5.coeff 27 =
      (
        (-619630231440505233) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_28 :
    exceptional5.coeff 28 =
      (
        (1890962459384133543) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_29 :
    exceptional5.coeff 29 =
      (
        (-740911643794187042) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_30 :
    exceptional5.coeff 30 =
      (
        (43187395200102413) /
        (2701952817826745525317758251276374498475904172488650 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_31 :
    exceptional5.coeff 31 =
      (
        (-641325284806649048) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_32 :
    exceptional5.coeff 32 =
      (
        (1577124548959608153) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_33 :
    exceptional5.coeff 33 =
      (
        (-746018908790785361) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_34 :
    exceptional5.coeff 34 =
      (
        (66612249239833749) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_35 :
    exceptional5.coeff 35 =
      (
        (-67117380579095351) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_36 :
    exceptional5.coeff 36 =
      (
        (2209865215767196) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_37 :
    exceptional5.coeff 37 =
      (
        (1314723494770327) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_38 :
    exceptional5.coeff 38 =
      (
        (-1164910419752001) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_39 :
    exceptional5.coeff 39 =
      (
        (96410003919333) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_40 :
    exceptional5.coeff 40 =
      (
        (-17280322500519) /
        (39988901703835833774702822118890342577443381752832020 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_41 :
    exceptional5.coeff 41 =
      (
        (14504235379297) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_42 :
    exceptional5.coeff 42 =
      (
        (-1882452416113) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_43 :
    exceptional5.coeff 43 =
      (
        (47558583852) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_44 :
    exceptional5.coeff 44 =
      (
        (-7432928163) /
        (99972254259589584436757055297225856443608454382080050 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_45 :
    exceptional5.coeff 45 =
      (
        (220175003) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_46 :
    exceptional5.coeff 46 =
      (
        (-38109181) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_47 :
    exceptional5.coeff 47 =
      (
        (1124157) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_48 :
    exceptional5.coeff 48 =
      (
        (-4871) /
        (49986127129794792218378527648612928221804227191040025 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_49 :
    exceptional5.coeff 49 =
      (
        (117) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5Exceptional_coeff_50 :
    exceptional5.coeff 50 =
      (
        (1) /
        (199944508519179168873514110594451712887216908764160100 : ℚ)
      ) := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  unfold recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold coefficientTerm
  norm_num [Polynomial.coeff_monomial]

private theorem recurrence5ExceptionalNormalizedBlock0_coeff_high (n : ℕ) (h : 50 < n) :
    recurrence5ExceptionalNormalizedBlock0.coeff n = 0 := by
  unfold recurrence5ExceptionalNormalizedBlock0 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5ExceptionalNormalizedBlock1_coeff_high (n : ℕ) (h : 50 < n) :
    recurrence5ExceptionalNormalizedBlock1.coeff n = 0 := by
  unfold recurrence5ExceptionalNormalizedBlock1 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5ExceptionalNormalizedBlock2_coeff_high (n : ℕ) (h : 50 < n) :
    recurrence5ExceptionalNormalizedBlock2.coeff n = 0 := by
  unfold recurrence5ExceptionalNormalizedBlock2 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5ExceptionalNormalizedBlock3_coeff_high (n : ℕ) (h : 50 < n) :
    recurrence5ExceptionalNormalizedBlock3.coeff n = 0 := by
  unfold recurrence5ExceptionalNormalizedBlock3 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5ExceptionalNormalizedBlock4_coeff_high (n : ℕ) (h : 50 < n) :
    recurrence5ExceptionalNormalizedBlock4.coeff n = 0 := by
  unfold recurrence5ExceptionalNormalizedBlock4 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5ExceptionalNormalizedBlock5_coeff_high (n : ℕ) (h : 50 < n) :
    recurrence5ExceptionalNormalizedBlock5.coeff n = 0 := by
  unfold recurrence5ExceptionalNormalizedBlock5 coefficientTerm
  simp only [Polynomial.coeff_add, Polynomial.coeff_monomial]
  split_ifs <;> norm_num <;> omega

private theorem recurrence5ExceptionalNormalized_coeff_high
    (n : ℕ) (h : 50 < n) :
    recurrence5ExceptionalNormalized.coeff n = 0 := by
  unfold recurrence5ExceptionalNormalized
  simp only [Polynomial.coeff_add]
  rw [recurrence5ExceptionalNormalizedBlock0_coeff_high n h]
  rw [recurrence5ExceptionalNormalizedBlock1_coeff_high n h]
  rw [recurrence5ExceptionalNormalizedBlock2_coeff_high n h]
  rw [recurrence5ExceptionalNormalizedBlock3_coeff_high n h]
  rw [recurrence5ExceptionalNormalizedBlock4_coeff_high n h]
  rw [recurrence5ExceptionalNormalizedBlock5_coeff_high n h]
  norm_num

theorem recurrence5Exceptional_coeff_high
    (n : ℕ) (h : 50 < n) : exceptional5.coeff n = 0 := by
  rw [exceptional5_eq_recurrence5ExceptionalNormalized]
  unfold exceptionalUnit5
  rw [Polynomial.coeff_C_mul]
  rw [recurrence5ExceptionalNormalized_coeff_high n h]
  norm_num

theorem recurrence5Exceptional_natDegree_le :
    exceptional5.natDegree ≤ 50 := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    recurrence5Exceptional_coeff_high

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
