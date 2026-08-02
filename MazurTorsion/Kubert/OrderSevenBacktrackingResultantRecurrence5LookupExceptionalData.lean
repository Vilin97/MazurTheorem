/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.Ring

/-!
# Recurrence 5 lookup certificate: exceptional polynomial data

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence5ExceptionalNormalizedBlock0 : Coefficient :=
  coefficientTerm 2 (
    (1 : ℚ)) +
  coefficientTerm 3 (
    (-165 : ℚ)) +
  coefficientTerm 4 (
    (-12857 : ℚ)) +
  coefficientTerm 5 (
    (-371666 : ℚ)) +
  coefficientTerm 6 (
    (-5596321 : ℚ)) +
  coefficientTerm 7 (
    (-43625367 : ℚ)) +
  coefficientTerm 8 (
    (-83007371 : ℚ))

def recurrence5ExceptionalNormalizedBlock1 : Coefficient :=
  coefficientTerm 9 (
    (1461586220 : ℚ)) +
  coefficientTerm 10 (
    (11693942234 : ℚ)) +
  coefficientTerm 11 (
    (9503828816 : ℚ)) +
  coefficientTerm 12 (
    (-245447424547 : ℚ)) +
  coefficientTerm 13 (
    (-770033174521 : ℚ)) +
  coefficientTerm 14 (
    (2904564913328 : ℚ)) +
  coefficientTerm 15 (
    (14370548777889 : ℚ)) +
  coefficientTerm 16 (
    (-29285183309310 : ℚ)) +
  coefficientTerm 17 (
    (-165270662414299 : ℚ))

def recurrence5ExceptionalNormalizedBlock2 : Coefficient :=
  coefficientTerm 18 (
    (330344346226122 : ℚ)) +
  coefficientTerm 19 (
    (1263901517563683 : ℚ)) +
  coefficientTerm 20 (
    (-3641041722168920 : ℚ)) +
  coefficientTerm 21 (
    (-4744288554171373 : ℚ)) +
  coefficientTerm 22 (
    (28679746662344416 : ℚ)) +
  coefficientTerm 23 (
    (-17807823205029481 : ℚ)) +
  coefficientTerm 24 (
    (-109135034667591369 : ℚ)) +
  coefficientTerm 25 (
    (281993125551433686 : ℚ)) +
  coefficientTerm 26 (
    (-154750981476043511 : ℚ))

def recurrence5ExceptionalNormalizedBlock3 : Coefficient :=
  coefficientTerm 27 (
    (-619630231440505233 : ℚ)) +
  coefficientTerm 28 (
    (1890962459384133543 : ℚ)) +
  coefficientTerm 29 (
    (-2963646575176748168 : ℚ)) +
  coefficientTerm 30 (
    (3195867244807578562 : ℚ)) +
  coefficientTerm 31 (
    (-2565301139226596192 : ℚ)) +
  coefficientTerm 32 (
    (1577124548959608153 : ℚ)) +
  coefficientTerm 33 (
    (-746018908790785361 : ℚ)) +
  coefficientTerm 34 (
    (266448996959334996 : ℚ)) +
  coefficientTerm 35 (
    (-67117380579095351 : ℚ))

def recurrence5ExceptionalNormalizedBlock4 : Coefficient :=
  coefficientTerm 36 (
    (8839460863068784 : ℚ)) +
  coefficientTerm 37 (
    (1314723494770327 : ℚ)) +
  coefficientTerm 38 (
    (-1164910419752001 : ℚ)) +
  coefficientTerm 39 (
    (385640015677332 : ℚ)) +
  coefficientTerm 40 (
    (-86401612502595 : ℚ)) +
  coefficientTerm 41 (
    (14504235379297 : ℚ)) +
  coefficientTerm 42 (
    (-1882452416113 : ℚ)) +
  coefficientTerm 43 (
    (190234335408 : ℚ)) +
  coefficientTerm 44 (
    (-14865856326 : ℚ))

def recurrence5ExceptionalNormalizedBlock5 : Coefficient :=
  coefficientTerm 45 (
    (880700012 : ℚ)) +
  coefficientTerm 46 (
    (-38109181 : ℚ)) +
  coefficientTerm 47 (
    (1124157 : ℚ)) +
  coefficientTerm 48 (
    (-19484 : ℚ)) +
  coefficientTerm 49 (
    (117 : ℚ)) +
  coefficientTerm 50 (
    (1 : ℚ))

def recurrence5ExceptionalNormalized : Coefficient :=
  recurrence5ExceptionalNormalizedBlock0 +
  recurrence5ExceptionalNormalizedBlock1 +
  recurrence5ExceptionalNormalizedBlock2 +
  recurrence5ExceptionalNormalizedBlock3 +
  recurrence5ExceptionalNormalizedBlock4 +
  recurrence5ExceptionalNormalizedBlock5

theorem exceptional5_eq_recurrence5ExceptionalNormalized :
    exceptional5 =
      exceptionalUnit5 * recurrence5ExceptionalNormalized := by
  unfold exceptional5 recurrence5ExceptionalNormalized
  unfold
    recurrence5ExceptionalNormalizedBlock0
    recurrence5ExceptionalNormalizedBlock1
    recurrence5ExceptionalNormalizedBlock2
    recurrence5ExceptionalNormalizedBlock3
    recurrence5ExceptionalNormalizedBlock4
    recurrence5ExceptionalNormalizedBlock5
  unfold discriminantFactor cmSix parameter
  simp only [coefficientTerm_eq_C_mul_X_pow]
  simp only [map_neg, map_ofNat, map_one]
  ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
