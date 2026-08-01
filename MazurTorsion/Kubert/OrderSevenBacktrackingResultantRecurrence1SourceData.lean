/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData1

import Mathlib.Tactic.Ring

/-!
# Recurrence 1 certificate: SourceData

This file is a checked bounded-band arithmetic shard for the first
pseudo-division recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

def recurrence1Source0Block0 : Coefficient :=
  X ^ 0 * (
    (1) * X ^ 3 +
    (-77) * X ^ 4 +
    (-1181) * X ^ 5 +
    (741) * X ^ 6 +
    (95279) * X ^ 7 +
    (-772464) * X ^ 8
  )

def recurrence1Source0Block1 : Coefficient :=
  X ^ 9 * (
    (3222128) +
    (-8636434) * X ^ 1 +
    (15939042) * X ^ 2 +
    (-20695126) * X ^ 3 +
    (18939622) * X ^ 4 +
    (-12491384) * X ^ 5 +
    (7213570) * X ^ 6 +
    (-5733840) * X ^ 7 +
    (5624303) * X ^ 8
  )

def recurrence1Source0Block2 : Coefficient :=
  X ^ 18 * (
    (-4405352) +
    (2405086) * X ^ 1 +
    (-886465) * X ^ 2 +
    (206818) * X ^ 3 +
    (-24787) * X ^ 4 +
    (637) * X ^ 5 +
    (-209) * X ^ 6 +
    (98) * X ^ 7 +
    (-5) * X ^ 8
  )

def recurrence1Source0Block3 : Coefficient :=
  X ^ 27 * (
    (-1)
  )

def recurrence1Source0 : Coefficient :=
  recurrence1Source0Block0 +
  recurrence1Source0Block1 +
  recurrence1Source0Block2 +
  recurrence1Source0Block3

def recurrence1Source1Block0 : Coefficient :=
  X ^ 0 * (
    (21) * X ^ 3 +
    (406) * X ^ 4 +
    (1589) * X ^ 5 +
    (-93457) * X ^ 6 +
    (708841) * X ^ 7 +
    (-2769417) * X ^ 8
  )

def recurrence1Source1Block1 : Coefficient :=
  X ^ 9 * (
    (6825462) +
    (-11412394) * X ^ 1 +
    (13386751) * X ^ 2 +
    (-11239305) * X ^ 3 +
    (6871774) * X ^ 4 +
    (-3086608) * X ^ 5 +
    (940373) * X ^ 6 +
    (-65296) * X ^ 7 +
    (-125181) * X ^ 8
  )

def recurrence1Source1Block2 : Coefficient :=
  X ^ 18 * (
    (67522) +
    (-8743) * X ^ 1 +
    (-3269) * X ^ 2 +
    (959) * X ^ 3 +
    (-14) * X ^ 4 +
    (-14) * X ^ 5
  )

def recurrence1Source1 : Coefficient :=
  recurrence1Source1Block0 +
  recurrence1Source1Block1 +
  recurrence1Source1Block2

def recurrence1Source2Block0 : Coefficient :=
  X ^ 0 * (
    (-91) * X ^ 3 +
    (-2331) * X ^ 4 +
    (38542) * X ^ 5 +
    (-250488) * X ^ 6 +
    (878003) * X ^ 7 +
    (-1917251) * X ^ 8
  )

def recurrence1Source2Block1 : Coefficient :=
  X ^ 9 * (
    (2824976) +
    (-2915535) * X ^ 1 +
    (2121469) * X ^ 2 +
    (-1083838) * X ^ 3 +
    (410326) * X ^ 4 +
    (-149079) * X ^ 5 +
    (62594) * X ^ 6 +
    (-20265) * X ^ 7 +
    (2884) * X ^ 8
  )

def recurrence1Source2Block2 : Coefficient :=
  X ^ 18 * (
    (161) +
    (-77) * X ^ 1
  )

def recurrence1Source2 : Coefficient :=
  recurrence1Source2Block0 +
  recurrence1Source2Block1 +
  recurrence1Source2Block2

def recurrence1Source3Block0 : Coefficient :=
  X ^ 0 * (
    (14) * X ^ 2 +
    (728) * X ^ 3 +
    (-8477) * X ^ 4 +
    (39032) * X ^ 5 +
    (-108654) * X ^ 6 +
    (198100) * X ^ 7 +
    (-242060) * X ^ 8
  )

def recurrence1Source3Block1 : Coefficient :=
  X ^ 9 * (
    (204596) +
    (-124124) * X ^ 1 +
    (53942) * X ^ 2 +
    (-14567) * X ^ 3 +
    (812) * X ^ 4 +
    (868) * X ^ 5 +
    (-210) * X ^ 6
  )

def recurrence1Source3 : Coefficient :=
  recurrence1Source3Block0 +
  recurrence1Source3Block1

def recurrence1Source4Block0 : Coefficient :=
  X ^ 0 * (
    (-98) * X ^ 2 +
    (707) * X ^ 3 +
    (-1372) * X ^ 4 +
    (-322) * X ^ 5 +
    (2912) * X ^ 6 +
    (-2450) * X ^ 7 +
    (1442) * X ^ 8
  )

def recurrence1Source4Block1 : Coefficient :=
  X ^ 9 * (
    (-1799) +
    (1274) * X ^ 1 +
    (-294) * X ^ 2
  )

def recurrence1Source4 : Coefficient :=
  recurrence1Source4Block0 +
  recurrence1Source4Block1

def recurrence1Source5Block0 : Coefficient :=
  X ^ 0 * (
    (7) * X ^ 1 +
    (56) * X ^ 2 +
    (-406) * X ^ 3 +
    (994) * X ^ 4 +
    (-1239) * X ^ 5 +
    (791) * X ^ 6 +
    (-203) * X ^ 7
  )

def recurrence1Source5 : Coefficient :=
  recurrence1Source5Block0

def recurrence1Source6Block0 : Coefficient :=
  X ^ 0 * (
    (-14) * X ^ 1 +
    (49) * X ^ 2 +
    (-35) * X ^ 3
  )

def recurrence1Source6 : Coefficient :=
  recurrence1Source6Block0

def recurrence1Source7Block0 : Coefficient :=
  X ^ 0 * (
    (1)
  )

def recurrence1Source7 : Coefficient :=
  recurrence1Source7Block0

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
