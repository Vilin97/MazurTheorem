/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: A0 source coefficients, low half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5A0_coeff_0 :
    remainder5Coefficient0.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_1 :
    remainder5Coefficient0.coeff 1 =
      (4887571991875429920 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_2 :
    remainder5Coefficient0.coeff 2 =
      (-25862224734312801281604 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_3 :
    remainder5Coefficient0.coeff 3 =
      (35372326149991200512269296 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_4 :
    remainder5Coefficient0.coeff 4 =
      (-11994495558598503003979650365 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_5 :
    remainder5Coefficient0.coeff 5 =
      (439412061172741909170749685506 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_6 :
    remainder5Coefficient0.coeff 6 =
      (535531707559636373716732677521571 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_7 :
    remainder5Coefficient0.coeff 7 =
      (3515669660008120863103970037003788 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_8 :
    remainder5Coefficient0.coeff 8 =
      (-137797227938399012622190556536047978182 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_9 :
    remainder5Coefficient0.coeff 9 =
      (75113304221638554753993755673360353276034 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_10 :
    remainder5Coefficient0.coeff 10 =
      (-21845786630709128854528865089894322350844359 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_11 :
    remainder5Coefficient0.coeff 11 =
      (3911350934757114325710432818796201936741460436 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_12 :
    remainder5Coefficient0.coeff 12 =
      (-398441293078700088041923675400363165043295235234 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_13 :
    remainder5Coefficient0.coeff 13 =
      (4123882365520527489359092464019602725830484471169 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_14 :
    remainder5Coefficient0.coeff 14 =
      (6314254018905038755463164606664769270219017021638468 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_15 :
    remainder5Coefficient0.coeff 15 =
      (-1281930500475189602907473686431531793653024235046383974 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_16 :
    remainder5Coefficient0.coeff 16 =
      (156268923495287605702743256327598685864433911490898944117 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_17 :
    remainder5Coefficient0.coeff 17 =
      (-13995239471151658079713348857659400489044334716804388277939 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_18 :
    remainder5Coefficient0.coeff 18 =
      (984589177406832517922864869071975516417569516408064882992691 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_19 :
    remainder5Coefficient0.coeff 19 =
      (-56233032965062559106099866374398202932848512704147182831909385 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_20 :
    remainder5Coefficient0.coeff 20 =
      (2658073941048334658369917470590569052347447165406127167753461207 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_21 :
    remainder5Coefficient0.coeff 21 =
      (-105230819192365117504301362271166219711415602761053764576508612404 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_22 :
    remainder5Coefficient0.coeff 22 =
      (3511657931145534156721969993525652669762967877218775064312017896152 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_23 :
    remainder5Coefficient0.coeff 23 =
      (-98855060217706313715227024215381219274544749687701849505168936375605 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_24 :
    remainder5Coefficient0.coeff 24 =
      (2329485503403438133869436195842905867890200111313951578007010764929866 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_25 :
    remainder5Coefficient0.coeff 25 =
      -((4 * 10 ^ 70 +
        4816818404677567728838884038004383623840895033748741112433687787162681) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_26 :
    remainder5Coefficient0.coeff 26 =
      ((65 * 10 ^ 70 +
        3079939636693244908229108408669143254114959505578711742633319810237042) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_27 :
    remainder5Coefficient0.coeff 27 =
      -((511 * 10 ^ 70 +
        4586006030062491512618567007445058137468126488848592962293829871268773) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_28 :
    remainder5Coefficient0.coeff 28 =
      -((7122 * 10 ^ 70 +
        9010306559825805936161673099251638061098505513350380986679725209237102) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_29 :
    remainder5Coefficient0.coeff 29 =
      ((419433 * 10 ^ 70 +
        1216452963268839721926139146932021471711218920888090495977302659690910) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_30 :
    remainder5Coefficient0.coeff 30 =
      -((11326449 * 10 ^ 70 +
        8714999495182556155513853879792303248713267764998032183764037381103072) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_31 :
    remainder5Coefficient0.coeff 31 =
      ((231687424 * 10 ^ 70 +
        7404541280923740754719677496834713464055526621117991213590491943731302) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_32 :
    remainder5Coefficient0.coeff 32 =
      -((3973938455 * 10 ^ 70 +
        8883936936827253717741022225307913347502862539219693216828977300642560) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_33 :
    remainder5Coefficient0.coeff 33 =
      ((59505147162 * 10 ^ 70 +
        7005929429080188721404364714239765370856654625524764091032895166211547) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_34 :
    remainder5Coefficient0.coeff 34 =
      -((794474175631 * 10 ^ 70 +
        4431221808749201154051520176448555079871063640247457266497528879041402) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_35 :
    remainder5Coefficient0.coeff 35 =
      ((9582320454870 * 10 ^ 70 +
        5926602439026853781148868883061758139389362358480933867852156822896436) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_36 :
    remainder5Coefficient0.coeff 36 =
      -((105351733438460 * 10 ^ 70 +
        6876605402206019425184413646483721211520709104168654329502241657586890) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_37 :
    remainder5Coefficient0.coeff 37 =
      ((1062940127362624 * 10 ^ 70 +
        4749532907494087477248734158257704027784005424961040075868060769280471) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_38 :
    remainder5Coefficient0.coeff 38 =
      -((9893892705968742 * 10 ^ 70 +
        0910011074355011057314683901928848081195128183278597365061627204810745) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_39 :
    remainder5Coefficient0.coeff 39 =
      ((85329079432408139 * 10 ^ 70 +
        5246714028361672843581308608449037934242866570553203143935573016437015) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_40 :
    remainder5Coefficient0.coeff 40 =
      -((684359851738989164 * 10 ^ 70 +
        4055636350113265734812957669343123737839048743429909754405787145966666) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_41 :
    remainder5Coefficient0.coeff 41 =
      ((5120318652697546548 * 10 ^ 70 +
        8135360967938154814143874952785069541271360156945336214463898549868583) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_42 :
    remainder5Coefficient0.coeff 42 =
      -((35837067586821021901 * 10 ^ 70 +
        2449414159821985023501744803449135092362883806102763506866020870934047) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_43 :
    remainder5Coefficient0.coeff 43 =
      ((235208635655594796314 * 10 ^ 70 +
        0995372543377698186930075944151705738193128538582218841618885795728980) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_44 :
    remainder5Coefficient0.coeff 44 =
      -((1450807765581795301238 * 10 ^ 70 +
        1990968635986496744204014077081284485004598874375548540147043688991488) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_45 :
    remainder5Coefficient0.coeff 45 =
      ((8426717830051821298372 * 10 ^ 70 +
        4823519948504416295743268906798714047156214305440942000800673860103762) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_46 :
    remainder5Coefficient0.coeff 46 =
      -((46171504189600759183412 * 10 ^ 70 +
        1537907360524331429008757371321057077570964137531730280228498096717354) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_47 :
    remainder5Coefficient0.coeff 47 =
      ((239034558744841404434241 * 10 ^ 70 +
        4394903167035330091431640800311814446445989887616078499314700805292382) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_48 :
    remainder5Coefficient0.coeff 48 =
      -((1171007820132776185988031 * 10 ^ 70 +
        7046548327444828128742021358598201755468672784835371918018137485693917) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_49 :
    remainder5Coefficient0.coeff 49 =
      ((5435712887280180991037964 * 10 ^ 70 +
        7157359685329614465626902469018382704599097729708638117375685811357788) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_50 :
    remainder5Coefficient0.coeff 50 =
      -((23937863875881329174746485 * 10 ^ 70 +
        7556473673475092394677659152956535842338698483317092340958289901227230) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_51 :
    remainder5Coefficient0.coeff 51 =
      ((100123281544262259505981396 * 10 ^ 70 +
        8236332114746982416332770559689156771755981372690973775919450035097727) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_52 :
    remainder5Coefficient0.coeff 52 =
      -((398155141402022928237601435 * 10 ^ 70 +
        6920440533596595012539365120557430487271887852095979268091246922934109) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_53 :
    remainder5Coefficient0.coeff 53 =
      ((1506765451223968972262942646 * 10 ^ 70 +
        1451227728505681878019872182607369524742199704166268925971086976384040) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_54 :
    remainder5Coefficient0.coeff 54 =
      -((5431108575438797143759885055 * 10 ^ 70 +
        7665708507346268702578261202533478262930015915656189209274882040910068) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_55 :
    remainder5Coefficient0.coeff 55 =
      ((18660448535995011753694541582 * 10 ^ 70 +
        9853877297720489641463655677681339984352922324903215478602958538715211) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_56 :
    remainder5Coefficient0.coeff 56 =
      -((61158686041306839404091406377 * 10 ^ 70 +
        2088162296226133127611704325252144974150259434942515615179101544564573) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_57 :
    remainder5Coefficient0.coeff 57 =
      ((191329205793070466164989489039 * 10 ^ 70 +
        6110472704748055000747334535575154979395187526071955624118758991633955) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_58 :
    remainder5Coefficient0.coeff 58 =
      -((571677521334184191012689678804 * 10 ^ 70 +
        9250410680547903706395400509991507546235707173281922332795334225285294) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_59 :
    remainder5Coefficient0.coeff 59 =
      ((1632316976399195611587173073528 * 10 ^ 70 +
        1870524784866876222188686450937614827450004948767598673224838836175651) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_60 :
    remainder5Coefficient0.coeff 60 =
      -((4456123933955960731809436413387 * 10 ^ 70 +
        7384023557985226534905262530789622839281072616492225232195603228842131) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_61 :
    remainder5Coefficient0.coeff 61 =
      ((11636062687267213896627407406533 * 10 ^ 70 +
        5757436555693248046523831693456188969647694620069399853040469394129594) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_62 :
    remainder5Coefficient0.coeff 62 =
      -((29075684806921527817763431638831 * 10 ^ 70 +
        5105922683526793073933332415764717528187606223666847855925365036563421) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_63 :
    remainder5Coefficient0.coeff 63 =
      ((69549178636088182871034694361742 * 10 ^ 70 +
        1696479838373984598028512647266279435604589961722051285943410821810206) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_64 :
    remainder5Coefficient0.coeff 64 =
      -((159309125789417493428163940784944 * 10 ^ 70 +
        7205991083419461212179413582964036644734131101707474092641341443121857) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_65 :
    remainder5Coefficient0.coeff 65 =
      ((349551442116073380694987905484751 * 10 ^ 70 +
        4762747922977764434004797794653711833758649082659921185397910671631189) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_66 :
    remainder5Coefficient0.coeff 66 =
      -((734897197142545534039006166595572 * 10 ^ 70 +
        7297789376458434716590175405229677479337751491295152176201521668430134) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_67 :
    remainder5Coefficient0.coeff 67 =
      ((1480811244380893341196991283636431 * 10 ^ 70 +
        9573019480663410545928739569337870706768003416793653569772332565440367) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_68 :
    remainder5Coefficient0.coeff 68 =
      -((2860444776487941119332018778494857 * 10 ^ 70 +
        1515451027288870268655322317190352948297806619183709976953334662988135) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_69 :
    remainder5Coefficient0.coeff 69 =
      ((5298136340065355922206131007550661 * 10 ^ 70 +
        6079040861684780246967180871471795521090464818133849612153000008391215) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_70 :
    remainder5Coefficient0.coeff 70 =
      -((9411447826555658618025003315947917 * 10 ^ 70 +
        2770448195139388982143683242981935381452740027188165557956119295322222) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_71 :
    remainder5Coefficient0.coeff 71 =
      ((16036736550276335274554057653397162 * 10 ^ 70 +
        2620841655701793052303117716290990196501875413380403771295736645631298) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_72 :
    remainder5Coefficient0.coeff 72 =
      -((26216830646887135752800176957696623 * 10 ^ 70 +
        4183299183213561726796853007361683377452384820971925555130963560507579) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_73 :
    remainder5Coefficient0.coeff 73 =
      ((41126794497004408367551300142090161 * 10 ^ 70 +
        1167099546730892418935027948040240114769885793896055258239594308535512) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_74 :
    remainder5Coefficient0.coeff 74 =
      -((61919152039956767651397917379434832 * 10 ^ 70 +
        6796057013962313078721166176959815558521680842725668233761257861622960) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_75 :
    remainder5Coefficient0.coeff 75 =
      ((89486310243001259935457437560569698 * 10 ^ 70 +
        7612857108252901539798226547855367342171911980562494905877926301476561) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_76 :
    remainder5Coefficient0.coeff 76 =
      -((124164856438049782603024935910088518 * 10 ^ 70 +
        7082866496188776513635281914185184899482005316140924152326491972920466) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_77 :
    remainder5Coefficient0.coeff 77 =
      ((165438087338405025268063752741835370 * 10 ^ 70 +
        3575587088970557143090312595229950392524459740461728854517786663210807) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_78 :
    remainder5Coefficient0.coeff 78 =
      -((211718470892814818149351123099125982 * 10 ^ 70 +
        2283028350335698018097981095338374505423186859138490990217001370359556) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_79 :
    remainder5Coefficient0.coeff 79 =
      ((260297462351817494862697006271819896 * 10 ^ 70 +
        2517623694194833343259771956122989021675077360716008329749151835304143) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_80 :
    remainder5Coefficient0.coeff 80 =
      -((307526461409996066913756217047807698 * 10 ^ 70 +
        4674254522717532200451165358834291349018790024487901267676213429203588) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_81 :
    remainder5Coefficient0.coeff 81 =
      ((349239665380013329937954137094088623 * 10 ^ 70 +
        2153412932869011989103931606436024022167691774754309554283001751461191) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_82 :
    remainder5Coefficient0.coeff 82 =
      -((381359926020766459983986293433501353 * 10 ^ 70 +
        6741729606880763146845237922564643233148420610041927320355752144134513) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_83 :
    remainder5Coefficient0.coeff 83 =
      ((400565442267181068985388715955408179 * 10 ^ 70 +
        6076442350875644654576171949281150250608338654174122507197679536491805) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_84 :
    remainder5Coefficient0.coeff 84 =
      -((404862933058487126089385281268509210 * 10 ^ 70 +
        0396203678983565364388919311358989611632729853202522127176132739688346) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_85 :
    remainder5Coefficient0.coeff 85 =
      ((393927286528283979441148634009500441 * 10 ^ 70 +
        8427976985601367575651235380823240782739109063166891311688142130194069) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_86 :
    remainder5Coefficient0.coeff 86 =
      -((369126738800481839759908256992710194 * 10 ^ 70 +
        5621769250933224382290814418722678270430104546972132621553143295302900) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_87 :
    remainder5Coefficient0.coeff 87 =
      ((333236826929963856231256738191043055 * 10 ^ 70 +
        1424431443627908077517731394037363989415597489885590615852578495449821) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A0_coeff_88 :
    remainder5Coefficient0.coeff 88 =
      -((289926340930413391493594466822976939 * 10 ^ 70 +
        5020980558870460893368627812229004713684663731465865614623594148701096) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
