/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B5 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B5_coeff_0 :
    remainder3Coefficient5.coeff 0 =
      (64 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_1 :
    remainder3Coefficient5.coeff 1 =
      (-12156 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_2 :
    remainder3Coefficient5.coeff 2 =
      (1354562202 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_3 :
    remainder3Coefficient5.coeff 3 =
      (-518380813692 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_4 :
    remainder3Coefficient5.coeff 4 =
      (585555622533882 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_5 :
    remainder3Coefficient5.coeff 5 =
      (-157410261428692160 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_6 :
    remainder3Coefficient5.coeff 6 =
      (34556515582732965276 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_7 :
    remainder3Coefficient5.coeff 7 =
      (-4301410760970204622105 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_8 :
    remainder3Coefficient5.coeff 8 =
      (384185146583496783398731 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_9 :
    remainder3Coefficient5.coeff 9 =
      (-23102340457255115206225180 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_10 :
    remainder3Coefficient5.coeff 10 =
      (1023234497103504062614474552 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_11 :
    remainder3Coefficient5.coeff 11 =
      (-33268964950842174920443327383 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_12 :
    remainder3Coefficient5.coeff 12 =
      (758633249959525901109917614448 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_13 :
    remainder3Coefficient5.coeff 13 =
      (1507484628252244886952455312383 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_14 :
    remainder3Coefficient5.coeff 14 =
      (-1597478344599563677298840073878171 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_15 :
    remainder3Coefficient5.coeff 15 =
      (116373838883438904938614640656704955 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_16 :
    remainder3Coefficient5.coeff 16 =
      (-5366032119857615523081935066061634679 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_17 :
    remainder3Coefficient5.coeff 17 =
      (181168266321197660865678430073531837421 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_18 :
    remainder3Coefficient5.coeff 18 =
      (-4688268113965608702130455099134678375699 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_19 :
    remainder3Coefficient5.coeff 19 =
      (94242606004781941951845106722309539305573 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_20 :
    remainder3Coefficient5.coeff 20 =
      (-1443692377612875362915310937684463618654664 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_21 :
    remainder3Coefficient5.coeff 21 =
      (15220765080512840366464686731227324522190291 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_22 :
    remainder3Coefficient5.coeff 22 =
      (-51709534414231195056832264154795877180578015 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_23 :
    remainder3Coefficient5.coeff 23 =
      (-2088691358881307945602799163382309623604857558 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_24 :
    remainder3Coefficient5.coeff 24 =
      (62112663824049410516588572312860692397002375981 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_25 :
    remainder3Coefficient5.coeff 25 =
      (-1096152708335522347033464127465701902955878650206 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_26 :
    remainder3Coefficient5.coeff 26 =
      (14948017681121838016616867722378586391672891499004 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_27 :
    remainder3Coefficient5.coeff 27 =
      (-169500399305199683132202717770969364728771132566079 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_28 :
    remainder3Coefficient5.coeff 28 =
      (1651019051308693417631201608933808494457423689764077 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_29 :
    remainder3Coefficient5.coeff 29 =
      (-14063627383815414127233100855777399941339125040500099 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_30 :
    remainder3Coefficient5.coeff 30 =
      (105917189634355617289564490597701936033350055464950937 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_31 :
    remainder3Coefficient5.coeff 31 =
      (-710165696978516089964604718979335271731610544719841884 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_32 :
    remainder3Coefficient5.coeff 32 =
      (4256548100224837219944082284559531223048156335571915446 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_33 :
    remainder3Coefficient5.coeff 33 =
      (-22848238885305523165302020957055047654566058350901061154 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_34 :
    remainder3Coefficient5.coeff 34 =
      (109789128754097385507407932976912040088068164627896663603 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_35 :
    remainder3Coefficient5.coeff 35 =
      (-470661950176926338602388446111629162245194919375373530551 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_36 :
    remainder3Coefficient5.coeff 36 =
      (1785017533754185844634067673117507157955536654718105276975 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_37 :
    remainder3Coefficient5.coeff 37 =
      (-5877578946285211009667169735200547441309488908296664940137 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_38 :
    remainder3Coefficient5.coeff 38 =
      (16073844166706592948672022590492243118351718016347366895539 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_39 :
    remainder3Coefficient5.coeff 39 =
      (-31972063857397936867818279330587369649806597070346540161288 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_40 :
    remainder3Coefficient5.coeff 40 =
      (16526830343414984442770481395649957371359772004219738968345 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_41 :
    remainder3Coefficient5.coeff 41 =
      (232874833269767410146557178501078408661719140279534891310910 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_42 :
    remainder3Coefficient5.coeff 42 =
      (-1483268019190884257892954689205167345399660826585251827140150 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_43 :
    remainder3Coefficient5.coeff 43 =
      (6153412297890782315442632121625329952107476035612251127804010 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_44 :
    remainder3Coefficient5.coeff 44 =
      (-21050635779083919515488972262208135117165390212869305927476258 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_45 :
    remainder3Coefficient5.coeff 45 =
      (62627862336168020614276340147971039322194268518301393583264248 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_46 :
    remainder3Coefficient5.coeff 46 =
      (-156650913352348315895120015905858960763193998994036032611684592 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_47 :
    remainder3Coefficient5.coeff 47 =
      (288605086662484691375303631867463597517122484614948498510881529 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_48 :
    remainder3Coefficient5.coeff 48 =
      (-274939148849570046895308170617336734246000723960126787775642912 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_49 :
    remainder3Coefficient5.coeff 49 =
      (152350745627287390737076952925818039970546316231009997001622265 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_50 :
    remainder3Coefficient5.coeff 50 =
      (-3675919368687448028956551421543945784774951429554339175838887131 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_51 :
    remainder3Coefficient5.coeff 51 =
      (24718253578327531557654063039275426081028169217687267035479497655 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_52 :
    remainder3Coefficient5.coeff 52 =
      (-55400300387709814704672048624214403986754900782173671569889578366 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_53 :
    remainder3Coefficient5.coeff 53 =
      (-157374571515781813053417558657762161533945946317239716557761927688 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_54 :
    remainder3Coefficient5.coeff 54 =
      (1534714190196044122729144518082790927485218819424997583811024485594 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_55 :
    remainder3Coefficient5.coeff 55 =
      (-4282329269304493210767701528326420236321334042909988444148947142377 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_56 :
    remainder3Coefficient5.coeff 56 =
      (-3041267233044429338394683166576711604150740321675024639781277390349 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_57 :
    remainder3Coefficient5.coeff 57 =
      (69524738659047282022855197487281119144351180244689394823464662944194 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_58 :
    remainder3Coefficient5.coeff 58 =
      (-255969526666785140037704816165129538592843787358204745662036357188846 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_59 :
    remainder3Coefficient5.coeff 59 =
      (241457309966006350374379727158419282784868344869176178406301862034607 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_60 :
    remainder3Coefficient5.coeff 60 =
      (1955858626746270931855404397872885430919663983795806797029695044989887 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_61 :
    remainder3Coefficient5.coeff 61 =
      -((1 * 10 ^ 70 +
        1051349933467088165738058933963914517770030080980683601082305893458160) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_62 :
    remainder3Coefficient5.coeff 62 =
      ((2 * 10 ^ 70 +
        6400172437023117610899553651518033237685125014432822917090407935153063) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_63 :
    remainder3Coefficient5.coeff 63 =
      (-91318310931367026818465719861175689272173472685573552275420049939245 : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_64 :
    remainder3Coefficient5.coeff 64 =
      -((25 * 10 ^ 70 +
        8532857061551560619365614597404627507404602945638687838891821075609611) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_65 :
    remainder3Coefficient5.coeff 65 =
      ((111 * 10 ^ 70 +
        4163830836147869011439870007577002678406117261980631161822979234983019) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_66 :
    remainder3Coefficient5.coeff 66 =
      -((247 * 10 ^ 70 +
        9240447283096022041103532283391225269761211109368923961149915724191930) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B5_coeff_67 :
    remainder3Coefficient5.coeff 67 =
      ((110 * 10 ^ 70 +
        2611223183233577487645478890032845953513110067800062998680582546465865) : ℚ) := by
  unfold
    remainder3Coefficient5
    remainder3Coefficient5Block1
    remainder3Coefficient5Block0
    remainder3Coefficient5Chunk16
    remainder3Coefficient5Chunk15
    remainder3Coefficient5Chunk14
    remainder3Coefficient5Chunk13
    remainder3Coefficient5Chunk12
    remainder3Coefficient5Chunk11
    remainder3Coefficient5Chunk10
    remainder3Coefficient5Chunk9
    remainder3Coefficient5Chunk8
    remainder3Coefficient5Chunk7
    remainder3Coefficient5Chunk6
    remainder3Coefficient5Chunk5
    remainder3Coefficient5Chunk4
    remainder3Coefficient5Chunk3
    remainder3Coefficient5Chunk2
    remainder3Coefficient5Chunk1
    remainder3Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
