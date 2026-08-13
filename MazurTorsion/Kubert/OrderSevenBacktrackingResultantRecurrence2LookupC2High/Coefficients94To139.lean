/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: C2 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2C2_coeff_94 :
    remainder4Coefficient2.coeff 94 =
      ((1767557249382891057135697480888 * 10 ^ 70 +
        2706408288388953232305808502036777758253541368550503717959757145505844) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_95 :
    remainder4Coefficient2.coeff 95 =
      -((1810058987033920597474075641122 * 10 ^ 70 +
        7449030846929552131098494411960867011698261342043173255392970743722540) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_96 :
    remainder4Coefficient2.coeff 96 =
      ((1792372205318080624151854379397 * 10 ^ 70 +
        3495410899569893978240178699839162856651984104086252369683241040245948) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_97 :
    remainder4Coefficient2.coeff 97 =
      -((1716233744269651030021134444440 * 10 ^ 70 +
        4379135248100137167989718537606739708577908355054171233958353225461955) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_98 :
    remainder4Coefficient2.coeff 98 =
      ((1589025417315563474946800058802 * 10 ^ 70 +
        6689961549088725592299606587436862162433490416298346003571416308356122) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_99 :
    remainder4Coefficient2.coeff 99 =
      -((1422597081808654222915982975791 * 10 ^ 70 +
        1058149761872011000880795590727574061612932446622988184013066122921782) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_100 :
    remainder4Coefficient2.coeff 100 =
      ((1231451842576351883514643006415 * 10 ^ 70 +
        6411182686533701128925055067799005297758819813745485937571084382472765) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_101 :
    remainder4Coefficient2.coeff 101 =
      -((1030677288462129098833186835812 * 10 ^ 70 +
        7402798983786396455240892052558820524966467937047404859798212495542034) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_102 :
    remainder4Coefficient2.coeff 102 =
      ((834028280571507099001617348463 * 10 ^ 70 +
        0074179777719206447141617902779963654180666747817912812546878689600191) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_103 :
    remainder4Coefficient2.coeff 103 =
      -((652488187217275441231940757294 * 10 ^ 70 +
        8389078418241355429097420653483054165534486952379422647299659724346161) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_104 :
    remainder4Coefficient2.coeff 104 =
      ((493489061134408917018631246472 * 10 ^ 70 +
        8476751543295376303033512097558100045533906787081483549167689365311490) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_105 :
    remainder4Coefficient2.coeff 105 =
      -((360805381045047700060441469942 * 10 ^ 70 +
        5454802700959704208190282227231956840467355343603320865445437093273103) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_106 :
    remainder4Coefficient2.coeff 106 =
      ((254997127084310292210908546804 * 10 ^ 70 +
        8896949530709155769971097891611953899299081501256661236347177910279045) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_107 :
    remainder4Coefficient2.coeff 107 =
      -((174196482029223774442802714660 * 10 ^ 70 +
        5835180236448404921193397068221809503235183648918267332754537681871510) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_108 :
    remainder4Coefficient2.coeff 108 =
      ((115016262533483869946643410744 * 10 ^ 70 +
        8335271096135395826498240666652049956252097738656854648622922846037312) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_109 :
    remainder4Coefficient2.coeff 109 =
      -((73395250490251188233433559276 * 10 ^ 70 +
        0609303405190306836138714685756123176877424047225274427913957142311699) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_110 :
    remainder4Coefficient2.coeff 110 =
      ((45262413117648321985944700776 * 10 ^ 70 +
        8800536057934041623915058550556142059606406186611502221009547291563760) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_111 :
    remainder4Coefficient2.coeff 111 =
      -((26973654513491506746463499868 * 10 ^ 70 +
        7001123776167073764726932667115757116831306692705408467467401124329812) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_112 :
    remainder4Coefficient2.coeff 112 =
      ((15532606055050890699632107117 * 10 ^ 70 +
        0534300458120783632411594858031605907276468710399888537519417520263111) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_113 :
    remainder4Coefficient2.coeff 113 =
      -((8642105440386627929706254586 * 10 ^ 70 +
        3899060535812233801963055132186244209244574022583905128515833543098573) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_114 :
    remainder4Coefficient2.coeff 114 =
      ((4645478961594193618484260531 * 10 ^ 70 +
        4011717169320576353789373413482768110949482405442424835462968030944887) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_115 :
    remainder4Coefficient2.coeff 115 =
      -((2412328244291712309722400034 * 10 ^ 70 +
        7369887917465300938983345319098602580869631921855944955036392998231800) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_116 :
    remainder4Coefficient2.coeff 116 =
      ((1210003303300320555011332491 * 10 ^ 70 +
        3466519090259771111155360426703911113179054826318139876932419554727206) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_117 :
    remainder4Coefficient2.coeff 117 =
      -((586156499693961919511418929 * 10 ^ 70 +
        5251859329234638649326845806110560665451404026610181293427734716372534) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_118 :
    remainder4Coefficient2.coeff 118 =
      ((274172352710634564671137571 * 10 ^ 70 +
        8020504851004520688038449421934759035523214976421047690171873315410567) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_119 :
    remainder4Coefficient2.coeff 119 =
      -((123789330569039945785175976 * 10 ^ 70 +
        7789706006780579715708839612327931141417199071603396403395804901168564) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_120 :
    remainder4Coefficient2.coeff 120 =
      ((53926549758661731625694666 * 10 ^ 70 +
        0601231215137652161277742148564045897878837083959337994910203021554459) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_121 :
    remainder4Coefficient2.coeff 121 =
      -((22652638048529757619537233 * 10 ^ 70 +
        9917607680047455714446101997051387325272613221750468281795763685667034) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_122 :
    remainder4Coefficient2.coeff 122 =
      ((9168127757468182405699770 * 10 ^ 70 +
        2772503304999554941231843849929638522716164395198266725933165491425025) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_123 :
    remainder4Coefficient2.coeff 123 =
      -((3571460555701047558685527 * 10 ^ 70 +
        9522545203325105643595737605076471383661360181627557592276792742875316) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_124 :
    remainder4Coefficient2.coeff 124 =
      ((1337522480729370975231870 * 10 ^ 70 +
        0945206078201234336460746578712571574639690362230866994859063367318997) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_125 :
    remainder4Coefficient2.coeff 125 =
      -((480982103222555419877202 * 10 ^ 70 +
        0588684887844842054556599536937039213335907960341170296627726330781390) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_126 :
    remainder4Coefficient2.coeff 126 =
      ((165943972447586393194236 * 10 ^ 70 +
        9938041750817852537616809828505142371302028809276201575550277428073756) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_127 :
    remainder4Coefficient2.coeff 127 =
      -((54941622142462081458677 * 10 ^ 70 +
        3813731332578171103309073912163342057155379707499116024627142257537340) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_128 :
    remainder4Coefficient2.coeff 128 =
      ((17505576773096151367565 * 10 ^ 70 +
        5020509398092839294168543886678135876643133985011058021229205843864676) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_129 :
    remainder4Coefficient2.coeff 129 =
      -((5413194523426354673444 * 10 ^ 70 +
        2552000893415836736633294988700807452449281464410288588477455277697697) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_130 :
    remainder4Coefficient2.coeff 130 =
      ((1656911895220697913574 * 10 ^ 70 +
        3677092793940925620490073250552585138438894572943443149858681043276181) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_131 :
    remainder4Coefficient2.coeff 131 =
      -((521998097954849195252 * 10 ^ 70 +
        4450832979965332611339789034592793897814238840124874708895678218395410) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_132 :
    remainder4Coefficient2.coeff 132 =
      ((179751241059137240542 * 10 ^ 70 +
        3801303462987099907126927293090249117281318268888705105546384968813428) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_133 :
    remainder4Coefficient2.coeff 133 =
      -((71520596284454848030 * 10 ^ 70 +
        0596906199466088374726201378005874241434264841262653340614122769503766) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_134 :
    remainder4Coefficient2.coeff 134 =
      ((33025238052407507156 * 10 ^ 70 +
        0483097653649468369573061415046099698638823199265513312642084257066707) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_135 :
    remainder4Coefficient2.coeff 135 =
      -((16827018124105433569 * 10 ^ 70 +
        5869079929605806154768184022478284863699275447785848148241535187021437) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_136 :
    remainder4Coefficient2.coeff 136 =
      ((8902826847065231474 * 10 ^ 70 +
        6982033705194849096256371127336103813968299715371519615651179193591940) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_137 :
    remainder4Coefficient2.coeff 137 =
      -((4686765018938911838 * 10 ^ 70 +
        4675216231429415084542287555941563752607231080434727149489942952838472) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_138 :
    remainder4Coefficient2.coeff 138 =
      ((2395618811090236772 * 10 ^ 70 +
        5776690109455047544422872567766884188017341558709669196107968884919046) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_139 :
    remainder4Coefficient2.coeff 139 =
      -((1172855168503441596 * 10 ^ 70 +
        5741250873301268262923088586432694745731452798021534216191055423486283) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
