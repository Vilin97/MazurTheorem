/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: C1 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2C1_coeff_166 :
    remainder4Coefficient1.coeff 166 =
      ((1250 * 10 ^ 70 +
        7903442222304732803123971906028783063848574119434822864816834563953003) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_167 :
    remainder4Coefficient1.coeff 167 =
      -((14 * 10 ^ 70 +
        9989615836734697970532791043680633945266608971793423361466969110295794) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_168 :
    remainder4Coefficient1.coeff 168 =
      -((14 * 10 ^ 70 +
        8696398539325476469068356168921780691864510622423485343401920923605166) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_169 :
    remainder4Coefficient1.coeff 169 =
      ((2 * 10 ^ 70 +
        0237063316334925680608760927303605068267938560261997819558586394122914) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_170 :
    remainder4Coefficient1.coeff 170 =
      (-748371003927271741154170478339583777836960419996028824929270989581123 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_171 :
    remainder4Coefficient1.coeff 171 =
      (-85500969710033529515701255008079454173238356005406635218287093039812 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_172 :
    remainder4Coefficient1.coeff 172 =
      (9805356358872421213404169395195216896652001757665991741785888748610 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_173 :
    remainder4Coefficient1.coeff 173 =
      (-61345332488416245192841569760865389874036903242755294008937358735 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_174 :
    remainder4Coefficient1.coeff 174 =
      (-30602577928356269945403679237996685764814476605133233014722791183 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_175 :
    remainder4Coefficient1.coeff 175 =
      (323186898189767301851367256237775098177011900046387817145431534 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_176 :
    remainder4Coefficient1.coeff 176 =
      (57076164149317311983241554774282234744487139323987989294860309 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_177 :
    remainder4Coefficient1.coeff 177 =
      (1329663713510284822304878170309472305717733391736680340167785 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_178 :
    remainder4Coefficient1.coeff 178 =
      (13522759127750948405565665267486800697891120261481180520272 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_179 :
    remainder4Coefficient1.coeff 179 =
      (68440232685480362737473256330659552453146279574330053768 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_180 :
    remainder4Coefficient1.coeff 180 =
      (156301300456882419884388060396740496525691255162599401 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_181 :
    remainder4Coefficient1.coeff 181 =
      (20821378000265036417859664107395263307004515217945 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_182 :
    remainder4Coefficient1.coeff 182 =
      (-561782912259307626492836017518121175468993499202 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_183 :
    remainder4Coefficient1.coeff 183 =
      (-908825169258193200572233082016061743080333582 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_184 :
    remainder4Coefficient1.coeff 184 =
      (-492227487195799594960341191069630546220098 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_185 :
    remainder4Coefficient1.coeff 185 =
      (-90673694400791428354037928543020554710 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_186 :
    remainder4Coefficient1.coeff 186 =
      (-4894913024786264472437929522098555 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_187 :
    remainder4Coefficient1.coeff 187 =
      (-60464546983171638597828541088 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_188 :
    remainder4Coefficient1.coeff 188 =
      (-115387634732139429500246 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_189 :
    remainder4Coefficient1.coeff 189 =
      (-16865704796555725 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C1_coeff_190 :
    remainder4Coefficient1.coeff 190 =
      (-47165519 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
