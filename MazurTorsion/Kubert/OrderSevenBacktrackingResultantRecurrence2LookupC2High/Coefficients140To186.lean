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

theorem recurrence2C2_coeff_140 :
    remainder4Coefficient2.coeff 140 =
      ((545495042251656678 * 10 ^ 70 +
        4448047402110233460146282112556757291567967665075212206962081089569165) : ℚ) := by
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

theorem recurrence2C2_coeff_141 :
    remainder4Coefficient2.coeff 141 =
      -((239635525698333278 * 10 ^ 70 +
        2313879726027214180604480213380039675328710039723652185594984982722881) : ℚ) := by
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

theorem recurrence2C2_coeff_142 :
    remainder4Coefficient2.coeff 142 =
      ((98936186088592686 * 10 ^ 70 +
        0999798035647160554046509150553892349377879300720051505481113835226060) : ℚ) := by
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

theorem recurrence2C2_coeff_143 :
    remainder4Coefficient2.coeff 143 =
      -((38184727599314742 * 10 ^ 70 +
        9711642300618301348353547144994237822801814416213389089581355340798977) : ℚ) := by
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

theorem recurrence2C2_coeff_144 :
    remainder4Coefficient2.coeff 144 =
      ((13685700167421208 * 10 ^ 70 +
        0441960218832716707883599606323854120524379319121072077228824611642072) : ℚ) := by
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

theorem recurrence2C2_coeff_145 :
    remainder4Coefficient2.coeff 145 =
      -((4512962701163464 * 10 ^ 70 +
        8481994650197117062797183134315190447379958138072976622656384777476829) : ℚ) := by
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

theorem recurrence2C2_coeff_146 :
    remainder4Coefficient2.coeff 146 =
      ((1349937174563399 * 10 ^ 70 +
        2366383376103963424797613579139842371246961828632613065521410288659204) : ℚ) := by
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

theorem recurrence2C2_coeff_147 :
    remainder4Coefficient2.coeff 147 =
      -((357504839514598 * 10 ^ 70 +
        6264001012184531861179826681129668217238819294980375827349814318187155) : ℚ) := by
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

theorem recurrence2C2_coeff_148 :
    remainder4Coefficient2.coeff 148 =
      ((79794795263487 * 10 ^ 70 +
        3001422348877838102440219321132104321794504097291801071751528264013964) : ℚ) := by
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

theorem recurrence2C2_coeff_149 :
    remainder4Coefficient2.coeff 149 =
      -((13085779699821 * 10 ^ 70 +
        7561263622115097279825692105824275409705351569275370805001196731315909) : ℚ) := by
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

theorem recurrence2C2_coeff_150 :
    remainder4Coefficient2.coeff 150 =
      ((557848508684 * 10 ^ 70 +
        3194049029470949951372079004904281088440799602826741906765519633180691) : ℚ) := by
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

theorem recurrence2C2_coeff_151 :
    remainder4Coefficient2.coeff 151 =
      ((656491974330 * 10 ^ 70 +
        1259271028764794897564872386758683949788656350642552684179839014462251) : ℚ) := by
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

theorem recurrence2C2_coeff_152 :
    remainder4Coefficient2.coeff 152 =
      -((340265097786 * 10 ^ 70 +
        9073936987252594643044456356652589106723432010870921611703964077502102) : ℚ) := by
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

theorem recurrence2C2_coeff_153 :
    remainder4Coefficient2.coeff 153 =
      ((110261265197 * 10 ^ 70 +
        6606211127788267877361795094128304590273551701327081125314949560654168) : ℚ) := by
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

theorem recurrence2C2_coeff_154 :
    remainder4Coefficient2.coeff 154 =
      -((27369200514 * 10 ^ 70 +
        3007499319135674520415723558904852651605530633918761890006680036424865) : ℚ) := by
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

theorem recurrence2C2_coeff_155 :
    remainder4Coefficient2.coeff 155 =
      ((5341863670 * 10 ^ 70 +
        3533521403882490129350488568993074985030032417003855160123865201318551) : ℚ) := by
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

theorem recurrence2C2_coeff_156 :
    remainder4Coefficient2.coeff 156 =
      -((777462185 * 10 ^ 70 +
        4287032543423151395136377560713134475394336387200732060197148451687229) : ℚ) := by
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

theorem recurrence2C2_coeff_157 :
    remainder4Coefficient2.coeff 157 =
      ((64874925 * 10 ^ 70 +
        4819097285143644149880824481890867775232475613171423661072952397032363) : ℚ) := by
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

theorem recurrence2C2_coeff_158 :
    remainder4Coefficient2.coeff 158 =
      ((4066755 * 10 ^ 70 +
        9961745948466811916356930393490027724357280090943765495520663687537879) : ℚ) := by
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

theorem recurrence2C2_coeff_159 :
    remainder4Coefficient2.coeff 159 =
      -((2671670 * 10 ^ 70 +
        0449768319193609518989633960724072860960250174953457224823174829481186) : ℚ) := by
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

theorem recurrence2C2_coeff_160 :
    remainder4Coefficient2.coeff 160 =
      ((527435 * 10 ^ 70 +
        6025225703046170242979901357741635181363681816204785116299129863311508) : ℚ) := by
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

theorem recurrence2C2_coeff_161 :
    remainder4Coefficient2.coeff 161 =
      -((57843 * 10 ^ 70 +
        3365242037667793316025326110860620185301292048009247099537570690234235) : ℚ) := by
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

theorem recurrence2C2_coeff_162 :
    remainder4Coefficient2.coeff 162 =
      ((1759 * 10 ^ 70 +
        8377451888598060835054508831783532371938876082709989283341087212863893) : ℚ) := by
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

theorem recurrence2C2_coeff_163 :
    remainder4Coefficient2.coeff 163 =
      ((585 * 10 ^ 70 +
        7324080631565493577444444058116452194427675603956331700136455457121921) : ℚ) := by
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

theorem recurrence2C2_coeff_164 :
    remainder4Coefficient2.coeff 164 =
      -((112 * 10 ^ 70 +
        7047228734001551804772221975168972668695974820502998424925313345626848) : ℚ) := by
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

theorem recurrence2C2_coeff_165 :
    remainder4Coefficient2.coeff 165 =
      ((8 * 10 ^ 70 +
        6170654803447237825628813806279840136283737627718799899506883417704738) : ℚ) := by
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

theorem recurrence2C2_coeff_166 :
    remainder4Coefficient2.coeff 166 =
      (260304475161797145398747507909755831126921362946186995357748453767939 : ℚ) := by
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

theorem recurrence2C2_coeff_167 :
    remainder4Coefficient2.coeff 167 =
      (-623110430768711450652133308005580578248691415521024213386880594118973 : ℚ) := by
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

theorem recurrence2C2_coeff_168 :
    remainder4Coefficient2.coeff 168 =
      (41776801331108241105978128716420030700017442670779391098954405488922 : ℚ) := by
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

theorem recurrence2C2_coeff_169 :
    remainder4Coefficient2.coeff 169 =
      (552873088182398204575602962978492116170266734493275883094696905346 : ℚ) := by
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

theorem recurrence2C2_coeff_170 :
    remainder4Coefficient2.coeff 170 =
      (-146641573414660105079274449564423591228713461852171327308007703462 : ℚ) := by
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

theorem recurrence2C2_coeff_171 :
    remainder4Coefficient2.coeff 171 =
      (140414764137155687548391560719402298423384047790785358226966828 : ℚ) := by
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

theorem recurrence2C2_coeff_172 :
    remainder4Coefficient2.coeff 172 =
      (246756829723010629400696609968495046438482087364781599416547030 : ℚ) := by
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

theorem recurrence2C2_coeff_173 :
    remainder4Coefficient2.coeff 173 =
      (6374876097679124864271013837989479431461389504478683404698450 : ℚ) := by
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

theorem recurrence2C2_coeff_174 :
    remainder4Coefficient2.coeff 174 =
      (68644985716931685935093412619381806311742578076046833518791 : ℚ) := by
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

theorem recurrence2C2_coeff_175 :
    remainder4Coefficient2.coeff 175 =
      (364752712682660817273052048753785522516042208091698118328 : ℚ) := by
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

theorem recurrence2C2_coeff_176 :
    remainder4Coefficient2.coeff 176 =
      (887672225200959590046747140069739815284081905985503186 : ℚ) := by
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

theorem recurrence2C2_coeff_177 :
    remainder4Coefficient2.coeff 177 =
      (260416846363090404572065299936426001227011827652536 : ℚ) := by
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

theorem recurrence2C2_coeff_178 :
    remainder4Coefficient2.coeff 178 =
      (-2999868740724368539976749597623483368695197658822 : ℚ) := by
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

theorem recurrence2C2_coeff_179 :
    remainder4Coefficient2.coeff 179 =
      (-5293787106788466174945020234609187203594277827 : ℚ) := by
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

theorem recurrence2C2_coeff_180 :
    remainder4Coefficient2.coeff 180 =
      (-3092215409250669568723570087366039416554849 : ℚ) := by
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

theorem recurrence2C2_coeff_181 :
    remainder4Coefficient2.coeff 181 =
      (-623385139448741590273548450203781354774 : ℚ) := by
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

theorem recurrence2C2_coeff_182 :
    remainder4Coefficient2.coeff 182 =
      (-37819466164327403912651638801913724 : ℚ) := by
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

theorem recurrence2C2_coeff_183 :
    remainder4Coefficient2.coeff 183 =
      (-547300143822422198021388493673 : ℚ) := by
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

theorem recurrence2C2_coeff_184 :
    remainder4Coefficient2.coeff 184 =
      (-1310874591511338125412131 : ℚ) := by
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

theorem recurrence2C2_coeff_185 :
    remainder4Coefficient2.coeff 185 =
      (-274805999919516755 : ℚ) := by
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

theorem recurrence2C2_coeff_186 :
    remainder4Coefficient2.coeff 186 =
      (-1255012469 : ℚ) := by
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
