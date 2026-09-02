/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: C0 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2C0_coeff_146 :
    remainder4Coefficient0.coeff 146 =
      ((2179059921661511888 * 10 ^ 70 +
        0991752452806648450968465558688246233946116322420926607056820994759497) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_147 :
    remainder4Coefficient0.coeff 147 =
      -((930438017594896638 * 10 ^ 70 +
        6650817082302097075734917481119248244934997071052476678789216854859040) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_148 :
    remainder4Coefficient0.coeff 148 =
      ((370078080084612672 * 10 ^ 70 +
        6356268494519348454107964577116556841179398797321382685185587977969958) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_149 :
    remainder4Coefficient0.coeff 149 =
      -((136324086262083576 * 10 ^ 70 +
        8246127665592509277672122803695542468580504597063369582241026083316053) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_150 :
    remainder4Coefficient0.coeff 150 =
      ((46114161072042203 * 10 ^ 70 +
        1619855561256426869109327039185942397130099847618310755502120843935805) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_151 :
    remainder4Coefficient0.coeff 151 =
      -((14141637145293236 * 10 ^ 70 +
        6696660424614082136556413716638760770015715444095244284927265056776749) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_152 :
    remainder4Coefficient0.coeff 152 =
      ((3849065333280932 * 10 ^ 70 +
        8191852857828602130803663147684770773644642822376664781584286416155514) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_153 :
    remainder4Coefficient0.coeff 153 =
      -((892538137145727 * 10 ^ 70 +
        8589245934693804232998064720111038488256438425342463453413630502594490) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_154 :
    remainder4Coefficient0.coeff 154 =
      ((158900984539287 * 10 ^ 70 +
        8213885013155175857050104770356610490363088824067103302086798702172890) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_155 :
    remainder4Coefficient0.coeff 155 =
      -((12845979152437 * 10 ^ 70 +
        3952102125208711633256306570477379602297413297266602914312942847991116) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_156 :
    remainder4Coefficient0.coeff 156 =
      -((4952009817960 * 10 ^ 70 +
        9766051920037663089847934235957144678347013097709693482200759458430610) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_157 :
    remainder4Coefficient0.coeff 157 =
      ((3130923925535 * 10 ^ 70 +
        7051172609300198008448717376092167422365900102224697565232535215125597) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_158 :
    remainder4Coefficient0.coeff 158 =
      -((1090353929656 * 10 ^ 70 +
        1802487035470916553142686351407780548265950620925894539180506989180889) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_159 :
    remainder4Coefficient0.coeff 159 =
      ((289732706217 * 10 ^ 70 +
        2954703749019295892016393876716821923603526598093827252836550846592953) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_160 :
    remainder4Coefficient0.coeff 160 =
      -((62735336779 * 10 ^ 70 +
        2789377103612303012058938534008591191932022968962835664652448891380099) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_161 :
    remainder4Coefficient0.coeff 161 =
      ((11201421520 * 10 ^ 70 +
        8401315213701625437984408347409685991178020441655906033199560639454476) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_162 :
    remainder4Coefficient0.coeff 162 =
      -((1624714740 * 10 ^ 70 +
        7361104903942987222452242785258853936932178308834787764395759665560181) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_163 :
    remainder4Coefficient0.coeff 163 =
      ((182584385 * 10 ^ 70 +
        7604499146126937649075375543776365546152693771193848074797577335659711) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_164 :
    remainder4Coefficient0.coeff 164 =
      -((13817162 * 10 ^ 70 +
        7214269463011922325848156704753591889865036468984965071567793113452941) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_165 :
    remainder4Coefficient0.coeff 165 =
      ((209782 * 10 ^ 70 +
        2094106489120588856037917536419340071433635105084013564343611263547470) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_166 :
    remainder4Coefficient0.coeff 166 =
      ((145206 * 10 ^ 70 +
        4528597046033119626948008317148313523207739024886427213817137504083847) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_167 :
    remainder4Coefficient0.coeff 167 =
      -((35509 * 10 ^ 70 +
        0721851320102010514722188083833589047530319007515966311486773027305418) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_168 :
    remainder4Coefficient0.coeff 168 =
      ((6653 * 10 ^ 70 +
        5492775502688787126444689998100435765105082833122206676907646117739069) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_169 :
    remainder4Coefficient0.coeff 169 =
      -((1073 * 10 ^ 70 +
        1787471038864785302093506654383403722115820053168548171692481888824813) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_170 :
    remainder4Coefficient0.coeff 170 =
      ((126 * 10 ^ 70 +
        4465680900694424296929497460633001937576356380218108765012949936948604) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_171 :
    remainder4Coefficient0.coeff 171 =
      -((7 * 10 ^ 70 +
        0566883241089539501574168803224841998247744390462042092115746606585737) : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_172 :
    remainder4Coefficient0.coeff 172 =
      (-5949021069314912499218015499466762175779153381151659091216591557085197 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_173 :
    remainder4Coefficient0.coeff 173 =
      (1550380030422564465875269695055190298347996242193328209760210880699813 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_174 :
    remainder4Coefficient0.coeff 174 =
      (-105855926497116723523780251450470580706896012768015499477968758417400 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_175 :
    remainder4Coefficient0.coeff 175 =
      (-2838077055611550274189583444950879257865316421125520017061330837915 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_176 :
    remainder4Coefficient0.coeff 176 =
      (783590988982254652111397081543146640551367615803055901369869344387 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_177 :
    remainder4Coefficient0.coeff 177 =
      (-18372827940877057673746240632768768859675347009073454012456445736 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_178 :
    remainder4Coefficient0.coeff 178 =
      (-2274138631337607890492464187160830175346527766501608262674397586 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_179 :
    remainder4Coefficient0.coeff 179 =
      (49144424934164725853973261610454550096791534782749823789854331 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_180 :
    remainder4Coefficient0.coeff 180 =
      (4883363746765941070383021567347045919911709669465415663317523 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_181 :
    remainder4Coefficient0.coeff 181 =
      (104482058353109320795095882459950782183495671711564601157820 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_182 :
    remainder4Coefficient0.coeff 182 =
      (1013312218865942400154746725814114442928670347104302841719 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_183 :
    remainder4Coefficient0.coeff 183 =
      (4929570330808463102337290866341963053483875340733703656 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_184 :
    remainder4Coefficient0.coeff 184 =
      (10690241718563232403029017228930202689205002396035271 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_185 :
    remainder4Coefficient0.coeff 185 =
      (37255090241448419285485780043556267538878986299 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_186 :
    remainder4Coefficient0.coeff 186 =
      (-40261639580430794091260719055174595888192792539 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_187 :
    remainder4Coefficient0.coeff 187 =
      (-61079873397016864996137135464749154193285043 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_188 :
    remainder4Coefficient0.coeff 188 =
      (-31216992430162399546553766900032427897848 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_189 :
    remainder4Coefficient0.coeff 189 =
      (-5358408125710834446514646338336979053 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_190 :
    remainder4Coefficient0.coeff 190 =
      (-263448704752898688304416795843710 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_191 :
    remainder4Coefficient0.coeff 191 =
      (-2855796515767601392313015758 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_192 :
    remainder4Coefficient0.coeff 192 =
      (-4481810793931984381827 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_193 :
    remainder4Coefficient0.coeff 193 =
      (-467172343028109 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C0_coeff_194 :
    remainder4Coefficient0.coeff 194 =
      (-794588 : ℚ) := by
  unfold
    remainder4Coefficient0
    remainder4Coefficient0Block2
    remainder4Coefficient0Block1
    remainder4Coefficient0Block0
    remainder4Coefficient0Chunk24
    remainder4Coefficient0Chunk23
    remainder4Coefficient0Chunk22
    remainder4Coefficient0Chunk21
    remainder4Coefficient0Chunk20
    remainder4Coefficient0Chunk19
    remainder4Coefficient0Chunk18
    remainder4Coefficient0Chunk17
    remainder4Coefficient0Chunk16
    remainder4Coefficient0Chunk15
    remainder4Coefficient0Chunk14
    remainder4Coefficient0Chunk13
    remainder4Coefficient0Chunk12
    remainder4Coefficient0Chunk11
    remainder4Coefficient0Chunk10
    remainder4Coefficient0Chunk9
    remainder4Coefficient0Chunk8
    remainder4Coefficient0Chunk7
    remainder4Coefficient0Chunk6
    remainder4Coefficient0Chunk5
    remainder4Coefficient0Chunk4
    remainder4Coefficient0Chunk3
    remainder4Coefficient0Chunk2
    remainder4Coefficient0Chunk1
    remainder4Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
