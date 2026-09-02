/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: B0 source coefficients, low half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5B0_coeff_0 :
    remainder6Coefficient0.coeff 0 =
      (0 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_1 :
    remainder6Coefficient0.coeff 1 =
      (81587636298033060663187077555821876849709622834602720 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_2 :
    remainder6Coefficient0.coeff 2 =
      (246845433310606475862989082822077983955717706626661394428 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_3 :
    remainder6Coefficient0.coeff 3 =
      (-340628448854087974146081095924895319400586076344905194547244 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_4 :
    remainder6Coefficient0.coeff 4 =
      (689298895060134429088448794088039851881611271374139442667475584 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_5 :
    remainder6Coefficient0.coeff 5 =
      (-600634412867710912520513575055560016029959615940035723424897964124 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_6 :
    remainder6Coefficient0.coeff 6 =
      (223136587262302447532307541769865535023908414854556090387159913082740 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_7 :
    remainder6Coefficient0.coeff 7 =
      ((3 * 10 ^ 70 +
        1647945797012725717877286124503658201061838449907545734357244143190147) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_8 :
    remainder6Coefficient0.coeff 8 =
      -((7374 * 10 ^ 70 +
        9095323611250910782390280980090923232831091945889176226743713719660437) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_9 :
    remainder6Coefficient0.coeff 9 =
      ((3932356 * 10 ^ 70 +
        4113575521817346909319047115999489968726726716224411975524942890531509) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_10 :
    remainder6Coefficient0.coeff 10 =
      -((1271599316 * 10 ^ 70 +
        4899023900173584288936110753850005465656501899420217746474963038856273) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_11 :
    remainder6Coefficient0.coeff 11 =
      ((290386914259 * 10 ^ 70 +
        0979943181678724614994842452177943554419194728894447150907815569921908) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_12 :
    remainder6Coefficient0.coeff 12 =
      -((49900769478837 * 10 ^ 70 +
        1146383009444661515075717978729613091820152603255424917398512777536100) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_13 :
    remainder6Coefficient0.coeff 13 =
      ((6693405304943718 * 10 ^ 70 +
        4363533420925068166140291241618739214390176661865294069928296819892931) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_14 :
    remainder6Coefficient0.coeff 14 =
      -((718552768638537988 * 10 ^ 70 +
        8401608873006149776130503822509587166960704398660491290003393730715122) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_15 :
    remainder6Coefficient0.coeff 15 =
      ((62909551193508837509 * 10 ^ 70 +
        6928083011224755441742636232482853255114938538966295967217810498757021) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_16 :
    remainder6Coefficient0.coeff 16 =
      -((4559806438745737355827 * 10 ^ 70 +
        9776455122342343535700094988443008937456910386251234087006516639294836) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_17 :
    remainder6Coefficient0.coeff 17 =
      ((277049530348970173786243 * 10 ^ 70 +
        5453996303939614111453261332885984020710382804306332807228681473653514) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_18 :
    remainder6Coefficient0.coeff 18 =
      -((14261036291373936787218781 * 10 ^ 70 +
        5926482804119502765804811675323779991412346679447558223496521297727794) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_19 :
    remainder6Coefficient0.coeff 19 =
      ((627648747240560790786795512 * 10 ^ 70 +
        6894686706812701022537984067939948168486039158300349569482337837433506) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_20 :
    remainder6Coefficient0.coeff 20 =
      -((23810251529552624031814848055 * 10 ^ 70 +
        6757757081431457112365113128708319612581662123622904193999990198947031) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_21 :
    remainder6Coefficient0.coeff 21 =
      ((784184268137572567962122142662 * 10 ^ 70 +
        1804962723673572359952074361900158723995630020600441093341199415329329) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_22 :
    remainder6Coefficient0.coeff 22 =
      -((22567816601035420690089274509287 * 10 ^ 70 +
        6492324836671537240925738401433670833712299738368817058418435770955518) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_23 :
    remainder6Coefficient0.coeff 23 =
      ((570857054284993491671597437044045 * 10 ^ 70 +
        3838722235372225912264482441713520496372125027630688070113992016359022) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_24 :
    remainder6Coefficient0.coeff 24 =
      -((12760297915069847757022947122246670 * 10 ^ 70 +
        8187339894068552253544891976882261005052923350206126223371061098487733) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_25 :
    remainder6Coefficient0.coeff 25 =
      ((253297982339036723798858832280864527 * 10 ^ 70 +
        3053178507724970526050176072605684464531339835270233270276724541087407) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_26 :
    remainder6Coefficient0.coeff 26 =
      -((4485600174228412687829367038327567489 * 10 ^ 70 +
        9285427697532575575615275148468634920389378194814212393083993881258738) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_27 :
    remainder6Coefficient0.coeff 27 =
      ((71165103565463240291349391803225859346 * 10 ^ 70 +
        8376666929117021030591348824205623595544234955986885443018283861776206) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_28 :
    remainder6Coefficient0.coeff 28 =
      -((1015516932117400362118948269454234370586 * 10 ^ 70 +
        0373799023707817140167773100838435574184495457797528660378286672078068) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_29 :
    remainder6Coefficient0.coeff 29 =
      ((13082366257879451265428926004006090050889 * 10 ^ 70 +
        6077804054690574070028631020652351727171766258152719371586443830500742) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_30 :
    remainder6Coefficient0.coeff 30 =
      -((152675959105693266657445628571032046714585 * 10 ^ 70 +
        9537716857802229608195011685423896135460146898755801757134344358903749) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_31 :
    remainder6Coefficient0.coeff 31 =
      ((1619407413971341859410175798759554955716807 * 10 ^ 70 +
        6453659133206874839179996376827419031169047226019912796130221265828157) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_32 :
    remainder6Coefficient0.coeff 32 =
      -((15659424969662481103434227370268550601786993 * 10 ^ 70 +
        8372267178217296319420114593239911522747340380007552036723432517156473) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_33 :
    remainder6Coefficient0.coeff 33 =
      ((138447874494517086870504512584679773711503714 * 10 ^ 70 +
        5244849157254825401797227835067607184059518108116855560544922283403911) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_34 :
    remainder6Coefficient0.coeff 34 =
      -((1122206812132187727274107983045899633497647262 * 10 ^ 70 +
        9249816556911618780137751150344622105747713032056832494328680893724375) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_35 :
    remainder6Coefficient0.coeff 35 =
      ((8360923622649742252439403432374145577347600977 * 10 ^ 70 +
        0715053501696693483963179736936885176724025730525414034226907494573884) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_36 :
    remainder6Coefficient0.coeff 36 =
      -((57396607604073290273163929540045854640239151011 * 10 ^ 70 +
        9650087852105966814711485363625756001104301817846993112499565461196740) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_37 :
    remainder6Coefficient0.coeff 37 =
      ((363886055678617128723843595057580149010453135812 * 10 ^ 70 +
        2337770061241442026040170446551960412286622676671477998463392629320018) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_38 :
    remainder6Coefficient0.coeff 38 =
      -((2135169335976033275859149153120925092050497909555 * 10 ^ 70 +
        7214731793582838450144681902113636144555413734566342512868239789447074) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_39 :
    remainder6Coefficient0.coeff 39 =
      ((11619146468619195007821985561186341647604828145402 * 10 ^ 70 +
        0256414003406211255785566675655412639765715291778218593670489849716249) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_40 :
    remainder6Coefficient0.coeff 40 =
      -((58752700127816288093764497806961774759259355392363 * 10 ^ 70 +
        6890812330484243421772828179022985948730235550020793715996074419565979) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_41 :
    remainder6Coefficient0.coeff 41 =
      ((276555170853268761474203432356666211801215858062274 * 10 ^ 70 +
        8589262290246342155180248331763672539771325479303626342783351588742369) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_42 :
    remainder6Coefficient0.coeff 42 =
      -((1213889160067983392759998202478829220307106681840610 * 10 ^ 70 +
        0061031238938825167801785140375468348230673435316460331073289893977336) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_43 :
    remainder6Coefficient0.coeff 43 =
      ((4976443572868131147051162214768230442890024296335588 * 10 ^ 70 +
        0646898058853099467693069013906903768505402069151264015411298811251057) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_44 :
    remainder6Coefficient0.coeff 44 =
      -((19083592998710665311435868170286849685078469288275241 * 10 ^ 70 +
        8826755264377454247613761177583652096569657830807274081287762526712038) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_45 :
    remainder6Coefficient0.coeff 45 =
      ((68552168929088960534341169806072594549588034086558905 * 10 ^ 70 +
        2860935751369428178718557649245624255627332183826432567027651976857948) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_46 :
    remainder6Coefficient0.coeff 46 =
      -((230985108321059748939813779601202800728302169097591935 * 10 ^ 70 +
        7594669012216218234513609880486561560181531000908255224947382332013311) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_47 :
    remainder6Coefficient0.coeff 47 =
      ((730962129855787539411095155291310930213045815352480587 * 10 ^ 70 +
        3179252825388759289217382226283307556288033173080824406183018126350175) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_48 :
    remainder6Coefficient0.coeff 48 =
      -((2175037475120179762651662291516584563858073214400125839 * 10 ^ 70 +
        1655820015034916141964942221190502771570588802899757007435551263712357) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_49 :
    remainder6Coefficient0.coeff 49 =
      ((6092291092180939561237142964639058383347813010464897069 * 10 ^ 70 +
        8882973903568917598775452146753922340474723300153772799262032445733560) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_50 :
    remainder6Coefficient0.coeff 50 =
      -((16080054132649264883012014476983180647384776754118687403 * 10 ^ 70 +
        4726895225994420667242962821833788580525654613741576401193847726379253) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_51 :
    remainder6Coefficient0.coeff 51 =
      ((40032220152557967002733848757514959538873364127646813793 * 10 ^ 70 +
        0984589222409667154984671491471873849448253435974618522763877533464393) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_52 :
    remainder6Coefficient0.coeff 52 =
      -((94089771545530571730264430171462021896847163036563896118 * 10 ^ 70 +
        5377424078913462399503762474156382480053796705472630684691143472158852) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_53 :
    remainder6Coefficient0.coeff 53 =
      ((208956207482123872094171882176100098914741406357011927655 * 10 ^ 70 +
        5035890681293125767155603287680392424014596110939656364499010568199575) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_54 :
    remainder6Coefficient0.coeff 54 =
      -((438827085562056036936092948234778080190543144384362758935 * 10 ^ 70 +
        7283726591569445512759658702143426432528163622536359401395370669903565) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_55 :
    remainder6Coefficient0.coeff 55 =
      ((872125190602408841764777142879697555929218397703330647748 * 10 ^ 70 +
        7892982578822893797680602204524221505484522440927262650804268185326769) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_56 :
    remainder6Coefficient0.coeff 56 =
      -((1641388543779478962100383041981857127277284842825612733577 * 10 ^ 70 +
        0755930174631756496920958617035567752447020744257671515079431842233912) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_57 :
    remainder6Coefficient0.coeff 57 =
      ((2927318587749651370820389314554991243585795156491388477635 * 10 ^ 70 +
        6620919131425763555159514336742487903724502791542053456798435378302067) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_58 :
    remainder6Coefficient0.coeff 58 =
      -((4950093082481964939467334428249541674115373558884263570556 * 10 ^ 70 +
        0888156035517640583271204212049257055063965642106582039835035567240407) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_59 :
    remainder6Coefficient0.coeff 59 =
      ((7941106365124242531620614553694793850688858601262448009194 * 10 ^ 70 +
        3118553085307873325507461136246174743933863893764634821788994606388425) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_60 :
    remainder6Coefficient0.coeff 60 =
      -((12091881948267649544802913053193128595183243301725597579397 * 10 ^ 70 +
        5710098383057681300305488142252980899746918034812228672311420432351610) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_61 :
    remainder6Coefficient0.coeff 61 =
      ((17484576087196982247431412316228730984316436241428927146355 * 10 ^ 70 +
        6253716843133205585847775095830735154593293983047997668486746852217677) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_62 :
    remainder6Coefficient0.coeff 62 =
      -((24018749085271666223796205930120372832755524503062132632959 * 10 ^ 70 +
        3349492382742923532480677724588197149932857391338014207889374893923641) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_63 :
    remainder6Coefficient0.coeff 63 =
      ((31358015367023108447761225075762714496717954551360645028551 * 10 ^ 70 +
        2032702136202602812893399706644044144165190306181886629774795281312453) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_64 :
    remainder6Coefficient0.coeff 64 =
      -((38922604342494754625889906875399656855768178169170463981149 * 10 ^ 70 +
        7290916090175759943204194378636859723884434180519216629538470593339629) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_65 :
    remainder6Coefficient0.coeff 65 =
      ((45945835485429018500923179671511910556943801286032558513289 * 10 ^ 70 +
        2234985541878418701818414512523542204875986537997319543956927298329848) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_66 :
    remainder6Coefficient0.coeff 66 =
      -((51594179759928346718315678796094641336352973818816179055363 * 10 ^ 70 +
        2343163429511969530432868773489010352300335645425274109489009444455215) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_67 :
    remainder6Coefficient0.coeff 67 =
      ((55127495084870116439803426063775441327657237306442010228063 * 10 ^ 70 +
        3237629770412217812332582366474355802338883632742099610226346979068925) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_68 :
    remainder6Coefficient0.coeff 68 =
      -((56057570501131775463462824279733718993302815019406337495981 * 10 ^ 70 +
        0751865101625253029846444181663401981276822550689093150633733873638348) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_69 :
    remainder6Coefficient0.coeff 69 =
      ((54258277787651117943018735687033043890078159966218730104299 * 10 ^ 70 +
        6040900514455285629485898616623232747848385636880160789306423097077249) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_70 :
    remainder6Coefficient0.coeff 70 =
      -((49993176120711763271948078388518815730552416773305297115340 * 10 ^ 70 +
        3933464697697747618145047161312587893472177041562336881568912724265022) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_71 :
    remainder6Coefficient0.coeff 71 =
      ((43852335432793247925384129941025964612188616003265600994150 * 10 ^ 70 +
        5587878864905992256816705486286920625663869185020090296183486794913723) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_72 :
    remainder6Coefficient0.coeff 72 =
      -((36619140532666090825839834270159550517721228654407660686899 * 10 ^ 70 +
        5085235259466207187665477357934443960304998366111326175505889595022953) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_73 :
    remainder6Coefficient0.coeff 73 =
      ((29108247220452557388402150209336838773248788503636729156148 * 10 ^ 70 +
        1708583191525897355774797884937360898123139513374429308729388627386891) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_74 :
    remainder6Coefficient0.coeff 74 =
      -((22020270632000478923163186063231341744337627771726706081885 * 10 ^ 70 +
        9508231025612557990516607202946264332913274580351629223084415517685539) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_75 :
    remainder6Coefficient0.coeff 75 =
      ((15847213796582792682078784266545766520359044412444769995721 * 10 ^ 70 +
        6556349207519336847040703918730307733796645550194747093984694460812884) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5B0_coeff_76 :
    remainder6Coefficient0.coeff 76 =
      -((10841732996495315469946172347077025163169127982199976630877 * 10 ^ 70 +
        0259262978903680506197200238131498687922214112910154464892280700435472) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
