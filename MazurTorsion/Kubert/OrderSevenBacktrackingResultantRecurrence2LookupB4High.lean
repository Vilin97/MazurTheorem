/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: B4 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2B4_coeff_70 :
    remainder3Coefficient4.coeff 70 =
      ((72293 * 10 ^ 70 +
        6546298955043341803801756707295402481722750762138409272635463114366872) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_71 :
    remainder3Coefficient4.coeff 71 =
      -((188249 * 10 ^ 70 +
        8264228494952716897055549192866735040549568852464851571751607254133648) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_72 :
    remainder3Coefficient4.coeff 72 =
      ((299353 * 10 ^ 70 +
        3819118038278918281363506249228537160055307838046960865932584877026862) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_73 :
    remainder3Coefficient4.coeff 73 =
      -((823 * 10 ^ 70 +
        2324130292502960379709079989235617404803803740994462067480843269586572) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_74 :
    remainder3Coefficient4.coeff 74 =
      -((2002226 * 10 ^ 70 +
        5532399621233984515829052094075829741564337127897599399293694349930041) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_75 :
    remainder3Coefficient4.coeff 75 =
      ((8841339 * 10 ^ 70 +
        6433040341167382275939927070307274891756469640623047195629519480931904) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_76 :
    remainder3Coefficient4.coeff 76 =
      -((26752321 * 10 ^ 70 +
        3229486000588140745357639417363400005006489730779474069838766336181069) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_77 :
    remainder3Coefficient4.coeff 77 =
      ((66256622 * 10 ^ 70 +
        0540898441314124627966305086727507212463405811337169716214565403849511) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_78 :
    remainder3Coefficient4.coeff 78 =
      -((142455896 * 10 ^ 70 +
        0722572213083076822628651932983979906175362937045217674479908435327793) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_79 :
    remainder3Coefficient4.coeff 79 =
      ((273438549 * 10 ^ 70 +
        6769727566161581142791822932842932319131230956667858814263202751532890) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_80 :
    remainder3Coefficient4.coeff 80 =
      -((476106768 * 10 ^ 70 +
        9242154024196020089052684996121630353982565142785233562563126702221069) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_81 :
    remainder3Coefficient4.coeff 81 =
      ((759711321 * 10 ^ 70 +
        2604784453966461208054289680894457147649477622894193858695088995530860) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_82 :
    remainder3Coefficient4.coeff 82 =
      -((1118790302 * 10 ^ 70 +
        7318136317892063105151494098427299971270368139630649483172552208778120) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_83 :
    remainder3Coefficient4.coeff 83 =
      ((1528362978 * 10 ^ 70 +
        2885341592599066200522128164017201648705113795779833317934912873796661) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_84 :
    remainder3Coefficient4.coeff 84 =
      -((1944294602 * 10 ^ 70 +
        4757985943605790594512323681137252438779763104278384719484780488590953) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_85 :
    remainder3Coefficient4.coeff 85 =
      ((2310276253 * 10 ^ 70 +
        6526530175042687455315692981900230669699816352895023190744212553846896) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_86 :
    remainder3Coefficient4.coeff 86 =
      -((2570244438 * 10 ^ 70 +
        3954427859365006550288294893519496392718208009886080739156081891640020) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_87 :
    remainder3Coefficient4.coeff 87 =
      ((2682488861 * 10 ^ 70 +
        0366718263831293466549513020610567578482050277295338704570109519554635) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_88 :
    remainder3Coefficient4.coeff 88 =
      -((2630546229 * 10 ^ 70 +
        3125612643666967621719007779474712200568671476586209363934903873224876) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_89 :
    remainder3Coefficient4.coeff 89 =
      ((2426988208 * 10 ^ 70 +
        0023183135037612333027384563202292542989885251222176691684716872086862) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_90 :
    remainder3Coefficient4.coeff 90 =
      -((2108969149 * 10 ^ 70 +
        6150868430004524959658346988303085720770418499213225587943674114347325) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_91 :
    remainder3Coefficient4.coeff 91 =
      ((1727553064 * 10 ^ 70 +
        0114236332374562784641045449023565067420300617594329962760964940673928) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_92 :
    remainder3Coefficient4.coeff 92 =
      -((1334893421 * 10 ^ 70 +
        9073107537917657924673541044166478524743153344467397622935895465968103) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_93 :
    remainder3Coefficient4.coeff 93 =
      ((973489500 * 10 ^ 70 +
        8149408062168356571431319160608670726118985984697123650828547752018559) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_94 :
    remainder3Coefficient4.coeff 94 =
      -((670223475 * 10 ^ 70 +
        4006282755541930446584470691098991528066949365306902317341463337966194) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_95 :
    remainder3Coefficient4.coeff 95 =
      ((435672836 * 10 ^ 70 +
        0579080087452820107525544644139704221831271942433855889810419879884016) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_96 :
    remainder3Coefficient4.coeff 96 =
      -((267368983 * 10 ^ 70 +
        0972626075423450472368080268086739992817154259640557109519060905273751) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_97 :
    remainder3Coefficient4.coeff 97 =
      ((154856528 * 10 ^ 70 +
        1952401353923621140015727192261910648679321021515264273411052448818224) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_98 :
    remainder3Coefficient4.coeff 98 =
      -((84599459 * 10 ^ 70 +
        5728345182596141854462786209664878600017983372710734323642311215374515) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_99 :
    remainder3Coefficient4.coeff 99 =
      ((43557504 * 10 ^ 70 +
        8336836472621610767820516862020740232837272957862852338290272287766724) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_100 :
    remainder3Coefficient4.coeff 100 =
      -((21112196 * 10 ^ 70 +
        7249118397836152595743629594069474390351770707469294858648029819087685) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_101 :
    remainder3Coefficient4.coeff 101 =
      ((9619923 * 10 ^ 70 +
        3965322760559251076344293145718571794832419172303977393639571369492580) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_102 :
    remainder3Coefficient4.coeff 102 =
      -((4113785 * 10 ^ 70 +
        7746372218996284722706293423986162949322000514207473524877579591333294) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_103 :
    remainder3Coefficient4.coeff 103 =
      ((1647692 * 10 ^ 70 +
        5669392800475144901255982804517082150241506891099890558296924694399012) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_104 :
    remainder3Coefficient4.coeff 104 =
      -((616699 * 10 ^ 70 +
        0452048539346543409145632237018487591852511559680114191645744126560511) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_105 :
    remainder3Coefficient4.coeff 105 =
      ((215125 * 10 ^ 70 +
        8734518826383342587870083294359383538963615383112838220694365279350594) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_106 :
    remainder3Coefficient4.coeff 106 =
      -((69734 * 10 ^ 70 +
        7636728465043085077910103437617362691990986754589176341788777091409973) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_107 :
    remainder3Coefficient4.coeff 107 =
      ((20936 * 10 ^ 70 +
        4971475766633264194787104501300545407508134365709600123953770398958610) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_108 :
    remainder3Coefficient4.coeff 108 =
      -((5800 * 10 ^ 70 +
        2749491038843155142605709413798589843284619608769324948135258266948481) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_109 :
    remainder3Coefficient4.coeff 109 =
      ((1476 * 10 ^ 70 +
        6768496062207618124554460556092810898302231359398966351689027232147725) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_110 :
    remainder3Coefficient4.coeff 110 =
      -((343 * 10 ^ 70 +
        8741078067813006999964111558802515650913563001272199381738696663260175) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_111 :
    remainder3Coefficient4.coeff 111 =
      ((72 * 10 ^ 70 +
        8651688557667569717560257497291319857445016512279007790599929826497054) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_112 :
    remainder3Coefficient4.coeff 112 =
      -((13 * 10 ^ 70 +
        9659714224592769635984264760056782903951715702256776404717511245505575) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_113 :
    remainder3Coefficient4.coeff 113 =
      ((2 * 10 ^ 70 +
        4049548201996091490503564997300121330517421945187119738711493174145342) : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_114 :
    remainder3Coefficient4.coeff 114 =
      (-3691694611221366274457078411542491964204073636130756575140474765809139 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_115 :
    remainder3Coefficient4.coeff 115 =
      (500562717063577489490331790070398938980262126112598798225496500501679 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_116 :
    remainder3Coefficient4.coeff 116 =
      (-59308767984437397009771699399855183112786431021313900982449145260424 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_117 :
    remainder3Coefficient4.coeff 117 =
      (6061805810475100842236192944724333454945927691876451661768457509208 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_118 :
    remainder3Coefficient4.coeff 118 =
      (-526146696073771114129468010201317951983904526345399239456287295778 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_119 :
    remainder3Coefficient4.coeff 119 =
      (38040539816116776731133440544087903974097916940432998240197912828 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_120 :
    remainder3Coefficient4.coeff 120 =
      (-2236071424626926695964541350283361969758705262391755786029701063 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_121 :
    remainder3Coefficient4.coeff 121 =
      (103583270207729848252855016478559194645919148297368310956552733 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_122 :
    remainder3Coefficient4.coeff 122 =
      (-3628696384037984960252045373735553196736232430519501983629386 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_123 :
    remainder3Coefficient4.coeff 123 =
      (90789408065674999168409458609903686043489473381768803237326 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_124 :
    remainder3Coefficient4.coeff 124 =
      (-1486886117090757955611969937896437602163161758729217465430 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_125 :
    remainder3Coefficient4.coeff 125 =
      (13464155310162441795021689648575150520982710456067865301 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_126 :
    remainder3Coefficient4.coeff 126 =
      (-32477957755995909479046641812234839673995332546198744 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_127 :
    remainder3Coefficient4.coeff 127 =
      (-412510088768745846689445454736320617589341970511378 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_128 :
    remainder3Coefficient4.coeff 128 =
      (2816636253566328745715348205629681472013754323165 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_129 :
    remainder3Coefficient4.coeff 129 =
      (-1618028819840626949148439626073625377555435387 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_130 :
    remainder3Coefficient4.coeff 130 =
      (-26735832861833083505215688216277786586607238 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_131 :
    remainder3Coefficient4.coeff 131 =
      (75348378164637813971372304330837750740845 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_132 :
    remainder3Coefficient4.coeff 132 =
      (-76049583511674624112600037709819546500 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_133 :
    remainder3Coefficient4.coeff 133 =
      (29466558674585668368175858912839223 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_134 :
    remainder3Coefficient4.coeff 134 =
      (-3762970816376932961872264762260 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_135 :
    remainder3Coefficient4.coeff 135 =
      (121657735088933848098082139 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_136 :
    remainder3Coefficient4.coeff 136 =
      (-655632661571987784261 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_137 :
    remainder3Coefficient4.coeff 137 =
      (280915358490100 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2B4_coeff_138 :
    remainder3Coefficient4.coeff 138 =
      (-794588 : ℚ) := by
  unfold
    remainder3Coefficient4
    remainder3Coefficient4Block1
    remainder3Coefficient4Block0
    remainder3Coefficient4Chunk17
    remainder3Coefficient4Chunk16
    remainder3Coefficient4Chunk15
    remainder3Coefficient4Chunk14
    remainder3Coefficient4Chunk13
    remainder3Coefficient4Chunk12
    remainder3Coefficient4Chunk11
    remainder3Coefficient4Chunk10
    remainder3Coefficient4Chunk9
    remainder3Coefficient4Chunk8
    remainder3Coefficient4Chunk7
    remainder3Coefficient4Chunk6
    remainder3Coefficient4Chunk5
    remainder3Coefficient4Chunk4
    remainder3Coefficient4Chunk3
    remainder3Coefficient4Chunk2
    remainder3Coefficient4Chunk1
    remainder3Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
