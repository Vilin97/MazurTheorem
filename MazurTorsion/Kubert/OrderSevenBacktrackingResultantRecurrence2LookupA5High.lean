/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A5 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A5_coeff_50 :
    remainder2Coefficient5.coeff 50 =
      (4536997018687278322071825226880515848890525143295 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_51 :
    remainder2Coefficient5.coeff 51 =
      (30849558643173766701288435074088248503281094991097 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_52 :
    remainder2Coefficient5.coeff 52 =
      (-95220340007489739605214981707878241588414868276620 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_53 :
    remainder2Coefficient5.coeff 53 =
      (106536583640868574405256960339526933228721070489684 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_54 :
    remainder2Coefficient5.coeff 54 =
      (93164830782748409651416769751500784564105781779151 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_55 :
    remainder2Coefficient5.coeff 55 =
      (-578627282538253583321543106577877607366906622185027 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_56 :
    remainder2Coefficient5.coeff 56 =
      (1092445794418350991227293304062352945919761085569406 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_57 :
    remainder2Coefficient5.coeff 57 =
      (-1010285970366236261311586117768254048794953317061497 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_58 :
    remainder2Coefficient5.coeff 58 =
      (-214009112868664380275346632408479348707168575965346 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_59 :
    remainder2Coefficient5.coeff 59 =
      (2355888510834570221982904312471436476951726541414062 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_60 :
    remainder2Coefficient5.coeff 60 =
      (-4213993205963876886713791483973426125072084952402930 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_61 :
    remainder2Coefficient5.coeff 61 =
      (4374189055099625082866580706568063519555735942802816 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_62 :
    remainder2Coefficient5.coeff 62 =
      (-2426562057443760437955479795717455422957310538712072 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_63 :
    remainder2Coefficient5.coeff 63 =
      (-547879151578059857926911438579520090404041947816918 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_64 :
    remainder2Coefficient5.coeff 64 =
      (2795730063013252313772849604653854918973775121773327 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_65 :
    remainder2Coefficient5.coeff 65 =
      (-3262110651062154797891480141719997226909503679611118 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_66 :
    remainder2Coefficient5.coeff 66 =
      (2229408024555610605875320579090371052347830568858257 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_67 :
    remainder2Coefficient5.coeff 67 =
      (-782020535002471299227450895820569521667112384018964 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_68 :
    remainder2Coefficient5.coeff 68 =
      (-181307121752543769113092165260465525831938245452680 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_69 :
    remainder2Coefficient5.coeff 69 =
      (451941038044837849384065317876121764680852616234936 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_70 :
    remainder2Coefficient5.coeff 70 =
      (-317279331924508839779158647612370746188168316281419 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_71 :
    remainder2Coefficient5.coeff 71 =
      (118291409856805654155265315825055214060283244115820 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_72 :
    remainder2Coefficient5.coeff 72 =
      (-9067085802950879916402351125455550792960048428609 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_73 :
    remainder2Coefficient5.coeff 73 =
      (-16752041284191756224890747636760189106858007365013 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_74 :
    remainder2Coefficient5.coeff 74 =
      (10467065061107254327435430760433350574226355396713 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_75 :
    remainder2Coefficient5.coeff 75 =
      (-2776079750871447450040554150772889836624742403460 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_76 :
    remainder2Coefficient5.coeff 76 =
      (3807677038252640414310368810121093925398743568 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_77 :
    remainder2Coefficient5.coeff 77 =
      (254735917876843325547217135374763303741153870467 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_78 :
    remainder2Coefficient5.coeff 78 =
      (-79970716861673357875251224597009651876784519597 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_79 :
    remainder2Coefficient5.coeff 79 =
      (5086554838729128011357916514757208966931108845 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_80 :
    remainder2Coefficient5.coeff 80 =
      (3002133683565988392458948980633539621521290947 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_81 :
    remainder2Coefficient5.coeff 81 =
      (-733117506467283953626185539260366384756126532 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_82 :
    remainder2Coefficient5.coeff 82 =
      (-3671711776486332869099310649452547803580870 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_83 :
    remainder2Coefficient5.coeff 83 =
      (19844078368367647479805269940340036920130269 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_84 :
    remainder2Coefficient5.coeff 84 =
      (-1019998825567616745605344467509616177727522 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_85 :
    remainder2Coefficient5.coeff 85 =
      (-300251147139026137458381741843066253390545 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_86 :
    remainder2Coefficient5.coeff 86 =
      (8331610236584716832086290155981013157605 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_87 :
    remainder2Coefficient5.coeff 87 =
      (3122163349981012136172833905772391019781 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_88 :
    remainder2Coefficient5.coeff 88 =
      (183377772338127822273190994703138876095 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_89 :
    remainder2Coefficient5.coeff 89 =
      (4809272671110001400826091023037899395 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_90 :
    remainder2Coefficient5.coeff 90 =
      (63506625011524370119277185841139399 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_91 :
    remainder2Coefficient5.coeff 91 =
      (418819725802625644021293199369765 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_92 :
    remainder2Coefficient5.coeff 92 =
      (1197901248587625823394131256191 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_93 :
    remainder2Coefficient5.coeff 93 =
      (309822799767340730668764003 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_94 :
    remainder2Coefficient5.coeff 94 =
      (-4534798300274140721268369 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_95 :
    remainder2Coefficient5.coeff 95 =
      (-6000547169591553991323 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_96 :
    remainder2Coefficient5.coeff 96 =
      (-1661458723421419362 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_97 :
    remainder2Coefficient5.coeff 97 =
      (-62108676656411 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A5_coeff_98 :
    remainder2Coefficient5.coeff 98 =
      (-84879584 : ℚ) := by
  unfold
    remainder2Coefficient5
    remainder2Coefficient5Block1
    remainder2Coefficient5Block0
    remainder2Coefficient5Chunk12
    remainder2Coefficient5Chunk11
    remainder2Coefficient5Chunk10
    remainder2Coefficient5Chunk9
    remainder2Coefficient5Chunk8
    remainder2Coefficient5Chunk7
    remainder2Coefficient5Chunk6
    remainder2Coefficient5Chunk5
    remainder2Coefficient5Chunk4
    remainder2Coefficient5Chunk3
    remainder2Coefficient5Chunk2
    remainder2Coefficient5Chunk1
    remainder2Coefficient5Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
